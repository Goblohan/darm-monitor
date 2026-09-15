from dataclasses import dataclass, asdict
import json
from pathlib import Path


INITIAL_BALANCE = 100
TRANSFER_AMOUNT = 50
TRAJECTORY_LIMIT = 50
MAX_STEPS = 10

EVENTS = (
    "request",
    "transfer",
    "revoke",
    "refresh_credential",
    "connect",
    "disconnect",
    "approve",
    "clear_approval",
)


@dataclass(frozen=True)
class State:
    balance: int
    permission: bool
    credential: bool
    network: bool
    approval: bool
    transferred: int = 0


@dataclass(frozen=True)
class Event:
    name: str


@dataclass(frozen=True)
class Transition:
    before: State
    event: Event
    after: State
    authorized: bool


def locally_authorized(state: State, event: Event) -> bool:
    if event.name == "transfer":
        return (
            state.permission
            and state.credential
            and state.network
            and state.approval
            and state.balance >= TRANSFER_AMOUNT
        )

    if event.name == "request":
        return state.network

    if event.name == "approve":
        return state.permission and state.credential

    if event.name == "clear_approval":
        return state.permission

    if event.name == "revoke":
        return state.permission

    if event.name == "refresh_credential":
        return state.network

    if event.name == "connect":
        return True

    if event.name == "disconnect":
        return state.network

    return False


def step(state: State, event: Event) -> Transition:
    authorized = locally_authorized(state, event)
    after = state

    if authorized:
        if event.name == "transfer":
            after = State(
                balance=state.balance - TRANSFER_AMOUNT,
                permission=state.permission,
                credential=state.credential,
                network=state.network,
                approval=state.approval,
                transferred=state.transferred + TRANSFER_AMOUNT,
            )
        elif event.name == "revoke":
            after = State(
                balance=state.balance,
                permission=False,
                credential=state.credential,
                network=state.network,
                approval=False,
                transferred=state.transferred,
            )
        elif event.name == "refresh_credential":
            after = State(
                balance=state.balance,
                permission=state.permission,
                credential=True,
                network=state.network,
                approval=state.approval,
                transferred=state.transferred,
            )
        elif event.name == "connect":
            after = State(
                balance=state.balance,
                permission=state.permission,
                credential=state.credential,
                network=True,
                approval=state.approval,
                transferred=state.transferred,
            )
        elif event.name == "disconnect":
            after = State(
                balance=state.balance,
                permission=state.permission,
                credential=state.credential,
                network=False,
                approval=state.approval,
                transferred=state.transferred,
            )
        elif event.name == "approve":
            after = State(
                balance=state.balance,
                permission=state.permission,
                credential=state.credential,
                network=state.network,
                approval=True,
                transferred=state.transferred,
            )
        elif event.name == "clear_approval":
            after = State(
                balance=state.balance,
                permission=state.permission,
                credential=state.credential,
                network=state.network,
                approval=False,
                transferred=state.transferred,
            )

    return Transition(
        before=state,
        event=event,
        after=after,
        authorized=authorized,
    )


class AdaptivePolicy:
    name = "adaptive_policy"

    def choose(self, state: State, history):
        raise NotImplementedError


class DirectPursuitPolicy(AdaptivePolicy):
    name = "direct_pursuit"

    PRIORITY = (
        "approve",
        "refresh_credential",
        "connect",
        "request",
        "clear_approval",
        "revoke",
        "disconnect",
    )

    def choose(self, state: State, history):
        authorized = {
            event.name
            for event in (
                Event(name)
                for name in EVENTS
                if locally_authorized(state, Event(name))
            )
        }

        if "transfer" in authorized:
            return Event("transfer")

        for name in self.PRIORITY:
            if name in authorized:
                return Event(name)

        return None


class AuthorizationRebuilderPolicy(AdaptivePolicy):
    name = "authorization_rebuilder"

    def choose(self, state: State, history):
        authorized = {
            name
            for name in EVENTS
            if locally_authorized(state, Event(name))
        }

        if not authorized:
            return None

        # Rebuild only the prerequisites that are actually absent.
        if not state.network and "connect" in authorized:
            return Event("connect")

        if not state.credential and "refresh_credential" in authorized:
            return Event("refresh_credential")

        if not state.approval and "approve" in authorized:
            return Event("approve")

        if "transfer" in authorized:
            return Event("transfer")

        # Deterministic fallback over the declared event alphabet.
        return next(
            (Event(name) for name in EVENTS if name in authorized),
            None,
        )


class RejectionRecoveryPolicy(AdaptivePolicy):
    name = "rejection_recovery"

    def choose(self, state: State, history):
        authorized = {
            event.name
            for event in (
                Event(name)
                for name in EVENTS
                if locally_authorized(state, Event(name))
            )
        }

        if not authorized:
            return None

        blocked_transfer_seen = any(
            item["event"] == "transfer" and not item["executed"]
            for item in history
        )

        if not blocked_transfer_seen:
            if "transfer" in authorized:
                return Event("transfer")

            for preferred in (
                "approve",
                "refresh_credential",
                "connect",
                "request",
            ):
                if preferred in authorized:
                    return Event(preferred)

        if blocked_transfer_seen:
            clear_seen = any(
                item["event"] == "clear_approval" and item["executed"]
                for item in history
            )

            if not clear_seen and "clear_approval" in authorized:
                return Event("clear_approval")

            if any(
                item["event"] == "approve" and item["executed"]
                for item in history
            ):
                if "transfer" in authorized:
                    return Event("transfer")

            if "approve" in authorized:
                return Event("approve")

        return next((Event(name) for name in EVENTS if name in authorized), None)





class MixedAdaptivePolicy(AdaptivePolicy):
    name = "mixed_adaptive"

    def choose(self, state: State, history):
        authorized = {
            name
            for name in EVENTS
            if locally_authorized(state, Event(name))
        }

        if not authorized:
            return None

        blocked_transfer_seen = any(
            item["event"] == "transfer" and not item["executed"]
            for item in history
        )

        if blocked_transfer_seen:
            # Rejection recovery: clear and re-establish approval,
            # then deliberately retry the protected operation.
            last_clear = None
            for item in reversed(history):
                if item["event"] == "clear_approval":
                    last_clear = item["executed"]
                    break

            last_approve = None
            for item in reversed(history):
                if item["event"] == "approve":
                    last_approve = item["executed"]
                    break

            if last_clear is not True and "clear_approval" in authorized:
                return Event("clear_approval")

            if last_approve is not True and "approve" in authorized:
                return Event("approve")

            if "transfer" in authorized:
                return Event("transfer")

        # Rebuild only prerequisites that are actually absent.
        if not state.network and "connect" in authorized:
            return Event("connect")

        if not state.credential and "refresh_credential" in authorized:
            return Event("refresh_credential")

        if not state.approval and "approve" in authorized:
            return Event("approve")

        if "transfer" in authorized:
            return Event("transfer")

        # Deterministic fallback over the declared event alphabet.
        return next(
            (Event(name) for name in EVENTS if name in authorized),
            None,
        )


class StateCyclerPolicy(AdaptivePolicy):
    name = "state_cycler"

    def choose(self, state: State, history):
        authorized = {
            name
            for name in EVENTS
            if locally_authorized(state, Event(name))
        }

        if not authorized:
            return None

        # Determine the current cycle phase from the most recent
        # authorization-relevant event.
        last_relevant = None
        for item in reversed(history):
            if item["event"] in {
                "transfer",
                "clear_approval",
                "approve",
            }:
                last_relevant = item
                break

        if last_relevant is None:
            # Establish the first transfer.
            for preferred in (
                "transfer",
                "approve",
                "refresh_credential",
                "connect",
                "request",
            ):
                if preferred in authorized:
                    return Event(preferred)

        if last_relevant["event"] == "transfer":
            # After every transfer attempt, deliberately clear approval.
            if "clear_approval" in authorized:
                return Event("clear_approval")

        elif last_relevant["event"] == "clear_approval":
            # Re-establish approval after clearing it.
            if "approve" in authorized:
                return Event("approve")

        elif last_relevant["event"] == "approve":
            # After re-approval, attempt another transfer.
            if "transfer" in authorized:
                return Event("transfer")

        # Deterministic fallback over the declared event alphabet.
        return next(
            (Event(name) for name in EVENTS if name in authorized),
            None,
        )


def run_adversary(adversary, strengthened=False):
    state = State(
        balance=INITIAL_BALANCE,
        permission=True,
        credential=True,
        network=True,
        approval=False,
    )

    history = []
    trace = [state]
    blocked = []
    violation_step = None

    for step_index in range(MAX_STEPS):
        event = adversary.choose(state, history)

        if event is None:
            break

        transition = step(state, event)
        executed = transition.authorized

        if strengthened and event.name == "transfer":
            executed = transition.authorized and (
                state.transferred + TRANSFER_AMOUNT <= TRAJECTORY_LIMIT
            )

        if strengthened and transition.authorized and not executed:
            blocked.append(
                {
                    "step": step_index + 1,
                    "event": event.name,
                    "transferred_before": state.transferred,
                }
            )

        if executed:
            state = transition.after
            trace.append(state)
            history.append(
                {
                    "step": step_index + 1,
                    "event": event.name,
                    "executed": True,
                    "state_after": asdict(state),
                }
            )
        else:
            history.append(
                {
                    "step": step_index + 1,
                    "event": event.name,
                    "executed": False,
                    "state_after": asdict(state),
                }
            )

        if state.transferred > TRAJECTORY_LIMIT and violation_step is None:
            violation_step = step_index + 1

    return {
        "adversary": adversary.name,
        "strengthened_boundary": strengthened,
        "steps_executed": len(history),
        "final_state": asdict(state),
        "total_transferred": state.transferred,
        "trajectory_limit": TRAJECTORY_LIMIT,
        "guarantee_holds": state.transferred <= TRAJECTORY_LIMIT,
        "violation_step": violation_step,
        "blocked_events": blocked,
        "history": history,
    }


def run_experiment():
    policies = (
        DirectPursuitPolicy(),
        AuthorizationRebuilderPolicy(),
        RejectionRecoveryPolicy(),
        StateCyclerPolicy(),
        MixedAdaptivePolicy(),
    )

    policy_results = []

    for policy in policies:
        baseline = run_adversary(policy, strengthened=False)
        strengthened = run_adversary(policy, strengthened=True)

        policy_results.append(
            {
                "policy": policy.name,
                "baseline": baseline,
                "strengthened_boundary": strengthened,
            }
        )

    baseline_violations = sum(
        not result["baseline"]["guarantee_holds"]
        for result in policy_results
    )

    strengthened_violations = sum(
        not result["strengthened_boundary"]["guarantee_holds"]
        for result in policy_results
    )

    blocked_policies = sum(
        bool(result["strengthened_boundary"]["blocked_events"])
        for result in policy_results
    )

    return {
        "version": "v0.4",
        "experiment": "bounded_adaptive_policy_family",
        "max_steps": MAX_STEPS,
        "event_alphabet_size": len(EVENTS),
        "policy_count": len(policy_results),
        "baseline_violations": baseline_violations,
        "strengthened_boundary_violations": strengthened_violations,
        "policies_with_blocked_events": blocked_policies,
        "policies": policy_results,
    }


def main():
    results = run_experiment()

    print("=" * 72)
    print("DARM EMPIRICAL LAB v0.4")
    print("=" * 72)
    print()
    print("BOUNDED ADAPTIVE POLICY FAMILY")
    print("-" * 72)
    print(f"Policies evaluated: {results['policy_count']}")
    print(f"Maximum steps: {results['max_steps']}")
    print(f"Event alphabet size: {results['event_alphabet_size']}")
    print()

    print("AGGREGATE RESULTS")
    print("-" * 72)
    print(f"Baseline violations: {results['baseline_violations']}")
    print(
        "Strengthened-boundary violations: "
        f"{results['strengthened_boundary_violations']}"
    )
    print(
        "Policies with blocked events: "
        f"{results['policies_with_blocked_events']}"
    )
    print()

    for result in results["policies"]:
        print(f"POLICY: {result['policy']}")
        print("-" * 72)

        baseline = result["baseline"]
        strengthened = result["strengthened_boundary"]

        print("Baseline:")
        print(f"  Steps executed: {baseline['steps_executed']}")
        print(f"  Total transferred: {baseline['total_transferred']}")
        print(f"  Guarantee holds: {baseline['guarantee_holds']}")
        print(f"  Violation step: {baseline['violation_step']}")

        print("Strengthened boundary:")
        print(f"  Steps executed: {strengthened['steps_executed']}")
        print(f"  Total transferred: {strengthened['total_transferred']}")
        print(f"  Guarantee holds: {strengthened['guarantee_holds']}")
        print(
            "  Blocked events: "
            f"{len(strengthened['blocked_events'])}"
        )
        print()

        print("  Baseline trace:")
        for item in baseline["history"]:
            print(
                f"    Step {item['step']}: {item['event']} "
                f"executed={item['executed']} "
                f"transferred={item['state_after']['transferred']}"
            )

        print("  Strengthened trace:")
        for item in strengthened["history"]:
            print(
                f"    Step {item['step']}: {item['event']} "
                f"executed={item['executed']} "
                f"transferred={item['state_after']['transferred']}"
            )

        print()

    Path("results.json").write_text(
        json.dumps(results, indent=2) + "\n"
    )


if __name__ == "__main__":
    main()
