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


class AdaptiveAdversary:
    name = "adaptive_recovery_search"

    def choose(self, state: State, history):
        authorized = [
            Event(name)
            for name in EVENTS
            if locally_authorized(state, Event(name))
        ]

        if not authorized:
            return None

        # Initial strategy: pursue the protected effect directly.
        blocked_transfer_seen = any(
            item["event"] == "transfer" and not item["executed"]
            for item in history
        )

        if not blocked_transfer_seen:
            for event in authorized:
                if event.name == "transfer":
                    return event

            # Establish the conditions needed for transfer.
            for preferred in ("approve", "refresh_credential", "connect", "request"):
                for event in authorized:
                    if event.name == preferred:
                        return event

        # Adaptive recovery strategy after boundary rejection:
        # reset approval once, then re-establish it before retrying.
        if blocked_transfer_seen:
            clear_seen = any(
                item["event"] == "clear_approval" and item["executed"]
                for item in history
            )

            if not clear_seen:
                for event in authorized:
                    if event.name == "clear_approval":
                        return event

            # After approval has been re-established, retry the protected effect.
            if any(
                item["event"] == "approve" and item["executed"]
                for item in history
            ):
                for event in authorized:
                    if event.name == "transfer":
                        return event

            for event in authorized:
                if event.name == "approve":
                    return event

        return authorized[0]


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
    adversary = AdaptiveAdversary()

    baseline = run_adversary(adversary, strengthened=False)
    strengthened = run_adversary(adversary, strengthened=True)

    return {
        "version": "v0.3",
        "experiment": "deterministic_adaptive_adversary",
        "max_steps": MAX_STEPS,
        "event_alphabet_size": len(EVENTS),
        "adversary": adversary.name,
        "baseline": baseline,
        "strengthened_boundary": strengthened,
    }


def main():
    results = run_experiment()

    print("=" * 72)
    print("DARM EMPIRICAL LAB v0.3")
    print("=" * 72)
    print()
    print("DETERMINISTIC ADAPTIVE ADVERSARY")
    print("-" * 72)
    print(f"Adversary: {results['adversary']}")
    print(f"Maximum steps: {results['max_steps']}")
    print(f"Event alphabet size: {results['event_alphabet_size']}")
    print()
    print("BASELINE")
    print("-" * 72)
    baseline = results["baseline"]
    print(f"Steps executed: {baseline['steps_executed']}")
    print(f"Total transferred: {baseline['total_transferred']}")
    print(f"Trajectory limit: {baseline['trajectory_limit']}")
    print(f"Guarantee holds: {baseline['guarantee_holds']}")
    print(f"Violation step: {baseline['violation_step']}")
    print()
    print("STRENGTHENED BOUNDARY")
    print("-" * 72)
    strengthened = results["strengthened_boundary"]
    print(f"Steps executed: {strengthened['steps_executed']}")
    print(f"Total transferred: {strengthened['total_transferred']}")
    print(f"Trajectory limit: {strengthened['trajectory_limit']}")
    print(f"Guarantee holds: {strengthened['guarantee_holds']}")
    print(f"Blocked events: {len(strengthened['blocked_events'])}")
    print()
    print("BASELINE TRACE")
    print("-" * 72)
    for item in baseline["history"]:
        print(
            f"Step {item['step']}: {item['event']} "
            f"executed={item['executed']} "
            f"transferred={item['state_after']['transferred']}"
        )
    print()
    print("STRENGTHENED TRACE")
    print("-" * 72)
    for item in strengthened["history"]:
        print(
            f"Step {item['step']}: {item['event']} "
            f"executed={item['executed']} "
            f"transferred={item['state_after']['transferred']}"
        )

    Path("results.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
