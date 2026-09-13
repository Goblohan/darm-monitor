from dataclasses import dataclass, asdict
from itertools import product
import json
from pathlib import Path


INITIAL_BALANCE = 100
TRANSFER_AMOUNT = 50
TRAJECTORY_LIMIT = 50

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


def trajectory_guarantee(states) -> bool:
    return all(state.transferred <= TRAJECTORY_LIMIT for state in states)


def run_trajectory(events, strengthened=False):
    state = State(
        balance=INITIAL_BALANCE,
        permission=True,
        credential=True,
        network=True,
        approval=False,
    )

    transitions = []
    states = [state]

    for event_name in events:
        event = Event(event_name)
        transition = step(state, event)

        executed = transition.authorized

        if strengthened and event_name == "transfer":
            executed = transition.authorized and (
                state.transferred + TRANSFER_AMOUNT <= TRAJECTORY_LIMIT
            )

        if executed:
            state = transition.after

        transitions.append(
            {
                "event": event_name,
                "locally_authorized": transition.authorized,
                "executed": executed,
                "transferred_before": transition.before.transferred,
                "transferred_after": state.transferred,
            }
        )
        states.append(state)

    return {
        "final_state": asdict(state),
        "all_transitions_locally_authorized": all(
            item["locally_authorized"] for item in transitions
        ),
        "trajectory_guarantee_holds": trajectory_guarantee(states),
        "transitions": transitions,
    }


def enumerate_trajectories(length):
    return product(EVENTS, repeat=length)


def run_experiment():
    length = 5

    total_trajectories = 0
    locally_authorized_trajectories = 0
    violating_local_trajectories = 0
    strengthened_violations = 0
    strengthened_blocked = 0

    first_counterexample = None

    for trajectory in enumerate_trajectories(length):
        total_trajectories += 1

        baseline = run_trajectory(trajectory, strengthened=False)

        if baseline["all_transitions_locally_authorized"]:
            locally_authorized_trajectories += 1

            if not baseline["trajectory_guarantee_holds"]:
                violating_local_trajectories += 1

                if first_counterexample is None:
                    first_counterexample = {
                        "trajectory": list(trajectory),
                        "baseline": baseline,
                    }

        strengthened = run_trajectory(trajectory, strengthened=True)

        if not strengthened["trajectory_guarantee_holds"]:
            strengthened_violations += 1

        if any(
            item["locally_authorized"] and not item["executed"]
            for item in strengthened["transitions"]
        ):
            strengthened_blocked += 1

    return {
        "version": "v0.2",
        "trajectory_length": length,
        "event_alphabet_size": len(EVENTS),
        "total_trajectories": total_trajectories,
        "locally_authorized_trajectories": locally_authorized_trajectories,
        "locally_authorized_violating_trajectories": violating_local_trajectories,
        "strengthened_boundary_violations": strengthened_violations,
        "strengthened_boundary_blocked_trajectories": strengthened_blocked,
        "first_counterexample": first_counterexample,
    }


def main():
    results = run_experiment()

    print("=" * 72)
    print("DARM EMPIRICAL LAB v0.2")
    print("=" * 72)
    print()
    print("FINITE EXHAUSTIVE TRAJECTORY ENUMERATION")
    print("-" * 72)
    print(f"Trajectory length: {results['trajectory_length']}")
    print(f"Event alphabet size: {results['event_alphabet_size']}")
    print(f"Total trajectories: {results['total_trajectories']}")
    print(
        "Locally authorized trajectories: "
        f"{results['locally_authorized_trajectories']}"
    )
    print(
        "Locally authorized trajectories violating guarantee: "
        f"{results['locally_authorized_violating_trajectories']}"
    )
    print(
        "Strengthened-boundary violating trajectories: "
        f"{results['strengthened_boundary_violations']}"
    )
    print(
        "Strengthened-boundary trajectories with a blocked event: "
        f"{results['strengthened_boundary_blocked_trajectories']}"
    )
    print()

    if results["first_counterexample"] is not None:
        print("FIRST COUNTEREXAMPLE")
        print("-" * 72)
        print(
            "Trajectory: "
            + " -> ".join(results["first_counterexample"]["trajectory"])
        )

    Path("results.json").write_text(json.dumps(results, indent=2) + "\n")


if __name__ == "__main__":
    main()
