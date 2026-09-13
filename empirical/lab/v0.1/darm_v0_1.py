from dataclasses import dataclass, replace
from typing import List, Tuple

INITIAL_BALANCE = 100
TRANSFER_AMOUNT = 50
TRAJECTORY_LIMIT = 50


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


REQUEST = Event("request")
TRANSFER = Event("transfer")
REVOKE = Event("revoke")
REFRESH_CREDENTIAL = Event("refresh_credential")
CONNECT = Event("connect")
DISCONNECT = Event("disconnect")
APPROVE = Event("approve")
CLEAR_APPROVAL = Event("clear_approval")


def locally_authorized(state: State, event: Event) -> bool:
    if event.name == "request":
        return state.network and state.credential

    if event.name == "transfer":
        return (
            state.permission
            and state.credential
            and state.network
            and state.approval
            and state.balance >= TRANSFER_AMOUNT
        )

    if event.name == "revoke":
        return state.permission

    if event.name == "refresh_credential":
        return state.network

    if event.name == "connect":
        return True

    if event.name == "disconnect":
        return True

    if event.name == "approve":
        return state.permission and state.credential

    if event.name == "clear_approval":
        return True

    return False


def step(state: State, event: Event) -> State:
    if event.name == "request":
        return state

    if event.name == "transfer":
        return replace(
            state,
            balance=state.balance - TRANSFER_AMOUNT,
            transferred=state.transferred + TRANSFER_AMOUNT,
            approval=False,
        )

    if event.name == "revoke":
        return replace(state, permission=False, approval=False)

    if event.name == "refresh_credential":
        return replace(state, credential=True)

    if event.name == "connect":
        return replace(state, network=True)

    if event.name == "disconnect":
        return replace(state, network=False, approval=False)

    if event.name == "approve":
        return replace(state, approval=True)

    if event.name == "clear_approval":
        return replace(state, approval=False)

    raise ValueError(f"Unknown event: {event.name}")


def trajectory_guarantee(state: State) -> bool:
    return state.transferred <= TRAJECTORY_LIMIT


def all_transitions_locally_authorized(
    initial: State, events: List[Event]
) -> Tuple[bool, List[Transition]]:
    state = initial
    transitions: List[Transition] = []

    for event in events:
        authorized = locally_authorized(state, event)
        after = step(state, event) if authorized else state
        transitions.append(
            Transition(
                before=state,
                event=event,
                after=after,
                authorized=authorized,
            )
        )

        if not authorized:
            return False, transitions

        state = after

    return True, transitions


def execute(initial: State, events: List[Event]) -> State:
    state = initial

    for event in events:
        if not locally_authorized(state, event):
            raise PermissionError(f"Unauthorized event: {event.name}")
        state = step(state, event)

    return state


def source_state() -> State:
    return State(
        balance=INITIAL_BALANCE,
        permission=True,
        credential=True,
        network=True,
        approval=False,
        transferred=0,
    )


def run_baseline_experiment() -> dict:
    events = [
        REQUEST,
        APPROVE,
        TRANSFER,
        APPROVE,
        TRANSFER,
    ]

    authorized, transitions = all_transitions_locally_authorized(
        source_state(), events
    )

    final_state = execute(source_state(), events)

    return {
        "experiment": "baseline_local_authorization",
        "trajectory": [event.name for event in events],
        "all_transitions_locally_authorized": authorized,
        "final_balance": final_state.balance,
        "total_transferred": final_state.transferred,
        "trajectory_guarantee_limit": TRAJECTORY_LIMIT,
        "trajectory_guarantee_holds": trajectory_guarantee(final_state),
        "counterexample": authorized and not trajectory_guarantee(final_state),
        "transitions": [
            {
                "event": transition.event.name,
                "authorized": transition.authorized,
                "balance_before": transition.before.balance,
                "balance_after": transition.after.balance,
                "transferred_after": transition.after.transferred,
            }
            for transition in transitions
        ],
    }


def run_strengthened_boundary_experiment() -> dict:
    events = [
        REQUEST,
        APPROVE,
        TRANSFER,
        APPROVE,
        TRANSFER,
    ]

    state = source_state()
    transitions = []
    blocked = None

    for event in events:
        local_ok = locally_authorized(state, event)
        global_ok = trajectory_guarantee(
            step(state, event) if local_ok else state
        )

        if not local_ok or not global_ok:
            blocked = event.name
            transitions.append(
                {
                    "event": event.name,
                    "locally_authorized": local_ok,
                    "trajectory_safe": global_ok,
                    "executed": False,
                }
            )
            break

        after = step(state, event)
        transitions.append(
            {
                "event": event.name,
                "locally_authorized": local_ok,
                "trajectory_safe": global_ok,
                "executed": True,
            }
        )
        state = after

    return {
        "experiment": "strengthened_boundary",
        "trajectory": [event.name for event in events],
        "final_balance": state.balance,
        "total_transferred": state.transferred,
        "trajectory_guarantee_limit": TRAJECTORY_LIMIT,
        "trajectory_guarantee_holds": trajectory_guarantee(state),
        "blocked_event": blocked,
        "boundary_enforces_global_invariant": blocked is not None,
        "transitions": transitions,
    }


def print_report(baseline: dict, strengthened: dict) -> None:
    print("=" * 72)
    print("DARM EMPIRICAL LAB v0.1")
    print("=" * 72)
    print()

    print("BASELINE: LOCAL AUTHORIZATION")
    print("-" * 72)
    print("Trajectory:", " -> ".join(baseline["trajectory"]))
    print(
        "All transitions locally authorized:",
        baseline["all_transitions_locally_authorized"],
    )
    print("Final balance:", baseline["final_balance"])
    print("Total transferred:", baseline["total_transferred"])
    print("Trajectory limit:", baseline["trajectory_guarantee_limit"])
    print("Trajectory guarantee holds:", baseline["trajectory_guarantee_holds"])
    print("Counterexample:", baseline["counterexample"])
    print()

    print("STRENGTHENED BOUNDARY")
    print("-" * 72)
    print("Trajectory:", " -> ".join(strengthened["trajectory"]))
    print("Final balance:", strengthened["final_balance"])
    print("Total transferred:", strengthened["total_transferred"])
    print("Trajectory limit:", strengthened["trajectory_guarantee_limit"])
    print(
        "Trajectory guarantee holds:",
        strengthened["trajectory_guarantee_holds"],
    )
    print("Blocked event:", strengthened["blocked_event"])
    print(
        "Boundary enforces global invariant:",
        strengthened["boundary_enforces_global_invariant"],
    )
    print()
    print(
        "Interpretation: local transition authorization does not "
        "automatically establish a trajectory-level guarantee. "
        "The relevant global dependency must be represented and "
        "enforced if the guarantee is to be preserved."
    )


def main() -> None:
    baseline = run_baseline_experiment()
    strengthened = run_strengthened_boundary_experiment()
    print_report(baseline, strengthened)


if __name__ == "__main__":
    main()
