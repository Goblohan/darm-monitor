from dataclasses import asdict, dataclass
import json
from pathlib import Path


INITIAL_BALANCE = 100
TRANSFER_AMOUNT = 50
TRAJECTORY_LIMIT = 50
MAX_DEPTH = 50

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
    executed: bool


INITIAL_STATE = State(
    balance=INITIAL_BALANCE,
    permission=True,
    credential=True,
    network=False,
    approval=False,
    transferred=0,
)


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


def step(
    state: State,
    event: Event,
    strengthened_boundary: bool = False,
) -> Transition:
    authorized = locally_authorized(state, event)
    executed = authorized

    if (
        strengthened_boundary
        and event.name == "transfer"
        and authorized
        and state.transferred + TRANSFER_AMOUNT > TRAJECTORY_LIMIT
    ):
        executed = False

    after = state

    if executed:
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
        executed=executed,
    )


def shortest_trace_to_state(
    target: State,
    strengthened_boundary: bool,
) -> list[dict] | None:
    frontier = [(INITIAL_STATE, [])]
    seen = {INITIAL_STATE}

    while frontier:
        state, trace = frontier.pop(0)

        if state == target:
            return trace

        for name in EVENTS:
            event = Event(name)

            if not locally_authorized(state, event):
                continue

            transition = step(
                state,
                event,
                strengthened_boundary=strengthened_boundary,
            )

            nxt = transition.after

            if nxt in seen:
                continue

            seen.add(nxt)

            next_trace = trace + [
                {
                    "step": len(trace) + 1,
                    "event": name,
                    "authorized": transition.authorized,
                    "executed": transition.executed,
                    "before": asdict(state),
                    "after": asdict(nxt),
                }
            ]

            frontier.append((nxt, next_trace))

    return None


def analyze(strengthened_boundary: bool) -> dict:
    states = {INITIAL_STATE}
    frontier = {INITIAL_STATE}

    depth_counts = {0: 1}

    authorized_transitions = 0
    blocked_transitions = 0
    first_entry_violations = []
    all_violating_transitions = []

    first_violation_depth = None

    for depth in range(1, MAX_DEPTH + 1):
        next_frontier = set()

        for state in frontier:
            for name in EVENTS:
                event = Event(name)

                if not locally_authorized(state, event):
                    continue

                authorized_transitions += 1

                transition = step(
                    state,
                    event,
                    strengthened_boundary=strengthened_boundary,
                )

                if transition.authorized and not transition.executed:
                    blocked_transitions += 1

                before_safe = (
                    state.transferred <= TRAJECTORY_LIMIT
                )
                after_unsafe = (
                    transition.after.transferred > TRAJECTORY_LIMIT
                )

                if after_unsafe:
                    all_violating_transitions.append(
                        {
                            "depth": depth,
                            "before": asdict(state),
                            "event": name,
                            "after": asdict(transition.after),
                        }
                    )

                    if before_safe:
                        first_entry_violations.append(
                            {
                                "depth": depth,
                                "before": asdict(state),
                                "event": name,
                                "after": asdict(transition.after),
                            }
                        )

                        if first_violation_depth is None:
                            first_violation_depth = depth

                nxt = transition.after

                if nxt not in states:
                    states.add(nxt)
                    next_frontier.add(nxt)

        depth_counts[depth] = len(next_frontier)

        frontier = next_frontier

        if not frontier:
            break

    violating_states = [
        asdict(state)
        for state in states
        if state.transferred > TRAJECTORY_LIMIT
    ]

    return {
        "strengthened_boundary": strengthened_boundary,
        "fixed_point_states": len(states),
        "authorized_transitions": authorized_transitions,
        "blocked_transitions": blocked_transitions,
        "all_violating_transitions": len(
            all_violating_transitions
        ),
        "first_entry_violations": len(
            first_entry_violations
        ),
        "first_violation_depth": first_violation_depth,
        "violating_states": len(violating_states),
        "depth_counts": depth_counts,
        "first_entry_violation": (
            first_entry_violations[0]
            if first_entry_violations
            else None
        ),
        "states": states,
    }


def representative_trace(
    analysis_result: dict,
    strengthened_boundary: bool,
) -> list[dict] | None:
    violation = analysis_result["first_entry_violation"]

    if violation is None:
        return None

    target = State(**violation["after"])

    return shortest_trace_to_state(
        target,
        strengthened_boundary=strengthened_boundary,
    )


def main() -> None:
    baseline = analyze(False)
    strengthened = analyze(True)

    baseline_trace = representative_trace(
        baseline,
        strengthened_boundary=False,
    )

    strengthened_target = State(
        balance=50,
        permission=True,
        credential=True,
        network=True,
        approval=True,
        transferred=50,
    )

    strengthened_trace = shortest_trace_to_state(
        strengthened_target,
        strengthened_boundary=True,
    )

    blocked_transfer = {
        "before": asdict(strengthened_target),
        "event": "transfer",
        "authorized": True,
        "executed": False,
        "after": asdict(strengthened_target),
    }

    output = {
        "version": "v0.5",
        "experiment": "exhaustive_bounded_reachability_analysis",
        "model": {
            "initial_state": asdict(INITIAL_STATE),
            "event_alphabet": list(EVENTS),
            "event_alphabet_size": len(EVENTS),
            "initial_balance": INITIAL_BALANCE,
            "transfer_amount": TRANSFER_AMOUNT,
            "trajectory_limit": TRAJECTORY_LIMIT,
            "maximum_depth": MAX_DEPTH,
        },
        "baseline": {
            key: value
            for key, value in baseline.items()
            if key != "states"
        },
        "strengthened": {
            key: value
            for key, value in strengthened.items()
            if key != "states"
        },
        "comparison": {
            "baseline_fixed_point_states": baseline[
                "fixed_point_states"
            ],
            "strengthened_fixed_point_states": strengthened[
                "fixed_point_states"
            ],
            "baseline_first_entry_violations": baseline[
                "first_entry_violations"
            ],
            "strengthened_first_entry_violations": strengthened[
                "first_entry_violations"
            ],
            "baseline_first_violation_depth": baseline[
                "first_violation_depth"
            ],
            "strengthened_first_violation_depth": strengthened[
                "first_violation_depth"
            ],
            "strengthened_blocked_transitions": strengthened[
                "blocked_transitions"
            ],
            "baseline_violating_states": baseline[
                "violating_states"
            ],
            "strengthened_violating_states": strengthened[
                "violating_states"
            ],
        },
        "representative_baseline_trace": baseline_trace,
        "representative_strengthened_trace": strengthened_trace,
        "representative_blocked_transfer": blocked_transfer,
    }

    output_path = Path(__file__).with_name("results.json")
    output_path.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    print("DARM EMPIRICAL LAB v0.5")
    print("Experiment: exhaustive bounded reachability analysis")
    print()
    print("BASELINE")
    print(
        f"Fixed-point states: "
        f"{baseline['fixed_point_states']}"
    )
    print(
        f"Authorized transitions: "
        f"{baseline['authorized_transitions']}"
    )
    print(
        f"First-entry violations: "
        f"{baseline['first_entry_violations']}"
    )
    print(
        f"All transitions from violating states: "
        f"{baseline['all_violating_transitions']}"
    )
    print(
        f"First violation depth: "
        f"{baseline['first_violation_depth']}"
    )
    print(
        f"Violating states: "
        f"{baseline['violating_states']}"
    )
    print()
    print("STRENGTHENED BOUNDARY")
    print(
        f"Fixed-point states: "
        f"{strengthened['fixed_point_states']}"
    )
    print(
        f"Authorized transitions: "
        f"{strengthened['authorized_transitions']}"
    )
    print(
        f"First-entry violations: "
        f"{strengthened['first_entry_violations']}"
    )
    print(
        f"Blocked transitions: "
        f"{strengthened['blocked_transitions']}"
    )
    print(
        f"First violation depth: "
        f"{strengthened['first_violation_depth']}"
    )
    print(
        f"Violating states: "
        f"{strengthened['violating_states']}"
    )
    print()
    print(f"Results written to {output_path}")


if __name__ == "__main__":
    main()
