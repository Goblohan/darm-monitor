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


def reachable_graph(strengthened_boundary: bool) -> tuple[set[State], dict]:
    states = {INITIAL_STATE}
    frontier = {INITIAL_STATE}
    graph = {}
    depth = 0

    while frontier and depth < MAX_DEPTH:
        next_frontier = set()

        for state in frontier:
            transitions = []

            for name in EVENTS:
                event = Event(name)

                if not locally_authorized(state, event):
                    continue

                transition = step(
                    state,
                    event,
                    strengthened_boundary=strengthened_boundary,
                )

                transitions.append(transition)

                if transition.after not in states:
                    states.add(transition.after)
                    next_frontier.add(transition.after)

            graph[state] = transitions

        frontier = next_frontier
        depth += 1

    return states, graph


def violating(state: State) -> bool:
    return state.transferred > TRAJECTORY_LIMIT


def adversarial_winning_region(
    states: set[State],
    graph: dict[State, list[Transition]],
) -> tuple[
    set[State],
    dict[State, Transition],
    dict[State, int],
]:
    winning = {
        state
        for state in states
        if violating(state)
    }

    ranks: dict[State, int] = {
        state: 0
        for state in winning
    }

    witness: dict[State, Transition] = {}

    current_rank = 0

    while True:
        candidates = []

        for state in sorted(
            states,
            key=lambda item: (
                item.transferred,
                item.balance,
                item.permission,
                item.credential,
                item.network,
                item.approval,
            ),
        ):
            if state in winning:
                continue

            eligible = [
                transition
                for transition in graph.get(state, [])
                if transition.executed
                and transition.after in winning
            ]

            if not eligible:
                continue

            eligible.sort(
                key=lambda transition: (
                    ranks[transition.after],
                    transition.event.name,
                    asdict(transition.after).__repr__(),
                )
            )

            candidates.append(
                (state, eligible[0])
            )

        if not candidates:
            break

        current_rank += 1

        for state, transition in candidates:
            if state in winning:
                continue

            winning.add(state)
            ranks[state] = current_rank
            witness[state] = transition

    return winning, witness, ranks


def shortest_trace_to_state(
    target: State,
    graph: dict[State, list[Transition]],
) -> list[dict] | None:
    frontier = [(INITIAL_STATE, [])]
    seen = {INITIAL_STATE}

    while frontier:
        state, trace = frontier.pop(0)

        if state == target:
            return trace

        for transition in graph.get(state, []):
            nxt = transition.after

            if nxt in seen:
                continue

            seen.add(nxt)

            frontier.append(
                (
                    nxt,
                    trace
                    + [
                        {
                            "step": len(trace) + 1,
                            "event": transition.event.name,
                            "authorized": transition.authorized,
                            "executed": transition.executed,
                            "before": asdict(transition.before),
                            "after": asdict(transition.after),
                        }
                    ],
                )
            )

    return None


def winning_strategy_trace(
    graph: dict[State, list[Transition]],
    witness: dict[State, Transition],
) -> list[dict] | None:
    state = INITIAL_STATE
    trace = []

    seen = set()

    while state not in seen:
        seen.add(state)

        if violating(state):
            return trace

        transition = witness.get(state)

        if transition is None:
            return None

        trace.append(
            {
                "step": len(trace) + 1,
                "event": transition.event.name,
                "authorized": transition.authorized,
                "executed": transition.executed,
                "before": asdict(transition.before),
                "after": asdict(transition.after),
            }
        )

        state = transition.after

    return None


def blocked_transitions(
    graph: dict[State, list[Transition]],
) -> list[dict]:
    blocked = []

    for transitions in graph.values():
        for transition in transitions:
            if transition.authorized and not transition.executed:
                blocked.append(
                    {
                        "before": asdict(transition.before),
                        "event": transition.event.name,
                        "authorized": transition.authorized,
                        "executed": transition.executed,
                        "after": asdict(transition.after),
                    }
                )

    return blocked


def analyze(strengthened_boundary: bool) -> dict:
    states, graph = reachable_graph(
        strengthened_boundary=strengthened_boundary
    )

    winning, witness, ranks = adversarial_winning_region(
        states,
        graph,
    )

    blocked = blocked_transitions(graph)

    winning_reachable_from_initial = INITIAL_STATE in winning

    strategy_trace = (
        winning_strategy_trace(graph, witness)
        if winning_reachable_from_initial
        else None
    )

    return {
        "strengthened_boundary": strengthened_boundary,
        "reachable_states": len(states),
        "authorized_transitions": sum(
            len(transitions)
            for transitions in graph.values()
        ),
        "blocked_transitions": len(blocked),
        "violating_states": sum(
            1
            for state in states
            if violating(state)
        ),
        "adversarial_winning_states": len(winning),
        "initial_state_winning": winning_reachable_from_initial,
        "winning_witnesses": len(witness),
        "blocked_transition_details": blocked,
        "strategy_trace": strategy_trace,
        "winning_state_details": [
            {
                "state": asdict(state),
                "violating": violating(state),
                "rank": ranks[state],
                "witness_event": (
                    witness[state].event.name
                    if state in witness
                    else None
                ),
                "witness_after": (
                    asdict(witness[state].after)
                    if state in witness
                    else None
                ),
            }
            for state in sorted(
                winning,
                key=lambda item: (
                    item.transferred,
                    item.balance,
                    item.permission,
                    item.credential,
                    item.network,
                    item.approval,
                ),
            )
        ],
    }


def main() -> None:
    baseline = analyze(False)
    strengthened = analyze(True)

    output = {
        "version": "v0.6",
        "experiment": "finite_adversarial_winning_region_analysis",
        "model": {
            "initial_state": asdict(INITIAL_STATE),
            "event_alphabet": list(EVENTS),
            "event_alphabet_size": len(EVENTS),
            "initial_balance": INITIAL_BALANCE,
            "transfer_amount": TRANSFER_AMOUNT,
            "trajectory_limit": TRAJECTORY_LIMIT,
            "maximum_depth": MAX_DEPTH,
            "invariant": "transferred <= TRAJECTORY_LIMIT",
        },
        "baseline": baseline,
        "strengthened": strengthened,
        "comparison": {
            "baseline_reachable_states": baseline[
                "reachable_states"
            ],
            "strengthened_reachable_states": strengthened[
                "reachable_states"
            ],
            "baseline_adversarial_winning_states": baseline[
                "adversarial_winning_states"
            ],
            "strengthened_adversarial_winning_states": strengthened[
                "adversarial_winning_states"
            ],
            "baseline_initial_state_winning": baseline[
                "initial_state_winning"
            ],
            "strengthened_initial_state_winning": strengthened[
                "initial_state_winning"
            ],
            "strengthened_blocked_transitions": strengthened[
                "blocked_transitions"
            ],
        },
    }

    output_path = Path(__file__).with_name("results.json")
    output_path.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    print("DARM EMPIRICAL LAB v0.6")
    print("Experiment: finite adversarial winning-region analysis")
    print()
    print("BASELINE")
    print(
        f"Reachable states: "
        f"{baseline['reachable_states']}"
    )
    print(
        f"Authorized transitions: "
        f"{baseline['authorized_transitions']}"
    )
    print(
        f"Violating states: "
        f"{baseline['violating_states']}"
    )
    print(
        f"Adversarial winning states: "
        f"{baseline['adversarial_winning_states']}"
    )
    print(
        f"Initial state winning: "
        f"{baseline['initial_state_winning']}"
    )
    print(
        f"Winning witnesses: "
        f"{baseline['winning_witnesses']}"
    )
    print()
    print("STRENGTHENED BOUNDARY")
    print(
        f"Reachable states: "
        f"{strengthened['reachable_states']}"
    )
    print(
        f"Authorized transitions: "
        f"{strengthened['authorized_transitions']}"
    )
    print(
        f"Violating states: "
        f"{strengthened['violating_states']}"
    )
    print(
        f"Adversarial winning states: "
        f"{strengthened['adversarial_winning_states']}"
    )
    print(
        f"Initial state winning: "
        f"{strengthened['initial_state_winning']}"
    )
    print(
        f"Blocked transitions: "
        f"{strengthened['blocked_transitions']}"
    )
    print()
    print(f"Results written to {output_path}")


if __name__ == "__main__":
    main()
