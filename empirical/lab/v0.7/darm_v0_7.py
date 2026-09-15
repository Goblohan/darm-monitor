from dataclasses import asdict, dataclass
import json
from pathlib import Path


INITIAL_BALANCE = 100
TRANSFER_AMOUNT = 50
TRAJECTORY_LIMIT = 50
MAX_DEPTH = 50

CONFIGURATIONS = ("A", "B", "C")

DEPENDENCY_REQUIREMENTS = {
    "transfer": frozenset({"authA"}),
    "transfer_alt": frozenset({"authB"}),
}

BOUNDARY_COVERAGE = {
    "A": frozenset({"authA"}),
    "B": frozenset({"authA"}),
    "C": frozenset({"authA", "authB"}),
}

EVENTS = (
    "request",
    "transfer",
    "transfer_alt",
    "revoke",
    "refresh_credential",
    "connect",
    "disconnect",
    "approve",
    "clear_approval",
)

CONFIGURATION_EVENTS = {
    "A": tuple(event for event in EVENTS if event != "transfer_alt"),
    "B": EVENTS,
    "C": EVENTS,
}


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


def dependency_requirements(event: Event) -> frozenset[str]:
    return DEPENDENCY_REQUIREMENTS.get(event.name, frozenset())


def boundary_covers(configuration: str, event: Event) -> bool:
    required = dependency_requirements(event)
    coverage = BOUNDARY_COVERAGE[configuration]
    return bool(required) and required.issubset(coverage)


def locally_authorized(state: State, event: Event) -> bool:
    if event.name in ("transfer", "transfer_alt"):
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
    configuration: str | None = None,
) -> Transition:
    authorized = locally_authorized(state, event)
    executed = authorized

    if (
        configuration is not None
        and boundary_covers(configuration, event)
        and authorized
        and state.transferred + TRANSFER_AMOUNT > TRAJECTORY_LIMIT
    ):
        executed = False

    after = state

    if executed:
        if event.name in ("transfer", "transfer_alt"):
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


def reachable_graph(
    configuration: str,
) -> tuple[set[State], dict]:
    states = {INITIAL_STATE}
    frontier = {INITIAL_STATE}
    graph = {}
    depth = 0

    while frontier and depth < MAX_DEPTH:
        next_frontier = set()

        for state in frontier:
            transitions = []

            for name in CONFIGURATION_EVENTS[configuration]:
                event = Event(name)

                if not locally_authorized(state, event):
                    continue

                transition = step(
                    state,
                    event,
                    configuration=configuration,
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


def changes_guarantee_state(
    transition: Transition,
) -> bool:
    return transition.after.transferred != transition.before.transferred


def semantically_relevant_dependencies(
    states: set[State],
    graph: dict[State, list[Transition]],
) -> frozenset[str]:
    relevant = set()

    for state in states:
        for transition in graph.get(state, []):
            if not transition.executed:
                continue

            if not changes_guarantee_state(transition):
                continue

            relevant.update(
                dependency_requirements(transition.event)
            )

    return frozenset(relevant)


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


def analyze(configuration: str) -> dict:
    if configuration not in CONFIGURATIONS:
        raise ValueError(f"Unknown configuration: {configuration}")

    event_names = CONFIGURATION_EVENTS[configuration]

    declared_dependency_surface = frozenset(
        dependency
        for event_name in event_names
        for dependency in DEPENDENCY_REQUIREMENTS.get(
            event_name,
            frozenset(),
        )
    )

    boundary_coverage = BOUNDARY_COVERAGE[configuration]

    states, graph = reachable_graph(
        configuration=configuration
    )

    semantic_dependency_surface = (
        semantically_relevant_dependencies(
            states,
            graph,
        )
    )

    dependency_surface_consistent = (
        declared_dependency_surface
        == semantic_dependency_surface
    )

    dependency_surface = semantic_dependency_surface

    grbs = dependency_surface.issubset(boundary_coverage)

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
        "configuration": configuration,
        "event_alphabet": list(event_names),
        "dependency_surface": sorted(dependency_surface),
        "declared_dependency_surface": sorted(
            declared_dependency_surface
        ),
        "semantic_dependency_surface": sorted(
            semantic_dependency_surface
        ),
        "dependency_surface_consistent": (
            dependency_surface_consistent
        ),
        "boundary_coverage": sorted(boundary_coverage),
        "grbs": grbs,
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
    analyses = {
        configuration: analyze(configuration)
        for configuration in CONFIGURATIONS
    }

    configuration_a = analyses["A"]
    configuration_b = analyses["B"]
    configuration_c = analyses["C"]

    output = {
        "version": "v0.7",
        "experiment": "dependency_expansion_and_boundary_coverage",
        "model": {
            "initial_state": asdict(INITIAL_STATE),
            "event_alphabet": list(EVENTS),
            "event_alphabet_size": len(EVENTS),
            "configuration_event_alphabets": {
                configuration: list(CONFIGURATION_EVENTS[configuration])
                for configuration in CONFIGURATIONS
            },
            "initial_balance": INITIAL_BALANCE,
            "transfer_amount": TRANSFER_AMOUNT,
            "trajectory_limit": TRAJECTORY_LIMIT,
            "maximum_depth": MAX_DEPTH,
            "invariant": "transferred <= TRAJECTORY_LIMIT",
            "dependency_requirements": {
                event: sorted(dependencies)
                for event, dependencies in DEPENDENCY_REQUIREMENTS.items()
            },
            "boundary_coverage": {
                configuration: sorted(coverage)
                for configuration, coverage in BOUNDARY_COVERAGE.items()
            },
        },
        "configurations": analyses,
        "comparison": {
            "dependency_expanded": (
                configuration_a["dependency_surface"]
                != configuration_b["dependency_surface"]
            ),
            "coverage_expanded": (
                configuration_b["boundary_coverage"]
                != configuration_c["boundary_coverage"]
            ),
            "grbs_changed": (
                configuration_a["grbs"]
                != configuration_b["grbs"]
                or configuration_b["grbs"]
                != configuration_c["grbs"]
            ),
            "winning_region_changed": (
                configuration_a["adversarial_winning_states"]
                != configuration_b["adversarial_winning_states"]
                or configuration_b["adversarial_winning_states"]
                != configuration_c["adversarial_winning_states"]
            ),
            "A_to_B": {
                "dependency_surface_before": configuration_a[
                    "dependency_surface"
                ],
                "dependency_surface_after": configuration_b[
                    "dependency_surface"
                ],
                "boundary_coverage_before": configuration_a[
                    "boundary_coverage"
                ],
                "boundary_coverage_after": configuration_b[
                    "boundary_coverage"
                ],
                "grbs_before": configuration_a["grbs"],
                "grbs_after": configuration_b["grbs"],
                "winning_states_before": configuration_a[
                    "adversarial_winning_states"
                ],
                "winning_states_after": configuration_b[
                    "adversarial_winning_states"
                ],
                "initial_state_winning_before": configuration_a[
                    "initial_state_winning"
                ],
                "initial_state_winning_after": configuration_b[
                    "initial_state_winning"
                ],
            },
            "B_to_C": {
                "dependency_surface_before": configuration_b[
                    "dependency_surface"
                ],
                "dependency_surface_after": configuration_c[
                    "dependency_surface"
                ],
                "boundary_coverage_before": configuration_b[
                    "boundary_coverage"
                ],
                "boundary_coverage_after": configuration_c[
                    "boundary_coverage"
                ],
                "grbs_before": configuration_b["grbs"],
                "grbs_after": configuration_c["grbs"],
                "winning_states_before": configuration_b[
                    "adversarial_winning_states"
                ],
                "winning_states_after": configuration_c[
                    "adversarial_winning_states"
                ],
                "initial_state_winning_before": configuration_b[
                    "initial_state_winning"
                ],
                "initial_state_winning_after": configuration_c[
                    "initial_state_winning"
                ],
            },
        },
    }

    output_path = Path(__file__).with_name("results.json")
    output_path.write_text(
        json.dumps(output, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )

    print("DARM EMPIRICAL LAB v0.7")
    print("Experiment: dependency expansion and boundary coverage")
    print()

    for configuration in CONFIGURATIONS:
        result = analyses[configuration]

        print(f"CONFIGURATION {configuration}")
        print(
            f"Event alphabet size: "
            f"{len(result['event_alphabet'])}"
        )
        print(
            f"Dependency surface: "
            f"{result['dependency_surface']}"
        )
        print(
            f"Boundary coverage: "
            f"{result['boundary_coverage']}"
        )
        print(f"GRBS: {result['grbs']}")
        print(
            f"Reachable states: "
            f"{result['reachable_states']}"
        )
        print(
            f"Authorized transitions: "
            f"{result['authorized_transitions']}"
        )
        print(
            f"Blocked transitions: "
            f"{result['blocked_transitions']}"
        )
        print(
            f"Violating states: "
            f"{result['violating_states']}"
        )
        print(
            f"Adversarial winning states: "
            f"{result['adversarial_winning_states']}"
        )
        print(
            f"Initial state winning: "
            f"{result['initial_state_winning']}"
        )
        print(
            f"Winning witnesses: "
            f"{result['winning_witnesses']}"
        )
        print()

    print("A -> B: DEPENDENCY EXPANSION")
    print(
        f"GRBS: "
        f"{configuration_a['grbs']} -> "
        f"{configuration_b['grbs']}"
    )
    print(
        f"Adversarial winning states: "
        f"{configuration_a['adversarial_winning_states']} -> "
        f"{configuration_b['adversarial_winning_states']}"
    )
    print(
        f"Initial state winning: "
        f"{configuration_a['initial_state_winning']} -> "
        f"{configuration_b['initial_state_winning']}"
    )
    print()

    print("B -> C: BOUNDARY COVERAGE EXPANSION")
    print(
        f"GRBS: "
        f"{configuration_b['grbs']} -> "
        f"{configuration_c['grbs']}"
    )
    print(
        f"Adversarial winning states: "
        f"{configuration_b['adversarial_winning_states']} -> "
        f"{configuration_c['adversarial_winning_states']}"
    )
    print(
        f"Initial state winning: "
        f"{configuration_b['initial_state_winning']} -> "
        f"{configuration_c['initial_state_winning']}"
    )


if __name__ == "__main__":
    main()
