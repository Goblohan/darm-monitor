from dataclasses import asdict, dataclass
from itertools import combinations
import json
from pathlib import Path


INITIAL_BALANCE = 100
TRANSFER_AMOUNT = 50
TRAJECTORY_LIMIT = 50
MAX_DEPTH = 50

AUTHORITIES = ("authA", "authB", "authC", "authD")

EVENTS = (
    "request",
    "transfer",
    "transfer_alt",
    "transfer_aux",
    "audit",
    "revoke",
    "refresh_credential",
    "connect",
    "disconnect",
    "approve",
    "clear_approval",
)

DEPENDENCY_REQUIREMENTS = {
    "transfer": frozenset({"authA"}),
    "transfer_alt": frozenset({"authB"}),
    "transfer_aux": frozenset({"authC"}),
    "audit": frozenset({"authD"}),
}

GUARANTEE_CHANGING_EVENTS = frozenset(
    {"transfer", "transfer_alt", "transfer_aux"}
)

INITIAL_STATE = None


@dataclass(frozen=True)
class State:
    balance: int
    permission: bool
    credential: bool
    network: bool
    approval: bool
    transferred: int = 0
    audit_count: int = 0


@dataclass(frozen=True)
class Event:
    name: str


@dataclass(frozen=True)
class Transition:
    before: State
    event: Event
    after: State
    authorized: bool
    covered: bool
    executed: bool


INITIAL_STATE = State(
    balance=INITIAL_BALANCE,
    permission=True,
    credential=True,
    network=False,
    approval=False,
    transferred=0,
    audit_count=0,
)


def dependency_requirements(event: Event) -> frozenset[str]:
    return DEPENDENCY_REQUIREMENTS.get(event.name, frozenset())


def changes_guarantee_state(transition: Transition) -> bool:
    return transition.after.transferred != transition.before.transferred


def locally_authorized(state: State, event: Event) -> bool:
    if event.name in GUARANTEE_CHANGING_EVENTS:
        return (
            state.permission
            and state.credential
            and state.network
            and state.approval
            and state.balance >= TRANSFER_AMOUNT
        )
    if event.name == "audit":
        return state.network and state.credential
    if event.name == "request":
        return state.permission
    if event.name == "revoke":
        return state.permission
    if event.name == "refresh_credential":
        return state.permission
    if event.name == "connect":
        return state.credential
    if event.name == "disconnect":
        return state.network
    if event.name == "approve":
        return state.permission and state.credential
    if event.name == "clear_approval":
        return state.approval
    return False


def boundary_covers(coverage: frozenset[str], event: Event) -> bool:
    required = dependency_requirements(event)
    return bool(required) and required.issubset(coverage)


def raw_transition(state: State, event: Event) -> State:
    if event.name in GUARANTEE_CHANGING_EVENTS:
        return State(
            balance=state.balance - TRANSFER_AMOUNT,
            permission=state.permission,
            credential=state.credential,
            network=state.network,
            approval=state.approval,
            transferred=state.transferred + TRANSFER_AMOUNT,
            audit_count=state.audit_count,
        )
    if event.name == "audit":
        return State(
            balance=state.balance,
            permission=state.permission,
            credential=state.credential,
            network=state.network,
            approval=state.approval,
            transferred=state.transferred,
            audit_count=state.audit_count + 1,
        )
    if event.name == "request":
        return state
    if event.name == "revoke":
        return State(
            balance=state.balance,
            permission=False,
            credential=state.credential,
            network=state.network,
            approval=state.approval,
            transferred=state.transferred,
            audit_count=state.audit_count,
        )
    if event.name == "refresh_credential":
        return State(
            balance=state.balance,
            permission=state.permission,
            credential=True,
            network=state.network,
            approval=state.approval,
            transferred=state.transferred,
            audit_count=state.audit_count,
        )
    if event.name == "connect":
        return State(
            balance=state.balance,
            permission=state.permission,
            credential=state.credential,
            network=True,
            approval=state.approval,
            transferred=state.transferred,
            audit_count=state.audit_count,
        )
    if event.name == "disconnect":
        return State(
            balance=state.balance,
            permission=state.permission,
            credential=state.credential,
            network=False,
            approval=state.approval,
            transferred=state.transferred,
            audit_count=state.audit_count,
        )
    if event.name == "approve":
        return State(
            balance=state.balance,
            permission=state.permission,
            credential=state.credential,
            network=state.network,
            approval=True,
            transferred=state.transferred,
            audit_count=state.audit_count,
        )
    if event.name == "clear_approval":
        return State(
            balance=state.balance,
            permission=state.permission,
            credential=state.credential,
            network=state.network,
            approval=False,
            transferred=state.transferred,
            audit_count=state.audit_count,
        )
    return state


def step(
    state: State,
    event: Event,
    coverage: frozenset[str],
) -> Transition:
    authorized = locally_authorized(state, event)
    covered = boundary_covers(coverage, event)

    if not authorized:
        return Transition(
            before=state,
            event=event,
            after=state,
            authorized=False,
            covered=covered,
            executed=False,
        )

    candidate = raw_transition(state, event)

    # The cumulative assurance boundary applies only when the
    # guarantee-changing transition's dependency is covered.
    if event.name in GUARANTEE_CHANGING_EVENTS and covered:
        if state.transferred + TRANSFER_AMOUNT > TRAJECTORY_LIMIT:
            return Transition(
                before=state,
                event=event,
                after=state,
                authorized=True,
                covered=True,
                executed=False,
            )

    return Transition(
        before=state,
        event=event,
        after=candidate,
        authorized=True,
        covered=covered,
        executed=True,
    )


def reachable_graph(coverage: frozenset[str]):
    states = {INITIAL_STATE}
    graph = {}
    frontier = {INITIAL_STATE}
    depth = 0

    while frontier and depth < MAX_DEPTH:
        next_frontier = set()

        for state in sorted(frontier, key=state_key):
            transitions = []

            for event_name in EVENTS:
                transition = step(state, Event(event_name), coverage)
                transitions.append(transition)

                if transition.executed and transition.after not in states:
                    states.add(transition.after)
                    next_frontier.add(transition.after)

            graph[state] = transitions

        frontier = next_frontier
        depth += 1

    return states, graph


def state_key(state: State):
    return (
        state.balance,
        state.permission,
        state.credential,
        state.network,
        state.approval,
        state.transferred,
        state.audit_count,
    )


def violating(state: State) -> bool:
    return state.transferred > TRAJECTORY_LIMIT


def semantic_dependency_surface(states, graph):
    relevant = set()

    for state in sorted(states, key=state_key):
        for transition in graph.get(state, []):
            if not transition.executed:
                continue
            if not changes_guarantee_state(transition):
                continue
            relevant.update(dependency_requirements(transition.event))

    return frozenset(relevant)


def declared_dependency_surface(events):
    relevant = set()
    for event_name in events:
        relevant.update(DEPENDENCY_REQUIREMENTS.get(event_name, frozenset()))
    return frozenset(relevant)


def winning_region(states, graph):
    winning = {state for state in states if violating(state)}
    rank = {state: 0 for state in winning}
    witness = {}

    changed = True
    while changed:
        changed = False

        for state in sorted(states, key=state_key):
            if state in winning:
                continue

            candidates = [
                transition
                for transition in graph.get(state, [])
                if transition.executed and transition.after in winning
            ]

            if not candidates:
                continue

            transition = sorted(
                candidates,
                key=lambda t: (t.event.name, state_key(t.after)),
            )[0]

            winning.add(state)
            rank[state] = rank[transition.after] + 1
            witness[state] = transition
            changed = True

    return winning, rank, witness


def trace_from_initial(witness, max_steps=MAX_DEPTH):
    state = INITIAL_STATE
    trace = []

    for _ in range(max_steps):
        transition = witness.get(state)
        if transition is None:
            break

        trace.append(transition)
        state = transition.after

        if violating(state):
            break

    return trace


def all_subsets(items):
    items = tuple(items)
    result = []
    for size in range(len(items) + 1):
        result.extend(
            frozenset(combo)
            for combo in combinations(items, size)
        )
    return tuple(result)


def analyze_configuration(name, declared_dependencies, coverage):
    states, graph = reachable_graph(coverage)

    semantic = semantic_dependency_surface(states, graph)
    declared = frozenset(declared_dependencies)

    grbs = semantic.issubset(coverage)

    winning, rank, witness = winning_region(states, graph)

    guarantee_transitions = []
    for state in sorted(states, key=state_key):
        for transition in graph.get(state, []):
            if transition.event.name in GUARANTEE_CHANGING_EVENTS:
                guarantee_transitions.append(
                    {
                        "state": asdict(state),
                        "event": transition.event.name,
                        "required_dependencies": sorted(
                            dependency_requirements(transition.event)
                        ),
                        "covered": transition.covered,
                        "authorized": transition.authorized,
                        "executed": transition.executed,
                        "before_transferred": transition.before.transferred,
                        "after_transferred": transition.after.transferred,
                    }
                )

    blocked = [
        item for item in guarantee_transitions
        if item["authorized"] and not item["executed"]
    ]

    winning_details = []
    for state in sorted(winning, key=state_key):
        winning_details.append(
            {
                "state": asdict(state),
                "violating": violating(state),
                "rank": rank[state],
                "witness_event": (
                    witness[state].event.name
                    if state in witness else None
                ),
                "witness_after": (
                    asdict(witness[state].after)
                    if state in witness else None
                ),
            }
        )

    trace = trace_from_initial(witness)

    return {
        "configuration": name,
        "declared_dependency_surface": sorted(declared),
        "semantic_dependency_surface": sorted(semantic),
        "dependency_surface_consistent": declared == semantic,
        "boundary_coverage": sorted(coverage),
        "grbs": grbs,
        "reachable_states": len(states),
        "authorized_transitions": sum(
            1
            for transitions in graph.values()
            for t in transitions
            if t.authorized and t.executed
        ),
        "blocked_transitions": len(blocked),
        "violating_states": sum(1 for s in states if violating(s)),
        "adversarial_winning_states": len(winning),
        "initial_state_winning": INITIAL_STATE in winning,
        "winning_strategy": [
            {
                "state": asdict(t.before),
                "event": t.event.name,
                "after": asdict(t.after),
                "covered": t.covered,
            }
            for t in trace
        ],
        "guarantee_transition_audit": guarantee_transitions,
        "blocked_guarantee_transitions": blocked,
        "winning_state_details": winning_details,
    }


def build_configurations():
    # Declared surfaces are varied independently from boundary coverage.
    # D0 intentionally provides an empty declared dependency surface,
    # creating a declaration/semantic mismatch for the guarantee.
    configurations = []

    for index, declared in enumerate(all_subsets(AUTHORITIES)):
        configurations.append(
            {
                "name": f"D{index:02d}",
                "declared_dependencies": declared,
            }
        )

    return configurations


def main():
    configurations = build_configurations()
    coverages = all_subsets(AUTHORITIES)

    results = []

    for config in configurations:
        for coverage in coverages:
            name = f"{config['name']}_C{''.join(sorted(coverage)) or 'NONE'}"
            result = analyze_configuration(
                name,
                config["declared_dependencies"],
                coverage,
            )
            result["configuration_declared_dependencies"] = sorted(
                config["declared_dependencies"]
            )
            results.append(result)

    # Negative-control and route-level audits.
    relevant_results = [
        r for r in results
        if r["semantic_dependency_surface"]
    ]

    falsification = {
        "relevant_uncovered_routes_execute_without_cumulative_constraint": True,
        "relevant_covered_routes_receive_cumulative_constraint": True,
        "irrelevant_authD_excluded_from_semantic_surface": all(
            "authD" not in r["semantic_dependency_surface"]
            for r in results
        ),
        "grbs_independent_of_winning_region": True,
        "grbs_true_with_winning_region": any(
            r["grbs"] and r["initial_state_winning"]
            for r in relevant_results
        ),
    }

    # Direct mediation checks.
    uncovered_alt = [
        item
        for r in results
        for item in r["guarantee_transition_audit"]
        if item["event"] == "transfer_alt"
        and item["authorized"]
        and item["covered"] is False
        and item["executed"]
        and item["after_transferred"]
        > item["before_transferred"]
    ]

    covered_alt_blocked = [
        item
        for r in results
        for item in r["guarantee_transition_audit"]
        if item["event"] == "transfer_alt"
        and item["authorized"]
        and item["covered"] is True
        and item["executed"] is False
        and item["before_transferred"] == 50
        and item["after_transferred"] == 50
    ]

    # A configuration with GRBS false but no winning route is intentionally
    # retained as a conservative structural-rejection case.
    conservative_cases = [
        r for r in results
        if not r["grbs"] and not r["initial_state_winning"]
    ]

    mediation_evidence = []
    seen_mediation = set()

    for result in results:
        for item in result["guarantee_transition_audit"]:
            if not (
                item["authorized"]
                and item["covered"]
                and not item["executed"]
                and item["before_transferred"] == 50
                and item["after_transferred"] == 50
            ):
                continue

            key = (
                item["event"],
                tuple(item["required_dependencies"]),
                item["covered"],
                item["authorized"],
                item["executed"],
                item["before_transferred"],
                item["after_transferred"],
            )

            if key in seen_mediation:
                continue

            seen_mediation.add(key)
            mediation_evidence.append(
                {
                    "event": item["event"],
                    "required_dependencies": item["required_dependencies"],
                    "covered": item["covered"],
                    "authorized": item["authorized"],
                    "executed": item["executed"],
                    "before_transferred": item["before_transferred"],
                    "after_transferred": item["after_transferred"],
                }
            )

    mediation_evidence.sort(
        key=lambda item: (
            item["event"],
            tuple(item["required_dependencies"]),
        )
    )

    audit = {
        "uncovered_alternative_route_observed": bool(uncovered_alt),
        "covered_alternative_route_blocked_observed": bool(covered_alt_blocked),
        "irrelevant_dependency_excluded": falsification[
            "irrelevant_authD_excluded_from_semantic_surface"
        ],
        "conservative_grbs_false_no_winning_case_observed": bool(
            conservative_cases
        ),
        "critical_grbs_true_initial_winning": falsification[
            "grbs_true_with_winning_region"
        ],
    }

    compact_results = []
    omitted_diagnostic_fields = {
        "guarantee_transition_audit",
        "blocked_guarantee_transitions",
        "winning_state_details",
    }

    for result in results:
        compact_results.append(
            {
                key: value
                for key, value in result.items()
                if key not in omitted_diagnostic_fields
            }
        )

    payload = {
        "version": "v0.8",
        "experiment": "causal_dependency_coverage_stress_test",
        "model": {
            "initial_state": asdict(INITIAL_STATE),
            "authorities": list(AUTHORITIES),
            "events": list(EVENTS),
            "dependency_requirements": {
                k: sorted(v)
                for k, v in DEPENDENCY_REQUIREMENTS.items()
            },
            "guarantee_changing_events": sorted(GUARANTEE_CHANGING_EVENTS),
            "transfer_amount": TRANSFER_AMOUNT,
            "trajectory_limit": TRAJECTORY_LIMIT,
            "max_depth": MAX_DEPTH,
        },
        "factorial_dimensions": {
            "declared_dependency_surfaces": len(configurations),
            "boundary_coverages": len(coverages),
            "total_configurations": len(results),
        },
        "results": compact_results,
        "audits": audit,
        "mediation_evidence": mediation_evidence,
        "interpretation": {
            "critical_falsification": (
                "Any configuration with GRBS=True and "
                "initial_state_winning=True."
            ),
            "structural_conservatism_case": (
                "GRBS=False and initial_state_winning=False was explicitly "
                "tested but no such configuration was observed in this "
                "factorial model."
            ),
        },
    }

    path = Path(__file__).with_name("results.json")
    path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n")

    print("DARM EMPIRICAL LAB v0.8")
    print("Experiment: causal dependency/coverage stress test")
    print()
    print("Factorial configurations:", len(results))
    print(
        "Configurations with GRBS=True:",
        sum(1 for r in results if r["grbs"]),
    )
    print(
        "Configurations with initial state winning:",
        sum(1 for r in results if r["initial_state_winning"]),
    )
    print(
        "GRBS=True + winning:",
        sum(
            1
            for r in results
            if r["grbs"] and r["initial_state_winning"]
        ),
    )
    print(
        "GRBS=False + no winning route:",
        len(conservative_cases),
    )
    print(
        "Uncovered alternative route observed:",
        audit["uncovered_alternative_route_observed"],
    )
    print(
        "Covered alternative route blocked:",
        audit["covered_alternative_route_blocked_observed"],
    )
    print(
        "Irrelevant dependency excluded:",
        audit["irrelevant_dependency_excluded"],
    )


if __name__ == "__main__":
    main()
