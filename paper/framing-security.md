# Framing: security venue

Target: IEEE S&P, USENIX Security, ACM CCS.

## Abstract (draft)

Agents that act through tools need a boundary that decides, executes and
records each action, and whose guarantees survive a compromised agent. We
present a reference monitor for agent tool use whose every stated guarantee is
tied, mechanically, to a machine-checked theorem, a runtime test, and a stated
limit. We show exactly when authorization can be complete, prove that no rule
over proposals alone closes a redemption race that affects deployed intent
systems, and establish execution identity by two complementary mechanisms, each
defeating an attack the other misses. [composition results withheld pending
disclosure]

## Section order

1. Introduction: the compromised-agent threat; what goes wrong without
   completeness; contributions.
2. Threat model and guarantees (core 1, core 7's two-way check).
3. Attacks and what stops them: the redemption race (core 2), the move and the
   replay (core 5), composition faults (core 6).
4. Why the guarantees hold: completeness (core 2, 3), from authorization to
   effect (core 4), identity (core 5), with theorems as backing.
5. Evaluation: probes, mutation gate, metrics (core 7); composition (core 6).
6. Limits (core 8). Related work. Conclusion.
