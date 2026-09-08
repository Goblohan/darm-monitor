# R3b / AG-ATTACK-1 Finding — GRBS vs. Assume-Guarantee: a Precise Localization

> **Evidence status: `Proved`** for the formal statements (machine-checked in
> `GRBS/AGAttack.lean` and `GRBS/AGBypass.lean`; both principal theorems depend
> on ZERO axioms — not even `propext` — and contain no `sorry`). The prior-art
> interpretation is `Argued`.

## The question

R3 established GRBS is a strict weakening of complete mediation via semantic
sensitivity (`FalsifiableVia`). R3b asked the harder, deflationary question: is
the GRBS transfer judgment merely ordinary assume-guarantee (AG) contract
reasoning in new notation? Following the falsification discipline, we tried to
KILL the novelty claim by reducing GRBS to AG, and we gave AG maximal fair power
rather than building a weak-AG strawman.

## Methodological discipline (enforced structurally in Lean)

* `AGSatisfies` and `GRBS` are semantically independent: the AG contract sees the
  system's trace/interface semantics and the fixed guarantee; GRBS additionally
  sees the coverage topology.
* `cov` is NOT a function of traces — separate `System` fields, no definitional
  link. Whether behavior determines coverage is a THEOREM to test, not an axiom.
* The guarantee `g` is held FIXED across the two witness systems, closing the
  "guarantee-indexing escape hatch" (an assumption chosen per-guarantee could
  otherwise smuggle the GRBS verdict through the choice of assumption).
* Admissibility is fixed INDEPENDENTLY of the witness channel: an environment is
  admissible iff it respects the interface. The exclusion of the exploiting
  adversary is a consequence of that fixed policy, not a gerrymander.

## Result 1 — AG-0 (environment-only) diagnostic floor

With a fixed guarantee, two systems that are trace-identical but coverage-
different are AG-indistinguishable (Lemma: AG is blind to any difference
invisible in traces) while GRBS distinguishes them
(`GRBS.AGAttack.separation`, zero axioms).

This is recorded NARROWLY and diagnostically. It is weak on its own: the
coverage field in that model is causally inert (it affects no trace), so "AG
cannot see it" is unremarkable — nothing can. A referee would rightly object
that inert coverage is decoration, not a safety property. AG-0 is a scaffolding
sanity check, not evidence.

## Result 2 — 2b: the structural isolation theorem (the real result)

We strengthened the model to separate THREE objects, grounding the separation in
hardware-security mechanics rather than an abstract variable:

* `interfaceTraces` — software-contract-visible behavior (what AG observes);
* `physicalStep`    — execution across the hardware substrate footprint
                      (what a below-interface adversary can drive);
* `cov`             — coverage topology (what GRBS sees).

The witness channel `d` (an unmediated DMA / direct-register / shared-clock class
bypass) lies in the PHYSICAL FOOTPRINT of both systems but OUTSIDE the interface.
It is:

* structurally present (`depB` holds — it can physically produce a trace);
* unreachable by any interface-respecting (admissible) environment (so the two
  systems are interface-identical and AG-over-the-full-admissible-class cannot
  distinguish them);
* a PROVED LIVE HAZARD, not inert: an explicit physical (interface-violating)
  adversary drives `d` to a real guarantee violation in the uncovered system
  (`physical_exploit_S2`).

**Theorem `grbs_isolates_latent_bypass` (zero axioms).** For the fixed guarantee
and every behaviorally-grounded AG assumption:

1. AG-over-admissible gives the two systems the identical verdict (interface-
   indistinguishable, bypass below the interface);
2. GRBS distinguishes them (one mediates the bypass, the other does not);
3. the bypass is a live physical hazard (the non-inertness witness).

## The verdict — a precise localization, not a one-sided claim

GRBS is **NOT reducible** to AG-over-the-admissible-class, and the reason is
exact:

> AG contract reasoning proves safety UNDER THE ASSUMPTION that environments
> respect the software interface. GRBS additionally requires mediation of
> physical channels present in the substrate footprint but ABSENT from the
> interface contract. The two judgments provably diverge exactly on LATENT
> HARDWARE BYPASS — the DMA / register / clock class of channel.

Combined with the (informal) 2a direction — a coverage difference that manifests
under some ADMISSIBLE adversary IS behaviorally recoverable, so AG-with-adv would
catch it — the complete picture is a biconditional localization:

> **GRBS coincides with AG-over-admissible on ABOVE-interface coverage, and
> strictly exceeds it on BELOW-interface (latent physical) coverage. The boundary
> between reduction and separation is exactly the interface/footprint boundary.**

DARM's contribution over assume-guarantee reasoning is therefore not a new logic
and not mere renotation. It is, precisely: **the enforcement of complete
mediation on the hardware substrate beneath the software-contract abstraction** —
zero-trust against adversaries the interface-contract threat model excludes by
assumption. This is exactly the DMA/IOMMU "locally verified, globally rejected"
scenario that motivated the program, now a machine-checked separation theorem.

## Consequence for the paper's claim

State GRBS's relationship to AG as: *GRBS coincides with assume-guarantee
contract satisfaction over the interface-respecting environment class, and
diverges from it exactly on the mediation of below-interface physical channels
(latent hardware bypass). Against adversaries bound by the software interface,
the judgments agree; against adversaries exploiting the physical substrate, GRBS
is strictly stronger.* This is a narrow, precise, defensible novelty claim — not
"AG cannot express GRBS" (false: unrestricted guarantee-indexed AG can) and not
"GRBS is a fundamentally new assurance logic" (overreach), but a formal
localization of exactly where guarantee-relative physical mediation exceeds
contract reasoning.

## Honest limits and open threads

* **2a is argued, not yet formalized.** The reduction half — that above-interface
  coverage is behaviorally recoverable by AG-with-admissible-adversary — is
  reasoned but not machine-checked. Formalizing it would complete the
  biconditional as a theorem pair.
* **One substrate model.** The below-interface hazard is modeled concretely
  (footprint vs. interface, one bypass channel). A richer substrate (multiple
  channels, partial mediation, timing) could refine the boundary.
* **Unrestricted guarantee-indexed AG (AG-2) trivially reduces GRBS** and is not
  claimed otherwise: an arbitrary predicate `A(G,E) := GRBS(...)` encodes it.
  The separation is specifically against BEHAVIORALLY-GROUNDED AG over the
  admissible class — which is the honest, fair notion of "ordinary AG."
