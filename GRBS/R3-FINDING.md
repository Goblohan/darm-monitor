# R3 Finding — GRBS Survives the Novelty Attack, in Corrected Form

> **Evidence status: `Proved` (for the formal claims) / `Argued` (for the
> prior-art comparison).** The formal statements below are machine-checked in
> `GRBS/GRBSStructural.lean` (axiom trace `[propext]` only — fully constructive,
> no `Classical.choice`, no `sorryAx`). The comparison against complete mediation
> is established; the comparison against assume-guarantee contracts is argued but
> not yet formalized and is marked open.

## The experiment

R3 asked whether `Dependence` — the one assumed Frame field in the R1 kernel —
could be *proved* from a genuinely structural definition of `dep`, or whether it
collapses into a renotation of complete mediation. We built a concrete structural
model (state = components → bits, structural `dep` = mentions ∩ writable, semantic
`Safe` = predicate on the run result) and attempted to prove the honest
structural target, `structural_exploitability`. We let the proof decide the
outcome rather than steering it.

## The result (Outcome 2, machine-checked)

**The R1 `Dependence` is too strong and is not provable from structure.** A
guarantee can *mention* a component (list it in its footprint) yet be *insensitive*
to it — the model's `predRespectsMentions` explicitly permits vacuous mention. So
structural dependency does **not** entail exploitability:

> `depS g s d`  ⊬  `FalsifiableVia g s d`

The provable target requires an added hypothesis, `FalsifiableVia` ("some value of
`d` makes the guarantee false"), and under it the exploit is constructive:

> **Theorem (`structural_exploitability`, axiom trace `[propext]`).**
> If `d` is a structural dependency of `g` in `s` and `g` is genuinely
> falsifiable via `d`, then there is a single-step adversarial trace that
> perturbs `d` and violates `g`.

## What this establishes about the novelty claim

**1. GRBS is not a renotation of complete mediation.**
Complete mediation requires mediating *every* access to a protected object. The
proof shows transfer failure is driven only by accesses to dependencies that are
**both** in the guarantee's structural footprint **and** ones the guarantee is
genuinely sensitive to (`FalsifiableVia`). Accesses to unmentioned or
insensitively-mentioned components need no mediation. The set that must be
covered is therefore strictly smaller than "everything":

> mediate only  `{ d : dep(g,s) d  ∧  FalsifiableVia g s d }`,  not the whole
> interface.

This is a genuine, formalized weakening of the complete-mediation requirement.

**2. The distinguishing principle is guarantee-SENSITIVITY-relative coverage,
not guarantee-DEPENDENCY-relative coverage.**
The R1 framing ("uncovered structural dependency ⇒ failure") was the wrong
principle. The corrected, machine-checked principle is:

> **uncovered dependency to which the guarantee is genuinely sensitive ⇒ failure.**

`FalsifiableVia` — semantic sensitivity — is the actual load-bearing hypothesis.
This corrects and sharpens the calculus. The R1 kernel's `Dependence` field
should be understood as the *fused* consequence of coverage plus sensitivity,
and future work should re-derive the R1 necessity theorem with `FalsifiableVia`
made explicit.

**3. Coverage and sensitivity are orthogonal contributors to transfer failure.**
A second, sharp finding: `¬cov` is **not used** in the structural exploit
construction. The unsafe trace is produced from `FalsifiableVia` alone. In this
model, therefore:

> * Coverage gates ACCESS — it lives in the environment/trace layer (an uncovered
>   channel is what makes the adversary *admissible*).
> * Sensitivity gates EFFECT — `FalsifiableVia` is what makes an admitted
>   perturbation *violate* the guarantee.

The R1 Frame fuses these via `Envs`. The structural decomposition shows GRBS's
`Dep \ Cov` set-difference is really:

> `{ dependencies the guarantee is sensitive to }  ∩  { reachable via an uncovered channel }`

Neither factor alone forces failure; their conjunction does. This is a cleaner
statement of the calculus than either R1 or the informal GRBS framing gave.

## Honest limits and open comparisons

* **One model.** The finding is proved in a concrete state/bit/write model. It is
  strong evidence, not a universal impossibility. A more general model (richer
  values, multi-step guarantees, temporal predicates) could expose further
  conditions. Marked: `Proved (this model)`.

* **Assume-guarantee contracts — comparison OPEN.** The sharpest remaining
  novelty question: can `Cov(B,L,S)` be expressed as an assume-guarantee
  *assumption*, making `transfer_fails_of_uncovered` an instance of contract
  violation? If yes, GRBS is a specialization of AG reasoning; if the
  sensitivity/coverage orthogonality resists AG encoding, it is genuinely
  distinct. This is not yet formalized and is the recommended next R3 step.

* **Non-interference.** Whether `Perturbs`/`Safe` reduce to an interference
  relation is unexamined here (the main line's NR1 already separates enforcement
  from noninterference; this needs cross-checking).

## Consequence for the paper

The GRBS contribution should be stated as: *a machine-checked calculus in which
assurance transfer fails exactly when a guarantee is genuinely sensitive to a
dependency reachable through an unmediated channel — a strict, formalized
weakening of complete mediation via guarantee-sensitivity-relative coverage.*
The claim is **not** "structural dependency uncovered ⇒ failure" (false), and is
**not** a renotation of complete mediation (disproved by the strict weakening).
The assume-guarantee comparison must be either closed or explicitly left open in
the paper's related-work section.

## Verdict

The novelty claim **survives the attack, in corrected form.** The correction —
sensitivity-relative rather than dependency-relative coverage, and the
coverage/sensitivity orthogonality — is itself a sharper result than the original
claim, and it was forced by the formalization rather than assumed. That is the
gate working as intended.
