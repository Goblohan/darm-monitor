# Hidden Defeater Witness

This note records a minimal Lean formalization of the claim that a visible true claim can induce reliance while a hidden boundary condition defeats target warrant.

Compiled modules:

- `HiddenDefeater`
- `HiddenDefeaterBoundary`

Key theorems:

- `GRBS.HiddenDefeater.material_secret_exists`
- `GRBS.HiddenDefeaterBoundary.deceptive_transfer_exists`
- `GRBS.HiddenDefeaterBoundary.source_warrant_without_target_warrant_with_confidence`

Lean reports that these theorems do not depend on any axioms.

Interpretation:

A local visible claim may remain true, and may induce confidence, while a fuller information state defeats authorized reliance in the target boundary. This gives a minimal formal witness for the DARM framing:

> Deception is confidence transfer without admissible warrant transfer.

## Converse-shaped materiality criterion

The module also proves a constructive converse-shaped theorem:

- `GRBS.HiddenDefeater.not_material_secret_blocks_reliance_refutation`

Interpretation:

If an atom is hidden, reliance holds before disclosure, and the atom is not material, then disclosure cannot refute reliance. Constructively this is stated as `¬ ¬ relies Ir`, avoiding classical assumptions.

This tightens the criterion:

> A hidden item is material exactly when its disclosure participates in defeating reliance.

## Local truth without target warrant

The boundary module proves:

- `GRBS.HiddenDefeaterBoundary.visible_claim_holds_but_target_warrant_fails`
- `GRBS.HiddenDefeaterBoundary.local_truth_with_deceptive_transfer`

Interpretation:

The visible/local claim can hold while the fuller target-boundary warrant fails. This makes the central point explicit:

> Deception need not depend on a false visible claim. It can arise when a true local claim transfers confidence beyond its admissible warrant.

## Admissibility blocks deception

The boundary module proves:

- `GRBS.HiddenDefeaterBoundary.admissible_transfer_blocks_deception`
- `GRBS.HiddenDefeaterBoundary.deceptive_transfer_iff_confidence_without_admissibility`

Interpretation:

If transfer is admissible, deceptive transfer is impossible in this model. Deceptive transfer is exactly confidence transfer without admissible warrant transfer.

This gives the positive DARM role:

> DARM does not merely detect hidden defeaters. It blocks deceptive transfer by requiring admissible warrant preservation.
