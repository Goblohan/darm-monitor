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
