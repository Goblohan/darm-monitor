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

## Theorem table

| Theorem | Informal meaning | Axiom status |
|---|---|---|
| `GRBS.HiddenDefeater.material_secret_exists` | In the card experiment, there exists a hidden material secret. | No axioms |
| `GRBS.HiddenDefeater.material_secret_iff_hidden_reliance_collapse` | A material secret is exactly a hidden item whose disclosure participates in reliance collapse. | No axioms |
| `GRBS.HiddenDefeater.not_material_secret_blocks_reliance_refutation` | If a hidden item is not material, disclosure cannot refute reliance constructively. | No axioms |
| `GRBS.HiddenDefeater.only_format_test_not_nonmaterial` | The format-only hidden condition is not non-material. | No axioms |
| `GRBS.HiddenDefeaterBoundary.deceptive_transfer_exists` | Confidence transfers from the visible slice while admissible transfer fails. | No axioms |
| `GRBS.HiddenDefeaterBoundary.deceptive_transfer_iff_confidence_without_admissibility` | Deceptive transfer is exactly confidence transfer without admissible transfer. | No axioms |
| `GRBS.HiddenDefeaterBoundary.admissible_transfer_blocks_deception` | If transfer is admissible, deceptive transfer is impossible. | No axioms |
| `GRBS.HiddenDefeaterBoundary.source_warrant_without_target_warrant_with_confidence` | A source warrant and confidence transfer can coexist with target-warrant failure. | No axioms |
| `GRBS.HiddenDefeaterBoundary.visible_claim_holds_but_target_warrant_fails` | The visible local claim can hold while target warrant fails. | No axioms |
| `GRBS.HiddenDefeaterBoundary.local_truth_with_deceptive_transfer` | A locally true claim can coexist with deceptive transfer. | No axioms |

## Compressed result

The hidden-defeater witness separates four notions:

1. local claim holding,
2. confidence transfer,
3. target warrant,
4. admissible transfer.

The core result is:

> A visible claim can be locally true and still participate in deceptive transfer when confidence crosses a boundary without admissible warrant preservation.

In this model, DARM's positive role is:

> admissible transfer blocks deceptive transfer.

## Reproducibility

Run:

    ./scripts/check_hidden_defeater.sh

This builds HiddenDefeater and HiddenDefeaterBoundary, then checks that the core hidden-defeater theorems do not depend on any axioms.

The same audit is enforced by GitHub Actions in .github/workflows/hidden-defeater.yml.
