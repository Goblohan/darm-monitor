/-
  Step 1 — the CoverageSensitive derivation attack.

  2a proved: given `CoverageSensitive M`, an above-interface coverage difference
  is AG-observable. Escape-hatch worry: is `CoverageSensitive M` itself a
  smuggled DARM assumption, or DERIVABLE from ordinary operational semantics?

  We answer for the CANONICAL TRAPPING MEDIATION (the honest reference-monitor
  model): covered channel -> trapped -> safe; uncovered channel -> raw effect.

  Result: `CoverageSensitive M_trap` is DERIVABLE and holds EXACTLY WHEN the raw
  channel is hazardous (`rawUnsafe`). So the 2a hypothesis is not hidden DARM
  content — under honest mediation it reduces to raw operational hazard (the same
  sensitivity condition as R3's `FalsifiableVia`).

  DISCIPLINE: `M_trap` is defined by the trapping discipline, NOT reverse-
  engineered. Whether it is coverage-sensitive is a THEOREM about `rawUnsafe`.
-/

namespace GRBS
namespace CoverageSensitivity

/-- Observable outcomes. -/
inductive Obs where
  | safe
  | violation
deriving DecidableEq

/-- **Canonical trapping mediation**, at a driven channel. `rawUnsafe` is whether
    the channel's raw (unmediated) effect is hazardous; `covered` is whether
    the boundary mediates it. Discipline: covered -> safe (trapped); uncovered ->
    violation iff the raw effect is unsafe. Defined from the discipline, not from
    the desired conclusion. -/
def M_trap (rawUnsafe : Prop) [Decidable rawUnsafe]
    (covered : Prop) [Decidable covered] : Obs :=
  if covered then Obs.safe
  else if rawUnsafe then Obs.violation else Obs.safe

/-- `M_trap` on a covered channel is always safe. -/
theorem M_trap_covered (rawUnsafe : Prop) [Decidable rawUnsafe] :
    M_trap rawUnsafe True = Obs.safe := by
  simp [M_trap]

/-- `M_trap` on an uncovered channel is `violation` iff `rawUnsafe`. -/
theorem M_trap_uncovered_unsafe (rawUnsafe : Prop) [Decidable rawUnsafe]
    (h : rawUnsafe) : M_trap rawUnsafe False = Obs.violation := by
  simp [M_trap, h]

theorem M_trap_uncovered_safe (rawUnsafe : Prop) [Decidable rawUnsafe]
    (h : ¬ rawUnsafe) : M_trap rawUnsafe False = Obs.safe := by
  simp [M_trap, h]

/-- Coverage-sensitivity (driven case): the observable differs between the
    covered and uncovered assignments. -/
def CoverageSensitive (rawUnsafe : Prop) [Decidable rawUnsafe] : Prop :=
  M_trap rawUnsafe True ≠ M_trap rawUnsafe False

/-- **Forward.** Raw hazard entails coverage-sensitivity: `M_trap` covered = safe,
    uncovered = violation, and safe ≠ violation. So `CoverageSensitive` is not an
    independent assumption. --/
theorem coverageSensitive_of_rawUnsafe
    (rawUnsafe : Prop) [Decidable rawUnsafe] (h : rawUnsafe) :
    CoverageSensitive rawUnsafe := by
  unfold CoverageSensitive
  rw [M_trap_covered, M_trap_uncovered_unsafe rawUnsafe h]
  exact fun heq => Obs.noConfusion heq

/-- **Converse.** Coverage-sensitivity forces raw hazard: if not `rawUnsafe`, both
    covered and uncovered give `safe`, so not sensitive. -/
theorem rawUnsafe_of_coverageSensitive
    (rawUnsafe : Prop) [Decidable rawUnsafe]
    (h : CoverageSensitive rawUnsafe) : rawUnsafe := by
  apply Classical.byContradiction
  intro hn
  apply h
  rw [M_trap_covered, M_trap_uncovered_safe rawUnsafe hn]

/-- **The exact equivalence.** For the canonical trapping mediation,
    coverage-sensitivity coincides with raw hazard. Closes the escape-hatch
    worry: 2a's `CoverageSensitive` hypothesis, under honest mediation, is
    derivable and equals raw operational hazard (R3's sensitivity condition), NOT
    smuggled DARM content. --/
theorem coverageSensitive_iff_rawUnsafe
    (rawUnsafe : Prop) [Decidable rawUnsafe] :
    CoverageSensitive rawUnsafe ↔ rawUnsafe :=
  ⟨rawUnsafe_of_coverageSensitive rawUnsafe, coverageSensitive_of_rawUnsafe rawUnsafe⟩

end CoverageSensitivity
end GRBS
