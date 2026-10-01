import E32AuthorizationTransformation

namespace DARM.E32.Canonicalization

abbrev P₁ := Bool
abbrev P₂ := Bool × Unit
abbrev I₁ := Unit
abbrev I₂ := Unit
abbrev E₁ := Unit
abbrev E₂ := Unit

abbrev i₀ : I₁ := ()

def f : P₁ → P₂ :=
  fun p => (p, ())

def g : I₁ → I₂ :=
  fun _ => ()

def fits₁ : I₁ → P₁ → Bool :=
  fun _ p => p

def fits₂ : I₂ → P₂ → Bool :=
  fun _ q => q.1

abbrev admit₁ : P₁ → Option E₁ :=
  fun _ => some ()

abbrev admit₂ : P₂ → Option E₂ :=
  fun _ => some ()

def acc₁ : P₁ → Prop :=
  fun p => p = true

def acc₂ : P₂ → Prop :=
  fun q => q.1 = true

theorem coverage :
    FitCoverage fits₁ fits₂ f g i₀ := by
  intro q hq
  refine ⟨q.1, ?_, ?_⟩
  · rfl
  · exact hq

theorem accepts_forward :
    AcceptsForward acc₁ acc₂ f := by
  intro p hp
  exact hp

theorem admission_reflects :
    AdmissionReflects admit₁ admit₂ f := by
  intro p e₂ _
  exact ⟨(), rfl⟩

theorem source_complete :
    ∀ p e,
      fits₁ i₀ p = true →
      admit₁ p = some e →
      acc₁ p := by
  intro p e hfit _
  exact hfit

theorem transfers_completeness :
    ∀ q e₂,
      fits₂ (g i₀) q = true →
      admit₂ q = some e₂ →
      acc₂ q := by
  exact complete_under_transfer
    source_complete
    coverage
    admission_reflects
    accepts_forward

def widenedFits₂ : I₂ → P₂ → Bool :=
  fun _ _ => true

theorem widened_target_lacks_coverage :
    ¬ FitCoverage fits₁ widenedFits₂ f g i₀ := by
  intro h
  obtain ⟨p, hp, hfit⟩ := h (false, ()) rfl
  have hp' : p = false := by
    simpa [f] using hp
  subst p
  simp [fits₁] at hfit

end DARM.E32.Canonicalization
