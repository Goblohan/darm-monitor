import E32AuthorizationTransformation

namespace DARM.E32.Countermodel

abbrev P₁ := Unit
abbrev P₂ := Bool
abbrev I₁ := Unit
abbrev I₂ := Unit
abbrev E₁ := Unit
abbrev E₂ := Unit

abbrev fits₁ : I₁ → P₁ → Bool := fun _ _ => true
abbrev fits₂ : I₂ → P₂ → Bool := fun _ _ => true

abbrev f : P₁ → P₂ := fun _ => false
abbrev g : I₁ → I₂ := fun _ => ()

abbrev admit₁ : P₁ → Option E₁ := fun _ => some ()
abbrev admit₂ : P₂ → Option E₂ := fun _ => some ()

abbrev acc₁ : P₁ → Prop := fun _ => True
abbrev acc₂ : P₂ → Prop := fun q => q = false

abbrev i₀ : I₁ := ()

theorem source_complete :
    ∀ p e,
      fits₁ i₀ p = true →
      admit₁ p = some e →
      acc₁ p := by
  intro p e _ _
  trivial

theorem accepts_forward :
    AcceptsForward acc₁ acc₂ f := by
  intro p _
  simp [acc₂, f]

theorem admission_reflects :
    AdmissionReflects admit₁ admit₂ f := by
  intro p e₂ _
  exact ⟨(), rfl⟩

theorem not_fit_coverage :
    ¬ FitCoverage fits₁ fits₂ f g i₀ := by
  intro h
  obtain ⟨p, hp, _⟩ := h true rfl
  exact Bool.noConfusion hp

theorem target_incomplete :
    ¬ (∀ q e₂,
      fits₂ (g i₀) q = true →
      admit₂ q = some e₂ →
      acc₂ q) := by
  intro h
  have hacc : acc₂ true := h true () rfl rfl
  exact Bool.noConfusion hacc

theorem separation :
    (∀ p e,
      fits₁ i₀ p = true →
      admit₁ p = some e →
      acc₁ p) ∧
    AcceptsForward acc₁ acc₂ f ∧
    AdmissionReflects admit₁ admit₂ f ∧
    ¬ FitCoverage fits₁ fits₂ f g i₀ ∧
    ¬ (∀ q e₂,
      fits₂ (g i₀) q = true →
      admit₂ q = some e₂ →
      acc₂ q) := by
  constructor
  · exact source_complete
  constructor
  · exact accepts_forward
  constructor
  · exact admission_reflects
  constructor
  · exact not_fit_coverage
  · exact target_incomplete

end DARM.E32.Countermodel
