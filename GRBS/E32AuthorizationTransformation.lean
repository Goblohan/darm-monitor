import E24bResourceIntents

namespace DARM.E32

def FitCoverage
    {P₁ P₂ I₁ I₂ : Type}
    (fits₁ : I₁ → P₁ → Bool)
    (fits₂ : I₂ → P₂ → Bool)
    (f : P₁ → P₂)
    (g : I₁ → I₂)
    (i : I₁) : Prop :=
  ∀ q,
    fits₂ (g i) q = true →
    ∃ p,
      f p = q ∧ fits₁ i p = true

def AcceptsForward
    {P₁ P₂ : Type}
    (acc₁ : P₁ → Prop)
    (acc₂ : P₂ → Prop)
    (f : P₁ → P₂) : Prop :=
  ∀ p, acc₁ p → acc₂ (f p)

def AdmissionReflects
    {P₁ P₂ E₁ E₂ : Type}
    (admit₁ : P₁ → Option E₁)
    (admit₂ : P₂ → Option E₂)
    (f : P₁ → P₂) : Prop :=
  ∀ p e₂,
    admit₂ (f p) = some e₂ →
    ∃ e₁, admit₁ p = some e₁

theorem complete_under_transfer
    {P₁ P₂ E₁ E₂ I₁ I₂ : Type}
    {acc₁ : P₁ → Prop}
    {acc₂ : P₂ → Prop}
    {fits₁ : I₁ → P₁ → Bool}
    {fits₂ : I₂ → P₂ → Bool}
    {admit₁ : P₁ → Option E₁}
    {admit₂ : P₂ → Option E₂}
    {f : P₁ → P₂}
    {g : I₁ → I₂}
    {i : I₁}
    (hComplete :
      ∀ p e₁,
        fits₁ i p = true →
        admit₁ p = some e₁ →
        acc₁ p)
    (hCoverage :
      FitCoverage fits₁ fits₂ f g i)
    (hAdmission :
      AdmissionReflects admit₁ admit₂ f)
    (hAccept :
      AcceptsForward acc₁ acc₂ f) :
    ∀ q e₂,
      fits₂ (g i) q = true →
      admit₂ q = some e₂ →
      acc₂ q := by
  intro q e₂ hfit hq
  obtain ⟨p, rfl, hsourceFit⟩ := hCoverage q hfit
  obtain ⟨e₁, hsourceAdmit⟩ := hAdmission p e₂ hq
  exact hAccept p (hComplete p e₁ hsourceFit hsourceAdmit)

end DARM.E32
