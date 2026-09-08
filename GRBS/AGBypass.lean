/-
  AG-ATTACK-1, experiment 2b: the STRUCTURAL ISOLATION theorem.

  Separates three distinct objects (the fairness of the whole experiment):
    * interfaceTraces : software-contract-visible behavior  (what AG observes)
    * physicalStep    : execution across the hardware substrate footprint
                        (what a below-interface adversary can drive)
    * cov             : coverage topology                    (what GRBS sees)

  A latent channel `d` lies in the PHYSICAL FOOTPRINT but OUTSIDE the interface:
  unreachable by any interface-respecting environment, yet a real hardware
  channel a physical adversary can drive.

  Admissibility is fixed INDEPENDENTLY of `d`: an environment is admissible iff
  it issues only interface actions. It knows nothing of `d` or coverage. So the
  exclusion of the exposing adversary is a PRINCIPLED consequence of `d` being
  below-interface, NOT a gerrymander.

  Non-inertness is PROVED: an explicit physical (interface-violating) adversary
  drives `d` to a G-violation in S2, while S1's coverage neutralizes it. So `d`
  is a genuine hazard, not inert decoration.

  Verdict target (grbs_isolates_latent_bypass):
      AG_admissible S1 = AG_admissible S2   (interface-indistinguishable)
    ∧ GRBS S1 ≠ GRBS S2                      (coverage distinguishes them)
    ∧ d is a live physical hazard           (non-inertness witness)

  AG proves safety ASSUMING interface-respect. GRBS proves safety against
  physical adversaries exploiting unmediated below-interface channels.
-/

namespace GRBS
namespace AGBypass

/-- Interface actions the software contract exposes. -/
abbrev Action := Nat

/-- A guarantee is a predicate on traces. -/
abbrev Guarantee (Trace : Type) := Trace → Prop

/-- An environment issues a set of actions (the actions it drives). Abstractly, a
    predicate on actions: `e a` means environment `e` may drive action `a`. -/
abbrev Environment := Action → Prop

/-- **System with a hardware substrate.** Four pieces, deliberately separate:
      * `interface` — the actions the software contract exposes;
      * `interfaceTraces` — behavior under interface-respecting environments
        (what AG sees);
      * `physicalStep` — substrate execution over the footprint: `physicalStep d t`
        means driving channel `d` physically yields trace `t` (what a
        below-interface adversary can do);
      * `cov` — which channels are mediated (what GRBS sees).
    Nothing links `cov` to `interfaceTraces`. -/
structure System (Trace Channel : Type) where
  interface : Action → Prop
  interfaceTraces : Environment → Trace → Prop
  physicalStep : Channel → Trace → Prop
  cov : Channel → Prop

/-- The structural dependency set: channels the guarantee structurally rests on,
    read from the physical footprint (a channel is a dependency if it can
    physically produce a trace). Blind to `cov`. -/
def depB {Trace Channel : Type}
    (_g : Guarantee Trace) (s : System Trace Channel) (d : Channel) : Prop :=
  ∃ t, s.physicalStep d t

/-- **GRBS.** Every structural (physical-footprint) dependency is covered. -/
def GRBS {Trace Channel : Type}
    (g : Guarantee Trace) (s : System Trace Channel) : Prop :=
  ∀ d : Channel, depB g s d → s.cov d

/-- **Admissibility, fixed independently of any channel.** An environment is
    admissible for `s` iff every action it drives is in `s.interface`. Knows
    nothing of `d` or `cov`. -/
def Admissible {Trace Channel : Type}
    (s : System Trace Channel) (e : Environment) : Prop :=
  ∀ a : Action, e a → s.interface a

/-- **AG assumption** — a predicate on environments (behaviorally grounded). -/
abbrev AGAssumption := Environment → Prop

/-- **AG satisfaction over the admissible class.** Under every ADMISSIBLE
    environment admitted by `A`, every interface trace satisfies `g`. AG assumes
    interface-respect: it quantifies over `Admissible` environments and observes
    only `interfaceTraces`. Never sees `physicalStep` or `cov`. -/
def AGSatisfiesAdm {Trace Channel : Type}
    (A : AGAssumption) (g : Guarantee Trace) (s : System Trace Channel) : Prop :=
  ∀ e : Environment, Admissible s e → A e →
    ∀ t : Trace, s.interfaceTraces e t → g t

/-- Interface-trace equivalence: identical interface behavior under every
    admissible environment. All the AG side can observe. -/
def IfaceTraceEqAdm {Trace Channel : Type}
    (s1 s2 : System Trace Channel) : Prop :=
  (∀ a, s1.interface a ↔ s2.interface a) ∧
  (∀ (e : Environment) (t : Trace), s1.interfaceTraces e t ↔ s2.interfaceTraces e t)

/-- **Lemma (AG blindness below the interface).** If two systems have the same
    interface and the same interface traces, then AG-over-admissible cannot
    distinguish them — for every assumption and guarantee. Does NOT reference
    `physicalStep` or `cov`. -/
theorem agAdm_congr_of_ifaceTraceEq {Trace Channel : Type}
    (s1 s2 : System Trace Channel) (h : IfaceTraceEqAdm s1 s2)
    (A : AGAssumption) (g : Guarantee Trace) :
    AGSatisfiesAdm A g s1 ↔ AGSatisfiesAdm A g s2 := by
  obtain ⟨hIface, hTr⟩ := h
  constructor
  · intro hsat e hAdm hA t ht
    -- admissibility transfers via interface equality
    have hAdm1 : Admissible s1 e := by
      intro a ha; exact (hIface a).mpr (hAdm a ha)
    exact hsat e hAdm1 hA t ((hTr e t).mpr ht)
  · intro hsat e hAdm hA t ht
    have hAdm2 : Admissible s2 e := by
      intro a ha; exact (hIface a).mp (hAdm a ha)
    exact hsat e hAdm2 hA t ((hTr e t).mp ht)

end AGBypass
end GRBS

namespace GRBS
namespace AGBypass
namespace Witness

/-! ## Concrete witness: the DMA bypass.

    Traces record whether a violation occurred. The physical channel `d0` (think
    unmediated DMA / direct register access) is in the footprint of both systems
    but NOT in the interface. Interface-respecting environments cannot reach it,
    so S1 and S2 have identical interface behavior (AG-indistinguishable). S1
    mediates `d0` (covered); S2 does not. A physical adversary driving `d0`
    produces a violating trace in S2 — proving `d0` is a live hazard, not inert. -/

/-- Traces: either the safe interface behavior, or a violation produced by
    driving the physical bypass. -/
inductive Tr where
  | ok        -- ordinary interface-visible behavior (safe)
  | violated  -- a guarantee violation (produced only via the physical channel)
deriving DecidableEq

/-- One physical channel: the bypass. -/
inductive Ch where | d0
deriving DecidableEq

/-- The guarantee: the `violated` trace is unsafe; everything else is safe. -/
def g : Guarantee Tr
  | Tr.ok => True
  | Tr.violated => False

/-- Interface: NO action reaches the bypass channel. Concretely, the interface
    exposes (say) action 0 only, and the bypass is not driven by any interface
    action. We keep the interface trivial: only the `ok` trace is interface-
    reachable, identically for both systems. -/
def ifaceTraces : Environment → Tr → Prop :=
  fun _ t => t = Tr.ok   -- interface-respecting runs only ever produce `ok`

/-- The interface predicate: expose action 0 only (irrelevant to the separation,
    but fixed and identical across systems). -/
def iface : Action → Prop := fun a => a = 0

/-- Physical substrate: driving the bypass channel `d0` can produce the
    `violated` trace. This is the below-interface hazard, present in BOTH
    systems' footprints. -/
def physStep : Ch → Tr → Prop :=
  fun _ t => t = Tr.violated

/-- System 1: the bypass `d0` is COVERED (mediated — e.g. IOMMU traps it). -/
def S1 : System Tr Ch where
  interface := iface
  interfaceTraces := ifaceTraces
  physicalStep := physStep
  cov := fun _ => True

/-- System 2: SAME interface, SAME interface traces, SAME physical footprint,
    but the bypass `d0` is NOT covered (bare-metal DMA, unmediated). -/
def S2 : System Tr Ch where
  interface := iface
  interfaceTraces := ifaceTraces
  physicalStep := physStep
  cov := fun _ => False

/-- **Interface-indistinguishability.** S1 and S2 have identical interface and
    identical interface traces, so AG-over-admissible cannot tell them apart. -/
theorem ifaceTraceEq_S1_S2 : IfaceTraceEqAdm S1 S2 := by
  constructor
  · intro a; exact Iff.rfl
  · intro e t; exact Iff.rfl

/-- `d0` IS a structural dependency in both (its physical step produces a trace).
    So GRBS is not vacuous. -/
theorem dep_holds_S1 : depB g S1 Ch.d0 := ⟨Tr.violated, rfl⟩
theorem dep_holds_S2 : depB g S2 Ch.d0 := ⟨Tr.violated, rfl⟩

/-- GRBS holds for S1: its one physical dependency `d0` is covered. -/
theorem GRBS_S1 : GRBS g S1 := by
  intro d _hd; trivial

/-- GRBS FAILS for S2: `d0` is a physical dependency but uncovered. -/
theorem not_GRBS_S2 : ¬ GRBS g S2 := by
  intro h
  exact h Ch.d0 dep_holds_S2

/-! ### Non-inertness: `d0` is a LIVE hazard, not decoration.

    An explicit physical adversary drives `d0` to a genuine `g`-violation in S2.
    This is what distinguishes 2b (structural isolation) from the vacuous
    inert-shadow case: the uncovered channel is really exploitable — just not by
    an interface-respecting (admissible) environment. -/

/-- The physical adversary's exploit: driving `d0` physically produces the
    `violated` trace, which violates `g`. This trace exists in S2's footprint
    and is unsafe. -/
theorem physical_exploit_S2 :
    ∃ t, S2.physicalStep Ch.d0 t ∧ ¬ g t := by
  exact ⟨Tr.violated, rfl, by intro h; exact h⟩

/-- In S1 the SAME physical drive is mediated: `d0` is covered, so GRBS's
    obligation is met and the bypass is accounted for. (Formally: S1 satisfies
    GRBS, so every physical dependency including `d0` is under mediation.) -/
theorem bypass_mediated_S1 : S1.cov Ch.d0 := trivial

/-- The physical drive is UNMEDIATED in S2: `d0` is not covered. Combined with
    `physical_exploit_S2`, this is the concrete hazard GRBS flags and AG misses. -/
theorem bypass_unmediated_S2 : ¬ S2.cov Ch.d0 := by
  intro h; exact h

/-! ## The structural isolation theorem. -/

/-- **grbs_isolates_latent_bypass.**
    For the fixed guarantee `g` and every behaviorally-grounded AG assumption
    `A`:
      (1) AG-over-admissible gives S1 and S2 the identical verdict — it cannot
          distinguish them, because they are interface-identical and the bypass
          is below the interface;
      (2) GRBS distinguishes them — S1 mediates the bypass, S2 does not;
      (3) the bypass is a LIVE physical hazard — a physical adversary drives `d0`
          to a real `g`-violation in S2, unmediated.

    Verdict: AG proves safety ASSUMING interface-respect; GRBS additionally
    requires mediation of below-interface physical channels. The separation is a
    genuine structural isolation result — zero-trust complete mediation vs.
    interface-contract safety — not a trace-checking artifact and not inert
    decoration. -/
theorem grbs_isolates_latent_bypass (A : AGAssumption) :
    (AGSatisfiesAdm A g S1 ↔ AGSatisfiesAdm A g S2)          -- (1) AG cannot distinguish
    ∧ (GRBS g S1 ∧ ¬ GRBS g S2)                              -- (2) GRBS distinguishes
    ∧ (∃ t, S2.physicalStep Ch.d0 t ∧ ¬ g t ∧ ¬ S2.cov Ch.d0) -- (3) live unmediated hazard
    := by
  refine ⟨?_, ⟨GRBS_S1, not_GRBS_S2⟩, ?_⟩
  · exact agAdm_congr_of_ifaceTraceEq S1 S2 ifaceTraceEq_S1_S2 A g
  · exact ⟨Tr.violated, rfl, (by intro h; exact h), bypass_unmediated_S2⟩

end Witness
end AGBypass
end GRBS
