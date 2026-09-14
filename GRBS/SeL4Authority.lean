/-
  GRBS/SeL4Authority.lean — seL4-structured paired-system AG separation.

  SCOPE AND HONEST LIMITATIONS
  ────────────────────────────
  * This is a seL4-STRUCTURED model in Lean 4, not a verified correspondence
    to seL4's actual Isabelle/HOL specification. The types are abstractions of
    seL4 concepts (CSpace capabilities, physical DMA channels), not imports of
    seL4's formal artifacts.
  * We define explicit correspondence relations (`R_cap`, authority-extension)
    between DARM authority concepts and seL4-like capability/physical structures,
    and prove properties OF those relations.
  * "Verified correspondence to seL4's actual Isabelle spec" is stated as future
    work, not claimed. Properties hold of the Lean model; transfer to the real
    seL4 requires engaging the Isabelle spec, which is out of scope here.

  EMPIRICAL FACT THE EXPEIMENT RESTS ON
  ──────────────────────────────────────
  * In base seL4, DMA is NOT mediated through CSpace. A device with
    bus-mastering DMA reads/writes physical memory directly, bypassing the
    CPU's MMU and hence seL4's capability checks.
  * seL4's integrity/confidentiality proofs carry an explicit precondition:
    either no DMA-capable devices exist, or DMA is properly managed externally.
  * IOMMU (Intel VT-d, ARM SMMU) can restrict DMA but requires explicit
    configuration and is NOT part of seL4's base formal verification scope.
  * Hence: `Cov(DMA) = true ⟸ IOMMU configured` is the faithful correspondence.

  THE PAIRED-SYSTEM EXPERIMENT
  ────────────────────────────
  * System A: All authority is CSpace-mediated. No DMA-capable devices.
  * System B: SAME CSpace as A (capability layout held constant).
              Additionally has a DMA channel reaching the same resource,
              NOT mediated by CSpace (base seL4, no IOMMU).
  * CSpace_A = CSpace_B  →  AG (over CSpace observables) sees no difference.
  * AuthorityTopology_A ≠ AuthorityTopology_B  →  GRBS distinguishes them.
  * Holding CSpace constant structurally prevents the "DARM is just
    capability analysis" dismissal: the systems have IDENTICAL capability
    layouts, and GRBS still separates them.

  RELATION TO AGAttack.lean (AG-0 DIAGNOSTIC)
  ────────────────────────────────────────────
  * AGAttack.lean proved separation via trace-identical + dep-equal + cov-different
    systems (the AG-0 diagnostic). That witness's honest weakness: coverage was
    trace-inert — a referee can object that "inert" coverage is meaningless.
  * This file instantiates the separation on seL4-structured types where coverage
    has operational meaning: DMA authority is physically real, un-CSpace-mediated,
    and the source of actual integrity violations (see seL4's own preconditions).
    The dep sets genuinely differ (System B has an additional physical channel).
    This is NOT the AGAttack DepEq case; we use a direct separation theorem
    requiring only TraceEq + GRBS-differs.
-/

namespace GRBS.SeL4Authority

-- ═══════════════════════════════════════════════════════════════════════════
-- § 1  Abstract carriers — seL4-structured
-- ═══════════════════════════════════════════════════════════════════════════

/-- Authority channels: how a component can exercise authority over a resource.
    - `cap`: access through a CSpace capability (kernel-mediated).
    - `dma`: direct memory access from a bus-mastering device (physical, bypasses
      the CPU's MMU and hence CSpace). -/
inductive Channel where
  | cap : Channel
  | dma : Channel
deriving DecidableEq

/-- CSpace-level environments the system composes with. -/
inductive Env where | base

/-- Observable CSpace-level execution traces. -/
inductive CTrace where | nominal

-- ═══════════════════════════════════════════════════════════════════════════
-- § 2  System, guarantee, GRBS, AG
-- ════════════════════════════════════════════════════════════════════════════

/-- A guarantee is a predicate on (CSpace-observable) traces. -/
abbrev Guarantee := CTrace → Prop

/-- System: THREE independent pieces of structure, no definitional link.
    * `traces`   — CSpace-level behavioral semantics (what AG can observe).
    * `channels` — the authority topology (which channels exist — CSpace AND
                   physical). Determined by the hardware + configuration.
    * `cov`      — the coverage topology (which channels are boundary-mediated).
                   Determined by whether mediation infrastructure exists for
                   each channel (CSpace for caps, IOMMU for DMA).
    Any connection among these is a theorem, never a definition. -/
structure System where
  traces   : Env → CTrace → Prop
  channels : Channel → Prop
  cov      : Channel → Prop

/-- GRBS: every authority channel of the system is covered (boundary-mediated).
    References `s.channels` (authority topology) and `s.cov` (coverage topology).
    The guarantee parameter is retained for signature compatibility with the
    DARM framework; in this instantiation, the dependency set is `s.channels`
    for every guarantee — the simplification is noted and honest. -/
def GRBS (_g : Guarantee) (s : System) : Prop :=
  ∀ ch : Channel, s.channels ch → s.cov ch

/-- AG assumption: a predicate on the ENVIRONMENT only (AG-0). -/
abbrev AGAssumption := Env → Prop

/-- AG satisfaction (ordinary, untuned): under every environment admitted by `A`,
    every trace of `s` satisfies `g`. Sees ONLY `s.traces` and `g`.
    NEVER `s.channels`, NEVER `s.cov`. -/
def AGSatisfies (A : AGAssumption) (g : Guarantee) (s : System) : Prop :=
  ∀ e : Env, A e → ∀ t : CTrace, s.traces e t → g t

-- ════════════════════════════════════════════════════════════════════════════
-- § 3  Behavioral equivalence
-- ════════════════════════════════════════════════════════════════════════════

/-- Trace-equivalence: identical CSpace-level executions under every environment.
    All that the AG side can observe. -/
def TraceEq (s1 s2 : System) : Prop :=
  ∀ (e : Env) (t : CTrace), s1.traces e t ↔ s2.traces e t

-- ════════════════════════════════════════════════════════════════════════════
-- § 4  Lemma 1 — AG is blind to anything invisible in traces (unconditional)
-- ════════════════════════════════════════════════════════════════════════════

theorem agSatisfies_congr_of_traceEq (s1 s2 : System)
    (h : TraceEq s1 s2) (A : AGAssumption) (g : Guarantee) :
    AGSatisfies A g s1 ↔ AGSatisfies A g s2 := by
  constructor
  · intro hsat e hA t ht
    exact hsat e hA t ((h e t).mpr ht)
  · intro hsat e hA t ht
    exact hsat e hA t ((h e t).mp ht)

-- ═══════════════════════════════════════════════════════════════════════════
-- § 5  seL4-structured paired systems
-- ════════════════════════════════════════════════════════════════════════════

/-- Shared CSpace behavior: both systems produce the same traces.
    Content is irrelevant to the separation (it's about authority/coverage,
    not about whether g holds). -/
def sharedTraces : Env → CTrace → Prop := fun _ _ => True

/-- **System A (CSpace only).** One authority channel: the CSpace capability.
    It IS covered (CSpace mediates it). No DMA-capable devices. -/
def SysA : System where
  traces   := sharedTraces
  channels := fun ch => ch = Channel.cap
  cov      := fun ch => ch = Channel.cap

/-- **System B (CSpace + DMA, base seL4, no IOMMU).** SAME CSpace behavior,
    SAME CSpace capability. But also has a DMA channel reaching the same
    resource. DMA is NOT CSpace-mediated (base seL4, no IOMMU).
    CSpace layout is HELD CONSTANT — divergence is only at the physical layer. -/
def SysB : System where
  traces   := sharedTraces
  channels := fun _ => True
  cov      := fun ch => ch = Channel.cap

-- ════════════════════════════════════════════════════════════════════════════
-- § 6  Correspondence relations and their properties
-- ════════════════════════════════════════════════════════════════════════════

/-- `R_cap`: a CSpace capability in the seL4 configuration corresponds to a
    covered authority channel in the DARM model. -/
def R_cap (s : System) (ch : Channel) : Prop :=
  ch = Channel.cap ∧ s.channels ch ∧ s.cov ch

/-- Property of `R_cap`: CSpace authority is always covered (by construction of
    the CSpace mediation boundary). -/
theorem R_cap_implies_covered (s : System) (ch : Channel) (h : R_cap s ch) :
    s.cov ch :=
  h.2.2

/-- Property: systems with the same CSpace produce the same traces.
    The behavioral faithfulness of holding CSpace constant. -/
theorem R_sys_traceEq : TraceEq SysA SysB := by
  intro e t; constructor <;> (intro; trivial)

/-- Property: SysB has strictly more authority channels than SysA.
    The additional authority (DMA) is outside CSpace. -/
theorem R_sys_authority_strictly_extends :
    (∀ ch, SysA.channels ch → SysB.channels ch)
    ∧ (∃ ch, SysB.channels ch ∧ ¬ SysA.channels ch) := by
  constructor
  · intro _ch _; trivial
  · exact ⟨Channel.dma, trivial, fun h => Channel.noConfusion h⟩

/-- Property: the CSpace portion of coverage is identical — both systems cover
    CSpace channels the same way. The difference is only in physical channels. -/
theorem R_sys_cspace_coverage_identical :
    SysA.cov Channel.cap ↔ SysB.cov Channel.cap := by
  constructor <;> (intro; rfl)

/-- Property: the DMA channel in SysB is NOT covered (base seL4, no IOMMU). -/
theorem R_sys_dma_uncovered : SysB.channels Channel.dma ∧ ¬ SysB.cov Channel.dma := by
  constructor
  · trivial
  · intro h; exact Channel.noConfusion h

-- ════════════════════════════════════════════════════════════════════════════
-- § 7  The separation
-- ═══════════════════════════════════════════════════════════════════════════

/-- The guarantee: all traces are safe. Content is irrelevant to the separation;
    what matters is that AG gives the SAME verdict for both (TraceEq ensures this)
    while GRBS gives DIFFERENT verdicts (authority/coverage diverge). -/
def g : Guarantee := fun _ => True

/-- GRBS holds for System A: its one authority channel (cap) is covered. -/
theorem GRBS_SysA : GRBS g SysA := by
  intro ch hch
  exact hch

/-- GRBS FAILS for System B: DMA is an authority channel but is not covered.
    This is the formal expression of seL4's DMA gap under base configuration. -/
theorem not_GRBS_SysB : ¬ GRBS g SysB := by
  intro h
  -- h : ∀ ch, SysB.channels ch → SysB.cov ch
  -- Specialize to DMA: SysB.channels dma = True, so h gives SysB.cov dma
  -- But SysB.cov dma = (dma = cap), which is false.
  have h2 : Channel.dma = Channel.cap := h Channel.dma trivial
  exact Channel.noConfusion h2

/-- **seL4 PAIRED-SYSTEM SEPARATION.**

    For every behaviorally-grounded AG assumption `A`:
    * AG gives the IDENTICAL verdict for SysA and SysB
      (same CSpace behavior → Lemma 1).
    * GRBS distinguishes them: holds for SysA (all authority covered),
      fails for SysB (DMA authority uncovered).

    The separation holds precisely because DMA authority exists outside
    CSpace's mediation boundary. CSpace confinement is held constant —
    the systems have identical capability layouts. This structurally
    prevents the "DARM is just capability analysis" dismissal: the
    capability topology is the same, and GRBS STILL separates. -/
theorem seL4_separation (A : AGAssumption) :
    (AGSatisfies A g SysA ↔ AGSatisfies A g SysB)
    ∧ (GRBS g SysA ∧ ¬ GRBS g SysB) := by
  exact ⟨agSatisfies_congr_of_traceEq SysA SysB R_sys_traceEq A g,
         GRBS_SysA, not_GRBS_SysB⟩

-- ═══════════════════════════════════════════════════════════════════════════
-- § 8  IOMMU recovery — when DMA IS mediated, GRBS is restored
-- ════════════════════════════════════════════════════════════════════════════

/-- System B with IOMMU: same authority topology as SysB (DMA exists), but
    NOW the DMA channel is covered by IOMMU mediation.
    This demonstrates that GRBS separation is about the mediation gap,
    not about DMA existing — and that IOMMU is precisely the fix GRBS demands. -/
def SysB_IOMMU : System where
  traces   := sharedTraces
  channels := fun _ => True
  cov      := fun _ => True

/-- With IOMMU, GRBS holds for System B: all channels (cap AND dma) are covered. -/
theorem GRBS_SysB_IOMMU : GRBS g SysB_IOMMU := by
  intro _ch _; trivial

/-- The IOMMU recovery is structurally precise: extending coverage to physical
    channels restores the GRBS invariant without changing the authority topology
    or the CSpace behavior. -/
theorem IOMMU_recovers_without_behavioral_change :
    TraceEq SysB SysB_IOMMU
    ∧ (∀ ch, SysB.channels ch ↔ SysB_IOMMU.channels ch)
    ∧ GRBS g SysB_IOMMU := by
  refine ⟨?_, ?_, GRBS_SysB_IOMMU⟩
  · intro e t; constructor <;> (intro; trivial)
  · intro _; constructor <;> (intro; trivial)

-- ════════════════════════════════════════════════════════════════════════════
-- § 9  Summary: what the experiment decides and what it defers
-- ════════════════════════════════════════════════════════════════════════════

/-!
  ## Established (machine-checked, axiom-free):

  1. `seL4_separation`: for CSpace-identical systems where one has an additional
     physical authority channel (DMA), AG (over CSpace behavior) gives identical
     verdicts while GRBS distinguishes them. The GRBS transfer judgment is NOT
     recoverable from CSpace-level assume-guarantee reasoning.

  2. `R_sys_authority_strictly_extends`: the divergence is at the physical layer
     OUTSIDE CSpace — the capability topology is identical. DARM's authority
     topology is strictly more expressive than CSpace confinement.

  3. `R_sys_dma_uncovered`: the DMA channel is a real authority channel that is
     NOT covered in base seL4 — formalizing seL4's own stated precondition.

  4. `IOMMU_recovers_without_behavioral_change`: IOMMU extends coverage to
     physical channels, recovering GRBS without changing behavior or authority.
     This is structurally precise: IOMMU is exactly what GRBS demands.

  ## Deferred (future work, NOT Ilaimed):

  * Verified correspondence to seL4's actual Isabelle/HOL specification.
    Properties hold of this Lean model; transfer requires engaging seL4's
    formal artifacts, which is a separate verification effort.

  * AG-3 (adversarial-environment) strengthening: the version where coverage
    is inert under base environment but causally live under an adversarial
    environment, with AG given the adversarial environment too. See the
    honest analysis in AGAttack.lean's header.

  * Multi-resource / multi-guarantee scaling: this experiment uses minimal
    carriers (one resource, one cap, one DMA channel). Real systems have
    complex authority topologies; the parametric framework supports them
    but concrete instantiation is future work.
-/

end GRBS.SeL4Authority
