/-
  E30 — ATTRIBUTION THROUGH RENAMES

  E28 attributes a file placed by a write. A file placed by a rename needs two
  attributions: which rename invocation placed it, and which write invocation
  authorized its content. E29 shows that, under attestation-faithful renames,
  an attested content was produced by some write; this file strengthens that
  to a lineage, a chain of request identifiers from the attestation present
  back to the write that first produced the content.

  Proved: in an attestation-faithful history from the empty world, every
  attestation present has a lineage (evolve_lin), and every lineage ends at a
  write of that content (lineage_origin). A rename invocation corresponds to a
  move from its path argument to its destination argument (ExecRename). For a
  consistently attested file placed under a rename's request, the move is in
  the history, from the rename invocation's path to its destination, and the
  content has a lineage ending at a write (rename_placed_lineage). If the
  content's originating write was executed for the authorized write
  invocation, the renamed file holds exactly the authorized content
  (rename_placed_content_authorized): attribution through two requests.

  Assumed, and stated: attestation-faithfulness (enforced by the broker since
  Darm-Guard 0.19.0); RenameExecutedUnder and E28's ExecutedUnder, the request
  links (each request belongs to one invocation, checked at runtime); in the
  capstone, that the content was written under one request.

  NOT claimed: deletes as authorized effects; anything about the
  implementation beyond the stated runtime checks.
-/
import E29FaithfulRename

namespace DARM.E30

open DARM.EffectIntegrity2 (World File Op BrokerOp Consistent empty
  brokerWrite brokerDelete brokerRename)
open DARM.E27b (Event Foreign evolve step applyForeign)
open DARM.E29 (AttFaithfulStep Faithful)

/-- A chain of requests from an attestation back to the write that produced
    its content. -/
inductive Lineage (h : List Event) : Nat → String → List Nat → Prop where
  | write {r : Nat} {t d : String} :
      Event.broker (BrokerOp.wr r t d) ∈ h → Lineage h r d [r]
  | rename {r r' : Nat} {s t d : String} {chain : List Nat} :
      Event.broker (BrokerOp.mv r s t d) ∈ h → Lineage h r' d chain → Lineage h r d (r :: chain)

theorem lineage_mono {h : List Event} {e : Event} {r : Nat} {d : String} {c : List Nat}
    (hl : Lineage h r d c) : Lineage (h ++ [e]) r d c := by
  induction hl with
  | write hm => exact Lineage.write (List.mem_append_left _ hm)
  | rename hm _ ih => exact Lineage.rename (List.mem_append_left _ hm) ih

/-- Every lineage ends at a write of that content, whose request is in the chain. -/
theorem lineage_origin {h : List Event} {r : Nat} {d : String} {c : List Nat}
    (hl : Lineage h r d c) : ∃ r0 t0, Event.broker (BrokerOp.wr r0 t0 d) ∈ h ∧ r0 ∈ c := by
  induction hl with
  | write hm => exact ⟨_, _, hm, List.mem_singleton.mpr rfl⟩
  | rename _ _ ih =>
    obtain ⟨r0, t0, hm, hr⟩ := ih
    exact ⟨r0, t0, hm, List.mem_cons.mpr (Or.inr hr)⟩

/-- Every attestation present has a lineage in h. -/
def LinInv (h : List Event) (w : World) : Prop :=
  ∀ x f r d, w.files x = some f → f.att = some (r, d) → ∃ c, Lineage h r d c

theorem lin_mono {done : List Event} {e : Event} {r : Nat} {d : String}
    (h : ∃ c, Lineage done r d c) : ∃ c, Lineage (done ++ [e]) r d c := by
  obtain ⟨c, hl⟩ := h
  exact ⟨c, lineage_mono hl⟩

theorem step_lin (done : List Event) (w : World) (e : Event)
    (hf : AttFaithfulStep w e) (h : LinInv done w) : LinInv (done ++ [e]) (step w e) := by
  intro x f r d hx ha
  cases e with
  | broker op =>
    cases op with
    | wr r0 t0 d0 =>
      simp only [step, DARM.EffectIntegrity2.apply, brokerWrite] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        cases hx
        simp at ha
        obtain ⟨rfl, rfl⟩ := ha
        exact ⟨_, Lineage.write (List.mem_append_right _ (List.mem_singleton.mpr rfl))⟩
      · rw [if_neg hxt] at hx
        exact lin_mono (h x f r d hx ha)
    | dl r0 t0 =>
      simp only [step, DARM.EffectIntegrity2.apply, brokerDelete] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        cases hx
      · rw [if_neg hxt] at hx
        exact lin_mono (h x f r d hx ha)
    | mv r0 s t0 d0 =>
      simp only [AttFaithfulStep] at hf
      simp only [step, DARM.EffectIntegrity2.apply, brokerRename] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        cases hx
        simp at ha
        obtain ⟨rfl, rfl⟩ := ha
        obtain ⟨fs, r', hs, hsa⟩ := hf
        obtain ⟨c, hl⟩ := h s fs r' _ hs hsa
        exact ⟨_, Lineage.rename (List.mem_append_right _ (List.mem_singleton.mpr rfl)) (lineage_mono hl)⟩
      · rw [if_neg hxt] at hx
        by_cases hxs : x = s
        · rw [if_pos hxs] at hx
          cases hx
        · rw [if_neg hxs] at hx
          exact lin_mono (h x f r d hx ha)
  | foreign fa =>
    cases fa with
    | del t0 =>
      simp only [step, applyForeign, DARM.EffectIntegrity2.foreignDelete] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        cases hx
      · rw [if_neg hxt] at hx
        exact lin_mono (h x f r d hx ha)
    | tamper t0 d' =>
      simp only [step, applyForeign, DARM.EffectIntegrity2.tamper] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        cases h0 : w.files t0 with
        | none =>
          rw [h0] at hx
          cases hx
        | some f0 =>
          rw [h0] at hx
          simp at hx
          subst hx
          exact lin_mono (h t0 f0 r d h0 ha)
      · rw [if_neg hxt] at hx
        exact lin_mono (h x f r d hx ha)
    | create t0 d0 =>
      simp only [step, applyForeign, DARM.EffectIntegrity2.create] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        cases hx
        simp at ha
      · rw [if_neg hxt] at hx
        exact lin_mono (h x f r d hx ha)
    | move s0 t0 =>
      simp only [step, applyForeign, DARM.EffectIntegrity2.foreignMove] at hx
      by_cases hxt : x = t0
      · rw [if_pos hxt] at hx
        exact lin_mono (h s0 f r d hx ha)
      · rw [if_neg hxt] at hx
        by_cases hxs : x = s0
        · rw [if_pos hxs] at hx
          cases hx
        · rw [if_neg hxs] at hx
          exact lin_mono (h x f r d hx ha)

theorem evolve_lin (es : List Event) :
    ∀ (done : List Event) (w : World), Faithful AttFaithfulStep w es → LinInv done w →
      LinInv (done ++ es) (evolve w es) := by
  induction es with
  | nil =>
    intro done w _ h
    simpa [evolve] using h
  | cons e es ih =>
    intro done w hfa h
    simp only [Faithful] at hfa
    have := ih (done ++ [e]) (step w e) hfa.2 (step_lin done w e hfa.1 h)
    simpa [evolve, List.append_assoc] using this

/-- Rename correspondence: a rename invocation corresponds to a move from its
    path argument to its destination argument. -/
def ExecRename (inv : DARM.Kernel.Invocation) (op : BrokerOp) : Prop :=
  inv.tool = "rename_file" ∧
  ∃ rid s t d, DARM.E26.hasArg inv "path" s ∧ DARM.E26.hasArg inv "destination" t ∧
    op = BrokerOp.mv rid s t d

/-- The request link for a rename invocation, as E28's for a write. -/
def RenameExecutedUnder (h : List Event) (e : DARM.Kernel.Invocation) (rid : Nat) : Prop :=
  ∀ op, Event.broker op ∈ h → DARM.E28.requestOf op = rid → ExecRename e op

/-- A consistently attested file placed under a rename's request: the move is
    in the history, from the rename invocation's path to its destination, and
    the content has a lineage ending at a write. -/
theorem rename_placed_lineage (h : List Event)
    (hf : Faithful AttFaithfulStep empty h) (hc : Consistent (evolve empty h))
    (t : String) (f : File) (r2 : Nat) (d : String)
    (hx : (evolve empty h).files t = some f) (ha : f.att = some (r2, d))
    (e2 : DARM.Kernel.Invocation) (hren : RenameExecutedUnder h e2 r2) :
    (∃ s, Event.broker (BrokerOp.mv r2 s t d) ∈ h ∧
        DARM.E26.hasArg e2 "path" s ∧ DARM.E26.hasArg e2 "destination" t) ∧
    ∃ chain, Lineage h r2 d chain ∧ ∃ r0 t0, Event.broker (BrokerOp.wr r0 t0 d) ∈ h ∧ r0 ∈ chain := by
  obtain ⟨op, hop, hform⟩ := DARM.E27b.attested_file_was_placed_by_broker h hc t f r2 d hx ha
  have hli := evolve_lin h [] empty hf (by
    intro x f r d hx
    simp [empty] at hx)
  obtain ⟨chain, hl⟩ : ∃ c, Lineage h r2 d c := by simpa using hli t f r2 d hx ha
  refine ⟨?_, chain, hl, lineage_origin hl⟩
  rcases hform with hwr | ⟨s, hmv⟩
  · subst hwr
    obtain ⟨_, rid, s', t', d', _, _, heq⟩ := hren _ hop rfl
    cases heq
  · subst hmv
    obtain ⟨_, rid, s', t', d', hs, ht, heq⟩ := hren _ hop rfl
    injection heq with h1 h2 h3 h4
    exact ⟨s, hop, by rw [h2]; exact hs, by rw [h3]; exact ht⟩

/-- A write of d executed for a write invocation carrying exactly c has d = c. -/
theorem write_attribution (h : List Event) (r0 : Nat) (t0 d : String)
    (hm : Event.broker (BrokerOp.wr r0 t0 d) ∈ h)
    (e1 : DARM.Kernel.Invocation) (x1 c : String)
    (hinv : DARM.E26.invocationWritesExactly x1 c e1)
    (hexec : DARM.E28.ExecutedUnder h e1 r0) : d = c := by
  obtain ⟨_, rid, pth, cnt, _, hcnt, heq⟩ := hexec _ hm rfl
  injection heq with h1 h2 h3
  rw [h3]
  exact DARM.E28.content_forced x1 c cnt e1 hinv hcnt

/-- Attribution through two requests: a file placed by a rename invocation,
    whose content was written once, under a request executed for the authorized
    write invocation, holds exactly the authorized content. -/
theorem rename_placed_content_authorized (h : List Event)
    (hf : Faithful AttFaithfulStep empty h) (hc : Consistent (evolve empty h))
    (t : String) (f : File) (r2 : Nat) (d : String)
    (hx : (evolve empty h).files t = some f) (ha : f.att = some (r2, d))
    (e2 : DARM.Kernel.Invocation) (hren : RenameExecutedUnder h e2 r2)
    (e1 : DARM.Kernel.Invocation) (x1 c : String)
    (hinv : DARM.E26.invocationWritesExactly x1 c e1)
    (r0 : Nat) (hexec : DARM.E28.ExecutedUnder h e1 r0)
    (honce : ∀ r t', Event.broker (BrokerOp.wr r t' d) ∈ h → r = r0) :
    f.digest = c := by
  obtain ⟨_, _, _, hl⟩ := rename_placed_lineage h hf hc t f r2 d hx ha e2 hren
  obtain ⟨r0', t0, hm, _⟩ := hl
  have hr : r0' = r0 := honce r0' t0 hm
  subst hr
  have hdc := write_attribution h r0' t0 d hm e1 x1 c hinv hexec
  have hdig := (DARM.E27.consistent_attested_identifies_write _ hc t f r2 d hx ha).2
  rw [hdig, hdc]

end DARM.E30

#print axioms DARM.E30.lineage_origin
#print axioms DARM.E30.evolve_lin
#print axioms DARM.E30.rename_placed_lineage
#print axioms DARM.E30.write_attribution
#print axioms DARM.E30.rename_placed_content_authorized
