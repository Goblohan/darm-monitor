/-
  E28a — E28 UNDER ATTACK

  E28 frozen as the core result and attacked. Most attacks are stopped by its
  hypotheses (consistency, attestation, ExecutedUnder); this file mechanizes
  the four findings that are not simply "stopped".

  e28_hypotheses_satisfiable: E28's hypotheses hold together in a concrete
  instance, so the theorem is not vacuous.

  rename_mints_content: B8's rename puts d at the destination without
  requiring the source to hold d. A history of one rename from the empty world
  yields a consistent world with an attested file whose content no write ever
  produced. E28 is unaffected (ExecutedUnder rules renames out), but any
  generalization of attribution to renames must first restrict them to
  faithful renames (the source holds d when it moves), as the runtime does.

  replay_by_move_inconsistent: a replay built from foreign moves (write, move
  away, broker delete, move back) is excluded by consistency.

  e28_latest: E28's conclusion strengthened: the file's request is the latest
  log entry at the path, not merely an operation somewhere in the history.

  NOT claimed: foreign copy within E28's history model (E27b models delete,
  tamper, create and move; copy is covered by B8p's route to identity, not by
  E28); anything about renames as authorized effects.
-/
import E28AuthorizedEffectIdentity

namespace DARM.E28a

open DARM.EffectIntegrity2 (World File Op BrokerOp Consistent expected latest empty
  brokerWrite brokerDelete brokerRename)

def X : String := "/workspace/reports/q3.md"
def C : String := "Q3 summary"

/-- One authorized write, and nothing else. -/
def oneWrite : List DARM.E27b.Event := [DARM.E27b.Event.broker (BrokerOp.wr 1 X C)]

theorem oneWrite_consistent : Consistent (DARM.E27b.evolve empty oneWrite) := by
  unfold Consistent
  intro t
  by_cases ht : t = X
  · subst ht
    simp [oneWrite, DARM.E27b.evolve, DARM.E27b.step, DARM.EffectIntegrity2.apply,
      brokerWrite, expected, latest, empty]
  · have ht' : X ≠ t := fun h => ht h.symm
    simp [oneWrite, DARM.E27b.evolve, DARM.E27b.step, DARM.EffectIntegrity2.apply,
      brokerWrite, expected, latest, empty, ht, ht']

/-- E28 is not vacuous: its hypotheses hold together in a concrete instance. -/
theorem e28_hypotheses_satisfiable :
    ∃ (p : DARM.Broker.Proposal) (e : DARM.Kernel.Invocation) (rid : Nat) (f : File) (d : String),
      (DARM.E24e.pinned X C).fits p = true ∧
      DARM.Broker3.brokerStep DARM.Broker3.writeCfg p = some e ∧
      DARM.E28.ExecutedUnder oneWrite e rid ∧
      Consistent (DARM.E27b.evolve empty oneWrite) ∧
      (DARM.E27b.evolve empty oneWrite).files X = some f ∧ f.att = some (rid, d) := by
  have hfit : (DARM.E24e.pinned X C).fits DARM.Broker3.agentWritesReport = true := by
    decide +kernel
  have hsome : (DARM.Broker3.brokerStep DARM.Broker3.writeCfg
      DARM.Broker3.agentWritesReport).isSome = true := by
    decide +kernel
  cases hb : DARM.Broker3.brokerStep DARM.Broker3.writeCfg DARM.Broker3.agentWritesReport with
  | none =>
    rw [hb] at hsome
    simp at hsome
  | some e =>
    have hw := DARM.E24e.pinned_complete_general X C _ hfit ⟨e, hb⟩
    have hinv := DARM.E28.invocation_writes_exactly_of_proposal X C _ e hw hb
    refine ⟨_, e, 1, ⟨C, some (1, C)⟩, C, hfit, hb, ?_, oneWrite_consistent, ?_, rfl⟩
    · intro op hop _
      simp [oneWrite] at hop
      subst hop
      exact ⟨hinv.1, 1, X, C, DARM.E26.path_arg_of_invocationWritesExactly e hinv,
        DARM.E26.content_arg_of_invocationWritesExactly e hinv, rfl⟩
    · simp [oneWrite, DARM.E27b.evolve, DARM.E27b.step, DARM.EffectIntegrity2.apply,
        brokerWrite, empty]

/-- A single rename, from the empty world. -/
def renameOnly : List DARM.E27b.Event := [DARM.E27b.Event.broker (BrokerOp.mv 5 "/s" "/x" "evil")]

/-- B8's rename mints content: a consistent world, an attested file, and no
    write anywhere in the history that produced its content. -/
theorem rename_mints_content :
    Consistent (DARM.E27b.evolve empty renameOnly) ∧
    (DARM.E27b.evolve empty renameOnly).files "/x" = some ⟨"evil", some (5, "evil")⟩ ∧
    ∀ r t, DARM.E27b.Event.broker (BrokerOp.wr r t "evil") ∉ renameOnly := by
  refine ⟨?_, ?_, ?_⟩
  · unfold Consistent
    intro t
    by_cases h1 : t = "/x"
    · subst h1
      simp [renameOnly, DARM.E27b.evolve, DARM.E27b.step, DARM.EffectIntegrity2.apply,
        brokerRename, expected, latest, empty]
    · by_cases h2 : t = "/s"
      · subst h2
        simp [renameOnly, DARM.E27b.evolve, DARM.E27b.step, DARM.EffectIntegrity2.apply,
          brokerRename, expected, latest, empty]
      · simp [renameOnly, DARM.E27b.evolve, DARM.E27b.step, DARM.EffectIntegrity2.apply,
          brokerRename, expected, latest, empty, h1, h2, Ne.symm h1, Ne.symm h2]
  · simp [renameOnly, DARM.E27b.evolve, DARM.E27b.step, DARM.EffectIntegrity2.apply,
      brokerRename, empty]
  · intro r t h
    simp [renameOnly] at h

/-- A replay built from foreign moves. -/
def replayByMove : List DARM.E27b.Event :=
  [DARM.E27b.Event.broker (BrokerOp.wr 1 "/t" "x"),
   DARM.E27b.Event.foreign (DARM.E27b.Foreign.move "/t" "/bak"),
   DARM.E27b.Event.broker (BrokerOp.dl 2 "/t"),
   DARM.E27b.Event.foreign (DARM.E27b.Foreign.move "/bak" "/t")]

/-- Consistency excludes it: the latest entry at /t is the broker's delete. -/
theorem replay_by_move_inconsistent : ¬ Consistent (DARM.E27b.evolve empty replayByMove) := by
  intro hc
  have h := hc "/t"
  simp [replayByMove, DARM.E27b.evolve, DARM.E27b.step, DARM.E27b.applyForeign,
    DARM.EffectIntegrity2.apply, brokerWrite, brokerDelete, DARM.EffectIntegrity2.foreignMove,
    expected, latest, empty] at h

/-- E28 strengthened: the file's request is the latest log entry at the path. -/
theorem e28_latest (x c : String) (p : DARM.Broker.Proposal) (e : DARM.Kernel.Invocation)
    (hfit : (DARM.E24e.pinned x c).fits p = true)
    (hb : DARM.Broker3.brokerStep DARM.Broker3.writeCfg p = some e)
    (h : List DARM.E27b.Event) (rid : Nat) (hexec : DARM.E28.ExecutedUnder h e rid)
    (hc : Consistent (DARM.E27b.evolve empty h))
    (f : File) (d : String)
    (hf : (DARM.E27b.evolve empty h).files x = some f) (hatt : f.att = some (rid, d)) :
    latest (DARM.E27b.evolve empty h).log x = some ⟨rid, x, Op.write c⟩ := by
  have hE := DARM.E28.authorized_effect_to_attested_state x c p e hfit hb h rid hexec hc f d hf hatt
  have hl := DARM.E27.consistent_attested_identifies_write _ hc x f rid d hf hatt
  have hdc : d = c := hl.2.symm.trans hE.2.1
  rw [← hdc]
  exact hl.1

end DARM.E28a

#print axioms DARM.E28a.e28_hypotheses_satisfiable
#print axioms DARM.E28a.rename_mints_content
#print axioms DARM.E28a.replay_by_move_inconsistent
#print axioms DARM.E28a.e28_latest
