/-
  E28 — FROM AN AUTHORIZED PROPOSAL TO AN ATTESTED STATE, IN ONE THEOREM

  The capstone of the E24 to E27 chain, for any path x and content c.

  If a proposal fits the intent pinning x and c, B3 admits it as invocation e,
  the history executed e under request rid (every broker operation under rid
  corresponds to e: ExecutedUnder), and after any history of broker operations
  and foreign actions from the empty world the world is consistent and the file
  at x carries attestation (rid, d), then: e carries exactly the authorized
  payload; the file's content is exactly c; the history contains write rid x c;
  and that write corresponds to e (authorized_effect_to_attested_state).

  The proof composes proved results: pinned completeness (E24e) gives the
  proposal's payload; B3 (an admitted invocation is its canonicalization) and
  E26 (canonicalization keeps every key and value) carry it to e, now for any
  path and content (invocation_writes_exactly_of_proposal); E27b finds the
  operation under rid that placed the file; ExecutedUnder makes it correspond
  to e, which rules out a rename and makes it a write; content_forced makes its
  content c; E27 makes the file's content the attested one.

  Assumed, and stated: ExecutedUnder, the request link (in the runtime, each
  request identifier is minted for one invocation and used only for its
  execution; B8's history records requests, not invocations). Everything E27b
  and E27 assume (consistency at verification time; foreign actions never
  write the log).

  NOT claimed: anything about the implementation (its correspondence to these
  models is tested, not proved); deletes or renames as authorized effects
  (E26's correspondence covers writes); unpinned intents (P15b); the physical
  disk beyond B8's model (E2's transfer assumption).
-/
import E27bOperationIdentity
import E24eLineage

namespace DARM.E28

open DARM.EffectIntegrity2 (World File BrokerOp Consistent empty)
open DARM.Broker (Proposal)

/-- E26's bridge, for any path and content: a proposal that writes exactly x
    and c, admitted by B3 as e, gives an invocation carrying exactly x and c. -/
theorem invocation_writes_exactly_of_proposal (x c : String) (p : Proposal)
    (e : DARM.Kernel.Invocation)
    (hw : DARM.E24d.WritesExactly x c p)
    (hb : DARM.Broker3.brokerStep DARM.Broker3.writeCfg p = some e) :
    DARM.E26.invocationWritesExactly x c e := by
  have he := DARM.Broker3.executed_is_canonical _ p e hb
  obtain ⟨htool, hargs⟩ := DARM.E26.canonicalize_projection DARM.Broker3.writeCfg p
  rw [← he] at htool hargs
  obtain ⟨hpt, hall, ⟨ap, hap, hapk⟩, ⟨ac, hac, hack⟩⟩ := hw
  refine ⟨htool.trans hpt, ?_, ?_, ?_⟩
  · intro a ha
    have hm : DARM.E26.projectArg a ∈ p.args := by
      rw [← hargs]
      exact List.mem_map.mpr ⟨a, ha, rfl⟩
    exact hall _ hm
  · rw [← hargs] at hap
    obtain ⟨a, ha, hproj⟩ := List.mem_map.mp hap
    have hk : ap.1 = "path" := by first | exact hapk.1 | exact hapk
    exact ⟨a, ha, (congrArg Prod.fst hproj).trans hk⟩
  · rw [← hargs] at hac
    obtain ⟨a, ha, hproj⟩ := List.mem_map.mp hac
    have hk : ac.1 = "content" := by first | exact hack.1 | exact hack
    exact ⟨a, ha, (congrArg Prod.fst hproj).trans hk⟩

/-- An invocation carrying exactly x and c has c in every content argument. -/
theorem content_forced (x c d : String) (e : DARM.Kernel.Invocation)
    (h : DARM.E26.invocationWritesExactly x c e) (hd : DARM.E26.hasArg e "content" d) :
    d = c := by
  obtain ⟨a, ha, hk, hv⟩ := hd
  rcases h.2.1 a ha with ⟨hk', _⟩ | ⟨_, hv'⟩
  · rw [hk] at hk'
    exact absurd hk' (by decide)
  · rw [← hv, hv']

/-- The request an operation was performed under. -/
def requestOf : BrokerOp → Nat
  | .wr r _ _ => r
  | .dl r _ => r
  | .mv r _ _ _ => r

/-- The request link, stated: the history executed e under rid when every
    broker operation performed under rid corresponds to e. -/
def ExecutedUnder (h : List DARM.E27b.Event) (e : DARM.Kernel.Invocation) (rid : Nat) : Prop :=
  ∀ op, DARM.E27b.Event.broker op ∈ h → requestOf op = rid → DARM.E26.ExecCorresponds e op

/-- The capstone: an authorized agent-induced effect, followed from the
    proposal to the attested state of the world. -/
theorem authorized_effect_to_attested_state
    (x c : String) (p : Proposal) (e : DARM.Kernel.Invocation)
    (hfit : (DARM.E24e.pinned x c).fits p = true)
    (hb : DARM.Broker3.brokerStep DARM.Broker3.writeCfg p = some e)
    (h : List DARM.E27b.Event) (rid : Nat) (hexec : ExecutedUnder h e rid)
    (hc : Consistent (DARM.E27b.evolve empty h))
    (f : File) (d : String)
    (hf : (DARM.E27b.evolve empty h).files x = some f) (hatt : f.att = some (rid, d)) :
    DARM.E26.invocationWritesExactly x c e ∧ f.digest = c ∧
      DARM.E27b.Event.broker (BrokerOp.wr rid x c) ∈ h ∧
      DARM.E26.ExecCorresponds e (BrokerOp.wr rid x c) := by
  have hw : DARM.E24d.WritesExactly x c p := DARM.E24e.pinned_complete_general x c p hfit ⟨e, hb⟩
  have hinv := invocation_writes_exactly_of_proposal x c p e hw hb
  have hdig := (DARM.E27.consistent_attested_identifies_write _ hc x f rid d hf hatt).2
  obtain ⟨op, hop, hform⟩ := DARM.E27b.attested_file_was_placed_by_broker h hc x f rid d hf hatt
  rcases hform with hwr | ⟨s, hmv⟩
  · subst hwr
    have hcor := hexec _ hop rfl
    have hdc : d = c := by
      obtain ⟨_, r', pth, cnt, _, hcnt, hopeq⟩ := hcor
      injection hopeq with h1 h2 h3
      rw [h3]
      exact content_forced x c cnt e hinv hcnt
    subst hdc
    exact ⟨hinv, hdig, hop, hcor⟩
  · subst hmv
    have hcor := hexec _ hop rfl
    obtain ⟨_, r', pth, cnt, _, _, hopeq⟩ := hcor
    cases hopeq

end DARM.E28

#print axioms DARM.E28.invocation_writes_exactly_of_proposal
#print axioms DARM.E28.content_forced
#print axioms DARM.E28.authorized_effect_to_attested_state
