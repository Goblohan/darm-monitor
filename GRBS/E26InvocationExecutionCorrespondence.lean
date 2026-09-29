import B3BrokerModel
import E24dRedemption
import B8TypedEffectLog

namespace DARM.E26

open DARM.Kernel
open DARM.Broker (Proposal)
open DARM.Broker3
open DARM.E24b
open DARM.E24d
open DARM.EffectIntegrity2

/-!
E26 — Invocation / Execution Correspondence

E24d establishes proposal-level authorization completeness.
B3 canonicalizes an admitted proposal into an Invocation.
B8 defines the physical-effect vocabulary as BrokerOp.

The missing assurance edge is the preservation of the authorized
semantic payload across this boundary.

This first experiment deliberately handles only the pinned write case.
It does not yet claim a general Proposal -> Invocation -> World theorem.

NOT claimed (added on review): that the implementation matches either model.
Correspondence here is ExecCorresponds, a defined relation between two models'
vocabularies (B3 invocations and B8 operations); the existence of a
corresponding operation (invocation_writes_corresponds) holds by construction.
The substantive results are payload preservation (canonicalize_projection,
general; pinned_execution_reaches_invocation), uniqueness of write semantics
under the pinned payload, and realization in B8's world. The request
identifier is unconstrained. The implementation's correspondence to B8 is
established separately, by the B8 trace checker. Generalizing the pinned case
to any path and content is a natural next step (E24e pinned_complete_general).
-/

/-- Semantic projection of an Invocation, deliberately ignoring provenance. -/
def invocationWritesExactly
    (path content : String)
    (inv : DARM.Kernel.Invocation) : Prop :=
  inv.tool = "write_file" ∧
  (∀ a ∈ inv.args,
    (a.key = "path" ∧ a.value = path) ∨
    (a.key = "content" ∧ a.value = content)) ∧
  (∃ a ∈ inv.args, a.key = "path") ∧
  (∃ a ∈ inv.args, a.key = "content")

/-- Projection of canonical Invocation arguments back to proposal pairs. -/
def projectArg (a : DARM.Kernel.Arg) : String × String :=
  (a.key, a.value)

/-- The canonicalizer preserves tool and key/value payload exactly. -/
theorem canonicalize_projection
    (cfg : DARM.Broker3.Config) (p : Proposal) :
    (DARM.Broker3.canonicalize cfg p).tool = p.tool ∧
    (DARM.Broker3.canonicalize cfg p).args.map projectArg = p.args := by
  constructor
  · rfl
  · simp [DARM.Broker3.canonicalize, projectArg, Function.comp_def]

/-- Any proposal-level WritesExactly fact survives canonicalization,
    provided the canonical Invocation is the B3 execution result. -/
theorem writesExactly_survives_canonicalization
    (p : Proposal)
    (hwrite :
      DARM.E24d.WritesExactly
        "/workspace/reports/q3.md"
        "Q3 summary" p) :
    invocationWritesExactly
      "/workspace/reports/q3.md"
      "Q3 summary"
      (DARM.Broker3.canonicalize DARM.Broker3.writeCfg p) := by

  rcases hwrite with ⟨htool, hall, hpath, hcontent⟩

  unfold invocationWritesExactly
  constructor
  · exact htool
  · constructor
    · intro a ha
      simp only [DARM.Broker3.canonicalize] at ha
      simp only [List.mem_map] at ha
      obtain ⟨kv, hkv, rfl⟩ := ha
      rcases hall kv hkv with h | h
      · exact Or.inl h
      · exact Or.inr h

    · constructor
      · rcases hpath with ⟨a, ha, hap⟩
        refine ⟨
          { key := a.1
            value := a.2
            prov :=
              DARM.BrokerDerived.assignProv
                DARM.Broker3.writeCfg.registry
                a.2 },
          ?_,
          ?_⟩
        · simp only [DARM.Broker3.canonicalize, List.mem_map]
          exact ⟨a, ha, rfl⟩
        · exact hap

      · rcases hcontent with ⟨a, ha, hac⟩
        refine ⟨
          { key := a.1
            value := a.2
            prov :=
              DARM.BrokerDerived.assignProv
                DARM.Broker3.writeCfg.registry
                a.2 },
          ?_,
          ?_⟩
        · simp only [DARM.Broker3.canonicalize, List.mem_map]
          exact ⟨a, ha, rfl⟩
        · exact hac

/-- The pinned E24d completeness theorem therefore reaches the Invocation
    representation without changing the authorized semantic payload. -/
theorem pinned_execution_reaches_invocation :
    ∀ (p : Proposal) (e : DARM.Kernel.Invocation),
      DARM.E24d.pinnedReport.fits p = true →
      DARM.Broker3.brokerStep DARM.Broker3.writeCfg p = some e →
      invocationWritesExactly
        "/workspace/reports/q3.md"
        "Q3 summary" e := by
  intro p e hfit hb
  have hacc :
      DARM.E24d.WritesExactly
        "/workspace/reports/q3.md"
        "Q3 summary" p :=
    by
      exact DARM.E24d.pinned_complete_under_b3 p e hfit hb
  have hcanon :=
    DARM.Broker3.executed_is_canonical
      DARM.Broker3.writeCfg p e hb

  rw [hcanon]

  exact writesExactly_survives_canonicalization p hacc

/-!
Execution correspondence.

Unlike the earlier placeholder, this relation depends on the actual
Invocation payload.  `rid` remains execution metadata and is therefore
existentially quantified.
-/

/-- An Invocation contains a particular key/value pair. -/
def hasArg
    (inv : DARM.Kernel.Invocation)
    (key value : String) : Prop :=
  ∃ a ∈ inv.args, a.key = key ∧ a.value = value

/--
An Invocation corresponds to a B8 write operation exactly when its
authorized semantic payload is the same tool/path/content payload.

The relation deliberately ignores provenance here. Provenance is an
authorization property already checked by K4. This relation tests
semantic execution fidelity.
-/
def ExecCorresponds
    (inv : DARM.Kernel.Invocation)
    (op : DARM.EffectIntegrity2.BrokerOp) : Prop :=
  inv.tool = "write_file" ∧
  ∃ rid path content,
    hasArg inv "path" path ∧
    hasArg inv "content" content ∧
    op = DARM.EffectIntegrity2.BrokerOp.wr rid path content

/-- A path argument in an invocation whose payload satisfies
    `invocationWritesExactly` has exactly the requested path value. -/
theorem path_arg_of_invocationWritesExactly
    (inv : DARM.Kernel.Invocation)
    (h :
      invocationWritesExactly
        "/workspace/reports/q3.md"
        "Q3 summary"
        inv) :
    hasArg inv "path" "/workspace/reports/q3.md" := by
  rcases h with ⟨_, hall, hpath, _⟩
  rcases hpath with ⟨a, ha, hak⟩
  refine ⟨a, ha, hak, ?_⟩
  rcases hall a ha with hp | hc
  · exact hp.2
  · have : "path" = "content" := by
      exact hak.symm.trans hc.1
    simp at this

/-- A content argument in an invocation whose payload satisfies
    `invocationWritesExactly` has exactly the requested content value. -/
theorem content_arg_of_invocationWritesExactly
    (inv : DARM.Kernel.Invocation)
    (h :
      invocationWritesExactly
        "/workspace/reports/q3.md"
        "Q3 summary"
        inv) :
    hasArg inv "content" "Q3 summary" := by
  rcases h with ⟨_, hall, _, hcontent⟩
  rcases hcontent with ⟨a, ha, hak⟩
  refine ⟨a, ha, hak, ?_⟩
  rcases hall a ha with hp | hc
  · have : "content" = "path" := by
      exact hak.symm.trans hp.1
    simp at this
  · exact hc.2

/--
E26.2 positive correspondence.

An Invocation whose semantic payload is the pinned write necessarily
has a corresponding B8 BrokerOp with the same externally relevant
target and content.
-/
theorem invocation_writes_corresponds
    (inv : DARM.Kernel.Invocation)
    (h :
      invocationWritesExactly
        "/workspace/reports/q3.md"
        "Q3 summary"
        inv) :
    ∃ op : DARM.EffectIntegrity2.BrokerOp,
      ExecCorresponds inv op := by
  rcases h with ⟨htool, _, _, _⟩
  refine ⟨
    DARM.EffectIntegrity2.BrokerOp.wr
      0
      "/workspace/reports/q3.md"
      "Q3 summary",
    ?_⟩
  refine ⟨htool, 0, "/workspace/reports/q3.md", "Q3 summary", ?_, ?_, rfl⟩
  · exact path_arg_of_invocationWritesExactly inv
      ⟨htool, ‹_›, ‹_›, ‹_›⟩
  · exact content_arg_of_invocationWritesExactly inv
      ⟨htool, ‹_›, ‹_›, ‹_›⟩

/--
The pinned authorization therefore reaches an Invocation that has a
corresponding B8 write operation.
-/
theorem pinned_execution_has_corresponding_broker_op
    (p : Proposal)
    (e : DARM.Kernel.Invocation)
    (hfit : DARM.E24d.pinnedReport.fits p = true)
    (hb :
      DARM.Broker3.brokerStep
        DARM.Broker3.writeCfg p = some e) :
    ∃ op : DARM.EffectIntegrity2.BrokerOp,
      ExecCorresponds e op := by
  have hinv :=
    pinned_execution_reaches_invocation p e hfit hb
  exact invocation_writes_corresponds e hinv

/--
The externally relevant semantics of a BrokerOp.

Execution identifiers are deliberately erased.  Different `rid` values
therefore represent the same write effect when target and content agree.
-/
def writeSemantic
    (op : DARM.EffectIntegrity2.BrokerOp) :
    Option (String × String) :=
  match op with
  | DARM.EffectIntegrity2.BrokerOp.wr _ t d => some (t, d)
  | DARM.EffectIntegrity2.BrokerOp.dl _ _ => none
  | DARM.EffectIntegrity2.BrokerOp.mv _ _ _ _ => none

/--
Any operation corresponding to an Invocation with a write payload has
the semantic target/content encoded by that Invocation.
-/
theorem correspondence_semantic_projection
    (inv : DARM.Kernel.Invocation)
    (op : DARM.EffectIntegrity2.BrokerOp)
    (h : ExecCorresponds inv op) :
    ∃ path content,
      hasArg inv "path" path ∧
      hasArg inv "content" content ∧
      writeSemantic op = some (path, content) := by
  rcases h with ⟨_, rid, path, content, hpath, hcontent, hop⟩
  refine ⟨path, content, hpath, hcontent, ?_⟩
  rw [hop]
  rfl

/--
Every path argument of an invocation satisfying `invocationWritesExactly`
has the pinned path value.
-/
theorem path_value_forces_pinned
    (inv : DARM.Kernel.Invocation)
    (h : invocationWritesExactly
      "/workspace/reports/q3.md"
      "Q3 summary"
      inv)
    (a : DARM.Kernel.Arg)
    (ha : a ∈ inv.args)
    (hk : a.key = "path") :
    a.value = "/workspace/reports/q3.md" := by
  rcases h.2.1 a ha with harg | harg
  · exact harg.2
  · simp [hk] at harg

/--
Every content argument of an invocation satisfying `invocationWritesExactly`
has the pinned content value.
-/
theorem content_value_forces_pinned
    (inv : DARM.Kernel.Invocation)
    (h : invocationWritesExactly
      "/workspace/reports/q3.md"
      "Q3 summary"
      inv)
    (a : DARM.Kernel.Arg)
    (ha : a ∈ inv.args)
    (hk : a.key = "content") :
    a.value = "Q3 summary" := by
  rcases h.2.1 a ha with harg | harg
  · simp [hk] at harg
  · exact harg.2

/--
Two BrokerOps corresponding to the same pinned Invocation have identical
externally relevant write semantics.  Their execution identifiers may differ.

The `invocationWritesExactly` premise is essential.  `ExecCorresponds` alone
would permit an Invocation containing multiple conflicting path or content
arguments.
-/
theorem correspondence_same_write_semantics
    (inv : DARM.Kernel.Invocation)
    (hinv :
      invocationWritesExactly
        "/workspace/reports/q3.md"
        "Q3 summary"
        inv)
    (op₁ op₂ : DARM.EffectIntegrity2.BrokerOp)
    (h₁ : ExecCorresponds inv op₁)
    (h₂ : ExecCorresponds inv op₂) :
    writeSemantic op₁ = writeSemantic op₂ := by
  rcases h₁ with ⟨_, rid₁, path₁, content₁, hpath₁, hcontent₁, hop₁⟩
  rcases h₂ with ⟨_, rid₂, path₂, content₂, hpath₂, hcontent₂, hop₂⟩

  have hpath1 : path₁ = "/workspace/reports/q3.md" := by
    rcases hpath₁ with ⟨a, ha, hk, hv⟩
    exact hv.symm.trans (path_value_forces_pinned inv hinv a ha hk)

  have hpath2 : path₂ = "/workspace/reports/q3.md" := by
    rcases hpath₂ with ⟨a, ha, hk, hv⟩
    exact hv.symm.trans (path_value_forces_pinned inv hinv a ha hk)

  have hcontent1 : content₁ = "Q3 summary" := by
    rcases hcontent₁ with ⟨a, ha, hk, hv⟩
    exact hv.symm.trans (content_value_forces_pinned inv hinv a ha hk)

  have hcontent2 : content₂ = "Q3 summary" := by
    rcases hcontent₂ with ⟨a, ha, hk, hv⟩
    exact hv.symm.trans (content_value_forces_pinned inv hinv a ha hk)

  rw [hop₁, hop₂]
  simp [writeSemantic, hpath1, hpath2, hcontent1, hcontent2]

/--
A corresponding write BrokerOp realizes the pinned authorization in the
B8 world transition.  The resulting file contains exactly the authorized
content and carries the BrokerOp's execution attestation.
-/
theorem corresponding_write_realizes_pinned_transition
    (w : DARM.EffectIntegrity2.World)
    (inv : DARM.Kernel.Invocation)
    (hinv :
      invocationWritesExactly
        "/workspace/reports/q3.md"
        "Q3 summary"
        inv)
    (op : DARM.EffectIntegrity2.BrokerOp)
    (hcor : ExecCorresponds inv op) :
    ∃ rid : Nat,
      (DARM.EffectIntegrity2.apply w op).files
          "/workspace/reports/q3.md" =
        some
          ⟨"Q3 summary", some (rid, "Q3 summary")⟩ := by
  rcases hcor with
    ⟨_, rid, path, content, hpath, hcontent, hop⟩

  have hpath' : path = "/workspace/reports/q3.md" := by
    rcases hpath with ⟨a, ha, hk, hv⟩
    exact hv.symm.trans (path_value_forces_pinned inv hinv a ha hk)

  have hcontent' : content = "Q3 summary" := by
    rcases hcontent with ⟨a, ha, hk, hv⟩
    exact hv.symm.trans (content_value_forces_pinned inv hinv a ha hk)

  rw [hop]
  simp [DARM.EffectIntegrity2.apply,
    DARM.EffectIntegrity2.brokerWrite,
    hpath', hcontent']


/--
A coarse physical observer that sees only file contents and ignores
attestation metadata.
-/
def observedDigest
    (w : DARM.EffectIntegrity2.World)
    (path : String) : Option String :=
  (w.files path).map (fun f => f.digest)

/--
The authorized B8 write and an external creation can produce the same
digest-level observation, even though their attestation/provenance differs.
-/
theorem authorized_and_foreign_creation_same_observation
    (rid : Nat) :
    observedDigest
        (DARM.EffectIntegrity2.brokerWrite
          DARM.EffectIntegrity2.empty
          rid
          "/workspace/reports/q3.md"
          "Q3 summary")
        "/workspace/reports/q3.md"
      =
    observedDigest
        (DARM.EffectIntegrity2.create
          DARM.EffectIntegrity2.empty
          "/workspace/reports/q3.md"
          "Q3 summary")
        "/workspace/reports/q3.md" := by
  simp [observedDigest,
    DARM.EffectIntegrity2.brokerWrite,
    DARM.EffectIntegrity2.create]

/--
The two executions are not provenance-equivalent.  The broker-mediated
write records an execution entry, whereas foreign creation leaves the
audit log unchanged.
-/
theorem authorized_and_foreign_creation_have_distinct_logs
    (rid : Nat) :
    (DARM.EffectIntegrity2.brokerWrite
      DARM.EffectIntegrity2.empty
      rid
      "/workspace/reports/q3.md"
      "Q3 summary").log
      ≠
    (DARM.EffectIntegrity2.create
      DARM.EffectIntegrity2.empty
      "/workspace/reports/q3.md"
      "Q3 summary").log := by
  simp [DARM.EffectIntegrity2.brokerWrite,
    DARM.EffectIntegrity2.create]

/--
Digest-level observational equivalence therefore does not establish
authorization provenance.

The same observed content can arise from a mediated broker write or from
an external creation that carries no broker attestation.
-/
theorem observation_does_not_imply_authorization_lineage
    (rid : Nat) :
    observedDigest
        (DARM.EffectIntegrity2.brokerWrite
          DARM.EffectIntegrity2.empty
          rid
          "/workspace/reports/q3.md"
          "Q3 summary")
        "/workspace/reports/q3.md"
      =
    observedDigest
        (DARM.EffectIntegrity2.create
          DARM.EffectIntegrity2.empty
          "/workspace/reports/q3.md"
          "Q3 summary")
        "/workspace/reports/q3.md"
    ∧
    (DARM.EffectIntegrity2.brokerWrite
      DARM.EffectIntegrity2.empty
      rid
      "/workspace/reports/q3.md"
      "Q3 summary").log
      ≠
    (DARM.EffectIntegrity2.create
      DARM.EffectIntegrity2.empty
      "/workspace/reports/q3.md"
      "Q3 summary").log := by
  constructor
  · exact authorized_and_foreign_creation_same_observation rid
  · exact authorized_and_foreign_creation_have_distinct_logs rid


end DARM.E26

