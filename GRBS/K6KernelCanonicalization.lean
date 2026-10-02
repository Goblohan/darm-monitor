/-
  K6 — CANONICALIZATION IN THE KERNEL

  Today the broker canonicalizes a proposal in Python and sends the kernel an
  invocation; that step is certified against B3 on sampled inputs. K6 fixes
  what the kernel will compute instead, from the raw proposal: well-formedness
  (no repeated keys, P14; every path-valued key, path and destination, in
  normal form), then B3's own brokerStep (provenance assigned by B2a's
  assignProv, then kernelDecide).

  Proved: on well-formed proposals k6Step is brokerStep (k6_eq_brokerStep);
  everything else is refused (k6_refuses_malformed); what k6Step admits is
  exactly canonicalize cfg p, admitted by kernelDecide (k6_admits_canonical),
  so decided = executed by construction; well-formedness gives distinct keys
  and normal paths (wellFormed_nodup, wellFormed_paths).

  Found: B3 alone admits a rename whose destination escapes its prefix with
  '..' (b3_admits_escaping_destination); the broker had the same gap until its
  pre-decision check covered destination. k6Step refuses it.

  normalPath is strict on purpose: '/', or one leading slash and components
  that are never empty, '.' or '..'. It rejects '//a', which POSIX normpath
  keeps; the broker's own check is to mirror this definition exactly.

  NOT claimed: the server and its wire format for the new request (next);
  anything after the decision.
-/
import B3BrokerModel

namespace DARM.K6

open DARM.Kernel (Invocation Decision)

def pathKeys : List String := ["path", "destination"]

/-- Split a list of characters on '/', structurally. -/
def components : List Char → List (List Char)
  | [] => [[]]
  | c :: cs =>
    match components cs with
    | [] => [[c]]
    | w :: ws => if c = '/' then [] :: w :: ws else (c :: w) :: ws

/-- The strict normal form. -/
def normalPathChars : List Char → Bool
  | ['/'] => true
  | '/' :: rest => (components rest).all (fun w => !w.isEmpty && w != ['.'] && w != ['.', '.'])
  | _ => false

def normalPath (v : String) : Bool := normalPathChars v.toList

def wellFormed (p : DARM.Broker.Proposal) : Bool :=
  decide ((p.args.map Prod.fst).Nodup) &&
  p.args.all (fun kv => !(pathKeys.contains kv.1) || normalPath kv.2)

/-- What the kernel's new path computes, from the raw proposal. -/
def k6Step (cfg : DARM.Broker3.Config) (p : DARM.Broker.Proposal) : Option Invocation :=
  if wellFormed p then DARM.Broker3.brokerStep cfg p else none

theorem k6_eq_brokerStep (cfg : DARM.Broker3.Config) (p : DARM.Broker.Proposal)
    (h : wellFormed p = true) : k6Step cfg p = DARM.Broker3.brokerStep cfg p := by
  unfold k6Step
  rw [if_pos h]

theorem k6_refuses_malformed (cfg : DARM.Broker3.Config) (p : DARM.Broker.Proposal)
    (h : wellFormed p = false) : k6Step cfg p = none := by
  unfold k6Step
  rw [if_neg (by simp [h])]

/-- Decided = executed, by construction: what k6Step admits is exactly the
    canonical invocation, and kernelDecide admitted it. -/
theorem k6_admits_canonical (cfg : DARM.Broker3.Config) (p : DARM.Broker.Proposal)
    (inv : Invocation) (h : k6Step cfg p = some inv) :
    wellFormed p = true ∧ inv = DARM.Broker3.canonicalize cfg p ∧
    DARM.Kernel4.kernelDecide cfg.policy cfg.credential (DARM.Broker3.canonicalize cfg p) =
      Decision.admit := by
  unfold k6Step at h
  by_cases hw : wellFormed p = true
  · rw [if_pos hw] at h
    unfold DARM.Broker3.brokerStep at h
    by_cases hk : DARM.Kernel4.kernelDecide cfg.policy cfg.credential
        (DARM.Broker3.canonicalize cfg p) = Decision.admit
    · rw [if_pos hk] at h
      exact ⟨hw, (Option.some.inj h).symm, hk⟩
    · rw [if_neg hk] at h
      cases h
  · rw [if_neg hw] at h
    cases h

theorem wellFormed_nodup (p : DARM.Broker.Proposal) (h : wellFormed p = true) :
    (p.args.map Prod.fst).Nodup := by
  unfold wellFormed at h
  rw [Bool.and_eq_true] at h
  exact of_decide_eq_true h.1

theorem wellFormed_paths (p : DARM.Broker.Proposal) (h : wellFormed p = true)
    (kv : String × String) (hkv : kv ∈ p.args) (hk : pathKeys.contains kv.1 = true) :
    normalPath kv.2 = true := by
  unfold wellFormed at h
  rw [Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 kv hkv
  rw [hk] at this
  simpa using this

/-! ## The finding, in the model -/

def renameCfg : DARM.Broker3.Config :=
  { policy := { tools := [{ tool := "rename_file", rules :=
      [{ key := "path", allowedValues := [], allowedPrefixes := ["/workspace/reports/"], payload := false },
       { key := "destination", allowedValues := [], allowedPrefixes := ["/workspace/reports/"], payload := false }] }] },
    credential := { tools := ["rename_file"], expired := false },
    registry := { values := [], prefixes := ["/workspace/reports/"] } }

def escaping : DARM.Broker.Proposal :=
  { tool := "rename_file",
    args := [("path", "/workspace/reports/a.md"), ("destination", "/workspace/reports/../x.md")] }

/-- B3 alone admits a rename whose destination escapes its prefix; k6Step refuses it. -/
theorem b3_admits_escaping_destination :
    (DARM.Broker3.brokerStep renameCfg escaping).isSome = true ∧
    (k6Step renameCfg escaping).isSome = false := by
  decide +kernel

theorem normalPath_examples :
    normalPath "/" = true ∧ normalPath "/workspace/reports/a.md" = true ∧
    normalPath "//a" = false ∧ normalPath "/a/" = false ∧ normalPath "/a/./b" = false ∧
    normalPath "/a/../b" = false ∧ normalPath "a/b" = false ∧ normalPath "" = false := by
  decide +kernel

end DARM.K6

#print axioms DARM.K6.k6_eq_brokerStep
#print axioms DARM.K6.k6_refuses_malformed
#print axioms DARM.K6.k6_admits_canonical
#print axioms DARM.K6.wellFormed_nodup
#print axioms DARM.K6.wellFormed_paths
#print axioms DARM.K6.b3_admits_escaping_destination
#print axioms DARM.K6.normalPath_examples
