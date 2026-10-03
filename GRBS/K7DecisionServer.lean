/-
  K7 DECISION SERVER (kernel-v0.4.0)

  The kernel's root executable. Every request may carry a "nonce"; the kernel
  copies it into its reply, in every reply form (admission, rejection,
  malformed proposal, and the old request form). A request without a nonce is
  answered exactly as by kernel-v0.3.0.

  The broker accepts an admission only if its decision is exactly "admit" and,
  when it sent a nonce, the reply carries that nonce (pyAdmits7).

  Proved: every K6 reply has one of three shapes (handleLine6_shape), so the
  nonce can be added to all of them, read back exactly (shape_nonce), without
  changing whether the reply admits (shape_admits); a request carrying a nonce
  gets a reply carrying it (nonce_echoed); an accepted admission for nonce s
  answers a request that carried s, so a reply produced for any other request
  cannot be accepted (reply_names_its_request); and an accepted admission still
  means the proved kernel admitted that request (admit7_only_by_kernel).

  Assumed, and stated: the broker never reuses a nonce (it draws a fresh random
  one per request). Trusted, as in K5 and K6: the Lean compiler and runtime,
  Json.parse and the derived instances, the I/O loop, the broker's json.loads
  and its decoder matching pyAdmits7.
-/
import K6DecisionServer

open Lean

def nonceOf (line : String) : Option String :=
  match Json.parse line with
  | .ok j => (j.getObjValAs? String "nonce").toOption
  | .error _ => none

def addNonce (s : String) : Json → Json
  | .obj kvs => .obj (kvs.insert "nonce" (Json.str s))
  | j => j

def withNonce : Option String → Json → Json
  | none, j => j
  | some s, j => addNonce s j

def handleLine7 (line : String) : Json := withNonce (nonceOf line) (handleLine6 line)

partial def serveLoop7 (stdin stdout : IO.FS.Stream) : IO Unit := do
  let line ← stdin.getLine
  if line.isEmpty then return
  let t := line.trim
  unless t.isEmpty do
    stdout.putStrLn (handleLine7 t).compress
    stdout.flush
  serveLoop7 stdin stdout

def main : IO Unit := do
  serveLoop7 (← IO.getStdin) (← IO.getStdout)

namespace DARM.K7

/-- The broker's nonce check: no nonce sent, nothing to check; otherwise the
    reply must carry exactly that nonce. -/
def pyNonceOk (sent : Option String) (j : Json) : Bool :=
  match sent with
  | none => true
  | some n =>
    match j.getObjValAs? String "nonce" with
    | .ok m => m == n
    | .error _ => false

def pyAdmits7 (sent : Option String) (j : Json) : Bool :=
  DARM.K5.pyAdmits j && pyNonceOk sent j

/-- The three shapes a K6 reply can take. -/
def Shape (j : Json) : Prop :=
  (∃ d, j = decisionJson4 d) ∨ (∃ inv, j = replyFor inv .admit) ∨ (∃ e, j = DARM.K5.errorJson e)

theorem handleLine6_shape (line : String) : Shape (handleLine6 line) := by
  rcases DARM.K6Server.reply6_cases line with ⟨req, _, hr⟩ | hr
  · rw [hr]
    unfold handleRequest6
    split
    · cases hd : DARM.Kernel4.kernelDecide (cfgOf req).policy (cfgOf req).credential
          (DARM.Broker3.canonicalize (cfgOf req) req.proposal) with
      | admit => exact Or.inr (Or.inl ⟨_, rfl⟩)
      | reject f => exact Or.inl ⟨.reject f, rfl⟩
    · exact Or.inr (Or.inr ⟨"malformed proposal", rfl⟩)
  · rw [hr]
    rcases DARM.K5.reply_cases line with ⟨_, _, hr4⟩ | ⟨e, hr4⟩
    · rw [hr4]
      exact Or.inl ⟨_, rfl⟩
    · rw [hr4]
      exact Or.inr (Or.inr ⟨e, rfl⟩)

theorem shape_nonce (j : Json) (hj : Shape j) (s : String) :
    (addNonce s j).getObjValAs? String "nonce" = .ok s := by
  rcases hj with ⟨d, rfl⟩ | ⟨inv, rfl⟩ | ⟨e, rfl⟩
  · cases d with
    | admit => rfl
    | reject f => cases f <;> rfl
  · rfl
  · rfl

theorem shape_admits (j : Json) (hj : Shape j) (s : String) :
    DARM.K5.pyAdmits (addNonce s j) = DARM.K5.pyAdmits j := by
  rcases hj with ⟨d, rfl⟩ | ⟨inv, rfl⟩ | ⟨e, rfl⟩
  · cases d with
    | admit => rfl
    | reject f => cases f <;> rfl
  · rfl
  · rfl

/-- A request carrying a nonce gets a reply carrying it. -/
theorem nonce_echoed (line s : String) (h : nonceOf line = some s) :
    (handleLine7 line).getObjValAs? String "nonce" = .ok s := by
  unfold handleLine7
  rw [h]
  exact shape_nonce _ (handleLine6_shape line) s

/-- The replay closure: if the broker accepts an admission for nonce s, the
    request that reply answers carried s. -/
theorem reply_names_its_request (line s s' : String) (hn : nonceOf line = some s')
    (h : pyAdmits7 (some s) (handleLine7 line) = true) : s' = s := by
  have he := nonce_echoed line s' hn
  unfold pyAdmits7 pyNonceOk at h
  rw [he] at h
  simp at h
  exact h.2

/-- And an accepted admission still means the proved kernel admitted it. -/
theorem admit7_only_by_kernel (line : String) (sent : Option String)
    (h : pyAdmits7 sent (handleLine7 line) = true) :
    (∃ req, (Json.parse line >>= fromJson? : Except String KernelRequest6) = .ok req ∧
        DARM.K6.k6Step (cfgOf req) req.proposal =
          some (DARM.Broker3.canonicalize (cfgOf req) req.proposal)) ∨
    (∃ req, (Json.parse line >>= fromJson? : Except String KernelRequest4) = .ok req ∧
        DARM.Kernel4.kernelDecide req.policy req.credential req.invocation = .admit) := by
  have ha : DARM.K5.pyAdmits (handleLine7 line) = true := by
    unfold pyAdmits7 at h
    rw [Bool.and_eq_true] at h
    exact h.1
  have h6 : DARM.K5.pyAdmits (handleLine6 line) = true := by
    unfold handleLine7 at ha
    cases hn : nonceOf line with
    | none =>
      rw [hn] at ha
      exact ha
    | some s =>
      rw [hn] at ha
      rw [← shape_admits _ (handleLine6_shape line) s]
      exact ha
  exact DARM.K6Server.admit_only_by_kernel6 line h6

end DARM.K7

#print axioms DARM.K7.handleLine6_shape
#print axioms DARM.K7.shape_nonce
#print axioms DARM.K7.nonce_echoed
#print axioms DARM.K7.reply_names_its_request
#print axioms DARM.K7.admit7_only_by_kernel
