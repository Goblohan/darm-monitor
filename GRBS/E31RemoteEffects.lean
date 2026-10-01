/-
  E31 — REMOTE EFFECTS: WHAT TRANSFERS FROM THE FILESYSTEM, AND WHAT BREAKS

  The first domain orthogonal to the filesystem: an HTTP or API service whose
  state the broker cannot, in general, observe. A request is an endpoint and a
  body; the service applies a delivered request by adding a record. The broker
  logs each request it sends, with the outcome it saw (ok, or timeout). A
  request may be delivered (applied; its response may still be lost), dropped
  before delivery, or sent by a foreign client. A service may echo the
  request's identifier into the record it creates; foreign clients cannot
  produce the broker's identifiers (the remote form of unforgeability).

  Proved: with an echoing service, every record tagged with a request
  identifier was produced by the broker's delivered request under that
  identifier, with exactly that endpoint and body, in any history including
  foreign clients (echoed_record_attributed): execution identity, remotely.
  Without echo, a request delivered with its response lost and a request
  dropped while a foreign client sent the identical one reach the identical
  world, so no function of what can be observed attributes the record
  (no_attribution_without_echo, observation_cannot_attribute); with echo the
  worlds differ (echo_distinguishes). And from the broker's own record after a
  timeout, no retry decision is exactly-once: it applies the effect twice in
  one case or not at all in the other (no_exactly_once_from_own_record).

  The proposal side transfers unchanged: completeness, its characterization and
  composition are about proposals and boundaries, not about what a tool does.
  What breaks is everything that rested on observing the target: compare-and-
  swap, reconciliation, attestation on the effect. Attribution and
  exactly-once hold precisely when the remote state carries the request's
  identity, as the characterization of completeness predicts.

  NOT claimed: any particular API's semantics; that echoed identifiers are
  unforgeable in practice (an assumption, as signing keys are on the
  filesystem); reads of remote state (a service that can be queried by
  identifier makes outcomes observable, which is the echo assumption again).
-/
namespace DARM.E31

structure Req where
  endpoint : String
  body : String
  deriving DecidableEq, Repr

structure Record where
  endpoint : String
  body : String
  tag : Option Nat
  deriving DecidableEq, Repr

inductive Outcome where
  | ok
  | timeout
  deriving DecidableEq, Repr

/-- What the broker records about a request it sent. -/
structure Sent where
  rid : Nat
  req : Req
  outcome : Outcome
  deriving DecidableEq, Repr

structure W where
  remote : List Record
  log : List Sent
  deriving DecidableEq, Repr

inductive Ev where
  | brokerDelivered (rid : Nat) (r : Req) (echo : Bool) (seen : Outcome)
  | brokerDropped (rid : Nat) (r : Req)
  | foreign (r : Req)

def stepE (w : W) : Ev → W
  | .brokerDelivered rid r echo seen =>
    { remote := w.remote ++ [⟨r.endpoint, r.body, if echo then some rid else none⟩],
      log := w.log ++ [⟨rid, r, seen⟩] }
  | .brokerDropped rid r => { w with log := w.log ++ [⟨rid, r, .timeout⟩] }
  | .foreign r => { w with remote := w.remote ++ [⟨r.endpoint, r.body, none⟩] }

def run (w : W) : List Ev → W
  | [] => w
  | e :: es => run (stepE w e) es

def W0 : W := ⟨[], []⟩

/-! ## Identity, with an echoing service -/

def EchoInv (done : List Ev) (w : W) : Prop :=
  ∀ rec ∈ w.remote, ∀ rid, rec.tag = some rid →
    ∃ seen, Ev.brokerDelivered rid ⟨rec.endpoint, rec.body⟩ true seen ∈ done

theorem echo_step (done : List Ev) (w : W) (e : Ev) (h : EchoInv done w) :
    EchoInv (done ++ [e]) (stepE w e) := by
  intro rec hrec rid htag
  cases e with
  | brokerDelivered r0 q echo seen =>
    simp only [stepE, List.mem_append, List.mem_singleton] at hrec
    rcases hrec with hold | hnew
    · obtain ⟨s, hm⟩ := h rec hold rid htag
      exact ⟨s, List.mem_append_left _ hm⟩
    · subst hnew
      cases echo with
      | false => simp at htag
      | true =>
        simp at htag
        subst htag
        exact ⟨seen, List.mem_append_right _ (List.mem_singleton.mpr rfl)⟩
  | brokerDropped r0 q =>
    simp only [stepE] at hrec
    obtain ⟨s, hm⟩ := h rec hrec rid htag
    exact ⟨s, List.mem_append_left _ hm⟩
  | foreign q =>
    simp only [stepE, List.mem_append, List.mem_singleton] at hrec
    rcases hrec with hold | hnew
    · obtain ⟨s, hm⟩ := h rec hold rid htag
      exact ⟨s, List.mem_append_left _ hm⟩
    · subst hnew
      simp at htag

theorem echo_run (es : List Ev) :
    ∀ (done : List Ev) (w : W), EchoInv done w → EchoInv (done ++ es) (run w es) := by
  induction es with
  | nil =>
    intro done w h
    simpa [run] using h
  | cons e es ih =>
    intro done w h
    have := ih (done ++ [e]) (stepE w e) (echo_step done w e h)
    simpa [run, List.append_assoc] using this

/-- Remote execution identity: a record tagged with a request identifier was
    produced by the broker's delivered request under it, with exactly that
    endpoint and body, whatever foreign clients did. -/
theorem echoed_record_attributed (h : List Ev) (rec : Record)
    (hrec : rec ∈ (run W0 h).remote) (rid : Nat) (htag : rec.tag = some rid) :
    ∃ seen, Ev.brokerDelivered rid ⟨rec.endpoint, rec.body⟩ true seen ∈ h := by
  have hi := echo_run h [] W0 (by
    intro rec hrec
    simp [W0] at hrec)
  simpa using hi rec hrec rid htag

/-! ## Without echo, attribution is impossible -/

def order : Req := ⟨"/orders", "pay 10"⟩

/-- Delivered, response lost. -/
def delivered : List Ev := [.brokerDelivered 1 order false .timeout]
/-- Dropped; a foreign client sends the identical request. -/
def droppedThenForeign : List Ev := [.brokerDropped 1 order, .foreign order]

theorem no_attribution_without_echo :
    run W0 delivered = run W0 droppedThenForeign ∧
    (∃ seen, Ev.brokerDelivered 1 order false seen ∈ delivered) ∧
    (∀ echo seen, Ev.brokerDelivered 1 order echo seen ∉ droppedThenForeign) := by
  refine ⟨by decide, ⟨.timeout, by simp [delivered]⟩, ?_⟩
  intro echo seen h
  simp [droppedThenForeign] at h

/-- Hence no function of the observable world attributes the record. -/
theorem observation_cannot_attribute (attr : W → Bool) :
    attr (run W0 delivered) = attr (run W0 droppedThenForeign) := by
  rw [no_attribution_without_echo.1]

/-- With echo, the two worlds differ. -/
def deliveredEcho : List Ev := [.brokerDelivered 1 order true .timeout]

theorem echo_distinguishes : run W0 deliveredEcho ≠ run W0 droppedThenForeign := by
  decide

/-! ## Exactly-once is impossible from the broker's own record -/

def wDel : W := run W0 [.brokerDelivered 1 order false .timeout]
def wDrop : W := run W0 [.brokerDropped 1 order]

/-- After a timeout, the broker's record is the same whether the request was
    applied or dropped, so any retry decision based on it applies the effect
    twice in one case or not at all in the other. -/
theorem no_exactly_once_from_own_record (retry : List Sent → Bool) :
    (retry wDel.log = true ∧ (run wDel [.brokerDelivered 2 order false .ok]).remote.length = 2) ∨
    (retry wDrop.log = false ∧ wDrop.remote.length = 0) := by
  have hl : wDel.log = wDrop.log := by decide
  cases hr : retry wDel.log with
  | true =>
    left
    exact ⟨rfl, by decide⟩
  | false =>
    right
    rw [← hl]
    exact ⟨hr, by decide⟩

end DARM.E31

#print axioms DARM.E31.echoed_record_attributed
#print axioms DARM.E31.no_attribution_without_echo
#print axioms DARM.E31.observation_cannot_attribute
#print axioms DARM.E31.echo_distinguishes
#print axioms DARM.E31.no_exactly_once_from_own_record
