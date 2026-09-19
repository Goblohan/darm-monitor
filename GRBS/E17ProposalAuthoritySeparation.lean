/-
  E17 — PROPOSAL-AUTHORITY SEPARATION

  Formalizes: Proposal ≠ Authority, Intelligence ≠ Authority.
  An agent with unrestricted proposal generation cannot induce an
  unauthorized transition unless the gate independently grants authority.
-/

namespace GRBS.E17ProposalAuthoritySeparation

inductive Proposal where
  | readFile | execCode | exfilData
deriving DecidableEq

inductive Action where
  | readFile | execCode | exfilData
deriving DecidableEq

inductive St where
  | safe | compromised
deriving DecidableEq

def resolve : Proposal -> Action
  | Proposal.readFile => Action.readFile
  | Proposal.execCode => Action.execCode
  | Proposal.exfilData => Action.exfilData

def authorized : Action -> Bool
  | Action.readFile => true
  | Action.execCode => false
  | Action.exfilData => false

def step : St -> Action -> St
  | _, Action.readFile => St.safe
  | _, Action.execCode => St.compromised
  | _, Action.exfilData => St.compromised

def G : St -> Prop
  | St.safe => True
  | St.compromised => False

def AgentCanGenerate (_p : Proposal) : Prop := True

theorem agent_generates_all : forall p : Proposal, AgentCanGenerate p :=
  fun _ => trivial

theorem generation_does_not_imply_authorization :
    Not (forall p : Proposal, AgentCanGenerate p -> authorized (resolve p) = true) := by
  intro h
  exact absurd (h Proposal.execCode trivial) (by simp [resolve, authorized])

def GatedStep (p : Proposal) (s : St) : St :=
  if authorized (resolve p) then step s (resolve p) else s

theorem gated_step_preserves_safety (s : St) (hs : G s) (p : Proposal) :
    G (GatedStep p s) := by
  simp [GatedStep]
  cases p with
  | readFile => simp [resolve, authorized, step, G]
  | execCode => simp [resolve, authorized]; exact hs
  | exfilData => simp [resolve, authorized]; exact hs

theorem ungated_agent_compromises :
    exists p : Proposal, G St.safe ∧ Not (G (step St.safe (resolve p))) := by
  exact ⟨Proposal.execCode, trivial, by simp [resolve, step, G]⟩

theorem proposal_authority_separation :
    (forall p : Proposal, AgentCanGenerate p)
    ∧ Not (forall p : Proposal, AgentCanGenerate p -> authorized (resolve p) = true)
    ∧ (forall s : St, G s -> forall p : Proposal, G (GatedStep p s))
    ∧ (exists p : Proposal, G St.safe ∧ Not (G (step St.safe (resolve p)))) :=
  ⟨agent_generates_all, generation_does_not_imply_authorization,
   fun s hs p => gated_step_preserves_safety s hs p,
   ungated_agent_compromises⟩

end GRBS.E17ProposalAuthoritySeparation
