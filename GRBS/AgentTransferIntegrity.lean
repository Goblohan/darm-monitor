import R5AssuranceConservation

namespace GRBS.AgentTransferIntegrity

open GRBS.R5AssuranceConservation

inductive Tool where
  | fileRead
  | codeExec
  | networkReq
deriving DecidableEq

def authorized : Tool -> Prop
  | Tool.fileRead => True
  | Tool.codeExec => False
  | Tool.networkReq => False

def credential : Tool -> Prop
  | Tool.fileRead => True
  | _ => False

def request : Tool -> Prop
  | Tool.fileRead => True
  | Tool.codeExec => True
  | Tool.networkReq => False

theorem credential_is_valid :
    SourceAssured Tool credential authorized := by
  intro t ht
  cases t with
  | fileRead => trivial
  | codeExec => simp [credential] at ht
  | networkReq => simp [credential] at ht

theorem codeExec_is_delta :
    Delta Tool credential request Tool.codeExec := by
  constructor
  · trivial
  · simp [credential]

theorem obligation_not_dischargeable :
    Not (DeltaObligation Tool credential request authorized) := by
  intro h
  exact h Tool.codeExec codeExec_is_delta

theorem request_not_authorized :
    Not (TargetAssured Tool request authorized) := by
  intro h
  exact h Tool.codeExec trivial

def fullyAuthorized : Tool -> Prop := fun _ => True

theorem full_authorization_discharges :
    DeltaObligation Tool credential request fullyAuthorized := by
  intro _t _; trivial

theorem authorized_request_succeeds :
    TargetAssured Tool request fullyAuthorized :=
  target_assured_of_source_and_delta Tool credential request fullyAuthorized
    (fun _ _ => trivial) full_authorization_discharges

theorem agent_transfer_integrity :
    SourceAssured Tool credential authorized
    ∧ Delta Tool credential request Tool.codeExec
    ∧ Not (DeltaObligation Tool credential request authorized)
    ∧ Not (TargetAssured Tool request authorized) :=
  ⟨credential_is_valid, codeExec_is_delta,
   obligation_not_dischargeable, request_not_authorized⟩

end GRBS.AgentTransferIntegrity
