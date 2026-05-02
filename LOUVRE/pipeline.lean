-- Multiagent pipeline module for LOUVRE.

import LOUVRE.core
import LOUVRE.policy
import LOUVRE.theorems

namespace LOUVRE

-- roles in a LOUVRE-governed pipeline
inductive AgentId
  | Drafter
  | Sanitizer
  | Publisher
  deriving Repr, DecidableEq, Inhabited

-- lifecycle of a candidate policy
inductive PolicyStatus
  | candidate
  | rejected
  | certified
  deriving Repr, DecidableEq, Inhabited

-- actions an agent can take in a trace
inductive Action where
  | draft     : (msg : String) → Action
  | propose   : (policy : RedactionPolicy) → Action
  | certify   : (cp : CertifiedPolicy) → Action
  | sanitize  : (cp : CertifiedPolicy) → (input : String) → (output : String) → Action
  | publish   : (msg : String) → Action

-- true iff the action is a publish, with the published message
def Action.publishedMsg : Action → Option String
  | .publish s => some s
  | _ => none

-- a safe trace is built from agent steps, with the invariant that every `publish msg` is preceded by a `sanitize cp _ msg` whose output is the redaction of its input under a CertifiedPolicy
inductive SafeTrace : List Action → Prop
  | nil : SafeTrace []
  | drafted (msg : String) (rest : List Action) (h : SafeTrace rest) :
      SafeTrace ((.draft msg) :: rest)
  | proposed (p : RedactionPolicy) (rest : List Action) (h : SafeTrace rest) :
      SafeTrace ((.propose p) :: rest)
  | certified (cp : CertifiedPolicy) (rest : List Action) (h : SafeTrace rest) :
      SafeTrace ((.certify cp) :: rest)
  | sanitized (cp : CertifiedPolicy) (input output : String)
              (heq : output = redact cp.policy input)
              (rest : List Action) (h : SafeTrace rest) :
      SafeTrace ((.sanitize cp input output) :: rest)
  | published (cp : CertifiedPolicy) (input msg : String)
              (heq : msg = redact cp.policy input)
              (rest : List Action) (h : SafeTrace rest) :
      SafeTrace ((.publish msg) :: (.sanitize cp input msg) :: rest)

-- for tokenized redaction with a CertifiedPolicy, no field of the redacted output is in the source class, `safe_field_redaction` is liftedover the list of fields
theorem redact_clean_fields (cp : CertifiedPolicy) (input : String) :
    ∀ f ∈ (fields input).map (fun g =>
              if accepts cp.matcher g then cp.replacement else g),
        accepts cp.source f = false := by
  intro f hf
  rcases List.mem_map.mp hf with ⟨g, _, hg⟩
  rw [← hg]
  exact safe_field_redaction cp g

-- if a publish-sanitize pair is at the head of a safe trace, the published message is the redaction of some input under a certified policy, and every field of the redacted output is secret-clean
theorem published_secret_clean
    (cp : CertifiedPolicy) (input msg : String) (rest : List Action)
    (_h : SafeTrace ((.publish msg) :: (.sanitize cp input msg) :: rest))
    (_heq : msg = redact cp.policy input) :
    ∀ f ∈ (fields input).map (fun g =>
              if accepts cp.matcher g then cp.replacement else g),
        accepts cp.source f = false :=
  redact_clean_fields cp input

end LOUVRE
