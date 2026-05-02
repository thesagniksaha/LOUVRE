/-
Second positive demo: redaction of email-shaped tokens (anything containing
`@`). Source = matcher = `contains "@"`. The replacement `<email>` does not
contain `@`, so liveness holds.
-/

import LOUVRE

namespace LOUVRE.demo.emaildemo

open LOUVRE

def emailPolicy : RedactionPolicy where
  source       := Matcher.contains "@"
  matcher      := Matcher.contains "@"
  replacement  := "<email>"

theorem email_safety : Subsumes emailPolicy.source emailPolicy.matcher :=
  Subsumes.refl _

theorem email_liveness : CleanReplacement emailPolicy.source emailPolicy.replacement := by
  unfold CleanReplacement emailPolicy
  decide

def emailCertified : CertifiedPolicy :=
  ⟨emailPolicy, email_safety, email_liveness⟩

def draftMsg : String := "Contact me at hello@example.com for details"
def sanitizedMsg : String := redact emailPolicy draftMsg

#eval sanitizedMsg
-- expected: "Contact me at <email> for details"

def emailTrace : List Action :=
  [ .publish sanitizedMsg
  , .sanitize emailCertified draftMsg sanitizedMsg
  , .certify emailCertified
  , .propose emailPolicy
  , .draft draftMsg ]

theorem emailTrace_safe : SafeTrace emailTrace := by
  unfold emailTrace
  apply SafeTrace.published emailCertified draftMsg sanitizedMsg rfl
  apply SafeTrace.certified
  apply SafeTrace.proposed
  apply SafeTrace.drafted
  exact SafeTrace.nil

end LOUVRE.demo.emaildemo
