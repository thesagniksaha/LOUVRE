/-
A safe trace: a Drafter writes a message containing an AWS access key, a
Sanitizer applies a `CertifiedPolicy`, and the Publisher releases the
sanitized output. `SafeTrace` accepts; the headline theorem proves no field
of the published message is in the source class.
-/

import LOUVRE

namespace LOUVRE.demo.goodtrace

open LOUVRE

-- the AWS-key policy: source = redactor = `prefix "AKIA"`. Replacement is `[REDACTED-AWS-KEY]`
def awsPolicy : RedactionPolicy where
  source       := Matcher.prefix "AKIA"
  matcher      := Matcher.prefix "AKIA"
  replacement  := "[REDACTED-AWS-KEY]"

-- safety certificate: reflexivity of subsumption (source = matcher)
theorem aws_safety : Subsumes awsPolicy.source awsPolicy.matcher :=
  Subsumes.refl _

-- liveness certificate: the replacement does not start with `AKIA`
theorem aws_liveness : CleanReplacement awsPolicy.source awsPolicy.replacement := by
  unfold CleanReplacement
  decide

-- the certified AWS-key policy
def awsCertified : CertifiedPolicy :=
  ⟨awsPolicy, aws_safety, aws_liveness⟩

-- drafter's input: a tweet draft containing a key
def draftMsg : String :=
  "Tweet draft: launching at AKIAIOSFODNN7EXAMPLE today"

-- Sanitized output
def sanitizedMsg : String := redact awsPolicy draftMsg

#eval sanitizedMsg
-- expected: "Tweet draft: launching at [REDACTED-AWS-KEY] today"

-- The good trace: draft → propose → certify → sanitize → publish
def goodTrace : List Action :=
  [ .publish sanitizedMsg
  , .sanitize awsCertified draftMsg sanitizedMsg
  , .certify awsCertified
  , .propose awsPolicy
  , .draft draftMsg ]

-- Proof that the trace is safe
theorem goodTrace_safe : SafeTrace goodTrace := by
  unfold goodTrace
  apply SafeTrace.published awsCertified draftMsg sanitizedMsg rfl
  apply SafeTrace.certified
  apply SafeTrace.proposed
  apply SafeTrace.drafted
  exact SafeTrace.nil

end LOUVRE.demo.goodtrace
