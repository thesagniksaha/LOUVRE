/-
Demonstrates `compose_seq_safe`: applying two CertifiedPolicies in sequence
(here, AWS-key redaction followed by email redaction) preserves safety
provided the cross-policy side condition holds: the email replacement
`<email>` is not itself an AWS key, and vice versa is checked separately.
-/

import LOUVRE
import LOUVRE.demo.goodtrace
import LOUVRE.demo.emaildemo

namespace LOUVRE.demo.Compose

open LOUVRE LOUVRE.demo.goodtrace LOUVRE.demo.emaildemo

-- The cross-policy side condition: the email policy's replacement `<email>` is not an AWS key (does not start with `AKIA`)
theorem email_replacement_not_aws_secret :
    accepts awsCertified.source emailCertified.replacement = false := by
  unfold awsCertified emailCertified emailPolicy awsPolicy
  decide

theorem aws_then_email_safe (fs : List String) :
    ∀ g ∈ fs.map (fun f => stepRedact emailCertified (stepRedact awsCertified f)),
        accepts awsCertified.source g = false ∧
        accepts emailCertified.source g = false :=
  compose_seq_safe awsCertified emailCertified email_replacement_not_aws_secret fs

-- a concrete input mixing AWS keys and emails
def mixedInput : String :=
  "Reach me at hello@example.com or use AKIAIOSFODNN7EXAMPLE for now"

#eval mixedInput.splitOn " " |>.filter (· != "")
  |>.map (fun f => stepRedact emailCertified (stepRedact awsCertified f))
  |> String.intercalate " "
-- expected: "Reach me at <email> or use [REDACTED-AWS-KEY] for now"

end LOUVRE.demo.Compose
