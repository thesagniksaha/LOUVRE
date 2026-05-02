-- Policy module for LOUVRE.

import LOUVRE.core

namespace LOUVRE

-- subsumption: every string accepted by `src` is also accepted by `tgt`
def Subsumes (src tgt : Matcher) : Prop :=
  ∀ s : String, accepts src s = true → accepts tgt s = true

-- clean replacement
def CleanReplacement (src : Matcher) (rep : String) : Prop :=
  accepts src rep = false

instance (src : Matcher) (rep : String) : Decidable (CleanReplacement src rep) := by
  unfold CleanReplacement
  exact inferInstance

-- a redaction policy bundled with proofs
structure CertifiedPolicy where
  policy         : RedactionPolicy
  safety_cert    : Subsumes policy.source policy.matcher
  liveness_cert  : CleanReplacement policy.source policy.replacement

namespace CertifiedPolicy
  -- project the underlying matcher source
  @[inline] def source (cp : CertifiedPolicy) : Matcher := cp.policy.source
  -- project the matcher used at runtime
  @[inline] def matcher (cp : CertifiedPolicy) : Matcher := cp.policy.matcher
  -- project the replacement string
  @[inline] def replacement (cp : CertifiedPolicy) : String := cp.policy.replacement
end CertifiedPolicy

end LOUVRE
