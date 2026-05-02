/-
An unsafe trace: the Drafter writes a message containing an AWS key, and the
Publisher tries to release it without going through the Sanitizer. The
inductive `SafeTrace` predicate cannot be constructed for this trace, so we
have a proof that no `SafeTrace` derivation exists.
-/

import LOUVRE
import LOUVRE.demo.goodTrace

namespace LOUVRE.demo.badtrace

open LOUVRE LOUVRE.demo.goodtrace

def badTrace : List Action :=
  [ .publish draftMsg
  , .draft draftMsg ]

theorem badTrace_unsafe : ¬ SafeTrace badTrace := by
  intro h
  unfold badTrace at h
  cases h
  -- all `SafeTrace` constructors that match `(.publish _) :: rest` require
  -- `rest` to start with `.sanitize`. In `badTrace`, `rest = [.draft ...]`,
  -- so no constructor applies

end LOUVRE.demo.badtrace
