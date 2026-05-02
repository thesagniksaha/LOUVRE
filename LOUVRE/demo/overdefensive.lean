/-
A liveness failure: an "always" matcher catches every input, including
benign content. Even more starkly, the replacement string itself ends up in
the source language, so liveness fails by direct decision.
-/

import LOUVRE

namespace LOUVRE.demo.overdefensive

open LOUVRE

-- the source: a `prefix "AKIA"` (real-world AWS keys)
def src : Matcher := Matcher.prefix "AKIA"

-- a matcher that catches everything (over-defensive)
def overMatcher : Matcher := Matcher.always

-- a replacement string that itself starts with `AKIA` — a literal mistake a redactor might make
def badReplacement : String := "AKIA-REDACTED"

-- liveness fails because the replacement is itself in the source class: redacting any input would replace it with another secret
theorem over_defensive_liveness_fails : ¬ CleanReplacement src badReplacement := by
  unfold CleanReplacement src badReplacement
  decide

-- a benign sample: this would be destroyed by an `always` matcher
def benignSample : String := "Meeting notes: the project ships Friday"

#eval if accepts overMatcher benignSample then
        s!"DESTRUCTIVE: '{benignSample}' would be replaced wholesale"
      else
        s!"PRESERVED: '{benignSample}'"
-- expected output: DESTRUCTIVE: ...

end LOUVRE.demo.overdefensive
