/-
A safety failure: the source class includes both `sk_test_` and `sk_live_`
prefixed keys, but the matcher only catches `sk_test_`. Lean rejects the
attempted certificate by exhibiting a counterexample string in the source
language that the matcher misses.
-/

import LOUVRE

namespace LOUVRE.demo.WeakRedactor

open LOUVRE

def stripeSource : Matcher :=
  Matcher.anyOf [Matcher.prefix "sk_test_", Matcher.prefix "sk_live_"]

def weakMatcher : Matcher := Matcher.prefix "sk_test_"

def liveKey : String := "sk_live_dangerouslyExposed"

example : accepts weakMatcher liveKey = false := by decide

example : accepts stripeSource liveKey = true := by decide

theorem weak_not_subsumes : ¬ Subsumes stripeSource weakMatcher := by
  intro h
  have hs : accepts stripeSource liveKey = true := by decide
  have hm : accepts weakMatcher liveKey = true := h liveKey hs
  have hf : accepts weakMatcher liveKey = false := by decide
  rw [hm] at hf
  exact Bool.noConfusion hf

end LOUVRE.demo.WeakRedactor
