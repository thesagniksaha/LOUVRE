-- Helper lemmas for proving `Subsumes` claims on concrete `Matcher` pairs

import LOUVRE.core
import LOUVRE.policy

namespace LOUVRE

-- subsumption lemmas
-- reflexivity: every matcher subsumes itself
theorem Subsumes.refl (m : Matcher) : Subsumes m m := fun _ h => h

-- `never` is subsumed by everything
theorem Subsumes.never_subsumed (m : Matcher) : Subsumes Matcher.never m := by
  intro s h
  simp [accepts] at h

-- everything is subsumed by `always`
theorem Subsumes.subsumed_by_always (m : Matcher) : Subsumes m Matcher.always := by
  intro s _
  simp [accepts]

-- if `s` is in `m`, it's in any `anyOf` containing `m` in its head
theorem accepts_anyOf_head (m : Matcher) (ms : List Matcher) (s : String)
    (h : accepts m s = true) :
    accepts (Matcher.anyOf (m :: ms)) s = true := by
  simp [accepts, acceptsAny, h]

-- if `s` is in some matcher of `ms`, it's in `Matcher.anyOf ms`
theorem accepts_anyOf_of_mem (ms : List Matcher) (s : String)
    (m : Matcher) (hm : m ∈ ms) (hs : accepts m s = true) :
    accepts (Matcher.anyOf ms) s = true := by
  induction ms with
  | nil => exact absurd hm (by simp)
  | cons m' rest ih =>
      simp [accepts, acceptsAny]
      rcases List.mem_cons.mp hm with rfl | hm'
      · exact Or.inl hs
      · exact Or.inr (by simpa [accepts] using ih hm')

-- if a matcher subsumes some element of `ms`, it is subsumed by `anyOf ms`
theorem Subsumes.into_anyOf (src : Matcher) (ms : List Matcher)
    (m : Matcher) (hm : m ∈ ms) (h : Subsumes src m) :
    Subsumes src (Matcher.anyOf ms) := by
  intro s hs
  exact accepts_anyOf_of_mem ms s m hm (h s hs)

-- a matcher that subsumes both heads of an `anyOf` source subsumes the whole
theorem Subsumes.from_anyOf2
    {s1 s2 m : Matcher} (h1 : Subsumes s1 m) (h2 : Subsumes s2 m) :
    Subsumes (Matcher.anyOf [s1, s2]) m := by
  intro s hs
  simp [accepts, acceptsAny] at hs
  rcases hs with hs1 | hs2
  · exact h1 s hs1
  · exact h2 s hs2

-- a literal is subsumed by a prefix iff the prefix is a prefix of the literal
theorem Subsumes.literal_in_prefix (t p : String) (h : stringIsPrefixOf p t = true) :
    Subsumes (Matcher.literal t) (Matcher.prefix p) := by
  intro s hs
  simp [accepts] at hs ⊢
  rw [hs]
  exact h

-- a literal subsumes itself trivially
theorem Subsumes.literal_self (t : String) :
    Subsumes (Matcher.literal t) (Matcher.literal t) := Subsumes.refl _

end LOUVRE
