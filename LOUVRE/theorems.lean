-- Theorems module for LOUVRE.

import LOUVRE.core
import LOUVRE.policy

namespace LOUVRE

-- Theorem 1 (Safety): a redacted field is never a secret
theorem safe_field_redaction (cp : CertifiedPolicy) (f : String) :
    accepts cp.source (if accepts cp.matcher f then cp.replacement else f) = false := by
  by_cases hm : accepts cp.matcher f = true
  · -- field matched matcher, was replaced; apply liveness certificate
    rw [if_pos hm]
    exact cp.liveness_cert
  · -- field did not match matcher; apply contrapositive of safety
    rw [if_neg hm]
    -- bool case-analyse on `accepts cp.source f`
    cases h : accepts cp.source f with
    | false => rfl
    | true  => exact absurd (cp.safety_cert f h) hm

-- Theorem 2 (Liveness): benign fields pass through unchanged
theorem benign_field_preserved (cp : CertifiedPolicy) (f : String)
    (h : accepts cp.matcher f = false) :
    (if accepts cp.matcher f then cp.replacement else f) = f := by
  rw [h]
  simp

theorem live_preserves_benign (cp : CertifiedPolicy) (fs : List String)
    (h : ∀ f ∈ fs, accepts cp.matcher f = false) :
    fs.map (fun f => if accepts cp.matcher f then cp.replacement else f) = fs := by
  induction fs with
  | nil => rfl
  | cons f rest ih =>
    have hf : accepts cp.matcher f = false :=
      h f (by simp)
    have hrest : ∀ g ∈ rest, accepts cp.matcher g = false :=
      fun g hg => h g (by simp [hg])
    simp [List.map_cons, benign_field_preserved cp f hf, ih hrest]

-- Theorem 3: A matched secret is genuinely changed
theorem redact_changes_matched_secret (cp : CertifiedPolicy) (f : String)
    (hsec : accepts cp.source f = true) (hne : f ≠ cp.replacement) :
    (if accepts cp.matcher f then cp.replacement else f) ≠ f := by
  have hm : accepts cp.matcher f = true := cp.safety_cert f hsec
  rw [if_pos hm]
  exact fun h => hne h.symm

-- Theorem 4: Compositional safety under alternation
theorem subsumes_anyOf
    {s1 s2 m1 m2 : Matcher}
    (h1 : Subsumes s1 m1) (h2 : Subsumes s2 m2) :
    Subsumes (Matcher.anyOf [s1, s2]) (Matcher.anyOf [m1, m2]) := by
  intro s hs
  simp [accepts, acceptsAny] at hs ⊢
  rcases hs with h1' | h2'
  · exact Or.inl (h1 s h1')
  · exact Or.inr (h2 s h2')

-- Theorem 5: Sequential composition of two certified policies
-- replace `f` with the policy's replacement iff the matcher accepts
def stepRedact (cp : CertifiedPolicy) (f : String) : String :=
  if accepts cp.matcher f then cp.replacement else f

theorem safe_field_compose_seq
    (cp1 cp2 : CertifiedPolicy) (f : String)
    (no_cross : accepts cp1.source cp2.replacement = false) :
    accepts cp1.source (stepRedact cp2 (stepRedact cp1 f)) = false ∧
    accepts cp2.source (stepRedact cp2 (stepRedact cp1 f)) = false := by
  unfold stepRedact
  by_cases hm1 : accepts cp1.matcher f = true
  · -- after cp1: the field becomes cp1.replacement
    rw [if_pos hm1]
    by_cases hm2 : accepts cp2.matcher cp1.replacement = true
    · -- after cp2: the field becomes cp2.replacement
      rw [if_pos hm2]
      exact ⟨no_cross, cp2.liveness_cert⟩
    · -- after cp2: the field stays as cp1.replacement
      rw [if_neg hm2]
      refine ⟨cp1.liveness_cert, ?_⟩
      -- need: accepts cp2.source cp1.replacement = false
      -- from hm2: accepts cp2.matcher cp1.replacement ≠ true
      -- contrapositive of cp2.safety_cert closes this
      cases h : accepts cp2.source cp1.replacement with
      | false => rfl
      | true  => exact absurd (cp2.safety_cert _ h) hm2
  · -- after cp1: the field stays as f
    rw [if_neg hm1]
    by_cases hm2 : accepts cp2.matcher f = true
    · -- after cp2: the field becomes cp2.replacement
      rw [if_pos hm2]
      exact ⟨no_cross, cp2.liveness_cert⟩
    · -- after cp2: the field stays as f
      rw [if_neg hm2]
      refine ⟨?_, ?_⟩
      · -- accepts cp1.source f = false by contrapositive of cp1.safety_cert
        cases h : accepts cp1.source f with
        | false => rfl
        | true  => exact absurd (cp1.safety_cert _ h) hm1
      · -- accepts cp2.source f = false by contrapositive of cp2.safety_cert
        cases h : accepts cp2.source f with
        | false => rfl
        | true  => exact absurd (cp2.safety_cert _ h) hm2

theorem compose_seq_safe
    (cp1 cp2 : CertifiedPolicy)
    (no_cross : accepts cp1.source cp2.replacement = false)
    (fs : List String) :
    ∀ g ∈ fs.map (fun f => stepRedact cp2 (stepRedact cp1 f)),
        accepts cp1.source g = false ∧ accepts cp2.source g = false := by
  intro g hg
  rcases List.mem_map.mp hg with ⟨f, _, heq⟩
  rw [← heq]
  exact safe_field_compose_seq cp1 cp2 f no_cross

-- Theorem 6: Noninterference of redaction
-- two fields are *secret-equivalent* under a certified policy iff they are literally equal or both lie in the source class
def secretEquiv (cp : CertifiedPolicy) (f1 f2 : String) : Prop :=
  f1 = f2 ∨ (accepts cp.source f1 = true ∧ accepts cp.source f2 = true)

theorem stepRedact_noninterference
    (cp : CertifiedPolicy) (f1 f2 : String)
    (h : secretEquiv cp f1 f2) :
    stepRedact cp f1 = stepRedact cp f2 := by
  unfold secretEquiv at h
  unfold stepRedact
  rcases h with rfl | ⟨h1, h2⟩
  · rfl
  · have hm1 : accepts cp.matcher f1 = true := cp.safety_cert f1 h1
    have hm2 : accepts cp.matcher f2 = true := cp.safety_cert f2 h2
    rw [if_pos hm1, if_pos hm2]

inductive ListSecretEquiv (cp : CertifiedPolicy) : List String → List String → Prop
  | nil : ListSecretEquiv cp [] []
  | cons (f1 f2 : String) (fs1 fs2 : List String)
         (hpair : secretEquiv cp f1 f2)
         (hrest : ListSecretEquiv cp fs1 fs2) :
         ListSecretEquiv cp (f1 :: fs1) (f2 :: fs2)

theorem listStepRedact_noninterference
    (cp : CertifiedPolicy) (fs1 fs2 : List String)
    (h : ListSecretEquiv cp fs1 fs2) :
    fs1.map (stepRedact cp) = fs2.map (stepRedact cp) := by
  induction h with
  | nil => rfl
  | cons f1 f2 fs1' fs2' hpair _ ih =>
    rw [List.map_cons, List.map_cons,
        stepRedact_noninterference cp f1 f2 hpair, ih]

theorem redact_noninterference
    (cp : CertifiedPolicy) (s1 s2 : String)
    (h : ListSecretEquiv cp (fields s1) (fields s2)) :
    unfields ((fields s1).map (stepRedact cp)) =
    unfields ((fields s2).map (stepRedact cp)) := by
  rw [listStepRedact_noninterference cp _ _ h]

-- Theorem 7: N-ary sequential composition
-- generalises `compose_seq_safe` from two policies to a list of policies

def applyAll : List CertifiedPolicy → String → String
  | [],          f => f
  | cp :: rest,  f => applyAll rest (stepRedact cp f)

def crossClean (cps : List CertifiedPolicy) : Prop :=
  ∀ cp1 ∈ cps, ∀ cp2 ∈ cps, accepts cp1.source cp2.replacement = false

theorem applyAll_form (cps : List CertifiedPolicy) (f : String) :
    applyAll cps f = f ∨ ∃ cp ∈ cps, applyAll cps f = cp.replacement := by
  induction cps generalizing f with
  | nil => left; rfl
  | cons cp rest ih =>
    by_cases hm : accepts cp.matcher f = true
    · have hg : stepRedact cp f = cp.replacement := by
        unfold stepRedact; rw [if_pos hm]
      show applyAll rest (stepRedact cp f) = f ∨
            ∃ cp' ∈ cp :: rest, applyAll rest (stepRedact cp f) = cp'.replacement
      rw [hg]
      rcases ih cp.replacement with hkeep | ⟨cp', hcp', heq⟩
      · right; exact ⟨cp, List.mem_cons_self, hkeep⟩
      · right; exact ⟨cp', List.mem_cons_of_mem _ hcp', heq⟩
    · have hg : stepRedact cp f = f := by
        unfold stepRedact; rw [if_neg hm]
      show applyAll rest (stepRedact cp f) = f ∨
            ∃ cp' ∈ cp :: rest, applyAll rest (stepRedact cp f) = cp'.replacement
      rw [hg]
      rcases ih f with hkeep | ⟨cp', hcp', heq⟩
      · left; exact hkeep
      · right; exact ⟨cp', List.mem_cons_of_mem _ hcp', heq⟩

-- N-ary safety: after applying a `crossClean` list of policies, no field of the result lies in any of the policies' source classes
theorem applyAll_safe
    (cps : List CertifiedPolicy)
    (no_cross : crossClean cps)
    (f : String) :
    ∀ cp ∈ cps, accepts cp.source (applyAll cps f) = false := by
  induction cps generalizing f with
  | nil => intro cp hcp; exact absurd hcp (by simp)
  | cons cp1 rest ih =>
    intro cp hcp
    show accepts cp.source (applyAll rest (stepRedact cp1 f)) = false
    rcases List.mem_cons.mp hcp with heq | hcp_rest
    · -- cp = cp1 (use heq to keep cp1 explicit).
      rw [heq]
      rcases applyAll_form rest (stepRedact cp1 f) with hkeep | ⟨cp', hcp', heq2⟩
      · rw [hkeep]
        unfold stepRedact
        by_cases hm : accepts cp1.matcher f = true
        · rw [if_pos hm]; exact cp1.liveness_cert
        · rw [if_neg hm]
          cases h : accepts cp1.source f with
          | false => rfl
          | true  => exact absurd (cp1.safety_cert _ h) hm
      · rw [heq2]
        exact no_cross cp1 List.mem_cons_self cp' (List.mem_cons_of_mem _ hcp')
    · -- cp ∈ rest: apply IH with smaller crossClean.
      have crossRest : crossClean rest := fun a ha b hb =>
        no_cross a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)
      exact ih crossRest (stepRedact cp1 f) cp hcp_rest

end LOUVRE
