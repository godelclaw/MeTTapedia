import Mettapedia.Computability.PNP.BitVec
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Fin

/-!
# First-active feature lemmas

Generic facts about the first active Boolean feature in a fixed finite order.
These lemmas are shared by exact-ZAB and shared-affine decision-list
obstructions, so they live below those route-specific modules.
-/

namespace Mettapedia.Computability.PNP

section FirstActive

open Fin

/-- The first active feature in the fixed order `0, 1, ..., r-1`, if any. -/
noncomputable def firstActiveFeature? {r : Nat} (featureVec : BitVec r) : Option (Fin r) := by
  classical
  let active : Finset (Fin r) := (Finset.univ : Finset (Fin r)).filter fun j => featureVec j
  exact if h : active.Nonempty then some (active.min' h) else none

theorem firstActiveFeature?_eq_some_iff
    {r : Nat} (featureVec : BitVec r) (j : Fin r) :
    firstActiveFeature? featureVec = some j ↔
      featureVec j = true ∧ ∀ i, i < j → featureVec i = false := by
  classical
  let active : Finset (Fin r) := (Finset.univ : Finset (Fin r)).filter fun i => featureVec i
  by_cases hne : active.Nonempty
  · constructor
    · intro h
      have hmin : active.min' hne = j := by
        simpa [firstActiveFeature?, active, hne] using h
      have hjmem : j ∈ active := by
        simpa [hmin] using Finset.min'_mem active hne
      have hjtrue : featureVec j = true := by
        simpa [active, Finset.mem_filter] using hjmem
      refine ⟨hjtrue, ?_⟩
      intro i hij
      by_contra htrue
      have hiTrue : featureVec i = true := by
        cases hfi : featureVec i <;> simp [hfi] at htrue ⊢
      have himem : i ∈ active := by
        simp [active, Finset.mem_filter, hiTrue]
      have hle : active.min' hne ≤ i := Finset.min'_le active i himem
      rw [hmin] at hle
      exact (not_le_of_gt hij) hle
    · rintro ⟨hjtrue, hbefore⟩
      have hjmem : j ∈ active := by
        simp [active, Finset.mem_filter, hjtrue]
      have hle : active.min' hne ≤ j := Finset.min'_le active j hjmem
      have hge : j ≤ active.min' hne := by
        by_contra hjlt
        have hminmem : active.min' hne ∈ active := Finset.min'_mem active hne
        have hmintrue : featureVec (active.min' hne) = true := by
          simpa [active, Finset.mem_filter] using hminmem
        have hminfalse : featureVec (active.min' hne) = false := hbefore _ (lt_of_not_ge hjlt)
        simp [hmintrue] at hminfalse
      have hmin : active.min' hne = j := le_antisymm hle hge
      simp [firstActiveFeature?, active, hne, hmin]
  · constructor
    · intro h
      simp [firstActiveFeature?, active, hne] at h
    · rintro ⟨hjtrue, _⟩
      exfalso
      exact hne ⟨j, by simp [active, Finset.mem_filter, hjtrue]⟩

theorem firstActiveFeature?_eq_none_iff
    {r : Nat} (featureVec : BitVec r) :
    firstActiveFeature? featureVec = none ↔ ∀ j, featureVec j = false := by
  classical
  let active : Finset (Fin r) := (Finset.univ : Finset (Fin r)).filter fun i => featureVec i
  by_cases hne : active.Nonempty
  · constructor
    · simp [firstActiveFeature?, active, hne]
    · intro hall
      exfalso
      rcases hne with ⟨j, hj⟩
      have hjtrue : featureVec j = true := by
        simpa [active, Finset.mem_filter] using hj
      simp [hall j] at hjtrue
  · constructor
    · intro h j
      by_contra hj
      apply hne
      exact ⟨j, by simp [active, Finset.mem_filter, hj]⟩
    · simp [firstActiveFeature?, active, hne]

theorem firstActiveFeature?_zeroVec
    {r : Nat} :
    firstActiveFeature? (zeroVec : BitVec r) = none := by
  refine (firstActiveFeature?_eq_none_iff (featureVec := (zeroVec : BitVec r))).2 ?_
  intro j
  simp [zeroVec]

theorem exists_firstActiveFeature?_eq_some_of_ne_zero
    {r : Nat} {featureVec : BitVec r}
    (hvec : featureVec ≠ zeroVec) :
    ∃ j, firstActiveFeature? featureVec = some j := by
  by_cases hnone : firstActiveFeature? featureVec = none
  · exfalso
    apply hvec
    funext j
    exact (firstActiveFeature?_eq_none_iff (featureVec := featureVec)).1 hnone j
  · exact Option.ne_none_iff_exists'.1 hnone

theorem firstActiveFeature?_append_left
    {m n : Nat} {x : BitVec m} {y : BitVec n} {j : Fin m}
    (hx : firstActiveFeature? x = some j) :
    firstActiveFeature? (Fin.append x y) = some (Fin.castAdd n j) := by
  apply (firstActiveFeature?_eq_some_iff (featureVec := Fin.append x y) (j := Fin.castAdd n j)).2
  have hxspec := (firstActiveFeature?_eq_some_iff (featureVec := x) (j := j)).1 hx
  refine ⟨?_, ?_⟩
  · simpa using (show Fin.append x y (Fin.castAdd n j) = true by
      simpa using hxspec.1)
  · intro i hi
    cases i using Fin.addCases with
    | left i =>
        have hi' : i < j := by
          change i.1 < j.1
          change (Fin.castAdd n i).1 < (Fin.castAdd n j).1 at hi
          simpa using hi
        simpa using hxspec.2 i hi'
    | right i =>
        have hge : (Fin.castAdd n j : Fin (m + n)) ≤ Fin.natAdd m i := by
          refine Fin.le_iff_val_le_val.mpr ?_
          exact Nat.le_trans (Nat.le_of_lt (Fin.castAdd_lt n j)) (Fin.le_coe_natAdd m i)
        exact (not_lt_of_ge hge hi).elim

theorem firstActiveFeature?_append_right
    {m n : Nat} {x : BitVec m} {y : BitVec n} {j : Fin n}
    (hx : firstActiveFeature? x = none)
    (hy : firstActiveFeature? y = some j) :
    firstActiveFeature? (Fin.append x y) = some (Fin.natAdd m j) := by
  apply (firstActiveFeature?_eq_some_iff (featureVec := Fin.append x y) (j := Fin.natAdd m j)).2
  have hxspec := (firstActiveFeature?_eq_none_iff (featureVec := x)).1 hx
  have hyspec := (firstActiveFeature?_eq_some_iff (featureVec := y) (j := j)).1 hy
  refine ⟨?_, ?_⟩
  · simpa using (show Fin.append x y (Fin.natAdd m j) = true by
      simpa using hyspec.1)
  · intro i hi
    cases i using Fin.addCases with
    | left i =>
        simpa using hxspec i
    | right i =>
        have hi' : i < j := by
          simpa using hi
        simpa using hyspec.2 i hi'

end FirstActive

end Mettapedia.Computability.PNP
