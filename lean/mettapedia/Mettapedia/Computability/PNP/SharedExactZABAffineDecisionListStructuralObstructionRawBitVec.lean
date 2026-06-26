import Mettapedia.Computability.PNP.AffineFeatureFamily
import Mettapedia.Computability.PNP.FirstActiveFeature
import Mathlib.Tactic.NormNum

/-!
# P vs NP crux: raw BitVec first-active affine signatures are noninjective

This module contains the raw `BitVec` obstruction used by the shared exact ZAB
affine decision-list route.  The exact-ZAB transport layer lives in
`SharedExactZABAffineDecisionListStructuralObstructionExactZAB`.
-/

namespace Mettapedia.Computability.PNP

section RawBitVec

open Fin

theorem columnParity_toggleBit_of_coeff_false
    {d : ℕ} (coeff x : BitVec d) (i : Fin d)
    (hcoeff : coeff i = false) :
    columnParity coeff (toggleBit x i) = columnParity coeff x := by
  rw [columnParity]
  congr
  ext j
  by_cases hji : j = i
  · subst hji
    simp [toggleBit, hcoeff]
  · simp [toggleBit, hji]

theorem affineColumnPredict_toggleBit_of_coeff_false
    {d : ℕ} (coeff : BitVec d) (bias : Bool) (x : BitVec d) (i : Fin d)
    (hcoeff : coeff i = false) :
    affineColumnPredict coeff bias (toggleBit x i) =
      affineColumnPredict coeff bias x := by
  simp [affineColumnPredict, columnParity_toggleBit_of_coeff_false, hcoeff]

theorem singleton_support_of_all_true
    {d : ℕ} {coeff : BitVec d}
    (hall : ∀ t, coeff t = true) (i : Fin d) :
    ((Finset.univ : Finset (Fin d)).filter fun t => coeff t && singletonVec i t) = {i} := by
  ext t
  by_cases hti : t = i
  · subst hti
    simp [hall, singletonVec]
  · simp [hall, singletonVec, hti]

theorem pair_support_of_all_true
    {d : ℕ} {coeff : BitVec d}
    (hall : ∀ t, coeff t = true) {i j : Fin d} (hij : i ≠ j) :
    ((Finset.univ : Finset (Fin d)).filter fun t => coeff t && pairVec i j t) = {i, j} := by
  ext t
  by_cases hti : t = i
  · subst hti
    simp [hall, pairVec, hij]
  · by_cases htj : t = j
    · subst htj
      simp [hall, pairVec, hti]
    · simp [hall, pairVec, hti, htj]

theorem columnParity_all_true_singletonVec
    {d : ℕ} {coeff : BitVec d}
    (hall : ∀ t, coeff t = true) (i : Fin d) :
    columnParity coeff (singletonVec i) = true := by
  rw [columnParity, singleton_support_of_all_true hall i]
  simp

theorem columnParity_all_true_pairVec
    {d : ℕ} {coeff : BitVec d}
    (hall : ∀ t, coeff t = true) {i j : Fin d} (hij : i ≠ j) :
    columnParity coeff (pairVec i j) = false := by
  rw [columnParity, pair_support_of_all_true hall hij]
  simp [hij]

theorem columnParity_zeroVec
    {d : ℕ} (coeff : BitVec d) :
    columnParity coeff (zeroVec : BitVec d) = false := by
  simp [columnParity, zeroVec]

theorem affineColumnPredict_eq_false_of_not_exists_true
    {d : ℕ} {coeff : BitVec d} {bias : Bool}
    (hno : ¬ ∃ x, affineColumnPredict coeff bias x = true)
    (x : BitVec d) :
    affineColumnPredict coeff bias x = false := by
  cases hx : affineColumnPredict coeff bias x with
  | false =>
      rfl
  | true =>
      exact False.elim <| hno ⟨x, hx⟩

theorem exists_two_distinct_affineColumnPredict_true_of_one_lt
    {d : ℕ} {coeff : BitVec d} {bias : Bool}
    (hd : 1 < d)
    (hw : ∃ x, affineColumnPredict coeff bias x = true) :
    ∃ x y : BitVec d,
      x ≠ y ∧
      affineColumnPredict coeff bias x = true ∧
      affineColumnPredict coeff bias y = true := by
  classical
  by_cases hall : ∀ t, coeff t = true
  · let i0 : Fin d := ⟨0, Nat.lt_trans Nat.zero_lt_one hd⟩
    let i1 : Fin d := ⟨1, hd⟩
    have hi01 : i0 ≠ i1 := by
      simp [i0, i1]
    cases bias with
    | false =>
        refine ⟨singletonVec i0, singletonVec i1, ?_, ?_, ?_⟩
        · exact singletonVec_ne_singletonVec hi01
        · simp [affineColumnPredict, columnParity_all_true_singletonVec, hall]
        · simp [affineColumnPredict, columnParity_all_true_singletonVec, hall]
    | true =>
        refine ⟨(zeroVec : BitVec d), pairVec i0 i1, ?_, ?_, ?_⟩
        · exact fun h => pairVec_ne_zeroVec hi01 h.symm
        · simp [affineColumnPredict, columnParity_zeroVec]
        · simp [affineColumnPredict, columnParity_all_true_pairVec, hall, hi01]
  · push Not at hall
    rcases hall with ⟨i, hi⟩
    cases hcoeff : coeff i with
    | false =>
        rcases hw with ⟨x, hx⟩
        refine ⟨x, toggleBit x i, ?_, hx, ?_⟩
        · exact (toggleBit_ne_self x i).symm
        · calc
            affineColumnPredict coeff bias (toggleBit x i)
              = affineColumnPredict coeff bias x := by
                  simpa [hcoeff] using
                    affineColumnPredict_toggleBit_of_coeff_false coeff bias x i hcoeff
            _ = true := hx
    | true =>
        exact False.elim (hi hcoeff)

theorem not_injective_firstActiveFeature_affineFeatureVector_of_one_lt
    {p d : ℕ}
    (features : Fin p → AffineColumnCode d)
    (hd : 1 < d) :
    ¬ Function.Injective
      (fun x : BitVec d => firstActiveFeature? (affineFeatureVector features x)) := by
  classical
  let active : Finset (Fin p) :=
    (Finset.univ : Finset (Fin p)).filter fun j =>
      ∃ x, affineColumnPredict (features j).1 (features j).2 x = true
  by_cases hne : active.Nonempty
  · let j : Fin p := active.min' hne
    have hjmem : j ∈ active := Finset.min'_mem active hne
    have hjtrue : ∃ x, affineColumnPredict (features j).1 (features j).2 x = true := by
      simpa [active] using hjmem
    rcases exists_two_distinct_affineColumnPredict_true_of_one_lt
        (coeff := (features j).1) (bias := (features j).2) hd hjtrue with
      ⟨x, y, hxy, hx, hy⟩
    have hxsig :
        firstActiveFeature? (affineFeatureVector features x) = some j := by
      apply (firstActiveFeature?_eq_some_iff (featureVec := affineFeatureVector features x) (j := j)).2
      refine ⟨?_, ?_⟩
      · simpa [affineFeatureVector] using hx
      · intro i hij
        have himem : i ∉ active := by
          intro hi
          exact (not_le_of_gt hij) (Finset.min'_le active i hi)
        have hiempty : ¬ ∃ z, affineColumnPredict (features i).1 (features i).2 z = true := by
          simpa [active] using himem
        simpa [affineFeatureVector] using
          affineColumnPredict_eq_false_of_not_exists_true hiempty x
    have hysig :
        firstActiveFeature? (affineFeatureVector features y) = some j := by
      apply (firstActiveFeature?_eq_some_iff (featureVec := affineFeatureVector features y) (j := j)).2
      refine ⟨?_, ?_⟩
      · simpa [affineFeatureVector] using hy
      · intro i hij
        have himem : i ∉ active := by
          intro hi
          exact (not_le_of_gt hij) (Finset.min'_le active i hi)
        have hiempty : ¬ ∃ z, affineColumnPredict (features i).1 (features i).2 z = true := by
          simpa [active] using himem
        simpa [affineFeatureVector] using
          affineColumnPredict_eq_false_of_not_exists_true hiempty y
    intro hinj
    exact hxy (hinj (hxsig.trans hysig.symm))
  · let i0 : Fin d := ⟨0, Nat.lt_trans Nat.zero_lt_one hd⟩
    have hallfalse :
        ∀ j x, affineColumnPredict (features j).1 (features j).2 x = false := by
      intro j x
      have hjmem : j ∉ active := by
        intro hj
        exact hne ⟨j, hj⟩
      have hjempty : ¬ ∃ z, affineColumnPredict (features j).1 (features j).2 z = true := by
        simpa [active] using hjmem
      exact affineColumnPredict_eq_false_of_not_exists_true hjempty x
    have hnone0 :
        firstActiveFeature? (affineFeatureVector features (zeroVec : BitVec d)) = none := by
      refine (firstActiveFeature?_eq_none_iff
        (featureVec := affineFeatureVector features (zeroVec : BitVec d))).2 ?_
      intro j
      simpa [affineFeatureVector] using hallfalse j (zeroVec : BitVec d)
    have hnone1 :
        firstActiveFeature? (affineFeatureVector features (singletonVec i0)) = none := by
      refine (firstActiveFeature?_eq_none_iff
        (featureVec := affineFeatureVector features (singletonVec i0))).2 ?_
      intro j
      simpa [affineFeatureVector] using hallfalse j (singletonVec i0)
    intro hinj
    exact singletonVec_ne_zeroVec i0 <| hinj (hnone1.trans hnone0.symm)

end RawBitVec

end Mettapedia.Computability.PNP
