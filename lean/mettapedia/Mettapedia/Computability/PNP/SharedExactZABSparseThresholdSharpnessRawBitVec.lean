import Mettapedia.Computability.PNP.SharedExactZABAffineDecisionListStructuralObstructionRawBitVec
import Mettapedia.Computability.PNP.SharedAffineFeatureFamilies
import Mathlib.Tactic.NormNum

/-!
# P vs NP route sharpness: raw BitVec point-block counting

Raw BitVec affine point-block features, parity toggles, and exact block-count identities.
-/

namespace Mettapedia.Computability.PNP
section RawBitVec

variable {d : ℕ}

/-- The explicit shared feature count used by the point-block sparse-threshold
construction: one full affine block for every visible point. -/
abbrev allAffinePointBlockFeatureCount (d : ℕ) : ℕ :=
  Fintype.card (BitVec d × BitVec d)

@[simp] theorem allAffinePointBlockFeatureCount_eq (d : ℕ) :
    allAffinePointBlockFeatureCount d = 2 ^ d * 2 ^ d := by
  simp [allAffinePointBlockFeatureCount, BitVec]

/-- Decode a raw feature index as its center point and coefficient vector. -/
noncomputable def allAffinePointBlockFeatureIndexEquiv (d : ℕ) :
    BitVec d × BitVec d ≃ Fin (allAffinePointBlockFeatureCount d) :=
  Fintype.equivFin (BitVec d × BitVec d)

/-- One block feature: it fires exactly when the affine parity of the query
matches the affine parity of the chosen center point. -/
def allAffinePointBlockFeature (x coeff : BitVec d) : AffineColumnCode d :=
  (coeff, !(columnParity coeff x))

/-- The shared affine basis consisting of all point-centered affine blocks. -/
noncomputable def allAffinePointBlockFeatures (d : ℕ) :
    Fin (allAffinePointBlockFeatureCount d) → AffineColumnCode d :=
  fun j =>
    let xc := (allAffinePointBlockFeatureIndexEquiv d).symm j
    allAffinePointBlockFeature xc.1 xc.2

/-- The raw sparse-threshold predictor on one fixed shared basis over
`BitVec d`. -/
noncomputable def rawSharedSparseThresholdPredict
    {p : ℕ}
    (features : Fin p → AffineColumnCode d)
    (code : SharedSparseThresholdCode p)
    (x : BitVec d) : Bool :=
  decide (thresholdCodeValue (r := p) code.2 ≤
    maskedAffineFeatureCount (k := d) features code.1 x)

/-- Positive-point count of one raw Boolean rule on `BitVec d`. -/
noncomputable def rawPositivePointCount (rule : BitVec d → Bool) : ℕ :=
  Fintype.card {x : BitVec d // rule x}

/-- The point-block activity mask turns on exactly the blocks centered at
positive points of the target rule. -/
noncomputable def pointBlockMask (rule : BitVec d → Bool) :
    BitCode (allAffinePointBlockFeatureCount d) :=
  fun j =>
    rule ((allAffinePointBlockFeatureIndexEquiv d).symm j).1

/-- Half of one full affine block.  This is the exact off-diagonal block score
in the point-block construction. -/
abbrev pointBlockHalfCount (d : ℕ) : ℕ :=
  2 ^ (d - 1)

/-- Threshold code for one natural number below the available sparse-threshold
budget. -/
noncomputable def thresholdCodeOfNat
    {p t : ℕ} (ht : t < 2 ^ p) : BitCode p :=
  (Fintype.equivFinOfCardEq
    (by simp [BitCode] : Fintype.card (BitCode p) = 2 ^ p)).symm ⟨t, ht⟩

@[simp] theorem thresholdCodeValue_thresholdCodeOfNat
    {p t : ℕ} (ht : t < 2 ^ p) :
    thresholdCodeValue (r := p) (thresholdCodeOfNat (p := p) (t := t) ht) = t := by
  simp [thresholdCodeOfNat, thresholdCodeValue]

theorem toggleBit_toggleBit {d : ℕ} (x : BitVec d) (i : Fin d) :
    toggleBit (toggleBit x i) i = x := by
  funext j
  by_cases hji : j = i
  · subst hji
    simp [toggleBit]
  · simp [toggleBit, hji]

theorem columnParity_comm {d : ℕ} (x y : BitVec d) :
    columnParity x y = columnParity y x := by
  unfold columnParity
  congr
  ext i
  simp [Bool.and_comm]

theorem columnParity_toggleBit_of_coeff_true_of_input_false
    {d : ℕ} (coeff x : BitVec d) (i : Fin d)
    (hcoeff : coeff i = true) (hx : x i = false) :
    columnParity coeff (toggleBit x i) = !(columnParity coeff x) := by
  let s : Finset (Fin d) :=
    (Finset.univ : Finset (Fin d)).filter fun t => coeff t && x t
  have hi_not_mem : i ∉ s := by
    simp [s, hcoeff, hx]
  have hfilter :
      ((Finset.univ : Finset (Fin d)).filter fun t => coeff t && toggleBit x i t) =
        insert i s := by
    ext t
    by_cases hti : t = i
    · subst hti
      simp [s, toggleBit, hcoeff, hx]
    · simp [s, toggleBit, hti]
  rw [columnParity, hfilter, Finset.card_insert_of_notMem hi_not_mem, columnParity]
  change decide (Odd (s.card + 1)) = !decide (Odd s.card)
  by_cases hs : Odd s.card
  · have hs' : ¬ Odd (s.card + 1) := by
      simpa [Nat.odd_add_one] using hs
    simp [hs, hs']
  · have hs' : Odd (s.card + 1) := by
      simpa [Nat.odd_add_one] using hs
    simp [hs, hs']

theorem columnParity_toggleBit_of_coeff_true
    {d : ℕ} (coeff x : BitVec d) (i : Fin d)
    (hcoeff : coeff i = true) :
    columnParity coeff (toggleBit x i) = !(columnParity coeff x) := by
  cases hx : x i with
  | false =>
      exact columnParity_toggleBit_of_coeff_true_of_input_false coeff x i hcoeff hx
  | true =>
      have hstep :
          columnParity coeff x = !(columnParity coeff (toggleBit x i)) := by
        simpa [toggleBit_toggleBit] using
          (columnParity_toggleBit_of_coeff_true_of_input_false
            coeff (toggleBit x i) i hcoeff (by simp [toggleBit, hx]))
      simpa using (congrArg (!·) hstep).symm

theorem columnParity_toggleBit_left_of_input_false
    {d : ℕ} (coeff x : BitVec d) (i : Fin d)
    (hx : x i = false) :
    columnParity (toggleBit coeff i) x = columnParity coeff x := by
  simpa [columnParity_comm] using
    (columnParity_toggleBit_of_coeff_false x coeff i hx)

theorem columnParity_toggleBit_left_of_input_true
    {d : ℕ} (coeff x : BitVec d) (i : Fin d)
    (hx : x i = true) :
    columnParity (toggleBit coeff i) x = !(columnParity coeff x) := by
  simpa [columnParity_comm] using
    (columnParity_toggleBit_of_coeff_true x coeff i hx)

theorem exists_diff_coordinate_of_ne {d : ℕ} {x y : BitVec d} (hxy : x ≠ y) :
    ∃ i : Fin d, x i ≠ y i := by
  classical
  by_contra h
  apply hxy
  funext i
  by_contra hne
  exact h ⟨i, hne⟩

theorem pointBlockMatch_toggleBit_iff_not
    {d : ℕ} {x y coeff : BitVec d} {i : Fin d}
    (hxyi : x i ≠ y i) :
    (columnParity (toggleBit coeff i) x = columnParity (toggleBit coeff i) y) ↔
      ¬ (columnParity coeff x = columnParity coeff y) := by
  cases hx : x i <;> cases hy : y i
  · exfalso
    exact hxyi (by simp [hx, hy])
  ·
    rw [columnParity_toggleBit_left_of_input_false coeff x i hx,
      columnParity_toggleBit_left_of_input_true coeff y i hy]
    cases hpx : columnParity coeff x <;> cases hpy : columnParity coeff y <;>
      simp
  ·
    rw [columnParity_toggleBit_left_of_input_true coeff x i hx,
      columnParity_toggleBit_left_of_input_false coeff y i hy]
    cases hpx : columnParity coeff x <;> cases hpy : columnParity coeff y <;>
      simp
  · exfalso
    exact hxyi (by simp [hx, hy])

theorem pointBlockMatchCard_self (x : BitVec d) :
    Fintype.card {coeff : BitVec d // columnParity coeff x = columnParity coeff x} = 2 ^ d := by
  classical
  let e :
      {coeff : BitVec d // columnParity coeff x = columnParity coeff x} ≃ BitVec d :=
    Equiv.subtypeUnivEquiv fun _ => by rfl
  rw [Fintype.card_congr e]
  simp [BitVec]

theorem pointBlockMatchCard_eq_half_of_ne
    (hd : 0 < d) {x y : BitVec d} (hxy : x ≠ y) :
    Fintype.card {coeff : BitVec d // columnParity coeff x = columnParity coeff y} =
      pointBlockHalfCount d := by
  classical
  obtain ⟨i, hxyi⟩ := exists_diff_coordinate_of_ne hxy
  let P : BitVec d → Prop := fun coeff => columnParity coeff x = columnParity coeff y
  let e : {coeff : BitVec d // P coeff} ≃ {coeff : BitVec d // ¬ P coeff} := {
    toFun := fun z =>
      ⟨toggleBit z.1 i, by
        intro htoggle
        exact ((pointBlockMatch_toggleBit_iff_not (hxyi := hxyi)).1 htoggle) z.2⟩
    invFun := fun z =>
      ⟨toggleBit z.1 i, (pointBlockMatch_toggleBit_iff_not (hxyi := hxyi)).2 z.2⟩
    left_inv := by
      intro z
      apply Subtype.ext
      exact toggleBit_toggleBit z.1 i
    right_inv := by
      intro z
      apply Subtype.ext
      exact toggleBit_toggleBit z.1 i }
  have hsplit :
      Fintype.card {coeff : BitVec d // P coeff} =
        Fintype.card (BitVec d) - Fintype.card {coeff : BitVec d // P coeff} := by
    calc
      Fintype.card {coeff : BitVec d // P coeff}
          = Fintype.card {coeff : BitVec d // ¬ P coeff} := Fintype.card_congr e
      _ = Fintype.card (BitVec d) - Fintype.card {coeff : BitVec d // P coeff} := by
            exact Fintype.card_subtype_compl P
  have hpow : 2 ^ d = 2 * pointBlockHalfCount d := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', pointBlockHalfCount, Nat.pow_add]
    simp [Nat.mul_comm]
  have hcard : Fintype.card {coeff : BitVec d // P coeff} = pointBlockHalfCount d := by
    have hbit : Fintype.card (BitVec d) = 2 ^ d := by simp [BitVec]
    omega
  simpa [P] using hcard

theorem allAffinePointBlockFeature_eval
    (x coeff y : BitVec d) :
    affineColumnPredict (allAffinePointBlockFeature x coeff).1
        (allAffinePointBlockFeature x coeff).2 y =
      decide (columnParity coeff x = columnParity coeff y) := by
  simp [allAffinePointBlockFeature, affineColumnPredict]
  cases hx : columnParity coeff x <;> cases hy : columnParity coeff y <;>
    simp

theorem maskedAffineFeatureCount_allAffinePointBlockFeatures_eq_sum
    (rule : BitVec d → Bool) (y : BitVec d) :
    maskedAffineFeatureCount (k := d)
        (allAffinePointBlockFeatures d)
        (pointBlockMask (d := d) rule) y =
      ∑ x : {x : BitVec d // rule x},
          Fintype.card {coeff : BitVec d // columnParity coeff x.1 = columnParity coeff y} := by
  classical
  let P : Fin (allAffinePointBlockFeatureCount d) → Prop := fun j =>
    pointBlockMask (d := d) rule j = true ∧
      affineFeatureVector (allAffinePointBlockFeatures d) y j = true
  have hcard :
      maskedAffineFeatureCount (k := d)
          (allAffinePointBlockFeatures d)
          (pointBlockMask (d := d) rule) y =
        Fintype.card {j : Fin (allAffinePointBlockFeatureCount d) // P j} := by
    simp [maskedAffineFeatureCount, P, Fintype.card_subtype]
  let e₁ :
      {xc : BitVec d × BitVec d //
          rule xc.1 ∧ columnParity xc.2 xc.1 = columnParity xc.2 y} ≃
        {j : Fin (allAffinePointBlockFeatureCount d) // P j} := {
      toFun := fun z =>
        ⟨allAffinePointBlockFeatureIndexEquiv d z.1, by
          rcases z with ⟨⟨x, coeff⟩, hx, hmatch⟩
          simp [P, pointBlockMask, allAffinePointBlockFeatures, affineFeatureVector,
            allAffinePointBlockFeature_eval, hx, hmatch]⟩
      invFun := fun z =>
        ⟨(allAffinePointBlockFeatureIndexEquiv d).symm z.1, by
          simpa [P, pointBlockMask, allAffinePointBlockFeatures, affineFeatureVector,
            allAffinePointBlockFeature_eval] using z.2⟩
      left_inv := by
        intro z
        apply Subtype.ext
        simp [allAffinePointBlockFeatureIndexEquiv]
      right_inv := by
        intro z
        apply Subtype.ext
        simp [allAffinePointBlockFeatureIndexEquiv] }
  let e₂ :
      {xc : BitVec d × BitVec d //
          rule xc.1 ∧ columnParity xc.2 xc.1 = columnParity xc.2 y} ≃
        Σ x : {x : BitVec d // rule x},
          {coeff : BitVec d // columnParity coeff x.1 = columnParity coeff y} := {
      toFun := fun z => ⟨⟨z.1.1, z.2.1⟩, ⟨z.1.2, z.2.2⟩⟩
      invFun := fun z => ⟨(z.1.1, z.2.1), z.1.2, z.2.2⟩
      left_inv := by
        intro z
        rcases z with ⟨⟨x, coeff⟩, hx, hmatch⟩
        rfl
      right_inv := by
        intro z
        rcases z with ⟨⟨x, hx⟩, ⟨coeff, hmatch⟩⟩
        rfl }
  calc
    maskedAffineFeatureCount (k := d)
        (allAffinePointBlockFeatures d)
        (pointBlockMask (d := d) rule) y
      = Fintype.card {j : Fin (allAffinePointBlockFeatureCount d) // P j} := hcard
    _ =
        Fintype.card
          {xc : BitVec d × BitVec d //
            rule xc.1 ∧ columnParity xc.2 xc.1 = columnParity xc.2 y} := by
          rw [Fintype.card_congr e₁]
    _ =
        Fintype.card
          (Σ x : {x : BitVec d // rule x},
            {coeff : BitVec d // columnParity coeff x.1 = columnParity coeff y}) := by
          rw [Fintype.card_congr e₂]
    _ =
        ∑ x : {x : BitVec d // rule x},
          Fintype.card {coeff : BitVec d // columnParity coeff x.1 = columnParity coeff y} := by
          rw [Fintype.card_sigma]

theorem maskedAffineFeatureCount_allAffinePointBlockFeatures_of_false
    (hd : 0 < d) (rule : BitVec d → Bool) (y : BitVec d)
    (hy : rule y = false) :
    maskedAffineFeatureCount (k := d)
        (allAffinePointBlockFeatures d)
        (pointBlockMask (d := d) rule) y =
      rawPositivePointCount rule * pointBlockHalfCount d := by
  classical
  calc
    maskedAffineFeatureCount (k := d)
        (allAffinePointBlockFeatures d)
        (pointBlockMask (d := d) rule) y
      =
        ∑ x : {x : BitVec d // rule x},
          Fintype.card {coeff : BitVec d // columnParity coeff x.1 = columnParity coeff y} := by
            exact maskedAffineFeatureCount_allAffinePointBlockFeatures_eq_sum rule y
    _ = ∑ x : {x : BitVec d // rule x}, pointBlockHalfCount d := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          apply pointBlockMatchCard_eq_half_of_ne hd
          intro hxy
          have : rule y = true := by simpa [hxy] using x.2
          rw [hy] at this
          contradiction
    _ = rawPositivePointCount rule * pointBlockHalfCount d := by
          simp [rawPositivePointCount]

theorem maskedAffineFeatureCount_allAffinePointBlockFeatures_of_true
    (hd : 0 < d) (rule : BitVec d → Bool) (y : BitVec d)
    (hy : rule y = true) :
    maskedAffineFeatureCount (k := d)
        (allAffinePointBlockFeatures d)
        (pointBlockMask (d := d) rule) y =
      rawPositivePointCount rule * pointBlockHalfCount d + pointBlockHalfCount d := by
  classical
  have hpow : 2 ^ d = pointBlockHalfCount d + pointBlockHalfCount d := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', pointBlockHalfCount, Nat.pow_add]
    simp [two_mul, Nat.mul_comm]
  have hsingle :
      (∑ x : {x : BitVec d // rule x},
          if x.1 = y then pointBlockHalfCount d else 0) =
        pointBlockHalfCount d := by
    classical
    rw [Finset.sum_eq_single ⟨y, hy⟩]
    · simp
    · intro x _ hx
      simp [Subtype.ext_iff] at hx
      simp [hx]
    · intro hmem
      exact False.elim (hmem (Finset.mem_univ _))
  calc
    maskedAffineFeatureCount (k := d)
        (allAffinePointBlockFeatures d)
        (pointBlockMask (d := d) rule) y
      =
        ∑ x : {x : BitVec d // rule x},
          Fintype.card {coeff : BitVec d // columnParity coeff x.1 = columnParity coeff y} := by
            exact maskedAffineFeatureCount_allAffinePointBlockFeatures_eq_sum rule y
    _ =
        ∑ x : {x : BitVec d // rule x},
          (pointBlockHalfCount d + if x.1 = y then pointBlockHalfCount d else 0) := by
          refine Finset.sum_congr rfl ?_
          intro x hx
          by_cases hxy : x.1 = y
          · subst hxy
            rw [pointBlockMatchCard_self]
            simp [hpow]
          · rw [pointBlockMatchCard_eq_half_of_ne hd hxy]
            simp [hxy]
    _ =
        (∑ x : {x : BitVec d // rule x}, pointBlockHalfCount d) +
          (∑ x : {x : BitVec d // rule x},
            if x.1 = y then pointBlockHalfCount d else 0) := by
              rw [Finset.sum_add_distrib]
    _ = rawPositivePointCount rule * pointBlockHalfCount d + pointBlockHalfCount d := by
          simp [rawPositivePointCount, hsingle]

end RawBitVec

end Mettapedia.Computability.PNP
