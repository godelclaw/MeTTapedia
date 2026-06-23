import Mettapedia.Computability.PNP.SharedExactZABSparseThresholdSharpnessRawBitVec

/-!
# P vs NP route sharpness: raw sparse-threshold realization

Threshold code construction and raw sparse-threshold realization on the explicit point-block basis.
-/

namespace Mettapedia.Computability.PNP
section RawRealization

variable {d : ℕ}

/-- The threshold used by the point-block sparse-threshold witness. -/
noncomputable abbrev pointBlockThresholdNat (rule : BitVec d → Bool) : ℕ :=
  rawPositivePointCount rule * pointBlockHalfCount d + 1

theorem pointBlockHalfCount_pos (hd : 0 < d) :
    0 < pointBlockHalfCount d := by
  cases d with
  | zero =>
      cases Nat.lt_irrefl 0 hd
  | succ d =>
      simp [pointBlockHalfCount, Nat.pow_pos Nat.two_pos]

theorem pointBlockThresholdNat_lt_featureCount
    (hd : 0 < d) (rule : BitVec d → Bool) :
    pointBlockThresholdNat rule < allAffinePointBlockFeatureCount d := by
  have hcount :
      rawPositivePointCount rule ≤ 2 ^ d := by
    unfold rawPositivePointCount
    simpa [BitVec] using Fintype.card_subtype_le (fun x : BitVec d => rule x)
  have hhalfpos : 0 < pointBlockHalfCount d :=
    pointBlockHalfCount_pos hd
  have hpow : 2 ^ d = pointBlockHalfCount d + pointBlockHalfCount d := by
    have hd' : d = (d - 1) + 1 := by omega
    rw [hd', pointBlockHalfCount, Nat.pow_add]
    simp [two_mul, Nat.mul_comm]
  have hpowd2 : 2 ≤ 2 ^ d := by
    have hd1 : 1 ≤ d := Nat.succ_le_of_lt hd
    simpa using (Nat.pow_le_pow_right (show 1 ≤ 2 by decide) hd1)
  have htwo : 2 ≤ 2 ^ d * pointBlockHalfCount d := by
    have hhalf1 : 1 ≤ pointBlockHalfCount d := Nat.succ_le_of_lt hhalfpos
    simpa using Nat.mul_le_mul hpowd2 hhalf1
  have hgtone : 1 < 2 ^ d * pointBlockHalfCount d := by
    exact lt_of_lt_of_le (by decide : 1 < 2) htwo
  have hlt :
      rawPositivePointCount rule * pointBlockHalfCount d + 1 <
        rawPositivePointCount rule * pointBlockHalfCount d +
          2 ^ d * pointBlockHalfCount d := by
    exact Nat.add_lt_add_left hgtone (rawPositivePointCount rule * pointBlockHalfCount d)
  have hle :
      rawPositivePointCount rule * pointBlockHalfCount d +
          2 ^ d * pointBlockHalfCount d ≤
        2 ^ d * pointBlockHalfCount d + 2 ^ d * pointBlockHalfCount d := by
    exact Nat.add_le_add_right
      (Nat.mul_le_mul_right (pointBlockHalfCount d) hcount)
      (2 ^ d * pointBlockHalfCount d)
  have hfinal :
      rawPositivePointCount rule * pointBlockHalfCount d +
          2 ^ d * pointBlockHalfCount d ≤
        2 ^ d * 2 ^ d := by
    have hsum :
        2 ^ d * pointBlockHalfCount d + 2 ^ d * pointBlockHalfCount d =
          2 ^ d * 2 ^ d := by
      rw [← Nat.mul_add, ← hpow]
    exact hle.trans_eq hsum
  rw [allAffinePointBlockFeatureCount_eq]
  unfold pointBlockThresholdNat
  exact lt_of_lt_of_le hlt hfinal

theorem pointBlockThresholdNat_lt_thresholdBudget
    (hd : 0 < d) (rule : BitVec d → Bool) :
    pointBlockThresholdNat rule < 2 ^ allAffinePointBlockFeatureCount d := by
  exact
    (pointBlockThresholdNat_lt_featureCount (d := d) hd rule).trans_le
      (Nat.le_of_lt (allAffinePointBlockFeatureCount d).lt_two_pow_self)

/-- The explicit sparse-threshold witness code for the point-block
construction. -/
noncomputable def pointBlockSparseThresholdCode
    (hd : 0 < d) (rule : BitVec d → Bool) :
    SharedSparseThresholdCode (allAffinePointBlockFeatureCount d) :=
  (pointBlockMask (d := d) rule,
    thresholdCodeOfNat
      (p := allAffinePointBlockFeatureCount d)
      (t := pointBlockThresholdNat rule)
      (pointBlockThresholdNat_lt_thresholdBudget (d := d) hd rule))

@[simp] theorem thresholdCodeValue_pointBlockSparseThresholdCode
    (hd : 0 < d) (rule : BitVec d → Bool) :
    thresholdCodeValue (r := allAffinePointBlockFeatureCount d)
        (pointBlockSparseThresholdCode (d := d) hd rule).2 =
      pointBlockThresholdNat rule := by
  simp [pointBlockSparseThresholdCode]

theorem rawSharedSparseThresholdPredict_allAffinePointBlockFeatures_eq
    (hd : 0 < d) (rule : BitVec d → Bool) :
    rawSharedSparseThresholdPredict
        (allAffinePointBlockFeatures d)
        (pointBlockSparseThresholdCode (d := d) hd rule) =
      rule := by
  funext y
  cases hy : rule y with
  | false =>
      have hcount :=
        maskedAffineFeatureCount_allAffinePointBlockFeatures_of_false
          (d := d) hd rule y hy
      have hnot :
          ¬ pointBlockThresholdNat rule ≤
              rawPositivePointCount rule * pointBlockHalfCount d := by
        simp [pointBlockThresholdNat]
      simp [rawSharedSparseThresholdPredict, pointBlockSparseThresholdCode,
        pointBlockThresholdNat, hcount, hnot]
  | true =>
      have hcount :=
        maskedAffineFeatureCount_allAffinePointBlockFeatures_of_true
          (d := d) hd rule y hy
      have hhalfpos : 0 < pointBlockHalfCount d :=
        pointBlockHalfCount_pos (d := d) hd
      have hle :
          pointBlockThresholdNat rule ≤
            rawPositivePointCount rule * pointBlockHalfCount d +
              pointBlockHalfCount d := by
        simp [pointBlockThresholdNat]
        omega
      simp [rawSharedSparseThresholdPredict, pointBlockSparseThresholdCode,
        pointBlockThresholdNat, hcount, hle]

end RawRealization

end Mettapedia.Computability.PNP
