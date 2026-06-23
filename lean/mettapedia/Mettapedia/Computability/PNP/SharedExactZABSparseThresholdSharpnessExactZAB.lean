import Mettapedia.Computability.PNP.SharedExactZABSparseThresholdSharpnessRawRealization
import Mettapedia.Computability.PNP.SharedExactZABAffineDecisionListStructuralObstructionExactZAB

/-!
# P vs NP route sharpness: exact ZAB lifting

Lift the raw BitVec point-block sparse-threshold realization to the exact ZAB visible surface.
-/

namespace Mettapedia.Computability.PNP
section ExactZAB

variable {n k : ℕ}

@[simp] theorem sharedExactZABSparseThresholdAffinePredict_id_allAffinePointBlockFeatures_eq_raw
    (code : SharedSparseThresholdCode
      (allAffinePointBlockFeatureCount (n + (k + k))))
    (u : ExactVisiblePostSwitchSurface (BitVec n) k) :
    sharedExactZABSparseThresholdAffinePredict
        (Z := BitVec n)
        (p := allAffinePointBlockFeatureCount (n + (k + k)))
        (r := n) (k := k)
        (fun z => z)
        (allAffinePointBlockFeatures (n + (k + k))) code u =
      rawSharedSparseThresholdPredict
        (allAffinePointBlockFeatures (n + (k + k))) code
        (bitVecZABVisibleData (r := n) (k := k) u) := by
  simp [sharedExactZABSparseThresholdAffinePredict, rawSharedSparseThresholdPredict,
    bitVecZABVisibleData]

theorem fullExactVisibleRuleFamily_realizedBySharedExactZABSparseThresholdAffineFamily_id_allAffinePointBlockFeatures
    (hwidth : 0 < n + (k + k)) :
    RealizedBySharedExactZABSparseThresholdAffineFamily
      (Z := BitVec n)
      (p := allAffinePointBlockFeatureCount (n + (k + k)))
      (r := n) (k := k)
      (fun z => z)
      (allAffinePointBlockFeatures (n + (k + k)))
      (fullExactVisibleRuleFamily (BitVec n) k) := by
  let e : ExactVisiblePostSwitchSurface (BitVec n) k ≃ BitVec (n + (k + k)) :=
    Equiv.ofBijective
      (bitVecZABVisibleData (r := n) (k := k))
      (bitVecZABVisibleData_bijective (n := n) (k := k))
  intro i
  let rawRule : BitVec (n + (k + k)) → Bool := fun x => i (e.symm x)
  refine ⟨pointBlockSparseThresholdCode (d := n + (k + k)) hwidth rawRule, ?_⟩
  funext u
  have hraw :
      rawSharedSparseThresholdPredict
          (allAffinePointBlockFeatures (n + (k + k)))
          (pointBlockSparseThresholdCode (d := n + (k + k)) hwidth rawRule)
          (bitVecZABVisibleData (r := n) (k := k) u) =
        rawRule (bitVecZABVisibleData (r := n) (k := k) u) := by
    simpa [rawRule] using
      congrFun
        (rawSharedSparseThresholdPredict_allAffinePointBlockFeatures_eq
          (d := n + (k + k)) hwidth rawRule)
        (bitVecZABVisibleData (r := n) (k := k) u)
  have he :
      e.symm (bitVecZABVisibleData (r := n) (k := k) u) = u := by
    simpa [e] using e.left_inv u
  calc
    (fullExactVisibleRuleFamily (BitVec n) k).predict i u
      =
        i u := by
          rfl
    _ =
        rawRule (bitVecZABVisibleData (r := n) (k := k) u) := by
          symm
          simpa [rawRule] using congrArg i he
    _ =
        rawSharedSparseThresholdPredict
          (allAffinePointBlockFeatures (n + (k + k)))
          (pointBlockSparseThresholdCode (d := n + (k + k)) hwidth rawRule)
          (bitVecZABVisibleData (r := n) (k := k) u) := by
            symm
            exact hraw
    _ =
        sharedExactZABSparseThresholdAffinePredict
          (Z := BitVec n)
          (p := allAffinePointBlockFeatureCount (n + (k + k)))
          (r := n) (k := k)
          (fun z => z)
          (allAffinePointBlockFeatures (n + (k + k)))
          (pointBlockSparseThresholdCode (d := n + (k + k)) hwidth rawRule) u := by
            symm
            exact
              sharedExactZABSparseThresholdAffinePredict_id_allAffinePointBlockFeatures_eq_raw
                (n := n) (k := k)
                (pointBlockSparseThresholdCode (d := n + (k + k)) hwidth rawRule) u

end ExactZAB

end Mettapedia.Computability.PNP
