import KrennComponent46Normalization
import KrennFrozenCase0CollapseLayer
import KrennFrozenCase0System
import KrennComponent46Tree

/-!
The semantic seam from a full frozen case-0 valuation through the
external component-46 linear elimination.  The generated finite data
are rechecked by Lean; source hashes below are provenance only.
-/

namespace Krenn.Component46RootBridge

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.FrozenCase0CollapseLayer
open Krenn.Component46Normalization

def reducedRootSystemSHA256 : String := "9f48fab2ef23333ecedd3b3e60c5961aede43407ad654f4a113d8085dff2e53b"
def reducedRootFileSHA256 : String := "957b3e719ac5d28c5aed70dcb8496e77643597e5a071b172f230c19e1d051584"

def rootCoordinate : Fin 61 → Fin 75 := ![
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 13, 14, 16, 17, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 32, 33, 35, 36, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 55, 56, 57, 59, 60, 61, 63, 64, 65, 68, 69, 70, 71, 72, 73, 74
]

noncomputable def rootValues {R : Type*} (full : Fin 75 → R) : Fin 61 → R :=
  fun coordinate => full (rootCoordinate coordinate)

noncomputable def reconstructFull {R : Type*} [CommRing R]
    (values : Fin 61 → R) : Fin 75 → R := ![
  values 0,
  values 1,
  values 2,
  values 3,
  values 4,
  values 5,
  values 6,
  values 7,
  values 8,
  values 9,
  0,
  values 10,
  values 11,
  values 12,
  values 13,
  values 20,
  values 14,
  values 15,
  0,
  values 16,
  values 17,
  values 18,
  values 19,
  values 20,
  values 21,
  values 22,
  values 23,
  values 24,
  values 25,
  values 24 * values 48,
  0,
  values 30,
  values 26,
  values 27,
  0,
  values 28,
  values 29,
  0,
  0,
  values 30,
  values 31,
  values 32,
  values 33,
  values 34,
  values 35,
  values 36,
  values 37,
  values 38,
  values 39,
  values 40,
  values 41,
  values 42,
  values 43,
  values 44,
  0,
  values 45,
  values 46,
  values 47,
  values 23 * values 45,
  values 48,
  values 49,
  values 50,
  0,
  values 51,
  values 52,
  values 53,
  0,
  0,
  values 54,
  values 55,
  values 56,
  values 57,
  values 58,
  values 59,
  values 60
]

set_option maxRecDepth 100000 in
theorem full_eq_reconstruct_of_raw_component {R : Type*} [CommRing R]
    (full : Fin 75 → R) (rawZero : ∀ index,
      rawGeneratorEval (rawValues full) index = 0) :
    full = reconstructFull (rootValues full) := by
  have rawRelation67 : full 67 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 9
  have rawRelation66 : full 66 - full 34 * full 63 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 10
  have rawRelation62 : full 62 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 11
  have rawRelation58 : full 58 - full 26 * full 55 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 12
  have rawRelation54 : full 54 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 13
  have rawRelation38 : full 38 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 14
  have rawRelation37 : full 37 - full 35 * full 67 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 15
  have rawRelation34 : full 34 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 16
  have rawRelation31 : full 31 - full 39 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 17
  have rawRelation30 : full 30 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 18
  have rawRelation29 : full 29 - full 27 * full 59 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 19
  have rawRelation18 : full 18 - full 54 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 20
  have rawRelation15 : full 15 - full 23 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 21
  have rawRelation10 : full 10 - full 62 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 22
  have eliminated15 : full 15 = full 23 := by
    exact sub_eq_zero.mp rawRelation15
  have eliminated29 : full 29 = full 27 * full 59 := by
    exact sub_eq_zero.mp rawRelation29
  have eliminated30 : full 30 = 0 := by
    exact sub_eq_zero.mp rawRelation30
  have eliminated31 : full 31 = full 39 := by
    exact sub_eq_zero.mp rawRelation31
  have eliminated34 : full 34 = 0 := by
    exact sub_eq_zero.mp rawRelation34
  have eliminated38 : full 38 = 0 := by
    exact sub_eq_zero.mp rawRelation38
  have eliminated54 : full 54 = 0 := by
    exact sub_eq_zero.mp rawRelation54
  have eliminated58 : full 58 = full 26 * full 55 := by
    exact sub_eq_zero.mp rawRelation58
  have eliminated62 : full 62 = 0 := by
    exact sub_eq_zero.mp rawRelation62
  have eliminated67 : full 67 = 0 := by
    exact sub_eq_zero.mp rawRelation67
  have eliminated10 : full 10 = 0 := by
    calc
      full 10 = full 62 :=
        sub_eq_zero.mp rawRelation10
      _ = 0 := by
        simp [eliminated62]
  have eliminated18 : full 18 = 0 := by
    calc
      full 18 = full 54 :=
        sub_eq_zero.mp rawRelation18
      _ = 0 := by
        simp [eliminated54]
  have eliminated37 : full 37 = 0 := by
    calc
      full 37 = full 35 * full 67 :=
        sub_eq_zero.mp rawRelation37
      _ = 0 := by
        simp [eliminated67]
  have eliminated66 : full 66 = 0 := by
    calc
      full 66 = full 34 * full 63 :=
        sub_eq_zero.mp rawRelation66
      _ = 0 := by
        simp [eliminated34]
  funext coordinate
  fin_cases coordinate <;>
    simp [reconstructFull, rootValues, rootCoordinate, *]

end Krenn.Component46RootBridge

#print axioms Krenn.Component46RootBridge.full_eq_reconstruct_of_raw_component
