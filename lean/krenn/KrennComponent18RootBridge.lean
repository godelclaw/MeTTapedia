import KrennComponent18Normalization
import KrennFrozenCase0CollapseLayer
import KrennFrozenCase0System
import KrennComponent18Tree

/-!
The semantic seam from a full frozen case-0 valuation through the
external component-18 linear elimination.  The generated finite data
are rechecked by Lean; source hashes below are provenance only.
-/

namespace Krenn.Component18RootBridge

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.FrozenCase0CollapseLayer
open Krenn.Component18Normalization

def reducedRootSystemSHA256 : String := "fba17639cdae21f99f804cde81b7c6b45d5ff73de7549d833238d2fa43b7b49a"
def reducedRootFileSHA256 : String := "54c1a46199849c9408578e9adec10c381d9338dc6c3205f618f5fcdc10312441"

def rootCoordinate : Fin 61 → Fin 75 := ![
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 12, 14, 16, 17, 20, 21, 23, 24, 25, 26, 27, 28, 30, 32, 33, 34, 35, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 56, 57, 59, 60, 61, 63, 64, 67, 68, 69, 70, 71, 72, 73, 74
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
  0,
  values 12,
  values 17,
  values 13,
  values 14,
  values 45,
  0,
  values 15,
  values 16,
  0,
  values 17,
  values 18,
  values 19,
  values 20,
  values 21,
  values 22,
  values 21 * values 48,
  values 23,
  values 30,
  values 24,
  values 25,
  values 26,
  values 27,
  values 28,
  values 27 * values 53,
  values 29,
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
  values 45,
  0,
  values 46,
  values 47,
  0,
  values 48,
  values 49,
  values 50,
  0,
  values 51,
  values 52,
  0,
  values 26 * values 51,
  values 53,
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
  have rawRelation66 : full 66 - full 34 * full 63 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 8
  have rawRelation65 : full 65 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 9
  have rawRelation62 : full 62 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 10
  have rawRelation58 : full 58 - full 26 * full 55 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 11
  have rawRelation55 : full 55 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 12
  have rawRelation37 : full 37 - full 35 * full 67 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 13
  have rawRelation31 : full 31 - full 39 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 14
  have rawRelation29 : full 29 - full 27 * full 59 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 15
  have rawRelation22 : full 22 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 16
  have rawRelation19 : full 19 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 17
  have rawRelation18 : full 18 - full 54 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 18
  have rawRelation15 : full 15 - full 23 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 19
  have rawRelation13 : full 13 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 20
  have rawRelation10 : full 10 - full 62 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 21
  have eliminated13 : full 13 = 0 := by
    exact sub_eq_zero.mp rawRelation13
  have eliminated15 : full 15 = full 23 := by
    exact sub_eq_zero.mp rawRelation15
  have eliminated18 : full 18 = full 54 := by
    exact sub_eq_zero.mp rawRelation18
  have eliminated19 : full 19 = 0 := by
    exact sub_eq_zero.mp rawRelation19
  have eliminated22 : full 22 = 0 := by
    exact sub_eq_zero.mp rawRelation22
  have eliminated29 : full 29 = full 27 * full 59 := by
    exact sub_eq_zero.mp rawRelation29
  have eliminated31 : full 31 = full 39 := by
    exact sub_eq_zero.mp rawRelation31
  have eliminated37 : full 37 = full 35 * full 67 := by
    exact sub_eq_zero.mp rawRelation37
  have eliminated55 : full 55 = 0 := by
    exact sub_eq_zero.mp rawRelation55
  have eliminated62 : full 62 = 0 := by
    exact sub_eq_zero.mp rawRelation62
  have eliminated65 : full 65 = 0 := by
    exact sub_eq_zero.mp rawRelation65
  have eliminated66 : full 66 = full 34 * full 63 := by
    exact sub_eq_zero.mp rawRelation66
  have eliminated10 : full 10 = 0 := by
    calc
      full 10 = full 62 :=
        sub_eq_zero.mp rawRelation10
      _ = 0 := by
        simp [eliminated62]
  have eliminated58 : full 58 = 0 := by
    calc
      full 58 = full 26 * full 55 :=
        sub_eq_zero.mp rawRelation58
      _ = 0 := by
        simp [eliminated55]
  funext coordinate
  fin_cases coordinate <;>
    simp [reconstructFull, rootValues, rootCoordinate, *]

end Krenn.Component18RootBridge

#print axioms Krenn.Component18RootBridge.full_eq_reconstruct_of_raw_component
