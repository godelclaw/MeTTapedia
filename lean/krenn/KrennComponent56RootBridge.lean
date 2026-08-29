import KrennComponent56Normalization
import KrennFrozenCase0CollapseLayer
import KrennFrozenCase0System
import KrennComponent56Tree

/-!
The semantic seam from a full frozen case-0 valuation through the
external component-56 linear elimination.  The generated finite data
are rechecked by Lean; source hashes below are provenance only.
-/

namespace Krenn.Component56RootBridge

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.FrozenCase0CollapseLayer
open Krenn.Component56Normalization

def reducedRootSystemSHA256 : String := "fbbd7d45e6e83576d1057de6b27350a6566719970ad6752fa3b61e1df3a71885"
def reducedRootFileSHA256 : String := "af24e5e696b2b0408f90efd0fa72ee78da21e359db1f66898c60fb7705991bf5"

def rootCoordinate : Fin 57 → Fin 75 := ![
  0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 14, 16, 17, 20, 22, 24, 25, 26, 27, 28, 32, 33, 34, 35, 36, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 60, 61, 62, 63, 64, 65, 68, 69, 70, 71, 72, 73, 74
]

noncomputable def rootValues {R : Type*} (full : Fin 75 → R) : Fin 57 → R :=
  fun coordinate => full (rootCoordinate coordinate)

noncomputable def reconstructFull {R : Type*} [CommRing R]
    (values : Fin 57 → R) : Fin 75 → R := ![
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
  values 46,
  0,
  values 10,
  0,
  values 11,
  0,
  values 12,
  values 13,
  values 40,
  0,
  values 14,
  0,
  values 15,
  0,
  values 16,
  values 17,
  values 18,
  values 19,
  values 20,
  0,
  0,
  0,
  values 21,
  values 22,
  values 23,
  values 24,
  values 25,
  0,
  0,
  0,
  values 26,
  values 27,
  values 28,
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
  values 18 * values 41,
  0,
  values 44,
  values 45,
  values 46,
  values 47,
  values 48,
  values 49,
  values 23 * values 47,
  0,
  values 50,
  values 51,
  values 52,
  values 53,
  values 54,
  values 55,
  values 56
]

set_option maxRecDepth 100000 in
theorem full_eq_reconstruct_of_raw_component {R : Type*} [CommRing R]
    (full : Fin 75 → R) (rawZero : ∀ index,
      rawGeneratorEval (rawValues full) index = 0) :
    full = reconstructFull (rootValues full) := by
  have rawRelation67 : full 67 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 0
  have rawRelation66 : full 66 - full 34 * full 63 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 1
  have rawRelation59 : full 59 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 2
  have rawRelation58 : full 58 - full 26 * full 55 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 3
  have rawRelation39 : full 39 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 4
  have rawRelation38 : full 38 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 5
  have rawRelation37 : full 37 - full 35 * full 67 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 6
  have rawRelation31 : full 31 - full 39 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 7
  have rawRelation30 : full 30 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 8
  have rawRelation29 : full 29 - full 27 * full 59 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 9
  have rawRelation23 : full 23 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 10
  have rawRelation21 : full 21 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 11
  have rawRelation19 : full 19 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 12
  have rawRelation18 : full 18 - full 54 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 13
  have rawRelation15 : full 15 - full 23 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 14
  have rawRelation13 : full 13 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 15
  have rawRelation11 : full 11 - 0 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 16
  have rawRelation10 : full 10 - full 62 = 0 := by
    simpa [rawGeneratorEval, rawPositive, rawNegative, rawValues, rawCoordinate,
      monomial_add, monomial_single_one] using rawZero 17
  have eliminated10 : full 10 = full 62 := by
    exact sub_eq_zero.mp rawRelation10
  have eliminated11 : full 11 = 0 := by
    exact sub_eq_zero.mp rawRelation11
  have eliminated13 : full 13 = 0 := by
    exact sub_eq_zero.mp rawRelation13
  have eliminated18 : full 18 = full 54 := by
    exact sub_eq_zero.mp rawRelation18
  have eliminated19 : full 19 = 0 := by
    exact sub_eq_zero.mp rawRelation19
  have eliminated21 : full 21 = 0 := by
    exact sub_eq_zero.mp rawRelation21
  have eliminated23 : full 23 = 0 := by
    exact sub_eq_zero.mp rawRelation23
  have eliminated30 : full 30 = 0 := by
    exact sub_eq_zero.mp rawRelation30
  have eliminated38 : full 38 = 0 := by
    exact sub_eq_zero.mp rawRelation38
  have eliminated39 : full 39 = 0 := by
    exact sub_eq_zero.mp rawRelation39
  have eliminated58 : full 58 = full 26 * full 55 := by
    exact sub_eq_zero.mp rawRelation58
  have eliminated59 : full 59 = 0 := by
    exact sub_eq_zero.mp rawRelation59
  have eliminated66 : full 66 = full 34 * full 63 := by
    exact sub_eq_zero.mp rawRelation66
  have eliminated67 : full 67 = 0 := by
    exact sub_eq_zero.mp rawRelation67
  have eliminated15 : full 15 = 0 := by
    calc
      full 15 = full 23 :=
        sub_eq_zero.mp rawRelation15
      _ = 0 := by
        simp [eliminated23]
  have eliminated29 : full 29 = 0 := by
    calc
      full 29 = full 27 * full 59 :=
        sub_eq_zero.mp rawRelation29
      _ = 0 := by
        simp [eliminated59]
  have eliminated31 : full 31 = 0 := by
    calc
      full 31 = full 39 :=
        sub_eq_zero.mp rawRelation31
      _ = 0 := by
        simp [eliminated39]
  have eliminated37 : full 37 = 0 := by
    calc
      full 37 = full 35 * full 67 :=
        sub_eq_zero.mp rawRelation37
      _ = 0 := by
        simp [eliminated67]
  funext coordinate
  fin_cases coordinate <;>
    simp [reconstructFull, rootValues, rootCoordinate, *]

end Krenn.Component56RootBridge

#print axioms Krenn.Component56RootBridge.full_eq_reconstruct_of_raw_component
