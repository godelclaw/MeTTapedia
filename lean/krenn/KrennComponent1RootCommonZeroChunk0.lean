import KrennComponent1RootBridge

namespace Krenn.Component1RootCommonZero.Chunk0

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData
open Krenn.FrozenCase0CollapseLayer
open Krenn.Component1Normalization
open Krenn.Component1RootBridge

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1500000 in
theorem rootBlock_of_base_and_component {R : Type*} [CommRing R]
    (full : Fin 75 → R) (base : Krenn.FrozenCase0System.CommonZero full)
    (selectedVanish : ∀ generator ∈ componentGenerators 0,
      generatorEval (reduceRaw (rawValues full)) generator = 0) :
    ∀ offset : Fin 40, eval₂Hom (Int.castRingHom R) (rootValues full)
      (Krenn.Component1.Tree.rootEquations ⟨0 + offset.val, by omega⟩).toPoly = 0 := by
  have collapse := raw_collapse_of_base_common_zero full base
  have rawZero : ∀ index, rawGeneratorEval (rawValues full) index = 0 :=
    rawComponent1_vanishes (rawValues full) collapse selectedVanish
  have identified := full_eq_reconstruct_of_raw_component full rawZero
  intro offset
  fin_cases offset
  · have source := base 163
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 371
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 494
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 380
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 532
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 535
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 381
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 192
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 9
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 10
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 520
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 11
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 12
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 16
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 328
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 18
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 19
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 480
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 172
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 20
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 291
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 26
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 306
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 340
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 29
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 31
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 308
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 385
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 186
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 89
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 523
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 298
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 342
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 23
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 590
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 122
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 173
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 372
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 72
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 601
    rw [identified] at source
    simp [Krenn.Component1.Tree.rootEquations, Krenn.Component1.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl

end Krenn.Component1RootCommonZero.Chunk0
