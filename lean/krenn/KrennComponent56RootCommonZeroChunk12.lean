import KrennComponent56RootBridge

namespace Krenn.Component56RootCommonZero.Chunk12

open MvPolynomial
open Krenn.SparseCertificate
open Krenn.LatticeCombinationReflection
open Krenn.CollapseReductionReflection
open Krenn.CollapseComponentContainment
open Krenn.CollapseComponentContainmentData
open Krenn.FrozenCase0CollapseLayer
open Krenn.Component56Normalization
open Krenn.Component56RootBridge

set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false
set_option linter.unnecessarySeqFocus false

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1500000 in
theorem rootBlock_of_base_and_component {R : Type*} [CommRing R]
    (full : Fin 75 → R) (base : Krenn.FrozenCase0System.CommonZero full)
    (selectedVanish : ∀ generator ∈ componentGenerators 55,
      generatorEval (reduceRaw (rawValues full)) generator = 0) :
    ∀ offset : Fin 40, eval₂Hom (Int.castRingHom R) (rootValues full)
      (Krenn.Component56.Tree.rootEquations ⟨480 + offset.val, by omega⟩).toPoly = 0 := by
  have collapse := raw_collapse_of_base_common_zero full base
  have rawZero : ∀ index, rawGeneratorEval (rawValues full) index = 0 :=
    rawComponent56_vanishes (rawValues full) collapse selectedVanish
  have identified := full_eq_reconstruct_of_raw_component full rawZero
  intro offset
  fin_cases offset
  · have source := base 374
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 376
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 377
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 379
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 380
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 381
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 382
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 384
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 393
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 394
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 661
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 662
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 672
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 673
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 452
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 453
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 689
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 464
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 465
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 739
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 469
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 697
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 741
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 699
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 485
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 494
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 495
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 500
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 710
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 508
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 509
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 515
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 530
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 535
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 536
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 544
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 546
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 581
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 585
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl
  · have source := base 586
    rw [identified] at source
    simp [Krenn.Component56.Tree.rootEquations, Krenn.Component56.Root.rootEquations, Krenn.FrozenCase0System.equations, SparsePoly.toPoly, SparseTerm.toPoly, rootValues, reconstructFull, rootCoordinate, sub_eq_add_neg] at source ⊢
    convert source using 1 <;> ac_rfl

end Krenn.Component56RootCommonZero.Chunk12
