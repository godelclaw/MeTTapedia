import KrennOfficialBridge
import KrennX5Case178Selected

/-! Generated semantic attachment for one frozen normalized f9 case. -/

namespace Krenn.X5Case178Bridge

open MonochromaticQuantumGraph
open Krenn.OfficialBridge
open Krenn.SparseCertificate
open MvPolynomial

def entry (W : WeightsN 6 3 ℂ) (u v : Fin 6) (i j : Fin 3) : ℂ :=
  W (MonochromaticQuantumGraph.mkEdge u v i j)

structure NormalizedCase (W : WeightsN 6 3 ℂ) : Prop where
  fixed_01_01 : W (MonochromaticQuantumGraph.mkEdge 0 1 0 1) = 1
  fixed_02_01 : W (MonochromaticQuantumGraph.mkEdge 0 2 0 1) = 1
  fixed_03_20 : W (MonochromaticQuantumGraph.mkEdge 0 3 2 0) = 1
  fixed_04_21 : W (MonochromaticQuantumGraph.mkEdge 0 4 2 1) = 1
  fixed_15_20 : W (MonochromaticQuantumGraph.mkEdge 1 5 2 0) = 1
  outside05 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 0 5 i j) = 0
  outside12 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 1 2 i j) = 0
  outside13 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 1 3 i j) = 0
  outside14 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 1 4 i j) = 0
  outside23 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 2 3 i j) = 0
  outside24 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 2 4 i j) = 0
  outside25 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 2 5 i j) = 0
  outside34 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 3 4 i j) = 0
  outside35 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 3 5 i j) = 0
  outside45 : ∀ i j, i ≠ j → W (MonochromaticQuantumGraph.mkEdge 4 5 i j) = 0

def values (W : WeightsN 6 3 ℂ) : Fin 70 → ℂ := ![
  entry W 0 1 0 0,
  entry W 0 1 0 2,
  entry W 0 1 1 0,
  entry W 0 1 1 1,
  entry W 0 1 1 2,
  entry W 0 1 2 0,
  entry W 0 1 2 1,
  entry W 0 1 2 2,
  entry W 0 2 0 0,
  entry W 0 2 0 2,
  entry W 0 2 1 0,
  entry W 0 2 1 1,
  entry W 0 2 1 2,
  entry W 0 2 2 0,
  entry W 0 2 2 1,
  entry W 0 2 2 2,
  entry W 0 3 0 0,
  entry W 0 3 0 1,
  entry W 0 3 0 2,
  entry W 0 3 1 0,
  entry W 0 3 1 1,
  entry W 0 3 1 2,
  entry W 0 3 2 1,
  entry W 0 3 2 2,
  entry W 0 4 0 0,
  entry W 0 4 0 1,
  entry W 0 4 0 2,
  entry W 0 4 1 0,
  entry W 0 4 1 1,
  entry W 0 4 1 2,
  entry W 0 4 2 0,
  entry W 0 4 2 2,
  entry W 0 5 0 0,
  entry W 0 5 1 1,
  entry W 0 5 2 2,
  entry W 1 2 0 0,
  entry W 1 2 1 1,
  entry W 1 2 2 2,
  entry W 1 3 0 0,
  entry W 1 3 1 1,
  entry W 1 3 2 2,
  entry W 1 4 0 0,
  entry W 1 4 1 1,
  entry W 1 4 2 2,
  entry W 1 5 0 0,
  entry W 1 5 0 1,
  entry W 1 5 0 2,
  entry W 1 5 1 0,
  entry W 1 5 1 1,
  entry W 1 5 1 2,
  entry W 1 5 2 1,
  entry W 1 5 2 2,
  entry W 2 3 0 0,
  entry W 2 3 1 1,
  entry W 2 3 2 2,
  entry W 2 4 0 0,
  entry W 2 4 1 1,
  entry W 2 4 2 2,
  entry W 2 5 0 0,
  entry W 2 5 1 1,
  entry W 2 5 2 2,
  entry W 3 4 0 0,
  entry W 3 4 1 1,
  entry W 3 4 2 2,
  entry W 3 5 0 0,
  entry W 3 5 1 1,
  entry W 3 5 2 2,
  entry W 4 5 0 0,
  entry W 4 5 1 1,
  entry W 4 5 2 2
]

private def c0 : Fin 6 → Fin 3 := ![2, 2, 0, 0, 1, 0]
private def c1 : Fin 6 → Fin 3 := ![2, 2, 2, 2, 1, 0]
private def c2 : Fin 6 → Fin 3 := ![0, 2, 1, 0, 0, 0]
private def c3 : Fin 6 → Fin 3 := ![0, 2, 1, 2, 2, 0]
private def c4 : Fin 6 → Fin 3 := ![2, 2, 0, 2, 1, 0]
private def c5 : Fin 6 → Fin 3 := ![0, 2, 1, 2, 0, 0]
private def c6 : Fin 6 → Fin 3 := ![2, 1, 2, 0, 2, 2]
private def c7 : Fin 6 → Fin 3 := ![2, 0, 0, 0, 1, 0]
private def c8 : Fin 6 → Fin 3 := ![2, 2, 2, 2, 1, 2]
private def c9 : Fin 6 → Fin 3 := ![2, 2, 2, 0, 2, 2]
private def c10 : Fin 6 → Fin 3 := ![0, 0, 1, 0, 0, 0]
private def c11 : Fin 6 → Fin 3 := ![0, 2, 1, 2, 2, 2]
private def c12 : Fin 6 → Fin 3 := ![2, 2, 0, 2, 0, 2]
private def c13 : Fin 6 → Fin 3 := ![2, 2, 0, 2, 0, 0]
private def c14 : Fin 6 → Fin 3 := ![0, 1, 2, 2, 2, 2]
private def c15 : Fin 6 → Fin 3 := ![0, 0, 0, 0, 0, 0]
private def c16 : Fin 6 → Fin 3 := ![2, 2, 2, 2, 2, 2]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
theorem selectedEquations_vanish (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W) (hcase : NormalizedCase W) :
    ∀ index : Fin 17,
      eval₂Hom (Int.castRingHom ℂ) (values W)
        (Krenn.X5Case178Selected.selectedEquations index).toPoly = 0 := by
  intro index
  have r0 := hEq c0
  have r1 := hEq c1
  have r2 := hEq c2
  have r3 := hEq c3
  have r4 := hEq c4
  have r5 := hEq c5
  have r6 := hEq c6
  have r7 := hEq c7
  have r8 := hEq c8
  have r9 := hEq c9
  have r10 := hEq c10
  have r11 := hEq c11
  have r12 := hEq c12
  have r13 := hEq c13
  have r14 := hEq c14
  have r15 := hEq c15
  have r16 := hEq c16
  rw [official_pmSum_eq_pm15] at r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
  simp [-mul_eq_zero, pm15, w, c0, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, allEqual, allEqualList, vertices, hcase.fixed_01_01, hcase.fixed_02_01, hcase.fixed_03_20, hcase.fixed_04_21, hcase.fixed_15_20, hcase.outside05, hcase.outside12, hcase.outside13, hcase.outside14, hcase.outside23, hcase.outside24, hcase.outside25, hcase.outside34, hcase.outside35, hcase.outside45] at r0 r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 r14 r15 r16
  fin_cases index
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r0
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r1
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r2
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r3
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r4
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r5
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r6
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r7
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r8
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r9
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r10
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r11
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r12
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r13
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r14
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r15
  · simp [-mul_eq_zero, Krenn.X5Case178Selected.selectedEquations, SparsePoly.toPoly, SparseTerm.toPoly, values, entry, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one]
    linear_combination r16

theorem noNormalizedCase (W : WeightsN 6 3 ℂ)
    (hEq : EqSystemN 6 3 W) (hcase : NormalizedCase W) : False := by
  exact (Krenn.X5Case178Selected.selectedHasNoCommonZero (values W))
    (selectedEquations_vanish W hEq hcase)

#print axioms Krenn.X5Case178Bridge.noNormalizedCase

end Krenn.X5Case178Bridge
