import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16BackgroundCalculus
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16LeibnizJointRank

/-!
# OUR evaluation of relation rows on gauge backgrounds

A relation carrier is a trace-contracted product of field letters, each letter
a curvature with an ordered word of covariant derivatives.  On a gauge
background every letter becomes a `2 × 2` matrix, and the carrier becomes the
trace-order contraction of those matrices.  The letter's word is read from the
normalized sector data, so the value depends only on the contextual class of
the carrier.  Rows become linear combinations of values.

Every genuine consequence of the field identities vanishes on every background.
This module proves that the four-field commutator row of the earlier relation
operator does not: on an explicit constant `SU(2)` background (scalars `ℚ`,
vanishing derivations, covariant derivative `ad A`, curvature `[A, A]`) it has
the value `64`.  That row is therefore not a consequence of the field
identities, whereas its Leibniz-corrected row is one.

The contraction identities for inserting a letter before or after a given
letter of a trace cycle, and the trace formula for a single cycle, are proved
in general.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CommutatorRowEvaluation

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16ShuffleQuotient
open HypercubicDimension16TraceEvaluation
open HypercubicDimension16BackgroundCalculus
open HypercubicDimension16FieldFiveCommutatorSeparator
open HypercubicDimension16LeibnizCommutator

/-! ## Two permutation identities -/

theorem insertTraceAfter_apply_castSucc_of_ne {n : ℕ}
    (σ : Equiv.Perm (Fin n)) (after index : Fin n) (hne : index ≠ after) :
    insertTraceAfter σ after (Fin.castSucc index) = Fin.castSucc (σ index) := by
  have hσ : σ index ≠ σ after := fun hequal => hne (σ.injective hequal)
  simp only [insertTraceAfter, Equiv.trans_apply, extendFinPermutation_apply_castSucc]
  apply Equiv.swap_apply_of_ne_of_ne
  · intro hequal
    exact hσ (Fin.castSucc_injective n hequal)
  · exact Fin.castSucc_ne_last _

theorem finRotate_succ_eq_insertTraceAfter (n : ℕ) :
    finRotate (n + 2) = insertTraceAfter (finRotate (n + 1)) (Fin.last n) := by
  apply Equiv.ext
  intro index
  refine Fin.lastCases ?_ (fun initial => ?_) index
  · rw [insertTraceAfter_apply_last, finRotate_last, finRotate_last]
    rfl
  · by_cases hlast : initial = Fin.last n
    · subst initial
      rw [insertTraceAfter_apply_after]
      apply Fin.ext
      rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last _)]
      simp
    · rw [insertTraceAfter_apply_castSucc_of_ne _ _ _ hlast]
      apply Fin.ext
      rw [coe_finRotate_of_ne_last (Fin.castSucc_ne_last _), Fin.val_castSucc,
        Fin.val_castSucc, coe_finRotate_of_ne_last hlast]

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-! ## Inserting a letter into a trace cycle -/

/-- States of `n + 1` labels are states of the first `n` labels and of the last. -/
def snocStateEquiv (n : ℕ) : (Fin n → Fin 2) × Fin 2 ≃ (Fin (n + 1) → Fin 2) where
  toFun state := Fin.snoc state.1 state.2
  invFun state := (fun index => state (Fin.castSucc index), state (Fin.last n))
  left_inv state := by
    rcases state with ⟨initial, final⟩
    simp
  right_inv state := Fin.snoc_init_self state

@[simp] theorem snocStateEquiv_apply (n : ℕ) (state : (Fin n → Fin 2) × Fin 2) :
    snocStateEquiv n state = Fin.snoc state.1 state.2 :=
  rfl

/-- Inserting a letter `Y` right after the letter at `after` multiplies that
letter by `Y` on the right. -/
theorem contraction_insertTraceAfter {n : ℕ} (X : Fin n → Mat S) (Y : Mat S)
    (σ : Equiv.Perm (Fin n)) (after : Fin n) :
    tracePermutationContraction (Fin.snoc X Y : Fin (n + 1) → Mat S)
        (insertTraceAfter σ after) =
      tracePermutationContraction (Function.update X after (X after * Y)) σ := by
  rw [contraction_update_mul]
  unfold tracePermutationContraction
  rw [← Equiv.sum_comp (snocStateEquiv n), Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro initial _
  apply Finset.sum_congr rfl
  intro final _
  simp only [snocStateEquiv_apply]
  rw [Fin.prod_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last, insertTraceAfter_apply_last]
  rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ after)]
  rw [insertTraceAfter_apply_after, Fin.snoc_last]
  have hrest : ∀ index ∈ Finset.univ.erase after,
      X index (initial index)
          ((Fin.snoc initial final : Fin (n + 1) → Fin 2)
            (insertTraceAfter σ after (Fin.castSucc index))) =
        X index (initial index) (initial (σ index)) := by
    intro index hindex
    rw [insertTraceAfter_apply_castSucc_of_ne σ after index
      (Finset.ne_of_mem_erase hindex), Fin.snoc_castSucc]
  rw [Finset.prod_congr rfl hrest]
  ring

/-- Inserting a letter `Y` right before the letter at `before` multiplies that
letter by `Y` on the left. -/
theorem contraction_insertTraceBefore {n : ℕ} (X : Fin n → Mat S) (Y : Mat S)
    (σ : Equiv.Perm (Fin n)) (before : Fin n) :
    tracePermutationContraction (Fin.snoc X Y : Fin (n + 1) → Mat S)
        (insertTraceBefore σ before) =
      tracePermutationContraction (Function.update X before (Y * X before)) σ := by
  unfold insertTraceBefore
  rw [contraction_insertTraceAfter, contraction_move_across_edge,
    Equiv.apply_symm_apply]

/-! ## The contraction of one cycle is a trace -/

omit [Algebra ℚ S] in
theorem contraction_fin_one (X : Fin 1 → Mat S) (σ : Equiv.Perm (Fin 1)) :
    tracePermutationContraction X σ = (X 0).trace := by
  have hσ : ∀ index, σ index = index := fun index => Subsingleton.elim _ _
  unfold tracePermutationContraction
  simp only [hσ, Fin.prod_univ_one]
  rw [← (Equiv.funUnique (Fin 1) (Fin 2)).symm.sum_comp]
  simp [Matrix.trace, Fin.sum_univ_two]

omit [CommRing S] [Algebra ℚ S] in
theorem ofFn_update_last {n : ℕ} (f : Fin (n + 1) → Mat S) (value : Mat S) :
    List.ofFn (Function.update f (Fin.last n) value) =
      (List.ofFn fun index : Fin n => f (Fin.castSucc index)).concat value := by
  rw [List.ofFn_succ']
  congr 1
  · congr 1
    funext index
    exact Function.update_of_ne (Fin.castSucc_ne_last index) _ _
  · exact Function.update_self _ _ _

/-- The contraction around the cycle `0 → 1 → ⋯ → n → 0` is the trace of the
ordered product. -/
theorem contraction_finRotate : ∀ (n : ℕ) (X : Fin (n + 1) → Mat S),
    tracePermutationContraction X (finRotate (n + 1)) = (List.ofFn X).prod.trace
  | 0, X => by
      rw [contraction_fin_one]
      simp
  | n + 1, X => by
      have hX : X = Fin.snoc (fun index => X (Fin.castSucc index)) (X (Fin.last (n + 1))) :=
        (Fin.snoc_init_self X).symm
      rw [finRotate_succ_eq_insertTraceAfter]
      conv_lhs => rw [hX]
      rw [contraction_insertTraceAfter, contraction_finRotate n, ofFn_update_last]
      conv_rhs => rw [List.ofFn_succ', List.ofFn_succ']
      simp only [List.prod_concat, mul_assoc]

/-! ## Values of carriers and rows -/

/-- OUR matrix of one field letter: its derivative word, outermost first,
applied to its curvature. -/
def letterMatrix (bg : GaugeBackground S) {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount)
    (field : Fin fieldCount) : Mat S :=
  ((normalizedSectorData sector).derivativeFamily.1 field).foldr
    (fun axis matrix => bg.covDeriv axis matrix)
    (bg.curvature (sector.fieldFirst field) (sector.fieldSecond field))

/-- OUR value of a relation carrier on a background. -/
def carrierValue (bg : GaugeBackground S) (carrier : RelationCarrier) : S :=
  tracePermutationContraction (letterMatrix bg carrier.2) carrier.2.trace.traceOrder

/-- OUR value of a relation row on a background. -/
def relationValue (bg : GaugeBackground S) : RelationSpace →ₗ[ℚ] S :=
  Finsupp.linearCombination ℚ (carrierValue bg)

@[simp] theorem relationValue_single (bg : GaugeBackground S)
    (carrier : RelationCarrier) (coefficient : ℚ) :
    relationValue bg (Finsupp.single carrier coefficient) =
      coefficient • carrierValue bg carrier := by
  simp [relationValue]

/-! ## An explicit constant background -/

/-- OUR constant scalars: `ℚ` with vanishing derivations and the identity as
integral. -/
def constantScalars : DifferentialScalars ℚ where
  deriv := fun _ => 0
  deriv_mul := by intros; simp
  deriv_comm := by intros; simp
  integral := LinearMap.id
  integral_deriv := by intros; simp

/-- OUR integer connection matrices. -/
def intConnection : Fin 4 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![!![0, 0; -1, 0], !![-1, -1; 1, 1], !![-1, -1; 1, 1], !![0, -1; 0, 0]]

/-- Entrywise cast of integer matrices, a ring homomorphism. -/
def castMatrix : Matrix (Fin 2) (Fin 2) ℤ →+* Mat ℚ :=
  (Int.castRingHom ℚ).mapMatrix

/-- OUR traceless constant connection. -/
def defectConnection (μ : Fin 4) : Mat ℚ := castMatrix (intConnection μ)

/-- OUR constant background: `D_μ = ad A_μ`, `F_μν = [A_μ, A_ν]`. -/
def defectBackground : GaugeBackground ℚ where
  scalars := constantScalars
  connection := defectConnection
  connection_traceless := by
    intro μ
    fin_cases μ <;>
      simp [defectConnection, castMatrix, intConnection, Matrix.trace, Fin.sum_univ_two]

theorem defectBackground_mderiv (μ : Fin 4) (X : Mat ℚ) :
    defectBackground.scalars.mderiv μ X = 0 := by
  ext i j
  change constantScalars.deriv μ (X i j) = 0
  rfl

theorem defectBackground_covDeriv (μ : Fin 4) (X : Mat ℚ) :
    defectBackground.covDeriv μ X =
      defectConnection μ * X - X * defectConnection μ := by
  rw [GaugeBackground.covDeriv, defectBackground_mderiv, zero_add]
  rfl

/-- OUR integer word matrix: a derivative word, outermost first, applied by
`ad A` to an integer matrix. -/
def intWordMatrix (word : List (Fin 4)) (base : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  word.foldr (fun axis matrix =>
    intConnection axis * matrix - matrix * intConnection axis) base

/-- OUR integer curvature `[A_μ, A_ν]`. -/
def intCurvature (μ ν : Fin 4) : Matrix (Fin 2) (Fin 2) ℤ :=
  intConnection μ * intConnection ν - intConnection ν * intConnection μ

theorem defectBackground_curvature (μ ν : Fin 4) :
    defectBackground.curvature μ ν = castMatrix (intCurvature μ ν) := by
  rw [GaugeBackground.curvature, defectBackground_mderiv, defectBackground_mderiv,
    sub_self, zero_add, intCurvature, map_sub, map_mul, map_mul]
  rfl

theorem defectBackground_foldr (word : List (Fin 4))
    (base : Matrix (Fin 2) (Fin 2) ℤ) :
    word.foldr (fun axis matrix => defectBackground.covDeriv axis matrix)
        (castMatrix base) =
      castMatrix (intWordMatrix word base) := by
  induction word with
  | nil => rfl
  | cons axis rest ih =>
      simp only [List.foldr_cons, intWordMatrix] at ih ⊢
      rw [ih, defectBackground_covDeriv, map_sub, map_mul, map_mul]
      rfl

theorem letterMatrix_defect {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    letterMatrix defectBackground sector = fun field =>
      castMatrix (intWordMatrix ((normalizedSectorData sector).derivativeFamily.1 field)
        (intCurvature (sector.fieldFirst field) (sector.fieldSecond field))) := by
  funext field
  unfold letterMatrix
  rw [defectBackground_curvature, defectBackground_foldr]

theorem castMatrix_trace (M : Matrix (Fin 2) (Fin 2) ℤ) :
    (castMatrix M).trace = (M.trace : ℚ) := by
  simp [castMatrix, Matrix.trace, Fin.sum_univ_two]

theorem castMatrix_ofFn_prod {n : ℕ} (M : Fin n → Matrix (Fin 2) (Fin 2) ℤ) :
    (List.ofFn fun index => castMatrix (M index)).prod =
      castMatrix (List.ofFn M).prod := by
  rw [map_list_prod, List.map_ofFn]
  rfl

/-! ## The four-field row of the earlier operator is not a field identity -/

theorem fieldFourCarrier_traceOrder :
    fieldFourCarrier.2.trace.traceOrder = finRotate 4 := by
  decide

/-- OUR integer letters of the four-field source and its swapped form. -/
def fieldFourIntLetters (last : Fin 4) (secondLast : Fin 4) :
    Fin 4 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![intWordMatrix [2, 0, 1, 3, 0, 1, secondLast, last] (intCurvature 0 3),
    intCurvature 2 3, intCurvature 0 3, intCurvature 0 2]

theorem letterMatrix_fieldFourCarrier :
    letterMatrix defectBackground fieldFourCarrier.2 =
      fun field => castMatrix (fieldFourIntLetters 2 0 field) := by
  rw [letterMatrix_defect]
  funext field
  fin_cases field <;> rfl

theorem letterMatrix_fieldFourSwapped :
    letterMatrix defectBackground
        (swapExactDerivativePositions fieldFourCarrier fieldFourSite.outer
          fieldFourSite.inner).2 =
      fun field => castMatrix (fieldFourIntLetters 0 2 field) := by
  rw [letterMatrix_defect]
  funext field
  fin_cases field <;> rfl

/-- OUR integer letters of the five-field insertions: the source's four letters
with the outer derivative word only, then the inserted curvature `F_02`. -/
def fieldFiveIntLetters : Fin 5 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![intWordMatrix [2, 0, 1, 3, 0, 1] (intCurvature 0 3),
    intCurvature 2 3, intCurvature 0 3, intCurvature 0 2, intCurvature 0 2]

theorem fieldFourInsertion_derivativeWord (side : CurvatureInsertionSide) :
    (insertCurvatureCarrier fieldFourSite side).2.derivativeWord =
      { ownerAtPosition := fun _ => (0 : Fin 5)
        axisAtPosition := fun position =>
          Fin.ofNat 4 (#[2, 0, 1, 3, 0, 1].getD position.1 0) } := by
  apply OrderedDerivativeWord.ext
  · funext position
    cases side <;> exact fieldFourBefore_derivativeOwner position
  · funext position
    cases side <;> exact fieldFourBefore_derivativeAxis position

theorem fieldFourInsertion_word (side : CurvatureInsertionSide)
    (field : Fin (insertCurvatureCarrier fieldFourSite side).1.1) :
    (normalizedSectorData (insertCurvatureCarrier fieldFourSite side).2).derivativeFamily.1
        field =
      if field.1 = 0 then [2, 0, 1, 3, 0, 1] else [] := by
  change ownerAxisProjection field
      (sectorGlobalWord (insertCurvatureCarrier fieldFourSite side).2).toList = _
  unfold sectorGlobalWord
  rw [fieldFourInsertion_derivativeWord]
  rcases field with ⟨value, hvalue⟩
  change value < 5 at hvalue
  interval_cases value <;> rfl

theorem letterMatrix_fieldFourInsertion (side : CurvatureInsertionSide) :
    letterMatrix defectBackground (insertCurvatureCarrier fieldFourSite side).2 =
      fun field => castMatrix (fieldFiveIntLetters field) := by
  rw [letterMatrix_defect]
  funext field
  rw [fieldFourInsertion_word]
  rcases field with ⟨value, hvalue⟩
  change value < 5 at hvalue
  interval_cases value <;> cases side <;> rfl

theorem carrierValue_fieldFourCarrier :
    carrierValue defectBackground fieldFourCarrier =
      ((List.ofFn (fieldFourIntLetters 2 0)).prod.trace : ℚ) := by
  unfold carrierValue
  rw [fieldFourCarrier_traceOrder, contraction_finRotate 3,
    letterMatrix_fieldFourCarrier, castMatrix_ofFn_prod, castMatrix_trace]

theorem carrierValue_fieldFourSwapped :
    carrierValue defectBackground
        (swapExactDerivativePositions fieldFourCarrier fieldFourSite.outer
          fieldFourSite.inner) =
      ((List.ofFn (fieldFourIntLetters 0 2)).prod.trace : ℚ) := by
  have hvalue :
      carrierValue defectBackground
          (swapExactDerivativePositions fieldFourCarrier fieldFourSite.outer
            fieldFourSite.inner) =
        tracePermutationContraction
          (fun field : Fin 4 => castMatrix (fieldFourIntLetters 0 2 field))
          (finRotate 4) := by
    unfold carrierValue
    rw [letterMatrix_fieldFourSwapped]
    rfl
  rw [hvalue, contraction_finRotate 3, castMatrix_ofFn_prod, castMatrix_trace]

theorem update_castMatrix {n : ℕ} (letters : Fin n → Matrix (Fin 2) (Fin 2) ℤ)
    (index : Fin n) (value : Matrix (Fin 2) (Fin 2) ℤ) :
    Function.update (fun position => castMatrix (letters position)) index
        (castMatrix value) =
      fun position => castMatrix (Function.update letters index value position) := by
  funext position
  by_cases hposition : position = index
  · subst hposition
    simp
  · simp [Function.update_of_ne hposition]

theorem carrierValue_fieldFourInsertion (side : CurvatureInsertionSide) :
    carrierValue defectBackground (insertCurvatureCarrier fieldFourSite side) =
      ((List.ofFn (Function.update (fun index : Fin 4 => fieldFiveIntLetters (Fin.castSucc index))
        0 (match side with
          | .before => fieldFiveIntLetters 4 * fieldFiveIntLetters 0
          | .after => fieldFiveIntLetters 0 * fieldFiveIntLetters 4))).prod.trace : ℚ) := by
  unfold carrierValue
  rw [letterMatrix_fieldFourInsertion]
  have hsnoc : (fun field : Fin 5 => castMatrix (fieldFiveIntLetters field)) =
      Fin.snoc (fun index : Fin 4 => castMatrix (fieldFiveIntLetters (Fin.castSucc index)))
        (castMatrix (fieldFiveIntLetters (Fin.last 4))) :=
    (Fin.snoc_init_self _).symm
  rw [hsnoc]
  cases side
  · change tracePermutationContraction _
        (insertTraceBefore fieldFourCarrier.2.trace.traceOrder 0) = _
    rw [contraction_insertTraceBefore, fieldFourCarrier_traceOrder,
      contraction_finRotate 3, ← map_mul, update_castMatrix,
      castMatrix_ofFn_prod, castMatrix_trace]
    rfl
  · change tracePermutationContraction _
        (insertTraceAfter fieldFourCarrier.2.trace.traceOrder 0) = _
    rw [contraction_insertTraceAfter, fieldFourCarrier_traceOrder,
      contraction_finRotate 3, ← map_mul, update_castMatrix,
      castMatrix_ofFn_prod, castMatrix_trace]
    rfl

/-- The value of the earlier four-field commutator row on the constant
background. -/
theorem relationValue_covariantCommutatorRow_fieldFour :
    relationValue defectBackground (covariantCommutatorRow fieldFourSite) = 64 := by
  unfold covariantCommutatorRow
  simp only [map_sub, map_add, relationValue_single, one_smul]
  rw [carrierValue_fieldFourCarrier, carrierValue_fieldFourSwapped,
    carrierValue_fieldFourInsertion, carrierValue_fieldFourInsertion]
  norm_cast

/-- The four-field commutator row of the earlier relation operator is not a
consequence of the field identities: it does not vanish on the constant
background. -/
theorem covariantCommutatorRow_fieldFour_not_fieldIdentity :
    ∃ bg : GaugeBackground ℚ,
      relationValue bg (covariantCommutatorRow fieldFourSite) ≠ 0 :=
  ⟨defectBackground, by
    rw [relationValue_covariantCommutatorRow_fieldFour]
    norm_num⟩

#print axioms contraction_insertTraceAfter
#print axioms contraction_insertTraceBefore
#print axioms contraction_finRotate
#print axioms relationValue_covariantCommutatorRow_fieldFour
#print axioms covariantCommutatorRow_fieldFour_not_fieldIdentity

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CommutatorRowEvaluation
