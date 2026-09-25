import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16RelationEvaluationDescent

/-!
# OUR hypercubic equivariance of background evaluation

A signed axis permutation `h` rotates a gauge background: the connection
becomes `A'_μ = s_μ A_{π μ}` and the derivations rotate the same way, so
`D'_μ = s_μ D_{π μ}` and `F'_μν = s_μ s_ν F_{π μ, π ν}`.  The value of a labeled
sector on the rotated background is its tensor sign times the value of the
rotated sector on the original background.  Hence the integrated evaluation on
the orbit space intertwines the signed hypercubic action with rotation of the
background, and the Reynolds average of a vector is evaluated by averaging the
evaluations over the `384` rotated backgrounds.

Application.  The Reynolds-averaged four-field commutator row of the earlier
operator is a vector of the earlier joint invariant relation submodule.  On the
constant background its averaged value is `32/3`: the earlier row takes the
value `64` on exactly `64` of the rotated backgrounds and `0` on the others.
Every integrated evaluation vanishes on the corrected joint submodule, so that
invariant vector of the earlier joint submodule is not a joint relation.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16RelationEvaluationEquivariance

open V14HypercubicFDCensus
open SU2LatticeFDCensusNoGo
open V14HypercubicQuarticCensus
open HypercubicRawFDCharacterCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16ShuffleQuotient
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16TraceEvaluation
open HypercubicDimension16BackgroundCalculus
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16JointQuotientInvariants
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16FieldFiveCommutatorSeparator
open HypercubicDimension16LeibnizRelationOperator
open HypercubicDimension16CommutatorRowEvaluation
open HypercubicDimension16RelationRowSoundness
open HypercubicDimension16RelationEvaluationDescent

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-! ## Rotated backgrounds -/

/-- OUR scalars rotated by a hypercubic element. -/
def rotateScalars (sc : DifferentialScalars S) (h : Hypercubic4) : DifferentialScalars S where
  deriv μ := Hypercubic4.axisSign h μ • sc.deriv (h.perm μ)
  deriv_mul μ f g := by
    simp only [LinearMap.smul_apply, sc.deriv_mul, smul_add, smul_mul_assoc, mul_smul_comm]
  deriv_comm μ ν f := by
    simp only [LinearMap.smul_apply, LinearMap.map_smul, sc.deriv_comm]
    rw [smul_comm]
  integral := sc.integral
  integral_deriv μ f := by
    simp only [LinearMap.smul_apply, LinearMap.map_smul, sc.integral_deriv, smul_zero]

/-- OUR background rotated by a hypercubic element. -/
def rotateBackground (bg : GaugeBackground S) (h : Hypercubic4) : GaugeBackground S where
  scalars := rotateScalars bg.scalars h
  connection μ := Hypercubic4.axisSign h μ • bg.connection (h.perm μ)
  connection_traceless μ := by rw [Matrix.trace_smul, bg.connection_traceless, smul_zero]

theorem rotate_mderiv (bg : GaugeBackground S) (h : Hypercubic4) (μ : Fin 4) (X : Mat S) :
    (rotateScalars bg.scalars h).mderiv μ X =
      Hypercubic4.axisSign h μ • bg.scalars.mderiv (h.perm μ) X := by
  ext i j
  simp [DifferentialScalars.mderiv, rotateScalars, Matrix.map_apply]

theorem rotate_covDeriv (bg : GaugeBackground S) (h : Hypercubic4) (μ : Fin 4) (X : Mat S) :
    (rotateBackground bg h).covDeriv μ X =
      Hypercubic4.axisSign h μ • bg.covDeriv (h.perm μ) X := by
  change (rotateScalars bg.scalars h).mderiv μ X +
      (Hypercubic4.axisSign h μ • bg.connection (h.perm μ)) * X -
        X * (Hypercubic4.axisSign h μ • bg.connection (h.perm μ)) = _
  rw [rotate_mderiv, Matrix.smul_mul, Matrix.mul_smul]
  unfold GaugeBackground.covDeriv
  rw [smul_sub, smul_add]

theorem rotate_curvature (bg : GaugeBackground S) (h : Hypercubic4) (μ ν : Fin 4) :
    (rotateBackground bg h).curvature μ ν =
      (Hypercubic4.axisSign h μ * Hypercubic4.axisSign h ν) •
        bg.curvature (h.perm μ) (h.perm ν) := by
  change (rotateScalars bg.scalars h).mderiv μ
        (Hypercubic4.axisSign h ν • bg.connection (h.perm ν)) -
      (rotateScalars bg.scalars h).mderiv ν
        (Hypercubic4.axisSign h μ • bg.connection (h.perm μ)) +
      (Hypercubic4.axisSign h μ • bg.connection (h.perm μ)) *
        (Hypercubic4.axisSign h ν • bg.connection (h.perm ν)) -
      (Hypercubic4.axisSign h ν • bg.connection (h.perm ν)) *
        (Hypercubic4.axisSign h μ • bg.connection (h.perm μ)) = _
  rw [rotate_mderiv, rotate_mderiv, mderiv_qsmul, mderiv_qsmul]
  unfold GaugeBackground.curvature
  simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
  module

/-! ## Letters and values on rotated backgrounds -/

theorem foldr_rotate (bg : GaugeBackground S) (h : Hypercubic4) (word : List (Fin 4)) (c : ℚ)
    (M : Mat S) :
    word.foldr (fun a matrix => (rotateBackground bg h).covDeriv a matrix) (c • M) =
      ((word.map (Hypercubic4.axisSign h)).prod * c) •
        (word.map h.perm).foldr (fun a matrix => bg.covDeriv a matrix) M := by
  induction word with
  | nil => simp
  | cons a rest ih =>
      rw [List.foldr_cons, ih, rotate_covDeriv, covDeriv_qsmul, smul_smul]
      simp only [List.map_cons, List.prod_cons, List.foldr_cons, mul_assoc]

theorem curvature_rotate_plane (bg : GaugeBackground S) (h : Hypercubic4)
    (plane : OrientedPlane) :
    (rotateBackground bg h).curvature plane.first plane.second =
      (planeTensorSign h plane : ℚ) •
        bg.curvature (planeAction h plane).first (planeAction h plane).second := by
  rw [rotate_curvature, curvature_eq_orientation bg (h.perm plane.first) (h.perm plane.second),
    smul_smul]
  congr 1
  have hne : h.perm plane.first ≠ h.perm plane.second := fun hequal =>
    (ne_of_lt plane.ordered) (h.perm.injective hequal)
  unfold planeTensorSign planeReorderSign axisPairOrientationCoefficient Hypercubic4.axisSign
  by_cases hlt : h.perm plane.first < h.perm plane.second <;>
    by_cases hfirst : h.reflected plane.first <;>
      by_cases hsecond : h.reflected plane.second <;>
        simp [hne, hlt, hfirst, hsecond]

theorem labeledLetter_rotate (bg : GaugeBackground S) (h : Hypercubic4) {fieldCount d : ℕ}
    (sector : LabeledLocalWordSector fieldCount d) (field : Fin fieldCount) :
    labeledLetter (rotateBackground bg h) sector field =
      (sector.decoration.1 field).tensorSign h •
        labeledLetter bg (sector.hypercubicAct h) field := by
  unfold labeledLetter
  rw [curvature_rotate_plane, foldr_rotate]
  unfold LocalFieldLetter.tensorSign
  rw [List.map_ofFn, List.map_ofFn, List.prod_ofFn, mul_comm]
  rfl

theorem labeledValue_rotate (bg : GaugeBackground S) (h : Hypercubic4) {fieldCount d : ℕ}
    (sector : LabeledLocalWordSector fieldCount d) :
    labeledValue (rotateBackground bg h) sector =
      sector.tensorSign h • labeledValue bg (sector.hypercubicAct h) := by
  unfold labeledValue
  have hletters : labeledLetter (rotateBackground bg h) sector = fun field =>
      (sector.decoration.1 field).tensorSign h •
        labeledLetter bg (sector.hypercubicAct h) field :=
    funext (labeledLetter_rotate bg h sector)
  rw [hletters, contraction_smul_each]
  rfl

theorem orbitValue_rotate (bg : GaugeBackground S) (h : Hypercubic4) {fieldCount d : ℕ}
    (orbit : FieldRelabelOrbitCarrier fieldCount d) :
    orbitValue (rotateBackground bg h) orbit =
      orbit.tensorSign h • orbitValue bg (orbit.hypercubicAct h) := by
  induction orbit using Quotient.inductionOn with
  | h sector => exact labeledValue_rotate bg h sector

theorem orbitIntegratedValue_signedAction (bg : GaugeBackground S) (h : Hypercubic4)
    (value : ExactFieldRelabelOrbitSpace) :
    orbitIntegratedValue bg (signedExactFieldRelabelOrbitAction h value) =
      orbitIntegratedValue (rotateBackground bg h) value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add first second hfirst hsecond => simp only [map_add, hfirst, hsecond]
  | single target coefficient =>
      rw [signedExactFieldRelabelOrbitAction_single, orbitIntegratedValue_single,
        orbitIntegratedValue_single, orbitValue_rotate]
      change coefficient * target.2.tensorSign h *
          bg.scalars.integral (orbitValue bg (target.2.hypercubicAct h)) =
        coefficient *
          bg.scalars.integral (target.2.tensorSign h • orbitValue bg (target.2.hypercubicAct h))
      rw [map_smul, smul_eq_mul]
      ring

theorem orbitIntegratedValue_reynolds (bg : GaugeBackground S)
    (value : ExactFieldRelabelOrbitSpace) :
    orbitIntegratedValue bg (exactFieldOrbitReynolds value) =
      (1 / 384 : ℚ) *
        ∑ h : Hypercubic4, orbitIntegratedValue (rotateBackground bg h) value := by
  unfold exactFieldOrbitReynolds
  rw [LinearMap.smul_apply, LinearMap.sum_apply, map_smul, map_sum, smul_eq_mul]
  simp only [orbitIntegratedValue_signedAction]

/-! ## Constant integer backgrounds -/

/-- OUR constant background with an integer traceless connection. -/
def intBackground (connection : Fin 4 → Matrix (Fin 2) (Fin 2) ℤ)
    (htraceless : ∀ μ, (connection μ).trace = 0) : GaugeBackground ℚ where
  scalars := constantScalars
  connection μ := castMatrix (connection μ)
  connection_traceless μ := by rw [castMatrix_trace, htraceless, Int.cast_zero]

section IntBackground

variable (connection : Fin 4 → Matrix (Fin 2) (Fin 2) ℤ)
  (htraceless : ∀ μ, (connection μ).trace = 0)

/-- OUR integer word matrix for an integer connection. -/
def connectionWordMatrix (word : List (Fin 4)) (base : Matrix (Fin 2) (Fin 2) ℤ) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  word.foldr (fun axis matrix => connection axis * matrix - matrix * connection axis) base

/-- OUR integer curvature `[A_μ, A_ν]` of an integer connection. -/
def connectionCurvature (μ ν : Fin 4) : Matrix (Fin 2) (Fin 2) ℤ :=
  connection μ * connection ν - connection ν * connection μ

theorem intBackground_mderiv (μ : Fin 4) (X : Mat ℚ) :
    (intBackground connection htraceless).scalars.mderiv μ X = 0 := by
  ext i j
  change constantScalars.deriv μ (X i j) = 0
  rfl

theorem intBackground_curvature (μ ν : Fin 4) :
    (intBackground connection htraceless).curvature μ ν =
      castMatrix (connectionCurvature connection μ ν) := by
  rw [GaugeBackground.curvature, intBackground_mderiv, intBackground_mderiv, sub_self,
    zero_add, connectionCurvature, map_sub, map_mul, map_mul]
  rfl

theorem intBackground_foldr (word : List (Fin 4)) (base : Matrix (Fin 2) (Fin 2) ℤ) :
    word.foldr (fun axis matrix => (intBackground connection htraceless).covDeriv axis matrix)
        (castMatrix base) =
      castMatrix (connectionWordMatrix connection word base) := by
  induction word with
  | nil => rfl
  | cons axis rest ih =>
      simp only [List.foldr_cons, connectionWordMatrix] at ih ⊢
      rw [ih, GaugeBackground.covDeriv, intBackground_mderiv, zero_add, map_sub, map_mul,
        map_mul]
      rfl

theorem letterMatrix_intBackground {fieldCount derivativeCount : ℕ}
    (sector : DerivativeAlphaReducedSector fieldCount derivativeCount) :
    letterMatrix (intBackground connection htraceless) sector = fun field =>
      castMatrix (connectionWordMatrix connection
        ((normalizedSectorData sector).derivativeFamily.1 field)
        (connectionCurvature connection (sector.fieldFirst field) (sector.fieldSecond field))) := by
  funext field
  unfold letterMatrix
  rw [intBackground_curvature, intBackground_foldr]

/-- OUR integer letters of the four-field source for an integer connection. -/
def connectionFourLetters (last secondLast : Fin 4) : Fin 4 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![connectionWordMatrix connection [2, 0, 1, 3, 0, 1, secondLast, last]
      (connectionCurvature connection 0 3),
    connectionCurvature connection 2 3, connectionCurvature connection 0 3,
    connectionCurvature connection 0 2]

/-- OUR integer letters of the five-field insertions for an integer connection. -/
def connectionFiveLetters : Fin 5 → Matrix (Fin 2) (Fin 2) ℤ :=
  ![connectionWordMatrix connection [2, 0, 1, 3, 0, 1] (connectionCurvature connection 0 3),
    connectionCurvature connection 2 3, connectionCurvature connection 0 3,
    connectionCurvature connection 0 2, connectionCurvature connection 0 2]

/-- OUR integer value of the earlier four-field commutator row. -/
def earlierRowValue : ℤ :=
  (List.ofFn (connectionFourLetters connection 2 0)).prod.trace -
    (List.ofFn (connectionFourLetters connection 0 2)).prod.trace -
    (List.ofFn (Function.update
      (fun index : Fin 4 => connectionFiveLetters connection (Fin.castSucc index)) 0
      (connectionFiveLetters connection 4 * connectionFiveLetters connection 0))).prod.trace +
    (List.ofFn (Function.update
      (fun index : Fin 4 => connectionFiveLetters connection (Fin.castSucc index)) 0
      (connectionFiveLetters connection 0 * connectionFiveLetters connection 4))).prod.trace

theorem relationValue_intBackground_covariantCommutatorRow :
    relationValue (intBackground connection htraceless) (covariantCommutatorRow fieldFourSite) =
      (earlierRowValue connection : ℚ) := by
  unfold covariantCommutatorRow
  simp only [map_sub, map_add, relationValue_single, one_smul]
  have hsource : carrierValue (intBackground connection htraceless) fieldFourCarrier =
      ((List.ofFn (connectionFourLetters connection 2 0)).prod.trace : ℚ) := by
    have hletters : letterMatrix (intBackground connection htraceless) fieldFourCarrier.2 =
        fun field => castMatrix (connectionFourLetters connection 2 0 field) := by
      rw [letterMatrix_intBackground]
      funext field
      fin_cases field <;> rfl
    unfold carrierValue
    rw [fieldFourCarrier_traceOrder, contraction_finRotate 3, hletters, castMatrix_ofFn_prod,
      castMatrix_trace]
  have hswap : carrierValue (intBackground connection htraceless)
        (swapExactDerivativePositions fieldFourCarrier fieldFourSite.outer fieldFourSite.inner) =
      ((List.ofFn (connectionFourLetters connection 0 2)).prod.trace : ℚ) := by
    have hletters : letterMatrix (intBackground connection htraceless)
          (swapExactDerivativePositions fieldFourCarrier fieldFourSite.outer
            fieldFourSite.inner).2 =
        fun field => castMatrix (connectionFourLetters connection 0 2 field) := by
      rw [letterMatrix_intBackground]
      funext field
      fin_cases field <;> rfl
    have hvalue : carrierValue (intBackground connection htraceless)
          (swapExactDerivativePositions fieldFourCarrier fieldFourSite.outer fieldFourSite.inner) =
        tracePermutationContraction
          (fun field : Fin 4 => castMatrix (connectionFourLetters connection 0 2 field))
          (finRotate 4) := by
      unfold carrierValue
      rw [hletters]
      rfl
    rw [hvalue, contraction_finRotate 3, castMatrix_ofFn_prod, castMatrix_trace]
  have hinsertLetters : ∀ side : CurvatureInsertionSide,
      letterMatrix (intBackground connection htraceless)
          (insertCurvatureCarrier fieldFourSite side).2 =
        fun field => castMatrix (connectionFiveLetters connection field) := by
    intro side
    rw [letterMatrix_intBackground]
    funext field
    rw [fieldFourInsertion_word]
    rcases field with ⟨value, hvalue⟩
    change value < 5 at hvalue
    interval_cases value <;> cases side <;> rfl
  have hsnoc : (fun field : Fin 5 => castMatrix (connectionFiveLetters connection field)) =
      Fin.snoc (fun index : Fin 4 => castMatrix (connectionFiveLetters connection
          (Fin.castSucc index)))
        (castMatrix (connectionFiveLetters connection (Fin.last 4))) :=
    (Fin.snoc_init_self _).symm
  have hbefore : carrierValue (intBackground connection htraceless)
        (insertCurvatureCarrier fieldFourSite .before) =
      ((List.ofFn (Function.update
        (fun index : Fin 4 => connectionFiveLetters connection (Fin.castSucc index)) 0
        (connectionFiveLetters connection 4 * connectionFiveLetters connection 0))).prod.trace :
          ℚ) := by
    unfold carrierValue
    rw [hinsertLetters, hsnoc]
    change tracePermutationContraction _
        (insertTraceBefore fieldFourCarrier.2.trace.traceOrder 0) = _
    rw [contraction_insertTraceBefore, fieldFourCarrier_traceOrder, contraction_finRotate 3,
      ← map_mul, update_castMatrix, castMatrix_ofFn_prod, castMatrix_trace]
    rfl
  have hafter : carrierValue (intBackground connection htraceless)
        (insertCurvatureCarrier fieldFourSite .after) =
      ((List.ofFn (Function.update
        (fun index : Fin 4 => connectionFiveLetters connection (Fin.castSucc index)) 0
        (connectionFiveLetters connection 0 * connectionFiveLetters connection 4))).prod.trace :
          ℚ) := by
    unfold carrierValue
    rw [hinsertLetters, hsnoc]
    change tracePermutationContraction _
        (insertTraceAfter fieldFourCarrier.2.trace.traceOrder 0) = _
    rw [contraction_insertTraceAfter, fieldFourCarrier_traceOrder, contraction_finRotate 3,
      ← map_mul, update_castMatrix, castMatrix_ofFn_prod, castMatrix_trace]
    rfl
  rw [hsource, hswap, hbefore, hafter]
  unfold earlierRowValue
  push_cast
  ring

end IntBackground

/-! ## The rotated constant backgrounds -/

/-- OUR integer connection of the constant background rotated by `h`. -/
def rotatedIntConnection (h : Hypercubic4) (μ : Fin 4) : Matrix (Fin 2) (Fin 2) ℤ :=
  (if h.reflected μ then -1 else 1 : ℤ) • intConnection (h.perm μ)

theorem intConnection_traceless (μ : Fin 4) : (intConnection μ).trace = 0 := by
  fin_cases μ <;> simp [intConnection, Matrix.trace, Fin.sum_univ_two]

theorem rotatedIntConnection_traceless (h : Hypercubic4) (μ : Fin 4) :
    (rotatedIntConnection h μ).trace = 0 := by
  rw [rotatedIntConnection, Matrix.trace_smul, intConnection_traceless, smul_zero]

theorem rotate_defectBackground (h : Hypercubic4) :
    rotateBackground defectBackground h =
      intBackground (rotatedIntConnection h) (rotatedIntConnection_traceless h) := by
  have hscalars : rotateScalars constantScalars h = constantScalars := by
    unfold rotateScalars constantScalars
    congr 1
    funext μ
    simp
  have hconnection : (fun μ => Hypercubic4.axisSign h μ • defectConnection (h.perm μ)) =
      fun μ => castMatrix (rotatedIntConnection h μ) := by
    funext μ
    rw [rotatedIntConnection, map_zsmul, defectConnection, Hypercubic4.axisSign]
    by_cases hreflected : h.reflected μ <;> simp [hreflected]
  unfold rotateBackground intBackground
  change ({ scalars := rotateScalars constantScalars h,
            connection := fun μ => Hypercubic4.axisSign h μ • defectConnection (h.perm μ),
            connection_traceless := _ } : GaugeBackground ℚ) = _
  simp only [hscalars, hconnection]

theorem sum_earlierRowValue_rotated :
    ∑ h : Hypercubic4, earlierRowValue (rotatedIntConnection h) = 4096 := by
  rw [← Equiv.sum_comp hypercubicCharacterCodeEquiv]
  simp only [hypercubicCharacterCodeEquiv, Equiv.ofBijective_apply]
  decide +kernel

/-! ## The earlier invariant four-field row is not a corrected joint relation -/

theorem jointIntegratedValue_defect_fieldFourInvariantRow :
    jointIntegratedValue defectBackground (fieldFourInvariantCommutatorRow .offShell) =
      32 / 3 := by
  change orbitIntegratedValue defectBackground (exactFieldOrbitReynolds
    (orbitPhysicalRelationOperator .offShell
      (Finsupp.single (fieldFourCommutatorGenerator .offShell) 1))) = _
  rw [orbitIntegratedValue_reynolds]
  have hterm : ∀ h : Hypercubic4,
      orbitIntegratedValue (rotateBackground defectBackground h)
          (orbitPhysicalRelationOperator .offShell
            (Finsupp.single (fieldFourCommutatorGenerator .offShell) 1)) =
        (earlierRowValue (rotatedIntConnection h) : ℚ) := by
    intro h
    rw [orbitColumn_fieldFour_eq, orbitIntegratedValue_normalize, rotate_defectBackground]
    unfold integratedValue
    rw [LinearMap.comp_apply, relationValue_intBackground_covariantCommutatorRow]
    rfl
  simp only [hterm]
  rw [← Int.cast_sum, sum_earlierRowValue_rotated]
  norm_num

/-- The Reynolds-averaged four-field commutator row of the earlier operator
belongs to the earlier joint invariant relation submodule but is not a joint
relation of the corrected operator. -/
theorem fieldFourInvariantRow_not_mem_leibnizJointInvariantRelationSubmodule :
    fieldFourInvariantCommutatorRow .offShell ∈ jointInvariantRelationSubmodule .offShell ∧
      fieldFourInvariantCommutatorRow .offShell ∉
        leibnizJointInvariantRelationSubmodule .offShell := by
  refine ⟨fieldFourInvariantCommutatorRow_mem .offShell, ?_⟩
  intro hmem
  have hzero := leibnizJointInvariantRelationSubmodule_le_ker defectBackground
    (policy := .offShell) (fun h => nomatch h) hmem
  rw [LinearMap.mem_ker, jointIntegratedValue_defect_fieldFourInvariantRow] at hzero
  norm_num at hzero

#print axioms labeledValue_rotate
#print axioms orbitIntegratedValue_reynolds
#print axioms sum_earlierRowValue_rotated
#print axioms fieldFourInvariantRow_not_mem_leibnizJointInvariantRelationSubmodule

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16RelationEvaluationEquivariance
