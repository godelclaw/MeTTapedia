import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16RelationRowSoundness

/-!
# OUR descent of background evaluation to the joint quotient

A labeled local-word sector has a value on every gauge background: each letter
is its derivative word applied to the curvature of its oriented plane, and the
letters are contracted along the trace.  The value is invariant under field
relabeling, so it is defined on field-label orbits.  The value of a relation
carrier is its orientation coefficient times the value of its normalized
labeled sector, because the curvature is antisymmetric and the contraction is
multilinear.  Hence the integrated evaluation on relation rows factors through
the exact contextual quotient and the field-label orbit quotient.

Consequently every integrated evaluation vanishes on the Leibniz-corrected
orbit relation submodule and on the corrected joint invariant relation
submodule, and descends to the corrected joint scalar quotient.  On the
constant background of `HypercubicDimension16CommutatorRowEvaluation` the
orbit column of the earlier four-field commutator row has value `64`, so that
column of the earlier orbit relation range lies outside the corrected one.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia.QuantumTheory.YangMills.HypercubicDimension16RelationEvaluationDescent

open V14HypercubicFDCensus
open SU2LatticeFDCensusNoGo
open V14HypercubicQuarticCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16AntisymmetryQuotient
open HypercubicDimension16ContextualQuotient
open HypercubicDimension16ShuffleQuotient
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16OrbitCarrierBridge
open HypercubicDimension16TraceEvaluation
open HypercubicDimension16BackgroundCalculus
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16JointPhysicalQuotient
open HypercubicDimension16LeibnizRelationOperator
open HypercubicDimension16CommutatorRowEvaluation
open HypercubicDimension16RelationRowSoundness

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-! ## Rational scalars, orientation and multilinearity -/

theorem mderiv_qsmul (sc : DifferentialScalars S) (μ : Fin 4) (q : ℚ) (X : Mat S) :
    sc.mderiv μ (q • X) = q • sc.mderiv μ X := by
  ext i j
  simp [DifferentialScalars.mderiv, Matrix.map_apply]

theorem covDeriv_qsmul (bg : GaugeBackground S) (μ : Fin 4) (q : ℚ) (X : Mat S) :
    bg.covDeriv μ (q • X) = q • bg.covDeriv μ X := by
  unfold GaugeBackground.covDeriv
  rw [mderiv_qsmul, Matrix.mul_smul, Matrix.smul_mul, smul_sub, smul_add]

theorem foldr_covDeriv_qsmul (bg : GaugeBackground S) (word : List (Fin 4)) (q : ℚ)
    (X : Mat S) :
    word.foldr (fun a matrix => bg.covDeriv a matrix) (q • X) =
      q • word.foldr (fun a matrix => bg.covDeriv a matrix) X := by
  induction word with
  | nil => rfl
  | cons a rest ih => simp only [List.foldr_cons, ih, covDeriv_qsmul]

theorem planeLookup_of_lt :
    ∀ μ ν : Fin 4, μ < ν → (planeLookup μ ν).first = μ ∧ (planeLookup μ ν).second = ν := by
  decide

theorem planeLookup_of_gt :
    ∀ μ ν : Fin 4, ν < μ → (planeLookup μ ν).first = ν ∧ (planeLookup μ ν).second = μ := by
  decide

theorem curvature_eq_orientation (bg : GaugeBackground S) (μ ν : Fin 4) :
    bg.curvature μ ν =
      axisPairOrientationCoefficient (μ, ν) •
        bg.curvature (planeLookup μ ν).first (planeLookup μ ν).second := by
  unfold axisPairOrientationCoefficient
  rcases lt_trichotomy μ ν with hlt | heq | hgt
  · obtain ⟨hfirst, hsecond⟩ := planeLookup_of_lt μ ν hlt
    simp [ne_of_lt hlt, hlt, hfirst, hsecond]
  · subst heq
    simp [bg.curvature_self]
  · obtain ⟨hfirst, hsecond⟩ := planeLookup_of_gt μ ν hgt
    simp only [ne_of_gt hgt, not_lt.mpr (le_of_lt hgt), ite_false, hfirst, hsecond]
    rw [bg.curvature_antisymm ν μ, neg_one_smul]

theorem contraction_smul_each {n : ℕ} (c : Fin n → ℚ) (X : Fin n → Mat S)
    (σ : Equiv.Perm (Fin n)) :
    tracePermutationContraction (fun index => c index • X index) σ =
      (∏ index, c index) • tracePermutationContraction X σ := by
  unfold tracePermutationContraction
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro state _
  simp only [Matrix.smul_apply, Algebra.smul_def]
  rw [Finset.prod_mul_distrib, map_prod]

/-! ## Values of labeled sectors and of field-label orbits -/

/-- OUR letter of a labeled sector on a background. -/
def labeledLetter (bg : GaugeBackground S) {fieldCount d : ℕ}
    (sector : LabeledLocalWordSector fieldCount d) (field : Fin fieldCount) : Mat S :=
  (List.ofFn (sector.decoration.1 field).derivativeAxis).foldr
    (fun a matrix => bg.covDeriv a matrix)
    (bg.curvature (sector.decoration.1 field).plane.first
      (sector.decoration.1 field).plane.second)

/-- OUR value of a labeled sector on a background. -/
def labeledValue (bg : GaugeBackground S) {fieldCount d : ℕ}
    (sector : LabeledLocalWordSector fieldCount d) : S :=
  tracePermutationContraction (labeledLetter bg sector) sector.trace

theorem labeledValue_relabel (bg : GaugeBackground S) {fieldCount d : ℕ}
    (rename : Equiv.Perm (Fin fieldCount)) (sector : LabeledLocalWordSector fieldCount d) :
    labeledValue bg (sector.relabel rename) = labeledValue bg sector := by
  unfold labeledValue
  have hletters : labeledLetter bg (sector.relabel rename) =
      labeledLetter bg sector ∘ rename.symm := by
    funext field
    rfl
  rw [hletters]
  exact tracePermutationContraction_relabel rename (labeledLetter bg sector) sector.trace

/-- OUR value of a field-label orbit on a background. -/
def orbitValue (bg : GaugeBackground S) {fieldCount d : ℕ} :
    FieldRelabelOrbitCarrier fieldCount d → S :=
  Quotient.lift (labeledValue bg) (by
    intro first second hrelated
    change first ∈ MulAction.orbit (Equiv.Perm (Fin fieldCount)) second at hrelated
    obtain ⟨rename, hrename⟩ := hrelated
    rw [← hrename]
    exact labeledValue_relabel bg rename second)

@[simp] theorem orbitValue_mk (bg : GaugeBackground S) {fieldCount d : ℕ}
    (sector : LabeledLocalWordSector fieldCount d) :
    orbitValue bg (Quotient.mk _ sector) = labeledValue bg sector :=
  rfl

/-- OUR integrated evaluation on the exact field-label orbit space. -/
def orbitIntegratedValue (bg : GaugeBackground S) : ExactFieldRelabelOrbitSpace →ₗ[ℚ] ℚ :=
  Finsupp.linearCombination ℚ
    (fun target : ExactFieldRelabelOrbitCarrier => bg.scalars.integral (orbitValue bg target.2))

@[simp] theorem orbitIntegratedValue_single (bg : GaugeBackground S)
    (target : ExactFieldRelabelOrbitCarrier) (coefficient : ℚ) :
    orbitIntegratedValue bg (Finsupp.single target coefficient) =
      coefficient * bg.scalars.integral (orbitValue bg target.2) := by
  simp [orbitIntegratedValue]

/-! ## Carrier values factor through the normalized sector -/

theorem letterMatrix_eq_orientation (bg : GaugeBackground S) (carrier : RelationCarrier) :
    letterMatrix bg carrier.2 = fun field =>
      axisPairOrientationCoefficient (sectorFieldAxisAssignment carrier.2 field) •
        labeledLetter bg
          (orientedLocalSectorEquivLabeled _ _ (normalizedSectorData carrier.2)) field := by
  funext field
  unfold letterMatrix labeledLetter
  rw [curvature_eq_orientation bg (carrier.2.fieldFirst field) (carrier.2.fieldSecond field),
    foldr_covDeriv_qsmul]
  congr 1
  change _ = (List.ofFn ((normalizedSectorData carrier.2).derivativeFamily.1 field).get).foldr _ _
  rw [List.ofFn_get]
  rfl

theorem carrierValue_eq_labeledValue (bg : GaugeBackground S) (carrier : RelationCarrier) :
    carrierValue bg carrier =
      fieldAxisOrientationCoefficient (sectorFieldAxisAssignment carrier.2) •
        labeledValue bg
          (orientedLocalSectorEquivLabeled _ _ (normalizedSectorData carrier.2)) := by
  unfold carrierValue labeledValue
  rw [letterMatrix_eq_orientation, contraction_smul_each]
  rfl

theorem orbitIntegratedValue_normalize (bg : GaugeBackground S) (value : RelationSpace) :
    orbitIntegratedValue bg (normalizeExactFieldRelabel (normalizeExactContextual value)) =
      integratedValue bg value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add first second hfirst hsecond => simp only [map_add, hfirst, hsecond]
  | single carrier coefficient =>
      rw [normalizeExactContextual_single, map_smul, map_smul,
        HypercubicDimension16FieldFiveCommutatorSeparator.normalizeExactContextualBasis_fieldRelabel,
        orbitIntegratedValue_single]
      unfold integratedValue
      rw [LinearMap.comp_apply, relationValue_single, map_smul,
        carrierValue_eq_labeledValue, map_smul]
      rfl

/-! ## Descent to the corrected orbit and joint quotients -/

theorem leibnizOrbitPhysicalRelationSubmodule_le_ker (bg : GaugeBackground S)
    {policy : PhysicalRelationPolicy} (hshell : policy = .onShell → IsOnShell bg) :
    leibnizOrbitPhysicalRelationSubmodule policy ≤ LinearMap.ker (orbitIntegratedValue bg) := by
  rintro value ⟨source, rfl⟩
  rw [LinearMap.mem_ker]
  change orbitIntegratedValue bg (normalizeExactFieldRelabel
    (normalizeExactContextual (leibnizPhysicalRelationOperator policy source))) = 0
  rw [orbitIntegratedValue_normalize]
  exact leibnizPhysicalRelationSubmodule_le_ker_integratedValue bg hshell ⟨source, rfl⟩

/-- OUR integrated evaluation on the invariant orbit space. -/
def jointIntegratedValue (bg : GaugeBackground S) :
    exactFieldOrbitInvariantSubmodule →ₗ[ℚ] ℚ :=
  (orbitIntegratedValue bg).comp exactFieldOrbitInvariantSubmodule.subtype

theorem leibnizJointInvariantRelationSubmodule_le_ker (bg : GaugeBackground S)
    {policy : PhysicalRelationPolicy} (hshell : policy = .onShell → IsOnShell bg) :
    leibnizJointInvariantRelationSubmodule policy ≤ LinearMap.ker (jointIntegratedValue bg) :=
  fun _ hvalue => leibnizOrbitPhysicalRelationSubmodule_le_ker bg hshell hvalue

/-- OUR integrated evaluation on the corrected joint scalar quotient. -/
def quotientIntegratedValue (bg : GaugeBackground S) {policy : PhysicalRelationPolicy}
    (hshell : policy = .onShell → IsOnShell bg) :
    LeibnizJointScalarPhysicalQuotient policy →ₗ[ℚ] ℚ :=
  (leibnizJointInvariantRelationSubmodule policy).liftQ (jointIntegratedValue bg)
    (leibnizJointInvariantRelationSubmodule_le_ker bg hshell)

@[simp] theorem quotientIntegratedValue_mk (bg : GaugeBackground S)
    {policy : PhysicalRelationPolicy} (hshell : policy = .onShell → IsOnShell bg)
    (value : exactFieldOrbitInvariantSubmodule) :
    quotientIntegratedValue bg hshell (Submodule.Quotient.mk value) =
      jointIntegratedValue bg value :=
  rfl

/-! ## The earlier four-field column lies outside the corrected orbit range -/

theorem orbitColumn_fieldFour_eq :
    orbitPhysicalRelationOperator .offShell
        (Finsupp.single
          (HypercubicDimension16FieldFiveCommutatorSeparator.fieldFourCommutatorGenerator .offShell)
          1) =
      normalizeExactFieldRelabel (normalizeExactContextual
        (covariantCommutatorRow HypercubicDimension16FieldFiveCommutatorSeparator.fieldFourSite)) := by
  rw [orbitPhysicalRelationOperator, LinearMap.comp_apply, normalizedPhysicalRelationOperator,
    LinearMap.comp_apply, physicalRelationOperator_single, one_smul]
  rfl

theorem orbitIntegratedValue_defect_fieldFourColumn :
    orbitIntegratedValue defectBackground
        (orbitPhysicalRelationOperator .offShell
          (Finsupp.single
            (HypercubicDimension16FieldFiveCommutatorSeparator.fieldFourCommutatorGenerator
              .offShell) 1)) = 64 := by
  rw [orbitColumn_fieldFour_eq, orbitIntegratedValue_normalize,
    integratedValue_defect_covariantCommutatorRow]

/-- The orbit column of the earlier four-field commutator row belongs to the
earlier orbit relation range but not to the corrected one. -/
theorem fieldFourColumn_not_mem_leibnizOrbitPhysicalRelationSubmodule :
    orbitPhysicalRelationOperator .offShell
        (Finsupp.single
          (HypercubicDimension16FieldFiveCommutatorSeparator.fieldFourCommutatorGenerator .offShell)
          1) ∉ leibnizOrbitPhysicalRelationSubmodule .offShell := by
  intro hmem
  have hzero := leibnizOrbitPhysicalRelationSubmodule_le_ker defectBackground
    (policy := .offShell) (fun h => nomatch h) hmem
  rw [LinearMap.mem_ker, orbitIntegratedValue_defect_fieldFourColumn] at hzero
  norm_num at hzero

#print axioms labeledValue_relabel
#print axioms carrierValue_eq_labeledValue
#print axioms orbitIntegratedValue_normalize
#print axioms leibnizJointInvariantRelationSubmodule_le_ker
#print axioms fieldFourColumn_not_mem_leibnizOrbitPhysicalRelationSubmodule

end Mettapedia.QuantumTheory.YangMills.HypercubicDimension16RelationEvaluationDescent
