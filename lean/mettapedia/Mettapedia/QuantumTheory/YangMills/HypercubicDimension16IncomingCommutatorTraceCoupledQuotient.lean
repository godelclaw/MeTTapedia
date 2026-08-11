import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCoupledColumn
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceCanonicalProjection

/-!
# OUR local coupled field-seven/eight commutator quotient

The concrete covariant-commutator column has a derivative contribution in
field count seven and a curvature contribution in field count eight.  This
module constructs an exact two-band realization of that one physical column,
then quotients it by the span of the resulting coupled vector.

The construction is deliberately local: it is neither a census of all
field-seven/eight coordinates nor a computation of the full invariant
relation space `J_p`.  It provides a typed finite-support interface through
which later sparse rank certificates can add further physical rows and
coordinates without discarding the cross-sector terms.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IncomingCommutatorTraceCoupledQuotient

open HypercubicRawFDDimension16Census
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceProjection
open HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
open HypercubicDimension16IncomingCommutatorTraceCoupledColumn

/-- OUR seven-field orbit-carrier fibre. -/
abbrev FieldSevenOrbitCarrier := FieldRelabelOrbitCarrier 7 2

/-- OUR seven-field finite-support orbit space. -/
abbrev FieldSevenOrbitSpace := SectorFieldOrbitSpace 7 2

/-- OUR typed representation of the seven-field count. -/
def ourSevenFieldCount : Fin 9 := ⟨7, by decide⟩

/-- OUR dependent transport from an exact seven-field orbit fibre to the
ordinary seven-field orbit fibre. -/
def exactFieldSevenOrbitCast (fieldCount : Fin 9)
    (h : fieldCount = ourSevenFieldCount) :
    FieldRelabelOrbitCarrier fieldCount.1
      (dimension16DerivativeCount fieldCount) →
      FieldSevenOrbitCarrier :=
  cast (by subst fieldCount; rfl)

@[simp] theorem exactFieldSevenOrbitCast_self
    (orbit : FieldSevenOrbitCarrier)
    (h : ourSevenFieldCount = ourSevenFieldCount) :
    exactFieldSevenOrbitCast ourSevenFieldCount h orbit = orbit := by
  cases Subsingleton.elim h rfl
  rfl

/-- OUR two-band image of one exact orbit-carrier basis vector. -/
def exactFieldSevenEightProjectionBasis
    (target : ExactFieldRelabelOrbitCarrier) :
    FieldSevenOrbitSpace × FieldEightOrbitSpace :=
  match target with
  | ⟨fieldCount, orbit⟩ =>
      if hseven : fieldCount = ourSevenFieldCount then
        (Finsupp.single (exactFieldSevenOrbitCast fieldCount hseven orbit) 1, 0)
      else if height : fieldCount = ourEightFieldCount then
        (0, Finsupp.single (exactFieldEightOrbitCast fieldCount height orbit) 1)
      else 0

/-- OUR linear projection from the full exact carrier onto field counts seven
and eight. -/
def exactFieldSevenEightProjection : ExactFieldRelabelOrbitSpace →ₗ[ℚ]
    (FieldSevenOrbitSpace × FieldEightOrbitSpace) :=
  Finsupp.linearCombination ℚ exactFieldSevenEightProjectionBasis

@[simp] theorem exactFieldSevenEightProjection_single
    (target : ExactFieldRelabelOrbitCarrier) (coefficient : ℚ) :
    exactFieldSevenEightProjection (Finsupp.single target coefficient) =
      coefficient • exactFieldSevenEightProjectionBasis target := by
  simp [exactFieldSevenEightProjection]

/-- OUR coupled two-band vector for the full exact physical commutator
column. -/
def coupledIncomingCommutatorVector :
    FieldSevenOrbitSpace × FieldEightOrbitSpace :=
  exactFieldSevenEightProjectionBasis ourCommutatorSourceExactTarget -
    exactFieldSevenEightProjectionBasis ourCommutatorSwappedExactTarget -
      exactFieldSevenEightProjectionBasis
        (ourCommutatorInsertionExactTarget CurvatureInsertionSide.before) +
        exactFieldSevenEightProjectionBasis
          (ourCommutatorInsertionExactTarget CurvatureInsertionSide.after)

/-- The exact two-band projection of OUR full physical commutator column is
the coupled vector with both derivative and curvature contributions. -/
theorem exactFieldSevenEightProjection_ourCommutator_full
    (policy : PhysicalRelationPolicy) :
    exactFieldSevenEightProjection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) =
      coupledIncomingCommutatorVector := by
  rw [orbitPhysicalRelationOperator_ourCommutator_full]
  simp only [map_sub, map_add, exactFieldSevenEightProjection_single, one_smul]
  rfl

/-- OUR one-row local relation submodule in the coupled two-band space. -/
def coupledIncomingRelationSubmodule :
    Submodule ℚ (FieldSevenOrbitSpace × FieldEightOrbitSpace) :=
  Submodule.span ℚ {coupledIncomingCommutatorVector}

/-- OUR quotient of the two-band space by its concrete coupled commutator
row. -/
abbrev CoupledIncomingQuotient :=
  (FieldSevenOrbitSpace × FieldEightOrbitSpace) ⧸
    coupledIncomingRelationSubmodule

/-- OUR quotient map for the concrete two-band commutator relation. -/
def coupledIncomingQuotientMap :
    (FieldSevenOrbitSpace × FieldEightOrbitSpace) →ₗ[ℚ]
      CoupledIncomingQuotient :=
  Submodule.mkQ coupledIncomingRelationSubmodule

/-- OUR concrete full physical commutator column vanishes in the local
coupled quotient, for either relation policy. -/
theorem coupledIncomingQuotient_ourCommutator_zero
    (policy : PhysicalRelationPolicy) :
    coupledIncomingQuotientMap
      (exactFieldSevenEightProjection
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1))) = 0 := by
  rw [exactFieldSevenEightProjection_ourCommutator_full]
  change Submodule.Quotient.mk coupledIncomingCommutatorVector = 0
  exact (Submodule.Quotient.mk_eq_zero
    coupledIncomingRelationSubmodule).mpr
      (Submodule.subset_span (by simp))

/-- OUR two-band projection has the existing exact field-eight projection as
its second component. -/
theorem exactFieldSevenEightProjection_snd_eq_fieldEightProjection
    (value : ExactFieldRelabelOrbitSpace) :
    (exactFieldSevenEightProjection value).2 =
      exactFieldEightProjection value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp [hleft, hright]
  | single target coefficient =>
      rcases target with ⟨fieldCount, orbit⟩
      fin_cases fieldCount <;>
        simp [exactFieldSevenEightProjectionBasis,
          exactFieldEightProjectionBasis, ourSevenFieldCount,
          ourEightFieldCount]

/-- OUR field-eight trace map sends the full concrete commutator column to
the already certified literal incoming trace class. -/
theorem exactFieldEightTraceProjection_ourCommutator
    (policy : PhysicalRelationPolicy) :
    exactFieldEightTraceProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) =
      literalIncomingCommutatorClass := by
  have hsupport := congrArg
    (fun map : ExactFieldRelabelOrbitSpace →ₗ[ℚ]
      FieldEightPhysicalTraceQuotient =>
        map (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)))
    exactFieldEightTraceProjection_fieldEight_supported
  change exactFieldEightTraceProjection
      (orbitFieldFilter (fun fieldCount => fieldCount.1 = 8)
        (orbitPhysicalRelationOperator policy
          (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1))) =
    exactFieldEightTraceProjection
      (orbitPhysicalRelationOperator policy
        (Finsupp.single (ourFieldSevenCommutatorGenerator policy) 1)) at hsupport
  rw [actualIncomingProjection_eq_fieldEightExactEmbed,
    exactFieldEightTraceProjection_literalIncoming] at hsupport
  exact hsupport.symm

/-- The field-eight trace class of OUR coupled two-band commutator vector is
the certified nonzero literal incoming class. -/
theorem coupledIncomingCommutatorVector_traceClass :
    exactFieldEightTraceClassMap coupledIncomingCommutatorVector.2 =
      literalIncomingCommutatorClass := by
  rw [← exactFieldSevenEightProjection_ourCommutator_full .offShell]
  rw [exactFieldSevenEightProjection_snd_eq_fieldEightProjection]
  change exactFieldEightTraceProjection
    (orbitPhysicalRelationOperator .offShell
      (Finsupp.single (ourFieldSevenCommutatorGenerator .offShell) 1)) = _
  exact exactFieldEightTraceProjection_ourCommutator .offShell

/-- OUR coupled commutator row is nonzero, certified by its nonzero
field-eight trace class. -/
theorem coupledIncomingCommutatorVector_ne_zero :
    coupledIncomingCommutatorVector ≠ 0 := by
  intro hzero
  have hclass := congrArg
    (fun value : FieldSevenOrbitSpace × FieldEightOrbitSpace =>
      exactFieldEightTraceClassMap value.2) hzero
  rw [coupledIncomingCommutatorVector_traceClass] at hclass
  simpa using literalIncomingCommutatorClass_ne_zero hclass

/-- OUR local relation submodule is the singleton span of the coupled row. -/
theorem coupledIncomingRelationSubmodule_eq_span :
    coupledIncomingRelationSubmodule = ℚ ∙ coupledIncomingCommutatorVector := rfl

/-- OUR one-row coupled relation submodule has exact rational rank one. -/
theorem coupledIncomingRelationSubmodule_finrank :
    Module.finrank ℚ (ℚ ∙ coupledIncomingCommutatorVector) = 1 := by
  exact finrank_span_singleton coupledIncomingCommutatorVector_ne_zero

#print axioms exactFieldSevenEightProjection_ourCommutator_full
#print axioms coupledIncomingQuotient_ourCommutator_zero
#print axioms coupledIncomingCommutatorVector_traceClass
#print axioms coupledIncomingCommutatorVector_ne_zero
#print axioms coupledIncomingRelationSubmodule_eq_span
#print axioms coupledIncomingRelationSubmodule_finrank

end HypercubicDimension16IncomingCommutatorTraceCoupledQuotient
end YangMills
end QuantumTheory
end Mettapedia
