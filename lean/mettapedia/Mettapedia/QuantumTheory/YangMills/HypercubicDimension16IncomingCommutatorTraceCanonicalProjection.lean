import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16IncomingCommutatorTraceNoFieldEightDescent

/-!
# OUR canonical field-eight trace projection

This module constructs a concrete linear retraction from the exact
field-indexed orbit carrier to the ordinary eight-field orbit carrier.  It
discards every field count other than eight, descends through the signed
orbit and ordinary trace quotients, and is a left inverse to the typed
eight-field embedding.

The resulting full-carrier map is deliberately field-eight-supported.  Its
failure to annihilate the physical relation range is therefore an exact
obstruction to the direct field-eight-projection route, not a statement about
a genuinely joint construction retaining all coupled field sectors.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IncomingCommutatorTraceCanonicalProjection

open HypercubicRawFDDimension16Census
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalOrbitOperator
open HypercubicDimension16PhysicalRelationOperator
open HypercubicDimension16PhysicalRelationBlocks
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16IncomingCommutatorTraceCertificate
open HypercubicDimension16IncomingCommutatorTraceMismatch
open HypercubicDimension16IncomingCommutatorTraceProjection
open HypercubicDimension16IncomingCommutatorTraceNoFieldEightDescent

/-- OUR dependent transport from an exact field-eight orbit fibre to the
ordinary eight-field orbit fibre. -/
def exactFieldEightOrbitCast (fieldCount : Fin 9)
    (h : fieldCount = ourEightFieldCount) :
    FieldRelabelOrbitCarrier fieldCount.1
      (dimension16DerivativeCount fieldCount) →
      FieldEightOrbitCarrier :=
  cast (by subst fieldCount; rfl)

@[simp] theorem exactFieldEightOrbitCast_self
    (orbit : FieldEightOrbitCarrier)
    (h : ourEightFieldCount = ourEightFieldCount) :
    exactFieldEightOrbitCast ourEightFieldCount h orbit = orbit := by
  cases Subsingleton.elim h rfl
  rfl

/-- OUR exact field-eight component of one full orbit-carrier basis vector. -/
def exactFieldEightProjectionBasis
    (target : ExactFieldRelabelOrbitCarrier) : FieldEightOrbitSpace :=
  match target with
  | ⟨fieldCount, orbit⟩ =>
      if h : fieldCount = ourEightFieldCount then
        Finsupp.single (exactFieldEightOrbitCast fieldCount h orbit) 1
      else 0

/-- OUR linear field-eight projection of the full exact orbit carrier. -/
def exactFieldEightProjection : ExactFieldRelabelOrbitSpace →ₗ[ℚ]
    FieldEightOrbitSpace :=
  Finsupp.linearCombination ℚ exactFieldEightProjectionBasis

@[simp] theorem exactFieldEightProjection_single
    (target : ExactFieldRelabelOrbitCarrier) (coefficient : ℚ) :
    exactFieldEightProjection (Finsupp.single target coefficient) =
      coefficient • exactFieldEightProjectionBasis target := by
  simp [exactFieldEightProjection]

/-- OUR exact field-eight projection is a retraction of the typed inclusion. -/
theorem exactFieldEightProjection_fieldEightExactEmbed
    (value : FieldEightOrbitSpace) :
    exactFieldEightProjection (fieldEightExactEmbed value) = value := by
  induction value using Finsupp.induction_linear with
  | zero => simp [fieldEightExactEmbed]
  | add left right hleft hright =>
      simp [hleft, hright]
  | single target coefficient =>
      rw [fieldEightExactEmbed_single, exactFieldEightProjection_single]
      unfold exactFieldEightProjectionBasis fieldEightExactCarrier
      dsimp
      rw [exactFieldEightOrbitCast_self]
      simp

/-- OUR quotient map from the ordinary eight-field orbit carrier to the
ordinary derivative-free trace quotient. -/
def exactFieldEightTraceClassMap : FieldEightOrbitSpace →ₗ[ℚ]
    FieldEightPhysicalTraceQuotient :=
  (Submodule.mkQ fieldEightPhysicalTraceRelationSubmodule).comp
    (Submodule.mkQ fieldEightSignedOrbitRelationSubmodule)

/-- OUR canonical map from the full exact orbit carrier to the ordinary
eight-field trace quotient. -/
def exactFieldEightTraceProjection : ExactFieldRelabelOrbitSpace →ₗ[ℚ]
    FieldEightPhysicalTraceQuotient :=
  exactFieldEightTraceClassMap.comp exactFieldEightProjection

theorem exactFieldEightTraceClassMap_literalIncoming :
    exactFieldEightTraceClassMap literalIncomingCommutatorVector =
      literalIncomingCommutatorClass := by
  rfl

/-- OUR canonical full-carrier map sends the embedded literal pair to its
certified ordinary trace class. -/
theorem exactFieldEightTraceProjection_literalIncoming :
    exactFieldEightTraceProjection
        (fieldEightExactEmbed literalIncomingCommutatorVector) =
      literalIncomingCommutatorClass := by
  unfold exactFieldEightTraceProjection
  change exactFieldEightTraceClassMap
    (exactFieldEightProjection
      (fieldEightExactEmbed literalIncomingCommutatorVector)) = _
  rw [exactFieldEightProjection_fieldEightExactEmbed]
  exact exactFieldEightTraceClassMap_literalIncoming

/-- OUR field-eight projection is unchanged after the exact field-eight
filter. -/
theorem exactFieldEightProjection_fieldEight_filter
    (value : ExactFieldRelabelOrbitSpace) :
    exactFieldEightProjection
        (orbitFieldFilter (fun fieldCount => fieldCount.1 = 8) value) =
      exactFieldEightProjection value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      simp [hleft, hright]
  | single target coefficient =>
      rcases target with ⟨fieldCount, orbit⟩
      by_cases hheight : fieldCount.1 = 8
      · simp [orbitFieldFilter, hheight]
      · have hne : fieldCount ≠ ourEightFieldCount := by
          intro hequal
          apply hheight
          have hvalue := congrArg Fin.val hequal
          simpa [ourEightFieldCount] using hvalue
        simp [orbitFieldFilter, hheight, exactFieldEightProjection,
          exactFieldEightProjectionBasis, hne]

/-- OUR canonical full-carrier trace map is supported exactly on the
eight-field sector. -/
theorem exactFieldEightTraceProjection_fieldEight_supported :
    exactFieldEightTraceProjection.comp
      (orbitFieldFilter (fun fieldCount => fieldCount.1 = 8)) =
      exactFieldEightTraceProjection := by
  apply LinearMap.ext
  intro value
  change exactFieldEightTraceClassMap
      (exactFieldEightProjection
        (orbitFieldFilter (fun fieldCount => fieldCount.1 = 8) value)) =
    exactFieldEightTraceClassMap (exactFieldEightProjection value)
  rw [exactFieldEightProjection_fieldEight_filter]

/-- The canonical field-eight trace projection cannot annihilate the full
physical relation range, for either physical relation policy. -/
theorem exactFieldEightTraceProjection_not_annihilate_full_relations
    (policy : PhysicalRelationPolicy) :
    ¬ orbitPhysicalRelationSubmodule policy ≤
      LinearMap.ker exactFieldEightTraceProjection := by
  exact no_fieldEight_supported_trace_quotient_descent policy
    exactFieldEightTraceProjection
    exactFieldEightTraceProjection_fieldEight_supported
    exactFieldEightTraceProjection_literalIncoming

#print axioms exactFieldEightProjection_fieldEightExactEmbed
#print axioms exactFieldEightTraceProjection_literalIncoming
#print axioms exactFieldEightTraceProjection_fieldEight_supported
#print axioms exactFieldEightTraceProjection_not_annihilate_full_relations

end HypercubicDimension16IncomingCommutatorTraceCanonicalProjection
end YangMills
end QuantumTheory
end Mettapedia
