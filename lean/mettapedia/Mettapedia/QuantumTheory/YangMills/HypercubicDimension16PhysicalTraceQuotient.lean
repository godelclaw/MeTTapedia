import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceEvaluationReynolds
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalTraceWitnessBridge

/-!
# Exact derivative-free eight-field standard trace quotient

The selected sparse rows provide an independent `11556`-row subfamily of the
literal standard trace submodule.  Ninety-eight ordinary matrix evaluations
annihilate every standard trace row and remain independent on the certified
free classes.  These opposite inequalities identify the complete standard
trace submodule and give quotient dimension `98`.

This is the derivative-free eight-field trace quotient.  Covariant
commutators couple it to lower-field derivative sectors in the joint
dimension-sixteen physical quotient, so no joint-sector claim is made here.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalTraceQuotient

open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants
open HypercubicDimension16TraceOrbitBasis
open HypercubicDimension16TraceRankTheorem
open HypercubicDimension16TraceFiniteQuotient
open HypercubicDimension16FieldEightPhysicalTrace
open HypercubicDimension16PhysicalTraceWitnessSemantics
open HypercubicDimension16PhysicalTraceWitnessBridge
open HypercubicDimension16PhysicalTraceEvaluationReynolds

theorem rationalChartReynolds_ambientExtend (value : AmbientVector) :
    rationalChartReynolds (ambientExtend value) =
      positiveRepresentativeReynoldsBasis.repr.symm value := by
  induction value using Finsupp.induction_linear with
  | zero => simp [rationalChartReynolds]
  | add left right hleft hright =>
      simpa only [map_add, rationalChartReynolds_add] using
        congrArg₂ (· + ·) hleft hright
  | single column coefficient =>
      have hindex : Fin.ofNat 11654 column.1 = column := by
        apply Fin.ext
        simp [Fin.coe_ofNat_eq_mod, Nat.mod_eq_of_lt column.isLt]
      simp [ambientExtend, rationalChartReynolds, hindex]

theorem rationalChartReynolds_selectedRawVector
    (index : Fin 11556) :
    rationalChartReynolds (selectedRawVector index) =
      positiveRepresentativeReynoldsBasis.repr.symm
        (ambientSelectedRawVector index) := by
  rw [← ambientExtend_ambientSelectedRawVector]
  exact rationalChartReynolds_ambientExtend _

theorem rationalChartReynolds_selectedRawVector_linearIndependent :
    LinearIndependent ℚ
      (fun index : Fin 11556 =>
        rationalChartReynolds (selectedRawVector index)) := by
  have hmapped : LinearIndependent ℚ
      (fun index : Fin 11556 =>
        positiveRepresentativeReynoldsBasis.repr.symm
          (ambientSelectedRawVector index)) :=
    ambientSelectedRawVector_linearIndependent.map'
      positiveRepresentativeReynoldsBasis.repr.symm.toLinearMap
      (LinearMap.ker_eq_bot.mpr
        positiveRepresentativeReynoldsBasis.repr.symm.injective)
  simpa only [rationalChartReynolds_selectedRawVector] using hmapped

def selectedPhysicalGenerator (index : Fin 11556) :
    FieldEightTraceGenerator :=
  Classical.choose (selectedPhysicalTraceRow_reynolds index)

theorem selectedPhysicalGenerator_reynolds (index : Fin 11556) :
    fieldEightReynoldsToInvariant
        (fieldEightPhysicalTraceRow (selectedPhysicalGenerator index)) =
      rationalChartReynolds (selectedRawVector index) := by
  rw [← integerChartReynolds_selectedIntegerVector]
  exact Classical.choose_spec (selectedPhysicalTraceRow_reynolds index)

theorem selectedPhysicalCoinvariantRows_linearIndependent :
    LinearIndependent ℚ
      (fun index : Fin 11556 =>
        fieldEightCoinvariantTraceRow (selectedPhysicalGenerator index)) := by
  apply LinearIndependent.of_comp
    fieldEightSignedOrbitCoinvariantEquivInvariant.toLinearMap
  have hfamily :
      (fieldEightSignedOrbitCoinvariantEquivInvariant.toLinearMap :
          FieldEightSignedOrbitCoinvariant →
            sectorFieldOrbitInvariantSubmodule 8 0) ∘
          (fun index : Fin 11556 =>
            fieldEightCoinvariantTraceRow
              (selectedPhysicalGenerator index)) =
        fun index : Fin 11556 =>
          rationalChartReynolds (selectedRawVector index) := by
    funext index
    change fieldEightReynoldsToInvariant
        (fieldEightPhysicalTraceRow (selectedPhysicalGenerator index)) = _
    exact selectedPhysicalGenerator_reynolds index
  have htarget := rationalChartReynolds_selectedRawVector_linearIndependent
  rw [← hfamily] at htarget
  exact htarget

theorem selectedPhysicalCoinvariantSpan_finrank :
    Module.finrank ℚ
        (Submodule.span ℚ
          (Set.range fun index : Fin 11556 =>
            fieldEightCoinvariantTraceRow
              (selectedPhysicalGenerator index))) = 11556 := by
  rw [finrank_span_eq_card selectedPhysicalCoinvariantRows_linearIndependent]
  simp

theorem physicalTraceRelationSubmodule_finrank_ge :
    11556 ≤ Module.finrank ℚ fieldEightPhysicalTraceRelationSubmodule := by
  let selectedSpan : Submodule ℚ FieldEightSignedOrbitCoinvariant :=
    Submodule.span ℚ
      (Set.range fun index : Fin 11556 =>
        fieldEightCoinvariantTraceRow (selectedPhysicalGenerator index))
  have hle : selectedSpan ≤ fieldEightPhysicalTraceRelationSubmodule := by
    apply Submodule.span_le.mpr
    rintro _ ⟨index, rfl⟩
    exact Submodule.subset_span ⟨selectedPhysicalGenerator index, rfl⟩
  have hfinrank := Submodule.finrank_mono hle
  rw [show Module.finrank ℚ selectedSpan = 11556 by
    exact selectedPhysicalCoinvariantSpan_finrank] at hfinrank
  exact hfinrank

theorem physicalTraceQuotient_finrank_ge :
    98 ≤ Module.finrank ℚ FieldEightPhysicalTraceQuotient := by
  have hspan : Module.finrank ℚ
      (Submodule.span ℚ (Set.range physicalTraceFreeClass)) = 98 := by
    rw [finrank_span_eq_card physicalTraceFreeClass_linearIndependent]
    simp
  rw [← hspan]
  exact Submodule.finrank_le _

theorem physicalTraceRelationSubmodule_finrank_le :
    Module.finrank ℚ fieldEightPhysicalTraceRelationSubmodule ≤ 11556 := by
  have hquotient := physicalTraceQuotient_finrank_ge
  rw [Submodule.finrank_quotient,
    fieldEightSignedOrbitCoinvariant_finrank] at hquotient
  omega

/-- The literal standard trace submodule has exactly the rank of the selected
sparse family. -/
theorem physicalTraceRelationSubmodule_finrank :
    Module.finrank ℚ fieldEightPhysicalTraceRelationSubmodule = 11556 :=
  le_antisymm physicalTraceRelationSubmodule_finrank_le
    physicalTraceRelationSubmodule_finrank_ge

/-- Exact dimension of the complete derivative-free eight-field standard
trace quotient. -/
theorem physicalTraceQuotient_finrank :
    Module.finrank ℚ FieldEightPhysicalTraceQuotient = 98 := by
  rw [Submodule.finrank_quotient,
    fieldEightSignedOrbitCoinvariant_finrank,
    physicalTraceRelationSubmodule_finrank]

/-- The certified free classes form a basis of the complete standard trace
quotient. -/
noncomputable def physicalTraceFreeBasis :
    Module.Basis (Fin 98) ℚ FieldEightPhysicalTraceQuotient :=
  basisOfLinearIndependentOfCardEqFinrank
    physicalTraceFreeClass_linearIndependent (by
      rw [physicalTraceQuotient_finrank]
      simp)

@[simp] theorem physicalTraceFreeBasis_apply (index : Fin 98) :
    physicalTraceFreeBasis index = physicalTraceFreeClass index := by
  simp [physicalTraceFreeBasis]

end HypercubicDimension16PhysicalTraceQuotient
end YangMills
end QuantumTheory
end Mettapedia
