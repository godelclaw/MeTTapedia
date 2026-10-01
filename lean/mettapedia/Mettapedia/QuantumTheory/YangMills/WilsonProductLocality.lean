import Mettapedia.QuantumTheory.YangMills.WilsonPinnedIntegral

/-!
# Exact cancellation of untouched product coordinates

Functions depending on disjoint coordinate sets factor under the reference
product probability law. Consequently a positive density factor outside the
variables used by a marked local density cancels from the normalized marked
expectation. This is an exact locality identity at every coupling.
-/
set_option autoImplicit false
noncomputable section
open Finset MeasureTheory
open scoped Topology Classical
open Mettapedia.Combinatorics.PolymerGas
namespace Mettapedia.QuantumTheory.YangMills.WilsonProductLocality
open WilsonBlockElimination

variable {X E : Type*} [Fintype X] [DecidableEq X] [MeasurableSpace E]

export WilsonLocalResponse (DependsOn DependsOff)

namespace DependsOn
export WilsonLocalResponse.DependsOn (mul mono)
end DependsOn

/-- Real-valued product factorization, with dependence conditions referring
to the original coordinates, rather than supplied independence hypotheses. -/
theorem integral_mul_factor (ν₀ : Measure E) [IsProbabilityMeasure ν₀] (base : E)
    (S : Finset X) (F G : (X → E) → ℝ) (hF : Measurable F) (hG : Measurable G)
    (hFS : DependsOn S F) (hGS : DependsOff S G) :
    (∫ ω, F ω * G ω ∂Measure.pi (fun _ : X => ν₀)) =
      (∫ ω, F ω ∂Measure.pi (fun _ : X => ν₀)) *
        ∫ ω, G ω ∂Measure.pi (fun _ : X => ν₀) := by
  have : Nonempty E := ⟨base⟩
  let H : (S → E) → ℂ := fun v => (F (extendConfiguration base S v) : ℂ)
  have hext : Measurable (extendConfiguration base S) := by
    apply measurable_pi_lambda
    intro x
    dsimp [extendConfiguration]
    split_ifs
    · exact measurable_pi_apply _
    · exact measurable_const
  have hH : Measurable H := Complex.measurable_ofReal.comp (hF.comp hext)
  have hrec (ω : X → E) : H (restrictTo S ω) = (F ω : ℂ) := by
    apply congrArg Complex.ofReal
    apply hFS
    intro x hx
    simp [extendConfiguration, restrictTo, hx]
  have h := integral_mul_of_dependsOutside ν₀ S H hH (fun ω => (G ω : ℂ))
    (Complex.measurable_ofReal.comp hG)
    (fun ω ω' he => congrArg Complex.ofReal (hGS ω ω' he))
  simp_rw [hrec, ← Complex.ofReal_mul, integral_complex_ofReal] at h
  rw [← Complex.ofReal_mul] at h
  exact Complex.ofReal_injective h

section Continuous
variable [TopologicalSpace E] [CompactSpace E] [BorelSpace E] [SecondCountableTopology E]

/-- An independent exterior density cancels completely. In applications the
dependence assumptions are proved from plaquette geometry after fixing the
retained boundary coordinates. -/
theorem expectation_cancel_exterior (ν₀ : Measure E) [IsProbabilityMeasure ν₀]
    (base : E) (S : Finset X) (U V F : C(X → E, ℝ))
    (hU : ∀ ω, 0 < U ω) (hV : ∀ ω, 0 < V ω)
    (hUS : DependsOn S U) (hFS : DependsOn S F) (hVS : DependsOff S V) :
    expectation (Measure.pi fun _ : X => ν₀) (U * V) F =
      expectation (Measure.pi fun _ : X => ν₀) U F := by
  have hnum := integral_mul_factor ν₀ base S (fun ω => U ω * F ω) V
    ((U * F).continuous.measurable) V.continuous.measurable (hUS.mul hFS) hVS
  have hden := integral_mul_factor ν₀ base S U V U.continuous.measurable
    V.continuous.measurable hUS hVS
  have hZU := (partition_pos (Measure.pi fun _ : X => ν₀) U hU).ne'
  have hZV := (partition_pos (Measure.pi fun _ : X => ν₀) V hV).ne'
  unfold WilsonBlockElimination.expectation
  simp only [ContinuousMap.mul_apply]
  simp_rw [mul_right_comm (U _) (V _) (F _)]
  rw [hnum, hden]
  field_simp

end Continuous
#print axioms integral_mul_factor
#print axioms expectation_cancel_exterior
end Mettapedia.QuantumTheory.YangMills.WilsonProductLocality
