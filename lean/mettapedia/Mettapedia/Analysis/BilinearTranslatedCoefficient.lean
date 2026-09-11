import Mettapedia.Analysis.BilinearTranslatedKernel
import Mathlib.Topology.ContinuousMap.Compact

/-!
# Integrable translated densities with continuous two-point coefficients

Compactness is used only to establish integrability. The coefficient stays
inside the integral, so the resulting expression retains its spatial costs.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia.Analysis.BilinearTranslatedCoefficient

open MeasureTheory
open BilinearTranslatedKernel

variable {A X : Type*} [MeasurableSpace A] [MeasurableSpace X]
variable [TopologicalSpace X] [BorelSpace X] [SecondCountableTopology X] [CompactSpace X]
variable [AddCommGroup X] [MeasurableAdd₂ X] [MeasurableNeg X]
variable {μ : Measure A} {ν : Measure X} [SFinite μ] [SFinite ν] [ν.IsAddRightInvariant]

theorem integrable_weighted_translate_mul_continuous (w : A → ℝ) (f : X → ℝ)
    (hw : Integrable w μ) (hf : Integrable f ν)
    (a b : A → X) (ha : Measurable a) (hb : Measurable b) (c : C(X × X, ℝ)) :
    Integrable (fun p : A × X ↦ w p.1 * f (p.2 - a p.1) *
      c (p.2 - a p.1, p.2 - b p.1)) (μ.prod ν) := by
  apply (integrable_weighted_translate w f hw hf a ha).mul_bdd
    (c.continuous.measurable.comp ((measurable_snd.sub (ha.comp measurable_fst)).prodMk
      (measurable_snd.sub (hb.comp measurable_fst)))).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun p ↦ c.norm_coe_le_norm (p.2 - a p.1, p.2 - b p.1))

end Mettapedia.Analysis.BilinearTranslatedCoefficient
