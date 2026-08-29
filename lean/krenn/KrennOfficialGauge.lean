import KrennOfficialBridge
import DimensionMonotonicity

/-!
The semantic gauge action on the official `N = 6, D = 3` equations.

Multiplying an edge channel `(u,i)-(v,j)` by the two endpoint factors
`g u i * g v j` multiplies every perfect-matching term for a colouring `ι`
by the same product over the six vertices. Mixed-colour amplitudes remain
zero. If the product of the six factors is one in each constant colour, the
three monochromatic normalizations remain one as well.
-/

namespace Krenn.OfficialGauge

open MonochromaticQuantumGraph
open Krenn.OfficialBridge
open scoped BigOperators

def gauge (g : Fin 6 → Fin 3 → ℂ) (W : WeightsN 6 3 ℂ) :
    WeightsN 6 3 ℂ := fun edge =>
  g edge.u edge.i * g edge.v edge.j * W edge

def colouringFactor (g : Fin 6 → Fin 3 → ℂ) (ι : Fin 6 → Fin 3) : ℂ :=
  ∏ v, g v (ι v)

@[simp] theorem w_gauge (g : Fin 6 → Fin 3 → ℂ)
    (W : WeightsN 6 3 ℂ) (ι : Fin 6 → Fin 3) (u v : Fin 6) :
    w (gauge g W) ι u v = g u (ι u) * g v (ι v) * w W ι u v := rfl

theorem pm15_gauge (g : Fin 6 → Fin 3 → ℂ)
    (W : WeightsN 6 3 ℂ) (ι : Fin 6 → Fin 3) :
    pm15 (gauge g W) ι = colouringFactor g ι * pm15 W ι := by
  simp [pm15, w, gauge, colouringFactor, Fin.prod_univ_succ,
    MonochromaticQuantumGraph.mkEdge]
  ring

theorem pmSumN_gauge (g : Fin 6 → Fin 3 → ℂ)
    (W : WeightsN 6 3 ℂ) (ι : Fin 6 → Fin 3) :
    pmSumN 6 3 (gauge g W) ι = colouringFactor g ι * pmSumN 6 3 W ι := by
  rw [official_pmSum_eq_pm15, pm15_gauge, official_pmSum_eq_pm15]

theorem colouringFactor_constant (g : Fin 6 → Fin 3 → ℂ) (c : Fin 3) :
    colouringFactor g (fun _ => c) = ∏ v, g v c := rfl

/-- A product-one vertex-colour gauge preserves the official equation system. -/
theorem eqSystemN_gauge
    (g : Fin 6 → Fin 3 → ℂ) (W : WeightsN 6 3 ℂ)
    (productOne : ∀ c : Fin 3, ∏ v, g v c = 1)
    (hW : EqSystemN 6 3 W) : EqSystemN 6 3 (gauge g W) := by
  intro ι
  rw [pmSumN_gauge, hW]
  by_cases equal : allEqual ι
  · rw [if_pos equal]
    obtain ⟨c, rfl⟩ := (allEqual_iff_constant ι).mp equal
    simp [colouringFactor_constant, productOne]
  · rw [if_neg equal]
    ring

theorem gauge_entry_ne_zero_iff
    (g : Fin 6 → Fin 3 → ℂ) (W : WeightsN 6 3 ℂ)
    (nonzero : ∀ v c, g v c ≠ 0) (edge : EdgeN 6 3) :
    gauge g W edge ≠ 0 ↔ W edge ≠ 0 := by
  simp [gauge, nonzero]

theorem gauge_entry_eq_zero_iff
    (g : Fin 6 → Fin 3 → ℂ) (W : WeightsN 6 3 ℂ)
    (nonzero : ∀ v c, g v c ≠ 0) (edge : EdgeN 6 3) :
    gauge g W edge = 0 ↔ W edge = 0 := by
  simpa only [not_iff_not] using
    (gauge_entry_ne_zero_iff g W nonzero edge)

def relabelColours (τ : Equiv.Perm (Fin 3)) (W : WeightsN 6 3 ℂ) :
    WeightsN 6 3 ℂ := fun edge =>
  W { edge with i := τ edge.i, j := τ edge.j }

theorem pm15_relabelColours (τ : Equiv.Perm (Fin 3))
    (W : WeightsN 6 3 ℂ) (ι : Fin 6 → Fin 3) :
    pm15 (relabelColours τ W) ι = pm15 W (fun v => τ (ι v)) := by
  simp [pm15, w, relabelColours, MonochromaticQuantumGraph.mkEdge]

theorem pmSumN_relabelColours (τ : Equiv.Perm (Fin 3))
    (W : WeightsN 6 3 ℂ) (ι : Fin 6 → Fin 3) :
    pmSumN 6 3 (relabelColours τ W) ι =
      pmSumN 6 3 W (fun v => τ (ι v)) := by
  rw [official_pmSum_eq_pm15, pm15_relabelColours, official_pmSum_eq_pm15]

theorem eqSystemN_relabelColours (τ : Equiv.Perm (Fin 3))
    (W : WeightsN 6 3 ℂ) (hW : EqSystemN 6 3 W) :
    EqSystemN 6 3 (relabelColours τ W) := by
  intro ι
  rw [pmSumN_relabelColours, hW]
  exact if_congr
    (MonochromaticQuantumGraph.allEqual_comp_iff
      (fun c => τ c) τ.injective ι) rfl rfl

#print axioms Krenn.OfficialGauge.eqSystemN_gauge
#print axioms Krenn.OfficialGauge.gauge_entry_ne_zero_iff
#print axioms Krenn.OfficialGauge.eqSystemN_relabelColours

end Krenn.OfficialGauge
