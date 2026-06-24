import Mettapedia.FluidDynamics.NavierStokes.NavierStokesEnergyBasic

/-!
# Navier-Stokes Energy: Pressure-Schwartz Smooth Pressure Constructors

Semantic layer split from `NavierStokesEnergyPressureSchwartz`.
-/


set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace FluidDynamics
namespace NavierStokes

open MeasureTheory
open scoped ContDiff Laplacian RealInnerProductSpace LineDeriv SchwartzMap

/-- A smooth time coefficient multiplying a Schwartz spatial profile gives a
smooth concrete space-time pressure field. -/
theorem smoothSpaceTimePressure_scalar_smul_schwartzPressure
    {ρ : NSTime → ℝ} (hρ : ContDiff ℝ ∞ ρ) (q : 𝓢(NSSpace, ℝ)) :
    smoothSpaceTimePressure (fun t : NSTime => fun x : NSSpace => ρ t * q x) := by
  have hρTime : ContDiff ℝ ∞ (fun tx : NSSpacetime => ρ tx.1) :=
    hρ.comp (contDiff_fst : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.1)
  have hqSpace : ContDiff ℝ ∞ (fun tx : NSSpacetime => q tx.2) :=
    q.smooth'.comp (contDiff_snd : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.2)
  rw [smoothSpaceTimePressure]
  exact contDiff_congr_global (hρTime.mul hqSpace)
    (by intro tx; rfl)

/-- A smooth time-dependent affine spatial pressure profile
`p(t,x) = ⟪c(t), x⟫ + π(t)` is a smooth concrete space-time pressure field. -/
theorem smoothSpaceTimePressure_affinePressure
    {c : NSTime → NSSpace} {π : NSTime → ℝ}
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) :
    smoothSpaceTimePressure (fun t : NSTime => fun x : NSSpace => ⟪c t, x⟫ + π t) := by
  have hcTime : ContDiff ℝ ∞ (fun tx : NSSpacetime => c tx.1) :=
    hc.comp (contDiff_fst : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.1)
  have hxSpace : ContDiff ℝ ∞ (fun tx : NSSpacetime => tx.2) :=
    contDiff_snd
  have hCoord (i : Fin 3) :
      ContDiff ℝ ∞ (fun tx : NSSpacetime => (c tx.1) i * tx.2 i) :=
    ((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).contDiff.comp hcTime).mul
      ((EuclideanSpace.proj i : NSSpace →L[ℝ] ℝ).contDiff.comp hxSpace)
  have hInnerSum :
      ContDiff ℝ ∞ (fun tx : NSSpacetime => ∑ i : Fin 3, (c tx.1) i * tx.2 i) := by
    simpa using
      (ContDiff.sum (s := (Finset.univ : Finset (Fin 3)))
        (fun i _ => hCoord i))
  have hπTime : ContDiff ℝ ∞ (fun tx : NSSpacetime => π tx.1) :=
    hπ.comp (contDiff_fst : ContDiff ℝ ∞ fun tx : NSSpacetime => tx.1)
  rw [smoothSpaceTimePressure]
  exact contDiff_congr_global (hInnerSum.add hπTime)
    (by
      intro tx
      simp [spaceTimePressureMap, EuclideanSpace.inner_eq_star_dotProduct,
        dotProduct, mul_comm])

/-- Smooth affine pressures remain smooth after adding a smooth time
coefficient times a Schwartz spatial profile. -/
theorem smoothSpaceTimePressure_affine_add_scalar_smul_schwartzPressure
    {c : NSTime → NSSpace} {π ρ : NSTime → ℝ}
    (hc : ContDiff ℝ ∞ c) (hπ : ContDiff ℝ ∞ π) (hρ : ContDiff ℝ ∞ ρ)
    (q : 𝓢(NSSpace, ℝ)) :
    smoothSpaceTimePressure
      ((fun t : NSTime => fun x : NSSpace => ⟪c t, x⟫ + π t) +
        fun t : NSTime => fun x : NSSpace => ρ t * q x) := by
  exact
    smoothSpaceTimePressure_add
      (smoothSpaceTimePressure_affinePressure hc hπ)
      (smoothSpaceTimePressure_scalar_smul_schwartzPressure hρ q)

end NavierStokes
end FluidDynamics
end Mettapedia
