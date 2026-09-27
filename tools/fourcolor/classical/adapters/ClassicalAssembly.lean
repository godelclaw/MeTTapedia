import FourColor.Pilot.EmbeddedReconstruction
import FourColor.Main

/-!
# Conditional classical assembly through colouring reconstruction

The classical minimal-counterexample argument consumes the explicit colouring
reconstruction, then the reference's unchanged discharging soundness. This
factors the Gonthier/Werner argument as formalized by Chris Emery; it introduces
no new coverage principle. The 633 reducibility checks and seven presentation
results remain explicit hypotheses.
-/

namespace FourColor.ClassicalAssembly

open Hypermap

/-- The explicit reconstructed colouring contradicts minimality. -/
theorem no_embedded_reduction {Dc Dm : Type} [Finite Dc] [Finite Dm]
    {Gc : Hypermap Dc} {Gm : Hypermap Dm} {rc cc : List Dc} {h : Dc → Dm}
    (hemb : Gc.Embeddable rc) (hmin : Gm.MinimalCounterExample)
    (hpre : Preembedding Gc Gm h {z | Gc.Kernel rc z})
    (hcred : Gc.CReducible rc cc) : False := by
  let R : EmbeddedReduction Gc Gm rc cc h :=
    ⟨hemb, hmin.planar, hmin.plain, hmin.bridgeless, hmin.connected,
      hmin.cubic, hmin.birkhoffRings, hmin.pentagonal, hpre, hcred⟩
  obtain ⟨k, hk⟩ := hmin.contract_coloring R.birkhoff
    (embed_valid_contract R.embeddable R.planar R.plain R.bridgeless R.connected
      R.cubic R.birkhoff R.pentagonal R.preembedding R.injection R.reducible.base)
  let rebuilt := R.reconstruct ⟨k, hk⟩
  exact hmin.noncolorable ⟨rebuilt.val, rebuilt.property⟩

/-- Every fitted catalogue entry invokes the same witness reconstruction. -/
theorem no_fitted_configuration (hred : Reducibility)
    {D : Type} [Finite D] {G : Hypermap D}
    (hmin : G.MinimalCounterExample) (x : D) : ¬ G.Fit x theQuizTree := by
  intro hfit
  obtain ⟨cf, hcf, hR, hex⟩ := fit_theQuizTree hmin.plain hmin.cubic x hfit
  obtain ⟨x₀, hvq⟩ := valid_cfquiz hR
  have hemb := embeddable_cfquiz hR
  have hpc : (cfmap cf).map.Plain := hemb.base.base.base.base.plain
  have hqc : (cfmap cf).map.Quasicubic (cfring cf) :=
    hemb.base.base.base.base.quasicubic
  have hcr := cfReducible_of_mem hred hcf
  rcases hex with ⟨y, hy⟩ | ⟨y, hy⟩
  · exact no_embedded_reduction hemb hmin
      (quiz_preembedding hmin.plain hmin.cubic hpc hqc hvq hy) hcr
  · exact no_embedded_reduction hemb hmin.mirror
      (quiz_preembedding ((plain_mirror G).mpr hmin.plain)
        ((cubic_mirror G).mpr hmin.cubic) hpc hqc hvq hy) hcr

theorem redpart_sound (hred : Reducibility) : RedpartSound theRedpart := by
  intro D _ G hmin y q hq
  exact no_fit_redpart hmin.plainCubicPentagonal
    (no_fitted_configuration hred hmin) hq y

/-- The computational obligations exclude a minimal counterexample through
the same explicit colouring reconstruction. -/
theorem no_minimalCounterExample_of_checks (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    (e9 : ExcludedArity (RedpartSound theRedpart) 9)
    (e10 : ExcludedArity (RedpartSound theRedpart) 10)
    (e11 : ExcludedArity (RedpartSound theRedpart) 11)
    {D : Type} [Finite D] (G : Hypermap D) : ¬ G.MinimalCounterExample :=
  not_minimalCounterExample (G := G) (redpart_sound hred) e5 e6 e7 e8 e9 e10 e11

/-- The reference's real-plane theorem, conditional on all the original
computational obligations, with reducibility consumed through reconstruction. -/
theorem fourColorTheorem_of_checks (hred : Reducibility)
    (e5 : ExcludedArity (RedpartSound theRedpart) 5)
    (e6 : ExcludedArity (RedpartSound theRedpart) 6)
    (e7 : ExcludedArity (RedpartSound theRedpart) 7)
    (e8 : ExcludedArity (RedpartSound theRedpart) 8)
    (e9 : ExcludedArity (RedpartSound theRedpart) 9)
    (e10 : ExcludedArity (RedpartSound theRedpart) 10)
    (e11 : ExcludedArity (RedpartSound theRedpart) 11) : FourColorTheorem :=
  fourColorTheorem_of_unavoidability
    (no_minimalCounterExample_of_checks hred e5 e6 e7 e8 e9 e10 e11)

#print axioms no_embedded_reduction
#print axioms fourColorTheorem_of_checks

end FourColor.ClassicalAssembly
