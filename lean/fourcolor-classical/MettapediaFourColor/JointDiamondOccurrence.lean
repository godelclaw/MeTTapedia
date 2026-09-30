import MettapediaFourColor.JointDiamondIntrinsic
import Mettapedia.GraphTheory.FourColor.OpenTangleDartRecognition
import Mettapedia.GraphTheory.FourColor.SphericalVertexLowerBound

/-!
# Actual darts and an internal hexagon of a joint-diamond occurrence

An occurrence here is an exact isomorphism with an actual vertex shore.
It includes all vertex rotations, internal edges and exposed half-edges.
The internal hexagon survives in the ambient map. Euler counting therefore
forces more than twenty vertices in the minimum-face-five domain.

This interface accepts a proved occurrence; it does not yet construct one
from a list of neighbouring face lengths.
-/

namespace FourColor.JointDiamondPatch.Tangle.Occurrence

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24FaceOrbitIncidence

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E) (side : V → Prop) (root : RetainedDart RS side)
  (R : OpenTangleIsomorphism.Iso piece (ofVertexSide RS side root))

/-- Forget only the internal/boundary coordinate tag, retaining the actual dart. -/
def actual (d : Dart) : RS.D :=
  ((retainedDartEquivInternalSumBoundary RS side).symm (R.darts d)).1

theorem actual_injective : Function.Injective (actual RS side root R) :=
  Subtype.val_injective.comp
    ((retainedDartEquivInternalSumBoundary RS side).symm.injective.comp R.darts.injective)

theorem actual_alpha (i : Fin 34) :
    actual RS side root R (.inl (piece.interiorAlpha i)) =
      RS.alpha (actual RS side root R (.inl i)) := by
  exact congrArg (fun j : InternalDart RS side => j.1.1) (R.alpha i)

theorem actual_rho (d : Dart) :
    actual RS side root R (piece.rho d) = RS.rho (actual RS side root R d) := by
  unfold actual
  change ((retainedDartEquivInternalSumBoundary RS side).symm
    (Equiv.sumCongr R.interior R.boundary (piece.rho d))).1 = _
  rw [R.rotation, ofVertexSide_rho_underlying]
  rfl

theorem actual_vertex (d : Dart) :
    RS.vertOf (actual RS side root R d) = (R.vertex (vertex d)).1 := by
  have hh := congrArg Subtype.val (R.vert d)
  cases d <;> exact hh.symm

/-- One of the two literal internal hexagons. All six darts are internal. -/
def hex : Fin 6 → Fin 34 := ![0, 4, 28, 32, 26, 12]

theorem hex_injective : Function.Injective hex := by decide

theorem hex_step : ∀ i : Fin 6,
    piece.rho (.inl (piece.interiorAlpha (hex i))) = .inl (hex (i + 1)) := by decide

theorem actual_hex_step (i : Fin 6) :
    actual RS side root R (.inl (hex (i + 1))) =
      RS.phi (actual RS side root R (.inl (hex i))) := by
  rw [← hex_step, actual_rho, actual_alpha]
  rfl

include R in
/-- The internal orbit contributes six distinct genuine ambient darts. -/
theorem long_face : ∃ face : OrbitFace RS, 5 < (orbitFaceDarts RS face).card := by
  let f := dartOrbitFace RS (actual RS side root R (.inl (hex 0)))
  have step (i : Fin 6) :
      dartOrbitFace RS (actual RS side root R (.inl (hex (i + 1)))) =
        dartOrbitFace RS (actual RS side root R (.inl (hex i))) := by
    rw [actual_hex_step, dartOrbitFace_phi_eq]
  have same (i : Fin 6) : dartOrbitFace RS (actual RS side root R (.inl (hex i))) = f := by
    fin_cases i
    · rfl
    · exact step 0
    · exact (step 1).trans (step 0)
    · exact (step 2).trans ((step 1).trans (step 0))
    · exact (step 3).trans ((step 2).trans ((step 1).trans (step 0)))
    · exact (step 4).trans ((step 3).trans ((step 2).trans ((step 1).trans (step 0))))
  let points : Fin 6 → {d // d ∈ orbitFaceDarts RS f} := fun i =>
    ⟨actual RS side root R (.inl (hex i)), (mem_orbitFaceDarts_iff RS f _).mpr (same i)⟩
  have hinj : Function.Injective points := by
    intro i j hh
    have he : actual RS side root R (.inl (hex i)) =
        actual RS side root R (.inl (hex j)) :=
      congrArg (fun z : {d // d ∈ orbitFaceDarts RS f} => z.1) hh
    exact hex_injective (Sum.inl.inj
      (actual_injective RS side root R he))
  have hc := Fintype.card_le_of_injective points hinj
  simp only [Fintype.card_fin, Fintype.card_coe] at hc
  exact ⟨f, by omega⟩

include R in
/-- The space needed for the eight-port connectivity theorem follows
from this occurrence's own hexagon, rather than a separate size premise. -/
theorem twenty_lt_vertices (hsphere : OrbitSphericalCubicMapData RS)
    (hminimum : ∀ face : OrbitFace RS, 5 ≤ (orbitFaceBoundary RS face).card) :
    20 < Fintype.card V :=
  SphericalVertexLowerBound.twenty_lt_card_vertices_of_long_face RS hsphere hminimum
    (long_face RS side root R)

end
end FourColor.JointDiamondPatch.Tangle.Occurrence
