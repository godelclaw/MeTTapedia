import MettapediaFourColor.SourceTaitInverse

/-!
# Contract colourings from conserved edge fields

Integrating the complete Klein-group field preserves its values on every
edge. Its exact zero set becomes the contracted edge set; all other edges
remain properly coloured. No existence theorem for four-colourings is used.
-/

namespace FourColor.ConservedContract

open Mettapedia.GraphTheory.FourColor
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24TwoEdgeCutMinimality GoertzelV24BridgelessFaceTwoSided
open RotationConservedFacePotential SourceConstruction

noncomputable section

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u, u, u} V E)

/-- The entire edge field, including its zero set, is reconstructed. -/
theorem of_conserved (geometry : BridgelessSphericalCubicMapData RS)
    (field : E → Mettapedia.GraphTheory.FourColor.Color)
    (conserved : Conserved RS field) (cc : List RS.D)
    (zeros : ∀ d, field (RS.edgeOf d) = 0 ↔ d ∈ (sourceMap RS).insertE cc) :
    ∃ k : RS.D → Color, (sourceMap RS).CcColoring cc k ∧
      ∀ d, palette (k d + k (RS.alpha d)) = field (RS.edgeOf d) := by
  obtain ⟨p, hp⟩ := exists_facePotential RS
    (BridgelessSphericalCubicMapData.orbitFacesTwoSided RS geometry)
    (orbitFaceInteriorDual_connected RS geometry.spherical.cubic
      geometry.primalConnected geometry.vertexRotationCyclic)
    geometry.primalConnected geometry.spherical.euler field conserved
  let k : RS.D → Color := fun d => PhysicalKempeBoundary.palette.symm (p (dartOrbitFace RS d))
  have diff (d : RS.D) : palette (k d + k (RS.alpha d)) = field (RS.edgeOf d) := by
    change PhysicalKempeBoundary.paletteAdd (k d + k (RS.alpha d)) = _
    rw [map_add]
    simpa only [k, PhysicalKempeBoundary.paletteAdd, AddEquiv.coe_mk,
      Equiv.apply_symm_apply] using hp d
  refine ⟨k, ⟨?_, ?_⟩, diff⟩
  · intro d
    change k (RS.alpha d) = k d ↔ _
    rw [← zeros]
    constructor
    · intro eq
      rw [← diff, eq, Color.add_self, palette_zero]
    · intro zero
      have h : k d + k (RS.alpha d) = 0 := palette.injective (by
        rw [diff, zero, palette_zero])
      exact (Color.add_eq_zero_iff.mp h).symm
  · intro d
    change PhysicalKempeBoundary.palette.symm (p (dartOrbitFace RS (RS.phi d))) = _
    rw [dartOrbitFace_phi_eq]

/-- A singleton contract marks both darts of exactly one physical edge. -/
theorem singleton_support (d z : RS.D) :
    z ∈ (sourceMap RS).insertE [d] ↔ RS.edgeOf z = RS.edgeOf d := by
  change z ∈ [d, RS.alpha d] ↔ _
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (rfl | rfl)
    · rfl
    · exact RS.edge_alpha d
  · intro eq
    exact RS.edge_fiber_two_cases rfl eq

/-- The initial contract colouring needed by a singleton repair follows
from one conserved field with exactly that zero edge. -/
theorem singleton (geometry : BridgelessSphericalCubicMapData RS) (d : RS.D)
    (field : E → Mettapedia.GraphTheory.FourColor.Color)
    (conserved : Conserved RS field)
    (zeros : ∀ e, field e = 0 ↔ e = RS.edgeOf d) :
    ∃ k : RS.D → Color, (sourceMap RS).CcColoring [d] k ∧
      ∀ z, palette (k z + k (RS.alpha z)) = field (RS.edgeOf z) :=
  of_conserved RS geometry field conserved [d]
    (fun z => (zeros _).trans (singleton_support RS d z).symm)

end
end FourColor.ConservedContract
