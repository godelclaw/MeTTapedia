import MettapediaFourColor.SourceTait
import MettapediaFourColor.PhysicalKempeBoundary
import Mettapedia.GraphTheory.FourColor.RotationConservedFacePotential

/-!
# Exact inverse transport from physical edges to reference face colours

A given Tait colouring of a spherical cubic map supplies a reference face
colouring with exactly the same edge differences. Composing with the existing
face-to-edge interpretation returns the supplied colouring on every edge.
This is a representation bridge, independent of a Four Colour existence
theorem or configuration certificates.
-/

namespace FourColor.SourceConstruction

open Mettapedia.GraphTheory.FourColor
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24TwoEdgeCutMinimality GoertzelV24BridgelessFaceTwoSided
open GoertzelV24OrbitFaceTwoSided
open RotationConservedFacePotential

noncomputable section

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E] {RS : RotationSystem.{u,u,u} V E}

/-- Reference mirroring changes the orientation convention while retaining
the same face-colouring witness. -/
theorem reference_mirror_colouring_iff (k : RS.D → Color) :
    (sourceMap RS).mirror.Coloring k ↔ (sourceMap RS).Coloring k := by
  constructor
  · exact fun h => h.of_mirror
  · intro h
    have h' : (sourceMap RS).mirror.mirror.Coloring k := by simpa using h
    exact h'.of_mirror

/-- In the mirrored reference convention, the node follows the physical
rotation. Its adjacent face colours recover the original physical edge. -/
theorem mirror_node_difference {k : RS.D → Color}
    (hk : (sourceMap RS).mirror.Coloring k) (d : RS.D) :
    k d + k ((sourceMap RS).mirror.node d) = k d + k (RS.alpha d) := by
  change k d + k ((RS.rho⁻¹)⁻¹ d) = _
  rw [inv_inv, faceColor_rho hk.of_mirror]

/-- Conservation suffices even at a boundary vertex of degree greater than
three. Nonzero edge values give the reference proper-colouring condition. -/
theorem reference_colouring_of_conserved
    (ht : OrbitFacesTwoSided RS)
    (hd : (interiorDualGraph (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))).Connected)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (heuler : (Fintype.card V : Int) - Fintype.card E +
      Fintype.card (OrbitFace RS) = 2)
    (c : E → Mettapedia.GraphTheory.FourColor.Color)
    (hconserved : Conserved RS c) (hc : ∀ e, c e ≠ 0) :
    ∃ k : RS.D → Color, (sourceMap RS).Coloring k ∧
      ∀ d, palette (k d + k (RS.alpha d)) = c (RS.edgeOf d) := by
  obtain ⟨p, hp⟩ := exists_facePotential RS ht hd hconnected heuler c hconserved
  let k : RS.D → Color := fun d => PhysicalKempeBoundary.palette.symm (p (dartOrbitFace RS d))
  have hdiff (d : RS.D) : palette (k d + k (RS.alpha d)) = c (RS.edgeOf d) := by
    change PhysicalKempeBoundary.paletteAdd (k d + k (RS.alpha d)) = _
    rw [map_add]
    simpa only [k, PhysicalKempeBoundary.paletteAdd, AddEquiv.coe_mk,
      Equiv.apply_symm_apply] using hp d
  refine ⟨k, ⟨?_, ?_⟩, hdiff⟩
  · intro d he
    apply hc (RS.edgeOf d)
    rw [← hdiff d]
    change k (RS.alpha d) = k d at he
    rw [he, Color.add_self, palette_zero]
  · intro d
    change PhysicalKempeBoundary.palette.symm (p (dartOrbitFace RS (RS.phi d))) = _
    rw [dartOrbitFace_phi_eq]

/-- The face potential reconstructs the complete supplied physical edge field. -/
theorem reference_colouring_of_tait
    (hclass : BridgelessSphericalCubicMapData RS)
    (c : RS.EdgeColoring Mettapedia.GraphTheory.FourColor.Color)
    (hc : RS.IsTaitEdgeColoring c) :
    ∃ k : RS.D → Color, (sourceMap RS).Coloring k ∧
      ∀ d, palette (k d + k (RS.alpha d)) = c (RS.edgeOf d) :=
  reference_colouring_of_conserved
    (GoertzelV24BridgelessFaceTwoSided.BridgelessSphericalCubicMapData.orbitFacesTwoSided RS hclass)
    (orbitFaceInteriorDual_connected RS hclass.spherical.cubic
      hclass.primalConnected hclass.vertexRotationCyclic)
    hclass.primalConnected hclass.spherical.euler c
    (conserved_of_tait RS hclass.spherical.cubic c hc) hc

/-- The transport commutes with the existing face-to-edge interpretation:
every edge colour, and hence every joint boundary observation, is fixed. -/
theorem tait_round_trip
    (hclass : BridgelessSphericalCubicMapData RS)
    (c : RS.EdgeColoring Mettapedia.GraphTheory.FourColor.Color)
    (hc : RS.IsTaitEdgeColoring c) :
    ∃ k : RS.D → Color, ∃ hk : (sourceMap RS).Coloring k,
      ∀ e, taitColoring hclass.spherical.cubic hclass.vertexRotationCyclic hk e = c e := by
  obtain ⟨k, hk, he⟩ := reference_colouring_of_tait hclass c hc
  refine ⟨k, hk, ?_⟩
  intro e
  obtain ⟨d, hd⟩ := RS.dartsOn_nonempty e
  have hd' := RS.mem_dartsOn.mp hd
  rw [← hd', taitColoring_dart]
  exact he d

end
end FourColor.SourceConstruction
