import Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism
import Mettapedia.GraphTheory.FourColor.VertexSideExactReassembly

/-!
# Reassemble an exact open-piece occurrence in its actual source

An occurrence is an isomorphism with a literal vertex shore. Its boundary
coordinates determine the complementary exterior and the actual seam.
Sewing the model piece back gives an exact relabelling of the source,
including its rotations, edge pairs and vertices. Colouring transport
retains every literal edge value. No exterior connectivity is required.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleVertexOccurrence

open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RotationCutDartDecomposition GoertzelV24VertexSideReassembly
open GoertzelV24ComplementaryShoreBoundaryOrder GoertzelV24DeletedRegionRotationSplice
open GoertzelV24TwoEdgeCutMinimality

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {V E W I B : Type*}
  [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  [Fintype W] [DecidableEq W] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B]
  (RS : RotationSystem V E) (deleted : Finset V)
  (inside : RetainedDart RS (deletedSideKeep deleted))
  (piece : OpenTangleData W I B)
  (occurrence : OpenTangleIsomorphism.Iso piece
    (ofVertexSide RS (deletedSideKeep deleted) inside))

/-- Follow each model port across its original ambient edge. -/
def ports : B ≃ BoundaryDart RS (deletedRegionKeep deleted) :=
  occurrence.boundary.trans (complementBoundaryAlphaEquiv RS deleted).symm

variable (port : B)

/-- A chosen exposed port supplies the exterior's mark. It imposes no
condition on the number of exterior connected components. -/
abbrev outside := ofVertexSide RS (deletedRegionKeep deleted)
  ((ports RS deleted inside piece occurrence port).1)

abbrev assembled := (outside RS deleted inside piece occurrence port).composeRotationSystem
  piece (ports RS deleted inside piece occurrence).symm

theorem matching : (ports RS deleted inside piece occurrence).symm.trans
    occurrence.boundary = complementBoundaryAlphaEquiv RS deleted := by
  ext b
  simp [ports]

/-- The model vertex labels and literal exterior labels partition the source. -/
def vertices : ({v : V // deletedRegionKeep deleted v} ⊕ W) ≃ V :=
  (Equiv.sumCongr (Equiv.refl _) occurrence.vertex).trans (complementaryVertexEquiv deleted)

/-- Compose the existing exact sewing and complementary-shore reassembly. -/
def darts : (assembled RS deleted inside piece occurrence port).D ≃ RS.D :=
  (occurrence.sewnDarts (outside RS deleted inside piece occurrence port)
    (ports RS deleted inside piece occurrence).symm).trans
      (complementaryDartEquiv RS deleted
        ((ports RS deleted inside piece occurrence port).1) inside)

theorem darts_alpha (d : (assembled RS deleted inside piece occurrence port).D) :
    darts RS deleted inside piece occurrence port
      ((assembled RS deleted inside piece occurrence port).alpha d) =
      RS.alpha (darts RS deleted inside piece occurrence port d) := by
  rcases d with (i | j) | (b | c)
  · rfl
  · exact congrArg (fun x => x.1.1) (occurrence.alpha j)
  · have hp : occurrence.boundary ((ports RS deleted inside piece occurrence).symm b) =
        complementBoundaryAlphaEquiv RS deleted b :=
      congrArg (fun e => e b) (matching RS deleted inside piece occurrence)
    change (occurrence.boundary ((ports RS deleted inside piece occurrence).symm b)).1.1 = _
    rw [hp]
    exact complementBoundaryAlphaEquiv_val RS deleted b
  · exact complementBoundaryAlphaEquiv_symm_val RS deleted (occurrence.boundary c)

theorem darts_vertex (d : (assembled RS deleted inside piece occurrence port).D) :
    vertices RS deleted inside piece occurrence
      ((assembled RS deleted inside piece occurrence port).vertOf d) =
      RS.vertOf (darts RS deleted inside piece occurrence port d) := by
  unfold vertices darts
  simp only [Equiv.trans_apply]
  rw [occurrence.sewn_vert]
  exact complementaryDartEquiv_vertOf RS deleted _ inside _

theorem darts_rotation (d : (assembled RS deleted inside piece occurrence port).D) :
    darts RS deleted inside piece occurrence port
      ((assembled RS deleted inside piece occurrence port).rho d) =
      RS.rho (darts RS deleted inside piece occurrence port d) := by
  unfold darts
  simp only [Equiv.trans_apply]
  rw [occurrence.sewn_rotation]
  exact VertexSideExactReassembly.rotation RS deleted _ inside _

/-- All geometric fields follow from the actual source through the same
representation change. No field of the assembled map is assumed. -/
theorem assembled_class (h : BridgelessSphericalCubicMapData RS) :
    BridgelessSphericalCubicMapData (assembled RS deleted inside piece occurrence port) := by
  let d := darts RS deleted inside piece occurrence port
  let v := vertices RS deleted inside piece occurrence
  apply RotationSystemExactTransport.mapClass RS _ d.symm v.symm _ _ _ h
  · intro x
    apply d.injective
    rw [Equiv.apply_symm_apply, darts_alpha, Equiv.apply_symm_apply]
  · intro x
    apply v.injective
    rw [Equiv.apply_symm_apply, darts_vertex, Equiv.apply_symm_apply]
  · intro x
    apply d.injective
    rw [Equiv.apply_symm_apply, darts_rotation, Equiv.apply_symm_apply]

/-- Every supplied assembled colouring transports with all edge values fixed. -/
theorem reassemble_colouring
    (c : (assembled RS deleted inside piece occurrence port).EdgeColoring Color)
    (hc : (assembled RS deleted inside piece occurrence port).IsTaitEdgeColoring c) :
    ∃ result : RS.EdgeColoring Color, RS.IsTaitEdgeColoring result ∧
      ∀ d, result (RS.edgeOf (darts RS deleted inside piece occurrence port d)) =
        c ((assembled RS deleted inside piece occurrence port).edgeOf d) :=
  exists_taitColoring_of_dartEquiv _ _ (darts RS deleted inside piece occurrence port)
    (vertices RS deleted inside piece occurrence) (darts_alpha RS deleted inside piece occurrence port)
    (darts_vertex RS deleted inside piece occurrence port) c hc

theorem colorable_iff :
    RotationSystemTaitColorable (assembled RS deleted inside piece occurrence port) ↔
      RotationSystemTaitColorable RS :=
  rotationSystemTaitColorable_iff_of_dartEquiv _ _
    (darts RS deleted inside piece occurrence port) (vertices RS deleted inside piece occurrence)
    (darts_alpha RS deleted inside piece occurrence port)
    (darts_vertex RS deleted inside piece occurrence port)

include occurrence in
/-- Count the complete retained shore and the entire model piece. -/
theorem vertex_count : Fintype.card {v : V // deletedRegionKeep deleted v} +
    Fintype.card W = Fintype.card V := by
  simpa only [Fintype.card_sum] using
    Fintype.card_congr (vertices RS deleted inside piece occurrence)

end
end Mettapedia.GraphTheory.FourColor.OpenTangleVertexOccurrence
