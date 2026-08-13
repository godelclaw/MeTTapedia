import Mettapedia.GraphTheory.FourColor.GoertzelV24SourceTrailAlignment
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedAnnularExcess

/-!
# Embedded source trails and the geometric L9 seam

`SourceTrail` records the graph-side containers needed for the move relation,
but deliberately does not invent a cyclic order of every graph dart.  This
module states the additional semantic data supplied by an embedded source
formation: the two named facial holes are exactly the container boundaries,
and the frozen outward leaves occur twice on the outer facial walk.

Those facts imply the hole-perimeter baseline required by the framed annular
Excess Identity.  Constructing this embedding data from the manuscript's
Jordan-curve formation semantics remains a separate theorem; it is not
replaced by an arithmetic premise here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedTrail

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

namespace SourceTrail

/-- Rotation-level realization of the source trail's two container curves and
frozen outward leaf interface.  The edge-boundary equations prevent the two
distinguished faces from being arbitrary holes with convenient sizes. -/
structure AnnularEmbedding (source : SourceTrail G) where
  cellulation : FramedAnnularCellulation G
  /-- The distinguished rotation root is chosen on the source's named outer
  hole.  Source crosscuts select their retained component from this dart, so
  the root cannot be an arbitrary interior face representative. -/
  outer_dart_on_outerHole :
    dartOrbitFace cellulation.rotation.toRotationSystem
      cellulation.rotation.toRotationSystem.outer = cellulation.outerHole
  innerHole_boundary :
    orbitFaceBoundary cellulation.rotation.toRotationSystem
        cellulation.innerHole =
      source.innerContainerEdges
  outerHole_boundary :
    orbitFaceBoundary cellulation.rotation.toRotationSystem
        cellulation.outerHole =
      source.outerContainerEdges ∪ source.frozenInterfaceEdges
  stubToFrozenEdge :
    source.frozenInterfaceStubVertices ≃ source.frozenInterfaceEdges
  stubToFrozenEdge_incident :
    ∀ stub : source.frozenInterfaceStubVertices,
      (stubToFrozenEdge stub : G.edgeSet) ∈ incidentEdgeFinset G stub.1
  frozenEdgeDarts_on_outerHole :
    ∀ edge : source.frozenInterfaceEdges,
      ∀ dart ∈ cellulation.rotation.toRotationSystem.dartsOn edge.1,
        dartOrbitFace cellulation.rotation.toRotationSystem dart =
          cellulation.outerHole

namespace AnnularEmbedding

/-- A well-formed framed source trail is not a closed cubic graph: its two
missing-edge endpoints have degree two.  Consequently, a theorem requiring
global rotation-system cubicity cannot be instantiated directly on this
open source carrier.  This is a carrier guard for the L8--L10 assembly; it
does not deny the separately proved local cubicity of annular-interior faces.
-/
theorem rotationSystem_not_isCubic_of_wellFormed
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding) :
    ¬ embedded.cellulation.rotation.toRotationSystem.IsCubic := by
  intro hcubic
  have hregular : G.IsRegularOfDegree 3 :=
    embedded.cellulation.rotation.toRotationSystem_isCubic_iff.mp hcubic
  have htwo : G.degree (source.defectVertex 0) = 2 := by
    rw [← GoertzelV24FramedBoundaryCounts.incidentEdgeFinset_card_eq_degree
      (G := G)]
    exact hsource.defect_degree_two 0
  have hthree : G.degree (source.defectVertex 0) = 3 :=
    hregular (source.defectVertex 0)
  omega

/-- A dart over one of the source's frozen interface edges. -/
abbrev FrozenEdgeDart {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :=
  Σ edge : source.frozenInterfaceEdges,
    {dart // dart ∈
      embedded.cellulation.rotation.toRotationSystem.dartsOn edge.1}

/-- A dart together with the distinguished hole face containing it. -/
abbrev HoleDart {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :=
  Σ face : embedded.cellulation.holeFaces,
    {dart // dart ∈ orbitFaceDarts
      embedded.cellulation.rotation.toRotationSystem face.1}

/-- Each frozen-edge dart is a dart of the outer hole face. -/
noncomputable def frozenEdgeDartToHoleDart {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    embedded.FrozenEdgeDart → embedded.HoleDart :=
  fun item =>
    ⟨⟨embedded.cellulation.outerHole, by
        simp [GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.holeFaces]⟩,
      ⟨item.2.1, by
        rw [mem_orbitFaceDarts_iff]
        exact embedded.frozenEdgeDarts_on_outerHole
          item.1 item.2.1 item.2.2⟩⟩

theorem frozenEdgeDartToHoleDart_injective {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    Function.Injective embedded.frozenEdgeDartToHoleDart := by
  intro left right heq
  have hdart : left.2.1 = right.2.1 :=
    congrArg (fun item : embedded.HoleDart => item.2.1) heq
  have hedge : left.1.1 = right.1.1 := by
    have hleft :=
      (embedded.cellulation.rotation.toRotationSystem.mem_dartsOn).1 left.2.2
    have hright :=
      (embedded.cellulation.rotation.toRotationSystem.mem_dartsOn).1 right.2.2
    exact hleft.symm.trans ((congrArg
      embedded.cellulation.rotation.toRotationSystem.edgeOf hdart).trans hright)
  rcases left with ⟨leftEdge, leftDart⟩
  rcases right with ⟨rightEdge, rightDart⟩
  have hedge' : leftEdge = rightEdge := Subtype.ext hedge
  subst rightEdge
  have hdart' : leftDart = rightDart := Subtype.ext hdart
  subst rightDart
  rfl

theorem card_frozenEdgeDart {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    Fintype.card embedded.FrozenEdgeDart =
      2 * source.frozenInterfaceEdges.card := by
  rw [Fintype.card_sigma]
  calc
    (∑ edge : source.frozenInterfaceEdges,
        Fintype.card {dart // dart ∈
          embedded.cellulation.rotation.toRotationSystem.dartsOn edge.1}) =
        ∑ _edge : source.frozenInterfaceEdges, 2 := by
      apply Finset.sum_congr rfl
      intro edge _
      rw [Fintype.card_coe,
        embedded.cellulation.rotation.toRotationSystem.dartsOn_card_two]
    _ = 2 * source.frozenInterfaceEdges.card := by
      simp [Nat.mul_comm]

theorem card_holeDart {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    Fintype.card embedded.HoleDart =
      embedded.cellulation.holePerimeter := by
  rw [Fintype.card_sigma]
  unfold GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.holePerimeter
  calc
    (∑ face : embedded.cellulation.holeFaces,
        Fintype.card {dart // dart ∈ orbitFaceDarts
          embedded.cellulation.rotation.toRotationSystem face.1}) =
        ∑ face : embedded.cellulation.holeFaces,
          (orbitFaceDarts embedded.cellulation.rotation.toRotationSystem
            face.1).card := by
      apply Finset.sum_congr rfl
      intro face _
      rw [Fintype.card_coe]
    _ = ∑ face ∈ embedded.cellulation.holeFaces,
        embedded.cellulation.faceLength face := by
      simp only [
        GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.faceLength]
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach embedded.cellulation.holeFaces
        (fun face => (orbitFaceDarts
          embedded.cellulation.rotation.toRotationSystem face).card)

/-- Source-semantic frozen leaves supply the numerical hole-perimeter
baseline; it is not assumed independently. -/
theorem twice_frozenStubCount_le_holePerimeter {source : SourceTrail G}
    (embedded : source.AnnularEmbedding) :
    2 * source.frozenInterfaceStubVertices.card ≤
      embedded.cellulation.holePerimeter := by
  have hle := Fintype.card_le_of_injective
    embedded.frozenEdgeDartToHoleDart
    embedded.frozenEdgeDartToHoleDart_injective
  rw [embedded.card_frozenEdgeDart, embedded.card_holeDart] at hle
  have hstubEdge :
      source.frozenInterfaceStubVertices.card =
        source.frozenInterfaceEdges.card := by
    calc
      source.frozenInterfaceStubVertices.card =
          Fintype.card source.frozenInterfaceStubVertices := by simp
      _ = Fintype.card source.frozenInterfaceEdges :=
        Fintype.card_congr embedded.stubToFrozenEdge
      _ = source.frozenInterfaceEdges.card := by simp
  omega

/-- L9 for an embedded graph-side source trail: the framed excess constant is
`4 + 2s`, and `rho` is the actual surplus of its named hole walks. -/
theorem interiorExcess_eq_source_framed_constant
    {source : SourceTrail G} (hsource : source.WellFormed)
    (embedded : source.AnnularEmbedding) :
    embedded.cellulation.interiorExcess =
      4 + 2 * source.frozenInterfaceStubVertices.card -
        embedded.cellulation.boundarySurplus source.toFramedTrailData := by
  exact embedded.cellulation
    |>.interiorExcess_eq_four_add_twice_frozenStubCount_sub_boundarySurplus
      source.toFramedTrailData hsource
        embedded.twice_frozenStubCount_le_holePerimeter

end AnnularEmbedding

end SourceTrail

end GoertzelV24FramedTrail

end Mettapedia.GraphTheory.FourColor
