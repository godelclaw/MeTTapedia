import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebBoundaryData
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedAnnularExcess
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided

/-!
# Rotation-level embedding of the v24 closed-web interfaces

`AnnularBoundaryData` names the graph's inner and outer stub interfaces,
while `FramedAnnularCellulation` names two orbit faces.  Those structures do
not by themselves say that the interfaces bound the named holes.  This module
states that missing source-semantic relation explicitly, in the same style as
the framed source-trail embedding layer.

The relation is dart-sensitive: every dart over an inner boundary edge lies
on the inner hole face, and similarly outside.  The theorems below derive the
edge-boundary consequences and prove that neither interface can occur on the
opposite hole.  No chord-side or Sector-Alternation conclusion is included.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebAnnularEmbedding

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24OrbitFaceTwoSided
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

/-- The inner interface's actual graph edges. -/
def innerBoundaryEdges (data : AnnularBoundaryData G outerCount) :
    Finset G.edgeSet :=
  Finset.univ.map data.innerBoundaryEdge

/-- The outer interface's actual graph edges. -/
def outerBoundaryEdges (data : AnnularBoundaryData G outerCount) :
    Finset G.edgeSet :=
  Finset.univ.map data.outerBoundaryEdge

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem mem_innerBoundaryEdges_iff
    (data : AnnularBoundaryData G outerCount) (edge : G.edgeSet) :
    edge ∈ innerBoundaryEdges data ↔
      ∃ inner : Fin 5, data.innerBoundaryEdge inner = edge := by
  simp [innerBoundaryEdges]

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem mem_outerBoundaryEdges_iff
    (data : AnnularBoundaryData G outerCount) (edge : G.edgeSet) :
    edge ∈ outerBoundaryEdges data ↔
      ∃ outer : Fin outerCount, data.outerBoundaryEdge outer = edge := by
  simp [outerBoundaryEdges]

/-- A cellular annular realization of the two graph-side interfaces.  The
per-dart fields express that a degree-one boundary edge is gathered by its
designated hole face, rather than merely having a convenient edge count. -/
structure ClosedWebAnnularEmbedding
    (data : AnnularBoundaryData G outerCount) where
  cellulation : FramedAnnularCellulation G
  /-- The distinguished root of the graph-backed rotation data is chosen on
  the named outer hole.  The source splice selects its retained component from
  this root, so making the relation explicit prevents a purely arbitrary root
  from being mistaken for the exterior side. -/
  outer_dart_on_outerHole :
    dartOrbitFace cellulation.rotation.toRotationSystem
      cellulation.rotation.toRotationSystem.outer = cellulation.outerHole
  innerBoundaryEdgeDarts_on_innerHole :
    ∀ inner : Fin 5,
      ∀ dart ∈ cellulation.rotation.toRotationSystem.dartsOn
        (data.innerBoundaryEdge inner),
        dartOrbitFace cellulation.rotation.toRotationSystem dart =
          cellulation.innerHole
  outerBoundaryEdgeDarts_on_outerHole :
    ∀ outer : Fin outerCount,
      ∀ dart ∈ cellulation.rotation.toRotationSystem.dartsOn
        (data.outerBoundaryEdge outer),
        dartOrbitFace cellulation.rotation.toRotationSystem dart =
          cellulation.outerHole

namespace ClosedWebAnnularEmbedding

variable {data : AnnularBoundaryData G outerCount}
  (embedded : ClosedWebAnnularEmbedding data)

noncomputable abbrev RS := embedded.cellulation.rotation.toRotationSystem

/-- A Cell--3 annulus is deliberately not globally face-two-sided: each named
inner interface edge has both dart sides on the inner hole.  Source-local
separator arguments must therefore use the local two-sidedness of their
interior face support, rather than importing a closed-map theorem whose global
premise is false on this carrier. -/
theorem not_orbitFacesTwoSided :
    ¬ OrbitFacesTwoSided embedded.RS := by
  intro htwoSided
  have hcard := embedded.RS.dartsOn_card_two (data.innerBoundaryEdge 0)
  have hpositive : 0 < (embedded.RS.dartsOn
      (data.innerBoundaryEdge 0)).card := by
    omega
  rcases Finset.card_pos.mp hpositive with ⟨dart, hdart⟩
  have halpha : embedded.RS.alpha dart ∈ embedded.RS.dartsOn
      (data.innerBoundaryEdge 0) := by
    apply (embedded.RS.mem_dartsOn).2
    rw [embedded.RS.edge_alpha]
    exact (embedded.RS.mem_dartsOn).1 hdart
  have hleft : dartOrbitFace embedded.RS dart =
      embedded.cellulation.innerHole :=
    embedded.innerBoundaryEdgeDarts_on_innerHole 0 dart hdart
  have hright : dartOrbitFace embedded.RS (embedded.RS.alpha dart) =
      embedded.cellulation.innerHole :=
    embedded.innerBoundaryEdgeDarts_on_innerHole 0 (embedded.RS.alpha dart) halpha
  exact htwoSided dart (hleft.trans hright.symm)

/-- Every inner interface edge occurs on the named inner hole boundary. -/
theorem innerBoundaryEdge_mem_innerHoleBoundary (inner : Fin 5) :
    data.innerBoundaryEdge inner ∈
      orbitFaceBoundary embedded.RS embedded.cellulation.innerHole := by
  classical
  have hcard := embedded.RS.dartsOn_card_two
    (data.innerBoundaryEdge inner)
  have hnonempty :
      (embedded.RS.dartsOn (data.innerBoundaryEdge inner)).Nonempty :=
    Finset.card_pos.mp (by omega)
  rcases hnonempty with ⟨dart, hdart⟩
  apply (mem_orbitFaceBoundary_iff embedded.RS
    embedded.cellulation.innerHole (data.innerBoundaryEdge inner)).2
  refine ⟨dart, ?_, (embedded.RS.mem_dartsOn).1 hdart⟩
  exact (mem_orbitFaceDarts_iff embedded.RS
    embedded.cellulation.innerHole dart).2
      (embedded.innerBoundaryEdgeDarts_on_innerHole inner dart hdart)

/-- Every outer interface edge occurs on the named outer hole boundary. -/
theorem outerBoundaryEdge_mem_outerHoleBoundary (outer : Fin outerCount) :
    data.outerBoundaryEdge outer ∈
      orbitFaceBoundary embedded.RS embedded.cellulation.outerHole := by
  classical
  have hcard := embedded.RS.dartsOn_card_two
    (data.outerBoundaryEdge outer)
  have hnonempty :
      (embedded.RS.dartsOn (data.outerBoundaryEdge outer)).Nonempty :=
    Finset.card_pos.mp (by omega)
  rcases hnonempty with ⟨dart, hdart⟩
  apply (mem_orbitFaceBoundary_iff embedded.RS
    embedded.cellulation.outerHole (data.outerBoundaryEdge outer)).2
  refine ⟨dart, ?_, (embedded.RS.mem_dartsOn).1 hdart⟩
  exact (mem_orbitFaceDarts_iff embedded.RS
    embedded.cellulation.outerHole dart).2
      (embedded.outerBoundaryEdgeDarts_on_outerHole outer dart hdart)

/-- An inner interface edge cannot also occur on the distinct outer hole. -/
theorem innerBoundaryEdge_not_mem_outerHoleBoundary (inner : Fin 5) :
    data.innerBoundaryEdge inner ∉
      orbitFaceBoundary embedded.RS embedded.cellulation.outerHole := by
  intro houter
  rcases (mem_orbitFaceBoundary_iff embedded.RS
    embedded.cellulation.outerHole (data.innerBoundaryEdge inner)).1 houter with
    ⟨dart, hdartOuter, hedge⟩
  have hdartsOn : dart ∈ embedded.RS.dartsOn
      (data.innerBoundaryEdge inner) :=
    (embedded.RS.mem_dartsOn).2 hedge
  have hinnerFace :=
    embedded.innerBoundaryEdgeDarts_on_innerHole inner dart hdartsOn
  have houterFace := (mem_orbitFaceDarts_iff embedded.RS
    embedded.cellulation.outerHole dart).1 hdartOuter
  exact embedded.cellulation.holes_ne (hinnerFace.symm.trans houterFace)

/-- An outer interface edge cannot also occur on the distinct inner hole. -/
theorem outerBoundaryEdge_not_mem_innerHoleBoundary
    (outer : Fin outerCount) :
    data.outerBoundaryEdge outer ∉
      orbitFaceBoundary embedded.RS embedded.cellulation.innerHole := by
  intro hinner
  rcases (mem_orbitFaceBoundary_iff embedded.RS
    embedded.cellulation.innerHole (data.outerBoundaryEdge outer)).1 hinner with
    ⟨dart, hdartInner, hedge⟩
  have hdartsOn : dart ∈ embedded.RS.dartsOn
      (data.outerBoundaryEdge outer) :=
    (embedded.RS.mem_dartsOn).2 hedge
  have houterFace :=
    embedded.outerBoundaryEdgeDarts_on_outerHole outer dart hdartsOn
  have hinnerFace := (mem_orbitFaceDarts_iff embedded.RS
    embedded.cellulation.innerHole dart).1 hdartInner
  exact embedded.cellulation.holes_ne (hinnerFace.symm.trans houterFace)

/-- The complete named inner interface lies on the inner hole boundary. -/
theorem innerBoundaryEdges_subset_innerHoleBoundary :
    innerBoundaryEdges data ⊆
      orbitFaceBoundary embedded.RS embedded.cellulation.innerHole := by
  intro edge hedge
  rcases (mem_innerBoundaryEdges_iff data edge).1 hedge with ⟨inner, rfl⟩
  exact embedded.innerBoundaryEdge_mem_innerHoleBoundary inner

/-- The complete named outer interface lies on the outer hole boundary. -/
theorem outerBoundaryEdges_subset_outerHoleBoundary :
    outerBoundaryEdges data ⊆
      orbitFaceBoundary embedded.RS embedded.cellulation.outerHole := by
  intro edge hedge
  rcases (mem_outerBoundaryEdges_iff data edge).1 hedge with ⟨outer, rfl⟩
  exact embedded.outerBoundaryEdge_mem_outerHoleBoundary outer

/-- No named inner interface edge lies on the outer hole boundary. -/
theorem innerBoundaryEdges_disjoint_outerHoleBoundary :
    Disjoint (innerBoundaryEdges data)
      (orbitFaceBoundary embedded.RS embedded.cellulation.outerHole) := by
  rw [Finset.disjoint_left]
  intro edge hedgeInner hedgeOuter
  rcases (mem_innerBoundaryEdges_iff data edge).1 hedgeInner with ⟨inner, rfl⟩
  exact embedded.innerBoundaryEdge_not_mem_outerHoleBoundary inner hedgeOuter

/-- No named outer interface edge lies on the inner hole boundary. -/
theorem outerBoundaryEdges_disjoint_innerHoleBoundary :
    Disjoint (outerBoundaryEdges data)
      (orbitFaceBoundary embedded.RS embedded.cellulation.innerHole) := by
  rw [Finset.disjoint_left]
  intro edge hedgeOuter hedgeInner
  rcases (mem_outerBoundaryEdges_iff data edge).1 hedgeOuter with ⟨outer, rfl⟩
  exact embedded.outerBoundaryEdge_not_mem_innerHoleBoundary outer hedgeInner

end ClosedWebAnnularEmbedding

end GoertzelV24ClosedWebAnnularEmbedding

end Mettapedia.GraphTheory.FourColor
