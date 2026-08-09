import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAnnularEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24DualPathTransversal
import Mettapedia.GraphTheory.FourColor.GoertzelV24NonisolatedFaceDualConnectedness
import Mathlib.Combinatorics.SimpleGraph.DeleteEdges

/-!
# Simple annular crosscuts

The corridor profiles in Addendum XXVII live on open transversals: a simple
facial-dual path from one annular boundary to the other.  Such a crosscut is
not a closed Jordan wall and therefore does not carry a global vertex-side
predicate.  This file records the actual finite crosscut geometry used by an
open corridor: its ordered crossed primal edges and its intervening face
cells.

The later strip/splice construction will use two ordered crosscuts together.
Keeping one crosscut open here prevents an accidental replacement of the
source's open-interface construction by a stronger, generally false cyclic-cut
claim.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularCrosscut

open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24DualPathTransversal
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24NonisolatedFaceDualConnectedness
open SimpleGraph

variable {F E : Type*} [Fintype F] [DecidableEq F]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A source-level simple transversal, represented combinatorially by a
simple path in the facial dual.  Its endpoints are named boundary faces; the
path itself supplies the actual sequence of primal edges that it crosses. -/
structure SimpleDualCrosscut
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (start finish : AmbientFace allFaces) where
  walk : (interiorDualGraph faceBoundary allFaces).Walk start finish
  isPath : walk.IsPath

namespace SimpleDualCrosscut

/-- The primal edge crossed at one ordered position of the crosscut. -/
def crossingEdge
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (crosscut : SimpleDualCrosscut faceBoundary allFaces start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (step : Fin crosscut.walk.length) : E :=
  dualWalkCrossingEdge faceBoundary allFaces hunique crosscut.walk step

/-- The finite support of primal edges crossed by the open crosscut. -/
def crossingEdges
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (crosscut : SimpleDualCrosscut faceBoundary allFaces start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces) :
    Finset E :=
  dualWalkCrossingEdges faceBoundary allFaces hunique crosscut.walk

/-- The face cells strictly between consecutive crossings.  These are the
finite cells through which the open transversal passes; endpoint faces are
not included. -/
def intermediateFaces
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (crosscut : SimpleDualCrosscut faceBoundary allFaces start finish) :
    Finset (AmbientFace allFaces) :=
  Finset.univ.image
    (dualWalkIntermediateFace faceBoundary allFaces crosscut.walk)

@[simp]
theorem mem_crossingEdges_iff
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (crosscut : SimpleDualCrosscut faceBoundary allFaces start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (edge : E) :
    edge ∈ crosscut.crossingEdges hunique ↔
      ∃ step : Fin crosscut.walk.length,
        crosscut.crossingEdge hunique step = edge := by
  exact mem_dualWalkCrossingEdges_iff faceBoundary allFaces hunique
    crosscut.walk edge

/-- Simple dual paths cross distinct primal edges.  This is the first
mechanical part of the source's ``simple transversal'' condition. -/
theorem crossingEdge_injective
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    {start finish : AmbientFace allFaces}
    (crosscut : SimpleDualCrosscut faceBoundary allFaces start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces) :
    Function.Injective (crosscut.crossingEdge hunique) := by
  exact dualWalkCrossingEdge_injective_of_isPath faceBoundary allFaces hall
    hunique crosscut.walk crosscut.isPath

/-- The crosscut support has exactly one edge for every dual step. -/
theorem card_crossingEdges_eq_length
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    {start finish : AmbientFace allFaces}
    (crosscut : SimpleDualCrosscut faceBoundary allFaces start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces) :
    (crosscut.crossingEdges hunique).card = crosscut.walk.length := by
  exact card_dualWalkCrossingEdges_eq_length_of_isPath faceBoundary allFaces
    hall hunique crosscut.walk crosscut.isPath

/-- No intermediate facial cell repeats along a simple transversal. -/
theorem intermediateFace_injective
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (crosscut : SimpleDualCrosscut faceBoundary allFaces start finish) :
    Function.Injective
      (dualWalkIntermediateFace faceBoundary allFaces crosscut.walk) := by
  exact dualWalkIntermediateFace_injective_of_isPath faceBoundary allFaces
    crosscut.walk crosscut.isPath

/-- The concrete carrier of intervening cells has the expected length. -/
theorem card_intermediateFaces_eq_length_sub_one
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (crosscut : SimpleDualCrosscut faceBoundary allFaces start finish) :
    crosscut.intermediateFaces.card = crosscut.walk.length - 1 := by
  rw [intermediateFaces,
    Finset.card_image_of_injective _ crosscut.intermediateFace_injective,
    Finset.card_univ, Fintype.card_fin]

/-- An intermediate cell of a simple crosscut is neither endpoint face.  In
particular, a simple path between the two annular holes stays in the annular
cell complex after its first step and before its last. -/
theorem intermediateFace_ne_endpoints
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    {start finish : AmbientFace allFaces}
    (crosscut : SimpleDualCrosscut faceBoundary allFaces start finish)
    (step : Fin (crosscut.walk.length - 1)) :
    dualWalkIntermediateFace faceBoundary allFaces crosscut.walk step ≠ start ∧
      dualWalkIntermediateFace faceBoundary allFaces crosscut.walk step ≠ finish := by
  constructor
  · intro hface
    have hpositions : step.val + 1 = 0 :=
      crosscut.isPath.getVert_injOn
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simpa [dualWalkIntermediateFace] using hface)
    omega
  · intro hface
    have hpositions : step.val + 1 = crosscut.walk.length :=
      crosscut.isPath.getVert_injOn
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simp only [Set.mem_setOf_eq]; omega)
        (by simpa [dualWalkIntermediateFace] using hface)
    have hstep : step.val < crosscut.walk.length - 1 := step.isLt
    omega

/-- Consecutive crossed edges meet in their actual intervening face cell, and
are distinct.  This is the local cell datum from which a strip between two
crosscuts is assembled. -/
theorem intermediateFace_contains_distinct_crossings
    {faceBoundary : F → Finset E} {allFaces : Finset F}
    (hall : ∀ edge, totalIncidenceCount faceBoundary allFaces edge ≤ 2)
    {start finish : AmbientFace allFaces}
    (crosscut : SimpleDualCrosscut faceBoundary allFaces start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges faceBoundary allFaces)
    (step : Fin (crosscut.walk.length - 1)) :
    let incoming : Fin crosscut.walk.length := ⟨step.val, by omega⟩
    let outgoing : Fin crosscut.walk.length := ⟨step.val + 1, by omega⟩
    crosscut.crossingEdge hunique incoming ∈
        faceBoundary (dualWalkIntermediateFace faceBoundary allFaces
          crosscut.walk step).1 ∧
      crosscut.crossingEdge hunique outgoing ∈
        faceBoundary (dualWalkIntermediateFace faceBoundary allFaces
          crosscut.walk step).1 ∧
      crosscut.crossingEdge hunique incoming ≠
        crosscut.crossingEdge hunique outgoing := by
  exact dualWalkIntermediateFace_contains_distinct_crossings_of_isPath
    faceBoundary allFaces hall hunique crosscut.walk crosscut.isPath step

end SimpleDualCrosscut

omit [Fintype F] [DecidableEq F] [Fintype E] in
/-- Facial-dual connectedness constructs a genuine simple crosscut between
any two named faces.  No geometric witness is deferred to a caller: Lean
shortens an arbitrary dual walk to a simple path. -/
theorem exists_simpleDualCrosscut_of_connected
    (faceBoundary : F → Finset E) (allFaces : Finset F)
    (hconnected : (interiorDualGraph faceBoundary allFaces).Connected)
    (start finish : AmbientFace allFaces) :
    ∃ crosscut : SimpleDualCrosscut faceBoundary allFaces start finish,
      crosscut.walk.IsPath := by
  obtain ⟨walk, hpath⟩ := hconnected.exists_isPath start finish
  exact ⟨⟨walk, hpath⟩, hpath⟩

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

/-! ## The cut-open interface

The source's transversal is an open slit, so its graph-level realization is
edge deletion together with the two exposed oriented ends of every crossed
edge.  This is deliberately not a vertex-side construction: deleting an open
annular crosscut need not disconnect the ambient primal graph.

Mathlib's `deleteEdges` supplies the graph after opening; the finite sigma
carrier below records its actual boundary ports without adding an arbitrary
ordering or a synthetic separator. -/

/-- The finite support crossed by an ordered transversal. -/
noncomputable def crosscutSupport {n : Nat}
    (crossing : Fin n → G.edgeSet) : Finset G.edgeSet :=
  Finset.univ.image crossing

/-- The value-level edge support consumed by `SimpleGraph.deleteEdges`. -/
def crosscutEdgeValues {n : Nat}
    (crossing : Fin n → G.edgeSet) : Set (Sym2 V) :=
  Subtype.val '' (crosscutSupport crossing : Set G.edgeSet)

/-- One exposed oriented end of a crossed edge.  The first coordinate is the
source order of the transversal; the second coordinate is an actual dart of
the underlying graph, rather than a made-up stub. -/
abbrev CrosscutPort {n : Nat}
    (crossing : Fin n → G.edgeSet) :=
  Σ step : Fin n, {dart : G.Dart //
    (⟨dart.edge, dart.edge_mem⟩ : G.edgeSet) = crossing step}

namespace CrosscutPort

/-- The actual graph dart represented by an exposed crosscut port. -/
def dart {n : Nat} {crossing : Fin n → G.edgeSet}
    (port : CrosscutPort crossing) : G.Dart :=
  port.2.1

@[simp]
theorem dart_edge_eq_crossing {n : Nat} {crossing : Fin n → G.edgeSet}
    (port : CrosscutPort crossing) :
    (⟨port.dart.edge, port.dart.edge_mem⟩ : G.edgeSet) = crossing port.1 :=
  port.2.2

/-- When the ordered crossing list is injective, its two-port presentation
does not accidentally identify exposed ends from different crossing edges. -/
theorem dart_injective {n : Nat} {crossing : Fin n → G.edgeSet}
    (hinjective : Function.Injective crossing) :
    Function.Injective (dart (G := G) (crossing := crossing)) := by
  rintro ⟨leftStep, leftDart, hleftDart⟩ ⟨rightStep, rightDart, hrightDart⟩
    hdarts
  have hedges : crossing leftStep = crossing rightStep := by
    calc
      crossing leftStep =
          (⟨leftDart.edge, leftDart.edge_mem⟩ : G.edgeSet) :=
        hleftDart.symm
      _ = (⟨rightDart.edge, rightDart.edge_mem⟩ : G.edgeSet) := by
        apply Subtype.ext
        exact congrArg SimpleGraph.Dart.edge hdarts
      _ = crossing rightStep := hrightDart
  have hsteps : leftStep = rightStep := hinjective hedges
  cases hsteps
  change leftDart = rightDart at hdarts
  cases hdarts
  rfl

end CrosscutPort

/-- The ambient graph cut open along the listed transversal edges.  The
crossed edges disappear; their two oriented ends remain as `CrosscutPort`s
for the finite profile and later seam matching. -/
noncomputable def crosscutOpenGraph {n : Nat}
    (crossing : Fin n → G.edgeSet) : SimpleGraph V :=
  G.deleteEdges (crosscutEdgeValues crossing)

/-- Vertices of the graph literally slit open along a transversal.  Old
vertices remain on the left; the right summand consists of one fresh
degree-one endpoint for every oriented end of every crossed edge. -/
abbrev CrosscutSlitVertex {n : Nat}
    (crossing : Fin n → G.edgeSet) :=
  V ⊕ CrosscutPort crossing

/-- The graph obtained by replacing each crossed edge by two boundary stubs.
This is a concrete cut-open construction, not merely a deletion predicate:
noncrossing ambient edges remain between old vertices, while a crossed edge
is represented by its two separately exposed ports. -/
noncomputable def crosscutSlitGraph {n : Nat}
    (crossing : Fin n → G.edgeSet) : SimpleGraph (CrosscutSlitVertex crossing) where
  Adj left right :=
    match left, right with
    | Sum.inl first, Sum.inl second =>
        G.Adj first second ∧ s(first, second) ∉ crosscutEdgeValues crossing
    | Sum.inl vertex, Sum.inr port => vertex = port.dart.fst
    | Sum.inr port, Sum.inl vertex => port.dart.fst = vertex
    | Sum.inr _, Sum.inr _ => False
  symm := ⟨by
    rintro (first | port) (second | other) h
    · exact ⟨h.1.symm, by simpa [Sym2.eq_swap] using h.2⟩
    · exact h.symm
    · exact h.symm
    · exact h⟩
  loopless := ⟨by
    rintro (vertex | port) h
    · exact h.1.ne rfl
    · exact h⟩

/-- Embed an original vertex into the cut-open graph. -/
def CrosscutSlitVertex.old {n : Nat} {crossing : Fin n → G.edgeSet}
    (vertex : V) : CrosscutSlitVertex crossing :=
  Sum.inl vertex

/-- The fresh degree-one vertex belonging to one exposed crosscut port. -/
def CrosscutSlitVertex.stub {n : Nat} {crossing : Fin n → G.edgeSet}
    (port : CrosscutPort crossing) : CrosscutSlitVertex crossing :=
  Sum.inr port

@[simp]
theorem crosscutSlitGraph_old_adj_old_iff {n : Nat}
    (crossing : Fin n → G.edgeSet) (first second : V) :
    (crosscutSlitGraph crossing).Adj
        (CrosscutSlitVertex.old first) (CrosscutSlitVertex.old second) ↔
      G.Adj first second ∧
        s(first, second) ∉ crosscutEdgeValues crossing :=
  Iff.rfl

/-- A fresh port stub has exactly one possible neighbor: the old vertex at
the corresponding end of its original crossed edge. -/
theorem crosscutSlitGraph_stub_adj_iff {n : Nat}
    {crossing : Fin n → G.edgeSet} (port : CrosscutPort crossing)
    (vertex : CrosscutSlitVertex crossing) :
    (crosscutSlitGraph crossing).Adj (CrosscutSlitVertex.stub port) vertex ↔
      vertex = CrosscutSlitVertex.old port.dart.fst := by
  cases vertex with
  | inl oldVertex =>
      change port.dart.fst = oldVertex ↔
        (Sum.inl oldVertex : CrosscutSlitVertex crossing) =
          Sum.inl port.dart.fst
      constructor
      · intro h
        exact congrArg Sum.inl h.symm
      · intro h
        exact (Sum.inl.inj h).symm
  | inr otherPort =>
      simp [crosscutSlitGraph, CrosscutSlitVertex.stub,
        CrosscutSlitVertex.old]

/-- Every exposed port is connected to its own fresh degree-one stub edge. -/
theorem crosscutSlitGraph_stub_adj_old {n : Nat}
    {crossing : Fin n → G.edgeSet} (port : CrosscutPort crossing) :
    (crosscutSlitGraph crossing).Adj (CrosscutSlitVertex.stub port)
      (CrosscutSlitVertex.old port.dart.fst) := by
  exact (crosscutSlitGraph_stub_adj_iff port _).2 rfl

@[simp]
theorem mem_crosscutSupport_iff {n : Nat}
    (crossing : Fin n → G.edgeSet) (edge : G.edgeSet) :
    edge ∈ crosscutSupport crossing ↔
      ∃ step : Fin n, crossing step = edge := by
  simp [crosscutSupport]

@[simp]
theorem mem_crosscutEdgeValues_iff {n : Nat}
    (crossing : Fin n → G.edgeSet) (edge : G.edgeSet) :
    edge.1 ∈ crosscutEdgeValues crossing ↔
      ∃ step : Fin n, crossing step = edge := by
  constructor
  · rintro ⟨other, hother, hvalue⟩
    obtain ⟨step, hstep⟩ := (mem_crosscutSupport_iff crossing other).1 hother
    exact ⟨step, hstep.trans (Subtype.ext hvalue)⟩
  · rintro ⟨step, hstep⟩
    refine ⟨crossing step, ?_, ?_⟩
    · exact (mem_crosscutSupport_iff crossing _).2 ⟨step, rfl⟩
    · exact congrArg Subtype.val hstep

/-- The original two endpoints of any crossed edge are no longer adjacent
through old vertices in the slit graph.  Their information is retained only
at the two fresh boundary ports. -/
theorem CrosscutPort.not_old_adj_old_in_crosscutSlitGraph {n : Nat}
    {crossing : Fin n → G.edgeSet} (port : CrosscutPort crossing) :
    ¬ (crosscutSlitGraph crossing).Adj
      (CrosscutSlitVertex.old port.dart.fst)
      (CrosscutSlitVertex.old port.dart.snd) := by
  rw [crosscutSlitGraph_old_adj_old_iff]
  intro hadj
  exact hadj.2 ((mem_crosscutEdgeValues_iff crossing
    ⟨port.dart.edge, port.dart.edge_mem⟩).2
      ⟨port.1, port.dart_edge_eq_crossing.symm⟩)

namespace SimpleDualCrosscut

/-- Cut a graph open along the ordered primal crossings of a simple orbit-face
dual transversal.  The result is an actual graph with boundary stubs, ready
for a finite interface profile; it is not an assumed separator. -/
noncomputable def slitGraph
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))) :
    SimpleGraph (CrosscutSlitVertex (crosscut.crossingEdge hunique)) :=
  crosscutSlitGraph (crosscut.crossingEdge hunique)

/-- In the ordinary two-face-incidence setting, the slit interface has no
duplicate actual darts: the simple dual path's ordered crossings determine
distinct port ends. -/
theorem slitGraph_port_dart_injective
    {RS : RotationSystem V G.edgeSet}
    {start finish : AmbientFace (Finset.univ : Finset (OrbitFace RS))}
    (crosscut : SimpleDualCrosscut (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS)) start finish)
    (hunique : PairwiseUniqueSharedInteriorEdges (orbitFaceBoundary RS)
      (Finset.univ : Finset (OrbitFace RS))) :
    Function.Injective
      (CrosscutPort.dart (G := G)
        (crossing := crosscut.crossingEdge hunique)) := by
  apply CrosscutPort.dart_injective
  exact crosscut.crossingEdge_injective (orbitFace_incidence_le_two RS) hunique

end SimpleDualCrosscut

/-- A port's edge really has been removed from the cut-open graph. -/
theorem CrosscutPort.not_adj_in_crosscutOpenGraph {n : Nat}
    {crossing : Fin n → G.edgeSet} (port : CrosscutPort crossing) :
    ¬ (crosscutOpenGraph crossing).Adj port.dart.fst port.dart.snd := by
  rw [crosscutOpenGraph, SimpleGraph.deleteEdges_adj]
  simp only [port.dart.adj, true_and]
  intro hnotRemoved
  apply hnotRemoved
  exact (mem_crosscutEdgeValues_iff crossing
    ⟨port.dart.edge, port.dart.edge_mem⟩).2
      ⟨port.1, port.dart_edge_eq_crossing.symm⟩

/-- Any ambient edge outside the ordered transversal survives in the opened
graph.  This is the exact graph-side complement law needed to retain either
complementary piece before matching its ports to another crosscut. -/
theorem adj_in_crosscutOpenGraph_of_not_mem {n : Nat}
    {crossing : Fin n → G.edgeSet} {left right : V}
    (hadj : G.Adj left right)
    (hnot : ∀ step : Fin n,
      crossing step ≠ ⟨s(left, right), hadj⟩) :
    (crosscutOpenGraph crossing).Adj left right := by
  rw [crosscutOpenGraph, SimpleGraph.deleteEdges_adj]
  refine ⟨hadj, ?_⟩
  intro hremoved
  obtain ⟨step, hstep⟩ :=
    (mem_crosscutEdgeValues_iff crossing ⟨s(left, right), hadj⟩).1 hremoved
  exact hnot step hstep

/-- A closed-web annular embedding therefore has a simple source-level
transversal from its named inner hole to its named outer hole as soon as its
computed facial dual is connected.  The resulting object is an open interface
for the profile engine, not a cyclic edge cut. -/
theorem exists_holeCrosscut_of_dualConnected
    {data : GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hconnected :
      (interiorDualGraph (orbitFaceBoundary embedded.RS)
        (Finset.univ : Finset (OrbitFace embedded.RS))).Connected) :
    ∃ crosscut : SimpleDualCrosscut (orbitFaceBoundary embedded.RS)
        (Finset.univ : Finset (OrbitFace embedded.RS))
        ⟨embedded.cellulation.innerHole, Finset.mem_univ _⟩
        ⟨embedded.cellulation.outerHole, Finset.mem_univ _⟩,
      crosscut.walk.IsPath :=
  exists_simpleDualCrosscut_of_connected
    (orbitFaceBoundary embedded.RS)
    (Finset.univ : Finset (OrbitFace embedded.RS)) hconnected
    ⟨embedded.cellulation.innerHole, Finset.mem_univ _⟩
    ⟨embedded.cellulation.outerHole, Finset.mem_univ _⟩

/-- The stored connected graph and cyclic vertex rotations of a framed
annular cellulation make its full facial dual connected.  Boundary stubs do
not obstruct this: every vertex of a connected graph has an outgoing dart. -/
theorem holeDual_connected
    {data : GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data) :
    (interiorDualGraph (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))).Connected := by
  exact orbitFaceInteriorDual_connected_of_simpleGraph
    embedded.cellulation.rotation embedded.cellulation.connected
    embedded.cellulation.vertexRotation_cyclic

/-- Every closed-web annular embedding therefore constructs its own simple
inner-to-outer transversal.  This is the source-level geometric object on
which the length profile is taken. -/
theorem exists_holeCrosscut
    {data : GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data) :
    ∃ crosscut : SimpleDualCrosscut (orbitFaceBoundary embedded.RS)
        (Finset.univ : Finset (OrbitFace embedded.RS))
        ⟨embedded.cellulation.innerHole, Finset.mem_univ _⟩
        ⟨embedded.cellulation.outerHole, Finset.mem_univ _⟩,
      crosscut.walk.IsPath :=
  exists_holeCrosscut_of_dualConnected embedded (holeDual_connected embedded)

/-- In normal-form closed-web data where two distinct face cells share at
most one edge, the automatically found hole-to-hole crosscut comes with a
duplicate-free concrete slit interface.  The theorem constructs both the
crosscut and the port discipline from the embedding; only the ordinary
face-intersection hypothesis remains explicit. -/
theorem exists_holeCrosscut_with_injectivePorts
    {data : GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.RS)
      (Finset.univ : Finset (OrbitFace embedded.RS))) :
    ∃ crosscut : SimpleDualCrosscut (orbitFaceBoundary embedded.RS)
        (Finset.univ : Finset (OrbitFace embedded.RS))
        ⟨embedded.cellulation.innerHole, Finset.mem_univ _⟩
        ⟨embedded.cellulation.outerHole, Finset.mem_univ _⟩,
      Function.Injective
        (CrosscutPort.dart (G := G)
          (crossing := crosscut.crossingEdge hunique)) := by
  obtain ⟨crosscut, _⟩ := exists_holeCrosscut embedded
  exact ⟨crosscut, crosscut.slitGraph_port_dart_injective hunique⟩

/-- The automatically constructed inner-to-outer crosscut has only annular
intermediate cells.  This is the source-facing form used when a sequence of
such positions is assembled into a corridor strip. -/
theorem exists_holeCrosscut_with_annularCells
    {data : GoertzelV24ClosedWebBoundaryData.AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data) :
    ∃ crosscut : SimpleDualCrosscut (orbitFaceBoundary embedded.RS)
        (Finset.univ : Finset (OrbitFace embedded.RS))
        ⟨embedded.cellulation.innerHole, Finset.mem_univ _⟩
        ⟨embedded.cellulation.outerHole, Finset.mem_univ _⟩,
      crosscut.walk.IsPath ∧
        ∀ step : Fin (crosscut.walk.length - 1),
          dualWalkIntermediateFace (orbitFaceBoundary embedded.RS)
              (Finset.univ : Finset (OrbitFace embedded.RS))
              crosscut.walk step ≠
            ⟨embedded.cellulation.innerHole, Finset.mem_univ _⟩ ∧
          dualWalkIntermediateFace (orbitFaceBoundary embedded.RS)
              (Finset.univ : Finset (OrbitFace embedded.RS))
              crosscut.walk step ≠
            ⟨embedded.cellulation.outerHole, Finset.mem_univ _⟩ := by
  obtain ⟨crosscut, hpath⟩ := exists_holeCrosscut embedded
  refine ⟨crosscut, hpath, ?_⟩
  intro step
  exact crosscut.intermediateFace_ne_endpoints step

end

end GoertzelV24AnnularCrosscut

end Mettapedia.GraphTheory.FourColor
