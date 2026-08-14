import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoPentagonCapOpening
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# Facial pentagon caps

A `PentagonCap` is deliberately graph-theoretic: a five-cycle, five outward
spokes, and their incidence.  The Cell-3 formation needs strictly more: the
five-cycle must be the literal boundary of one face orbit of the closed
spherical rotation, so that opening the cap has a specified facial boundary
and surface surgery can compare Euler data.  This module records that stronger
datum without changing the graph-level cap library.

`FacialPentagonCap` is a cap together with a dart of the closed rotation whose
face orbit has exactly the five cap-cycle edges as its edge set.
`FacialPentagonCapPair` is a separated cap pair in which both caps are facial.
No annular carrier, hole-orbit computation, or crosscut is constructed here;
those are the later formation steps that consume this datum.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FacialPentagonCap

open SimpleGraphDartRotation
open GoertzelV24PentagonCapOpening
open GoertzelV24TwoPentagonCapOpening

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- A pentagon cap whose five-cycle is the literal boundary of one face orbit
of the closed rotation: some dart's face orbit has exactly the five cap-cycle
edges as its edge set.  This is the source-facing strengthening of the
graph-level `PentagonCap`; it is what licenses reading the cap deletion as
removing one pentagonal face rather than an arbitrary five-cycle. -/
structure FacialPentagonCap (data : Data G) extends PentagonCap G where
  faceDart : G.Dart
  face_edges_eq :
    data.toRotationSystem.faceEdges faceDart = toPentagonCap.cycleSupport

namespace FacialPentagonCap

variable {data : Data G}

/-- The pentagonal face has exactly five edges. -/
theorem faceEdges_card (cap : FacialPentagonCap data) :
    (data.toRotationSystem.faceEdges cap.faceDart).card = 5 := by
  rw [cap.face_edges_eq, PentagonCap.cycleSupport, Finset.card_map]
  simp

/-- Membership in the facial boundary is exactly being a named cap-cycle
edge. -/
theorem mem_faceEdges_iff (cap : FacialPentagonCap data) (edge : G.edgeSet) :
    edge ∈ data.toRotationSystem.faceEdges cap.faceDart ↔
      ∃ step : Fin 5, cap.toPentagonCap.cycleEdge step = edge := by
  rw [cap.face_edges_eq, PentagonCap.cycleSupport]
  simp

/-- No outward spoke lies on the pentagonal face: the face boundary consists
of cap-cycle edges only. -/
theorem spokeEdge_not_mem_faceEdges (cap : FacialPentagonCap data)
    (step : Fin 5) :
    cap.toPentagonCap.spokeEdge step ∉
      data.toRotationSystem.faceEdges cap.faceDart := by
  intro hmem
  rcases (cap.mem_faceEdges_iff _).mp hmem with ⟨cycle, hcycle⟩
  exact cap.toPentagonCap.cycle_spoke_ne cycle step hcycle

end FacialPentagonCap

/-- A facial pentagon cap whose `Fin 5` coordinates follow the cap cycle's
vertex order.  `FacialPentagonCap` identifies the face-edge *set*; this
strengthening records the source coordinates on that cycle.  It deliberately
does not yet assert that the closed face permutation visits those coordinates
in this order: the next structure records that actual boundary walk. -/
structure OrientedFacialPentagonCap (data : Data G)
    extends FacialPentagonCap data where
  cycleEdge_eq_vertices : ∀ step : Fin 5,
    (toFacialPentagonCap.toPentagonCap.cycleEdge step).1 =
      s(toFacialPentagonCap.toPentagonCap.vertex step,
        toFacialPentagonCap.toPentagonCap.vertex (step + 1))

/-- A facial pentagon cap with its literal five-step closed face walk.  The
face-edge set alone is insufficient for the cap-opening calculation: C-2 must
know which oriented dart follows which.  These fields are the exact
rotation-level version of the source's five stubs in cyclic order.  They are
still input data, not a construction of a cap from a minimal counterexample. -/
structure FacialPentagonCapBoundaryWalk (data : Data G)
    extends OrientedFacialPentagonCap data where
  boundaryDart : Fin 5 → G.Dart
  faceDart_eq_boundaryDart_zero :
    toOrientedFacialPentagonCap.toFacialPentagonCap.faceDart = boundaryDart 0
  boundaryDart_edge : ∀ step : Fin 5,
    data.toRotationSystem.edgeOf (boundaryDart step) =
      toOrientedFacialPentagonCap.toFacialPentagonCap.toPentagonCap.cycleEdge step
  boundaryDart_phi : ∀ step : Fin 5,
    data.toRotationSystem.phi (boundaryDart step) = boundaryDart (step + 1)

/-- Two separated pentagon caps, both facial.  This is the exact input datum
of the Cell-3 formation: from it, surface surgery must construct the two hole
orbits of the opened rotation and compare the Euler presentations.  The
separation fields are inherited unchanged from `PentagonCapPair`. -/
structure FacialPentagonCapPair (data : Data G) extends PentagonCapPair G where
  innerFaceDart : G.Dart
  outerFaceDart : G.Dart
  inner_face_edges_eq :
    data.toRotationSystem.faceEdges innerFaceDart =
      toPentagonCapPair.inner.cycleSupport
  outer_face_edges_eq :
    data.toRotationSystem.faceEdges outerFaceDart =
      toPentagonCapPair.outer.cycleSupport

namespace FacialPentagonCapPair

variable {data : Data G}

/-- The two facial caps of a pair are `FacialPentagonCap`s in their own
right (inner side). -/
def innerFacial (caps : FacialPentagonCapPair data) : FacialPentagonCap data where
  toPentagonCap := caps.toPentagonCapPair.inner
  faceDart := caps.innerFaceDart
  face_edges_eq := caps.inner_face_edges_eq

/-- The two facial caps of a pair are `FacialPentagonCap`s in their own
right (outer side). -/
def outerFacial (caps : FacialPentagonCapPair data) : FacialPentagonCap data where
  toPentagonCap := caps.toPentagonCapPair.outer
  faceDart := caps.outerFaceDart
  face_edges_eq := caps.outer_face_edges_eq

/-- The two named face boundaries of a separated facial pair are distinct
edge sets: an inner cap-cycle edge has both endpoints among the inner cap
vertices, which the pair's support disjointness keeps away from the outer cap
vertices carrying every outer cap-cycle edge. -/
theorem inner_faceEdges_ne_outer_faceEdges
    (caps : FacialPentagonCapPair data) :
    data.toRotationSystem.faceEdges caps.innerFaceDart ≠
      data.toRotationSystem.faceEdges caps.outerFaceDart := by
  rw [caps.inner_face_edges_eq, caps.outer_face_edges_eq]
  intro heq
  have hmemInner :
      caps.toPentagonCapPair.inner.cycleEdge 0 ∈
        caps.toPentagonCapPair.inner.cycleSupport :=
    Finset.mem_map_of_mem _ (Finset.mem_univ 0)
  have hmemOuter :
      caps.toPentagonCapPair.inner.cycleEdge 0 ∈
        caps.toPentagonCapPair.outer.cycleSupport := heq ▸ hmemInner
  rcases Finset.mem_map.mp hmemOuter with ⟨outerStep, -, houter⟩
  obtain ⟨⟨first, second⟩, hrep⟩ :=
    Quot.exists_rep (caps.toPentagonCapPair.inner.cycleEdge 0).1
  have hfirstMem : first ∈ (caps.toPentagonCapPair.inner.cycleEdge 0).1 := by
    rw [← hrep]
    exact Sym2.mem_mk_left first second
  rcases caps.toPentagonCapPair.inner.cycleEdge_endpoint_eq_vertex 0 first
      hfirstMem with ⟨innerStep, hinnerStep⟩
  have hfirstMemOuter :
      first ∈ (caps.toPentagonCapPair.outer.cycleEdge outerStep).1 := by
    rw [houter]
    exact hfirstMem
  rcases caps.toPentagonCapPair.outer.cycleEdge_endpoint_eq_vertex outerStep
      first hfirstMemOuter with ⟨outerVertexStep, houterVertexStep⟩
  have hinnerSupport :
      first ∈ caps.toPentagonCapPair.inner.vertexSupport :=
    (PentagonCap.mem_vertexSupport_iff _ _).mpr ⟨innerStep, hinnerStep⟩
  have houterSupport :
      first ∈ caps.toPentagonCapPair.outer.vertexSupport :=
    (PentagonCap.mem_vertexSupport_iff _ _).mpr
      ⟨outerVertexStep, houterVertexStep⟩
  exact Finset.disjoint_left.mp caps.toPentagonCapPair.vertexSupport_disjoint
    hinnerSupport houterSupport

end FacialPentagonCapPair

/-- A separated facial cap pair with the source's two cyclic five-stub
coordinate systems tied to the literal facial boundary order.  This is an
input interface for the cap-collar calculation, not a conclusion from the
unordered graph-level cap pair. -/
structure OrientedFacialPentagonCapPair (data : Data G)
    extends FacialPentagonCapPair data where
  inner_cycleEdge_eq_vertices : ∀ step : Fin 5,
    (toFacialPentagonCapPair.toPentagonCapPair.inner.cycleEdge step).1 =
      s(toFacialPentagonCapPair.toPentagonCapPair.inner.vertex step,
        toFacialPentagonCapPair.toPentagonCapPair.inner.vertex (step + 1))
  outer_cycleEdge_eq_vertices : ∀ step : Fin 5,
    (toFacialPentagonCapPair.toPentagonCapPair.outer.cycleEdge step).1 =
      s(toFacialPentagonCapPair.toPentagonCapPair.outer.vertex step,
        toFacialPentagonCapPair.toPentagonCapPair.outer.vertex (step + 1))

namespace OrientedFacialPentagonCapPair

variable {data : Data G}

/-- The inner member of an oriented facial pair. -/
def innerOriented (caps : OrientedFacialPentagonCapPair data) :
    OrientedFacialPentagonCap data where
  toFacialPentagonCap := caps.toFacialPentagonCapPair.innerFacial
  cycleEdge_eq_vertices := caps.inner_cycleEdge_eq_vertices

/-- The outer member of an oriented facial pair. -/
def outerOriented (caps : OrientedFacialPentagonCapPair data) :
    OrientedFacialPentagonCap data where
  toFacialPentagonCap := caps.toFacialPentagonCapPair.outerFacial
  cycleEdge_eq_vertices := caps.outer_cycleEdge_eq_vertices

end OrientedFacialPentagonCapPair

end

end GoertzelV24FacialPentagonCap

end Mettapedia.GraphTheory.FourColor
