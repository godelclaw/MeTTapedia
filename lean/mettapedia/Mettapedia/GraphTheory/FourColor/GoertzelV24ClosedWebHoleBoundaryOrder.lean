import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAnnularEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCyclicOrder

/-!
# Cyclic positions of the closed-web hole interfaces

The annular embedding places every named boundary edge on its designated
hole face.  This module retains the missing order information.  It orients
each boundary edge away from its ordered stub and records the unique cyclic
position of that dart in the corresponding face orbit.

The resulting position maps are injective.  Thus the supplied interfaces
really give distinct marked occurrences on the two facial cycles.  No
compatibility between the supplied `Fin` order and the facial cyclic order,
and no chord-side or disk-containment assertion, is assumed here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24ClosedWebHoleBoundaryOrder

open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedAnnularExcess
open GoertzelV24OrbitFaceCyclicOrder
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {outerCount : Nat}

noncomputable section

/-- Orient a named boundary edge away from its named stub. -/
def boundaryEdgeDartAt (edge : G.edgeSet) {vertex : V}
    (hvertex : vertex ∈ (edge.1 : Sym2 V)) : G.Dart :=
  ⟨(vertex, Sym2.Mem.other hvertex), by
    rw [← SimpleGraph.mem_edgeSet, Sym2.other_spec hvertex]
    exact edge.2⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem boundaryEdgeDartAt_fst (edge : G.edgeSet) {vertex : V}
    (hvertex : vertex ∈ (edge.1 : Sym2 V)) :
    (boundaryEdgeDartAt edge hvertex).fst = vertex :=
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
@[simp] theorem boundaryEdgeDartAt_edge (edge : G.edgeSet) {vertex : V}
    (hvertex : vertex ∈ (edge.1 : Sym2 V)) :
    (boundaryEdgeDartAt edge hvertex).edge = edge.1 :=
  Sym2.other_spec hvertex

/-- The inner boundary dart rooted at the ordered inner stub. -/
def innerBoundaryDart (data : AnnularBoundaryData G outerCount)
    (hdata : data.WellFormed) (inner : Fin 5) : G.Dart :=
  boundaryEdgeDartAt (data.innerBoundaryEdge inner) (by
    simpa [incidentEdgeFinset] using hdata.innerBoundaryEdge_incident inner)

/-- The outer boundary dart rooted at the ordered outer stub. -/
def outerBoundaryDart (data : AnnularBoundaryData G outerCount)
    (hdata : data.WellFormed) (outer : Fin outerCount) : G.Dart :=
  boundaryEdgeDartAt (data.outerBoundaryEdge outer) (by
    simpa [incidentEdgeFinset] using hdata.outerBoundaryEdge_incident outer)

@[simp] theorem innerBoundaryDart_fst
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (inner : Fin 5) :
    (innerBoundaryDart data hdata inner).fst = data.innerStub inner := by
  simp [innerBoundaryDart]

@[simp] theorem innerBoundaryDart_edge
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (inner : Fin 5) :
    (innerBoundaryDart data hdata inner).edge =
      (data.innerBoundaryEdge inner).1 := by
  simp [innerBoundaryDart]

@[simp] theorem outerBoundaryDart_fst
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (outer : Fin outerCount) :
    (outerBoundaryDart data hdata outer).fst = data.outerStub outer := by
  simp [outerBoundaryDart]

@[simp] theorem outerBoundaryDart_edge
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed)
    (outer : Fin outerCount) :
    (outerBoundaryDart data hdata outer).edge =
      (data.outerBoundaryEdge outer).1 := by
  simp [outerBoundaryDart]

/-- The chosen inner dart lies over its named boundary edge. -/
theorem innerBoundaryDart_mem_dartsOn
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (inner : Fin 5) :
    innerBoundaryDart data hdata inner ∈
      embedded.RS.dartsOn (data.innerBoundaryEdge inner) := by
  apply (embedded.RS.mem_dartsOn).2
  apply Subtype.ext
  exact innerBoundaryDart_edge data hdata inner

/-- The chosen outer dart lies over its named boundary edge. -/
theorem outerBoundaryDart_mem_dartsOn
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (outer : Fin outerCount) :
    outerBoundaryDart data hdata outer ∈
      embedded.RS.dartsOn (data.outerBoundaryEdge outer) := by
  apply (embedded.RS.mem_dartsOn).2
  apply Subtype.ext
  exact outerBoundaryDart_edge data hdata outer

/-- The chosen inner boundary dart belongs to the named inner hole. -/
theorem innerBoundaryDart_on_innerHole
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (inner : Fin 5) :
    dartOrbitFace embedded.RS (innerBoundaryDart data hdata inner) =
      embedded.cellulation.innerHole :=
  embedded.innerBoundaryEdgeDarts_on_innerHole inner
    (innerBoundaryDart data hdata inner)
    (innerBoundaryDart_mem_dartsOn embedded hdata inner)

/-- The chosen outer boundary dart belongs to the named outer hole. -/
theorem outerBoundaryDart_on_outerHole
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (outer : Fin outerCount) :
    dartOrbitFace embedded.RS (outerBoundaryDart data hdata outer) =
      embedded.cellulation.outerHole :=
  embedded.outerBoundaryEdgeDarts_on_outerHole outer
    (outerBoundaryDart data hdata outer)
    (outerBoundaryDart_mem_dartsOn embedded hdata outer)

/-- A representative dart of an orbit face. -/
def holeRootDart (cell : FramedAnnularCellulation G)
    (face : OrbitFace cell.rotation.toRotationSystem) :
    cell.rotation.toRotationSystem.D :=
  Classical.choose (exists_dartOrbitFace_eq
    cell.rotation.toRotationSystem face)

@[simp] theorem dartOrbitFace_holeRootDart
    (cell : FramedAnnularCellulation G)
    (face : OrbitFace cell.rotation.toRotationSystem) :
    dartOrbitFace cell.rotation.toRotationSystem (holeRootDart cell face) =
      face :=
  Classical.choose_spec (exists_dartOrbitFace_eq
    cell.rotation.toRotationSystem face)

/-- Cyclic positions on any named cellulation face are equivalent to its
complete dart fiber. -/
def holeFaceDartEquiv (cell : FramedAnnularCellulation G)
    (face : OrbitFace cell.rotation.toRotationSystem) :
    Fin (orbitFaceDarts cell.rotation.toRotationSystem face).card ≃
      {dart // dart ∈ orbitFaceDarts cell.rotation.toRotationSystem face} := by
  let root := holeRootDart cell face
  have hroot : dartOrbitFace cell.rotation.toRotationSystem root = face :=
    dartOrbitFace_holeRootDart cell face
  have horbit : cell.rotation.toRotationSystem.faceOrbit root =
      orbitFaceDarts cell.rotation.toRotationSystem face := by
    rw [← orbitFaceDarts_dartOrbitFace_eq_faceOrbit
      cell.rotation.toRotationSystem root, hroot]
  simpa only [horbit] using
    (faceOrbitDartEquiv cell.rotation.toRotationSystem root)

/-- The actual cyclic position occupied by an ordered inner boundary stub. -/
def innerBoundaryPosition
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (inner : Fin 5) :
    Fin (orbitFaceDarts embedded.RS embedded.cellulation.innerHole).card :=
  (holeFaceDartEquiv embedded.cellulation embedded.cellulation.innerHole).symm
    ⟨innerBoundaryDart data hdata inner,
      (mem_orbitFaceDarts_iff embedded.RS embedded.cellulation.innerHole _).2
        (innerBoundaryDart_on_innerHole embedded hdata inner)⟩

/-- The actual cyclic position occupied by an ordered outer boundary stub. -/
def outerBoundaryPosition
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (outer : Fin outerCount) :
    Fin (orbitFaceDarts embedded.RS embedded.cellulation.outerHole).card :=
  (holeFaceDartEquiv embedded.cellulation embedded.cellulation.outerHole).symm
    ⟨outerBoundaryDart data hdata outer,
      (mem_orbitFaceDarts_iff embedded.RS embedded.cellulation.outerHole _).2
        (outerBoundaryDart_on_outerHole embedded hdata outer)⟩

@[simp] theorem holeFaceDartEquiv_innerBoundaryPosition
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (inner : Fin 5) :
    holeFaceDartEquiv embedded.cellulation embedded.cellulation.innerHole
        (innerBoundaryPosition embedded hdata inner) =
      ⟨innerBoundaryDart data hdata inner,
        (mem_orbitFaceDarts_iff embedded.RS embedded.cellulation.innerHole _).2
          (innerBoundaryDart_on_innerHole embedded hdata inner)⟩ := by
  exact Equiv.apply_symm_apply _ _

@[simp] theorem holeFaceDartEquiv_outerBoundaryPosition
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) (outer : Fin outerCount) :
    holeFaceDartEquiv embedded.cellulation embedded.cellulation.outerHole
        (outerBoundaryPosition embedded hdata outer) =
      ⟨outerBoundaryDart data hdata outer,
        (mem_orbitFaceDarts_iff embedded.RS embedded.cellulation.outerHole _).2
          (outerBoundaryDart_on_outerHole embedded hdata outer)⟩ := by
  exact Equiv.apply_symm_apply _ _

/-- Distinct ordered inner stubs occupy distinct positions on the actual
inner face orbit. -/
theorem innerBoundaryPosition_injective
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) :
    Function.Injective (innerBoundaryPosition embedded hdata) := by
  intro first second hposition
  have hdarts := congrArg Subtype.val <|
    congrArg
      (holeFaceDartEquiv embedded.cellulation embedded.cellulation.innerHole)
      hposition
  have hvertices : data.innerStub first = data.innerStub second := by
    simpa using congrArg (fun dart : G.Dart => dart.fst) hdarts
  exact data.innerStub.injective hvertices

/-- Distinct ordered outer stubs occupy distinct positions on the actual
outer face orbit. -/
theorem outerBoundaryPosition_injective
    {data : AnnularBoundaryData G outerCount}
    (embedded : ClosedWebAnnularEmbedding data)
    (hdata : data.WellFormed) :
    Function.Injective (outerBoundaryPosition embedded hdata) := by
  intro first second hposition
  have hdarts := congrArg Subtype.val <|
    congrArg
      (holeFaceDartEquiv embedded.cellulation embedded.cellulation.outerHole)
      hposition
  have hvertices : data.outerStub first = data.outerStub second := by
    simpa using congrArg (fun dart : G.Dart => dart.fst) hdarts
  exact data.outerStub.injective hvertices

end

end GoertzelV24ClosedWebHoleBoundaryOrder

end Mettapedia.GraphTheory.FourColor
