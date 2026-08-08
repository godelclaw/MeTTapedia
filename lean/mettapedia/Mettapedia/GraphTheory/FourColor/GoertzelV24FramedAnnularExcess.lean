import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedBoundaryCounts
import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceOrbitIncidence
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

/-!
# Framed annular Euler and excess identities

This is the face-counting half of playbook flag L9.  The manuscript counts
only non-stub vertices in `V` and regards each missing incidence as a boundary
foot.  The graph-side framed model instead retains the two missing-edge
endpoints as degree-two defect vertices.  Consequently, if `s` is the number
of frozen degree-one interface stubs, its total boundary-foot count is
`b = s + 2`, and the manuscript's annular constant `2b` becomes `4 + 2s`.

Face length is counted by facial darts, not by the support of boundary edges;
this correctly counts a bridge twice on one facial walk.  The two hole faces
and the spherical Euler equation are explicit cellulation data.  A separate
formation-to-graph theorem must construct this data from the source's two
container curves; no such geometric construction is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedAnnularExcess

open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedTrail
open GoertzelV24FramedBoundaryCounts
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A graph-backed cellular embedding on the sphere with two distinguished
hole faces.  Removing those two faces leaves the annular internal cells used
by the manuscript. -/
structure FramedAnnularCellulation (G : SimpleGraph V)
    [Fintype V] [DecidableEq V] [DecidableRel G.Adj] where
  rotation : SimpleGraphDartRotation.Data G
  connected : G.Connected
  vertexRotation_cyclic :
    ∀ vertex : V,
      rotation.vertexRotation.IsCycleOn
        {dart : G.Dart | dart.fst = vertex}
  innerHole : OrbitFace rotation.toRotationSystem
  outerHole : OrbitFace rotation.toRotationSystem
  holes_ne : innerHole ≠ outerHole
  euler :
    (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace rotation.toRotationSystem) = 2

namespace FramedAnnularCellulation

omit [DecidableEq V] in
/-- The subtype cardinality of the graph's edge set agrees with its canonical
finite edge enumeration. -/
theorem edgeSet_card_eq_edgeFinset_card :
    Fintype.card G.edgeSet = G.edgeFinset.card :=
  G.card_edgeSet

/-- The two complementary hole faces. -/
noncomputable def holeFaces (cell : FramedAnnularCellulation G) :
    Finset (OrbitFace cell.rotation.toRotationSystem) :=
  {cell.innerHole, cell.outerHole}

/-- All facial cycles other than the two hole faces. -/
noncomputable def interiorFaces (cell : FramedAnnularCellulation G) :
    Finset (OrbitFace cell.rotation.toRotationSystem) :=
  Finset.univ \ cell.holeFaces

/-- Facial length with multiplicity, measured by the darts in the face
orbit. -/
noncomputable def faceLength (cell : FramedAnnularCellulation G)
    (face : OrbitFace cell.rotation.toRotationSystem) : Nat :=
  (orbitFaceDarts cell.rotation.toRotationSystem face).card

/-- Total dart perimeter of the two hole faces. -/
noncomputable def holePerimeter (cell : FramedAnnularCellulation G) : Nat :=
  ∑ face ∈ cell.holeFaces, cell.faceLength face

/-- The manuscript's `rho`: hole perimeter beyond the twice-per-frozen-stub
baseline.  Its geometric use is guarded by the explicit baseline inequality
below. -/
noncomputable def boundarySurplus (cell : FramedAnnularCellulation G)
    (data : FramedTrailData G) : Nat :=
  cell.holePerimeter - 2 * data.frozenInterfaceStubVertices.card

/-- Signed total excess of the internal faces over hexagons. -/
noncomputable def interiorExcess (cell : FramedAnnularCellulation G) : Int :=
  Finset.sum cell.interiorFaces
    (fun face => (cell.faceLength face : Int) - 6)

theorem holeFaces_card (cell : FramedAnnularCellulation G) :
    cell.holeFaces.card = 2 := by
  simp [holeFaces, cell.holes_ne]

theorem interiorFaces_disjoint_holeFaces
    (cell : FramedAnnularCellulation G) :
    Disjoint cell.interiorFaces cell.holeFaces := by
  rw [Finset.disjoint_left]
  simp [interiorFaces]

theorem interiorFaces_union_holeFaces
    (cell : FramedAnnularCellulation G) :
    cell.interiorFaces ∪ cell.holeFaces = Finset.univ := by
  simp [interiorFaces]

/-- The two hole faces account for exactly two of the sphere's facial
cycles. -/
theorem interiorFaces_card_add_two
    (cell : FramedAnnularCellulation G) :
    cell.interiorFaces.card + 2 =
      Fintype.card (OrbitFace cell.rotation.toRotationSystem) := by
  have hcard := congrArg Finset.card (cell.interiorFaces_union_holeFaces)
  rw [Finset.card_union_of_disjoint cell.interiorFaces_disjoint_holeFaces,
    cell.holeFaces_card, Finset.card_univ] at hcard
  exact hcard

/-- Facial dart orbits partition all graph darts, hence all face lengths sum
to twice the number of graph edges. -/
theorem sum_faceLength_eq_twice_edgeCount
    (cell : FramedAnnularCellulation G) :
    ∑ face : OrbitFace cell.rotation.toRotationSystem,
        cell.faceLength face = 2 * G.edgeFinset.card := by
  calc
    ∑ face : OrbitFace cell.rotation.toRotationSystem,
        cell.faceLength face =
      Fintype.card cell.rotation.toRotationSystem.D := by
        exact sum_card_orbitFaceDarts_eq_card_darts
          cell.rotation.toRotationSystem
    _ = 2 * Fintype.card G.edgeSet := by
      exact cell.rotation.toRotationSystem.card_darts_eq_twice_card_edges
    _ = 2 * G.edgeFinset.card := by
      rw [edgeSet_card_eq_edgeFinset_card]

/-- The all-face length sum splits exactly into internal faces and the two
hole perimeters. -/
theorem sum_interiorFaceLength_add_holePerimeter
    (cell : FramedAnnularCellulation G) :
    (∑ face ∈ cell.interiorFaces, cell.faceLength face) +
        cell.holePerimeter =
      2 * G.edgeFinset.card := by
  rw [← cell.sum_faceLength_eq_twice_edgeCount]
  change (∑ face ∈ cell.interiorFaces, cell.faceLength face) +
      (∑ face ∈ cell.holeFaces, cell.faceLength face) =
    ∑ face ∈ (Finset.univ :
      Finset (OrbitFace cell.rotation.toRotationSystem)), cell.faceLength face
  rw [← Finset.sum_union cell.interiorFaces_disjoint_holeFaces,
    cell.interiorFaces_union_holeFaces]

/-- Once every frozen interface stub contributes its two boundary-dart
incidences, the hole perimeter is the baseline plus its nonnegative surplus.
-/
theorem holePerimeter_eq_twice_frozenStubCount_add_boundarySurplus
    (cell : FramedAnnularCellulation G) (data : FramedTrailData G)
    (hbaseline :
      2 * data.frozenInterfaceStubVertices.card ≤ cell.holePerimeter) :
    cell.holePerimeter =
      2 * data.frozenInterfaceStubVertices.card +
        cell.boundarySurplus data := by
  unfold boundarySurplus
  omega

/-- Euler's equation plus the framed degree count gives the manuscript's
internal-face formula in graph coordinates. -/
theorem twice_interiorFaceCount_add_two_add_twice_frozenStubCount
    (cell : FramedAnnularCellulation G)
    (data : FramedTrailData G) (hdata : data.WellFormed) :
    2 * cell.interiorFaces.card + 2 +
        2 * data.frozenInterfaceStubVertices.card =
      Fintype.card V := by
  have hdegree :=
    twice_edgeCount_add_two_add_twice_frozenStubCount data hdata
  have hfaces := cell.interiorFaces_card_add_two
  have heuler := cell.euler
  rw [edgeSet_card_eq_edgeFinset_card] at heuler
  omega

/-- Source-form L9 excess identity.  If the two hole walks have total dart
perimeter `2s + rho`, where `s` is the number of frozen degree-one interface
stubs, then the internal excess is exactly `4 + 2s - rho`.  The extra `4`
is the contribution of the two degree-two missing-edge defects. -/
theorem interiorExcess_eq_four_add_twice_frozenStubCount_sub_of_holePerimeter
    (cell : FramedAnnularCellulation G)
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (rho : Nat)
    (hhole : cell.holePerimeter =
      2 * data.frozenInterfaceStubVertices.card + rho) :
    cell.interiorExcess =
      4 + 2 * data.frozenInterfaceStubVertices.card - rho := by
  have hdegree :=
    twice_edgeCount_add_two_add_twice_frozenStubCount data hdata
  have hfaceCount :=
    cell.twice_interiorFaceCount_add_two_add_twice_frozenStubCount data hdata
  have hfaceLengths := cell.sum_interiorFaceLength_add_holePerimeter
  have hfaceLengthsInt :
      (∑ face ∈ cell.interiorFaces,
          (cell.faceLength face : Int)) + cell.holePerimeter =
        2 * G.edgeFinset.card := by
    exact_mod_cast hfaceLengths
  unfold interiorExcess
  change Finset.sum cell.interiorFaces
    (fun face => (cell.faceLength face : Int) - 6) = _
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  omega

/-- Canonical L9 form, with `rho` defined from the two actual hole walks.
The only remaining perimeter premise is the source-geometric baseline that
each frozen degree-one interface stub lies on a hole face. -/
theorem interiorExcess_eq_four_add_twice_frozenStubCount_sub_boundarySurplus
    (cell : FramedAnnularCellulation G)
    (data : FramedTrailData G) (hdata : data.WellFormed)
    (hbaseline :
      2 * data.frozenInterfaceStubVertices.card ≤ cell.holePerimeter) :
    cell.interiorExcess =
      4 + 2 * data.frozenInterfaceStubVertices.card -
        cell.boundarySurplus data := by
  apply cell.interiorExcess_eq_four_add_twice_frozenStubCount_sub_of_holePerimeter
    data hdata (cell.boundarySurplus data)
  exact cell.holePerimeter_eq_twice_frozenStubCount_add_boundarySurplus
    data hbaseline

end FramedAnnularCellulation

end GoertzelV24FramedAnnularExcess

end Mettapedia.GraphTheory.FourColor
