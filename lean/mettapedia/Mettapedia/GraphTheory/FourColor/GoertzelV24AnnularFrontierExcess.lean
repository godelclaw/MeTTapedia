import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedWebAnnularEmbedding
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedBoundaryCounts

/-!
# The annular-frontier excess identity

This is Addendum XXV, Step 2 in the source route.  An annular frontier has
five inner and `n_out` outer degree-one stubs; the source's vertex count omits
those exposed stub vertices.  Handshaking and Euler's formula therefore give
the exact internal-face and excess identities used to force a long hexagonal
corridor.  The proof below derives both formulas from the literal boundary
data and cellular annular embedding, rather than inserting a curvature budget
as an interface premise.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierExcess

open SimpleGraph
open GoertzelV24ClosedWebBoundaryData
open GoertzelV24ClosedWebAnnularEmbedding
open GoertzelV24FramedAnnularExcess
open GoertzelV24FramedBoundaryCounts
open GoertzelV24FaceOrbitIncidence
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} {outerCount : Nat}

noncomputable section

namespace AnnularFrontierBoundaryCounts

/-- The source's `V` for an open annular frontier: all genuine interior
vertices, with the degree-one boundary stub vertices excluded. -/
def sourceInteriorVertexCount (data : AnnularBoundaryData G outerCount) : Nat :=
  data.interiorVertices.card

/-- The literal boundary and interior vertex sets are a disjoint partition of
the graph's vertices. -/
theorem boundaryStubVertices_disjoint_interiorVertices
    (data : AnnularBoundaryData G outerCount) :
    Disjoint data.boundaryStubVertices data.interiorVertices := by
  rw [Finset.disjoint_left]
  intro vertex hboundary hinterior
  exact (Finset.mem_sdiff.mp hinterior).2 hboundary

/-- The literal boundary and interior vertex sets exhaust the graph. -/
theorem boundaryStubVertices_union_interiorVertices
    (data : AnnularBoundaryData G outerCount) :
    data.boundaryStubVertices ∪ data.interiorVertices = Finset.univ := by
  ext vertex
  simp [AnnularBoundaryData.interiorVertices]

/-- Separate the total graph vertex count into the source's interior count
and the exposed annular-interface vertices. -/
theorem card_vertices_eq_boundaryStubCount_add_sourceInteriorVertexCount
    (data : AnnularBoundaryData G outerCount) :
    Fintype.card V =
      data.boundaryStubVertices.card + sourceInteriorVertexCount data := by
  have hcard := congrArg Finset.card
    (boundaryStubVertices_union_interiorVertices data)
  rw [Finset.card_union_of_disjoint
    (boundaryStubVertices_disjoint_interiorVertices data), Finset.card_univ] at hcard
  simpa [sourceInteriorVertexCount] using hcard.symm

variable [DecidableRel G.Adj]

/-- The exposed inner and outer stubs contribute degree one each. -/
theorem boundaryStubDegreeSum
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed) :
    (∑ vertex ∈ data.boundaryStubVertices, G.degree vertex) =
      data.boundaryStubVertices.card := by
  calc
    (∑ vertex ∈ data.boundaryStubVertices, G.degree vertex) =
        ∑ _vertex ∈ data.boundaryStubVertices, 1 := by
      apply Finset.sum_congr rfl
      intro vertex hboundary
      rw [← incidentEdgeFinset_card_eq_degree]
      simp only [AnnularBoundaryData.boundaryStubVertices, Finset.mem_union]
        at hboundary
      rcases hboundary with hinner | houter
      · rcases (AnnularBoundaryData.mem_innerStubVertices_iff data vertex).1 hinner with
          ⟨inner, hinner⟩
        subst vertex
        exact hdata.inner_stub_degree_one inner
      · rcases (AnnularBoundaryData.mem_outerStubVertices_iff data vertex).1 houter with
          ⟨outer, houter⟩
        subst vertex
        exact hdata.outer_stub_degree_one outer
    _ = data.boundaryStubVertices.card := by simp

/-- All non-boundary vertices of the annular frontier are cubic. -/
theorem interiorDegreeSum
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed) :
    (∑ vertex ∈ data.interiorVertices, G.degree vertex) =
      3 * data.interiorVertices.card := by
  calc
    (∑ vertex ∈ data.interiorVertices, G.degree vertex) =
        ∑ _vertex ∈ data.interiorVertices, 3 := by
      apply Finset.sum_congr rfl
      intro vertex hinterior
      have hnotBoundary := (Finset.mem_sdiff.mp hinterior).2
      rw [← incidentEdgeFinset_card_eq_degree]
      apply hdata.cubic_elsewhere vertex
      · intro inner heq
        apply hnotBoundary
        apply Finset.mem_union_left
        exact (AnnularBoundaryData.mem_innerStubVertices_iff data vertex).2
          ⟨inner, heq.symm⟩
      · intro outer heq
        apply hnotBoundary
        apply Finset.mem_union_right
        exact (AnnularBoundaryData.mem_outerStubVertices_iff data vertex).2
          ⟨outer, heq.symm⟩
    _ = 3 * data.interiorVertices.card := by simp [Nat.mul_comm]

/-- Exact degree accounting for a literal annular frontier.  Each exposed
degree-one stub has deficiency two relative to a cubic vertex. -/
theorem twice_edgeCount_add_twice_boundaryStubCount
    (data : AnnularBoundaryData G outerCount) (hdata : data.WellFormed) :
    2 * G.edgeFinset.card + 2 * data.boundaryStubVertices.card =
      3 * Fintype.card V := by
  have hdisjoint := boundaryStubVertices_disjoint_interiorVertices data
  have hpartition := boundaryStubVertices_union_interiorVertices data
  have hdegreePartition :
      (∑ vertex : V, G.degree vertex) =
        (∑ vertex ∈ data.boundaryStubVertices, G.degree vertex) +
          ∑ vertex ∈ data.interiorVertices, G.degree vertex := by
    rw [← hpartition, Finset.sum_union hdisjoint]
  have hhandshake :
      (∑ vertex : V, G.degree vertex) = 2 * G.edgeFinset.card := by
    simpa using G.sum_degrees_eq_twice_card_edges
  rw [boundaryStubDegreeSum data hdata, interiorDegreeSum data hdata]
    at hdegreePartition
  have hvertexCount :=
    card_vertices_eq_boundaryStubCount_add_sourceInteriorVertexCount data
  unfold sourceInteriorVertexCount at hvertexCount
  omega

end AnnularFrontierBoundaryCounts

namespace AnnularFrontierEmbeddingExcess

variable [DecidableRel G.Adj] {data : AnnularBoundaryData G outerCount}

/-- A dart occurrence over one of the five literal inner-interface edges. -/
abbrev InnerBoundaryEdgeDart (embedded : ClosedWebAnnularEmbedding data) :=
  Σ inner : Fin 5,
    {dart // dart ∈ embedded.cellulation.rotation.toRotationSystem.dartsOn
      (data.innerBoundaryEdge inner)}

/-- A dart occurrence over one literal outer-interface edge. -/
abbrev OuterBoundaryEdgeDart (embedded : ClosedWebAnnularEmbedding data) :=
  Σ outer : Fin outerCount,
    {dart // dart ∈ embedded.cellulation.rotation.toRotationSystem.dartsOn
      (data.outerBoundaryEdge outer)}

/-- The exposed boundary darts, retaining the inner/outer interface side.
Keeping occurrences rather than just edges is essential: each edge contributes
two darts to a facial perimeter. -/
abbrev BoundaryEdgeDart (embedded : ClosedWebAnnularEmbedding data) :=
  InnerBoundaryEdgeDart embedded ⊕ OuterBoundaryEdgeDart embedded

/-- A dart occurrence on either of the two distinguished hole walks. -/
abbrev HoleDart (embedded : ClosedWebAnnularEmbedding data) :=
  Σ face : embedded.cellulation.holeFaces,
    {dart // dart ∈ orbitFaceDarts
      embedded.cellulation.rotation.toRotationSystem face.1}

/-- The literal embedding sends every exposed boundary-dart occurrence to its
designated hole occurrence. -/
noncomputable def boundaryEdgeDartToHoleDart
    (embedded : ClosedWebAnnularEmbedding data) :
    BoundaryEdgeDart embedded → HoleDart embedded :=
  fun item => match item with
    | Sum.inl innerItem =>
      ⟨⟨embedded.cellulation.innerHole, by
          simp [GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.holeFaces]⟩,
        ⟨innerItem.2.1, by
          rw [mem_orbitFaceDarts_iff]
          exact embedded.innerBoundaryEdgeDarts_on_innerHole
            innerItem.1 innerItem.2.1 innerItem.2.2⟩⟩
    | Sum.inr outerItem =>
      ⟨⟨embedded.cellulation.outerHole, by
          simp [GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.holeFaces]⟩,
        ⟨outerItem.2.1, by
          rw [mem_orbitFaceDarts_iff]
          exact embedded.outerBoundaryEdgeDarts_on_outerHole
            outerItem.1 outerItem.2.1 outerItem.2.2⟩⟩

/-- Different literal boundary-dart occurrences remain different on the
two hole walks.  The cross-side case uses the source interface's disjoint
edge embeddings, so no perimeter contribution is silently identified. -/
theorem boundaryEdgeDartToHoleDart_injective
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed) :
    Function.Injective (boundaryEdgeDartToHoleDart embedded) := by
  intro left right heq
  cases left with
  | inl left =>
    cases right with
    | inl right =>
      have hdart : left.2.1 = right.2.1 := by
        simpa [boundaryEdgeDartToHoleDart] using
          congrArg (fun item : HoleDart embedded => item.2.1) heq
      have hedge : data.innerBoundaryEdge left.1 = data.innerBoundaryEdge right.1 := by
        have hleft :=
          (embedded.cellulation.rotation.toRotationSystem.mem_dartsOn).1 left.2.2
        have hright :=
          (embedded.cellulation.rotation.toRotationSystem.mem_dartsOn).1 right.2.2
        exact hleft.symm.trans ((congrArg
          embedded.cellulation.rotation.toRotationSystem.edgeOf hdart).trans hright)
      rcases left with ⟨leftInner, leftDart⟩
      rcases right with ⟨rightInner, rightDart⟩
      have hinner : leftInner = rightInner := data.innerBoundaryEdge.injective hedge
      subst rightInner
      have hdart' : leftDart = rightDart := Subtype.ext hdart
      subst rightDart
      rfl
    | inr right =>
      have hdart : left.2.1 = right.2.1 := by
        simpa [boundaryEdgeDartToHoleDart] using
          congrArg (fun item : HoleDart embedded => item.2.1) heq
      have hedge : data.innerBoundaryEdge left.1 = data.outerBoundaryEdge right.1 := by
        have hleft :=
          (embedded.cellulation.rotation.toRotationSystem.mem_dartsOn).1 left.2.2
        have hright :=
          (embedded.cellulation.rotation.toRotationSystem.mem_dartsOn).1 right.2.2
        exact hleft.symm.trans ((congrArg
          embedded.cellulation.rotation.toRotationSystem.edgeOf hdart).trans hright)
      exact (hdata.inner_outer_edge_disjoint left.1 right.1 hedge).elim
  | inr left =>
    cases right with
    | inl right =>
      have hdart : left.2.1 = right.2.1 := by
        simpa [boundaryEdgeDartToHoleDart] using
          congrArg (fun item : HoleDart embedded => item.2.1) heq
      have hedge : data.outerBoundaryEdge left.1 = data.innerBoundaryEdge right.1 := by
        have hleft :=
          (embedded.cellulation.rotation.toRotationSystem.mem_dartsOn).1 left.2.2
        have hright :=
          (embedded.cellulation.rotation.toRotationSystem.mem_dartsOn).1 right.2.2
        exact hleft.symm.trans ((congrArg
          embedded.cellulation.rotation.toRotationSystem.edgeOf hdart).trans hright)
      exact (hdata.inner_outer_edge_disjoint right.1 left.1 hedge.symm).elim
    | inr right =>
      have hdart : left.2.1 = right.2.1 := by
        simpa [boundaryEdgeDartToHoleDart] using
          congrArg (fun item : HoleDart embedded => item.2.1) heq
      have hedge : data.outerBoundaryEdge left.1 = data.outerBoundaryEdge right.1 := by
        have hleft :=
          (embedded.cellulation.rotation.toRotationSystem.mem_dartsOn).1 left.2.2
        have hright :=
          (embedded.cellulation.rotation.toRotationSystem.mem_dartsOn).1 right.2.2
        exact hleft.symm.trans ((congrArg
          embedded.cellulation.rotation.toRotationSystem.edgeOf hdart).trans hright)
      rcases left with ⟨leftOuter, leftDart⟩
      rcases right with ⟨rightOuter, rightDart⟩
      have houter : leftOuter = rightOuter := data.outerBoundaryEdge.injective hedge
      subst rightOuter
      have hdart' : leftDart = rightDart := Subtype.ext hdart
      subst rightDart
      rfl

/-- The exposed boundary contributes exactly two dart occurrences per stub. -/
theorem card_boundaryEdgeDart
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed) :
    Fintype.card (BoundaryEdgeDart embedded) =
      2 * data.boundaryStubVertices.card := by
  have hinner : Fintype.card (InnerBoundaryEdgeDart embedded) = 10 := by
    rw [Fintype.card_sigma]
    calc
      (∑ inner : Fin 5,
          Fintype.card {dart // dart ∈
            embedded.cellulation.rotation.toRotationSystem.dartsOn
              (data.innerBoundaryEdge inner)}) =
          ∑ _inner : Fin 5, 2 := by
        apply Finset.sum_congr rfl
        intro inner _
        rw [Fintype.card_coe,
          embedded.cellulation.rotation.toRotationSystem.dartsOn_card_two]
      _ = 10 := by norm_num
  have houter : Fintype.card (OuterBoundaryEdgeDart embedded) =
      2 * outerCount := by
    rw [Fintype.card_sigma]
    calc
      (∑ outer : Fin outerCount,
          Fintype.card {dart // dart ∈
            embedded.cellulation.rotation.toRotationSystem.dartsOn
              (data.outerBoundaryEdge outer)}) =
          ∑ _outer : Fin outerCount, 2 := by
        apply Finset.sum_congr rfl
        intro outer _
        rw [Fintype.card_coe,
          embedded.cellulation.rotation.toRotationSystem.dartsOn_card_two]
      _ = 2 * outerCount := by simp [Nat.mul_comm]
  rw [Fintype.card_sum, hinner, houter,
    AnnularBoundaryData.boundaryStubVertices_card data hdata]
  omega

/-- The subtype of all hole-dart occurrences has exactly the total hole
perimeter as its cardinality. -/
theorem card_holeDart (embedded : ClosedWebAnnularEmbedding data) :
    Fintype.card (HoleDart embedded) = embedded.cellulation.holePerimeter := by
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
      simp only [GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.faceLength]
      rw [Finset.univ_eq_attach]
      exact Finset.sum_attach embedded.cellulation.holeFaces
        (fun face => (orbitFaceDarts
          embedded.cellulation.rotation.toRotationSystem face).card)

/-- Every literal boundary stub supplies its two distinct facial-dart
occurrences to the designated holes.  This derives, rather than assumes, the
nonnegative surplus condition in Addendum XXV. -/
theorem twice_boundaryStubCount_le_holePerimeter
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed) :
    2 * data.boundaryStubVertices.card ≤ embedded.cellulation.holePerimeter := by
  have hle := Fintype.card_le_of_injective
    (boundaryEdgeDartToHoleDart embedded)
    (boundaryEdgeDartToHoleDart_injective embedded hdata)
  rw [card_boundaryEdgeDart embedded hdata, card_holeDart embedded] at hle
  exact hle

/-- The source's `rho`: the actual extra perimeter of the two designated
hole walks beyond the two dart occurrences supplied by each exposed stub. -/
noncomputable def boundarySurplus (embedded : ClosedWebAnnularEmbedding data) : Nat :=
  embedded.cellulation.holePerimeter - 2 * data.boundaryStubVertices.card

/-- The literal embedded frontier has its hole perimeter expressed as the
baseline plus its canonically defined nonnegative surplus. -/
theorem holePerimeter_eq_twice_boundaryStubCount_add_boundarySurplus
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed) :
    embedded.cellulation.holePerimeter =
      2 * data.boundaryStubVertices.card + boundarySurplus embedded := by
  unfold boundarySurplus
  have hbaseline := twice_boundaryStubCount_le_holePerimeter embedded hdata
  omega

/-- Euler plus the literal annular boundary degrees.  This is the exact
source convention: after excluding the `5 + n_out` degree-one stubs, the
internal-face count is `(V - 5 - n_out) / 2`. -/
theorem twice_interiorFaceCount_add_twice_boundaryStubCount
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed) :
    2 * embedded.cellulation.interiorFaces.card +
        2 * data.boundaryStubVertices.card =
      Fintype.card V := by
  have hdegree :=
    AnnularFrontierBoundaryCounts.twice_edgeCount_add_twice_boundaryStubCount data hdata
  have hfaces := embedded.cellulation.interiorFaces_card_add_two
  have heuler := embedded.cellulation.euler
  rw [GoertzelV24FramedAnnularExcess.FramedAnnularCellulation.edgeSet_card_eq_edgeFinset_card] at heuler
  omega

/-- Addendum XXV's internal-face formula in the source's vertex convention. -/
theorem twice_interiorFaceCount_add_five_add_outerCount_eq_sourceInteriorVertexCount
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed) :
    2 * embedded.cellulation.interiorFaces.card + 5 + outerCount =
      AnnularFrontierBoundaryCounts.sourceInteriorVertexCount data := by
  have hfaces := twice_interiorFaceCount_add_twice_boundaryStubCount embedded hdata
  have hvertices :=
    AnnularFrontierBoundaryCounts.card_vertices_eq_boundaryStubCount_add_sourceInteriorVertexCount
      data
  rw [AnnularBoundaryData.boundaryStubVertices_card data hdata] at hfaces hvertices
  omega

/-- Addendum XXV, Step 2: the exact annular excess identity.  The only
geometric quantity left visible is `rho`, the actual excess perimeter of the
two hole faces beyond their two darts per exposed stub. -/
theorem interiorExcess_eq_ten_add_twice_outerCount_sub_of_holePerimeter
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed)
    (rho : Nat)
    (hhole : embedded.cellulation.holePerimeter =
      2 * data.boundaryStubVertices.card + rho) :
    embedded.cellulation.interiorExcess = 10 + 2 * outerCount - rho := by
  have hdegree :=
    AnnularFrontierBoundaryCounts.twice_edgeCount_add_twice_boundaryStubCount data hdata
  have hfaceCount :=
    twice_interiorFaceCount_add_twice_boundaryStubCount embedded hdata
  have hboundaryCard := AnnularBoundaryData.boundaryStubVertices_card data hdata
  have hfaceLengths := embedded.cellulation.sum_interiorFaceLength_add_holePerimeter
  have hfaceLengthsInt :
      (∑ face ∈ embedded.cellulation.interiorFaces,
          (embedded.cellulation.faceLength face : Int)) +
          embedded.cellulation.holePerimeter =
        2 * G.edgeFinset.card := by
    exact_mod_cast hfaceLengths
  unfold FramedAnnularCellulation.interiorExcess
  change Finset.sum embedded.cellulation.interiorFaces
    (fun face => (embedded.cellulation.faceLength face : Int) - 6) = _
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, nsmul_eq_mul]
  omega

/-- Canonical Addendum XXV Step 2 form: the literal annular embedding itself
supplies the perimeter baseline, so `rho` is the actual nonnegative boundary
surplus rather than a separately assumed geometric quantity. -/
theorem interiorExcess_eq_ten_add_twice_outerCount_sub_boundarySurplus
    (embedded : ClosedWebAnnularEmbedding data) (hdata : data.WellFormed) :
    embedded.cellulation.interiorExcess =
      10 + 2 * outerCount - boundarySurplus embedded := by
  apply interiorExcess_eq_ten_add_twice_outerCount_sub_of_holePerimeter
    embedded hdata (boundarySurplus embedded)
  exact holePerimeter_eq_twice_boundaryStubCount_add_boundarySurplus
    embedded hdata

end AnnularFrontierEmbeddingExcess

end

end GoertzelV24AnnularFrontierExcess

end Mettapedia.GraphTheory.FourColor
