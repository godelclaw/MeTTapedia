import Mettapedia.GraphTheory.FourColor.GoertzelV24ConnectedVertexSideEdgeShore
import Mettapedia.GraphTheory.FourColor.GoertzelV24FramedCorridorSerialPrefixVertexSide

/-!
# Laminarity of literal source-corridor prefixes

The literal source Cells are accumulated in their source order.  Consequently
their vertex-side prefixes are monotone without any geometric or colouring
hypothesis beyond those used to construct the Cells.  If the next Cell
contains one vertex not already present, the next prefix is strictly larger.
The canonical incident-edge shores inherit the same monotonicity.

This separates the easy order theory from the remaining source-corridor
problem: proving fresh material, connected complementary sides, and a uniform
bound on the true crossing frontier.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FramedCorridorSerialPrefixLaminarity

open GoertzelV24ConnectedVertexSideEdgeShore
open GoertzelV24FaceDualConnectedness
open GoertzelV24FaceOrbitIncidence
open GoertzelV24FramedTrail
open GoertzelV24FramedTrail.SourceTrail
open GoertzelV24FramedTrail.SourceTrail.AnnularEmbedding
open GoertzelV24OrbitFaceTwoSided
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

local instance framedCorridorSerialPrefixLaminarityEdgeSetFintype :
    Fintype G.edgeSet :=
  SimpleGraph.fintypeEdgeSet G

local instance framedCorridorSerialPrefixLaminarityEdgeSetDecidableEq :
    DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Enlarging the source-index bound enlarges the cumulative literal Cell
vertex side. -/
theorem sourceCorridorSerialPrefixVertexSide_mono
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    {first second : Nat} (hfirstSecond : first ≤ second) :
    sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
        htwoSided hunique first ⊆
      sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
        htwoSided hunique second := by
  intro vertex hvertex
  simp only [sourceCorridorSerialPrefixVertexSide, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and] at hvertex ⊢
  obtain ⟨offset, hoffset, hvertexCell⟩ := hvertex
  exact ⟨offset, hoffset.trans_le hfirstSecond, hvertexCell⟩

/-- A vertex in the next literal Cell that is absent from the old prefix
makes the consecutive prefix inclusion strict. -/
theorem sourceCorridorSerialPrefixVertexSide_ssubset_succ_of_fresh
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (cut : Nat) (hcut : cut < blockLength - 3)
    (vertex : V)
    (hvertexCell : vertex ∈
      sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
        htwoSided hunique ⟨cut, hcut⟩)
    (hvertexFresh : vertex ∉
      sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
        htwoSided hunique cut) :
    sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
        htwoSided hunique cut ⊂
      sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
        htwoSided hunique (cut + 1) := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨sourceCorridorSerialPrefixVertexSide_mono realization hcubic
    hrotation htwoSided hunique (Nat.le_succ cut), ?_⟩
  intro heq
  apply hvertexFresh
  rw [heq]
  simp only [sourceCorridorSerialPrefixVertexSide, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨cut, hcut⟩, Nat.lt_succ_self cut, hvertexCell⟩

/-- The canonical incident-edge shores of two ordered literal prefixes are
ordered in the same direction. -/
theorem sourceCorridorSerialPrefixIncidentShore_mono
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    {first second : Nat} (hfirstSecond : first ≤ second) :
    incidentEdgeShore G (fun vertex => vertex ∈
        sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
          htwoSided hunique first) ⊆
      incidentEdgeShore G (fun vertex => vertex ∈
        sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
          htwoSided hunique second) :=
  incidentEdgeShore_mono
    (fun _ hvertex => sourceCorridorSerialPrefixVertexSide_mono realization
      hcubic hrotation htwoSided hunique hfirstSecond hvertex)

/-- If the next Cell contains an endpoint of an edge not already assigned to
the old incident-edge shore, then the consecutive incident-edge shores are
strictly ordered. -/
theorem sourceCorridorSerialPrefixIncidentShore_ssubset_succ_of_fresh_edge
    {source : SourceTrail G}
    {embedded : source.AnnularEmbedding} {blockLength : Nat}
    (realization : BoundaryCleanCorridorRealization embedded blockLength)
    (hcubic : embedded.cellulation.rotation.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic
      embedded.cellulation.rotation.toRotationSystem)
    (htwoSided : OrbitFacesTwoSided
      embedded.cellulation.rotation.toRotationSystem)
    (hunique : PairwiseUniqueSharedInteriorEdges
      (orbitFaceBoundary embedded.cellulation.rotation.toRotationSystem)
      (Finset.univ : Finset
        (OrbitFace embedded.cellulation.rotation.toRotationSystem)))
    (cut : Nat) (hcut : cut < blockLength - 3)
    (vertex : V) (edge : G.edgeSet)
    (hvertexEdge : vertex ∈ (edge : Sym2 V))
    (hvertexCell : vertex ∈
      sourceSlabLiteralCellVertexSideAt realization hcubic hrotation
        htwoSided hunique ⟨cut, hcut⟩)
    (hedgeFresh : edge ∉
      incidentEdgeShore G (fun vertex => vertex ∈
        sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
          htwoSided hunique cut)) :
    incidentEdgeShore G (fun vertex => vertex ∈
        sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
          htwoSided hunique cut) ⊂
      incidentEdgeShore G (fun vertex => vertex ∈
        sourceCorridorSerialPrefixVertexSide realization hcubic hrotation
          htwoSided hunique (cut + 1)) := by
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨sourceCorridorSerialPrefixIncidentShore_mono realization hcubic
    hrotation htwoSided hunique (Nat.le_succ cut), ?_⟩
  intro heq
  apply hedgeFresh
  rw [heq]
  apply (mem_incidentEdgeShore_iff _ _).2
  refine ⟨vertex, hvertexEdge, ?_⟩
  simp only [sourceCorridorSerialPrefixVertexSide, Finset.mem_biUnion,
    Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨⟨cut, hcut⟩, Nat.lt_succ_self cut, hvertexCell⟩

end

end GoertzelV24FramedCorridorSerialPrefixLaminarity

end Mettapedia.GraphTheory.FourColor
