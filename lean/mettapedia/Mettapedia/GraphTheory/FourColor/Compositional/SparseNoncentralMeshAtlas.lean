import Mettapedia.GraphTheory.FourColor.Compositional.DeletionAtlasPath
import Mettapedia.GraphTheory.FourColor.Compositional.MeshJunctionAlternatingGeometry
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshColoringAtlas

/-!
# A sparse noncentral deletion atlas on an ordered mesh row

Choose nine internal row junctions with one unused branch column between
successive choices.  At each junction a perfect matching can use at most one
of the incoming and outgoing arms, so choose a noncentral arm.  The spacing
makes the first endpoint maps and the second endpoint maps injective even
though the incoming/outgoing choice depends on the matching.

Consequently the nine chosen adjacent-pair deletions cover every ambient edge
and every adjacent pair of ambient edges.  This is the geometric input needed
to run the finite common-core path argument without retaining a central-edge
alternative at any selected site.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.SparseNoncentralMeshAtlas

open AlternatingSiteGeometry
open DeletionAtlasPath
open MeshJunctionAlternatingGeometry
open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairColoringAtlas.PairDeletionColoringFamily
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshColoringAtlas
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a : Nat}

variable
  (rotation : Data G)
  (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
  (ordered : OrderedInjectiveMesh
    (toMultigraph rotation.toRotationSystem) a 20)

/-- Nine internal junctions, with one unused branch column between successive
selected junctions. -/
def sparseJunctionColumn (index : Fin 9) : Fin 18 :=
  ⟨2 * index.val, by omega⟩

/-- Successive sparse junctions are separated by at least two row-step
positions.  The proof uses the unused branch column between them. -/
theorem sparse_branchPosition_add_two_le
    (row : Fin a) {first second : Fin 9} (hlt : first < second) :
    (internalRowPosition rotation ordered row
        (sparseJunctionColumn first)).val + 2 ≤
      (internalRowPosition rotation ordered row
        (sparseJunctionColumn second)).val := by
  let middle : Fin 20 := ⟨2 * first.val + 2, by omega⟩
  have hleft :
      internalColumn (sparseJunctionColumn first) < middle := by
    apply Fin.mk_lt_mk.mpr
    simp [sparseJunctionColumn]
  have hright :
      middle < internalColumn (sparseJunctionColumn second) := by
    apply Fin.mk_lt_mk.mpr
    simp [sparseJunctionColumn]
    omega
  have hfirstMiddle := ordered.rowBranchPosition_strictMono row hleft
  have hmiddleSecond := ordered.rowBranchPosition_strictMono row hright
  change
    (internalRowPosition rotation ordered row
        (sparseJunctionColumn first)).val <
      (ordered.rowBranchPosition row middle).val at hfirstMiddle
  change
    (ordered.rowBranchPosition row middle).val <
      (internalRowPosition rotation ordered row
        (sparseJunctionColumn second)).val at hmiddleSecond
  omega

/-- At a sparse junction, choose the outgoing arm when it is noncentral and
the incoming arm otherwise. -/
def selectedRowStep
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a) (index : Fin 9) :
    Fin ((ordered.toMesh.row row).len) :=
  if minimizer.pairing.partner
        (globalFirstVertex rotation ordered
          (outgoingGlobalStep rotation ordered row
            (sparseJunctionColumn index))) =
      globalSecondVertex rotation ordered
        (outgoingGlobalStep rotation ordered row
          (sparseJunctionColumn index)) then
    incomingRowStep rotation ordered row (sparseJunctionColumn index)
  else
    outgoingRowStep rotation ordered row (sparseJunctionColumn index)

/-- The selected arm as a globally indexed row step. -/
def selectedGlobalStep
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a) (index : Fin 9) : GlobalMeshStep rotation ordered :=
  .inl ⟨row, selectedRowStep rotation ordered minimizer row index⟩

/-- The selected step is either the incoming or outgoing arm of its sparse
junction. -/
theorem selectedRowStep_eq_incoming_or_outgoing
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a) (index : Fin 9) :
    selectedRowStep rotation ordered minimizer row index =
        incomingRowStep rotation ordered row (sparseJunctionColumn index) ∨
      selectedRowStep rotation ordered minimizer row index =
        outgoingRowStep rotation ordered row (sparseJunctionColumn index) := by
  by_cases hcentral : minimizer.pairing.partner
        (globalFirstVertex rotation ordered
          (outgoingGlobalStep rotation ordered row
            (sparseJunctionColumn index))) =
      globalSecondVertex rotation ordered
        (outgoingGlobalStep rotation ordered row
          (sparseJunctionColumn index))
  · exact Or.inl (by simp [selectedRowStep, hcentral])
  · exact Or.inr (by simp [selectedRowStep, hcentral])

/-- The matching does not use the selected arm. -/
theorem selectedGlobalStep_noncentral
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a) (index : Fin 9) :
    minimizer.pairing.partner
        (globalFirstVertex rotation ordered
          (selectedGlobalStep rotation ordered minimizer row index)) ≠
      globalSecondVertex rotation ordered
        (selectedGlobalStep rotation ordered minimizer row index) := by
  by_cases hcentral : minimizer.pairing.partner
        (globalFirstVertex rotation ordered
          (outgoingGlobalStep rotation ordered row
            (sparseJunctionColumn index))) =
      globalSecondVertex rotation ordered
        (outgoingGlobalStep rotation ordered row
          (sparseJunctionColumn index))
  · have hincoming : minimizer.pairing.partner
          (globalFirstVertex rotation ordered
            (incomingGlobalStep rotation ordered row
              (sparseJunctionColumn index))) ≠
        globalSecondVertex rotation ordered
          (incomingGlobalStep rotation ordered row
            (sparseJunctionColumn index)) := by
      intro hbad
      exact not_both_arms_central rotation ordered minimizer.pairing row
        (sparseJunctionColumn index) ⟨hbad, hcentral⟩
    simpa [selectedGlobalStep, selectedRowStep, hcentral,
      incomingGlobalStep] using hincoming
  · have hselected :
        selectedRowStep rotation ordered minimizer row index =
          outgoingRowStep rotation ordered row (sparseJunctionColumn index) := by
      simp [selectedRowStep, hcentral]
    change minimizer.pairing.partner
        (globalFirstVertex rotation ordered
          (.inl ⟨row, selectedRowStep rotation ordered minimizer row index⟩)) ≠
      globalSecondVertex rotation ordered
        (.inl ⟨row, selectedRowStep rotation ordered minimizer row index⟩)
    rw [hselected]
    exact hcentral

/-- The selected row-step index lies immediately before or immediately after
the sparse junction position. -/
theorem selectedRowStep_bounds
    (minimizer : ResidualDefectMinimizer G)
    (row : Fin a) (index : Fin 9) :
    (internalRowPosition rotation ordered row
        (sparseJunctionColumn index)).val - 1 ≤
        (selectedRowStep rotation ordered minimizer row index).val ∧
      (selectedRowStep rotation ordered minimizer row index).val ≤
        (internalRowPosition rotation ordered row
          (sparseJunctionColumn index)).val := by
  rcases selectedRowStep_eq_incoming_or_outgoing
      rotation ordered minimizer row index with hin | hout
  · rw [hin]
    simp [incomingRowStep]
  · rw [hout]
    simp [outgoingRowStep, internalRowPosition]

/-- Sparse selected steps occur in strict row order. -/
theorem selectedRowStep_strictMono
    (minimizer : ResidualDefectMinimizer G) (row : Fin a) :
    StrictMono (selectedRowStep rotation ordered minimizer row) := by
  intro first second hlt
  have hgap := sparse_branchPosition_add_two_le
    rotation ordered row hlt
  have hfirst := selectedRowStep_bounds
    rotation ordered minimizer row first
  have hsecond := selectedRowStep_bounds
    rotation ordered minimizer row second
  omega

/-- The first endpoints of the nine selected arms are pairwise distinct. -/
theorem selectedFirstVertex_injective
    (minimizer : ResidualDefectMinimizer G) (row : Fin a) :
    Function.Injective fun index : Fin 9 =>
      globalFirstVertex rotation ordered
        (selectedGlobalStep rotation ordered minimizer row index) := by
  intro first second heq
  have hposition := ordered.rowVertexInjective row heq
  have hstep :
      selectedRowStep rotation ordered minimizer row first =
        selectedRowStep rotation ordered minimizer row second := by
    exact (Fin.castSucc_injective _) hposition
  exact (selectedRowStep_strictMono rotation ordered minimizer row).injective hstep

/-- The second endpoints of the nine selected arms are pairwise distinct. -/
theorem selectedSecondVertex_injective
    (minimizer : ResidualDefectMinimizer G) (row : Fin a) :
    Function.Injective fun index : Fin 9 =>
      globalSecondVertex rotation ordered
        (selectedGlobalStep rotation ordered minimizer row index) := by
  intro first second heq
  have hposition := ordered.rowVertexInjective row heq
  have hval := congrArg Fin.val hposition
  have hstep :
      selectedRowStep rotation ordered minimizer row first =
        selectedRowStep rotation ordered minimizer row second := by
    apply Fin.ext
    change
      (selectedRowStep rotation ordered minimizer row first).val + 1 =
        (selectedRowStep rotation ordered minimizer row second).val + 1 at hval
    omega
  exact (selectedRowStep_strictMono rotation ordered minimizer row).injective hstep

/-- The selected deletion data and canonical colouring at the nine sparse
noncentral arms. -/
def coloringFamily
    (minimizer : ResidualDefectMinimizer G) (row : Fin a) :
    PairDeletionColoringFamily (G := G) (Fin 9) where
  data index :=
    (selectedGlobalKempeSite rotation minimal ordered
      (selectedGlobalStep rotation ordered minimizer row index)).data
  coloring index :=
    (selectedGlobalKempeSite rotation minimal ordered
      (selectedGlobalStep rotation ordered minimizer row index)).base
  tait index :=
    (selectedGlobalKempeSite rotation minimal ordered
      (selectedGlobalStep rotation ordered minimizer row index)).baseTait

/-- The common residual-defect minimizer is noncentral at every coordinate of
the sparse atlas. -/
theorem coloringFamily_noncentral
    (minimizer : ResidualDefectMinimizer G) (row : Fin a)
    (index : Fin 9) :
    minimizer.pairing.partner
        ((coloringFamily rotation minimal ordered minimizer row).data index).firstVertex ≠
      ((coloringFamily rotation minimal ordered minimizer row).data index).secondVertex := by
  change minimizer.pairing.partner
      (selectedGlobalKempeSite rotation minimal ordered
        (selectedGlobalStep rotation ordered minimizer row index)).data.firstVertex ≠
    (selectedGlobalKempeSite rotation minimal ordered
      (selectedGlobalStep rotation ordered minimizer row index)).data.secondVertex
  rw [(selectedGlobalKempeSite rotation minimal ordered
    (selectedGlobalStep rotation ordered minimizer row index)).first_eq]
  rw [(selectedGlobalKempeSite rotation minimal ordered
    (selectedGlobalStep rotation ordered minimizer row index)).second_eq]
  exact selectedGlobalStep_noncentral
    rotation ordered minimizer row index

/-- Avoiding the selected step's two endpoints makes an ambient edge survive
that deletion patch. -/
theorem coloringFamily_retains_of_avoids
    (minimizer : ResidualDefectMinimizer G) (row : Fin a)
    (index : Fin 9) (edge : G.edgeSet)
    (hfirst : globalFirstVertex rotation ordered
        (selectedGlobalStep rotation ordered minimizer row index) ∉
          edge.1.toFinset)
    (hsecond : globalSecondVertex rotation ordered
        (selectedGlobalStep rotation ordered minimizer row index) ∉
          edge.1.toFinset) :
    IsRetainedAmbientEdge
      ((coloringFamily rotation minimal ordered minimizer row).data index)
      edge := by
  apply isRetainedAmbientEdge_of_deleted_vertices_not_mem
  · change (selectedGlobalKempeSite rotation minimal ordered
      (selectedGlobalStep rotation ordered minimizer row index)).data.firstVertex ∉
        edge.1.toFinset
    rw [(selectedGlobalKempeSite rotation minimal ordered
      (selectedGlobalStep rotation ordered minimizer row index)).first_eq]
    exact hfirst
  · change (selectedGlobalKempeSite rotation minimal ordered
      (selectedGlobalStep rotation ordered minimizer row index)).data.secondVertex ∉
        edge.1.toFinset
    rw [(selectedGlobalKempeSite rotation minimal ordered
      (selectedGlobalStep rotation ordered minimizer row index)).second_eq]
    exact hsecond

/-- The sparse noncentral atlas covers every ambient edge. -/
theorem coloringFamily_coversEdges
    (minimizer : ResidualDefectMinimizer G) (row : Fin a) :
    (coloringFamily rotation minimal ordered minimizer row).CoversEdges := by
  intro edge
  have hcard : edge.1.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag edge.1
      (G.not_isDiag_of_mem_edgeSet edge.2)
  obtain ⟨index, hfirst, hsecond⟩ := exists_avoiding_two_injective
    (fun index : Fin 9 => globalFirstVertex rotation ordered
      (selectedGlobalStep rotation ordered minimizer row index))
    (fun index : Fin 9 => globalSecondVertex rotation ordered
      (selectedGlobalStep rotation ordered minimizer row index))
    (selectedFirstVertex_injective rotation ordered minimizer row)
    (selectedSecondVertex_injective rotation ordered minimizer row)
    edge.1.toFinset (by simp [hcard])
  exact ⟨index, coloringFamily_retains_of_avoids
    rotation minimal ordered minimizer row index edge hfirst hsecond⟩

/-- The sparse noncentral atlas covers every adjacent pair of ambient edges. -/
theorem coloringFamily_coversAdjacentEdges
    (minimizer : ResidualDefectMinimizer G) (row : Fin a) :
    (coloringFamily rotation minimal ordered minimizer row).CoversAdjacentEdges := by
  intro first second _hadjacent
  let forbidden : Finset V := first.1.toFinset ∪ second.1.toFinset
  have hfirstCard : first.1.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag first.1
      (G.not_isDiag_of_mem_edgeSet first.2)
  have hsecondCard : second.1.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag second.1
      (G.not_isDiag_of_mem_edgeSet second.2)
  have hforbiddenCard : forbidden.card ≤ 4 := by
    calc
      forbidden.card ≤ first.1.toFinset.card + second.1.toFinset.card :=
        Finset.card_union_le _ _
      _ = 4 := by rw [hfirstCard, hsecondCard]
  obtain ⟨index, hfirst, hsecond⟩ := exists_avoiding_two_injective
    (fun index : Fin 9 => globalFirstVertex rotation ordered
      (selectedGlobalStep rotation ordered minimizer row index))
    (fun index : Fin 9 => globalSecondVertex rotation ordered
      (selectedGlobalStep rotation ordered minimizer row index))
    (selectedFirstVertex_injective rotation ordered minimizer row)
    (selectedSecondVertex_injective rotation ordered minimizer row)
    forbidden (by simp; omega)
  have hfirstLeft : globalFirstVertex rotation ordered
      (selectedGlobalStep rotation ordered minimizer row index) ∉
        first.1.toFinset :=
    fun hmem => hfirst (Finset.mem_union_left _ hmem)
  have hsecondLeft : globalSecondVertex rotation ordered
      (selectedGlobalStep rotation ordered minimizer row index) ∉
        first.1.toFinset :=
    fun hmem => hsecond (Finset.mem_union_left _ hmem)
  have hfirstRight : globalFirstVertex rotation ordered
      (selectedGlobalStep rotation ordered minimizer row index) ∉
        second.1.toFinset :=
    fun hmem => hfirst (Finset.mem_union_right _ hmem)
  have hsecondRight : globalSecondVertex rotation ordered
      (selectedGlobalStep rotation ordered minimizer row index) ∉
        second.1.toFinset :=
    fun hmem => hsecond (Finset.mem_union_right _ hmem)
  exact ⟨index,
    coloringFamily_retains_of_avoids rotation minimal ordered minimizer row
      index first hfirstLeft hsecondLeft,
    coloringFamily_retains_of_avoids rotation minimal ordered minimizer row
      index second hfirstRight hsecondRight⟩

/-- The sparse mesh atlas exposes a geometric horn, or else supplies a
coherent same-colour pair with exact two-sector return geometry.  This is the
consumer-facing interface between the mesh and the compositional path
argument. -/
theorem branchingOrBoundary_or_hasCoherentTwoSectorPair
    (minimizer : ResidualDefectMinimizer G) (row : Fin a) :
    (∃ assignment : TaitAssignment
        (coloringFamily rotation minimal ordered minimizer row),
      HasBranchingOrBoundary
        (coloringFamily rotation minimal ordered minimizer row) assignment) ∨
      HasCoherentTwoSectorPair rotation minimal
        (coloringFamily rotation minimal ordered minimizer row) minimizer := by
  classical
  by_cases hhorn : ∃ assignment : TaitAssignment
      (coloringFamily rotation minimal ordered minimizer row),
    HasBranchingOrBoundary
      (coloringFamily rotation minimal ordered minimizer row) assignment
  · exact Or.inl hhorn
  · right
    apply hasCoherentTwoSectorPair_of_no_branchingOrBoundary
      rotation minimal
      (coloringFamily rotation minimal ordered minimizer row) minimizer
    · intro assignment
      exact fun hexposes => hhorn ⟨assignment, hexposes⟩
    · exact coloringFamily_noncentral
        rotation minimal ordered minimizer row

end

end Mettapedia.GraphTheory.FourColor.Compositional.SparseNoncentralMeshAtlas
