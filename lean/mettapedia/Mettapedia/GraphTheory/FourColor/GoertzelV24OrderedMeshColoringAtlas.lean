import Mettapedia.GraphTheory.FourColor.GoertzelV24AdjacentPairColoringAtlas
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrderedMeshGlobalSites

/-!
# A deletion-colouring atlas on one ordered mesh row

The globally selected adjacent-pair colourings form a family of partial
ambient colourings.  This file proves that a sufficiently long ordered row
automatically supplies the two coverage fields needed by the generic atlas
gluing theorem.

The counting input is elementary and uniform.  If two maps from a finite
index type are injective, a set of `s` forbidden vertices blocks at most
`2 * s` indices.  On a simple ordered mesh row, the first and second
endpoints of the steps immediately following successive branch positions
are separately injective.  Nine such intervals therefore contain a step
avoiding the at most four endpoints of any two ambient edges.

No wall exclusion is concluded.  The remaining high-width obligation is
now colour-theoretic: show that the selected local colourings can be made to
agree on every common deletion, or extract a route-native replacement from
the disagreement forced below.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrderedMeshColoringAtlas

open GoertzelV24AdjacentPairBoundary
open GoertzelV24AdjacentPairColoringAtlas
open GoertzelV24AdjacentPairColoringAtlas.PairDeletionColoringFamily
open GoertzelV24AdjacentPairInsertion
open GoertzelV24AdjacentPairInsertion.AdjacentPairData
open GoertzelV24MeshIsoperimetry
open GoertzelV24OrderedInjectiveMeshWidthFactorization
open GoertzelV24OrderedMeshGlobalSites
open GoertzelV24RotationMultigraphAdapter
open GoertzelV24TwoEdgeCutMinimality
open SimpleGraph
open SimpleGraphDartRotation

noncomputable section

universe u w

/-- Two injective endpoint maps cannot have all their indices blocked by a
forbidden set smaller than half the index type. -/
theorem exists_avoiding_two_injective
    {I : Type w} {X : Type u} [Fintype I] [DecidableEq X]
    (first second : I → X)
    (firstInjective : Function.Injective first)
    (secondInjective : Function.Injective second)
    (forbidden : Finset X)
    (hlarge : 2 * forbidden.card < Fintype.card I) :
    ∃ index, first index ∉ forbidden ∧ second index ∉ forbidden := by
  by_contra hnone
  have hblocked (index : I) :
      first index ∈ forbidden ∨ second index ∈ forbidden := by
    by_cases hfirst : first index ∈ forbidden
    · exact Or.inl hfirst
    · right
      by_contra hsecond
      exact hnone ⟨index, hfirst, hsecond⟩
  let code : I →
      Sum {vertex // vertex ∈ forbidden} {vertex // vertex ∈ forbidden} :=
    fun index =>
      if hfirst : first index ∈ forbidden then
        Sum.inl ⟨first index, hfirst⟩
      else
        Sum.inr ⟨second index, (hblocked index).resolve_left hfirst⟩
  have codeInjective : Function.Injective code := by
    intro left right heq
    by_cases hleft : first left ∈ forbidden
    · by_cases hright : first right ∈ forbidden
      · have hsub :
            (⟨first left, hleft⟩ : {vertex // vertex ∈ forbidden}) =
              ⟨first right, hright⟩ := by
          simpa [code, hleft, hright] using heq
        exact firstInjective (congrArg Subtype.val hsub)
      · have hfalse : False := by
          simpa [code, hleft, hright] using heq
        exact hfalse.elim
    · by_cases hright : first right ∈ forbidden
      · have hfalse : False := by
          simpa [code, hleft, hright] using heq
        exact hfalse.elim
      · have hsub :
            (⟨second left, (hblocked left).resolve_left hleft⟩ :
                {vertex // vertex ∈ forbidden}) =
              ⟨second right, (hblocked right).resolve_left hright⟩ := by
          simpa [code, hleft, hright] using heq
        exact secondInjective (congrArg Subtype.val hsub)
  have hcard := Fintype.card_le_of_injective code codeInjective
  simp only [Fintype.card_sum, Fintype.card_coe] at hcard
  omega

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  {a n : Nat}

variable
  (rotation : Data G)
  (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
  (ordered : OrderedInjectiveMesh
    (toMultigraph rotation.toRotationSystem) a (n + 1))

/-- The row step immediately following a designated branch position. -/
def rowStepAfterBranch (row : Fin a) (column : Fin n) :
    Fin ((ordered.toMesh.row row).len) :=
  ⟨(ordered.rowBranchPosition row column.castSucc).val, by
    have hstrict :
        (ordered.rowBranchPosition row column.castSucc).val <
          (ordered.rowBranchPosition row column.succ).val :=
      ordered.rowBranchPosition_strictMono row column.castSucc_lt_succ
    have hnext := (ordered.rowBranchPosition row column.succ).isLt
    omega⟩

/-- First endpoint of the selected row step. -/
def rowStepFirstEndpoint (row : Fin a) (column : Fin n) : V :=
  (ordered.toMesh.row row).vert
    (rowStepAfterBranch rotation ordered row column).castSucc

/-- Second endpoint of the selected row step. -/
def rowStepSecondEndpoint (row : Fin a) (column : Fin n) : V :=
  (ordered.toMesh.row row).vert
    (rowStepAfterBranch rotation ordered row column).succ

/-- Distinct branch intervals on a simple row have distinct first
endpoints. -/
theorem rowStepFirstEndpoint_injective (row : Fin a) :
    Function.Injective (rowStepFirstEndpoint rotation ordered row) := by
  intro first second heq
  have hposition := ordered.rowVertexInjective row heq
  have hval := congrArg Fin.val hposition
  have hbranchPosition :
      ordered.rowBranchPosition row first.castSucc =
        ordered.rowBranchPosition row second.castSucc := by
    apply Fin.ext
    simpa [rowStepFirstEndpoint, rowStepAfterBranch] using hval
  have hcolumn :=
    (ordered.rowBranchPosition_strictMono row).injective hbranchPosition
  apply Fin.ext
  exact congrArg (fun column : Fin (n + 1) => column.val) hcolumn

/-- Distinct branch intervals on a simple row have distinct second
endpoints. -/
theorem rowStepSecondEndpoint_injective (row : Fin a) :
    Function.Injective (rowStepSecondEndpoint rotation ordered row) := by
  intro first second heq
  have hposition := ordered.rowVertexInjective row heq
  have hval := congrArg Fin.val hposition
  have hbranchPosition :
      ordered.rowBranchPosition row first.castSucc =
        ordered.rowBranchPosition row second.castSucc := by
    apply Fin.ext
    dsimp [rowStepSecondEndpoint, rowStepAfterBranch] at hval
    omega
  have hcolumn :=
    (ordered.rowBranchPosition_strictMono row).injective hbranchPosition
  apply Fin.ext
  exact congrArg (fun column : Fin (n + 1) => column.val) hcolumn

/-- A long enough ordered row has a designated step whose two endpoints
avoid any supplied finite forbidden set. -/
theorem exists_rowStep_avoiding
    (row : Fin a) (forbidden : Finset V)
    (hlarge : 2 * forbidden.card < n) :
    ∃ column : Fin n,
      rowStepFirstEndpoint rotation ordered row column ∉ forbidden ∧
        rowStepSecondEndpoint rotation ordered row column ∉ forbidden := by
  simpa using exists_avoiding_two_injective
    (rowStepFirstEndpoint rotation ordered row)
    (rowStepSecondEndpoint rotation ordered row)
    (rowStepFirstEndpoint_injective rotation ordered row)
    (rowStepSecondEndpoint_injective rotation ordered row)
    forbidden (by simpa using hlarge)

/-- The globally selected deletion colourings, indexed once by every row or
column step of the ordered mesh. -/
def globalColoringFamily :
    PairDeletionColoringFamily (G := G)
      (GlobalMeshStep rotation ordered) where
  data step :=
    (selectedGlobalKempeSite rotation minimal ordered step).data
  coloring step :=
    (selectedGlobalKempeSite rotation minimal ordered step).base
  tait step :=
    (selectedGlobalKempeSite rotation minimal ordered step).baseTait

/-- The globally indexed row occurrence immediately following a branch
position. -/
def globalRowStep (row : Fin a) (column : Fin n) :
    GlobalMeshStep rotation ordered :=
  .inl ⟨row, rowStepAfterBranch rotation ordered row column⟩

@[simp] theorem globalFirstVertex_globalRowStep
    (row : Fin a) (column : Fin n) :
    globalFirstVertex rotation ordered
        (globalRowStep rotation ordered row column) =
      rowStepFirstEndpoint rotation ordered row column :=
  rfl

@[simp] theorem globalSecondVertex_globalRowStep
    (row : Fin a) (column : Fin n) :
    globalSecondVertex rotation ordered
        (globalRowStep rotation ordered row column) =
      rowStepSecondEndpoint rotation ordered row column :=
  rfl

/-- If the selected row step avoids the endpoints of an ambient edge, the
globally selected deletion patch retains that edge. -/
theorem selectedGlobalKempeSite_retains_of_rowStep_avoids
    (row : Fin a) (column : Fin n) (edge : G.edgeSet)
    (hfirst : rowStepFirstEndpoint rotation ordered row column ∉ edge.1.toFinset)
    (hsecond : rowStepSecondEndpoint rotation ordered row column ∉ edge.1.toFinset) :
    IsRetainedAmbientEdge
      (selectedGlobalKempeSite rotation minimal ordered
        (globalRowStep rotation ordered row column)).data edge := by
  apply isRetainedAmbientEdge_of_deleted_vertices_not_mem
  · rw [(selectedGlobalKempeSite rotation minimal ordered
      (globalRowStep rotation ordered row column)).first_eq]
    simpa using hfirst
  · rw [(selectedGlobalKempeSite rotation minimal ordered
      (globalRowStep rotation ordered row column)).second_eq]
    simpa using hsecond

/-- Five branch intervals already suffice to cover each individual ambient
edge, since an edge has exactly two endpoints. -/
theorem globalColoringFamily_coversEdges
    (row : Fin a) (hlarge : 4 < n) :
    (globalColoringFamily rotation minimal ordered).CoversEdges := by
  intro edge
  have hcard : edge.1.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag edge.1
      (G.not_isDiag_of_mem_edgeSet edge.2)
  obtain ⟨column, hfirst, hsecond⟩ :=
    exists_rowStep_avoiding rotation ordered row edge.1.toFinset (by omega)
  exact ⟨globalRowStep rotation ordered row column,
    selectedGlobalKempeSite_retains_of_rowStep_avoids
      rotation minimal ordered row column edge hfirst hsecond⟩

/-- Nine branch intervals cover any two ambient edges simultaneously.  The
adjacency premise is deliberately not needed: the union of two endpoint
sets has cardinality at most four. -/
theorem globalColoringFamily_coversAdjacentEdges
    (row : Fin a) (hlarge : 8 < n) :
    (globalColoringFamily rotation minimal ordered).CoversAdjacentEdges := by
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
      forbidden.card ≤
          first.1.toFinset.card + second.1.toFinset.card :=
        Finset.card_union_le _ _
      _ = 4 := by rw [hfirstCard, hsecondCard]
  obtain ⟨column, hleft, hright⟩ :=
    exists_rowStep_avoiding rotation ordered row forbidden (by omega)
  have hleftFirst :
      rowStepFirstEndpoint rotation ordered row column ∉ first.1.toFinset :=
    fun hmem => hleft (Finset.mem_union_left _ hmem)
  have hrightFirst :
      rowStepSecondEndpoint rotation ordered row column ∉ first.1.toFinset :=
    fun hmem => hright (Finset.mem_union_left _ hmem)
  have hleftSecond :
      rowStepFirstEndpoint rotation ordered row column ∉ second.1.toFinset :=
    fun hmem => hleft (Finset.mem_union_right _ hmem)
  have hrightSecond :
      rowStepSecondEndpoint rotation ordered row column ∉ second.1.toFinset :=
    fun hmem => hright (Finset.mem_union_right _ hmem)
  exact ⟨globalRowStep rotation ordered row column,
    selectedGlobalKempeSite_retains_of_rowStep_avoids
      rotation minimal ordered row column first hleftFirst hrightFirst,
    selectedGlobalKempeSite_retains_of_rowStep_avoids
      rotation minimal ordered row column second hleftSecond hrightSecond⟩

/-! ## Localizing the obstruction to any nine selected row intervals -/

/-- Restrict the globally selected deletion colourings to an arbitrary
family of row intervals. -/
def rowSelectionColoringFamily {I : Type w}
    (row : Fin a) (slot : I → Fin n) :
    PairDeletionColoringFamily (G := G) I where
  data index :=
    (selectedGlobalKempeSite rotation minimal ordered
      (globalRowStep rotation ordered row (slot index))).data
  coloring index :=
    (selectedGlobalKempeSite rotation minimal ordered
      (globalRowStep rotation ordered row (slot index))).base
  tait index :=
    (selectedGlobalKempeSite rotation minimal ordered
      (globalRowStep rotation ordered row (slot index))).baseTait

/-- Any injective selection of at least five row intervals covers every
ambient edge. -/
theorem rowSelectionColoringFamily_coversEdges
    {I : Type w} [Fintype I]
    (row : Fin a) (slot : I → Fin n)
    (slotInjective : Function.Injective slot)
    (hlarge : 4 < Fintype.card I) :
    (rowSelectionColoringFamily rotation minimal ordered row slot).CoversEdges := by
  intro edge
  have hcard : edge.1.toFinset.card = 2 :=
    Sym2.card_toFinset_of_not_isDiag edge.1
      (G.not_isDiag_of_mem_edgeSet edge.2)
  obtain ⟨index, hfirst, hsecond⟩ := exists_avoiding_two_injective
    (fun index => rowStepFirstEndpoint rotation ordered row (slot index))
    (fun index => rowStepSecondEndpoint rotation ordered row (slot index))
    ((rowStepFirstEndpoint_injective rotation ordered row).comp slotInjective)
    ((rowStepSecondEndpoint_injective rotation ordered row).comp slotInjective)
    edge.1.toFinset (by omega)
  exact ⟨index, selectedGlobalKempeSite_retains_of_rowStep_avoids
    rotation minimal ordered row (slot index) edge hfirst hsecond⟩

/-- Any injective selection of nine row intervals covers every pair of
ambient edges simultaneously, hence in particular every adjacent pair. -/
theorem rowSelectionColoringFamily_coversAdjacentEdges
    {I : Type w} [Fintype I]
    (row : Fin a) (slot : I → Fin n)
    (slotInjective : Function.Injective slot)
    (hlarge : 8 < Fintype.card I) :
    (rowSelectionColoringFamily rotation minimal ordered row slot).CoversAdjacentEdges := by
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
  obtain ⟨index, hleft, hright⟩ := exists_avoiding_two_injective
    (fun index => rowStepFirstEndpoint rotation ordered row (slot index))
    (fun index => rowStepSecondEndpoint rotation ordered row (slot index))
    ((rowStepFirstEndpoint_injective rotation ordered row).comp slotInjective)
    ((rowStepSecondEndpoint_injective rotation ordered row).comp slotInjective)
    forbidden (by omega)
  have hleftFirst :
      rowStepFirstEndpoint rotation ordered row (slot index) ∉
        first.1.toFinset :=
    fun hmem => hleft (Finset.mem_union_left _ hmem)
  have hrightFirst :
      rowStepSecondEndpoint rotation ordered row (slot index) ∉
        first.1.toFinset :=
    fun hmem => hright (Finset.mem_union_left _ hmem)
  have hleftSecond :
      rowStepFirstEndpoint rotation ordered row (slot index) ∉
        second.1.toFinset :=
    fun hmem => hleft (Finset.mem_union_right _ hmem)
  have hrightSecond :
      rowStepSecondEndpoint rotation ordered row (slot index) ∉
        second.1.toFinset :=
    fun hmem => hright (Finset.mem_union_right _ hmem)
  exact ⟨index,
    selectedGlobalKempeSite_retains_of_rowStep_avoids
      rotation minimal ordered row (slot index) first hleftFirst hrightFirst,
    selectedGlobalKempeSite_retains_of_rowStep_avoids
      rotation minimal ordered row (slot index) second hleftSecond hrightSecond⟩

/-- Every injective nine-site sample on one ordered row contains two selected
deletion colourings whose exact common-restriction bit is false. -/
theorem exists_rowSelection_commonRestriction_disagreement
    {I : Type w} [Fintype I]
    (row : Fin a) (slot : I → Fin n)
    (slotInjective : Function.Injective slot)
    (hlarge : 8 < Fintype.card I) :
    ∃ first second : I,
      commonRestrictionAgreementBit
        (selectedGlobalKempeSite rotation minimal ordered
          (globalRowStep rotation ordered row (slot first))).data
        (selectedGlobalKempeSite rotation minimal ordered
          (globalRowStep rotation ordered row (slot second))).data
        (selectedGlobalKempeSite rotation minimal ordered
          (globalRowStep rotation ordered row (slot first))).base
        (selectedGlobalKempeSite rotation minimal ordered
          (globalRowStep rotation ordered row (slot second))).base = false := by
  let family := rowSelectionColoringFamily rotation minimal ordered row slot
  have hnot := family.not_pairwiseCommonRestrictionAgrees_of_minimal
    rotation minimal
    (rowSelectionColoringFamily_coversEdges rotation minimal ordered row slot
      slotInjective (by omega))
    (rowSelectionColoringFamily_coversAdjacentEdges
      rotation minimal ordered row slot slotInjective hlarge)
  unfold PairwiseCommonRestrictionAgrees at hnot
  push Not at hnot
  rcases hnot with ⟨first, second, hagrees⟩
  refine ⟨first, second, ?_⟩
  change commonRestrictionAgreementBit
      (family.data first) (family.data second)
      (family.coloring first) (family.coloring second) = false
  cases hvalue : commonRestrictionAgreementBit
      (family.data first) (family.data second)
      (family.coloring first) (family.coloring second) <;>
    simp_all

/-- Publication-facing fixed-size form: any nine distinct intervals on one
ordered row contain a disagreeing pair. -/
theorem exists_disagreement_in_any_nine_row_intervals
    (row : Fin a) (slot : Fin 9 ↪ Fin n) :
    ∃ first second : Fin 9,
      commonRestrictionAgreementBit
        (selectedGlobalKempeSite rotation minimal ordered
          (globalRowStep rotation ordered row (slot first))).data
        (selectedGlobalKempeSite rotation minimal ordered
          (globalRowStep rotation ordered row (slot second))).data
        (selectedGlobalKempeSite rotation minimal ordered
          (globalRowStep rotation ordered row (slot first))).base
        (selectedGlobalKempeSite rotation minimal ordered
          (globalRowStep rotation ordered row (slot second))).base = false := by
  exact exists_rowSelection_commonRestriction_disagreement
    rotation minimal ordered row slot slot.injective (by simp)

/-- A least counterexample carrying an ordered mesh with ten columns has two
globally selected deletion colourings whose exact common-restriction bit is
false.  Thus the high-width argument must resolve a concrete disagreement;
pairwise nonempty local supports cannot by themselves close the route. -/
theorem exists_global_commonRestriction_disagreement
    (row : Fin a) (hlarge : 8 < n) :
    ∃ first second : GlobalMeshStep rotation ordered,
      commonRestrictionAgreementBit
        (selectedGlobalKempeSite rotation minimal ordered first).data
        (selectedGlobalKempeSite rotation minimal ordered second).data
        (selectedGlobalKempeSite rotation minimal ordered first).base
        (selectedGlobalKempeSite rotation minimal ordered second).base = false := by
  let family := globalColoringFamily rotation minimal ordered
  have hnot := family.not_pairwiseCommonRestrictionAgrees_of_minimal
    rotation minimal
    (globalColoringFamily_coversEdges rotation minimal ordered row (by omega))
    (globalColoringFamily_coversAdjacentEdges
      rotation minimal ordered row hlarge)
  unfold PairwiseCommonRestrictionAgrees at hnot
  push Not at hnot
  rcases hnot with ⟨first, second, hagrees⟩
  refine ⟨first, second, ?_⟩
  change commonRestrictionAgreementBit
      (family.data first) (family.data second)
      (family.coloring first) (family.coloring second) = false
  cases hvalue : commonRestrictionAgreementBit
      (family.data first) (family.data second)
      (family.coloring first) (family.coloring second) <;>
    simp_all

end

end GoertzelV24OrderedMeshColoringAtlas

end Mettapedia.GraphTheory.FourColor
