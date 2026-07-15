import Mettapedia.GraphTheory.FourColor.GoertzelV24TubeCorridorStrands

namespace Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer

open GoertzelV24WindingClassification

/-- The merge-to-frontier coordinate tables are mutual inverses. -/
theorem secondNew_newSecond (position : Fin 5) :
    secondNew (newSecond position) = position := by fin_cases position <;> rfl

theorem newSecond_secondNew (vertex : Fin 5) :
    newSecond (secondNew vertex) = vertex := by fin_cases vertex <;> rfl

/-- Complete enumeration of the three edges at a split vertex. -/
theorem firstIncident_eq_true_iff (edge : TubeRingEdge) (vertex : Fin 5) :
    firstIncident edge vertex = true ↔
      edge = .old vertex ∨
      edge = .middle (firstLeft vertex) ∨
      edge = .middle (firstRight vertex) := by
  cases edge with
  | old position =>
      simp only [firstIncident, beq_iff_eq]
      constructor
      · intro h
        exact Or.inl (congrArg TubeRingEdge.old h)
      · rintro (h | h | h)
        · exact TubeRingEdge.old.inj h
        · contradiction
        · contradiction
  | middle edge =>
      simp only [firstIncident, beq_iff_eq]
      fin_cases vertex <;> fin_cases edge <;>
        simp [middleFirst, firstLeft, firstRight]
  | new position => simp [firstIncident]

/-- Complete enumeration of the three edges at a merge vertex. -/
theorem secondIncident_eq_true_iff (edge : TubeRingEdge) (vertex : Fin 5) :
    secondIncident edge vertex = true ↔
      edge = .middle (secondLeft vertex) ∨
      edge = .middle (secondRight vertex) ∨
      edge = .new (secondNew vertex) := by
  cases edge with
  | old position => simp [secondIncident]
  | middle edge =>
      simp only [secondIncident, beq_iff_eq]
      fin_cases vertex <;> fin_cases edge <;>
        simp [middleSecond, secondLeft, secondRight]
  | new position =>
      simp only [secondIncident, beq_iff_eq]
      constructor
      · intro h
        right
        right
        apply congrArg TubeRingEdge.new
        rw [← h]
        exact (secondNew_newSecond position).symm
      · rintro (h | h | h)
        · contradiction
        · contradiction
        · have := TubeRingEdge.new.inj h
          rw [this]
          exact newSecond_secondNew vertex

theorem pairwiseDistinct3_ne
    {first second third : StrandColor}
    (hpairwise : PairwiseDistinct3 first second third) :
    first ≠ second ∧ second ≠ first ∧
    first ≠ third ∧ third ≠ first ∧
    second ≠ third ∧ third ≠ second :=
  ⟨hpairwise.1, hpairwise.1.symm,
    hpairwise.2.1, hpairwise.2.1.symm,
    hpairwise.2.2, hpairwise.2.2.symm⟩

/-- Local Tait properness separates the colors of every two distinct edges
sharing either internal vertex of a ring. -/
theorem TubeRingChoice.ringColor_ne_of_share
    (source : TubeFrontierState) (choice : TubeRingChoice)
    (hlocal : choice.LocallyTait source)
    {left right : TubeRingEdge} (hne : left ≠ right)
    (hshare : ShareRingVertex left right) :
    ringColor source choice left ≠ ringColor source choice right := by
  rcases hshare with ⟨vertex, hleft, hright⟩ | ⟨vertex, hleft, hright⟩
  · rw [firstIncident_eq_true_iff] at hleft hright
    rcases hleft with rfl | rfl | rfl <;>
      rcases hright with rfl | rfl | rfl
    all_goals
      first
      | exact False.elim (hne rfl)
      | exact (pairwiseDistinct3_ne (hlocal.1 vertex)).1
      | exact (pairwiseDistinct3_ne (hlocal.1 vertex)).2.1
      | exact (pairwiseDistinct3_ne (hlocal.1 vertex)).2.2.1
      | exact (pairwiseDistinct3_ne (hlocal.1 vertex)).2.2.2.1
      | exact (pairwiseDistinct3_ne (hlocal.1 vertex)).2.2.2.2.1
      | exact (pairwiseDistinct3_ne (hlocal.1 vertex)).2.2.2.2.2
  · rw [secondIncident_eq_true_iff] at hleft hright
    rcases hleft with rfl | rfl | rfl <;>
      rcases hright with rfl | rfl | rfl
    all_goals
      first
      | exact False.elim (hne rfl)
      | exact (pairwiseDistinct3_ne (hlocal.2 vertex)).1
      | exact (pairwiseDistinct3_ne (hlocal.2 vertex)).2.1
      | exact (pairwiseDistinct3_ne (hlocal.2 vertex)).2.2.1
      | exact (pairwiseDistinct3_ne (hlocal.2 vertex)).2.2.2.1
      | exact (pairwiseDistinct3_ne (hlocal.2 vertex)).2.2.2.2.1
      | exact (pairwiseDistinct3_ne (hlocal.2 vertex)).2.2.2.2.2

/-- The line graph of the canonical normalized tube incidence model. Its
vertices are tube edges; two are adjacent exactly when they share an internal
split or merge vertex in one ring. -/
def tubeCorridorLineGraph (rings : Nat) :
    SimpleGraph (TubeCorridorEdge rings) where
  Adj left right := ∃ ring localLeft localRight,
    localLeft ≠ localRight ∧ ShareRingVertex localLeft localRight ∧
    embedRingEdge ring localLeft = left ∧
    embedRingEdge ring localRight = right
  symm := ⟨by
    rintro left right ⟨ring, localLeft, localRight, hne, hshare, rfl, rfl⟩
    exact ⟨ring, localRight, localLeft, hne.symm,
      shareRingVertex_symm.symm localLeft localRight hshare, rfl, rfl⟩⟩
  loopless := ⟨by
    rintro edge ⟨ring, localLeft, localRight, hne, _hshare, hleft, hright⟩
    exact hne (embedRingEdge_injective ring (hleft.trans hright.symm))⟩

/-- The global edge-color function restricts to the certified local ring
coloring on every ring. -/
theorem TubeCorridorTaitColoring.edgeColor_embedRingEdge
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    (ring : Fin rings) (edge : TubeRingEdge) :
    coloring.edgeColor (embedRingEdge ring edge) =
      ringColor (coloring.frontierState ring.castSucc)
        (coloring.ringChoice ring) edge := by
  cases edge with
  | old position => rfl
  | middle edge => rfl
  | new position =>
      exact (coloring.successor ring).2.2.2.1 position

/-- An assembled tube certificate is a genuine proper coloring of the
canonical corridor line graph. -/
def TubeCorridorTaitColoring.toLineColoring
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish) :
    (tubeCorridorLineGraph rings).Coloring StrandColor :=
  SimpleGraph.Coloring.mk coloring.edgeColor <| by
    rintro left right ⟨ring, localLeft, localRight, hne, hshare, rfl, rfl⟩
    rw [coloring.edgeColor_embedRingEdge, coloring.edgeColor_embedRingEdge]
    exact TubeRingChoice.ringColor_ne_of_share
      (coloring.frontierState ring.castSucc) (coloring.ringChoice ring)
      (coloring.successor ring).locallyTait hne hshare

/-- The strand graph has exactly the line-graph adjacencies whose endpoints
carry the two tracked colors. -/
theorem TubeCorridorTaitColoring.trackedGraph_adj_iff
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish)
    (left right : TubeCorridorEdge rings) :
    coloring.trackedGraph.Adj left right ↔
      (tubeCorridorLineGraph rings).Adj left right ∧
      IsTracked (coloring.edgeColor left) ∧
      IsTracked (coloring.edgeColor right) := by
  constructor
  · rintro ⟨ring, localLeft, localRight, hadj, rfl, rfl⟩
    refine ⟨⟨ring, localLeft, localRight, hadj.1, hadj.2.2.2, rfl, rfl⟩, ?_, ?_⟩
    · rw [coloring.edgeColor_embedRingEdge]
      exact hadj.2.1
    · rw [coloring.edgeColor_embedRingEdge]
      exact hadj.2.2.1
  · rintro ⟨⟨ring, localLeft, localRight, hne, hshare, rfl, rfl⟩,
      hleftTracked, hrightTracked⟩
    refine ⟨ring, localLeft, localRight, ⟨hne, ?_, ?_, hshare⟩, rfl, rfl⟩
    · rw [← coloring.edgeColor_embedRingEdge]
      exact hleftTracked
    · rw [← coloring.edgeColor_embedRingEdge]
      exact hrightTracked

/-- The two-color support subgraph defined directly from the line coloring. -/
def TubeCorridorTaitColoring.trackedLineSubgraph
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish) :
    SimpleGraph (TubeCorridorEdge rings) where
  Adj left right :=
    (tubeCorridorLineGraph rings).Adj left right ∧
      IsTracked (coloring.edgeColor left) ∧
      IsTracked (coloring.edgeColor right)
  symm := ⟨by
    rintro left right ⟨hadj, hleft, hright⟩
    exact ⟨hadj.symm, hright, hleft⟩⟩
  loopless := ⟨by
    intro edge hedge
    exact (tubeCorridorLineGraph rings).loopless.irrefl edge hedge.1⟩

/-- The transfer-built strand graph and the graph-theoretic two-color support
subgraph are definitionally faithful descriptions of the same adjacency. -/
theorem TubeCorridorTaitColoring.trackedGraph_eq_trackedLineSubgraph
    {rings : Nat} {start finish : TubeFrontierState}
    (coloring : TubeCorridorTaitColoring rings start finish) :
    coloring.trackedGraph = coloring.trackedLineSubgraph := by
  ext left right
  exact coloring.trackedGraph_adj_iff left right

end Mettapedia.GraphTheory.FourColor.GoertzelV24TubeRingTransfer
