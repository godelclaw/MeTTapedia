import Mettapedia.GraphTheory.FourColor.GoertzelV24RetainedVertexTaitSplice
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutRouting

namespace Mettapedia.GraphTheory.FourColor

namespace RotationSystem

open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RetainedVertexTaitSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Change only the distinguished outer dart of a rotation system. The
underlying graph, rotations, faces as unpointed orbits, cubicity, and edge
colorings are unchanged. -/
def withOuter (RS : RotationSystem V E) (root : RS.D) : RotationSystem V E :=
  { RS with outer := root }

@[simp]
theorem withOuter_outer (RS : RotationSystem V E) (root : RS.D) :
    (RS.withOuter root).outer = root :=
  rfl

@[simp]
theorem withOuter_dartsAt (RS : RotationSystem V E) (root : RS.D)
    (vertex : V) :
    (RS.withOuter root).dartsAt vertex = RS.dartsAt vertex :=
  rfl

@[simp]
theorem withOuter_vertexSideEdgeBoundary
    (RS : RotationSystem V E) (root : RS.D) (side : Finset V) :
    (RS.withOuter root).vertexSideEdgeBoundary side =
      RS.vertexSideEdgeBoundary side :=
  rfl

@[simp]
theorem withOuter_edgeAdjacencyGraph
    (RS : RotationSystem V E) (root : RS.D) :
    (RS.withOuter root).edgeAdjacencyGraph = RS.edgeAdjacencyGraph :=
  rfl

@[simp]
theorem withOuter_isCubic_iff
    (RS : RotationSystem V E) (root : RS.D) :
    (RS.withOuter root).IsCubic ↔ RS.IsCubic :=
  Iff.rfl

/-- A representative dart of an existing rotation-system edge. -/
def dartRepresentative (RS : RotationSystem V E) (edge : E) : RS.D :=
  Classical.choose (RS.dartsOn_nonempty edge)

theorem dartRepresentative_edgeOf
    (RS : RotationSystem V E) (edge : E) :
    RS.edgeOf (RS.dartRepresentative edge) = edge := by
  exact RS.mem_dartsOn.mp (Classical.choose_spec (RS.dartsOn_nonempty edge))

/-- Descend an alpha-invariant dart color to the existing edge carrier. -/
def dartDescendedEdgeColor
    (RS : RotationSystem V E) (dartColor : RS.D → Color) (edge : E) : Color :=
  dartColor (RS.dartRepresentative edge)

theorem dartDescendedEdgeColor_edgeOf
    (RS : RotationSystem V E) (dartColor : RS.D → Color)
    (hAlpha : ∀ dart, dartColor (RS.alpha dart) = dartColor dart)
    (dart : RS.D) :
    RS.dartDescendedEdgeColor dartColor (RS.edgeOf dart) = dartColor dart := by
  unfold dartDescendedEdgeColor
  rcases RS.edge_fiber_two_cases (e := RS.edgeOf dart) (d := dart)
      (y := RS.dartRepresentative (RS.edgeOf dart)) rfl
      (RS.dartRepresentative_edgeOf (RS.edgeOf dart)) with
    hsame | hopposite
  · rw [hsame]
  · rw [hopposite, hAlpha]

/-- Alpha invariance and local properness on darts construct a proper edge
coloring of the original rotation system. -/
def dartDescendedColoring
    (RS : RotationSystem V E) (dartColor : RS.D → Color)
    (hAlpha : ∀ dart, dartColor (RS.alpha dart) = dartColor dart)
    (hProper : ∀ {left right : RS.D},
      RS.vertOf left = RS.vertOf right → left ≠ right →
        dartColor left ≠ dartColor right) :
    RS.EdgeColoring Color :=
  SimpleGraph.Coloring.mk (RS.dartDescendedEdgeColor dartColor) <| by
    intro leftEdge rightEdge hadjacent
    rcases (RS.edgeAdjacencyGraph_adj_iff).1 hadjacent with
      ⟨hedgeNe, vertex, hleftVertex, hrightVertex⟩
    rcases (RS.mem_endpoints_iff).1 hleftVertex with
      ⟨leftDart, hleftDartEdge, hleftDartVertex⟩
    rcases (RS.mem_endpoints_iff).1 hrightVertex with
      ⟨rightDart, hrightDartEdge, hrightDartVertex⟩
    have hleftEdge : RS.edgeOf leftDart = leftEdge :=
      RS.mem_dartsOn.mp hleftDartEdge
    have hrightEdge : RS.edgeOf rightDart = rightEdge :=
      RS.mem_dartsOn.mp hrightDartEdge
    have hdartNe : leftDart ≠ rightDart := by
      intro hdarts
      apply hedgeNe
      rw [← hleftEdge, ← hrightEdge, hdarts]
    rw [← hleftEdge, ← hrightEdge,
      RS.dartDescendedEdgeColor_edgeOf dartColor hAlpha,
      RS.dartDescendedEdgeColor_edgeOf dartColor hAlpha]
    exact hProper (hleftDartVertex.trans hrightDartVertex.symm) hdartNe

theorem dartDescendedColoring_isTait
    (RS : RotationSystem V E) (dartColor : RS.D → Color)
    (hAlpha : ∀ dart, dartColor (RS.alpha dart) = dartColor dart)
    (hProper : ∀ {left right : RS.D},
      RS.vertOf left = RS.vertOf right → left ≠ right →
        dartColor left ≠ dartColor right)
    (hNonzero : ∀ dart, dartColor dart ≠ 0) :
    RS.IsTaitEdgeColoring
      (RS.dartDescendedColoring dartColor hAlpha hProper) := by
  intro edge
  exact hNonzero (RS.dartRepresentative edge)

/-- Relabel every edge color by a color equivalence. -/
def relabelColoring
    (RS : RotationSystem V E) (C : RS.EdgeColoring Color)
    (relabel : Color ≃ Color) : RS.EdgeColoring Color :=
  SimpleGraph.Coloring.mk (fun edge => relabel (C edge)) <| by
    intro left right hadjacent
    exact relabel.injective.ne (C.valid hadjacent)

@[simp]
theorem relabelColoring_apply
    (RS : RotationSystem V E) (C : RS.EdgeColoring Color)
    (relabel : Color ≃ Color) (edge : E) :
    RS.relabelColoring C relabel edge = relabel (C edge) :=
  rfl

theorem relabelColoring_isTait
    (RS : RotationSystem V E) (C : RS.EdgeColoring Color)
    (relabel : Color ≃ Color) (hzero : relabel 0 = 0)
    (hC : RS.IsTaitEdgeColoring C) :
    RS.IsTaitEdgeColoring (RS.relabelColoring C relabel) := by
  intro edge hrelabeled
  apply hC edge
  apply relabel.injective
  exact hrelabeled.trans hzero.symm

/-- One rooted side of an exact two-edge cut. The endpoint condition is the
precise condition excluding a loop when the two exposed half-edges are joined
to form the cap edge. -/
structure TwoEdgeCutSideData (RS : RotationSystem V E) where
  side : Finset V
  leftEdge : E
  rightEdge : E
  edges_ne : leftEdge ≠ rightEdge
  boundary_eq : RS.vertexSideEdgeBoundary side = {leftEdge, rightEdge}
  outer_mem : RS.vertOf RS.outer ∈ side
  retainedEndpointsDistinct :
    ∀ (left right : BoundaryDart RS (fun vertex => vertex ∈ side)),
      RS.edgeOf left.1.1 = leftEdge →
      RS.edgeOf right.1.1 = rightEdge →
      RS.vertOf left.1.1 ≠ RS.vertOf right.1.1

/-- An exact two-edge cut with non-colliding retained endpoints on both
complementary sides. This is the root-independent input for constructing the
two capped halves. -/
structure TwoEdgeCutPairData (RS : RotationSystem V E) where
  side : Finset V
  leftEdge : E
  rightEdge : E
  edges_ne : leftEdge ≠ rightEdge
  boundary_eq : RS.vertexSideEdgeBoundary side = {leftEdge, rightEdge}
  sideRetainedEndpointsDistinct :
    ∀ (left right : BoundaryDart RS (fun vertex => vertex ∈ side)),
      RS.edgeOf left.1.1 = leftEdge →
      RS.edgeOf right.1.1 = rightEdge →
      RS.vertOf left.1.1 ≠ RS.vertOf right.1.1
  complementRetainedEndpointsDistinct :
    ∀ (left right : BoundaryDart RS (fun vertex => vertex ∈ sideᶜ)),
      RS.edgeOf left.1.1 = leftEdge →
      RS.edgeOf right.1.1 = rightEdge →
      RS.vertOf left.1.1 ≠ RS.vertOf right.1.1

namespace TwoEdgeCutSideData

variable {RS : RotationSystem V E} (data : TwoEdgeCutSideData RS)

/-- The retained vertex predicate of the chosen cut side. -/
def keep (vertex : V) : Prop :=
  vertex ∈ data.side

instance keepDecidablePred : DecidablePred data.keep :=
  fun vertex => Finset.decidableMem vertex data.side

/-- The first cut edge as a singleton ordered interface. -/
def leftCrossing : Fin 1 → E :=
  fun _ => data.leftEdge

/-- The second cut edge as a singleton ordered interface. -/
def rightCrossing : Fin 1 → E :=
  fun _ => data.rightEdge

@[simp]
theorem orderedCut_leftCrossing :
    orderedCut data.leftCrossing = {data.leftEdge} := by
  ext edge
  simp [orderedCut, leftCrossing]

@[simp]
theorem orderedCut_rightCrossing :
    orderedCut data.rightCrossing = {data.rightEdge} := by
  ext edge
  simp [orderedCut, rightCrossing]

theorem leftEdge_mem_boundary :
    data.leftEdge ∈ RS.vertexSideEdgeBoundary data.side := by
  rw [data.boundary_eq]
  simp

theorem rightEdge_mem_boundary :
    data.rightEdge ∈ RS.vertexSideEdgeBoundary data.side := by
  rw [data.boundary_eq]
  simp

/-- The computed boundary supplies the outward dart on the first cut edge. -/
theorem leftCrosses (step : Fin 1) :
    ∃ dart : RS.D,
      RS.edgeOf dart = data.leftCrossing step ∧
      data.keep (RS.vertOf dart) ∧
      ¬ data.keep (RS.vertOf (RS.alpha dart)) := by
  let dart := RS.boundaryDartOfCrossingEdge data.side data.leftEdge
    data.leftEdge_mem_boundary
  refine ⟨dart.1.1, ?_, ?_, ?_⟩
  · change RS.edgeOf dart.1.1 = data.leftEdge
    exact RS.boundaryDartOfCrossingEdge_edgeOf data.side data.leftEdge
      data.leftEdge_mem_boundary
  · exact dart.1.2
  · exact dart.2

/-- The computed boundary supplies the outward dart on the second cut edge. -/
theorem rightCrosses (step : Fin 1) :
    ∃ dart : RS.D,
      RS.edgeOf dart = data.rightCrossing step ∧
      data.keep (RS.vertOf dart) ∧
      ¬ data.keep (RS.vertOf (RS.alpha dart)) := by
  let dart := RS.boundaryDartOfCrossingEdge data.side data.rightEdge
    data.rightEdge_mem_boundary
  refine ⟨dart.1.1, ?_, ?_, ?_⟩
  · change RS.edgeOf dart.1.1 = data.rightEdge
    exact RS.boundaryDartOfCrossingEdge_edgeOf data.side data.rightEdge
      data.rightEdge_mem_boundary
  · exact dart.1.2
  · exact dart.2

theorem leftCrossing_injective : Function.Injective data.leftCrossing := by
  intro left right _
  exact Subsingleton.elim left right

theorem rightCrossing_injective : Function.Injective data.rightCrossing := by
  intro left right _
  exact Subsingleton.elim left right

/-- Exactness of the computed two-edge boundary covers every exposed dart. -/
theorem boundaryCover (dart : BoundaryDart RS data.keep) :
    RS.edgeOf dart.1.1 ∈ orderedCut data.leftCrossing ∨
      RS.edgeOf dart.1.1 ∈ orderedCut data.rightCrossing := by
  have hmem := RS.boundaryDart_edge_mem_vertexSideEdgeBoundary data.side dart
  rw [data.boundary_eq] at hmem
  simpa [data.orderedCut_leftCrossing, data.orderedCut_rightCrossing] using hmem

/-- Distinct cut edges give disjoint singleton interfaces. -/
theorem cutsDisjoint :
    Disjoint (orderedCut data.leftCrossing)
      (orderedCut data.rightCrossing) := by
  rw [data.orderedCut_leftCrossing, data.orderedCut_rightCrossing]
  simp [data.edges_ne]

/-- The no-loop condition on retained endpoints is exactly the seam-endpoint
condition required by the rotation-system splice constructor. -/
theorem seamEndpoints (step : Fin 1) :
    RS.vertOf
        (orderedBoundaryDart RS data.keep data.leftCrossing
          data.leftCrosses step).1.1.1 ≠
      RS.vertOf
        (orderedBoundaryDart RS data.keep data.rightCrossing
          data.rightCrosses step).1.1.1 := by
  apply data.retainedEndpointsDistinct
  · exact orderedBoundaryDart_edgeOf RS data.keep data.leftCrossing
      data.leftCrosses step
  · exact orderedBoundaryDart_edgeOf RS data.keep data.rightCrossing
      data.rightCrosses step

/-- The honest vertex carrier of the capped side. -/
abbrev CapVertex := RetainedVertex data.keep

/-- The rewired dart system obtained by joining the two exposed half-edges. -/
def capRewiredDartSystem :=
  orderedCutRetainedVertexRewiredDartSystem RS data.keep
    data.leftCrossing data.rightCrossing data.leftCrosses data.rightCrosses
    data.leftCrossing_injective data.rightCrossing_injective
    data.boundaryCover data.cutsDisjoint data.outer_mem data.seamEndpoints

/-- The edge carrier of the capped side. -/
abbrev CapEdge := data.capRewiredDartSystem.Edge

/-- Join the two boundary half-edges of one side of an exact two-edge cut.
The result retains precisely the vertices of that side. -/
def capRotationSystem : RotationSystem data.CapVertex data.CapEdge :=
  orderedCutRetainedVertexRotationSystem RS data.keep
    data.leftCrossing data.rightCrossing data.leftCrosses data.rightCrosses
    data.leftCrossing_injective data.rightCrossing_injective
    data.boundaryCover data.cutsDisjoint data.outer_mem data.seamEndpoints

/-- Embed an old dart based on the retained side into the capped dart
carrier. -/
def capDartOfRetained (dart : RetainedDart RS data.keep) :
    MatchedSeam.Dart (InternalDart RS data.keep)
      (BoundaryDartOn RS data.keep (orderedCut data.leftCrossing))
      (BoundaryDartOn RS data.keep (orderedCut data.rightCrossing)) :=
  retainedDartEquivMatchedParts RS data.keep
    (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
    data.boundaryCover data.cutsDisjoint dart

theorem capDartOfRetained_injective :
    Function.Injective data.capDartOfRetained := by
  unfold capDartOfRetained
  exact (retainedDartEquivMatchedParts RS data.keep
    (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
    data.boundaryCover data.cutsDisjoint).injective

/-- The capped edge containing an old retained dart. The two old cut edges
map to the same new edge, while every internal old edge maps to its retained
copy. -/
def capEdgeOfRetainedDart (dart : RetainedDart RS data.keep) : data.CapEdge :=
  data.capRewiredDartSystem.edgeOf (data.capDartOfRetained dart)

/-- The unique new cap edge, named from the first exposed half-edge. -/
def capEdge : data.CapEdge :=
  data.capRewiredDartSystem.edgeOf
    (Sum.inr (Sum.inl
      (orderedBoundaryDart RS data.keep data.leftCrossing
        data.leftCrosses (0 : Fin 1))))

/-- The cap embedding preserves the base vertex of every retained dart. -/
theorem capRotationSystem_vertOf_capDartOfRetained
    (dart : RetainedDart RS data.keep) :
    data.capRotationSystem.vertOf (data.capDartOfRetained dart) =
      (⟨RS.vertOf dart.1, dart.2⟩ : data.CapVertex) := by
  apply Subtype.ext
  change RS.vertOf (matchedPartUnderlyingDart RS data.keep
    (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
    (data.capDartOfRetained dart)) = RS.vertOf dart.1
  unfold capDartOfRetained
  rw [matchedPartUnderlyingDart_equiv]

/-- Distinct retained darts based at one old vertex determine adjacent,
distinct cap edges. -/
theorem capEdgeAdj_of_retainedDarts
    (left right : RetainedDart RS data.keep)
    (hvertex : RS.vertOf left.1 = RS.vertOf right.1)
    (hne : left.1 ≠ right.1) :
    data.capRotationSystem.edgeAdjacencyGraph.Adj
      (data.capEdgeOfRetainedDart left)
      (data.capEdgeOfRetainedDart right) := by
  let vertex : data.CapVertex := ⟨RS.vertOf left.1, left.2⟩
  have hleftAt : data.capDartOfRetained left ∈
      data.capRotationSystem.dartsAt vertex := by
    unfold RotationSystem.dartsAt
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        data.capRotationSystem_vertOf_capDartOfRetained left⟩
  have hrightAt : data.capDartOfRetained right ∈
      data.capRotationSystem.dartsAt vertex := by
    have hvertices :
        (⟨RS.vertOf right.1, right.2⟩ : data.CapVertex) = vertex := by
      apply Subtype.ext
      exact hvertex.symm
    unfold RotationSystem.dartsAt
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,
        (data.capRotationSystem_vertOf_capDartOfRetained right).trans
          hvertices⟩
  have hedgeNe : data.capEdgeOfRetainedDart left ≠
      data.capEdgeOfRetainedDart right := by
    intro hedges
    have hdarts := data.capRotationSystem.edgeOf_injOn_dartsAt vertex
      hleftAt hrightAt hedges
    exact hne (congrArg Subtype.val
      (data.capDartOfRetained_injective hdarts))
  apply data.capRotationSystem.edgeAdjacencyGraph_adj_of_mem_incidentEdges
    hedgeNe
  · exact (data.capRotationSystem.mem_incidentEdges_iff).2
      ⟨data.capDartOfRetained left, rfl,
        data.capRotationSystem_vertOf_capDartOfRetained left⟩
  · exact (data.capRotationSystem.mem_incidentEdges_iff).2
      ⟨data.capDartOfRetained right, rfl,
        (data.capRotationSystem_vertOf_capDartOfRetained right).trans
          (Subtype.ext hvertex.symm)⟩

private theorem capDartOfRetained_leftBoundary :
    data.capDartOfRetained
        (orderedBoundaryDart RS data.keep data.leftCrossing
          data.leftCrosses (0 : Fin 1)).1.1 =
      Sum.inr (Sum.inl
        (orderedBoundaryDart RS data.keep data.leftCrossing
          data.leftCrosses (0 : Fin 1))) := by
  apply matchedPartUnderlyingDart_injective RS data.keep
    (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
    data.boundaryCover data.cutsDisjoint
  unfold capDartOfRetained
  rw [matchedPartUnderlyingDart_equiv]
  rfl

private theorem capDartOfRetained_rightBoundary :
    data.capDartOfRetained
        (orderedBoundaryDart RS data.keep data.rightCrossing
          data.rightCrosses (0 : Fin 1)).1.1 =
      Sum.inr (Sum.inr
        (orderedBoundaryDart RS data.keep data.rightCrossing
          data.rightCrosses (0 : Fin 1))) := by
  apply matchedPartUnderlyingDart_injective RS data.keep
    (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
    data.boundaryCover data.cutsDisjoint
  unfold capDartOfRetained
  rw [matchedPartUnderlyingDart_equiv]
  rfl

private theorem capRewiredDartSystem_alpha_leftBoundary :
    data.capRewiredDartSystem.alpha
        (Sum.inr (Sum.inl
          (orderedBoundaryDart RS data.keep data.leftCrossing
            data.leftCrosses (0 : Fin 1)))) =
      Sum.inr (Sum.inr
        (orderedBoundaryDart RS data.keep data.rightCrossing
          data.rightCrosses (0 : Fin 1))) := by
  change
    (orderedCutMatchedSeamData RS data.keep data.leftCrossing
      data.rightCrossing data.leftCrosses data.rightCrosses
      data.leftCrossing_injective data.rightCrossing_injective
      data.boundaryCover data.cutsDisjoint data.outer_mem).alpha
        (Sum.inr (Sum.inl
          (orderedBoundaryDart RS data.keep data.leftCrossing
            data.leftCrosses (0 : Fin 1)))) = _
  rw [MatchedSeam.Data.alpha_left]
  congr 2

/-- Every exposed dart of the retained side lies on the unique new cap edge. -/
theorem capEdgeOfRetainedDart_eq_capEdge_of_boundary
    (dart : BoundaryDart RS data.keep) :
    data.capEdgeOfRetainedDart dart.1 = data.capEdge := by
  have hedge := RS.boundaryDart_edge_mem_vertexSideEdgeBoundary data.side dart
  rw [data.boundary_eq] at hedge
  simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
  rcases hedge with hedge | hedge
  · have hdart : dart =
        (orderedBoundaryDart RS data.keep data.leftCrossing
          data.leftCrosses (0 : Fin 1)).1 := by
      apply boundaryDart_eq_of_edgeOf_eq RS data.keep
      simpa [leftCrossing] using hedge
    subst dart
    unfold capEdgeOfRetainedDart capEdge
    rw [data.capDartOfRetained_leftBoundary]
  · have hdart : dart =
        (orderedBoundaryDart RS data.keep data.rightCrossing
          data.rightCrosses (0 : Fin 1)).1 := by
      apply boundaryDart_eq_of_edgeOf_eq RS data.keep
      simpa [rightCrossing] using hedge
    subst dart
    unfold capEdgeOfRetainedDart capEdge
    rw [data.capDartOfRetained_rightBoundary]
    apply (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff _ _).2
    right
    exact data.capRewiredDartSystem_alpha_leftBoundary.symm

/-- If both ends of an old edge are retained, its two old darts determine the
same internal edge of the cap. -/
theorem capEdgeOfRetainedDart_alpha_of_internal
    (dart : RS.D) (hkeep : data.keep (RS.vertOf dart))
    (hkeepAlpha : data.keep (RS.vertOf (RS.alpha dart))) :
    data.capEdgeOfRetainedDart ⟨RS.alpha dart, hkeepAlpha⟩ =
      data.capEdgeOfRetainedDart ⟨dart, hkeep⟩ := by
  let retained : RetainedDart RS data.keep := ⟨dart, hkeep⟩
  let retainedAlpha : RetainedDart RS data.keep :=
    ⟨RS.alpha dart, hkeepAlpha⟩
  let internal : InternalDart RS data.keep := ⟨retained, hkeepAlpha⟩
  let internalAlpha : InternalDart RS data.keep :=
    ⟨retainedAlpha, by
      change data.keep (RS.vertOf (RS.alpha (RS.alpha dart)))
      simpa [RS.alpha_involutive] using hkeep⟩
  have hcap : data.capDartOfRetained retained = Sum.inl internal := by
    apply matchedPartUnderlyingDart_injective RS data.keep
      (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
      data.boundaryCover data.cutsDisjoint
    unfold capDartOfRetained
    rw [matchedPartUnderlyingDart_equiv]
    rfl
  have hcapAlpha :
      data.capDartOfRetained retainedAlpha = Sum.inl internalAlpha := by
    apply matchedPartUnderlyingDart_injective RS data.keep
      (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
      data.boundaryCover data.cutsDisjoint
    unfold capDartOfRetained
    rw [matchedPartUnderlyingDart_equiv]
    rfl
  unfold capEdgeOfRetainedDart
  rw [hcap, hcapAlpha]
  apply (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff _ _).2
  right
  change Sum.inl internalAlpha =
    Sum.inl (GoertzelV24RotationCutDartDecomposition.internalAlpha
      RS data.keep internal)
  congr 2

/-- Capping an exact two-edge-cut side preserves cubicity. -/
theorem capRotationSystem_isCubic (hCubic : RS.IsCubic) :
    data.capRotationSystem.IsCubic := by
  exact orderedCutRetainedVertexRotationSystem_isCubic RS data.keep
    data.leftCrossing data.rightCrossing data.leftCrosses data.rightCrosses
    data.leftCrossing_injective data.rightCrossing_injective
    data.boundaryCover data.cutsDisjoint data.outer_mem data.seamEndpoints
    hCubic

/-- A genuine crossing edge witnesses a deleted vertex, so the capped side is
strictly smaller than the ambient vertex carrier. -/
theorem card_capVertex_lt :
    Fintype.card data.CapVertex < Fintype.card V := by
  rcases data.leftCrosses (0 : Fin 1) with
    ⟨dart, _hedge, _hinside, houtside⟩
  exact card_retainedVertex_lt data.keep (RS.vertOf (RS.alpha dart)) houtside

/-- Cut parity supplies the equal seam colors needed to descend a coloring. -/
theorem cutColors
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) (step : Fin 1) :
    C (data.leftCrossing step) = C (data.rightCrossing step) := by
  simpa [leftCrossing, rightCrossing] using
    RS.twoEdgeCut_colors_eq hCubic C hC data.side data.edges_ne
      data.boundary_eq

/-- Restrict an ambient Tait coloring to the side and color the new cap edge
by the forced common color of the two old cut edges. -/
def capColoring
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.capRotationSystem.EdgeColoring Color :=
  orderedCutRetainedVertexSplicedColoring RS data.keep
    data.leftCrossing data.rightCrossing data.leftCrosses data.rightCrosses
    data.leftCrossing_injective data.rightCrossing_injective
    data.boundaryCover data.cutsDisjoint data.outer_mem data.seamEndpoints C
    (data.cutColors hCubic C hC)

/-- The induced coloring on the capped side is a genuine Tait coloring. -/
theorem capColoring_isTait
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.capRotationSystem.IsTaitEdgeColoring
      (data.capColoring hCubic C hC) := by
  exact orderedCutRetainedVertexSplicedColoring_isTait RS data.keep
    data.leftCrossing data.rightCrossing data.leftCrosses data.rightCrosses
    data.leftCrossing_injective data.rightCrossing_injective
    data.boundaryCover data.cutsDisjoint data.outer_mem data.seamEndpoints
    C hC (data.cutColors hCubic C hC)

/-- On every retained old dart, the induced cap coloring is exactly the old
edge color. This also identifies the color of the new seam edge. -/
theorem capColoring_capEdgeOfRetainedDart
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C)
    (dart : RetainedDart RS data.keep) :
    data.capColoring hCubic C hC (data.capEdgeOfRetainedDart dart) =
      C (RS.edgeOf dart.1) := by
  have hvalue := orderedCutRetainedVertexSplicedColoring_edgeOf RS data.keep
    data.leftCrossing data.rightCrossing data.leftCrosses data.rightCrosses
    data.leftCrossing_injective data.rightCrossing_injective
    data.boundaryCover data.cutsDisjoint data.outer_mem data.seamEndpoints C
    (data.cutColors hCubic C hC) (data.capDartOfRetained dart)
  calc
    data.capColoring hCubic C hC (data.capEdgeOfRetainedDart dart) =
        C (RS.edgeOf (matchedPartUnderlyingDart RS data.keep
          (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
          (data.capDartOfRetained dart))) := by
      unfold capColoring capEdgeOfRetainedDart capRewiredDartSystem
      convert hvalue using 1
      all_goals rfl
    _ = C (RS.edgeOf dart.1) := by
      congr 1
      exact congrArg RS.edgeOf
        (matchedPartUnderlyingDart_equiv RS data.keep
          (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
          data.boundaryCover data.cutsDisjoint dart)

/-- The new cap edge receives the common color of the two cut edges. -/
theorem capColoring_capEdge
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.capColoring hCubic C hC data.capEdge = C data.leftEdge := by
  let seamDart : MatchedSeam.Dart (InternalDart RS data.keep)
      (BoundaryDartOn RS data.keep (orderedCut data.leftCrossing))
      (BoundaryDartOn RS data.keep (orderedCut data.rightCrossing)) :=
    Sum.inr (Sum.inl
      (orderedBoundaryDart RS data.keep data.leftCrossing
        data.leftCrosses (0 : Fin 1)))
  have hvalue := orderedCutRetainedVertexSplicedColoring_edgeOf RS data.keep
    data.leftCrossing data.rightCrossing data.leftCrosses data.rightCrosses
    data.leftCrossing_injective data.rightCrossing_injective
    data.boundaryCover data.cutsDisjoint data.outer_mem data.seamEndpoints C
    (data.cutColors hCubic C hC) seamDart
  calc
    data.capColoring hCubic C hC data.capEdge =
        C (RS.edgeOf (matchedPartUnderlyingDart RS data.keep
          (orderedCut data.leftCrossing) (orderedCut data.rightCrossing)
          seamDart)) := by
      unfold capColoring capEdge capRewiredDartSystem
      convert hvalue using 1
      all_goals rfl
    _ = C data.leftEdge := by
      change C (RS.edgeOf
        (orderedBoundaryDart RS data.keep data.leftCrossing
          data.leftCrosses (0 : Fin 1)).1.1.1) = C data.leftEdge
      rw [orderedBoundaryDart_edgeOf]
      rfl

end TwoEdgeCutSideData

namespace TwoEdgeCutPairData

variable {RS : RotationSystem V E} (data : TwoEdgeCutPairData RS)

theorem leftEdge_mem_boundary :
    data.leftEdge ∈ RS.vertexSideEdgeBoundary data.side := by
  rw [data.boundary_eq]
  simp

theorem rightEdge_mem_boundary :
    data.rightEdge ∈ RS.vertexSideEdgeBoundary data.side := by
  rw [data.boundary_eq]
  simp

/-- The complementary vertex side has exactly the same two crossing edges. -/
theorem complement_boundary_eq :
    RS.vertexSideEdgeBoundary data.sideᶜ =
      {data.leftEdge, data.rightEdge} := by
  rw [RS.vertexSideEdgeBoundary_compl data.side, data.boundary_eq]

theorem leftEdge_mem_complement_boundary :
    data.leftEdge ∈ RS.vertexSideEdgeBoundary data.sideᶜ := by
  rw [data.complement_boundary_eq]
  simp

theorem rightEdge_mem_complement_boundary :
    data.rightEdge ∈ RS.vertexSideEdgeBoundary data.sideᶜ := by
  rw [data.complement_boundary_eq]
  simp

/-- A retained dart on the first cut edge roots the chosen side without
changing its underlying rotation system. -/
def sideRoot : RS.D :=
  (RS.boundaryDartOfCrossingEdge data.side data.leftEdge
    data.leftEdge_mem_boundary).1.1

/-- A retained dart on the first cut edge roots the complementary side. -/
def complementRoot : RS.D :=
  (RS.boundaryDartOfCrossingEdge data.sideᶜ data.leftEdge
    data.leftEdge_mem_complement_boundary).1.1

def sideRootedRotationSystem : RotationSystem V E :=
  RS.withOuter data.sideRoot

def complementRootedRotationSystem : RotationSystem V E :=
  RS.withOuter data.complementRoot

/-- The chosen side, rooted at one of its exposed darts, as cap-construction
data. -/
def sideData : TwoEdgeCutSideData data.sideRootedRotationSystem where
  side := data.side
  leftEdge := data.leftEdge
  rightEdge := data.rightEdge
  edges_ne := data.edges_ne
  boundary_eq := by
    simpa [sideRootedRotationSystem] using data.boundary_eq
  outer_mem := by
    change RS.vertOf data.sideRoot ∈ data.side
    exact (RS.boundaryDartOfCrossingEdge data.side data.leftEdge
      data.leftEdge_mem_boundary).1.2
  retainedEndpointsDistinct := by
    intro left right hleft hright
    exact data.sideRetainedEndpointsDistinct left right hleft hright

/-- The complementary side, independently rooted at an exposed dart, as
cap-construction data. -/
def complementData :
    TwoEdgeCutSideData data.complementRootedRotationSystem where
  side := data.sideᶜ
  leftEdge := data.leftEdge
  rightEdge := data.rightEdge
  edges_ne := data.edges_ne
  boundary_eq := by
    simpa [complementRootedRotationSystem] using data.complement_boundary_eq
  outer_mem := by
    change RS.vertOf data.complementRoot ∈ data.sideᶜ
    exact (RS.boundaryDartOfCrossingEdge data.sideᶜ data.leftEdge
      data.leftEdge_mem_complement_boundary).1.2
  retainedEndpointsDistinct := by
    intro left right hleft hright
    exact data.complementRetainedEndpointsDistinct left right hleft hright

/-- Each cap has strictly fewer vertices than the original rotation system. -/
theorem card_sideCapVertex_lt :
    Fintype.card data.sideData.CapVertex < Fintype.card V :=
  data.sideData.card_capVertex_lt

theorem card_complementCapVertex_lt :
    Fintype.card data.complementData.CapVertex < Fintype.card V :=
  data.complementData.card_capVertex_lt

/-- Both complementary cap constructions preserve cubicity. -/
theorem sideCap_isCubic (hCubic : RS.IsCubic) :
    data.sideData.capRotationSystem.IsCubic := by
  apply data.sideData.capRotationSystem_isCubic
  simpa [sideRootedRotationSystem] using hCubic

theorem complementCap_isCubic (hCubic : RS.IsCubic) :
    data.complementData.capRotationSystem.IsCubic := by
  apply data.complementData.capRotationSystem_isCubic
  simpa [complementRootedRotationSystem] using hCubic

/-- Restrict one ambient Tait coloring to the two independently rooted caps. -/
def sideCapColoring
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.sideData.capRotationSystem.EdgeColoring Color :=
  data.sideData.capColoring (by
    simpa [sideRootedRotationSystem] using hCubic) C hC

def complementCapColoring
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.complementData.capRotationSystem.EdgeColoring Color :=
  data.complementData.capColoring (by
    simpa [complementRootedRotationSystem] using hCubic) C hC

theorem sideCapColoring_isTait
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.sideData.capRotationSystem.IsTaitEdgeColoring
      (data.sideCapColoring hCubic C hC) := by
  exact data.sideData.capColoring_isTait
    (by simpa [sideRootedRotationSystem] using hCubic) C hC

theorem complementCapColoring_isTait
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.complementData.capRotationSystem.IsTaitEdgeColoring
      (data.complementCapColoring hCubic C hC) := by
  exact data.complementData.capColoring_isTait
    (by simpa [complementRootedRotationSystem] using hCubic) C hC

/-- The two induced cap edges carry the same old cut color. -/
theorem sideCapColoring_capEdge
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.sideCapColoring hCubic C hC data.sideData.capEdge =
      C data.leftEdge := by
  exact data.sideData.capColoring_capEdge
    (by simpa [sideRootedRotationSystem] using hCubic) C hC

theorem complementCapColoring_capEdge
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    data.complementCapColoring hCubic C hC data.complementData.capEdge =
      C data.leftEdge := by
  exact data.complementData.capColoring_capEdge
    (by simpa [complementRootedRotationSystem] using hCubic) C hC

/-- The cap edge containing a dart based on the chosen side. -/
def sideCapEdgeOfDart (dart : RS.D)
    (hside : RS.vertOf dart ∈ data.side) : data.sideData.CapEdge :=
  data.sideData.capEdgeOfRetainedDart ⟨dart, hside⟩

/-- The cap edge containing a dart based on the complementary side. -/
def complementCapEdgeOfDart (dart : RS.D)
    (hcomplement : RS.vertOf dart ∈ data.sideᶜ) :
    data.complementData.CapEdge :=
  data.complementData.capEdgeOfRetainedDart ⟨dart, hcomplement⟩

/-- Read a dart color from whichever capped half contains its base vertex. -/
def gluedDartColor
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (dart : RS.D) : Color :=
  if hside : RS.vertOf dart ∈ data.side then
    sideColoring (data.sideCapEdgeOfDart dart hside)
  else
    complementColoring
      (data.complementCapEdgeOfDart dart (by simpa using hside))

/-- Matching cap-edge colors make the piecewise dart color invariant under
the old edge involution. Internal edges use one cap edge on both darts;
crossing edges use the common seam color. -/
theorem gluedDartColor_alpha
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (hseam : sideColoring data.sideData.capEdge =
      complementColoring data.complementData.capEdge)
    (dart : RS.D) :
    data.gluedDartColor sideColoring complementColoring (RS.alpha dart) =
      data.gluedDartColor sideColoring complementColoring dart := by
  by_cases hside : RS.vertOf dart ∈ data.side
  · by_cases hsideAlpha : RS.vertOf (RS.alpha dart) ∈ data.side
    · rw [gluedDartColor, dif_pos hsideAlpha, gluedDartColor, dif_pos hside]
      congr 1
      exact data.sideData.capEdgeOfRetainedDart_alpha_of_internal
        dart hside hsideAlpha
    · rw [gluedDartColor, dif_neg hsideAlpha, gluedDartColor, dif_pos hside]
      let sideBoundary : BoundaryDart data.sideRootedRotationSystem
          data.sideData.keep :=
        ⟨⟨dart, hside⟩, hsideAlpha⟩
      let complementBoundary :
          BoundaryDart data.complementRootedRotationSystem
            data.complementData.keep :=
        ⟨⟨RS.alpha dart, by
          change RS.vertOf (RS.alpha dart) ∈ data.sideᶜ
          simpa using hsideAlpha⟩, by
          change RS.vertOf (RS.alpha (RS.alpha dart)) ∉ data.sideᶜ
          simpa [RS.alpha_involutive] using hside⟩
      change complementColoring
          (data.complementData.capEdgeOfRetainedDart complementBoundary.1) =
        sideColoring
          (data.sideData.capEdgeOfRetainedDart sideBoundary.1)
      rw [data.complementData.capEdgeOfRetainedDart_eq_capEdge_of_boundary,
        data.sideData.capEdgeOfRetainedDart_eq_capEdge_of_boundary]
      exact hseam.symm
  · by_cases hsideAlpha : RS.vertOf (RS.alpha dart) ∈ data.side
    · rw [gluedDartColor, dif_pos hsideAlpha, gluedDartColor, dif_neg hside]
      let complementBoundary :
          BoundaryDart data.complementRootedRotationSystem
            data.complementData.keep :=
        ⟨⟨dart, by
          change RS.vertOf dart ∈ data.sideᶜ
          simpa using hside⟩, by
          change RS.vertOf (RS.alpha dart) ∉ data.sideᶜ
          simpa using hsideAlpha⟩
      let sideBoundary : BoundaryDart data.sideRootedRotationSystem
          data.sideData.keep :=
        ⟨⟨RS.alpha dart, hsideAlpha⟩, by
          change RS.vertOf (RS.alpha (RS.alpha dart)) ∉ data.side
          simpa [RS.alpha_involutive] using hside⟩
      change sideColoring
          (data.sideData.capEdgeOfRetainedDart sideBoundary.1) =
        complementColoring
          (data.complementData.capEdgeOfRetainedDart complementBoundary.1)
      rw [data.sideData.capEdgeOfRetainedDart_eq_capEdge_of_boundary,
        data.complementData.capEdgeOfRetainedDart_eq_capEdge_of_boundary]
      exact hseam
    · rw [gluedDartColor, dif_neg hsideAlpha, gluedDartColor, dif_neg hside]
      congr 1
      apply data.complementData.capEdgeOfRetainedDart_alpha_of_internal

/-- At one old vertex both darts lie in the same capped half, where properness
of that cap coloring separates their colors. -/
theorem gluedDartColor_proper
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    {left right : RS.D}
    (hvertex : RS.vertOf left = RS.vertOf right) (hne : left ≠ right) :
    data.gluedDartColor sideColoring complementColoring left ≠
      data.gluedDartColor sideColoring complementColoring right := by
  by_cases hside : RS.vertOf left ∈ data.side
  · have hsideRight : RS.vertOf right ∈ data.side := by
      rw [← hvertex]
      exact hside
    rw [gluedDartColor, dif_pos hside, gluedDartColor, dif_pos hsideRight]
    apply sideColoring.valid
    exact data.sideData.capEdgeAdj_of_retainedDarts
      ⟨left, hside⟩ ⟨right, hsideRight⟩ hvertex hne
  · have hsideRight : RS.vertOf right ∉ data.side := by
      rw [← hvertex]
      exact hside
    rw [gluedDartColor, dif_neg hside, gluedDartColor, dif_neg hsideRight]
    apply complementColoring.valid
    apply data.complementData.capEdgeAdj_of_retainedDarts
      ⟨left, by
        change RS.vertOf left ∈ data.sideᶜ
        simpa using hside⟩
      ⟨right, by
        change RS.vertOf right ∈ data.sideᶜ
        simpa using hsideRight⟩
      hvertex hne

/-- Glue cap colorings with matching seam colors into an ambient proper edge
coloring. -/
def gluedColoring
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (hseam : sideColoring data.sideData.capEdge =
      complementColoring data.complementData.capEdge) :
    RS.EdgeColoring Color :=
  RS.dartDescendedColoring
    (data.gluedDartColor sideColoring complementColoring)
    (data.gluedDartColor_alpha sideColoring complementColoring hseam)
    (data.gluedDartColor_proper sideColoring complementColoring)

/-- Nonzero cap colorings glue to a nonzero ambient coloring. -/
theorem gluedColoring_isTait
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (hsideTait : data.sideData.capRotationSystem.IsTaitEdgeColoring
      sideColoring)
    (hcomplementTait :
      data.complementData.capRotationSystem.IsTaitEdgeColoring
        complementColoring)
    (hseam : sideColoring data.sideData.capEdge =
      complementColoring data.complementData.capEdge) :
    RS.IsTaitEdgeColoring
      (data.gluedColoring sideColoring complementColoring hseam) := by
  apply RS.dartDescendedColoring_isTait
    (data.gluedDartColor sideColoring complementColoring)
    (data.gluedDartColor_alpha sideColoring complementColoring hseam)
    (data.gluedDartColor_proper sideColoring complementColoring)
  intro dart
  by_cases hside : RS.vertOf dart ∈ data.side
  · rw [gluedDartColor, dif_pos hside]
    exact hsideTait _
  · rw [gluedDartColor, dif_neg hside]
    exact hcomplementTait _

/-- Globally swap the complementary cap's seam color with the chosen cap's
seam color. This preserves properness and fixes zero because both seam colors
are nonzero. -/
def alignedComplementColoring
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color) :
    data.complementData.capRotationSystem.EdgeColoring Color :=
  data.complementData.capRotationSystem.relabelColoring complementColoring
    (Equiv.swap
      (complementColoring data.complementData.capEdge)
      (sideColoring data.sideData.capEdge))

theorem alignedComplementColoring_capEdge
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color) :
    data.alignedComplementColoring sideColoring complementColoring
        data.complementData.capEdge =
      sideColoring data.sideData.capEdge := by
  simp [alignedComplementColoring]

theorem alignedComplementColoring_isTait
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (hsideTait : data.sideData.capRotationSystem.IsTaitEdgeColoring
      sideColoring)
    (hcomplementTait :
      data.complementData.capRotationSystem.IsTaitEdgeColoring
        complementColoring) :
    data.complementData.capRotationSystem.IsTaitEdgeColoring
      (data.alignedComplementColoring sideColoring complementColoring) := by
  apply data.complementData.capRotationSystem.relabelColoring_isTait
  · have hleft := hcomplementTait data.complementData.capEdge
    have hright := hsideTait data.sideData.capEdge
    have hzeroLeft :
        0 ≠ complementColoring data.complementData.capEdge := hleft.symm
    have hzeroRight : 0 ≠ sideColoring data.sideData.capEdge := hright.symm
    simp [Equiv.swap_apply_def, hzeroLeft, hzeroRight]
  · exact hcomplementTait

/-- Canonical gluing of arbitrary cap colorings: first align their seam
colors by a global color permutation, then descend the piecewise dart color. -/
def gluedColoringFromCaps
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color) :
    RS.EdgeColoring Color :=
  data.gluedColoring sideColoring
    (data.alignedComplementColoring sideColoring complementColoring)
    (data.alignedComplementColoring_capEdge
      sideColoring complementColoring).symm

theorem gluedColoringFromCaps_isTait
    (sideColoring : data.sideData.capRotationSystem.EdgeColoring Color)
    (complementColoring :
      data.complementData.capRotationSystem.EdgeColoring Color)
    (hsideTait : data.sideData.capRotationSystem.IsTaitEdgeColoring
      sideColoring)
    (hcomplementTait :
      data.complementData.capRotationSystem.IsTaitEdgeColoring
        complementColoring) :
    RS.IsTaitEdgeColoring
      (data.gluedColoringFromCaps sideColoring complementColoring) := by
  apply data.gluedColoring_isTait
  · exact hsideTait
  · exact data.alignedComplementColoring_isTait sideColoring
      complementColoring hsideTait hcomplementTait

/-- Exact two-edge-cut reduction, coloring direction used by minimality:
Tait colorability of both strictly smaller capped halves implies Tait
colorability of the ambient rotation system. -/
theorem taitColorable_of_caps
    (hside : ∃ sideColoring,
      data.sideData.capRotationSystem.IsTaitEdgeColoring sideColoring)
    (hcomplement : ∃ complementColoring,
      data.complementData.capRotationSystem.IsTaitEdgeColoring
        complementColoring) :
    ∃ C : RS.EdgeColoring Color, RS.IsTaitEdgeColoring C := by
  rcases hside with ⟨sideColoring, hsideTait⟩
  rcases hcomplement with ⟨complementColoring, hcomplementTait⟩
  exact ⟨data.gluedColoringFromCaps sideColoring complementColoring,
    data.gluedColoringFromCaps_isTait sideColoring complementColoring
      hsideTait hcomplementTait⟩

/-- An ambient Tait coloring restricts to Tait colorings of both capped
halves; cut parity supplies their common seam color. -/
theorem caps_taitColorable_of_ambient
    (hCubic : RS.IsCubic) (C : RS.EdgeColoring Color)
    (hC : RS.IsTaitEdgeColoring C) :
    (∃ sideColoring,
        data.sideData.capRotationSystem.IsTaitEdgeColoring sideColoring) ∧
      (∃ complementColoring,
        data.complementData.capRotationSystem.IsTaitEdgeColoring
          complementColoring) := by
  exact ⟨⟨data.sideCapColoring hCubic C hC,
      data.sideCapColoring_isTait hCubic C hC⟩,
    ⟨data.complementCapColoring hCubic C hC,
      data.complementCapColoring_isTait hCubic C hC⟩⟩

/-- Exact colorability equation for a non-colliding two-edge cut: the ambient
cubic rotation system is Tait colorable exactly when both strictly smaller
capped halves are Tait colorable. -/
theorem taitColorable_iff_caps (hCubic : RS.IsCubic) :
    (∃ C : RS.EdgeColoring Color, RS.IsTaitEdgeColoring C) ↔
      (∃ sideColoring,
          data.sideData.capRotationSystem.IsTaitEdgeColoring sideColoring) ∧
      (∃ complementColoring,
          data.complementData.capRotationSystem.IsTaitEdgeColoring
            complementColoring) := by
  constructor
  · rintro ⟨C, hC⟩
    exact data.caps_taitColorable_of_ambient hCubic C hC
  · rintro ⟨hside, hcomplement⟩
    exact data.taitColorable_of_caps hside hcomplement

end TwoEdgeCutPairData

end

end RotationSystem

end Mettapedia.GraphTheory.FourColor
