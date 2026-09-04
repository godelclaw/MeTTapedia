import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicThreeCutConnectedSides

/-!
# Saturating a cyclic edge cut to connected sides

A cyclic edge cut may be presented by a vertex predicate whose induced side
has several connected components.  This is harmless for existence of a cut,
but the literal compositional state requires connected complementary shores.

The standard finite repair is width-preserving.  Retain the reachable
component containing a chosen cycle on one side and recompute its exact edge
boundary.  The new boundary is contained in the old one; if that side was
disconnected, the containment is strict.  Repeating on either disconnected
side terminates by strict induction on the finite cut support.  The result is
a cyclic subcut, no wider than the original, whose two induced sides are
connected.

This theorem is purely graph-theoretic.  It uses neither planarity nor a
colouring and is therefore part of the generic separator interface rather
than the Four-Color-specific finite state.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace CyclicEdgeCutRealization

open GoertzelV24CyclicThreeCutConnectedSides
open SimpleGraph

noncomputable section

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

/-- The exact cut support of the reachable component of a selected-side
root.  Every edge leaving this component already belongs to the original
cut. -/
noncomputable def reachableCycleComponentCut
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (root : V) (hroot : realization.side root) : Finset G.edgeSet := by
  classical
  exact edgeCut.filter fun edge =>
    EdgeCrossesVertexSide G
      (inducedReachableSide G realization.side root hroot) edge

@[simp]
theorem mem_reachableCycleComponentCut_iff
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (root : V) (hroot : realization.side root) (edge : G.edgeSet) :
    edge ∈ realization.reachableCycleComponentCut root hroot ↔
      edge ∈ edgeCut ∧
        EdgeCrossesVertexSide G
          (inducedReachableSide G realization.side root hroot) edge := by
  simp [reachableCycleComponentCut]

theorem reachableCycleComponentCut_subset
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (root : V) (hroot : realization.side root) :
    realization.reachableCycleComponentCut root hroot ⊆ edgeCut := by
  classical
  simpa [reachableCycleComponentCut] using
    (Finset.filter_subset
      (fun edge => EdgeCrossesVertexSide G
        (inducedReachableSide G realization.side root hroot) edge)
      edgeCut)

/-- The reachable component containing a chosen side-cycle is itself one
side of an exact cyclic cut whose support is a subset of the original cut. -/
def reachableCycleComponentRealization
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (root : V) (hroot : realization.side root)
    (walk : G.Walk root root) (hcycle : walk.IsCycle)
    (hsupport : ∀ vertex, vertex ∈ walk.support → realization.side vertex) :
    CyclicEdgeCutRealization G
      (realization.reachableCycleComponentCut root hroot) where
  side := inducedReachableSide G realization.side root hroot
  hcut_eq := by
    intro edge
    rw [mem_reachableCycleComponentCut_iff]
    constructor
    · exact fun hedge => hedge.2
    · intro hcross
      exact ⟨(realization.hcut_eq edge).2
          (edgeCrossesVertexSide_of_inducedReachableSide
            realization.side root hroot edge hcross),
        hcross⟩
  hinside_cycle :=
    hasCycleOnSide_inducedReachableSide realization.side root hroot
      walk hcycle hsupport
  houtside_cycle := HasCycleOnSide.mono
    (fun vertex houtside hcomponent =>
      houtside (inducedReachableSide_mem hcomponent))
    realization.houtside_cycle

/-- If the selected side is disconnected, retaining the component containing
its chosen cycle strictly shrinks the exact cut support. -/
theorem reachableCycleComponentCut_ssubset_of_not_connected
    (hconnected : G.Connected)
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (root : V) (hroot : realization.side root)
    (walk : G.Walk root root) (hcycle : walk.IsCycle)
    (hsupport : ∀ vertex, vertex ∈ walk.support → realization.side vertex)
    (hnotConnected : ¬ (G.induce realization.side).Connected) :
    realization.reachableCycleComponentCut root hroot ⊂ edgeCut := by
  classical
  apply Finset.ssubset_iff_subset_ne.mpr
  refine ⟨realization.reachableCycleComponentCut_subset root hroot, ?_⟩
  intro hcutsEqual
  let component := inducedReachableSide G realization.side root hroot
  have hnotAll : ¬ ∀ vertex, realization.side vertex → component vertex := by
    intro hall
    apply hnotConnected
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨⟨root, hroot⟩, ?_⟩
    intro vertex
    rcases hall vertex.1 vertex.2 with ⟨_hvertex, hreachable⟩
    simpa [component] using hreachable
  push Not at hnotAll
  rcases hnotAll with ⟨vertex, hvertex, hnotComponent⟩
  let otherComponent :=
    inducedReachableSide G realization.side vertex hvertex
  have hotherVertex : otherComponent vertex :=
    inducedReachableSide_root realization.side vertex hvertex
  have hnotOtherRoot : ¬ otherComponent root := by
    intro hotherRoot
    apply hnotComponent
    rcases hotherRoot with ⟨_hroot, hreachable⟩
    exact ⟨hvertex, by simpa [component, otherComponent] using hreachable.symm⟩
  rcases hconnected vertex root with ⟨ambientWalk⟩
  rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides
      otherComponent ambientWalk hotherVertex hnotOtherRoot with
    ⟨edge, _hedgeWalk, hcrossOther⟩
  have hcrossSide : EdgeCrossesVertexSide G realization.side edge :=
    edgeCrossesVertexSide_of_inducedReachableSide
      realization.side vertex hvertex edge hcrossOther
  have hedgeCut : edge ∈ edgeCut := (realization.hcut_eq edge).2 hcrossSide
  have hedgeComponentCut :
      edge ∈ realization.reachableCycleComponentCut root hroot := by
    rw [hcutsEqual]
    exact hedgeCut
  have hcrossComponent : EdgeCrossesVertexSide G component edge := by
    exact ((realization.reachableCycleComponentRealization root hroot
      walk hcycle hsupport).hcut_eq edge).1 hedgeComponentCut
  rcases hcrossOther with
    ⟨inner, outer, hinnerEdge, houterEdge, hinnerOther, houterOther⟩
  have hverticesNe : inner ≠ outer := by
    intro heq
    exact houterOther (heq ▸ hinnerOther)
  have hedgePair : (edge : Sym2 V) = s(inner, outer) :=
    sym2_eq_mk_of_mem_of_mem_of_ne
      hinnerEdge houterEdge hverticesNe
  have hinnerSide : realization.side inner :=
    inducedReachableSide_mem hinnerOther
  have houterNotSide : ¬ realization.side outer := by
    intro houterSide
    exact (not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
      hedgePair hcrossSide)
      ⟨fun _ => houterSide, fun _ => hinnerSide⟩
  have hinnerNotComponent : ¬ component inner := by
    intro hinnerComponent
    apply hnotComponent
    rcases hinnerComponent with ⟨_hinnerSide, hrootInner⟩
    rcases hinnerOther with ⟨_hinnerSide', hvertexInner⟩
    exact ⟨hvertex, by
      simpa [component, otherComponent] using hrootInner.trans hvertexInner.symm⟩
  have houterNotComponent : ¬ component outer := by
    intro houterComponent
    exact houterNotSide (inducedReachableSide_mem houterComponent)
  exact (not_side_iff_of_edgeCrossesVertexSide_of_sym2_eq
    hedgePair hcrossComponent)
    ⟨fun hinnerComponent => (hinnerNotComponent hinnerComponent).elim,
      fun houterComponent => (houterNotComponent houterComponent).elim⟩

/-- **Width-preserving cyclic-cut saturation.**  Every cyclic edge cut in a
connected finite graph contains a cyclic subcut whose two induced sides are
connected. -/
theorem exists_connectedSides_subcut
    (hconnected : G.Connected)
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut) :
    ∃ connectedCut : Finset G.edgeSet,
      ∃ connectedRealization : CyclicEdgeCutRealization G connectedCut,
        connectedCut ⊆ edgeCut ∧
        (G.induce connectedRealization.side).Connected ∧
        (G.induce
          (fun vertex => ¬ connectedRealization.side vertex)).Connected := by
  classical
  refine Finset.strongInduction
    (p := fun currentCut =>
      CyclicEdgeCutRealization G currentCut →
        ∃ connectedCut : Finset G.edgeSet,
          ∃ connectedRealization : CyclicEdgeCutRealization G connectedCut,
            connectedCut ⊆ currentCut ∧
            (G.induce connectedRealization.side).Connected ∧
            (G.induce
              (fun vertex => ¬ connectedRealization.side vertex)).Connected)
    ?_ edgeCut realization
  intro currentCut ih currentRealization
  by_cases hside : (G.induce currentRealization.side).Connected
  · by_cases hcomplement :
        (G.induce
          (fun vertex => ¬ currentRealization.side vertex)).Connected
    · exact ⟨currentCut, currentRealization, Finset.Subset.rfl,
        hside, hcomplement⟩
    · let complementRealization := currentRealization.compl
      rcases complementRealization.hinside_cycle with
        ⟨root, hroot, walk, hcycle, hsupport⟩
      let smallerRealization :=
        complementRealization.reachableCycleComponentRealization
          root hroot walk hcycle hsupport
      have hstrict :
          complementRealization.reachableCycleComponentCut root hroot ⊂
            currentCut :=
        complementRealization.reachableCycleComponentCut_ssubset_of_not_connected
          hconnected root hroot walk hcycle hsupport hcomplement
      rcases ih _ hstrict smallerRealization with
        ⟨connectedCut, connectedRealization, hsubset, hfirst, hsecond⟩
      exact ⟨connectedCut, connectedRealization,
        hsubset.trans hstrict.1, hfirst, hsecond⟩
  · rcases currentRealization.hinside_cycle with
      ⟨root, hroot, walk, hcycle, hsupport⟩
    let smallerRealization :=
      currentRealization.reachableCycleComponentRealization
        root hroot walk hcycle hsupport
    have hstrict :
        currentRealization.reachableCycleComponentCut root hroot ⊂
          currentCut :=
      currentRealization.reachableCycleComponentCut_ssubset_of_not_connected
        hconnected root hroot walk hcycle hsupport hside
    rcases ih _ hstrict smallerRealization with
      ⟨connectedCut, connectedRealization, hsubset, hfirst, hsecond⟩
    exact ⟨connectedCut, connectedRealization,
      hsubset.trans hstrict.1, hfirst, hsecond⟩

/-- Cardinality form of saturation: the connected cyclic subcut is no wider
than the original cut. -/
theorem exists_connectedSides_subcut_card_le
    (hconnected : G.Connected)
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut) :
    ∃ connectedCut : Finset G.edgeSet,
      ∃ connectedRealization : CyclicEdgeCutRealization G connectedCut,
        connectedCut.card ≤ edgeCut.card ∧
        (G.induce connectedRealization.side).Connected ∧
        (G.induce
          (fun vertex => ¬ connectedRealization.side vertex)).Connected := by
  rcases realization.exists_connectedSides_subcut hconnected with
    ⟨connectedCut, connectedRealization, hsubset, hfirst, hsecond⟩
  exact ⟨connectedCut, connectedRealization,
    Finset.card_le_card hsubset, hfirst, hsecond⟩

/-- A bounded cyclic cut after width-preserving saturation.  Unlike the raw
existence predicate, this receipt records connected complementary induced
sides and can therefore be consumed without another ambient graph search. -/
structure ConnectedAtWidth (G : SimpleGraph V) [DecidableRel G.Adj]
    (bound : Nat) where
  edgeCut : Finset G.edgeSet
  realization : CyclicEdgeCutRealization G edgeCut
  card_le : edgeCut.card ≤ bound
  side_connected : (G.induce realization.side).Connected
  complement_connected :
    (G.induce (fun vertex => ¬ realization.side vertex)).Connected

/-- Saturate one specified cyclic cut while retaining the fact that the
connected result uses only edges of the original cut.  This is the
provenance-preserving form needed when the original cut came from a concrete
geometric separator. -/
theorem exists_connectedAtWidth_subcut
    (hconnected : G.Connected)
    {edgeCut : Finset G.edgeSet}
    (realization : CyclicEdgeCutRealization G edgeCut)
    (bound : Nat) (hcard : edgeCut.card ≤ bound) :
    ∃ connected : ConnectedAtWidth G bound,
      connected.edgeCut ⊆ edgeCut := by
  rcases realization.exists_connectedSides_subcut hconnected with
    ⟨connectedCut, connectedRealization, hsubset, hside, hcomplement⟩
  exact ⟨
    { edgeCut := connectedCut
      realization := connectedRealization
      card_le := (Finset.card_le_card hsubset).trans hcard
      side_connected := hside
      complement_connected := hcomplement },
    hsubset⟩

/-- Every bounded cyclic cut in a connected finite graph has a saturated
connected receipt at the same width. -/
theorem exists_connectedAtWidth_of_hasCyclicEdgeCutOfSizeAtMost
    (hconnected : G.Connected) (bound : Nat)
    (hcut : HasCyclicEdgeCutOfSizeAtMost G bound) :
    Nonempty (ConnectedAtWidth G bound) := by
  rcases hcut with ⟨edgeCut, ⟨realization⟩, hcard⟩
  rcases realization.exists_connectedAtWidth_subcut hconnected bound hcard with
    ⟨connected, _hsubset⟩
  exact ⟨connected⟩

end

end CyclicEdgeCutRealization

end Mettapedia.GraphTheory.FourColor
