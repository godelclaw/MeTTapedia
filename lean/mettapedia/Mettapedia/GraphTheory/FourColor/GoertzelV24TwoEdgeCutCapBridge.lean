import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationEdgeBridge
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutCapGeometry

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TwoEdgeCutCapBridge

open GoertzelV24FaceDualConnectedness
open GoertzelV24OrderedCutRotationSplice
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace RotationSystem.TwoEdgeCutSideData

variable {RS : RotationSystem V E} (data : RS.TwoEdgeCutSideData)

/-- The two canonical exposed ambient darts before they are joined. -/
def leftBoundaryDart : BoundaryDart RS data.keep :=
  (orderedBoundaryDart RS data.keep data.leftCrossing
    data.leftCrosses (0 : Fin 1)).1

def rightBoundaryDart : BoundaryDart RS data.keep :=
  (orderedBoundaryDart RS data.keep data.rightCrossing
    data.rightCrosses (0 : Fin 1)).1

/-- The two canonical darts of the new cap edge. -/
def leftCapDart :
    MatchedSeam.Dart (InternalDart RS data.keep)
      (BoundaryDartOn RS data.keep (orderedCut data.leftCrossing))
      (BoundaryDartOn RS data.keep (orderedCut data.rightCrossing)) :=
  Sum.inr (Sum.inl
    (orderedBoundaryDart RS data.keep data.leftCrossing
      data.leftCrosses (0 : Fin 1)))

def rightCapDart :
    MatchedSeam.Dart (InternalDart RS data.keep)
      (BoundaryDartOn RS data.keep (orderedCut data.leftCrossing))
      (BoundaryDartOn RS data.keep (orderedCut data.rightCrossing)) :=
  Sum.inr (Sum.inr
    (orderedBoundaryDart RS data.keep data.rightCrossing
      data.rightCrosses (0 : Fin 1)))

/-- The retained endpoints joined by the new cap edge. -/
def leftCapVertex : data.CapVertex :=
  ⟨RS.vertOf (leftBoundaryDart data).1.1,
    (leftBoundaryDart data).1.2⟩

def rightCapVertex : data.CapVertex :=
  ⟨RS.vertOf (rightBoundaryDart data).1.1,
    (rightBoundaryDart data).1.2⟩

@[simp]
theorem capRotationSystem_vertOf_leftCapDart :
    data.capRotationSystem.vertOf (leftCapDart data) =
      leftCapVertex data :=
  rfl

@[simp]
theorem capRotationSystem_vertOf_rightCapDart :
    data.capRotationSystem.vertOf (rightCapDart data) =
      rightCapVertex data :=
  rfl

theorem leftCapVertex_ne_rightCapVertex :
    leftCapVertex data ≠ rightCapVertex data := by
  intro heq
  apply data.seamEndpoints (0 : Fin 1)
  exact congrArg Subtype.val heq

@[simp]
theorem capRotationSystem_alpha_leftCapDart :
    data.capRotationSystem.alpha (leftCapDart data) =
      rightCapDart data := by
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

@[simp]
theorem capRotationSystem_alpha_rightCapDart :
    data.capRotationSystem.alpha (rightCapDart data) =
      leftCapDart data := by
  rw [← capRotationSystem_alpha_leftCapDart data]
  exact data.capRotationSystem.alpha_involutive (leftCapDart data)

@[simp]
theorem capRotationSystem_edgeOf_leftCapDart :
    data.capRotationSystem.edgeOf (leftCapDart data) = data.capEdge :=
  rfl

@[simp]
theorem capRotationSystem_edgeOf_rightCapDart :
    data.capRotationSystem.edgeOf (rightCapDart data) = data.capEdge := by
  rw [← capRotationSystem_alpha_leftCapDart data,
    data.capRotationSystem.edge_alpha]
  exact capRotationSystem_edgeOf_leftCapDart data

/-- Distinct old internal edge identifiers remain distinct cap edges. -/
theorem capRotationSystem_edgeOf_internal_ne_of_edgeOf_ne
    (left right : InternalDart RS data.keep)
    (hne : RS.edgeOf left.1.1 ≠ RS.edgeOf right.1.1) :
    data.capRotationSystem.edgeOf (Sum.inl left) ≠
      data.capRotationSystem.edgeOf (Sum.inl right) := by
  intro hedges
  have hcases := (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
    (Sum.inl left) (Sum.inl right)).1 hedges
  rcases hcases with hsame | hopposite
  · apply hne
    exact congrArg RS.edgeOf (congrArg Subtype.val
      (congrArg Subtype.val (Sum.inl.inj hsame)))
  · change Sum.inl left =
      (orderedCutMatchedSeamData RS data.keep data.leftCrossing
        data.rightCrossing data.leftCrosses data.rightCrosses
        data.leftCrossing_injective data.rightCrossing_injective
        data.boundaryCover data.cutsDisjoint data.outer_mem).alpha
          (Sum.inl right) at hopposite
    rw [MatchedSeam.Data.alpha_interior] at hopposite
    have hdarts : left.1.1 = RS.alpha right.1.1 :=
      congrArg Subtype.val
        (congrArg Subtype.val (Sum.inl.inj hopposite))
    apply hne
    rw [hdarts, RS.edge_alpha]

/-- Every old internal edge remains distinct from the new cap edge. -/
theorem capRotationSystem_edgeOf_internal_ne_capEdge
    (internal : InternalDart RS data.keep) :
    data.capRotationSystem.edgeOf (Sum.inl internal) ≠ data.capEdge := by
  intro hedge
  have hedge' :
      data.capRotationSystem.edgeOf (Sum.inl internal) =
        data.capRotationSystem.edgeOf (leftCapDart data) :=
    hedge.trans (capRotationSystem_edgeOf_leftCapDart data).symm
  have hcases := (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
    (Sum.inl internal) (leftCapDart data)).1 hedge'
  rcases hcases with hsame | hopposite
  · simp [leftCapDart] at hsame
  · change Sum.inl internal =
      data.capRotationSystem.alpha (leftCapDart data) at hopposite
    rw [capRotationSystem_alpha_leftCapDart data] at hopposite
    simp [rightCapDart] at hopposite

/-- An intact ambient dart gives the corresponding adjacency after any
different cap edge is deleted. -/
theorem edgeDeletedPrimalGraph_adj_internal
    (removed : data.CapEdge) (internal : InternalDart RS data.keep)
    (hne : data.capRotationSystem.edgeOf (Sum.inl internal) ≠ removed) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Adj
      ⟨RS.vertOf internal.1.1, internal.1.2⟩
      ⟨RS.vertOf (RS.alpha internal.1.1), internal.2⟩ := by
  refine ⟨Sum.inl internal, hne, rfl, ?_⟩
  rfl

/-- Unless it is the deleted edge itself, the new cap edge joins its two
canonical retained endpoints in the edge-deleted primal graph. -/
theorem edgeDeletedPrimalGraph_adj_cap
    (removed : data.CapEdge) (hne : data.capEdge ≠ removed) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Adj
      (leftCapVertex data) (rightCapVertex data) := by
  refine ⟨leftCapDart data, ?_, rfl, ?_⟩
  · simpa using hne
  · rw [capRotationSystem_alpha_leftCapDart data]
    rfl

/-- Every exposed dart is one of the two canonical sides of the cap. -/
theorem boundaryDart_eq_left_or_right
    (dart : BoundaryDart RS data.keep) :
    dart = leftBoundaryDart data ∨ dart = rightBoundaryDart data := by
  have hedge := RS.boundaryDart_edge_mem_vertexSideEdgeBoundary data.side dart
  rw [data.boundary_eq] at hedge
  simp only [Finset.mem_insert, Finset.mem_singleton] at hedge
  rcases hedge with hedge | hedge
  · left
    apply boundaryDart_eq_of_edgeOf_eq RS data.keep
    simpa [leftBoundaryDart, RotationSystem.TwoEdgeCutSideData.leftCrossing]
      using hedge
  · right
    apply boundaryDart_eq_of_edgeOf_eq RS data.keep
    simpa [rightBoundaryDart,
      RotationSystem.TwoEdgeCutSideData.rightCrossing] using hedge

/-- Collapse the complementary ambient side to the first cap endpoint while
fixing every retained vertex. -/
def collapseComplementToLeftCapVertex (vertex : V) : data.CapVertex :=
  if hkeep : data.keep vertex then ⟨vertex, hkeep⟩
  else leftCapVertex data

@[simp]
theorem collapseComplementToLeftCapVertex_of_keep
    (vertex : V) (hkeep : data.keep vertex) :
    collapseComplementToLeftCapVertex data vertex = ⟨vertex, hkeep⟩ := by
  simp [collapseComplementToLeftCapVertex, hkeep]

@[simp]
theorem collapseComplementToLeftCapVertex_of_not_keep
    (vertex : V) (hkeep : ¬ data.keep vertex) :
    collapseComplementToLeftCapVertex data vertex = leftCapVertex data := by
  simp [collapseComplementToLeftCapVertex, hkeep]

/-- After deleting an old internal cap edge, collapsing the complementary
side sends every different ambient edge either to an equality, to another
internal cap edge, or to the new cap edge. -/
theorem collapseComplement_adj_eq_or_adj_of_internal_removed
    (removed : InternalDart RS data.keep) (dart : RS.D)
    (hedge : RS.edgeOf dart ≠ RS.edgeOf removed.1.1) :
    collapseComplementToLeftCapVertex data (RS.vertOf dart) =
        collapseComplementToLeftCapVertex data
          (RS.vertOf (RS.alpha dart)) ∨
      (edgeDeletedPrimalGraph data.capRotationSystem
        (data.capRotationSystem.edgeOf (Sum.inl removed))).Adj
        (collapseComplementToLeftCapVertex data (RS.vertOf dart))
        (collapseComplementToLeftCapVertex data
          (RS.vertOf (RS.alpha dart))) := by
  by_cases hleft : data.keep (RS.vertOf dart)
  · by_cases hright : data.keep (RS.vertOf (RS.alpha dart))
    · right
      let internal : InternalDart RS data.keep :=
        ⟨⟨dart, hleft⟩, hright⟩
      have hne := capRotationSystem_edgeOf_internal_ne_of_edgeOf_ne
        data internal removed hedge
      simpa [collapseComplementToLeftCapVertex, hleft, hright,
        internal] using edgeDeletedPrimalGraph_adj_internal data
          (data.capRotationSystem.edgeOf (Sum.inl removed)) internal hne
    · let boundary : BoundaryDart RS data.keep :=
        ⟨⟨dart, hleft⟩, hright⟩
      rcases boundaryDart_eq_left_or_right data boundary with
        hboundary | hboundary
      · left
        have hvertex :
            (⟨RS.vertOf dart, hleft⟩ : data.CapVertex) =
              leftCapVertex data := by
          apply Subtype.ext
          simpa [boundary, leftCapVertex] using congrArg
            (fun exposed : BoundaryDart RS data.keep =>
              RS.vertOf exposed.1.1) hboundary
        simp [collapseComplementToLeftCapVertex, hleft, hright,
          hvertex]
      · right
        have hvertex :
            (⟨RS.vertOf dart, hleft⟩ : data.CapVertex) =
              rightCapVertex data := by
          apply Subtype.ext
          simpa [boundary, rightCapVertex] using congrArg
            (fun exposed : BoundaryDart RS data.keep =>
              RS.vertOf exposed.1.1) hboundary
        have hcap := edgeDeletedPrimalGraph_adj_cap data
          (data.capRotationSystem.edgeOf (Sum.inl removed))
          (capRotationSystem_edgeOf_internal_ne_capEdge data removed).symm
        simpa [collapseComplementToLeftCapVertex, hleft, hright,
          hvertex] using hcap.symm
  · by_cases hright : data.keep (RS.vertOf (RS.alpha dart))
    · let boundary : BoundaryDart RS data.keep :=
        ⟨⟨RS.alpha dart, hright⟩, by
          change ¬ data.keep
            (RS.vertOf (RS.alpha (RS.alpha dart)))
          simpa [RS.alpha_involutive] using hleft⟩
      rcases boundaryDart_eq_left_or_right data boundary with
        hboundary | hboundary
      · left
        have hvertex :
            (⟨RS.vertOf (RS.alpha dart), hright⟩ : data.CapVertex) =
              leftCapVertex data := by
          apply Subtype.ext
          simpa [boundary, leftCapVertex] using congrArg
            (fun exposed : BoundaryDart RS data.keep =>
              RS.vertOf exposed.1.1) hboundary
        simp [collapseComplementToLeftCapVertex, hleft, hright,
          hvertex]
      · right
        have hvertex :
            (⟨RS.vertOf (RS.alpha dart), hright⟩ : data.CapVertex) =
              rightCapVertex data := by
          apply Subtype.ext
          simpa [boundary, rightCapVertex] using congrArg
            (fun exposed : BoundaryDart RS data.keep =>
              RS.vertOf exposed.1.1) hboundary
        have hcap := edgeDeletedPrimalGraph_adj_cap data
          (data.capRotationSystem.edgeOf (Sum.inl removed))
          (capRotationSystem_edgeOf_internal_ne_capEdge data removed).symm
        simpa [collapseComplementToLeftCapVertex, hleft, hright,
          hvertex] using hcap
    · left
      simp [collapseComplementToLeftCapVertex, hleft, hright]

/-- Ambient bridge-freeness supplies a cap path around every retained
internal edge after the complementary side is contracted. -/
theorem cap_internal_reachable_of_edgeBridgeFree
    (hfree : EdgeBridgeFree RS)
    (removed : InternalDart RS data.keep) :
    (edgeDeletedPrimalGraph data.capRotationSystem
      (data.capRotationSystem.edgeOf (Sum.inl removed))).Reachable
      ⟨RS.vertOf removed.1.1, removed.1.2⟩
      ⟨RS.vertOf (RS.alpha removed.1.1), removed.2⟩ := by
  have hreach := hfree removed.1.1
  have hmapped := reachable_map_of_adj_eq_or_adj
    (collapseComplementToLeftCapVertex data)
    (fun {left right} hadj => by
      rcases hadj with ⟨dart, hedge, hleft, hright⟩
      subst left
      subst right
      exact collapseComplement_adj_eq_or_adj_of_internal_removed
        data removed dart hedge)
    hreach
  simpa [collapseComplementToLeftCapVertex, removed.1.2,
    removed.2] using hmapped

/-- Every retained ambient adjacency survives after the new cap edge is
deleted, because it is represented by an old internal edge. -/
theorem retainedAmbientPrimalGraph_le_cap_delete_capEdge :
    retainedAmbientPrimalGraph RS data.keep ≤
      edgeDeletedPrimalGraph data.capRotationSystem data.capEdge := by
  intro left right hadj
  change (rotationPrimalGraph RS).Adj left.1 right.1 at hadj
  rcases hadj with ⟨dart, hleft, hright⟩
  let internal : InternalDart RS data.keep :=
    ⟨⟨dart, by rw [hleft]; exact left.2⟩,
      by rw [hright]; exact right.2⟩
  have hne := capRotationSystem_edgeOf_internal_ne_capEdge data internal
  have hcap := edgeDeletedPrimalGraph_adj_internal data data.capEdge
    internal hne
  have hleftVertex :
      (⟨RS.vertOf dart, internal.1.2⟩ : data.CapVertex) = left :=
    Subtype.ext hleft
  have hrightVertex :
      (⟨RS.vertOf (RS.alpha dart), internal.2⟩ : data.CapVertex) = right :=
    Subtype.ext hright
  rw [hleftVertex, hrightVertex] at hcap
  exact hcap

/-- Connectedness of the retained ambient side gives a path around the new
cap edge. -/
theorem cap_endpoints_reachable_without_capEdge
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected) :
    (edgeDeletedPrimalGraph data.capRotationSystem data.capEdge).Reachable
      (leftCapVertex data) (rightCapVertex data) := by
  exact (hconnected (leftCapVertex data) (rightCapVertex data)).mono
    (retainedAmbientPrimalGraph_le_cap_delete_capEdge data)

/-- Exact two-edge capping preserves the ordinary multigraph bridge-free
condition. Internal cap edges inherit an avoiding path from the ambient map;
the new cap edge inherits one from connectedness of the retained side. -/
theorem capRotationSystem_edgeBridgeFree
    (hfree : EdgeBridgeFree RS)
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected) :
    EdgeBridgeFree data.capRotationSystem := by
  intro dart
  rcases dart with internal | side
  · exact cap_internal_reachable_of_edgeBridgeFree data hfree internal
  · rcases side with left | right
    · rcases orderedBoundaryDart_surjective RS data.keep
        data.leftCrossing data.leftCrosses left with ⟨step, hstep⟩
      have hzero : step = (0 : Fin 1) := Subsingleton.elim _ _
      subst step
      subst left
      change (edgeDeletedPrimalGraph data.capRotationSystem
        (data.capRotationSystem.edgeOf (leftCapDart data))).Reachable
          (data.capRotationSystem.vertOf (leftCapDart data))
          (data.capRotationSystem.vertOf
            (data.capRotationSystem.alpha (leftCapDart data)))
      rw [capRotationSystem_edgeOf_leftCapDart,
        capRotationSystem_vertOf_leftCapDart,
        capRotationSystem_alpha_leftCapDart,
        capRotationSystem_vertOf_rightCapDart]
      exact cap_endpoints_reachable_without_capEdge data hconnected
    · rcases orderedBoundaryDart_surjective RS data.keep
        data.rightCrossing data.rightCrosses right with ⟨step, hstep⟩
      have hzero : step = (0 : Fin 1) := Subsingleton.elim _ _
      subst step
      subst right
      change (edgeDeletedPrimalGraph data.capRotationSystem
        (data.capRotationSystem.edgeOf (rightCapDart data))).Reachable
          (data.capRotationSystem.vertOf (rightCapDart data))
          (data.capRotationSystem.vertOf
            (data.capRotationSystem.alpha (rightCapDart data)))
      rw [capRotationSystem_edgeOf_rightCapDart,
        capRotationSystem_vertOf_rightCapDart,
        capRotationSystem_alpha_rightCapDart,
        capRotationSystem_vertOf_leftCapDart]
      exact (cap_endpoints_reachable_without_capEdge data hconnected).symm

end RotationSystem.TwoEdgeCutSideData

@[simp]
theorem edgeBridgeFree_withOuter_iff
    (RS : RotationSystem V E) (root : RS.D) :
    EdgeBridgeFree (RS.withOuter root) ↔ EdgeBridgeFree RS :=
  Iff.rfl

namespace RotationSystem.TwoEdgeCutPairData

variable {RS : RotationSystem V E} (data : RS.TwoEdgeCutPairData)

/-- The chosen capped half of an exact two-edge cut remains bridge-free. -/
theorem sideCap_edgeBridgeFree
    (hfree : EdgeBridgeFree RS)
    (hsideConnected :
      ((rotationPrimalGraph RS).induce
        {vertex | vertex ∈ data.side}).Connected) :
    EdgeBridgeFree data.sideData.capRotationSystem := by
  apply TwoEdgeCutSideData.capRotationSystem_edgeBridgeFree data.sideData
  · simpa [RotationSystem.TwoEdgeCutPairData.sideRootedRotationSystem]
      using hfree
  · change
      ((rotationPrimalGraph RS).induce
        {vertex | vertex ∈ data.side}).Connected
    exact hsideConnected

/-- The complementary capped half remains bridge-free as well. -/
theorem complementCap_edgeBridgeFree
    (hfree : EdgeBridgeFree RS)
    (hcomplementConnected :
      ((rotationPrimalGraph RS).induce
        {vertex | vertex ∈ data.sideᶜ}).Connected) :
    EdgeBridgeFree data.complementData.capRotationSystem := by
  apply TwoEdgeCutSideData.capRotationSystem_edgeBridgeFree
    data.complementData
  · simpa [RotationSystem.TwoEdgeCutPairData.complementRootedRotationSystem]
      using hfree
  · change
      ((rotationPrimalGraph RS).induce
        {vertex | vertex ∈ data.sideᶜ}).Connected
    exact hcomplementConnected

end RotationSystem.TwoEdgeCutPairData

end

end GoertzelV24TwoEdgeCutCapBridge

end Mettapedia.GraphTheory.FourColor
