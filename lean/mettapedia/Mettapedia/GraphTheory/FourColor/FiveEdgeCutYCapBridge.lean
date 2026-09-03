import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCapFaces
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationEdgeBridge

/-!
# Bridge-freeness of the Y-capped shore

Every edge of the Y-capped shore lies on a cycle.  A spoke reconnects
through another spoke and the connected retained side; the seam reconnects
through the retained side alone, since both its endpoints are retained.
An internal retained edge takes an ambient detour avoiding the removed
edge and both seam-forming cut edges: such a detour crosses the cut only
through star positions, so collapsing the deleted side to the star vertex
maps it onto a capped path.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceDualConnectedness
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace FiveEdgeCutYCapData

variable {RS : RotationSystem V E} (data : FiveEdgeCutYCapData RS)

/-! ## The new edges -/

/-- The spoke edge at one star position. -/
def capSpokeEdge (spoke : Fin 3) : data.capRewiredDartSystem.Edge :=
  data.capRewiredDartSystem.edgeOf (data.capDart spoke)

/-- The seam edge joining the two retained seam endpoints. -/
def seamEdge : data.capRewiredDartSystem.Edge :=
  data.capRewiredDartSystem.edgeOf (Sum.inl (Sum.inr false))

/-- The retained endpoint of one seam half-edge. -/
def seamBoundaryVertex (part : Bool) : RetainedVertex data.keep :=
  ⟨RS.vertOf (data.seamDart part).1.1, (data.seamDart part).1.2⟩

theorem seamEdge_eq (part : Bool) :
    data.capRewiredDartSystem.edgeOf (Sum.inl (Sum.inr part)) =
      data.seamEdge := by
  cases part
  · rfl
  · calc
      data.capRewiredDartSystem.edgeOf (Sum.inl (Sum.inr true)) =
          data.capRewiredDartSystem.edgeOf
            (data.capRewiredDartSystem.alpha (Sum.inl (Sum.inr false))) := by
        rw [data.capRewiredDartSystem_alpha_seam]
        rfl
      _ = data.seamEdge :=
        data.capRewiredDartSystem.edgeOf_alpha _

/-- The three spoke edges are distinct. -/
theorem capSpokeEdge_injective : Function.Injective data.capSpokeEdge := by
  intro first second hedges
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (data.capDart first) (data.capDart second)).1 hedges with
    hdarts | hdarts
  · exact Sum.inr.inj (Sum.inr.inj hdarts)
  · exfalso
    unfold capDart at hdarts
    rw [data.capRewiredDartSystem_alpha_cap] at hdarts
    simp at hdarts

/-! ## Distinctness of edge classes -/

theorem capRotationSystem_edgeOf_internal_ne_of_edgeOf_ne
    (left right : InternalDart RS data.keep)
    (hne : RS.edgeOf left.1.1 ≠ RS.edgeOf right.1.1) :
    data.capRotationSystem.edgeOf (Sum.inl (Sum.inl left)) ≠
      data.capRotationSystem.edgeOf (Sum.inl (Sum.inl right)) := by
  intro hedges
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (Sum.inl (Sum.inl left)) (Sum.inl (Sum.inl right))).1 hedges with
    hsame | hopposite
  · apply hne
    exact congrArg RS.edgeOf (congrArg Subtype.val (congrArg Subtype.val
      (Sum.inl.inj (Sum.inl.inj hsame))))
  · rw [data.capRewiredDartSystem_alpha_internal] at hopposite
    have hdarts : left.1.1 = (internalAlpha RS data.keep right).1.1 :=
      congrArg Subtype.val (congrArg Subtype.val
        (Sum.inl.inj (Sum.inl.inj hopposite)))
    apply hne
    rw [hdarts, internalAlpha_val, RS.edge_alpha]

theorem capRotationSystem_edgeOf_internal_ne_capSpokeEdge
    (internal : InternalDart RS data.keep) (spoke : Fin 3) :
    data.capRotationSystem.edgeOf (Sum.inl (Sum.inl internal)) ≠
      data.capSpokeEdge spoke := by
  intro hedge
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (Sum.inl (Sum.inl internal)) (data.capDart spoke)).1 hedge with
    hsame | hopposite
  · simp [capDart] at hsame
  · unfold capDart at hopposite
    rw [data.capRewiredDartSystem_alpha_cap] at hopposite
    simp at hopposite

theorem capRotationSystem_edgeOf_internal_ne_seamEdge
    (internal : InternalDart RS data.keep) :
    data.capRotationSystem.edgeOf (Sum.inl (Sum.inl internal)) ≠
      data.seamEdge := by
  intro hedge
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (Sum.inl (Sum.inl internal)) (Sum.inl (Sum.inr false))).1 hedge with
    hsame | hopposite
  · simp at hsame
  · rw [data.capRewiredDartSystem_alpha_seam] at hopposite
    simp at hopposite

theorem capSpokeEdge_ne_seamEdge (spoke : Fin 3) :
    data.capSpokeEdge spoke ≠ data.seamEdge := by
  intro hedge
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (data.capDart spoke) (Sum.inl (Sum.inr false))).1 hedge with
    hsame | hopposite
  · simp [capDart] at hsame
  · rw [data.capRewiredDartSystem_alpha_seam] at hopposite
    simp [capDart] at hopposite

/-! ## Adjacencies surviving one deletion -/

theorem edgeDeletedPrimalGraph_adj_internal
    (removed : data.capRewiredDartSystem.Edge)
    (internal : InternalDart RS data.keep)
    (hne : data.capRotationSystem.edgeOf (Sum.inl (Sum.inl internal)) ≠
      removed) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Adj
      (Sum.inl
        (⟨RS.vertOf internal.1.1, internal.1.2⟩ :
          RetainedVertex data.keep))
      (Sum.inl
        (⟨RS.vertOf (RS.alpha internal.1.1), internal.2⟩ :
          RetainedVertex data.keep)) := by
  exact ⟨Sum.inl (Sum.inl internal), hne, rfl, rfl⟩

theorem edgeDeletedPrimalGraph_adj_capSpoke
    (removed : data.capRewiredDartSystem.Edge) (spoke : Fin 3)
    (hne : data.capSpokeEdge spoke ≠ removed) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Adj
      (Sum.inr ()) (Sum.inl (data.starBoundaryVertex spoke)) := by
  refine ⟨data.capDart spoke, hne,
    data.capRotationSystem_vertOf_capDart spoke, ?_⟩
  rw [data.capRotationSystem_alpha_capDart,
    data.capRotationSystem_vertOf_capDartOfRetained]
  rfl

theorem edgeDeletedPrimalGraph_adj_seam
    (removed : data.capRewiredDartSystem.Edge)
    (hne : data.seamEdge ≠ removed) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Adj
      (Sum.inl (data.seamBoundaryVertex false))
      (Sum.inl (data.seamBoundaryVertex true)) := by
  refine ⟨Sum.inl (Sum.inr false), ?_, rfl, ?_⟩
  · rw [show data.capRotationSystem.edgeOf (Sum.inl (Sum.inr false)) =
      data.seamEdge from data.seamEdge_eq false]
    exact hne
  · rw [show data.capRotationSystem.alpha (Sum.inl (Sum.inr false)) =
      Sum.inl (Sum.inr true) from data.capRewiredDartSystem_alpha_seam false]
    rfl

/-! ## Retained transport around a deleted new edge -/

theorem edgeDeletedPrimalGraph_adj_of_retained_of_ne
    (removed : data.capRewiredDartSystem.Edge)
    (hne : ∀ internal : InternalDart RS data.keep,
      data.capRotationSystem.edgeOf (Sum.inl (Sum.inl internal)) ≠ removed)
    {left right : RetainedVertex data.keep}
    (hadj : (retainedAmbientPrimalGraph RS data.keep).Adj left right) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Adj
      (Sum.inl left) (Sum.inl right) := by
  change (rotationPrimalGraph RS).Adj left.1 right.1 at hadj
  rcases hadj with ⟨dart, hleft, hright⟩
  have hkeepLeft : data.keep (RS.vertOf dart) := by
    rw [hleft]
    exact left.2
  have hkeepRight : data.keep (RS.vertOf (RS.alpha dart)) := by
    rw [hright]
    exact right.2
  let internal : InternalDart RS data.keep :=
    ⟨⟨dart, hkeepLeft⟩, hkeepRight⟩
  have hcap := data.edgeDeletedPrimalGraph_adj_internal removed internal
    (hne internal)
  have hleftVertex :
      (⟨RS.vertOf dart, hkeepLeft⟩ : RetainedVertex data.keep) = left :=
    Subtype.ext hleft
  have hrightVertex :
      (⟨RS.vertOf (RS.alpha dart), hkeepRight⟩ :
        RetainedVertex data.keep) = right :=
    Subtype.ext hright
  simpa [internal, hleftVertex, hrightVertex] using hcap

theorem edgeDeletedPrimalGraph_reachable_of_retained_of_ne
    (removed : data.capRewiredDartSystem.Edge)
    (hne : ∀ internal : InternalDart RS data.keep,
      data.capRotationSystem.edgeOf (Sum.inl (Sum.inl internal)) ≠ removed)
    {left right : RetainedVertex data.keep}
    (hreachable :
      (retainedAmbientPrimalGraph RS data.keep).Reachable left right) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Reachable
      (Sum.inl left) (Sum.inl right) := by
  exact reachable_map_of_adj_eq_or_adj
    (fun vertex : RetainedVertex data.keep =>
      (Sum.inl vertex : data.CapVertex))
    (fun {_ _} hadj => Or.inr
      (data.edgeDeletedPrimalGraph_adj_of_retained_of_ne removed hne hadj))
    hreachable

/-- Deleting the seam leaves its endpoints connected through the retained
side. -/
theorem seam_endpoints_reachable_without_seamEdge
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected) :
    (edgeDeletedPrimalGraph data.capRotationSystem
      data.seamEdge).Reachable
      (Sum.inl (data.seamBoundaryVertex false))
      (Sum.inl (data.seamBoundaryVertex true)) :=
  data.edgeDeletedPrimalGraph_reachable_of_retained_of_ne data.seamEdge
    data.capRotationSystem_edgeOf_internal_ne_seamEdge
    (hconnected (data.seamBoundaryVertex false)
      (data.seamBoundaryVertex true))

/-- Deleting one spoke leaves its endpoints connected through another spoke
and the retained side. -/
theorem cap_endpoints_reachable_without_capSpoke
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected)
    (removedSpoke : Fin 3) :
    (edgeDeletedPrimalGraph data.capRotationSystem
      (data.capSpokeEdge removedSpoke)).Reachable
      (Sum.inr ()) (Sum.inl (data.starBoundaryVertex removedSpoke)) := by
  let alternateSpoke := finRotate 3 removedSpoke
  have halternate : alternateSpoke ≠ removedSpoke := by
    have hmem : removedSpoke ∈ (finRotate 3).support := by
      rw [support_finRotate_of_le (by omega)]
      simp
    exact Equiv.Perm.mem_support.mp hmem
  have hspoke := data.edgeDeletedPrimalGraph_adj_capSpoke
    (data.capSpokeEdge removedSpoke) alternateSpoke
    (data.capSpokeEdge_injective.ne halternate)
  have hretained := data.edgeDeletedPrimalGraph_reachable_of_retained_of_ne
    (data.capSpokeEdge removedSpoke)
    (fun internal =>
      data.capRotationSystem_edgeOf_internal_ne_capSpokeEdge
        internal removedSpoke)
    (hconnected (data.starBoundaryVertex alternateSpoke)
      (data.starBoundaryVertex removedSpoke))
  exact hspoke.reachable.trans hretained

/-! ## Internal edges through a seam-avoiding ambient detour -/

/-- A boundary dart avoiding both seam-forming cut edges is a star dart. -/
theorem boundaryDart_star_of_edge_ne
    (dart : BoundaryDart RS data.keep)
    (hedge0 : RS.edgeOf dart.1.1 ≠ data.crossing 0)
    (hedge1 : RS.edgeOf dart.1.1 ≠ data.crossing 1) :
    ∃ spoke, dart = data.starDart spoke := by
  rcases data.boundaryDart_eq_seam_or_star dart with
    ⟨part, hpart⟩ | ⟨spoke, hspoke⟩
  · exfalso
    cases part
    · exact hedge0 (by rw [hpart]; exact data.seamDart_edgeOf_false)
    · exact hedge1 (by rw [hpart]; exact data.seamDart_edgeOf_true)
  · exact ⟨spoke, hspoke⟩

/-- Collapse every deleted-side vertex to the new star vertex. -/
def collapseComplementToCapVertex (vertex : V) : data.CapVertex :=
  if hkeep : data.keep vertex then
    Sum.inl ⟨vertex, hkeep⟩
  else
    Sum.inr ()

@[simp]
theorem collapseComplementToCapVertex_of_keep
    (vertex : V) (hkeep : data.keep vertex) :
    data.collapseComplementToCapVertex vertex =
      Sum.inl (⟨vertex, hkeep⟩ : RetainedVertex data.keep) := by
  simp [collapseComplementToCapVertex, hkeep]

@[simp]
theorem collapseComplementToCapVertex_of_not_keep
    (vertex : V) (hkeep : ¬ data.keep vertex) :
    data.collapseComplementToCapVertex vertex = Sum.inr () := by
  simp [collapseComplementToCapVertex, hkeep]

/-- An ambient adjacency avoiding the removed internal edge and both
seam-forming cut edges collapses inside the deleted side or survives in
the edge-deleted cap. -/
theorem collapseComplement_adj_eq_or_adj_of_internal_removed
    (removed : InternalDart RS data.keep) (dart : RS.D)
    (hedge : RS.edgeOf dart ≠ RS.edgeOf removed.1.1)
    (hedge0 : RS.edgeOf dart ≠ data.crossing 0)
    (hedge1 : RS.edgeOf dart ≠ data.crossing 1) :
    data.collapseComplementToCapVertex (RS.vertOf dart) =
        data.collapseComplementToCapVertex
          (RS.vertOf (RS.alpha dart)) ∨
      (edgeDeletedPrimalGraph data.capRotationSystem
        (data.capRotationSystem.edgeOf
          (Sum.inl (Sum.inl removed)))).Adj
        (data.collapseComplementToCapVertex (RS.vertOf dart))
        (data.collapseComplementToCapVertex
          (RS.vertOf (RS.alpha dart))) := by
  by_cases hleft : data.keep (RS.vertOf dart)
  · by_cases hright : data.keep (RS.vertOf (RS.alpha dart))
    · right
      let internal : InternalDart RS data.keep :=
        ⟨⟨dart, hleft⟩, hright⟩
      have hne := data.capRotationSystem_edgeOf_internal_ne_of_edgeOf_ne
        internal removed hedge
      simpa [collapseComplementToCapVertex, hleft, hright, internal] using
        data.edgeDeletedPrimalGraph_adj_internal
          (data.capRotationSystem.edgeOf (Sum.inl (Sum.inl removed)))
          internal hne
    · let boundary : BoundaryDart RS data.keep :=
        ⟨⟨dart, hleft⟩, hright⟩
      rcases data.boundaryDart_star_of_edge_ne boundary hedge0 hedge1 with
        ⟨spoke, hspoke⟩
      have hne : data.capSpokeEdge spoke ≠
          data.capRotationSystem.edgeOf (Sum.inl (Sum.inl removed)) :=
        (data.capRotationSystem_edgeOf_internal_ne_capSpokeEdge
          removed spoke).symm
      have hcap := data.edgeDeletedPrimalGraph_adj_capSpoke
        (data.capRotationSystem.edgeOf (Sum.inl (Sum.inl removed)))
        spoke hne
      right
      have hvertex : data.starBoundaryVertex spoke =
          (⟨RS.vertOf dart, hleft⟩ : RetainedVertex data.keep) := by
        apply Subtype.ext
        show RS.vertOf (data.starDart spoke).1.1 = RS.vertOf dart
        rw [← hspoke]
      rw [data.collapseComplementToCapVertex_of_keep _ hleft,
        data.collapseComplementToCapVertex_of_not_keep _ hright,
        ← hvertex]
      exact hcap.symm
  · by_cases hright : data.keep (RS.vertOf (RS.alpha dart))
    · let boundary : BoundaryDart RS data.keep :=
        ⟨⟨RS.alpha dart, hright⟩, by
          change ¬ data.keep
            (RS.vertOf (RS.alpha (RS.alpha dart)))
          simpa [RS.alpha_involutive] using hleft⟩
      have hboundaryEdge : RS.edgeOf boundary.1.1 = RS.edgeOf dart :=
        RS.edge_alpha dart
      rcases data.boundaryDart_star_of_edge_ne boundary
          (by rw [hboundaryEdge]; exact hedge0)
          (by rw [hboundaryEdge]; exact hedge1) with
        ⟨spoke, hspoke⟩
      have hne : data.capSpokeEdge spoke ≠
          data.capRotationSystem.edgeOf (Sum.inl (Sum.inl removed)) :=
        (data.capRotationSystem_edgeOf_internal_ne_capSpokeEdge
          removed spoke).symm
      have hcap := data.edgeDeletedPrimalGraph_adj_capSpoke
        (data.capRotationSystem.edgeOf (Sum.inl (Sum.inl removed)))
        spoke hne
      right
      have hvertex : data.starBoundaryVertex spoke =
          (⟨RS.vertOf (RS.alpha dart), hright⟩ :
            RetainedVertex data.keep) := by
        apply Subtype.ext
        show RS.vertOf (data.starDart spoke).1.1 = RS.vertOf (RS.alpha dart)
        rw [← hspoke]
      rw [data.collapseComplementToCapVertex_of_not_keep _ hleft,
        data.collapseComplementToCapVertex_of_keep _ hright,
        ← hvertex]
      exact hcap
    · left
      simp [collapseComplementToCapVertex, hleft, hright]

/-- Adjacency through darts avoiding one removed internal edge and both
seam-forming cut edges. -/
def InternalDetourAdj (removed : InternalDart RS data.keep)
    (left right : V) : Prop :=
  ∃ dart : RS.D,
    RS.edgeOf dart ≠ RS.edgeOf removed.1.1 ∧
    RS.edgeOf dart ≠ data.crossing 0 ∧
    RS.edgeOf dart ≠ data.crossing 1 ∧
    RS.vertOf dart = left ∧
    RS.vertOf (RS.alpha dart) = right

/-- The ambient detour graph for one removed internal edge. -/
def internalDetourGraph (removed : InternalDart RS data.keep) :
    SimpleGraph V where
  Adj := data.InternalDetourAdj removed
  symm := by
    constructor
    intro left right hadj
    obtain ⟨dart, hedge, hedge0, hedge1, hleft, hright⟩ := hadj
    refine ⟨RS.alpha dart, ?_, ?_, ?_, hright, ?_⟩
    · rw [RS.edge_alpha]
      exact hedge
    · rw [RS.edge_alpha]
      exact hedge0
    · rw [RS.edge_alpha]
      exact hedge1
    · rw [RS.alpha_involutive]
      exact hleft
  loopless := by
    constructor
    intro vertex hadj
    obtain ⟨dart, _, _, _, hleft, hright⟩ := hadj
    exact RS.no_self_loops dart (hleft.trans hright.symm)

/-- A seam-avoiding ambient detour collapses onto a capped path around the
removed internal edge. -/
theorem cap_internal_reachable_of_detour
    (removed : InternalDart RS data.keep)
    (hdetour : (data.internalDetourGraph removed).Reachable
      (RS.vertOf removed.1.1) (RS.vertOf (RS.alpha removed.1.1))) :
    (edgeDeletedPrimalGraph data.capRotationSystem
      (data.capRotationSystem.edgeOf (Sum.inl (Sum.inl removed)))).Reachable
      (Sum.inl
        (⟨RS.vertOf removed.1.1, removed.1.2⟩ :
          RetainedVertex data.keep))
      (Sum.inl
        (⟨RS.vertOf (RS.alpha removed.1.1), removed.2⟩ :
          RetainedVertex data.keep)) := by
  have hmapped := reachable_map_of_adj_eq_or_adj
    data.collapseComplementToCapVertex
    (fun {_ _} hadj => by
      obtain ⟨dart, hedge, hedge0, hedge1, hleft, hright⟩ := hadj
      subst hleft
      subst hright
      exact data.collapseComplement_adj_eq_or_adj_of_internal_removed
        removed dart hedge hedge0 hedge1)
    hdetour
  simpa [collapseComplementToCapVertex, removed.1.2,
    removed.2] using hmapped

/-! ## Bridge-freeness -/

/-- The Y-cap is bridge-free: spokes and the seam reconnect through the
retained side, and each internal edge through its seam-avoiding ambient
detour. -/
theorem capRotationSystem_edgeBridgeFree
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected)
    (hdetour : ∀ removed : InternalDart RS data.keep,
      (data.internalDetourGraph removed).Reachable
        (RS.vertOf removed.1.1) (RS.vertOf (RS.alpha removed.1.1))) :
    EdgeBridgeFree data.capRotationSystem := by
  intro dart
  rcases dart with interior | boundaryOrCap
  · rcases interior with internal | part
    · exact data.cap_internal_reachable_of_detour internal
        (hdetour internal)
    · have hedge : data.capRotationSystem.edgeOf (Sum.inl (Sum.inr part)) =
        data.seamEdge := data.seamEdge_eq part
      rw [hedge]
      cases part
      · rw [show data.capRotationSystem.alpha (Sum.inl (Sum.inr false)) =
          Sum.inl (Sum.inr true) from
            data.capRewiredDartSystem_alpha_seam false]
        exact data.seam_endpoints_reachable_without_seamEdge hconnected
      · rw [show data.capRotationSystem.alpha (Sum.inl (Sum.inr true)) =
          Sum.inl (Sum.inr false) from
            data.capRewiredDartSystem_alpha_seam true]
        exact
          (data.seam_endpoints_reachable_without_seamEdge hconnected).symm
  · rcases boundaryOrCap with spoke | spoke
    · have hedge : data.capRotationSystem.edgeOf (Sum.inr (Sum.inl spoke)) =
          data.capSpokeEdge spoke := by
        calc
          data.capRotationSystem.edgeOf (Sum.inr (Sum.inl spoke)) =
              data.capRotationSystem.edgeOf
                (data.capRotationSystem.alpha (Sum.inr (Sum.inl spoke))) :=
            (data.capRotationSystem.edge_alpha _).symm
          _ = data.capSpokeEdge spoke := by
            rw [show data.capRotationSystem.alpha
                (Sum.inr (Sum.inl spoke)) = Sum.inr (Sum.inr spoke) from
              data.capRewiredDartSystem_alpha_star spoke]
            rfl
      rw [hedge]
      rw [show data.capRotationSystem.alpha (Sum.inr (Sum.inl spoke)) =
        Sum.inr (Sum.inr spoke) from
          data.capRewiredDartSystem_alpha_star spoke]
      exact
        (data.cap_endpoints_reachable_without_capSpoke
          hconnected spoke).symm
    · rw [show data.capRotationSystem.alpha (Sum.inr (Sum.inr spoke)) =
        Sum.inr (Sum.inl spoke) from
          data.capRewiredDartSystem_alpha_cap spoke]
      exact data.cap_endpoints_reachable_without_capSpoke hconnected spoke

end FiveEdgeCutYCapData

end

end Mettapedia.GraphTheory.FourColor
