import Mettapedia.GraphTheory.FourColor.GoertzelV24FaceDualConnectedness
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RotationEdgeBridge

open GoertzelV24FaceDualConnectedness
open SimpleGraphDartRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- The primal graph after deleting one rotation-system edge identifier.
Unlike deleting an edge of `rotationPrimalGraph`, this retains any parallel
edge with the same pair of endpoints. -/
def edgeDeletedPrimalGraph (RS : RotationSystem V E) (removed : E) :
    SimpleGraph V where
  Adj left right :=
    ∃ dart : RS.D,
      RS.edgeOf dart ≠ removed ∧
      RS.vertOf dart = left ∧
      RS.vertOf (RS.alpha dart) = right
  symm := ⟨by
    rintro left right ⟨dart, hedge, hleft, hright⟩
    refine ⟨RS.alpha dart, ?_, hright, ?_⟩
    · intro halpha
      exact hedge ((RS.edge_alpha dart).symm.trans halpha)
    · rw [RS.alpha_involutive, hleft]⟩
  loopless := ⟨by
    rintro vertex ⟨dart, _, hleft, hright⟩
    exact RS.no_self_loops dart (hleft.trans hright.symm)⟩

@[simp]
theorem edgeDeletedPrimalGraph_adj_iff
    (RS : RotationSystem V E) (removed : E) {left right : V} :
    (edgeDeletedPrimalGraph RS removed).Adj left right ↔
      ∃ dart : RS.D,
        RS.edgeOf dart ≠ removed ∧
        RS.vertOf dart = left ∧
        RS.vertOf (RS.alpha dart) = right :=
  Iff.rfl

theorem edgeDeletedPrimalGraph_le_rotationPrimalGraph
    (RS : RotationSystem V E) (removed : E) :
    edgeDeletedPrimalGraph RS removed ≤ rotationPrimalGraph RS := by
  rintro left right ⟨dart, _, hleft, hright⟩
  exact ⟨dart, hleft, hright⟩

omit [Fintype V] [DecidableEq V] in
/-- A vertex map that sends every source edge either to an equality or to a
target edge sends source reachability to target reachability. This is the
graph-theoretic contraction principle used when one side of a cut is
collapsed to a cap endpoint. -/
theorem reachable_map_of_adj_eq_or_adj
    {W : Type*} {source : SimpleGraph V} {target : SimpleGraph W}
    (mapVertex : V → W)
    (hmap : ∀ ⦃left right⦄, source.Adj left right →
      mapVertex left = mapVertex right ∨
        target.Adj (mapVertex left) (mapVertex right))
    {left right : V} (hreachable : source.Reachable left right) :
    target.Reachable (mapVertex left) (mapVertex right) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at hreachable
  have hlift : Relation.ReflTransGen target.Reachable
      (mapVertex left) (mapVertex right) :=
    Relation.ReflTransGen.lift mapVertex (fun first second hadj => by
      rcases hmap hadj with heq | htarget
      · rw [heq]
      · exact htarget.reachable) hreachable
  exact Relation.ReflTransGen.trans_induction_on
    (motive := fun {first second} _ =>
      target.Reachable first second) hlift
    (fun _ => SimpleGraph.Reachable.rfl)
    (fun hstep => hstep)
    (fun _ _ hfirst hsecond => hfirst.trans hsecond)

/-- A rotation system is bridge-free when the endpoints of every dart remain
connected after deleting that dart's edge identifier. This is the ordinary
multigraph notion and distinguishes parallel edges. -/
def EdgeBridgeFree (RS : RotationSystem V E) : Prop :=
  ∀ dart : RS.D,
    (edgeDeletedPrimalGraph RS (RS.edgeOf dart)).Reachable
      (RS.vertOf dart) (RS.vertOf (RS.alpha dart))

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- On graph-backed rotation data, deleting a rotation edge identifier is
exactly ordinary simple-graph edge deletion. -/
theorem edgeDeletedPrimalGraph_toRotationSystem_eq
    (data : Data G) (removed : G.edgeSet) :
    edgeDeletedPrimalGraph data.toRotationSystem removed =
      G.deleteEdges {removed.1} := by
  ext left right
  simp only [edgeDeletedPrimalGraph_adj_iff, SimpleGraph.deleteEdges_adj,
    Set.mem_singleton_iff]
  constructor
  · rintro ⟨dart, hedge, rfl, rfl⟩
    refine ⟨dart.adj, ?_⟩
    intro hedgeValue
    apply hedge
    apply Subtype.ext
    simpa [SimpleGraph.Dart.edge] using hedgeValue
  · rintro ⟨hadj, hedge⟩
    let dart : G.Dart := ⟨(left, right), hadj⟩
    refine ⟨dart, ?_, rfl, rfl⟩
    intro hdart
    apply hedge
    simpa [dart, SimpleGraph.Dart.edge] using congrArg Subtype.val hdart

/-- Thus the rotation-system predicate specializes to the usual statement
that no graph edge represented by a dart is a bridge. -/
theorem edgeBridgeFree_toRotationSystem_iff
    (data : Data G) :
    EdgeBridgeFree data.toRotationSystem ↔
      ∀ dart : G.Dart, ¬ G.IsBridge dart.edge := by
  constructor
  · intro hfree dart hbridge
    have hreach := hfree dart
    rw [edgeDeletedPrimalGraph_toRotationSystem_eq] at hreach
    apply (SimpleGraph.isBridge_iff.mp (by
      simpa [SimpleGraph.Dart.edge] using hbridge)) hreach
  · intro hfree dart
    rw [edgeDeletedPrimalGraph_toRotationSystem_eq]
    apply Classical.byContradiction
    intro hnotReachable
    apply hfree dart
    apply SimpleGraph.isBridge_iff.mpr
    simpa [SimpleGraph.Dart.edge] using hnotReachable

end

end GoertzelV24RotationEdgeBridge

end Mettapedia.GraphTheory.FourColor
