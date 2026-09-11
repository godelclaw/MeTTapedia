import Mettapedia.GraphTheory.FourColor.BoundaryConnectivity
import Mettapedia.GraphTheory.FourColor.VertexSideCappedComponents
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideOpenTangle

/-!
# Boundary connectivity codes for actual open-tangle replacement

The generic path-compression theorem applies to the actual tangle
constructor through its existing multigraph isomorphism. Port visibility
is derived for arbitrary proper vertex sides, not supplied by a new
connected-side field. Equal boundary connectivity codes preserve primal
connectedness in every fixed exterior, including disconnected exteriors.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryConnectivity

open GoertzelV24BoundaryEssentialGluing GoertzelV24BoundaryEssentialGluing.Multigraph
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24RotationMultigraphAdapter GoertzelV24FaceDualConnectedness
open GoertzelV24RotationCutDartDecomposition GoertzelV24VertexSideOpenTangle
open VertexSideCappedComponents BoundaryConnectivity

noncomputable section
attribute [local instance] Classical.propDecidable

section VertexSide
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]

theorem sideReach_of_induce_reachable (RS : RotationSystem V E) (side : V → Prop)
    (outer : RetainedDart RS side) {u v : {v // side v}}
    (h : (SideGraph RS side).Reachable u v) :
    (sideMultigraph (OpenTangleData.ofVertexSide RS side outer)).Reach u v := by
  obtain ⟨walk⟩ := h
  induction walk with
  | nil => exact .refl
  | cons hadj _ ih =>
    exact (Relation.ReflTransGen.single (sideStep_of_induce_adj RS side outer hadj)).trans ih

theorem sideReach_iff_induce_reachable (RS : RotationSystem V E) (side : V → Prop)
    (outer : RetainedDart RS side) (u v : {v // side v}) :
    (sideMultigraph (OpenTangleData.ofVertexSide RS side outer)).Reach u v ↔
      (SideGraph RS side).Reachable u v := by
  refine ⟨?_, sideReach_of_induce_reachable RS side outer⟩
  intro h
  induction h with
  | refl => exact SimpleGraph.Reachable.refl _
  | tail _ hs ih =>
    obtain ⟨e, _, he⟩ := hs
    have ha : (SideGraph RS side).Adj
        ((sideMultigraph (OpenTangleData.ofVertexSide RS side outer)).fst e)
        ((sideMultigraph (OpenTangleData.ofVertexSide RS side outer)).snd e) :=
      ⟨e.2.choose.val.val, rfl, rfl⟩
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ih.trans ha.reachable
    · exact ih.trans ha.symm.reachable

/-- Proper vertex sides are port-visible, even when disconnected. -/
theorem visible_ofVertexSide (RS : RotationSystem V E) (side : V → Prop)
    (outer : RetainedDart RS side) (hconn : (rotationPrimalGraph RS).Connected)
    (hproper : ∃ v, ¬ side v) :
    PortVisible (sideMultigraph (OpenTangleData.ofVertexSide RS side outer))
      (OpenTangleData.ofVertexSide RS side outer).boundaryVert := by
  intro v
  obtain ⟨b, hb⟩ := boundaryComponent_surjective RS hconn side hproper
    ((SideGraph RS side).connectedComponentMk v)
  refine ⟨b, reach_symm ?_⟩
  exact sideReach_of_induce_reachable RS side outer (SimpleGraph.ConnectedComponent.exact hb)
end VertexSide

section Codes
variable {V I B K : Type*} [DecidableEq I]

/-- The actual boundary connectivity partition, in common coordinates.
The Boolean table is a finite carrier; no executable extractor is claimed. -/
def code (T : OpenTangleData V I B) (coords : B ≃ K) : K → K → Bool :=
  fun a b => decide ((sideMultigraph T).Reach
    (T.boundaryVert (coords.symm a)) (T.boundaryVert (coords.symm b)))

omit [DecidableEq I] in
theorem code_eq_true (T : OpenTangleData V I B) (coords : B ≃ K) (a b : K) :
    code T coords a b = true ↔ (sideMultigraph T).Reach
      (T.boundaryVert (coords.symm a)) (T.boundaryVert (coords.symm b)) := by
  simp only [code, decide_eq_true_eq]

theorem card_code_carrier [Fintype K] : Fintype.card (K → K → Bool) =
    2 ^ (Fintype.card K * Fintype.card K) := by
  simp only [Fintype.card_fun, Fintype.card_bool, pow_mul]

omit [DecidableEq I] in
theorem visible_reindex (T : OpenTangleData V I B)
    (h : PortVisible (sideMultigraph T) T.boundaryVert) (coords : K ≃ B) :
    PortVisible (sideMultigraph T) (fun p => T.boundaryVert (coords p)) := by
  intro v
  obtain ⟨b, hb⟩ := h v
  exact ⟨coords.symm b, by simpa only [coords.apply_symm_apply] using hb⟩
end Codes

section Composite
variable {V W I J L R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem composite_connected_iff_glue (left : OpenTangleData V I L)
    (right : OpenTangleData W J R) (matching : L ≃ R) :
    (rotationPrimalGraph (left.composeRotationSystem right matching)).Connected ↔
      (seamGlue left right matching).Connected := by
  letI : Nonempty V := ⟨left.vertOf left.outer⟩
  rw [← compositeRS_eq]
  constructor
  · intro h
    exact (compositeIso left right matching).connected_of (connected_of_primalConnected _ h)
  · intro h
    exact primalConnected_of_connected _ ((compositeIso left right matching).symm.connected_of h)

variable {W' J' R' K : Type*}
  [Fintype W'] [DecidableEq W'] [Fintype J'] [DecidableEq J']
  [Fintype R'] [DecidableEq R']

/-- Connectivity of the literal sewn rotation system depends only on the
replacement's boundary partition when its components all meet ports.
The exterior is arbitrary and need not itself be connected or port-visible. -/
theorem replacement_connected (left : OpenTangleData V I L)
    (old : OpenTangleData W J R) (new : OpenTangleData W' J' R')
    (hOld : PortVisible (sideMultigraph old) old.boundaryVert)
    (hNew : PortVisible (sideMultigraph new) new.boundaryVert)
    (oc : R ≃ K) (nc : R' ≃ K) (outside : L ≃ K)
    (heq : code old oc = code new nc) :
    (rotationPrimalGraph (left.composeRotationSystem old (outside.trans oc.symm))).Connected ↔
      (rotationPrimalGraph (left.composeRotationSystem new (outside.trans nc.symm))).Connected := by
  rw [composite_connected_iff_glue, composite_connected_iff_glue]
  obtain ⟨r, _⟩ := hOld (old.vertOf old.outer)
  apply BoundaryConnectivity.replacement_connected_any_exterior
    (sideMultigraph left) (sideMultigraph old) left.boundaryVert
    (fun l => old.boundaryVert ((outside.trans oc.symm) l))
    (sideMultigraph new) (fun l => new.boundaryVert ((outside.trans nc.symm) l))
    (outside.symm (oc r)) (visible_reindex old hOld _) (visible_reindex new hNew _)
  intro a b
  have hc := congrFun (congrFun heq (outside a)) (outside b)
  exact (code_eq_true old oc _ _).symm.trans
    ((congrArg (fun x : Bool => x = true) hc).to_iff.trans (code_eq_true new nc _ _))
end Composite

end
end Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryConnectivity
