import Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryConnectivity
import Mettapedia.GraphTheory.FourColor.SmallCutConnectedBridgeless
import Mathlib.Data.Finset.Sym

/-!
# Low-cut records for actual open-tangle replacement

The finite realized cut signature preserves connectedness and absence of
bridging edge identifiers under the literal rotation-system constructor.
No assumption of connected or port-visible pieces is imposed. Euler and
colouring semantics remain separate coordinates of a full interface.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleSmallCutReplacement

open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24FaceDualConnectedness GoertzelV24RotationMultigraphAdapter
open GoertzelV24RotationEdgeBridge GoertzelV24BoundaryEssentialGluing
open BoundarySmallCutProfile

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W W' I J J' L R R' K : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype W'] [DecidableEq W'] [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Fintype J'] [DecidableEq J']
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  [Fintype R'] [DecidableEq R']

local instance sideEdgeFintype (T : OpenTangleData W J R) : Fintype (SideEdge T) := by
  unfold SideEdge
  infer_instance

/-- A code is the set of realized cut states in common port coordinates. -/
def code (T : OpenTangleData W J R) (coords : R ≃ K) : Set (State K) :=
  profile (sideMultigraph T) (T.boundaryVert ∘ coords.symm)

theorem composite_structural_iff (left : OpenTangleData V I L)
    (right : OpenTangleData W J R) (matching : L ≃ R) :
    ((rotationPrimalGraph (left.composeRotationSystem right matching)).Connected ∧
      EdgeBridgeFree (left.composeRotationSystem right matching)) ↔
    ((seamGlue left right matching).Connected ∧ (seamGlue left right matching).Bridgeless) := by
  rw [OpenTangleBoundaryConnectivity.composite_connected_iff_glue]
  apply and_congr_right
  intro _
  rw [← bridgeless_iff_edgeBridgeFree, ← compositeRS_eq]
  exact ⟨(compositeIso left right matching).bridgeless_of,
    (compositeIso left right matching).symm.bridgeless_of⟩

/-- The actual sewn graph conditions factor through the finite cut code,
for arbitrary fixed exteriors and different internal carriers. -/
theorem replacement_connected_bridgeFree (left : OpenTangleData V I L)
    (old : OpenTangleData W J R) (new : OpenTangleData W' J' R')
    (oc : R ≃ K) (nc : R' ≃ K) (outside : L ≃ K)
    (h : code old oc = code new nc) :
    ((rotationPrimalGraph (left.composeRotationSystem old (outside.trans oc.symm))).Connected ∧
      EdgeBridgeFree (left.composeRotationSystem old (outside.trans oc.symm))) ↔
    ((rotationPrimalGraph (left.composeRotationSystem new (outside.trans nc.symm))).Connected ∧
      EdgeBridgeFree (left.composeRotationSystem new (outside.trans nc.symm))) := by
  rw [composite_structural_iff, composite_structural_iff]
  apply SmallCutConnectedBridgeless.replacement_connected_bridgeless
    (sideMultigraph left) (sideMultigraph old) (sideMultigraph new) left.boundaryVert
    (fun l => old.boundaryVert ((outside.trans oc.symm) l))
    (fun l => new.boundaryVert ((outside.trans nc.symm) l))
  change profile (sideMultigraph old) ((old.boundaryVert ∘ oc.symm) ∘ outside) =
    profile (sideMultigraph new) ((new.boundaryVert ∘ nc.symm) ∘ outside)
  rw [profile_reindex _ (old.boundaryVert ∘ oc.symm) outside,
    profile_reindex _ (new.boundaryVert ∘ nc.symm) outside]
  exact congrArg (fun p => reindex outside '' p) h

end
end Mettapedia.GraphTheory.FourColor.OpenTangleSmallCutReplacement
