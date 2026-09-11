import Mettapedia.GraphTheory.FourColor.ExecutableVertexCode
import Mettapedia.GraphTheory.FourColor.BoundarySmallCutViability

/-!
# Exact structural tests on physically decoded code runs

The evaluator's cut tests are identified with connectivity, bridge-freeness
and boundary visibility of the actual constructed object. In particular,
a completed nonempty object is terminal: continuing after its empty
frontier cannot produce a connected object. This prevents accumulating
closed components in the viable-prefix closure.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeViability

open VertexCodeTrace ExecutableVertexCode
open GoertzelV24OpenTangleComposition SerialTangleSmallCutTransfer
open GoertzelV24CompositeSeamMultigraph BoundarySmallCutExecutable
open BoundarySmallCutViability BoundaryConnectivity

def lastVertex : {r : ℕ} → (t : Trace r) → t.Vertex
  | _, .first _ _ => ()
  | _, .step _ _ _ => .inr ()

noncomputable section
attribute [local instance] Classical.propDecidable

theorem cuts_exact {r} (t : Trace r) :
    (evaluate t).cuts = extractTangle t.realize := by
  apply Finset.coe_injective
  rw [extractTangle_correct]
  exact congrArg SerialTangleJointTransfer.Signature.cuts (evaluate_physical t)

theorem graph_cuts_exact {r} (t : Trace r) :
    (evaluate t).cuts = extract (sideMultigraph (asOpen t.realize))
      (asOpen t.realize).boundaryVert := by
  apply Finset.coe_injective
  rw [extract_correct]
  exact congrArg SerialTangleJointTransfer.Signature.cuts (evaluate_physical t)

theorem connected_bridgeless_exact {r} (t : Trace r) :
    BoundarySmallCutExecutable.accepts (evaluate t).cuts = true ↔
      (sideMultigraph (asOpen t.realize)).Connected ∧
        (sideMultigraph (asOpen t.realize)).Bridgeless := by
  rw [graph_cuts_exact, accepts_extract]

theorem visibility_exact {r} (t : Trace r) :
    rejectsExtension (evaluate t).cuts = true ↔
      ¬ PortVisible (sideMultigraph (asOpen t.realize)) (asOpen t.realize).boundaryVert := by
  rw [cuts_exact, rejectsExtension_extractTangle]

/-- This forbids later vertices, not accepting the closed object itself. -/
theorem closed_rejects_extension (t : Trace 0) :
    rejectsExtension (evaluate t).cuts = true := by
  rw [visibility_exact]
  intro h
  obtain ⟨p, _⟩ := h (lastVertex t)
  cases p with
  | inl p => exact p.elim0
  | inr p => exact p.elim0

end
end Mettapedia.GraphTheory.FourColor.VertexCodeViability
