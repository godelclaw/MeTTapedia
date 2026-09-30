import Mettapedia.GraphTheory.FourColor.DualTruncateColoring
import Mettapedia.GraphTheory.FourColor.SourceConstructionGSLT
import Mettapedia.GraphTheory.FourColor.RotationSystemExactTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideReassembly

/-!
# Dual-and-truncate colouring witnesses on actual construction routes

The local reconstruction is consumed by the existing source encoder and
its faithful GSLT interpretation. Every complete sweep order of the literal
expanded map supports compatible choices. Exact dart, vertex and rotation
relabelings give the same result on another representation of that map.
The source three-vertex colouring remains an explicit input.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateConstructionGSLT

open DualTruncateColoring GoertzelV24FaceDualConnectedness
open GoertzelV24TwoEdgeCutMinimality
open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace
open VertexConstructionGSLT

noncomputable section
attribute [local instance] Classical.propDecidable

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u,u,u} V E)

theorem rotationCyclic : VertexRotationCyclic (rotation RS) := by
  rintro ⟨d, i⟩ ⟨e, j⟩ h
  change d = e at h
  subst e
  have h01 : (rotation RS).rho.SameCycle (d, 0) (d, 1) :=
    ⟨1, by simp [rho]⟩
  have h12 : (rotation RS).rho.SameCycle (d, 1) (d, 2) :=
    ⟨1, by simp [rho]⟩
  have h02 := h01.trans h12
  fin_cases i <;> fin_cases j <;>
    first
    | exact Equiv.Perm.SameCycle.refl _ _
    | exact h01
    | exact h12
    | exact h02
    | exact h01.symm
    | exact h12.symm
    | exact h02.symm

theorem tait (c : ThreeVertexColoring RS) :
    RotationSystemTaitColorable (rotation RS) :=
  ⟨colouring RS c, colouring_nonzero RS c⟩

/-- The reconstructed witness supports the exact encoded construction,
including all intermediate boundary choices, for every complete order. -/
theorem supported_encoded_route (c : ThreeVertexColoring RS)
    (order : List RS.D) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed (cubic RS) (rotationCyclic RS) order hn he hcover).trace)
      Fin.elim0 Fin.elim0 :=
  (SourceConstructionGSLT.encoded_support_iff (cubic RS) (rotationCyclic RS)
    order hn he hcover).mpr (tait RS c)

variable {W F : Type u} [Fintype W] [DecidableEq W] [Fintype F] [DecidableEq F]
  (target : RotationSystem.{u,u,u} W F)
  (d : (rotation RS).D ≃ target.D) (v : RS.D ≃ W)
  (ha : ∀ x, d ((rotation RS).alpha x) = target.alpha (d x))
  (hv : ∀ x, v ((rotation RS).vertOf x) = target.vertOf (d x))
  (hr : ∀ x, d ((rotation RS).rho x) = target.rho (d x))

include d v ha hv in
/-- An exact representation adapter transports the genuine reconstructed
colouring; only edge pairs and vertex fibres are needed by this consumer. -/
theorem tait_relabelled (c : ThreeVertexColoring RS) :
    RotationSystemTaitColorable target :=
  GoertzelV24VertexSideReassembly.rotationSystemTaitColorable_of_dartEquiv
    (rotation RS) target d v ha hv (tait RS c)

include ha in
/-- On the relabelled map, the same reconstruction gives a supported
operational route. Rotation compatibility is retained by the actual encoder. -/
theorem supported_relabelled_route (c : ThreeVertexColoring RS)
    (order : List W) (hn : order.Nodup) (he : order ≠ [])
    (hcover : ∀ w, visited order w) :
    VertexConstructionGSLT.colouring.Supports
      (route (encodeClosed
        (RotationSystemExactTransport.cubic (rotation RS) target d v hv (cubic RS))
        (RotationSystemExactTransport.rotationCyclic (rotation RS) target d v hv hr
          (rotationCyclic RS)) order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  (SourceConstructionGSLT.encoded_support_iff
    (RotationSystemExactTransport.cubic (rotation RS) target d v hv (cubic RS))
    (RotationSystemExactTransport.rotationCyclic (rotation RS) target d v hv hr
      (rotationCyclic RS)) order hn he hcover).mpr
        (tait_relabelled RS target d v ha hv c)

end
end Mettapedia.GraphTheory.FourColor.DualTruncateConstructionGSLT
