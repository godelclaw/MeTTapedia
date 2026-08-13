import Mettapedia.GraphTheory.FourColor.GoertzelV24OpenRegionFaceTransport

/-!
# Retained endpoint incidence under a literal opening

The closed Cell-3 bounded-interaction theorem produces one ambient vertex
incident with two crossed primal edges.  The literal opening does not need to
inherit the whole closed minimality package in order to preserve that fact.
If the common vertex is retained, the two computed open edges still meet at
the corresponding retained vertex.

This is generic opening theory.  It does not select the Cell-3 retained side
or prove that the closed common vertex lies on it; those are the remaining
source-specific formation obligations.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OpenRegionEndpointIncidence

open GoertzelV24OpenRegionFaceTransport
open GoertzelV24OpenRegionRotation

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- A retained endpoint of an ambient edge on a fully retained face remains
an endpoint of the corresponding computed edge in the literal opening. -/
theorem retainedVertex_mem_openFaceEdge_endpoints
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (root : RS.D) (hface : FaceFullyRetained RS keep root)
    (point : {point // RS.phi.SameCycle root point})
    (vertex : V) (hkeep : keep vertex)
    (hvertex : vertex ∈ RS.endpoints (RS.edgeOf point.1)) :
    (Sum.inl ⟨vertex, hkeep⟩ : Vertex RS keep) ∈
      (rotationSystem RS keep outer).endpoints
        (openFaceEdge RS keep outer root hface point) := by
  let openRS := rotationSystem RS keep outer
  let openDart := openFaceDart RS keep root hface point
  have hpointOn : point.1 ∈ RS.dartsOn (RS.edgeOf point.1) :=
    (RS.mem_dartsOn).2 rfl
  rw [RS.endpoints_eq_pair_of_mem hpointOn] at hvertex
  simp only [Finset.mem_insert, Finset.mem_singleton] at hvertex
  rcases hvertex with hbase | hopposite
  · apply (openRS.mem_endpoints_iff).2
    refine ⟨openDart, (openRS.mem_dartsOn).2 rfl, ?_⟩
    change (Sum.inl
      ⟨RS.vertOf point.1, hface point.1 point.2⟩ : Vertex RS keep) =
        Sum.inl ⟨vertex, hkeep⟩
    apply congrArg Sum.inl
    apply Subtype.ext
    exact hbase.symm
  · have halphaKeep : keep (RS.vertOf (RS.alpha point.1)) :=
      alpha_endpoint_keep_of_faceFullyRetained RS keep root hface point
    apply (openRS.mem_endpoints_iff).2
    refine ⟨openRS.alpha openDart, ?_, ?_⟩
    · apply (openRS.mem_dartsOn).2
      change openRS.edgeOf (openRS.alpha openDart) = openRS.edgeOf openDart
      exact openRS.edge_alpha openDart
    · change openRS.vertOf
        (openRS.alpha
          (Sum.inl ⟨point.1, hface point.1 point.2⟩)) =
            Sum.inl ⟨vertex, hkeep⟩
      rw [rotationSystem_alpha_old_of_internal RS keep outer _ halphaKeep]
      apply congrArg Sum.inl
      apply Subtype.ext
      exact hopposite.symm

/-- A common retained endpoint of two ambient face edges remains one common
endpoint of their two computed open edges.  The faces and edge occurrences
may be different; only the retained vertex is shared. -/
theorem exists_common_retainedVertex_of_ambient
    (RS : RotationSystem V E) (keep : V → Prop)
    (outer : Dart RS keep)
    (leftRoot rightRoot : RS.D)
    (hleft : FaceFullyRetained RS keep leftRoot)
    (hright : FaceFullyRetained RS keep rightRoot)
    (left : {point // RS.phi.SameCycle leftRoot point})
    (right : {point // RS.phi.SameCycle rightRoot point})
    (vertex : V) (hkeep : keep vertex)
    (hvertexLeft : vertex ∈ RS.endpoints (RS.edgeOf left.1))
    (hvertexRight : vertex ∈ RS.endpoints (RS.edgeOf right.1)) :
    ∃ openVertex : Vertex RS keep,
      openVertex ∈ (rotationSystem RS keep outer).endpoints
        (openFaceEdge RS keep outer leftRoot hleft left) ∧
      openVertex ∈ (rotationSystem RS keep outer).endpoints
        (openFaceEdge RS keep outer rightRoot hright right) := by
  refine ⟨Sum.inl ⟨vertex, hkeep⟩, ?_, ?_⟩
  · exact retainedVertex_mem_openFaceEdge_endpoints
      RS keep outer leftRoot hleft left vertex hkeep hvertexLeft
  · exact retainedVertex_mem_openFaceEdge_endpoints
      RS keep outer rightRoot hright right vertex hkeep hvertexRight

end

end GoertzelV24OpenRegionEndpointIncidence

end Mettapedia.GraphTheory.FourColor
