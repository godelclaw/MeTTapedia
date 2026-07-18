import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCapEuler
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationEdgeBridge

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceDualConnectedness
open GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace RotationSystem.ThreeEdgeCutSideData

variable {RS : RotationSystem V E} (data : ThreeEdgeCutSideData RS)

/-- The retained endpoint of one cap spoke. -/
def capBoundaryVertex (step : Fin 3) : RetainedVertex data.keep :=
  let boundary := data.crossingBoundaryDartEquiv step
  ⟨RS.vertOf boundary.1.1, boundary.1.2⟩

/-- Every retained ambient edge is still an edge between the corresponding
retained cap vertices. -/
theorem capPrimalGraph_adj_of_retained
    {left right : RetainedVertex data.keep}
    (hadj : (retainedAmbientPrimalGraph RS data.keep).Adj left right) :
    (rotationPrimalGraph data.capRotationSystem).Adj
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
  refine ⟨Sum.inl internal, ?_, ?_⟩
  · apply congrArg Sum.inl
    apply Subtype.ext
    exact hleft
  · change data.capSeamData.vertOf
      (data.capRewiredDartSystem.alpha (Sum.inl internal)) =
        Sum.inl right
    rw [data.capRewiredDartSystem_alpha_internal]
    apply congrArg Sum.inl
    apply Subtype.ext
    exact hright

/-- A cap dart is paired with the retained boundary dart at the same cut
position. -/
@[simp]
theorem capRotationSystem_alpha_capDart (step : Fin 3) :
    data.capRotationSystem.alpha (data.capDart step) =
      data.capDartOfRetained
        (data.crossingBoundaryDartEquiv step).1 := by
  change data.capRewiredDartSystem.alpha (data.capDart step) = _
  rw [data.capRewiredDartSystem_alpha_cap,
    data.capDartOfRetained_boundary]

/-- Each cap spoke joins the new cap vertex to its retained boundary
endpoint in the primal graph. -/
theorem capPrimalGraph_adj_capBoundaryVertex (step : Fin 3) :
    (rotationPrimalGraph data.capRotationSystem).Adj
      (Sum.inr ()) (Sum.inl (data.capBoundaryVertex step)) := by
  refine ⟨data.capDart step,
    data.capRotationSystem_vertOf_capDart step, ?_⟩
  rw [data.capRotationSystem_alpha_capDart,
    data.capRotationSystem_vertOf_capDartOfRetained]
  rfl

/-- Reachability inside the retained ambient side transports to
reachability between the corresponding cap vertices. -/
theorem capPrimalGraph_reachable_of_retained
    {left right : RetainedVertex data.keep}
    (hreachable :
      (retainedAmbientPrimalGraph RS data.keep).Reachable left right) :
    (rotationPrimalGraph data.capRotationSystem).Reachable
      (Sum.inl left) (Sum.inl right) := by
  exact reachable_map_of_adj_eq_or_adj
    (fun vertex : RetainedVertex data.keep =>
      (Sum.inl vertex : data.CapVertex))
    (fun {_ _} hadj =>
      Or.inr (data.capPrimalGraph_adj_of_retained hadj))
    hreachable

/-- A connected retained side remains connected after adjoining the cubic
cap vertex and its three spokes. -/
theorem capRotationSystem_primalConnected
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected) :
    (rotationPrimalGraph data.capRotationSystem).Connected := by
  refine { preconnected := ?_, nonempty := ⟨Sum.inr ()⟩ }
  intro left right
  let anchor := data.capBoundaryVertex (0 : Fin 3)
  have hspoke := data.capPrimalGraph_adj_capBoundaryVertex (0 : Fin 3)
  rcases left with left | leftCap <;>
    rcases right with right | rightCap
  · exact data.capPrimalGraph_reachable_of_retained
      (hconnected left right)
  · rcases rightCap with ⟨⟩
    exact (data.capPrimalGraph_reachable_of_retained
      (hconnected left anchor)).trans hspoke.symm.reachable
  · rcases leftCap with ⟨⟩
    exact hspoke.reachable.trans
      (data.capPrimalGraph_reachable_of_retained
        (hconnected anchor right))
  · rcases leftCap with ⟨⟩
    rcases rightCap with ⟨⟩
    exact SimpleGraph.Reachable.rfl

/-- A retained ambient rotation cycle remains a cycle in the retained
summand of the cap target rotation. -/
theorem capTargetRho_sameCycle_inl
    {left right : RetainedDart RS data.keep}
    (hcycle : (retainedRho RS data.keep).SameCycle left right) :
    data.capTargetRho.SameCycle (Sum.inl left) (Sum.inl right) := by
  rcases hcycle with ⟨power, hpower⟩
  refine ⟨power, ?_⟩
  change ((Equiv.sumCongr (retainedRho RS data.keep)
    (finRotate 3)) ^ power) (Sum.inl left) = Sum.inl right
  have hsum :
      (Equiv.sumCongr (retainedRho RS data.keep) (finRotate 3)) ^ power =
        Equiv.sumCongr ((retainedRho RS data.keep) ^ power)
          ((finRotate 3) ^ power) := by
    simpa using (map_zpow (Equiv.Perm.sumCongrHom
      (RetainedDart RS data.keep) (Fin 3))
        (retainedRho RS data.keep, finRotate 3) power).symm
  rw [hsum]
  exact congrArg Sum.inl hpower

/-- The standard three-cycle makes all cap-dart positions lie on one
rotation cycle. -/
theorem capTargetRho_sameCycle_inr (left right : Fin 3) :
    data.capTargetRho.SameCycle (Sum.inr left) (Sum.inr right) := by
  have hrotate : (finRotate 3).IsCycle :=
    isCycle_finRotate_of_le (by omega)
  have hleft : finRotate 3 left ≠ left := by
    have : left ∈ (finRotate 3).support := by
      rw [support_finRotate_of_le (by omega)]
      simp
    exact Equiv.Perm.mem_support.mp this
  have hright : finRotate 3 right ≠ right := by
    have : right ∈ (finRotate 3).support := by
      rw [support_finRotate_of_le (by omega)]
      simp
    exact Equiv.Perm.mem_support.mp this
  rcases hrotate.sameCycle hleft hright with ⟨power, hpower⟩
  refine ⟨power, ?_⟩
  change ((Equiv.sumCongr (retainedRho RS data.keep)
    (finRotate 3)) ^ power) (Sum.inr left) = Sum.inr right
  have hsum :
      (Equiv.sumCongr (retainedRho RS data.keep) (finRotate 3)) ^ power =
        Equiv.sumCongr ((retainedRho RS data.keep) ^ power)
          ((finRotate 3) ^ power) := by
    simpa using (map_zpow (Equiv.Perm.sumCongrHom
      (RetainedDart RS data.keep) (Fin 3))
        (retainedRho RS data.keep, finRotate 3) power).symm
  rw [hsum]
  exact congrArg Sum.inr hpower

/-- The three-star cap inherits one cyclic dart order at every retained
vertex, while the new cap vertex carries the standard three-cycle. -/
theorem capRotationSystem_vertexRotationCyclic
    (hcyclic : VertexRotationCyclic RS) :
    VertexRotationCyclic data.capRotationSystem := by
  intro left right hvertex
  have htargetVertex :
      data.capTargetVert (data.capDartEquiv left) =
        data.capTargetVert (data.capDartEquiv right) := by
    rw [← data.capSeamData_vertOf_eq_capTargetVert,
      ← data.capSeamData_vertOf_eq_capTargetVert]
    exact hvertex
  have htarget : data.capTargetRho.SameCycle
      (data.capDartEquiv left) (data.capDartEquiv right) := by
    generalize hleftTarget : data.capDartEquiv left = leftTarget at htargetVertex ⊢
    generalize hrightTarget : data.capDartEquiv right = rightTarget at htargetVertex ⊢
    rcases leftTarget with retainedLeft | capLeft <;>
      rcases rightTarget with retainedRight | capRight
    · have hunderlyingVertex :
          RS.vertOf retainedLeft.1 = RS.vertOf retainedRight.1 := by
        change (Sum.inl
            (⟨RS.vertOf retainedLeft.1, retainedLeft.2⟩ :
              RetainedVertex data.keep) : data.CapVertex) =
          Sum.inl
            (⟨RS.vertOf retainedRight.1, retainedRight.2⟩ :
              RetainedVertex data.keep) at htargetVertex
        exact congrArg Subtype.val (Sum.inl.inj htargetVertex)
      have hambient : RS.rho.SameCycle retainedLeft.1 retainedRight.1 :=
        hcyclic _ _ hunderlyingVertex
      exact data.capTargetRho_sameCycle_inl
        (Equiv.Perm.SameCycle.subtypePerm hambient)
    · change (Sum.inl _ : data.CapVertex) = Sum.inr () at htargetVertex
      exact False.elim (by cases htargetVertex)
    · change (Sum.inr () : data.CapVertex) = Sum.inl _ at htargetVertex
      exact False.elim (by cases htargetVertex)
    · exact data.capTargetRho_sameCycle_inr capLeft capRight
  have htransport :=
    (permCongr_sameCycle_iff data.capDartEquiv.symm data.capTargetRho
      (data.capDartEquiv left) (data.capDartEquiv right)).2 htarget
  have hrho : data.capRho =
      data.capDartEquiv.symm.permCongr data.capTargetRho := by
    apply Equiv.ext
    intro dart
    simp [capRho, Equiv.permCongr_apply]
  change data.capRho.SameCycle left right
  rw [hrho]
  simpa using htransport

end RotationSystem.ThreeEdgeCutSideData

end

end Mettapedia.GraphTheory.FourColor
