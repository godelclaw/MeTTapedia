import Mettapedia.GraphTheory.FourColor.FiveEdgeCutYCap
import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCapStructure

/-!
# Structural class facts for the Y-cap of a five-cut shore

The Y-capped shore keeps its primal connectivity — the retained side is
untouched, the seam joins two retained vertices, and the star vertex hangs
on three spokes — and inherits one cyclic dart rotation at every vertex:
retained vertices keep their old rotations, the star vertex carries the
standard three-cycle.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceDualConnectedness
open GoertzelV24OrderedCutFaceReturnProfile
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

/-! ## The rewired involution, case by case -/

@[simp]
theorem capRewiredDartSystem_alpha_internal
    (internal : InternalDart RS data.keep) :
    data.capRewiredDartSystem.alpha (Sum.inl (Sum.inl internal)) =
      Sum.inl (Sum.inl (internalAlpha RS data.keep internal)) :=
  rfl

@[simp]
theorem capRewiredDartSystem_alpha_seam (part : Bool) :
    data.capRewiredDartSystem.alpha (Sum.inl (Sum.inr part)) =
      Sum.inl (Sum.inr (seamPairSwap part)) :=
  rfl

@[simp]
theorem capRewiredDartSystem_alpha_star (spoke : Fin 3) :
    data.capRewiredDartSystem.alpha (Sum.inr (Sum.inl spoke)) =
      Sum.inr (Sum.inr spoke) :=
  rfl

@[simp]
theorem capRewiredDartSystem_alpha_cap (spoke : Fin 3) :
    data.capRewiredDartSystem.alpha (Sum.inr (Sum.inr spoke)) =
      Sum.inr (Sum.inl spoke) :=
  rfl

/-! ## Dart embeddings and vertices -/

@[simp]
theorem capDartOfRetained_internal
    (internal : InternalDart RS data.keep) :
    data.capDartOfRetained internal.1 = Sum.inl (Sum.inl internal) := by
  apply data.capDartEquiv.injective
  simp

@[simp]
theorem capDartOfRetained_seam (part : Bool) :
    data.capDartOfRetained (data.seamDart part).1 =
      Sum.inl (Sum.inr part) := by
  apply data.capDartEquiv.injective
  simp

@[simp]
theorem capDartOfRetained_star (spoke : Fin 3) :
    data.capDartOfRetained (data.starDart spoke).1 =
      Sum.inr (Sum.inl spoke) := by
  apply data.capDartEquiv.injective
  simp

@[simp]
theorem capRotationSystem_vertOf_capDartOfRetained
    (dart : RetainedDart RS data.keep) :
    data.capRotationSystem.vertOf (data.capDartOfRetained dart) =
      (Sum.inl ⟨RS.vertOf dart.1, dart.2⟩ : data.CapVertex) := by
  change data.capSeamData.vertOf (data.capDartOfRetained dart) = _
  rw [data.capSeamData_vertOf_eq_capTargetVert,
    data.capDartEquiv_capDartOfRetained]
  rfl

@[simp]
theorem capRotationSystem_vertOf_capDart (spoke : Fin 3) :
    data.capRotationSystem.vertOf (data.capDart spoke) =
      (Sum.inr () : data.CapVertex) := by
  change data.capSeamData.vertOf (data.capDart spoke) = _
  rw [data.capSeamData_vertOf_eq_capTargetVert,
    data.capDartEquiv_capDart]
  rfl

/-- The retained endpoint of one star spoke. -/
def starBoundaryVertex (spoke : Fin 3) : RetainedVertex data.keep :=
  let boundary := data.starDart spoke
  ⟨RS.vertOf boundary.1.1, boundary.1.2⟩

/-! ## Primal connectivity -/

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
  refine ⟨Sum.inl (Sum.inl internal), ?_, ?_⟩
  · apply congrArg Sum.inl
    apply Subtype.ext
    exact hleft
  · change data.capSeamData.vertOf
      (data.capRewiredDartSystem.alpha (Sum.inl (Sum.inl internal))) =
        Sum.inl right
    rw [data.capRewiredDartSystem_alpha_internal]
    apply congrArg Sum.inl
    apply Subtype.ext
    exact hright

/-- A star spoke is paired with the retained boundary dart at the same cut
position. -/
theorem capRotationSystem_alpha_capDart (spoke : Fin 3) :
    data.capRotationSystem.alpha (data.capDart spoke) =
      data.capDartOfRetained (data.starDart spoke).1 := by
  change data.capRewiredDartSystem.alpha (data.capDart spoke) = _
  rw [data.capDartOfRetained_star]
  rfl

/-- Each star spoke joins the new star vertex to its retained boundary
endpoint in the primal graph. -/
theorem capPrimalGraph_adj_starBoundaryVertex (spoke : Fin 3) :
    (rotationPrimalGraph data.capRotationSystem).Adj
      (Sum.inr ()) (Sum.inl (data.starBoundaryVertex spoke)) := by
  refine ⟨data.capDart spoke,
    data.capRotationSystem_vertOf_capDart spoke, ?_⟩
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

/-- A connected retained side remains connected after the seam and the
star. -/
theorem capRotationSystem_primalConnected
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected) :
    (rotationPrimalGraph data.capRotationSystem).Connected := by
  refine { preconnected := ?_, nonempty := ⟨Sum.inr ()⟩ }
  intro left right
  let anchor := data.starBoundaryVertex (0 : Fin 3)
  have hspoke := data.capPrimalGraph_adj_starBoundaryVertex (0 : Fin 3)
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

/-! ## Cyclic vertex rotations -/

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

/-- The standard three-cycle makes all star spokes lie on one rotation
cycle. -/
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

/-- The Y-cap inherits one cyclic dart order at every retained vertex,
while the new star vertex carries the standard three-cycle. -/
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

/-! ## Cubicity -/

/-- Darts over a retained cap vertex are exactly the old darts over its
ambient vertex. -/
def capTargetDartsAtRetainedEquiv (vertex : RetainedVertex data.keep) :
    { target : RetainedDart RS data.keep ⊕ Fin 3 //
      data.capTargetVert target = Sum.inl vertex } ≃
      { dart : RS.D // RS.vertOf dart = vertex.1 } where
  toFun target := by
    rcases target with ⟨retained | step, htarget⟩
    · have hvertices :
          (⟨RS.vertOf retained.1, retained.2⟩ :
            RetainedVertex data.keep) = vertex := by
        change (Sum.inl
          (⟨RS.vertOf retained.1, retained.2⟩ :
            RetainedVertex data.keep) : data.CapVertex) =
          Sum.inl vertex at htarget
        exact Sum.inl.inj htarget
      exact ⟨retained.1, congrArg Subtype.val hvertices⟩
    ·
      change (Sum.inr () : data.CapVertex) = Sum.inl vertex at htarget
      exact False.elim (by cases htarget)
  invFun dart :=
    ⟨Sum.inl ⟨dart.1, dart.2.symm ▸ vertex.2⟩, by
      change (Sum.inl
        (⟨RS.vertOf dart.1, _⟩ : RetainedVertex data.keep) :
          data.CapVertex) = Sum.inl vertex
      exact congrArg
        (fun retained : RetainedVertex data.keep =>
          (Sum.inl retained : data.CapVertex))
        (Subtype.ext dart.2)⟩
  left_inv target := by
    rcases target with ⟨retained | step, htarget⟩
    · apply Subtype.ext
      apply congrArg
        (fun retained : RetainedDart RS data.keep =>
          (Sum.inl retained : RetainedDart RS data.keep ⊕ Fin 3))
      apply Subtype.ext
      rfl
    ·
      change (Sum.inr () : data.CapVertex) = Sum.inl vertex at htarget
      exact False.elim (by cases htarget)
  right_inv dart := by
    apply Subtype.ext
    rfl

/-- The cap-dart equivalence restricted to one retained vertex. -/
def capRetainedVertexDartsEquiv (vertex : RetainedVertex data.keep) :
    { dart : data.CapDart //
      data.capRotationSystem.vertOf dart = Sum.inl vertex } ≃
      { dart : RS.D // RS.vertOf dart = vertex.1 } :=
  (data.capDartEquiv.subtypeEquiv (fun dart => by
      change data.capSeamData.vertOf dart = Sum.inl vertex ↔
        data.capTargetVert (data.capDartEquiv dart) = Sum.inl vertex
      rw [data.capSeamData_vertOf_eq_capTargetVert])).trans
    (data.capTargetDartsAtRetainedEquiv vertex)

/-- The local dart count at a retained vertex is unchanged. -/
theorem capRotationSystem_dartsAt_retained_card
    (vertex : RetainedVertex data.keep) :
    (data.capRotationSystem.dartsAt (Sum.inl vertex)).card =
      (RS.dartsAt vertex.1).card := by
  classical
  unfold RotationSystem.dartsAt
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (data.capRetainedVertexDartsEquiv vertex)

/-- The target darts based at the new star vertex are exactly its three
spoke positions. -/
def capTargetDartsAtCapEquiv :
    { target : RetainedDart RS data.keep ⊕ Fin 3 //
      data.capTargetVert target = Sum.inr () } ≃ Fin 3 where
  toFun target := by
    rcases target with ⟨retained | step, htarget⟩
    ·
      change (Sum.inl
        (⟨RS.vertOf retained.1, retained.2⟩ : RetainedVertex data.keep) :
          data.CapVertex) = Sum.inr () at htarget
      exact False.elim (by cases htarget)
    · exact step
  invFun step := ⟨Sum.inr step, rfl⟩
  left_inv target := by
    rcases target with ⟨retained | step, htarget⟩
    ·
      change (Sum.inl
        (⟨RS.vertOf retained.1, retained.2⟩ : RetainedVertex data.keep) :
          data.CapVertex) = Sum.inr () at htarget
      exact False.elim (by cases htarget)
    · apply Subtype.ext
      rfl
  right_inv _ := rfl

/-- The cap-dart equivalence restricted to the new star vertex. -/
def capVertexDartsEquiv :
    { dart : data.CapDart //
      data.capRotationSystem.vertOf dart = Sum.inr () } ≃ Fin 3 :=
  (data.capDartEquiv.subtypeEquiv (fun dart => by
      change data.capSeamData.vertOf dart = Sum.inr () ↔
        data.capTargetVert (data.capDartEquiv dart) = Sum.inr ()
      rw [data.capSeamData_vertOf_eq_capTargetVert])).trans
    data.capTargetDartsAtCapEquiv

/-- The new star vertex has exactly three darts. -/
theorem capRotationSystem_dartsAt_cap_card :
    (data.capRotationSystem.dartsAt (Sum.inr ())).card = 3 := by
  classical
  unfold RotationSystem.dartsAt
  rw [← Fintype.card_subtype]
  calc
    Fintype.card { dart : data.CapDart //
        data.capRotationSystem.vertOf dart = Sum.inr () } =
        Fintype.card (Fin 3) :=
      Fintype.card_congr data.capVertexDartsEquiv
    _ = 3 := Fintype.card_fin 3

/-- The Y-cap preserves cubicity. -/
theorem capRotationSystem_isCubic (hCubic : RS.IsCubic) :
    data.capRotationSystem.IsCubic := by
  intro vertex
  rcases vertex with retained | cap
  · rw [data.capRotationSystem_dartsAt_retained_card]
    exact hCubic retained.1
  · rcases cap with ⟨⟩
    exact data.capRotationSystem_dartsAt_cap_card

end FiveEdgeCutYCapData


end

end Mettapedia.GraphTheory.FourColor
