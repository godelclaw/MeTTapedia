import Mettapedia.GraphTheory.FourColor.FiveEdgeCutPentagonCap
import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCapStructure

/-!
# Structural class facts for the pentagon cap

The pentagon-capped shore keeps its primal connectivity — each new cap
vertex hangs on its spoke — and inherits one cyclic dart rotation at
every vertex: retained vertices keep their old rotations, each cap vertex
carries the three-cycle incoming-spoke-outgoing.  Local dart counts make
the capped shore cubic.
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

namespace FiveEdgeCutPentagonCapData

variable {RS : RotationSystem V E} (data : FiveEdgeCutPentagonCapData RS)

/-! ## The rewired involution, case by case -/

@[simp]
theorem capRewiredDartSystem_alpha_internal
    (internal : InternalDart RS data.keep) :
    data.capRewiredDartSystem.alpha (Sum.inl (Sum.inl internal)) =
      Sum.inl (Sum.inl (internalAlpha RS data.keep internal)) :=
  rfl

@[simp]
theorem capRewiredDartSystem_alpha_cycle (dart : Fin 5 × Bool) :
    data.capRewiredDartSystem.alpha (Sum.inl (Sum.inr dart)) =
      Sum.inl (Sum.inr (pentagonCyclePairing dart)) :=
  rfl

@[simp]
theorem capRewiredDartSystem_alpha_boundary (position : Fin 5) :
    data.capRewiredDartSystem.alpha (Sum.inr (Sum.inl position)) =
      Sum.inr (Sum.inr position) :=
  rfl

@[simp]
theorem capRewiredDartSystem_alpha_spoke (j : Fin 5) :
    data.capRewiredDartSystem.alpha (Sum.inr (Sum.inr j)) =
      Sum.inr (Sum.inl j) :=
  rfl

/-! ## Dart embeddings and vertices -/

@[simp]
theorem capDartOfRetained_internal
    (internal : InternalDart RS data.keep) :
    data.capDartOfRetained internal.1 = Sum.inl (Sum.inl internal) := by
  apply data.capDartEquiv.injective
  simp

@[simp]
theorem capDartOfRetained_boundary (position : Fin 5) :
    data.capDartOfRetained (data.crossingBoundaryDartEquiv position).1 =
      Sum.inr (Sum.inl position) := by
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
theorem capRotationSystem_vertOf_capDart (j : Fin 5) :
    data.capRotationSystem.vertOf (data.capDart j) =
      (Sum.inr j : data.CapVertex) := by
  change data.capSeamData.vertOf (Sum.inr (Sum.inr j)) = _
  rw [data.capSeamData_vertOf_eq_capTargetVert,
    data.capDartEquiv_spoke]
  rfl

@[simp]
theorem capRotationSystem_vertOf_cycleDart (dart : Fin 5 × Bool) :
    data.capRotationSystem.vertOf (data.cycleDart dart) =
      (Sum.inr dart.1 : data.CapVertex) := by
  change data.capSeamData.vertOf (Sum.inl (Sum.inr dart)) = _
  rw [data.capSeamData_vertOf_eq_capTargetVert,
    data.capDartEquiv_cycle]
  rcases dart with ⟨j, b⟩
  rfl

/-- The retained endpoint of one spoke. -/
def capBoundaryVertex (position : Fin 5) : RetainedVertex data.keep :=
  let boundary := data.crossingBoundaryDartEquiv position
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

/-- A spoke is paired with the retained boundary dart at its position. -/
theorem capRotationSystem_alpha_capDart (j : Fin 5) :
    data.capRotationSystem.alpha (data.capDart j) =
      data.capDartOfRetained (data.crossingBoundaryDartEquiv j).1 := by
  change data.capRewiredDartSystem.alpha (data.capDart j) = _
  rw [data.capDartOfRetained_boundary]
  rfl

/-- Each spoke joins its cap vertex to its retained boundary endpoint in
the primal graph. -/
theorem capPrimalGraph_adj_capBoundaryVertex (j : Fin 5) :
    (rotationPrimalGraph data.capRotationSystem).Adj
      (Sum.inr j) (Sum.inl (data.capBoundaryVertex j)) := by
  refine ⟨data.capDart j,
    data.capRotationSystem_vertOf_capDart j, ?_⟩
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

/-- A connected retained side remains connected after the pentagon cap. -/
theorem capRotationSystem_primalConnected
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected) :
    (rotationPrimalGraph data.capRotationSystem).Connected := by
  refine { preconnected := ?_, nonempty := ⟨Sum.inr 0⟩ }
  have hcapToRetained : ∀ j : Fin 5,
      (rotationPrimalGraph data.capRotationSystem).Reachable
        (Sum.inr j) (Sum.inl (data.capBoundaryVertex j)) :=
    fun j => (data.capPrimalGraph_adj_capBoundaryVertex j).reachable
  intro left right
  rcases left with left | leftCap <;>
    rcases right with right | rightCap
  · exact data.capPrimalGraph_reachable_of_retained
      (hconnected left right)
  · exact (data.capPrimalGraph_reachable_of_retained
      (hconnected left (data.capBoundaryVertex rightCap))).trans
      (hcapToRetained rightCap).symm
  · exact (hcapToRetained leftCap).trans
      (data.capPrimalGraph_reachable_of_retained
        (hconnected (data.capBoundaryVertex leftCap) right))
  · exact ((hcapToRetained leftCap).trans
      (data.capPrimalGraph_reachable_of_retained
        (hconnected (data.capBoundaryVertex leftCap)
          (data.capBoundaryVertex rightCap)))).trans
      (hcapToRetained rightCap).symm

/-! ## Cyclic vertex rotations -/

/-- A retained ambient rotation cycle remains a cycle in the retained
summand. -/
theorem capTargetRho_sameCycle_inl
    {left right : RetainedDart RS data.keep}
    (hcycle : (retainedRho RS data.keep).SameCycle left right) :
    data.capTargetRho.SameCycle (Sum.inl left) (Sum.inl right) := by
  rcases hcycle with ⟨power, hpower⟩
  refine ⟨power, ?_⟩
  change ((Equiv.sumCongr (retainedRho RS data.keep)
    pentagonRho) ^ power) (Sum.inl left) = Sum.inl right
  have hsum :
      (Equiv.sumCongr (retainedRho RS data.keep) pentagonRho) ^ power =
        Equiv.sumCongr ((retainedRho RS data.keep) ^ power)
          (pentagonRho ^ power) := by
    simpa using (map_zpow (Equiv.Perm.sumCongrHom
      (RetainedDart RS data.keep) ((Fin 5 × Bool) ⊕ Fin 5))
        (retainedRho RS data.keep, pentagonRho) power).symm
  rw [hsum]
  exact congrArg Sum.inl hpower

/-- The cap vertex of a new pentagon dart. -/
def pentagonVertexOf : (Fin 5 × Bool) ⊕ Fin 5 → Fin 5
  | Sum.inl (j, _) => j
  | Sum.inr j => j

/-- The pentagon rotation joins any two darts at one cap vertex. -/
theorem pentagonRho_sameCycle_of_vertex_eq
    {left right : (Fin 5 × Bool) ⊕ Fin 5}
    (hvertex : pentagonVertexOf left = pentagonVertexOf right) :
    pentagonRho.SameCycle left right := by
  have hstep : ∀ x, pentagonRho.SameCycle x (pentagonRho x) :=
    fun x => Mettapedia.GraphTheory.EquivPermSameCycle.step_right
      pentagonRho x
  rcases left with ⟨j, bl⟩ | j
  · rcases right with ⟨k, br⟩ | k
    · simp only [pentagonVertexOf] at hvertex
      subst hvertex
      cases bl <;> cases br
      · exact Equiv.Perm.SameCycle.refl _ _
      · exact (hstep _).trans (hstep _)
      · exact hstep _
      · exact Equiv.Perm.SameCycle.refl _ _
    · simp only [pentagonVertexOf] at hvertex
      subst hvertex
      cases bl
      · exact hstep _
      · exact (hstep _).trans (hstep _)
  · rcases right with ⟨k, br⟩ | k
    · simp only [pentagonVertexOf] at hvertex
      subst hvertex
      cases br
      · exact (hstep _).trans (hstep _)
      · exact hstep _
    · simp only [pentagonVertexOf] at hvertex
      subst hvertex
      exact Equiv.Perm.SameCycle.refl _ _

/-- Two pentagon darts at one cap vertex lie on one rotation cycle after
transport. -/
theorem capTargetRho_sameCycle_inr
    {left right : (Fin 5 × Bool) ⊕ Fin 5}
    (hvertex : pentagonVertexOf left = pentagonVertexOf right) :
    data.capTargetRho.SameCycle (Sum.inr left) (Sum.inr right) := by
  rcases pentagonRho_sameCycle_of_vertex_eq hvertex with ⟨power, hpower⟩
  refine ⟨power, ?_⟩
  change ((Equiv.sumCongr (retainedRho RS data.keep)
    pentagonRho) ^ power) (Sum.inr left) = Sum.inr right
  have hsum :
      (Equiv.sumCongr (retainedRho RS data.keep) pentagonRho) ^ power =
        Equiv.sumCongr ((retainedRho RS data.keep) ^ power)
          (pentagonRho ^ power) := by
    simpa using (map_zpow (Equiv.Perm.sumCongrHom
      (RetainedDart RS data.keep) ((Fin 5 × Bool) ⊕ Fin 5))
        (retainedRho RS data.keep, pentagonRho) power).symm
  rw [hsum]
  exact congrArg Sum.inr hpower

/-- The vertex projection of a pentagon dart is its cap vertex. -/
theorem capTargetVert_inr (dart : (Fin 5 × Bool) ⊕ Fin 5) :
    data.capTargetVert (Sum.inr dart) =
      Sum.inr (pentagonVertexOf dart) := by
  rcases dart with ⟨j, b⟩ | j
  · rfl
  · rfl

/-- The pentagon cap inherits one cyclic dart order at every vertex. -/
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
    rcases leftTarget with retainedLeft | pentagonLeft <;>
      rcases rightTarget with retainedRight | pentagonRight
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
    · rw [data.capTargetVert_inr] at htargetVertex
      change (Sum.inl _ : data.CapVertex) = Sum.inr _ at htargetVertex
      exact False.elim (by cases htargetVertex)
    · rw [data.capTargetVert_inr] at htargetVertex
      change (Sum.inr _ : data.CapVertex) = Sum.inl _ at htargetVertex
      exact False.elim (by cases htargetVertex)
    · rw [data.capTargetVert_inr, data.capTargetVert_inr] at htargetVertex
      exact data.capTargetRho_sameCycle_inr
        (Sum.inr.inj htargetVertex)
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
    { target : RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5) //
      data.capTargetVert target = Sum.inl vertex } ≃
      { dart : RS.D // RS.vertOf dart = vertex.1 } where
  toFun target := by
    rcases target with ⟨retained | pentagon, htarget⟩
    · have hvertices :
          (⟨RS.vertOf retained.1, retained.2⟩ :
            RetainedVertex data.keep) = vertex := by
        change (Sum.inl
          (⟨RS.vertOf retained.1, retained.2⟩ :
            RetainedVertex data.keep) : data.CapVertex) =
          Sum.inl vertex at htarget
        exact Sum.inl.inj htarget
      exact ⟨retained.1, congrArg Subtype.val hvertices⟩
    · exfalso
      rw [data.capTargetVert_inr] at htarget
      cases htarget
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
    rcases target with ⟨retained | pentagon, htarget⟩
    · apply Subtype.ext
      apply congrArg
        (fun retained : RetainedDart RS data.keep =>
          (Sum.inl retained :
            RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5)))
      apply Subtype.ext
      rfl
    · exfalso
      rw [data.capTargetVert_inr] at htarget
      cases htarget
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

theorem capRotationSystem_dartsAt_retained_card
    (vertex : RetainedVertex data.keep) :
    (data.capRotationSystem.dartsAt (Sum.inl vertex)).card =
      (RS.dartsAt vertex.1).card := by
  classical
  unfold RotationSystem.dartsAt
  rw [← Fintype.card_subtype, ← Fintype.card_subtype]
  exact Fintype.card_congr (data.capRetainedVertexDartsEquiv vertex)

/-- The target darts based at cap vertex `j` are its two cycle darts and
its spoke. -/
def capTargetDartsAtCapEquiv (j : Fin 5) :
    { target : RetainedDart RS data.keep ⊕ ((Fin 5 × Bool) ⊕ Fin 5) //
      data.capTargetVert target = Sum.inr j } ≃ Fin 3 where
  toFun target := by
    rcases target with ⟨retained | (⟨_, b⟩ | _), htarget⟩
    · change (Sum.inl _ : data.CapVertex) = Sum.inr j at htarget
      exact absurd htarget (by simp)
    · exact if b then 1 else 0
    · exact 2
  invFun step :=
    if step = 0 then ⟨Sum.inr (Sum.inl (j, false)), rfl⟩
    else if step = 1 then ⟨Sum.inr (Sum.inl (j, true)), rfl⟩
    else ⟨Sum.inr (Sum.inr j), rfl⟩
  left_inv target := by
    rcases target with ⟨retained | (⟨k, b⟩ | k), htarget⟩
    · change (Sum.inl _ : data.CapVertex) = Sum.inr j at htarget
      exact absurd htarget (by simp)
    · have hk : k = j := by
        rw [data.capTargetVert_inr] at htarget
        exact Sum.inr.inj htarget
      subst hk
      cases b <;> simp
    · have hk : k = j := by
        rw [data.capTargetVert_inr] at htarget
        exact Sum.inr.inj htarget
      subst hk
      simp
  right_inv step := by
    fin_cases step <;> simp

/-- The cap-dart equivalence restricted to one cap vertex. -/
def capVertexDartsEquiv (j : Fin 5) :
    { dart : data.CapDart //
      data.capRotationSystem.vertOf dart = Sum.inr j } ≃ Fin 3 :=
  (data.capDartEquiv.subtypeEquiv (fun dart => by
      change data.capSeamData.vertOf dart = Sum.inr j ↔
        data.capTargetVert (data.capDartEquiv dart) = Sum.inr j
      rw [data.capSeamData_vertOf_eq_capTargetVert])).trans
    (data.capTargetDartsAtCapEquiv j)

theorem capRotationSystem_dartsAt_cap_card (j : Fin 5) :
    (data.capRotationSystem.dartsAt (Sum.inr j)).card = 3 := by
  classical
  unfold RotationSystem.dartsAt
  rw [← Fintype.card_subtype]
  calc
    Fintype.card { dart : data.CapDart //
        data.capRotationSystem.vertOf dart = Sum.inr j } =
        Fintype.card (Fin 3) :=
      Fintype.card_congr (data.capVertexDartsEquiv j)
    _ = 3 := Fintype.card_fin 3

/-- The pentagon cap preserves cubicity. -/
theorem capRotationSystem_isCubic (hCubic : RS.IsCubic) :
    data.capRotationSystem.IsCubic := by
  intro vertex
  rcases vertex with retained | j
  · rw [data.capRotationSystem_dartsAt_retained_card]
    exact hCubic retained.1
  · exact data.capRotationSystem_dartsAt_cap_card j

end FiveEdgeCutPentagonCapData


end

end Mettapedia.GraphTheory.FourColor
