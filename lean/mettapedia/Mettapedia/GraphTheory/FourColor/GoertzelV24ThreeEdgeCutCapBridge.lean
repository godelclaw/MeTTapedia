import Mettapedia.GraphTheory.FourColor.GoertzelV24ThreeEdgeCutCapStructure

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceDualConnectedness
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

namespace RotationSystem.ThreeEdgeCutSideData

variable {RS : RotationSystem V E} (data : ThreeEdgeCutSideData RS)

/-- Distinct old internal edge identifiers remain distinct after capping. -/
theorem capRotationSystem_edgeOf_internal_ne_of_edgeOf_ne
    (left right : InternalDart RS data.keep)
    (hne : RS.edgeOf left.1.1 ≠ RS.edgeOf right.1.1) :
    data.capRotationSystem.edgeOf (Sum.inl left) ≠
      data.capRotationSystem.edgeOf (Sum.inl right) := by
  intro hedges
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (Sum.inl left) (Sum.inl right)).1 hedges with
    hsame | hopposite
  · apply hne
    exact congrArg RS.edgeOf (congrArg Subtype.val
      (congrArg Subtype.val (Sum.inl.inj hsame)))
  · rw [data.capRewiredDartSystem_alpha_internal] at hopposite
    have hdarts : left.1.1 = RS.alpha right.1.1 :=
      congrArg Subtype.val
        (congrArg Subtype.val (Sum.inl.inj hopposite))
    apply hne
    rw [hdarts, RS.edge_alpha]

/-- Every retained internal edge remains distinct from every new cap
spoke. -/
theorem capRotationSystem_edgeOf_internal_ne_capEdge
    (internal : InternalDart RS data.keep) (step : Fin 3) :
    data.capRotationSystem.edgeOf (Sum.inl internal) ≠
      data.capEdge step := by
  intro hedge
  change data.capRewiredDartSystem.edgeOf (Sum.inl internal) =
    data.capRewiredDartSystem.edgeOf (data.capDart step) at hedge
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (Sum.inl internal) (data.capDart step)).1 hedge with
    hsame | hopposite
  · simp [capDart] at hsame
  · rw [data.capRewiredDartSystem_alpha_cap] at hopposite
    simp at hopposite

/-- An internal retained edge different from the deleted edge supplies its
usual cap adjacency. -/
theorem edgeDeletedPrimalGraph_adj_internal
    (removed : data.capRewiredDartSystem.Edge)
    (internal : InternalDart RS data.keep)
    (hne : data.capRotationSystem.edgeOf (Sum.inl internal) ≠ removed) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Adj
      (Sum.inl
        (⟨RS.vertOf internal.1.1, internal.1.2⟩ :
          RetainedVertex data.keep))
      (Sum.inl
        (⟨RS.vertOf (RS.alpha internal.1.1), internal.2⟩ :
          RetainedVertex data.keep)) := by
  exact ⟨Sum.inl internal, hne, rfl, rfl⟩

/-- Unless it is the deleted edge, a cap spoke supplies the adjacency from
the new cap vertex to its retained endpoint. -/
theorem edgeDeletedPrimalGraph_adj_cap
    (removed : data.capRewiredDartSystem.Edge) (step : Fin 3)
    (hne : data.capEdge step ≠ removed) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Adj
      (Sum.inr ()) (Sum.inl (data.capBoundaryVertex step)) := by
  refine ⟨data.capDart step, ?_,
    data.capRotationSystem_vertOf_capDart step, ?_⟩
  · exact hne
  · rw [data.capRotationSystem_alpha_capDart,
      data.capRotationSystem_vertOf_capDartOfRetained]
    rfl

/-- Collapse every deleted-side vertex to the new cap vertex. -/
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

/-- Every ambient adjacency avoiding a retained internal edge either
collapses inside the deleted side or survives in the corresponding
edge-deleted cap. -/
theorem collapseComplement_adj_eq_or_adj_of_internal_removed
    (removed : InternalDart RS data.keep) (dart : RS.D)
    (hedge : RS.edgeOf dart ≠ RS.edgeOf removed.1.1) :
    data.collapseComplementToCapVertex (RS.vertOf dart) =
        data.collapseComplementToCapVertex
          (RS.vertOf (RS.alpha dart)) ∨
      (edgeDeletedPrimalGraph data.capRotationSystem
        (data.capRotationSystem.edgeOf (Sum.inl removed))).Adj
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
          (data.capRotationSystem.edgeOf (Sum.inl removed)) internal hne
    · let boundary : BoundaryDart RS data.keep :=
        ⟨⟨dart, hleft⟩, hright⟩
      let step := data.crossingBoundaryDartEquiv.symm boundary
      have hne : data.capEdge step ≠
          data.capRotationSystem.edgeOf (Sum.inl removed) :=
        (data.capRotationSystem_edgeOf_internal_ne_capEdge
          removed step).symm
      have hcap := data.edgeDeletedPrimalGraph_adj_cap
        (data.capRotationSystem.edgeOf (Sum.inl removed)) step hne
      right
      simpa [collapseComplementToCapVertex, hleft, hright,
        capBoundaryVertex, step, boundary] using hcap.symm
  · by_cases hright : data.keep (RS.vertOf (RS.alpha dart))
    · let boundary : BoundaryDart RS data.keep :=
        ⟨⟨RS.alpha dart, hright⟩, by
          change ¬ data.keep
            (RS.vertOf (RS.alpha (RS.alpha dart)))
          simpa [RS.alpha_involutive] using hleft⟩
      let step := data.crossingBoundaryDartEquiv.symm boundary
      have hne : data.capEdge step ≠
          data.capRotationSystem.edgeOf (Sum.inl removed) :=
        (data.capRotationSystem_edgeOf_internal_ne_capEdge
          removed step).symm
      have hcap := data.edgeDeletedPrimalGraph_adj_cap
        (data.capRotationSystem.edgeOf (Sum.inl removed)) step hne
      right
      simpa [collapseComplementToCapVertex, hleft, hright,
        capBoundaryVertex, step, boundary] using hcap
    · left
      simp [collapseComplementToCapVertex, hleft, hright]

/-- Ambient bridge-freeness supplies a cap path around every retained
internal edge after the complementary side is contracted. -/
theorem cap_internal_reachable_of_edgeBridgeFree
    (hfree : EdgeBridgeFree RS)
    (removed : InternalDart RS data.keep) :
    (edgeDeletedPrimalGraph data.capRotationSystem
      (data.capRotationSystem.edgeOf (Sum.inl removed))).Reachable
      (Sum.inl
        (⟨RS.vertOf removed.1.1, removed.1.2⟩ :
          RetainedVertex data.keep))
      (Sum.inl
        (⟨RS.vertOf (RS.alpha removed.1.1), removed.2⟩ :
          RetainedVertex data.keep)) := by
  have hreach := hfree removed.1.1
  have hmapped := reachable_map_of_adj_eq_or_adj
    data.collapseComplementToCapVertex
    (fun {_ _} hadj => by
      rcases hadj with ⟨dart, hedge, hleft, hright⟩
      subst hleft
      subst hright
      exact data.collapseComplement_adj_eq_or_adj_of_internal_removed
        removed dart hedge)
    hreach
  simpa [collapseComplementToCapVertex, removed.1.2,
    removed.2] using hmapped

/-- Retained ambient adjacency survives after deleting any cap spoke. -/
theorem edgeDeletedPrimalGraph_adj_of_retained
    (removedStep : Fin 3)
    {left right : RetainedVertex data.keep}
    (hadj : (retainedAmbientPrimalGraph RS data.keep).Adj left right) :
    (edgeDeletedPrimalGraph data.capRotationSystem
      (data.capEdge removedStep)).Adj (Sum.inl left) (Sum.inl right) := by
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
  have hcap := data.edgeDeletedPrimalGraph_adj_internal
    (data.capEdge removedStep) internal
    (data.capRotationSystem_edgeOf_internal_ne_capEdge
      internal removedStep)
  have hleftVertex :
      (⟨RS.vertOf dart, hkeepLeft⟩ : RetainedVertex data.keep) = left :=
    Subtype.ext hleft
  have hrightVertex :
      (⟨RS.vertOf (RS.alpha dart), hkeepRight⟩ :
        RetainedVertex data.keep) = right :=
    Subtype.ext hright
  simpa [internal, hleftVertex, hrightVertex] using hcap

/-- Retained-side reachability survives deletion of a cap spoke. -/
theorem edgeDeletedPrimalGraph_reachable_of_retained
    (removedStep : Fin 3)
    {left right : RetainedVertex data.keep}
    (hreachable :
      (retainedAmbientPrimalGraph RS data.keep).Reachable left right) :
    (edgeDeletedPrimalGraph data.capRotationSystem
      (data.capEdge removedStep)).Reachable
      (Sum.inl left) (Sum.inl right) := by
  exact reachable_map_of_adj_eq_or_adj
    (fun vertex : RetainedVertex data.keep =>
      (Sum.inl vertex : data.CapVertex))
    (fun {_ _} hadj => Or.inr
      (data.edgeDeletedPrimalGraph_adj_of_retained removedStep hadj))
    hreachable

/-- Deleting one cap spoke leaves its endpoints connected through another
spoke and the connected retained side. -/
theorem cap_endpoints_reachable_without_capEdge
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected)
    (removedStep : Fin 3) :
    (edgeDeletedPrimalGraph data.capRotationSystem
      (data.capEdge removedStep)).Reachable
      (Sum.inr ()) (Sum.inl (data.capBoundaryVertex removedStep)) := by
  let alternateStep := finRotate 3 removedStep
  have halternate : alternateStep ≠ removedStep := by
    have hmem : removedStep ∈ (finRotate 3).support := by
      rw [support_finRotate_of_le (by omega)]
      simp
    exact Equiv.Perm.mem_support.mp hmem
  have hspoke := data.edgeDeletedPrimalGraph_adj_cap
    (data.capEdge removedStep) alternateStep
    (data.capEdge_injective.ne halternate)
  have hretained := data.edgeDeletedPrimalGraph_reachable_of_retained
    removedStep
    (hconnected (data.capBoundaryVertex alternateStep)
      (data.capBoundaryVertex removedStep))
  exact hspoke.reachable.trans hretained

/-- The boundary dart at a listed cut position is paired with the cap dart
at that position. -/
@[simp]
theorem capRotationSystem_alpha_crossingBoundaryDart (step : Fin 3) :
    data.capRotationSystem.alpha
        (Sum.inr (Sum.inl (data.crossingBoundaryDartEquiv step))) =
      data.capDart step := by
  change data.capRewiredDartSystem.alpha
      (Sum.inr (Sum.inl (data.crossingBoundaryDartEquiv step))) = _
  rw [data.capRewiredDartSystem_alpha_boundary,
    Equiv.symm_apply_apply]

/-- The boundary dart and cap dart at one position determine the same cap
edge. -/
@[simp]
theorem capRotationSystem_edgeOf_crossingBoundaryDart (step : Fin 3) :
    data.capRotationSystem.edgeOf
        (Sum.inr (Sum.inl (data.crossingBoundaryDartEquiv step))) =
      data.capEdge step := by
  calc
    data.capRotationSystem.edgeOf
        (Sum.inr (Sum.inl (data.crossingBoundaryDartEquiv step))) =
        data.capRotationSystem.edgeOf
          (data.capRotationSystem.alpha
            (Sum.inr (Sum.inl
              (data.crossingBoundaryDartEquiv step)))) :=
      (data.capRotationSystem.edge_alpha _).symm
    _ = data.capEdge step := by
      rw [data.capRotationSystem_alpha_crossingBoundaryDart]
      rfl

/-- Exact three-star capping preserves bridge-freeness. Internal edges use
ambient avoiding paths; each cap spoke uses another spoke and retained-side
connectedness. -/
theorem capRotationSystem_edgeBridgeFree
    (hfree : EdgeBridgeFree RS)
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected) :
    EdgeBridgeFree data.capRotationSystem := by
  intro dart
  rcases dart with internal | boundaryOrCap
  · exact data.cap_internal_reachable_of_edgeBridgeFree hfree internal
  · rcases boundaryOrCap with boundary | step
    · rcases data.crossingBoundaryDartEquiv.surjective boundary with
        ⟨step, rfl⟩
      rw [data.capRotationSystem_edgeOf_crossingBoundaryDart,
        data.capRotationSystem_alpha_crossingBoundaryDart,
        data.capRotationSystem_vertOf_capDart]
      change (edgeDeletedPrimalGraph data.capRotationSystem
        (data.capEdge step)).Reachable
          (Sum.inl (data.capBoundaryVertex step)) (Sum.inr ())
      exact (data.cap_endpoints_reachable_without_capEdge
        hconnected step).symm
    · change (edgeDeletedPrimalGraph data.capRotationSystem
        (data.capEdge step)).Reachable
          (Sum.inr ()) (Sum.inl (data.capBoundaryVertex step))
      exact data.cap_endpoints_reachable_without_capEdge hconnected step

end RotationSystem.ThreeEdgeCutSideData

end

end Mettapedia.GraphTheory.FourColor
