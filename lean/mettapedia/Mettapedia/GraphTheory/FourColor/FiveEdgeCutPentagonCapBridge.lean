import Mettapedia.GraphTheory.FourColor.FiveEdgeCutPentagonCapStructure
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationEdgeBridge

/-!
# Bridge-freeness of the pentagon-capped shore

Every edge of the pentagon-capped shore lies on a cycle.  A spoke
reconnects through the cap cycle, the next spoke, and the retained side;
a cap cycle edge reconnects through the two adjacent spokes and the
retained side; an internal retained edge follows its ambient
bridge-freeness path, with every deleted excursion collapsed onto the cap:
entering and leaving spokes join cap vertices, which the cap cycle
connects.  No hypothesis beyond ambient bridge-freeness and retained-side
connectivity is required.
-/

namespace Mettapedia.GraphTheory.FourColor

open GoertzelV24FaceDualConnectedness
open GoertzelV24RetainedSplicePrimalGraph
open GoertzelV24RetainedVertexRotationSplice
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RotationEdgeBridge
open GoertzelV24RotationSpliceConstructor

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Map reachability through a function sending adjacency to
reachability. -/
theorem reachable_map_of_adj_reachable
    {A B : Type*} {G : SimpleGraph A} {H : SimpleGraph B} (f : A → B)
    (hadj : ∀ {x y : A}, G.Adj x y → H.Reachable (f x) (f y))
    {x y : A} (hreach : G.Reachable x y) :
    H.Reachable (f x) (f y) := by
  rcases hreach with ⟨walk⟩
  induction walk with
  | nil => exact SimpleGraph.Reachable.rfl
  | cons hstep _ ih => exact (hadj hstep).trans ih

namespace FiveEdgeCutPentagonCapData

variable {RS : RotationSystem V E} (data : FiveEdgeCutPentagonCapData RS)

/-! ## The new edges -/

/-- The spoke edge at one position. -/
def capSpokeEdge (j : Fin 5) : data.capRewiredDartSystem.Edge :=
  data.capRewiredDartSystem.edgeOf (data.capDart j)

/-- The cap cycle edge from vertex `j` to vertex `j + 1`. -/
def capCycleEdge (j : Fin 5) : data.capRewiredDartSystem.Edge :=
  data.capRewiredDartSystem.edgeOf (data.cycleDart (j, true))

theorem capCycleEdge_eq_false (j : Fin 5) :
    data.capRewiredDartSystem.edgeOf (data.cycleDart (j, false)) =
      data.capCycleEdge (j - 1) := by
  calc
    data.capRewiredDartSystem.edgeOf (data.cycleDart (j, false)) =
        data.capRewiredDartSystem.edgeOf
          (data.capRewiredDartSystem.alpha (data.cycleDart (j, false))) :=
      (data.capRewiredDartSystem.edgeOf_alpha _).symm
    _ = data.capCycleEdge (j - 1) := by
      change data.capRewiredDartSystem.edgeOf
        (data.capRewiredDartSystem.alpha (Sum.inl (Sum.inr (j, false)))) = _
      rw [data.capRewiredDartSystem_alpha_cycle]
      rfl

/-- The three edge families are pairwise distinct where needed. -/
theorem capSpokeEdge_injective : Function.Injective data.capSpokeEdge := by
  intro first second hedges
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (data.capDart first) (data.capDart second)).1 hedges with
    hdarts | hdarts
  · exact Sum.inr.inj (Sum.inr.inj hdarts)
  · exfalso
    unfold capDart at hdarts
    rw [data.capRewiredDartSystem_alpha_spoke] at hdarts
    simp at hdarts

theorem capCycleEdge_injective : Function.Injective data.capCycleEdge := by
  intro first second hedges
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (data.cycleDart (first, true)) (data.cycleDart (second, true))).1
      hedges with hdarts | hdarts
  · have := Sum.inr.inj (Sum.inl.inj hdarts)
    exact (Prod.ext_iff.mp this).1
  · exfalso
    unfold cycleDart at hdarts
    rw [data.capRewiredDartSystem_alpha_cycle] at hdarts
    have := Sum.inr.inj (Sum.inl.inj hdarts)
    have hb := (Prod.ext_iff.mp this).2
    simp [pentagonCyclePairing] at hb

theorem capSpokeEdge_ne_capCycleEdge (j k : Fin 5) :
    data.capSpokeEdge j ≠ data.capCycleEdge k := by
  intro hedge
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (data.capDart j) (data.cycleDart (k, true))).1 hedge with
    hdarts | hdarts
  · simp [capDart, cycleDart] at hdarts
  · unfold capDart cycleDart at hdarts
    rw [data.capRewiredDartSystem_alpha_cycle] at hdarts
    simp [pentagonCyclePairing] at hdarts

theorem capRotationSystem_edgeOf_internal_ne_capSpokeEdge
    (internal : InternalDart RS data.keep) (j : Fin 5) :
    data.capRotationSystem.edgeOf (Sum.inl (Sum.inl internal)) ≠
      data.capSpokeEdge j := by
  intro hedge
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (Sum.inl (Sum.inl internal)) (data.capDart j)).1 hedge with
    hsame | hopposite
  · simp [capDart] at hsame
  · unfold capDart at hopposite
    rw [data.capRewiredDartSystem_alpha_spoke] at hopposite
    simp at hopposite

theorem capRotationSystem_edgeOf_internal_ne_capCycleEdge
    (internal : InternalDart RS data.keep) (j : Fin 5) :
    data.capRotationSystem.edgeOf (Sum.inl (Sum.inl internal)) ≠
      data.capCycleEdge j := by
  intro hedge
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (Sum.inl (Sum.inl internal)) (data.cycleDart (j, true))).1 hedge with
    hsame | hopposite
  · simp [cycleDart] at hsame
  · unfold cycleDart at hopposite
    rw [data.capRewiredDartSystem_alpha_cycle] at hopposite
    simp at hopposite

/-! ## Adjacencies surviving one deletion -/

theorem edgeDeletedPrimalGraph_adj_internal
    (removed : data.capRewiredDartSystem.Edge)
    (internal : InternalDart RS data.keep)
    (hne : data.capRotationSystem.edgeOf (Sum.inl (Sum.inl internal)) ≠
      removed) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Adj
      (Sum.inl
        (⟨RS.vertOf internal.1.1, internal.1.2⟩ :
          RetainedVertex data.keep))
      (Sum.inl
        (⟨RS.vertOf (RS.alpha internal.1.1), internal.2⟩ :
          RetainedVertex data.keep)) := by
  exact ⟨Sum.inl (Sum.inl internal), hne, rfl, rfl⟩

theorem edgeDeletedPrimalGraph_adj_capSpoke
    (removed : data.capRewiredDartSystem.Edge) (j : Fin 5)
    (hne : data.capSpokeEdge j ≠ removed) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Adj
      (Sum.inr j) (Sum.inl (data.capBoundaryVertex j)) := by
  refine ⟨data.capDart j, hne,
    data.capRotationSystem_vertOf_capDart j, ?_⟩
  rw [data.capRotationSystem_alpha_capDart,
    data.capRotationSystem_vertOf_capDartOfRetained]
  rfl

theorem edgeDeletedPrimalGraph_adj_capCycle
    (removed : data.capRewiredDartSystem.Edge) (j : Fin 5)
    (hne : data.capCycleEdge j ≠ removed) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Adj
      (Sum.inr j) (Sum.inr (j + 1)) := by
  refine ⟨data.cycleDart (j, true), hne, ?_, ?_⟩
  · exact data.capRotationSystem_vertOf_cycleDart (j, true)
  · rw [show data.capRotationSystem.alpha (data.cycleDart (j, true)) =
      data.cycleDart (j + 1, false) from by
        change data.capRewiredDartSystem.alpha
          (Sum.inl (Sum.inr (j, true))) = _
        rw [data.capRewiredDartSystem_alpha_cycle]
        rfl]
    exact data.capRotationSystem_vertOf_cycleDart (j + 1, false)

/-! ## Retained transport and cap-cycle reachability -/

theorem edgeDeletedPrimalGraph_adj_of_retained_of_ne
    (removed : data.capRewiredDartSystem.Edge)
    (hne : ∀ internal : InternalDart RS data.keep,
      data.capRotationSystem.edgeOf (Sum.inl (Sum.inl internal)) ≠ removed)
    {left right : RetainedVertex data.keep}
    (hadj : (retainedAmbientPrimalGraph RS data.keep).Adj left right) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Adj
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
  have hcap := data.edgeDeletedPrimalGraph_adj_internal removed internal
    (hne internal)
  have hleftVertex :
      (⟨RS.vertOf dart, hkeepLeft⟩ : RetainedVertex data.keep) = left :=
    Subtype.ext hleft
  have hrightVertex :
      (⟨RS.vertOf (RS.alpha dart), hkeepRight⟩ :
        RetainedVertex data.keep) = right :=
    Subtype.ext hright
  simpa [internal, hleftVertex, hrightVertex] using hcap

theorem edgeDeletedPrimalGraph_reachable_of_retained_of_ne
    (removed : data.capRewiredDartSystem.Edge)
    (hne : ∀ internal : InternalDart RS data.keep,
      data.capRotationSystem.edgeOf (Sum.inl (Sum.inl internal)) ≠ removed)
    {left right : RetainedVertex data.keep}
    (hreachable :
      (retainedAmbientPrimalGraph RS data.keep).Reachable left right) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Reachable
      (Sum.inl left) (Sum.inl right) := by
  exact reachable_map_of_adj_eq_or_adj
    (fun vertex : RetainedVertex data.keep =>
      (Sum.inl vertex : data.CapVertex))
    (fun {_ _} hadj => Or.inr
      (data.edgeDeletedPrimalGraph_adj_of_retained_of_ne removed hne hadj))
    hreachable

/-- When no cap cycle edge is removed, the cap cycle connects any two cap
vertices. -/
theorem capVertex_reachable_of_cycle_free
    (removed : data.capRewiredDartSystem.Edge)
    (hcycle : ∀ j : Fin 5, data.capCycleEdge j ≠ removed)
    (j k : Fin 5) :
    (edgeDeletedPrimalGraph data.capRotationSystem removed).Reachable
      (Sum.inr j) (Sum.inr k) := by
  have hstep : ∀ i : Fin 5,
      (edgeDeletedPrimalGraph data.capRotationSystem removed).Reachable
        (Sum.inr i) (Sum.inr (i + 1)) :=
    fun i => (data.edgeDeletedPrimalGraph_adj_capCycle removed i
      (hcycle i)).reachable
  have hzero : ∀ i : Fin 5,
      (edgeDeletedPrimalGraph data.capRotationSystem removed).Reachable
        (Sum.inr (0 : Fin 5)) (Sum.inr i) := by
    intro i
    fin_cases i
    · exact SimpleGraph.Reachable.rfl
    · exact hstep 0
    · exact (hstep 0).trans (hstep 1)
    · exact ((hstep 0).trans (hstep 1)).trans (hstep 2)
    · exact (((hstep 0).trans (hstep 1)).trans (hstep 2)).trans (hstep 3)
  exact (hzero j).symm.trans (hzero k)

/-! ## Internal edges through the collapse -/

/-- Collapse every deleted-side vertex to cap vertex zero. -/
def collapseComplementToCap (vertex : V) : data.CapVertex :=
  if hkeep : data.keep vertex then
    Sum.inl ⟨vertex, hkeep⟩
  else
    Sum.inr 0

/-- Distinct old internal edges stay distinct after capping. -/
theorem capRotationSystem_edgeOf_internal_ne_of_edgeOf_ne
    (left right : InternalDart RS data.keep)
    (hne : RS.edgeOf left.1.1 ≠ RS.edgeOf right.1.1) :
    data.capRotationSystem.edgeOf (Sum.inl (Sum.inl left)) ≠
      data.capRotationSystem.edgeOf (Sum.inl (Sum.inl right)) := by
  intro hedges
  rcases (data.capRewiredDartSystem.edgeOf_eq_edgeOf_iff
      (Sum.inl (Sum.inl left)) (Sum.inl (Sum.inl right))).1 hedges with
    hsame | hopposite
  · apply hne
    exact congrArg RS.edgeOf (congrArg Subtype.val (congrArg Subtype.val
      (Sum.inl.inj (Sum.inl.inj hsame))))
  · rw [data.capRewiredDartSystem_alpha_internal] at hopposite
    have hdarts : left.1.1 = (internalAlpha RS data.keep right).1.1 :=
      congrArg Subtype.val (congrArg Subtype.val
        (Sum.inl.inj (Sum.inl.inj hopposite)))
    apply hne
    rw [hdarts, internalAlpha_val, RS.edge_alpha]

@[simp]
theorem collapseComplementToCap_of_keep
    (vertex : V) (hkeep : data.keep vertex) :
    data.collapseComplementToCap vertex =
      Sum.inl (⟨vertex, hkeep⟩ : RetainedVertex data.keep) := by
  simp [collapseComplementToCap, hkeep]

@[simp]
theorem collapseComplementToCap_of_not_keep
    (vertex : V) (hkeep : ¬ data.keep vertex) :
    data.collapseComplementToCap vertex = Sum.inr 0 := by
  simp [collapseComplementToCap, hkeep]

/-- Every ambient adjacency avoiding a removed internal edge maps to
reachability in the edge-deleted cap after the collapse. -/
theorem collapseComplement_reachable_of_internal_removed
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected)
    (removed : InternalDart RS data.keep) (dart : RS.D)
    (hedge : RS.edgeOf dart ≠ RS.edgeOf removed.1.1) :
    (edgeDeletedPrimalGraph data.capRotationSystem
      (data.capRotationSystem.edgeOf (Sum.inl (Sum.inl removed)))).Reachable
      (data.collapseComplementToCap (RS.vertOf dart))
      (data.collapseComplementToCap (RS.vertOf (RS.alpha dart))) := by
  set removedEdge := data.capRotationSystem.edgeOf
    (Sum.inl (Sum.inl removed)) with hremovedEdge
  have hcycleFree : ∀ j : Fin 5, data.capCycleEdge j ≠ removedEdge :=
    fun j => (data.capRotationSystem_edgeOf_internal_ne_capCycleEdge
      removed j).symm
  have hspokeFree : ∀ j : Fin 5, data.capSpokeEdge j ≠ removedEdge :=
    fun j => (data.capRotationSystem_edgeOf_internal_ne_capSpokeEdge
      removed j).symm
  have hinternalFree : ∀ internal : InternalDart RS data.keep,
      data.capRotationSystem.edgeOf (Sum.inl (Sum.inl internal)) ≠
        removedEdge → True := fun _ _ => trivial
  by_cases hleft : data.keep (RS.vertOf dart)
  · by_cases hright : data.keep (RS.vertOf (RS.alpha dart))
    · let internal : InternalDart RS data.keep :=
        ⟨⟨dart, hleft⟩, hright⟩
      have hne := data.capRotationSystem_edgeOf_internal_ne_of_edgeOf_ne
        internal removed hedge
      have hadj := data.edgeDeletedPrimalGraph_adj_internal
        removedEdge internal hne
      rw [data.collapseComplementToCap_of_keep _ hleft,
        data.collapseComplementToCap_of_keep _ hright]
      exact hadj.reachable
    · -- crossing dart at some position
      let boundary : BoundaryDart RS data.keep :=
        ⟨⟨dart, hleft⟩, hright⟩
      rcases data.crossingBoundaryDartEquiv.surjective boundary with
        ⟨position, hposition⟩
      have hvertex : data.capBoundaryVertex position =
          (⟨RS.vertOf dart, hleft⟩ : RetainedVertex data.keep) := by
        apply Subtype.ext
        show RS.vertOf (data.crossingBoundaryDartEquiv position).1.1 =
          RS.vertOf dart
        rw [hposition]
      rw [data.collapseComplementToCap_of_keep _ hleft,
        data.collapseComplementToCap_of_not_keep _ hright]
      have hspoke := (data.edgeDeletedPrimalGraph_adj_capSpoke
        removedEdge position (hspokeFree position)).reachable
      have hcycle := data.capVertex_reachable_of_cycle_free
        removedEdge hcycleFree position 0
      rw [hvertex] at hspoke
      exact (hspoke.symm.trans hcycle).symm.symm
  · by_cases hright : data.keep (RS.vertOf (RS.alpha dart))
    · let boundary : BoundaryDart RS data.keep :=
        ⟨⟨RS.alpha dart, hright⟩, by
          change ¬ data.keep (RS.vertOf (RS.alpha (RS.alpha dart)))
          simpa [RS.alpha_involutive] using hleft⟩
      rcases data.crossingBoundaryDartEquiv.surjective boundary with
        ⟨position, hposition⟩
      have hvertex : data.capBoundaryVertex position =
          (⟨RS.vertOf (RS.alpha dart), hright⟩ :
            RetainedVertex data.keep) := by
        apply Subtype.ext
        show RS.vertOf (data.crossingBoundaryDartEquiv position).1.1 =
          RS.vertOf (RS.alpha dart)
        rw [hposition]
      rw [data.collapseComplementToCap_of_not_keep _ hleft,
        data.collapseComplementToCap_of_keep _ hright]
      have hspoke := (data.edgeDeletedPrimalGraph_adj_capSpoke
        removedEdge position (hspokeFree position)).reachable
      have hcycle := data.capVertex_reachable_of_cycle_free
        removedEdge hcycleFree 0 position
      rw [hvertex] at hspoke
      exact hcycle.trans hspoke
    · rw [data.collapseComplementToCap_of_not_keep _ hleft,
        data.collapseComplementToCap_of_not_keep _ hright]

/-- Ambient bridge-freeness supplies a capped path around every retained
internal edge. -/
theorem cap_internal_reachable_of_edgeBridgeFree
    (hfree : EdgeBridgeFree RS)
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected)
    (removed : InternalDart RS data.keep) :
    (edgeDeletedPrimalGraph data.capRotationSystem
      (data.capRotationSystem.edgeOf (Sum.inl (Sum.inl removed)))).Reachable
      (Sum.inl
        (⟨RS.vertOf removed.1.1, removed.1.2⟩ :
          RetainedVertex data.keep))
      (Sum.inl
        (⟨RS.vertOf (RS.alpha removed.1.1), removed.2⟩ :
          RetainedVertex data.keep)) := by
  have hmapped := reachable_map_of_adj_reachable
    data.collapseComplementToCap
    (fun {_ _} hadj => by
      rcases hadj with ⟨dart, hedge, hleft, hright⟩
      subst hleft
      subst hright
      exact data.collapseComplement_reachable_of_internal_removed
        hconnected removed dart hedge)
    (hfree removed.1.1)
  simpa [collapseComplementToCap, removed.1.2, removed.2] using hmapped

/-! ## Spoke and cycle edges reconnect -/

theorem capSpoke_endpoints_reachable_without
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected)
    (j : Fin 5) :
    (edgeDeletedPrimalGraph data.capRotationSystem
      (data.capSpokeEdge j)).Reachable
      (Sum.inr j) (Sum.inl (data.capBoundaryVertex j)) := by
  have hinternalFree : ∀ internal : InternalDart RS data.keep,
      data.capRotationSystem.edgeOf (Sum.inl (Sum.inl internal)) ≠
        data.capSpokeEdge j :=
    fun internal =>
      data.capRotationSystem_edgeOf_internal_ne_capSpokeEdge internal j
  have hcycleStep := (data.edgeDeletedPrimalGraph_adj_capCycle
    (data.capSpokeEdge j) j
    ((data.capSpokeEdge_ne_capCycleEdge j j).symm)).reachable
  have hnextSpoke := (data.edgeDeletedPrimalGraph_adj_capSpoke
    (data.capSpokeEdge j) (j + 1)
    (data.capSpokeEdge_injective.ne (by
      intro h
      have := congrArg (fun x : Fin 5 => x - j) h
      simp at this))).reachable
  have hretained := data.edgeDeletedPrimalGraph_reachable_of_retained_of_ne
    (data.capSpokeEdge j) hinternalFree
    (hconnected (data.capBoundaryVertex (j + 1))
      (data.capBoundaryVertex j))
  exact (hcycleStep.trans hnextSpoke).trans hretained

theorem capCycle_endpoints_reachable_without
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected)
    (j : Fin 5) :
    (edgeDeletedPrimalGraph data.capRotationSystem
      (data.capCycleEdge j)).Reachable
      (Sum.inr j) (Sum.inr (j + 1)) := by
  have hinternalFree : ∀ internal : InternalDart RS data.keep,
      data.capRotationSystem.edgeOf (Sum.inl (Sum.inl internal)) ≠
        data.capCycleEdge j :=
    fun internal =>
      data.capRotationSystem_edgeOf_internal_ne_capCycleEdge internal j
  have hspokeLeft := (data.edgeDeletedPrimalGraph_adj_capSpoke
    (data.capCycleEdge j) j
    (data.capSpokeEdge_ne_capCycleEdge j j)).reachable
  have hspokeRight := (data.edgeDeletedPrimalGraph_adj_capSpoke
    (data.capCycleEdge j) (j + 1)
    (data.capSpokeEdge_ne_capCycleEdge (j + 1) j)).reachable
  have hretained := data.edgeDeletedPrimalGraph_reachable_of_retained_of_ne
    (data.capCycleEdge j) hinternalFree
    (hconnected (data.capBoundaryVertex j)
      (data.capBoundaryVertex (j + 1)))
  exact (hspokeLeft.trans hretained).trans hspokeRight.symm

/-! ## Bridge-freeness -/

/-- The pentagon cap is bridge-free. -/
theorem capRotationSystem_edgeBridgeFree
    (hfree : EdgeBridgeFree RS)
    (hconnected : (retainedAmbientPrimalGraph RS data.keep).Connected) :
    EdgeBridgeFree data.capRotationSystem := by
  intro dart
  rcases dart with interior | boundaryOrSpoke
  · rcases interior with internal | cyc
    · exact data.cap_internal_reachable_of_edgeBridgeFree hfree
        hconnected internal
    · rcases cyc with ⟨j, b⟩
      cases b
      · -- edge = capCycleEdge (j - 1); endpoints inr j → inr (j - 1)
        have hedge : data.capRotationSystem.edgeOf
            (Sum.inl (Sum.inr (j, false))) = data.capCycleEdge (j - 1) :=
          data.capCycleEdge_eq_false j
        rw [hedge]
        rw [show data.capRotationSystem.alpha (Sum.inl (Sum.inr (j, false))) =
          Sum.inl (Sum.inr (j - 1, true)) from by
            change data.capRewiredDartSystem.alpha
              (Sum.inl (Sum.inr (j, false))) = _
            rw [data.capRewiredDartSystem_alpha_cycle]
            rfl]
        have := (data.capCycle_endpoints_reachable_without hconnected
          (j - 1)).symm
        rw [sub_add_cancel] at this
        change (edgeDeletedPrimalGraph data.capRotationSystem
          (data.capCycleEdge (j - 1))).Reachable
            (data.capRotationSystem.vertOf (Sum.inl (Sum.inr (j, false))))
            (data.capRotationSystem.vertOf (Sum.inl (Sum.inr (j - 1, true))))
        rw [show data.capRotationSystem.vertOf
            (Sum.inl (Sum.inr (j, false))) = Sum.inr j from
          data.capRotationSystem_vertOf_cycleDart (j, false),
          show data.capRotationSystem.vertOf
            (Sum.inl (Sum.inr (j - 1, true))) = Sum.inr (j - 1) from
          data.capRotationSystem_vertOf_cycleDart (j - 1, true)]
        exact this
      · have hedge : data.capRotationSystem.edgeOf
            (Sum.inl (Sum.inr (j, true))) = data.capCycleEdge j := rfl
        rw [hedge]
        rw [show data.capRotationSystem.alpha (Sum.inl (Sum.inr (j, true))) =
          Sum.inl (Sum.inr (j + 1, false)) from by
            change data.capRewiredDartSystem.alpha
              (Sum.inl (Sum.inr (j, true))) = _
            rw [data.capRewiredDartSystem_alpha_cycle]
            rfl]
        have := data.capCycle_endpoints_reachable_without hconnected j
        change (edgeDeletedPrimalGraph data.capRotationSystem
          (data.capCycleEdge j)).Reachable
            (data.capRotationSystem.vertOf (Sum.inl (Sum.inr (j, true))))
            (data.capRotationSystem.vertOf (Sum.inl (Sum.inr (j + 1, false))))
        rw [show data.capRotationSystem.vertOf
            (Sum.inl (Sum.inr (j, true))) = Sum.inr j from
          data.capRotationSystem_vertOf_cycleDart (j, true),
          show data.capRotationSystem.vertOf
            (Sum.inl (Sum.inr (j + 1, false))) = Sum.inr (j + 1) from
          data.capRotationSystem_vertOf_cycleDart (j + 1, false)]
        exact this
  · rcases boundaryOrSpoke with position | j
    · have hedge : data.capRotationSystem.edgeOf
          (Sum.inr (Sum.inl position)) = data.capSpokeEdge position := by
        calc
          data.capRotationSystem.edgeOf (Sum.inr (Sum.inl position)) =
              data.capRotationSystem.edgeOf
                (data.capRotationSystem.alpha
                  (Sum.inr (Sum.inl position))) :=
            (data.capRotationSystem.edge_alpha _).symm
          _ = data.capSpokeEdge position := by
            rw [show data.capRotationSystem.alpha
                (Sum.inr (Sum.inl position)) =
                Sum.inr (Sum.inr position) from
              data.capRewiredDartSystem_alpha_boundary position]
            rfl
      rw [hedge]
      rw [show data.capRotationSystem.alpha (Sum.inr (Sum.inl position)) =
        Sum.inr (Sum.inr position) from
          data.capRewiredDartSystem_alpha_boundary position]
      change (edgeDeletedPrimalGraph data.capRotationSystem
        (data.capSpokeEdge position)).Reachable
          (data.capRotationSystem.vertOf (Sum.inr (Sum.inl position)))
          (data.capRotationSystem.vertOf (Sum.inr (Sum.inr position)))
      have hvertSpoke : data.capRotationSystem.vertOf
          (Sum.inr (Sum.inr position)) =
          (Sum.inr position : data.CapVertex) :=
        data.capRotationSystem_vertOf_capDart position
      rw [show data.capRotationSystem.vertOf
          (Sum.inr (Sum.inl position)) =
          Sum.inl (data.capBoundaryVertex position) from rfl,
        hvertSpoke]
      exact (data.capSpoke_endpoints_reachable_without hconnected
        position).symm
    · rw [show data.capRotationSystem.alpha (Sum.inr (Sum.inr j)) =
        Sum.inr (Sum.inl j) from
          data.capRewiredDartSystem_alpha_spoke j]
      change (edgeDeletedPrimalGraph data.capRotationSystem
        (data.capSpokeEdge j)).Reachable
          (data.capRotationSystem.vertOf (Sum.inr (Sum.inr j)))
          (data.capRotationSystem.vertOf (Sum.inr (Sum.inl j)))
      have hvertSpoke : data.capRotationSystem.vertOf
          (Sum.inr (Sum.inr j)) = (Sum.inr j : data.CapVertex) :=
        data.capRotationSystem_vertOf_capDart j
      rw [hvertSpoke,
        show data.capRotationSystem.vertOf (Sum.inr (Sum.inl j)) =
          Sum.inl (data.capBoundaryVertex j) from rfl]
      exact data.capSpoke_endpoints_reachable_without hconnected j

end FiveEdgeCutPentagonCapData

end

end Mettapedia.GraphTheory.FourColor
