import Mettapedia.GraphTheory.FourColor.OpenTangleCutDartSum

/-!
# Cut sizes from the actual darts of a rotation system

Every named edge contributes exactly two oppositely oriented darts. This
gives a cut-size formula independent of the chosen edge names, suitable
for comparing literal rewiring operations.
-/

namespace Mettapedia.GraphTheory.FourColor.RotationCutDartSum

open GoertzelV24RotationMultigraphAdapter GoertzelV24CompositeSeamMultigraph
open BoundarySmallCutProfile OpenTangleCutDartSum

noncomputable section
variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E)

def edgeDartEquiv : E × Bool ≃ RS.D where
  toFun x := if x.2 then someDart RS x.1 else RS.alpha (someDart RS x.1)
  invFun d := (RS.edgeOf d, decide (d = someDart RS (RS.edgeOf d)))
  left_inv := by
    rintro ⟨e, b⟩
    cases b <;> simp only [Bool.false_eq_true, ite_false, ite_true]
    · simp only [RS.edge_alpha, edgeOf_someDart, RS.alpha_fixfree, decide_false]
    · simp only [edgeOf_someDart, decide_true]
  right_inv := by
    intro d
    by_cases h : d = someDart RS (RS.edgeOf d)
    · have ht : decide (d = someDart RS (RS.edgeOf d)) = true := by simpa using h
      simp only [ht, ite_true]
      exact h.symm
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]
      rcases eq_someDart_or RS (RS.edgeOf d) rfl with hd | hd
      · exact (h hd).elim
      · exact hd.symm

def cost (s : V → Bool) : Nat :=
  ∑ d : RS.D, bit (s (RS.vertOf d)) (s (RS.vertOf (RS.alpha d)))

def selected {X : Type*} [Fintype X] (s : X → Bool) : Nat :=
  ∑ x, if s x = true then 1 else 0

theorem selected_card {X : Type*} [Fintype X] (s : X → Bool) :
    selected s = Fintype.card {x // s x = true} := by
  classical
  simp [selected, Fintype.card_subtype]

theorem selected_not {X : Type*} [Fintype X] (s : X → Bool) :
    selected s + selected (fun x => !(s x)) = Fintype.card X := by
  rw [selected, selected, ← Finset.sum_add_distrib]
  calc
    _ = ∑ _ : X, 1 := by
      apply Finset.sum_congr rfl
      intro x _
      cases s x <;> rfl
    _ = _ := by simp

theorem selected_transport {X Y : Type*} [Fintype X] [Fintype Y]
    (e : X ≃ Y) (s : Y → Bool) : selected (s ∘ e) = selected s := by
  exact Fintype.sum_equiv e _ _ (fun _ => rfl)

theorem selected_sum {X Y : Type*} [Fintype X] [Fintype Y]
    (s : X → Bool) (t : Y → Bool) : selected (Sum.elim s t) = selected s + selected t := by
  exact Fintype.sum_sum_type _

theorem twice_cutSize (s : V → Bool) :
    2 * cutSize (toMultigraph RS) s = cost RS s := by
  have he := Fintype.sum_equiv (edgeDartEquiv RS)
    (fun x => bit (s (RS.vertOf (edgeDartEquiv RS x)))
      (s (RS.vertOf (RS.alpha (edgeDartEquiv RS x)))))
    (fun d => bit (s (RS.vertOf d)) (s (RS.vertOf (RS.alpha d)))) (fun _ => rfl)
  unfold cost
  rw [← he, Fintype.sum_prod_type]
  unfold cutSize
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  simp only [Fintype.sum_bool, edgeDartEquiv, Equiv.coe_fn_mk,
    Bool.false_eq_true, ite_false, ite_true, RS.alpha_involutive]
  change 2 * bit (s (RS.vertOf (someDart RS e)))
    (s (RS.vertOf (RS.alpha (someDart RS e)))) = _
  rw [bit_symm (s (RS.vertOf (RS.alpha (someDart RS e)))), two_mul]

theorem cost_not (s : V → Bool) : cost RS (fun v => !(s v)) = cost RS s := by
  apply Finset.sum_congr rfl
  intro d _
  simp [bit]

/-- Count only the orientation leaving the selected side. -/
theorem cost_eq_twice_outgoing (s : V → Bool) : cost RS s =
    2 * Fintype.card {d : RS.D // s (RS.vertOf d) = true ∧
      s (RS.vertOf (RS.alpha d)) = false} := by
  classical
  let e : {d : RS.D // s (RS.vertOf d) = true ∧ s (RS.vertOf (RS.alpha d)) = false} ≃
      {d : RS.D // s (RS.vertOf d) = false ∧ s (RS.vertOf (RS.alpha d)) = true} :=
    { toFun := fun d => ⟨RS.alpha d.1, d.2.2, by simpa only [RS.alpha_involutive] using d.2.1⟩
      invFun := fun d => ⟨RS.alpha d.1, d.2.2, by simpa only [RS.alpha_involutive] using d.2.1⟩
      left_inv := fun d => Subtype.ext (RS.alpha_involutive d.1)
      right_inv := fun d => Subtype.ext (RS.alpha_involutive d.1) }
  have he := Fintype.card_congr e
  simp only [Fintype.card_subtype] at he ⊢
  have hb (a b : Bool) : bit a b =
      (if a = true ∧ b = false then 1 else 0) +
      (if a = false ∧ b = true then 1 else 0) := by cases a <;> cases b <;> rfl
  simp only [cost, hb, Finset.sum_add_distrib, Finset.sum_boole, Nat.cast_id]
  omega

/-- Exact dart and vertex transport preserves the whole cut count. -/
theorem cost_transport {W F : Type*} [Fintype W] [DecidableEq W]
    [Fintype F] [DecidableEq F] (T : RotationSystem W F)
    (d : RS.D ≃ T.D) (v : V ≃ W)
    (ha : ∀ x, d (RS.alpha x) = T.alpha (d x))
    (hv : ∀ x, v (RS.vertOf x) = T.vertOf (d x)) (s : W → Bool) :
    cost RS (s ∘ v) = cost T s := by
  apply Fintype.sum_equiv d
  intro x
  simp only [Function.comp_apply, hv, ha]

/-- Constantness of every putative small cut gives both graph conditions. -/
theorem structural_of_cost [Nonempty V]
    (h : ∀ s : V → Bool, cost RS s ≤ 2 → ∀ u v, s u = s v) :
    (GoertzelV24FaceDualConnectedness.rotationPrimalGraph RS).Connected ∧
      GoertzelV24RotationEdgeBridge.EdgeBridgeFree RS := by
  have hn : ¬ HasSmallCut (toMultigraph RS) := by
    rintro ⟨s, ⟨u, hu⟩, ⟨v, hv⟩, hs⟩
    have hh := h s (by rw [← twice_cutSize]; omega) u v
    simp only [hu, hv, Bool.true_eq_false] at hh
  have hc := SmallCutConnectedBridgeless.connected_of_no_small_cut _ hn
  have hb := SmallCutConnectedBridgeless.bridgeless_of_no_small_cut _ hn
  exact ⟨primalConnected_of_connected RS hc, (bridgeless_iff_edgeBridgeFree RS).mp hb⟩

theorem constant_of_structural
    (hc : (GoertzelV24FaceDualConnectedness.rotationPrimalGraph RS).Connected)
    (hb : GoertzelV24RotationEdgeBridge.EdgeBridgeFree RS)
    (s : V → Bool) (hs : cost RS s ≤ 2) (u v : V) : s u = s v := by
  have hn := SmallCutConnectedBridgeless.no_small_cut_of_connected_bridgeless
    (toMultigraph RS) (connected_of_primalConnected RS hc)
    ((bridgeless_iff_edgeBridgeFree RS).mpr hb)
  have hh : cutSize (toMultigraph RS) s ≤ 1 := by rw [← twice_cutSize] at hs; omega
  cases hu : s u <;> cases hv : s v
  · rfl
  · exact (hn ⟨s, ⟨v, hv⟩, ⟨u, hu⟩, hh⟩).elim
  · exact (hn ⟨s, ⟨u, hu⟩, ⟨v, hv⟩, hh⟩).elim
  · rfl

end
end Mettapedia.GraphTheory.FourColor.RotationCutDartSum

namespace Mettapedia.GraphTheory.FourColor.RotationCutDartSum
open GoertzelV24OpenTangleComposition GoertzelV24OpenTangleComposition.OpenTangleData
open OpenTangleCutDartSum

noncomputable section
variable {V W I J B : Type*} [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J] [Fintype B] [DecidableEq B]

theorem composite_cost (O : OpenTangleData V I B) (P : OpenTangleData W J B)
    (s : V → Bool) (t : W → Bool) :
    cost (O.composeRotationSystem P (Equiv.refl B)) (Sum.elim s t) =
      (∑ d : I, bit (s (O.interiorVert d)) (s (O.interiorVert (O.interiorAlpha d)))) +
      (∑ d : J, bit (t (P.interiorVert d)) (t (P.interiorVert (P.interiorAlpha d)))) +
      2 * ∑ b : B, bit (s (O.boundaryVert b)) (t (P.boundaryVert b)) := by
  unfold cost
  change (∑ d : (I ⊕ J) ⊕ (B ⊕ B), _) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  congr 1
  change (∑ b : B, bit (s (O.boundaryVert b)) (t (P.boundaryVert b))) +
    (∑ b : B, bit (t (P.boundaryVert b)) (s (O.boundaryVert b))) = _
  simp_rw [bit_symm (t _) (s _)]
  omega

end
end Mettapedia.GraphTheory.FourColor.RotationCutDartSum
