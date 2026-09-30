import MettapediaFourColor.JointDiamondTangle
import MettapediaFourColor.DiamondCoupledWiringCuts
import Mettapedia.GraphTheory.FourColor.InternalSixCutCost

/-! # Lifting separating port blocks through the original joint diamond

Two-vertex extensions turn either free-wire block into a three-edge cut.
For the four-port coupled block, two choices of old shore retain the same
five-edge cut cost while putting enough vertices on both sides. The
exterior size and its vertex bits remain parameters throughout.
-/

namespace FourColor.JointDiamondPatch.Tangle.CutLifting
open Mettapedia.GraphTheory.FourColor
open OpenTangleCutDartSum RotationCutDartSum BoundarySmallCutProfile
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open DiamondCoupledWiring.Rotation

def interiorCost (t : Fin 14 → Bool) : Nat :=
  ∑ d : Fin 34, bit (t (piece.interiorVert d)) (t (piece.interiorVert (piece.interiorAlpha d)))

def localCost (b : Fin 8 → Bool) (t : Fin 14 → Bool) : Nat :=
  interiorCost t + 2 * ∑ j : Fin 8, bit (b j) (t (piece.boundaryVert j))

def extend (i : Fin 3) (large : Bool) (v : Fin 14) : Bool :=
  if i = 0 then decide (v = 0 ∨ v = 1)
  else if i = 1 then decide (v = 8 ∨ v = 9)
  else if large then decide (v ≠ 0 ∧ v ≠ 1 ∧ v ≠ 8 ∧ v ≠ 9)
  else decide (v = 2 ∨ v = 3 ∨ v = 5 ∨ v = 6)

theorem extension_cost : ∀ i large,
    localCost (mask i) (extend i large) = if i = 2 then 8 else 4 := by decide +kernel

theorem extension_size : ∀ i large,
    selected (extend i large) = if i = 2 then (if large then 10 else 4) else 2 := by
  decide +kernel

theorem constant_cost : ∀ a : Bool, localCost (fun _ => a) (fun _ => a) = 0 := by
  decide +kernel

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  (O : OpenTangleData V I (Fin 8))

abbrev original := O.composeRotationSystem piece (Equiv.refl _)

theorem cost_original (s : V → Bool) (t : Fin 14 → Bool) :
    cost (original O) (Sum.elim s t) =
      2 * cutSize (sideMultigraph O) s + localCost (s ∘ O.boundaryVert) t := by
  rw [composite_cost, OpenTangleCutDartSum.twice_cutSize]
  exact Nat.add_assoc _ _ _

variable
  (hthree : ∀ s, 3 ≤ selected s → 3 ≤ selected (fun v => !(s v)) →
    10 ≤ cost (original O) s)
  (hfive : ∀ s, cost (original O) s ≤ 10 →
    selected s ≤ 5 ∨ selected (fun v => !(s v)) ≤ 5)
  (hspace : 3 ≤ Fintype.card V)

include hthree hfive hspace in
/-- A hypothetical one-edge exterior cut constant on a single block
violates an actual source cut bound. Both five-cut extensions are used. -/
theorem block_impossible (s : V → Bool) (hs : cutSize (sideMultigraph O) s ≤ 1)
    (i : Fin 3) (hb : s ∘ O.boundaryVert = mask i) : False := by
  have hc (large) : cost (original O) (Sum.elim s (extend i large)) ≤
      if i = 2 then 10 else 6 := by
    rw [cost_original, hb, extension_cost]
    split_ifs <;> omega
  have hn (large) : selected (fun v => !(Sum.elim s (extend i large) v)) =
      selected (fun v => !(s v)) + selected (fun v => !(extend i large v)) :=
    by
      have he : (fun v => !(Sum.elim s (extend i large) v)) =
          Sum.elim (fun v => !(s v)) (fun v => !(extend i large v)) := by
        funext v
        cases v <;> rfl
      rw [he, selected_sum]
  have ht (large) := selected_not (extend i large)
  simp only [Fintype.card_fin, extension_size] at ht
  by_cases hi : i = 2
  · subst i
    have ha := hfive _ (hc false)
    have hb' := hfive _ (hc true)
    simp only [selected_sum, hn, extension_size, ite_true, Bool.false_eq_true, ite_false] at ha hb'
    have htotal := selected_not s
    have ht0 := ht false
    have ht1 := ht true
    norm_num at ht0 ht1
    omega
  · have hx : 1 ≤ selected s := by
      have hm : ∃ j, mask i j = true := by fin_cases i <;> decide
      obtain ⟨j, hj⟩ := hm
      rw [selected_card]
      exact Fintype.card_pos_iff.mpr ⟨⟨O.boundaryVert j,
        (congrFun hb j).trans hj⟩⟩
    have hh := hthree (Sum.elim s (extend i false))
      (by rw [selected_sum, extension_size]; simp only [hi, ite_false]; omega)
      (by rw [hn]; have h := ht false; simp only [hi, ite_false] at h; omega)
    have hh' := hc false
    simp only [hi, ite_false] at hh'
    omega

variable (hlow : ∀ s, cost (original O) s ≤ 2 → ∀ u v, s u = s v)

include hthree hfive hspace hlow in
/-- The joint boundary cut law rules out every bridge in the actual wiring,
for an arbitrary connected exterior of the stated size. -/
theorem structural (hs : Separated O) (hout : (sideMultigraph O).Connected) :
    (GoertzelV24FaceDualConnectedness.rotationPrimalGraph (closed O hs)).Connected ∧
      GoertzelV24RotationEdgeBridge.EdgeBridgeFree (closed O hs) := by
  apply DiamondCoupledWiring.Rotation.structural O hs hout
  intro s hc c hz
  rcases block_cases (s ∘ O.boundaryVert) c hz with ⟨a, ha⟩ | ⟨i, hi⟩ | ⟨i, hi⟩
  · have hh := hlow (Sum.elim s (fun _ => a)) (by
      rw [cost_original, ha, constant_cost]
      omega)
    exact fun u v => hh (.inl u) (.inl v)
  · exact (block_impossible O hthree hfive hspace s hc i hi).elim
  · have hc' : cutSize (sideMultigraph O) (fun v => !(s v)) ≤ 1 := by
      have he : ∀ a b : Bool, ((!a) = (!b)) ↔ a = b := by decide
      simpa only [cutSize, he] using hc
    have hi' : (fun v => !(s v)) ∘ O.boundaryVert = mask i := by
      funext j
      have he := congrFun hi j
      change (!(s (O.boundaryVert j))) = mask i j
      change s (O.boundaryVert j) = !(mask i j) at he
      rw [he, Bool.not_not]
    exact (block_impossible O hthree hfive hspace _ hc' i hi').elim

end
end FourColor.JointDiamondPatch.Tangle.CutLifting
