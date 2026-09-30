import MettapediaFourColor.DiamondCoupledWiringRotation
import Mettapedia.GraphTheory.FourColor.RotationCutDartSum

/-! # The cut observation of the coupled wiring

The actual wiring has three boundary components. Its cut count retains
their joint port assignment and both new vertex bits. This is a structural
observation, separate from its colouring relation.
-/

namespace FourColor.DiamondCoupledWiring.Rotation

open Mettapedia.GraphTheory.FourColor
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open OpenTangleCutDartSum BoundarySmallCutProfile

def seamCost (b : Fin 8 → Bool) (c : Fin 2 → Bool) : Nat :=
  bit (b 0) (b 1) + bit (b 4) (b 5) +
  bit (b 2) (c 0) + bit (b 3) (c 0) +
  bit (b 6) (c 1) + bit (b 7) (c 1) + bit (c 0) (c 1)

/-- All three blocks, including the two free wires. -/
def block : Fin 8 → Fin 3 := ![0, 0, 2, 2, 1, 1, 2, 2]

theorem seamCost_zero_iff (b : Fin 8 → Bool) (c : Fin 2 → Bool) :
    seamCost b c = 0 ↔
      b 0 = b 1 ∧ b 4 = b 5 ∧
      b 2 = c 0 ∧ b 3 = c 0 ∧ b 6 = c 1 ∧ b 7 = c 1 ∧ c 0 = c 1 := by
  simp [seamCost, bit, and_assoc]

theorem constant_boundary (a : Bool) (c : Fin 2 → Bool)
    (h : seamCost (fun _ => a) c ≤ 1) : ∀ j, c j = a := by
  have hh : ∀ (a x y : Bool), seamCost (fun _ => a) ![x,y] ≤ 1 → x = a ∧ y = a := by
    decide
  have hc : c = ![c 0, c 1] := by ext j; fin_cases j <;> rfl
  rw [hc] at h
  have he := hh a (c 0) (c 1) h
  intro j
  fin_cases j
  · exact he.1
  · exact he.2

def mask (i : Fin 3) (b : Fin 8) : Bool := decide (block b = i)

/-- A zero seam cut is constant, a single block, or its complement. -/
theorem block_cases : ∀ (b : Fin 8 → Bool) (c : Fin 2 → Bool), seamCost b c = 0 →
    (∃ a, b = fun _ => a) ∨
      (∃ i, b = mask i) ∨ (∃ i, b = fun j => !(mask i j)) := by
  decide +kernel

noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  (O : OpenTangleData V I (Fin 8)) (hs : Separated O)

theorem cut_cost (s : V ⊕ Fin 2 → Bool) :
    RotationCutDartSum.cost (closed O hs) s =
      2 * cutSize (sideMultigraph O) (s ∘ Sum.inl) +
      2 * seamCost (s ∘ Sum.inl ∘ O.boundaryVert) (s ∘ Sum.inr) := by
  rw [OpenTangleCutDartSum.twice_cutSize]
  unfold RotationCutDartSum.cost
  change (∑ d : Dart I, bit (s (vertex O d)) (s (vertex O (alpha O d)))) = _
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Nat.add_assoc]
  congr 1
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero]
  dsimp [vertex, alpha, seam, seamFun, coreVertex]
  simp only [seamCost, Function.comp_apply]
  simp only [bit_symm (s (.inl (O.boundaryVert 1))),
    bit_symm (s (.inl (O.boundaryVert 5))), bit_symm (s (.inr 0)) (s (.inl (O.boundaryVert 2))),
    bit_symm (s (.inr 0)) (s (.inl (O.boundaryVert 3))),
    bit_symm (s (.inr 1)) (s (.inl (O.boundaryVert 6))),
    bit_symm (s (.inr 1)) (s (.inl (O.boundaryVert 7))),
    bit_symm (s (.inr 1)) (s (.inr 0))]
  omega

/-- Only cuts constant on each wiring component can survive a small-cut
test when the exterior is connected. -/
theorem structural
    (hc : (sideMultigraph O).Connected)
    (hblocked : ∀ s : V → Bool, cutSize (sideMultigraph O) s ≤ 1 →
      (∀ c, seamCost (s ∘ O.boundaryVert) c = 0 → ∀ u v, s u = s v)) :
    (GoertzelV24FaceDualConnectedness.rotationPrimalGraph (closed O hs)).Connected ∧
      GoertzelV24RotationEdgeBridge.EdgeBridgeFree (closed O hs) := by
  apply RotationCutDartSum.structural_of_cost
  intro s hcost
  rw [cut_cost] at hcost
  have ho : cutSize (sideMultigraph O) (s ∘ Sum.inl) ≤ 1 := by omega
  have hn : seamCost (s ∘ Sum.inl ∘ O.boundaryVert) (s ∘ Sum.inr) ≤ 1 := by omega
  have const : ∀ u v : V, s (.inl u) = s (.inl v) := by
    by_cases hz : cutSize (sideMultigraph O) (s ∘ Sum.inl) = 0
    · have he : ∀ e, (s ∘ Sum.inl) ((sideMultigraph O).fst e) =
          (s ∘ Sum.inl) ((sideMultigraph O).snd e) := by
        have hz' := Finset.sum_eq_zero_iff.mp hz
        intro e
        have hh := hz' e (Finset.mem_univ e)
        split_ifs at hh with hh'
        · exact hh'
      exact fun u v => SmallCutConnectedBridgeless.constant_on_path _ (s ∘ Sum.inl)
        (fun _ => False) (fun e _ => he e) (hc u v)
    · have hz' : seamCost (s ∘ Sum.inl ∘ O.boundaryVert) (s ∘ Sum.inr) = 0 := by omega
      exact hblocked _ ho (s ∘ Sum.inr) hz'
  let a := s (.inl (O.boundaryVert 0))
  have hb : s ∘ Sum.inl ∘ O.boundaryVert = fun _ => a := by
    funext b
    exact const _ _
  rw [hb] at hn
  have hj := constant_boundary a (s ∘ Sum.inr) hn
  have hall : ∀ v, s v = a := by
    rintro (v | j)
    · exact const _ _
    · exact hj j
  exact fun u v => (hall u).trans (hall v).symm

end
end FourColor.DiamondCoupledWiring.Rotation
