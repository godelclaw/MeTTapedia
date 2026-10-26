import Mettapedia.SetTheory.AntiFoundation.Graphs
import Mettapedia.SetTheory.AntiFoundation.ReadingFixedPoints
import Mathlib.Data.Fintype.Prod
import Mettapedia.Order.FiniteSetFixedPoints
import Mathlib.Data.Set.Card
import Mathlib.Logic.Function.Iterate
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Computable readings on a finite carrier

On a finite graph the child-class step reaches its least fixed point after at most
one more iteration than there are pairs of nodes, starting from equality, and its greatest
fixed point in the same number of steps starting from the total relation. The same upward
iteration from any bisimulation reaches the least reading above it. The Boolean matrix of
the upward iteration computes that closure; from the table of equality it computes the
least reading, and is the value decided on the pictures.

The greatest reading is bisimilarity. The refinement that computes bisimilarity of a finite
graph is `Profiles.ProfileGraphReadout.FiniteBoolean.equivalent`, and
`Profiles.ProfileFiniteReadings` states it for the greatest reading. On the pictures the
greatest reading is read off `gfp_eq_bisimilar` and the bisimulations of `Graphs.lean`.
-/

set_option autoImplicit false

open Function
open Mettapedia.TypeTheory.MaterialSets.Hypersets

namespace Mettapedia.SetTheory.AntiFoundation

universe u

variable {α : Type u}

/-- Pairs related by a relation. -/
def relPairs (R : α → α → Prop) : Set (α × α) :=
  {p | R p.1 p.2}

@[simp] theorem mem_relPairs {R : α → α → Prop} {p : α × α} :
    p ∈ relPairs R ↔ R p.1 p.2 := Iff.rfl

private theorem relPairs_injective :
    Function.Injective (fun R : Setoid α => relPairs (⇑R)) := by
  intro R S same
  ext a b
  exact Set.ext_iff.mp same (a, b)

/-- Both iteration directions use the same finite-pair stabilization theorem. -/
theorem ordered_iterate_stabilizes [Fintype α] (f : Setoid α →o Setoid α) (K : Setoid α)
    (ordered : K ≤ f K ∨ f K ≤ K) :
    f^[Fintype.card α * Fintype.card α] K =
      f^[Fintype.card α * Fintype.card α + 1] K := by
  apply relPairs_injective
  have stable : ∀ n, relPairs (⇑(f^[n] K)) = relPairs (⇑(f^[n+1] K)) →
      relPairs (⇑(f^[n+1] K)) = relPairs (⇑(f^[n+2] K)) := by
    intro n same
    rw [Function.iterate_succ_apply' f n, Function.iterate_succ_apply' f (n+1)]
    exact congrArg (fun R : Setoid α => relPairs (⇑(f R))) (relPairs_injective same)
  have card : Nat.card (α × α) = Fintype.card α * Fintype.card α := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card]
  rcases ordered with up | down
  · have monotone : Monotone (fun n => relPairs (⇑(f^[n] K))) :=
      fun _ _ h _ related => (f.monotone.monotone_iterate_of_le_map up h) related
    have result := Mettapedia.Order.FiniteSetFixedPoints.monotone_chain_stabilizes_at_card
      _ monotone stable
    rwa [card] at result
  · have antitone : Antitone (fun n => relPairs (⇑(f^[n] K))) :=
      fun _ _ h _ related => (f.monotone.antitone_iterate_of_map_le down h) related
    have result := Mettapedia.Order.FiniteSetFixedPoints.antitone_chain_stabilizes_at_card
      _ antitone stable
    rwa [card] at result

theorem bot_le_step_bot (edge : Edge α) : ⊥ ≤ step edge ⊥ := by
  rw [le_step_iff_isBisimulation]
  simpa [Setoid.bot_def] using (IsBisimulation.eq (r := edge))

/-! ## Iterating upward from a bisimulation -/

theorem iterate_le_succ (edge : Edge α) {K : Setoid α} (hK : K ≤ step edge K) (n : Nat) :
    (step edge)^[n] K ≤ (step edge)^[n + 1] K := by
  exact (step edge).monotone.monotone_iterate_of_le_map hK (Nat.le_succ n)

theorem le_iterate (edge : Edge α) {K : Setoid α} (hK : K ≤ step edge K) (n : Nat) :
    K ≤ (step edge)^[n] K := by
  exact (step edge).monotone.monotone_iterate_of_le_map hK (Nat.zero_le n)

theorem iterate_le_of_reading (edge : Edge α) {K R : Setoid α} (hKR : K ≤ R)
    (hR : step edge R ≤ R) (n : Nat) : (step edge)^[n] K ≤ R := by
  exact ((step edge).monotone.iterate n hKR).trans
    ((step edge).monotone.antitone_iterate_of_map_le hR (Nat.zero_le n))

theorem iterate_stable (edge : Edge α) {K : Setoid α} {k : Nat}
    (h : (step edge)^[k] K = (step edge)^[k + 1] K) (n : Nat) :
    (step edge)^[k + n] K = (step edge)^[k] K := by
  rw [Nat.add_comm k n, Function.iterate_add_apply]
  exact Function.iterate_fixed (by rw [← iterate_succ_apply' (step edge) k]; exact h.symm) n

theorem relPairs_ncard_le [Fintype α] (R : α → α → Prop) :
    (relPairs R).ncard ≤ Fintype.card α * Fintype.card α := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_prod] using (relPairs R).ncard_le_card

theorem relPairs_ncard_lt_of_lt [Fintype α] {R S : Setoid α} (hle : R ≤ S) (hne : R ≠ S) :
    (relPairs (⇑R)).ncard < (relPairs (⇑S)).ncard := by
  exact Set.ncard_lt_ncard (ssubset_iff_subset_ne.mpr
    ⟨fun _ hp => hle hp, fun equal => hne (relPairs_injective equal)⟩)

theorem ncard_iterate_ge [Fintype α] (edge : Edge α) {K : Setoid α} (hK : K ≤ step edge K)
    (n : Nat) (hstrict : ∀ k < n, (step edge)^[k] K ≠ (step edge)^[k + 1] K) :
    n ≤ (relPairs (⇑((step edge)^[n] K))).ncard := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
    have hlt := relPairs_ncard_lt_of_lt (iterate_le_succ edge hK n)
      (hstrict n (Nat.lt_succ_self n))
    exact Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (ih fun k hk => hstrict k (Nat.lt_succ_of_lt hk)) hlt)

theorem exists_iterate_fixed [Fintype α] (edge : Edge α) {K : Setoid α}
    (hK : K ≤ step edge K) :
    ∃ k, k ≤ Fintype.card α * Fintype.card α ∧
      (step edge)^[k] K = (step edge)^[k + 1] K := by
  exact ⟨_, le_rfl, ordered_iterate_stabilizes (step edge) K (.inl hK)⟩

/-- The closure of a setoid under the child-class step: one more iteration than there are
pairs of nodes. -/
def stepClosure [Fintype α] (edge : Edge α) (K : Setoid α) : Setoid α :=
  (step edge)^[Fintype.card α * Fintype.card α + 1] K

/-- The closure of a bisimulation is a reading. -/
theorem stepClosure_reading [Fintype α] (edge : Edge α) {K : Setoid α}
    (hK : K ≤ step edge K) : step edge (stepClosure edge K) = stepClosure edge K := by
  obtain ⟨k, hk, heq⟩ := exists_iterate_fixed edge hK
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le (Nat.le_succ_of_le hk)
  unfold stepClosure
  rw [← Nat.succ_eq_add_one, hd, iterate_stable edge heq d,
    ← iterate_succ_apply' (step edge) k]
  exact heq.symm

theorem le_stepClosure [Fintype α] (edge : Edge α) {K : Setoid α} (hK : K ≤ step edge K) :
    K ≤ stepClosure edge K :=
  le_iterate edge hK _

/-- One child-class step of a bisimulation lies inside its closure. -/
theorem step_le_stepClosure [Fintype α] (edge : Edge α) {K : Setoid α}
    (hK : K ≤ step edge K) : step edge K ≤ stepClosure edge K := by
  have h := (step edge).monotone (le_stepClosure edge hK)
  rwa [stepClosure_reading edge hK] at h

/-- The closure of a bisimulation lies below every reading above that bisimulation. -/
theorem stepClosure_le_of_reading [Fintype α] (edge : Edge α) {K R : Setoid α} (hKR : K ≤ R)
    (hR : step edge R ≤ R) : stepClosure edge K ≤ R :=
  iterate_le_of_reading edge hKR hR _

/-- A reading is its own closure. -/
theorem stepClosure_of_reading [Fintype α] (edge : Edge α) {K : Setoid α}
    (hK : step edge K = K) : stepClosure edge K = K :=
  Function.iterate_fixed hK _

/-- Equality iterated one step past the number of pairs is the least reading. -/
theorem iterate_fuel_eq_lfp [Fintype α] (edge : Edge α) :
    (step edge)^[Fintype.card α * Fintype.card α + 1] ⊥ = (step edge).lfp := by
  apply le_antisymm
  · exact iterate_le_of_reading edge bot_le (step edge).map_lfp.le _
  · exact (step edge).lfp_le (stepClosure_reading edge (bot_le_step_bot edge)).le

theorem iterate_top_succ_le (edge : Edge α) (n : Nat) :
    (step edge)^[n + 1] ⊤ ≤ (step edge)^[n] ⊤ := by
  exact (step edge).monotone.antitone_iterate_of_map_le le_top (Nat.le_succ n)

theorem gfp_le_iterate_top (edge : Edge α) (n : Nat) :
    (step edge).gfp ≤ (step edge)^[n] ⊤ := by
  exact ((step edge).isFixedPt_gfp.iterate n).symm.trans_le
    ((step edge).monotone.iterate n le_top)

theorem iterate_top_fixed_eq_gfp (edge : Edge α) {n : Nat}
    (h : (step edge)^[n + 1] ⊤ = (step edge)^[n] ⊤) :
    (step edge)^[n] ⊤ = (step edge).gfp := by
  apply le_antisymm
  · apply (step edge).le_gfp
    rw [← iterate_succ_apply' (step edge) n]
    exact h.symm.le
  · exact gfp_le_iterate_top edge n

theorem iterate_top_stable (edge : Edge α) {k : Nat}
    (h : (step edge)^[k + 1] ⊤ = (step edge)^[k] ⊤) (n : Nat) :
    (step edge)^[k + n] ⊤ = (step edge)^[k] ⊤ := by
  exact iterate_stable edge h.symm n

theorem ncard_iterate_top_add_le [Fintype α] (edge : Edge α) (n : Nat)
    (hstrict : ∀ k < n, (step edge)^[k + 1] ⊤ ≠ (step edge)^[k] ⊤) :
    (relPairs (⇑((step edge)^[n] ⊤))).ncard + n ≤ Fintype.card α * Fintype.card α := by
  induction n with
  | zero => change (relPairs (⇑(⊤ : Setoid α))).ncard ≤ _; exact relPairs_ncard_le _
  | succ n ih =>
    have drops := relPairs_ncard_lt_of_lt (iterate_top_succ_le edge n)
      (hstrict n (Nat.lt_succ_self n))
    have earlier := ih (fun k hk => hstrict k (Nat.lt_succ_of_lt hk))
    omega

theorem exists_top_iterate_fixed [Fintype α] (edge : Edge α) :
    ∃ k, k ≤ Fintype.card α * Fintype.card α ∧
      (step edge)^[k + 1] ⊤ = (step edge)^[k] ⊤ := by
  exact ⟨_, le_rfl, (ordered_iterate_stabilizes (step edge) ⊤ (.inr le_top)).symm⟩

/-- The total relation iterated one step past the number of pairs is the greatest reading. -/
theorem iterate_fuel_eq_gfp [Fintype α] (edge : Edge α) :
    (step edge)^[Fintype.card α * Fintype.card α + 1] ⊤ = (step edge).gfp := by
  have fixed := ordered_iterate_stabilizes (step edge) ⊤ (.inr le_top)
  exact fixed.symm.trans (iterate_top_fixed_eq_gfp edge fixed.symm)

/-! ## Boolean matrix -/

/-- One child-class step on a Boolean matrix, quantified over an enumeration. -/
def matrixStep (elems : List α) (edgeB : α → α → Bool) (M : α → α → Bool) : α → α → Bool :=
  fun a b =>
    elems.all (fun a' => !edgeB a a' || elems.any (fun b' => edgeB b b' && M a' b')) &&
      elems.all (fun b' => !edgeB b b' || elems.any (fun a' => edgeB a a' && M a' b'))

theorem matrixStep_true_iff [DecidableEq α] (elems : List α) (complete : ∀ a, a ∈ elems)
    (edge : Edge α) (edgeB : α → α → Bool)
    (hedge : ∀ x y, edgeB x y = true ↔ edge x y) (M : α → α → Bool) (R : α → α → Prop)
    (hM : ∀ x y, M x y = true ↔ R x y) (a b : α) :
    matrixStep elems edgeB M a b = true ↔ SameChildren edge R a b := by
  classical
  have hfalse : ∀ x y, edgeB x y = false ↔ ¬ edge x y := by
    intro x y
    exact Bool.eq_false_iff.trans (not_congr (hedge x y))
  simp [matrixStep, List.all_eq_true, List.any_eq_true, complete,
    Bool.or_eq_true, Bool.and_eq_true, hfalse, hedge, hM, SameChildren, ← imp_iff_not_or]

theorem matrixIter_iff [DecidableEq α] (elems : List α) (complete : ∀ a, a ∈ elems)
    (edge : Edge α) (edgeB : α → α → Bool)
    (hedge : ∀ x y, edgeB x y = true ↔ edge x y) (M : α → α → Bool) (K : Setoid α)
    (hM : ∀ x y, M x y = true ↔ K x y) (n : Nat) (a b : α) :
    (matrixStep elems edgeB)^[n] M a b = true ↔ ((step edge)^[n] K) a b := by
  induction n generalizing a b with
  | zero => exact hM a b
  | succ n ih =>
    rw [iterate_succ_apply', iterate_succ_apply']
    exact (matrixStep_true_iff elems complete edge edgeB hedge
      ((matrixStep elems edgeB)^[n] M) (⇑((step edge)^[n] K)) ih a b).trans
        (step_apply edge ((step edge)^[n] K) a b).symm

/-- The closure of a Boolean table under the child-class step. -/
def matrixClosure [Fintype α] (elems : List α) (edgeB : α → α → Bool) (M : α → α → Bool) :
    α → α → Bool :=
  (matrixStep elems edgeB)^[Fintype.card α * Fintype.card α + 1] M

theorem matrixClosure_iff [Fintype α] [DecidableEq α] (elems : List α)
    (complete : ∀ a, a ∈ elems) (edge : Edge α) (edgeB : α → α → Bool)
    (hedge : ∀ x y, edgeB x y = true ↔ edge x y) (M : α → α → Bool) (K : Setoid α)
    (hM : ∀ x y, M x y = true ↔ K x y) (a b : α) :
    matrixClosure elems edgeB M a b = true ↔ stepClosure edge K a b :=
  matrixIter_iff elems complete edge edgeB hedge M K hM _ a b

theorem decide_eq_iff_bot [DecidableEq α] (x y : α) :
    decide (x = y) = true ↔ (⊥ : Setoid α) x y := by
  simp

/-- Least reading, computed by closing the table of equality. -/
def matrixLfp [Fintype α] [DecidableEq α] (elems : List α) (edgeB : α → α → Bool) :
    α → α → Bool :=
  matrixClosure elems edgeB (fun x y => decide (x = y))

theorem matrixLfp_iff_lfp [Fintype α] [DecidableEq α] (elems : List α) (complete : ∀ a, a ∈ elems)
    (edge : Edge α) (edgeB : α → α → Bool)
    (hedge : ∀ x y, edgeB x y = true ↔ edge x y) (a b : α) :
    matrixLfp elems edgeB a b = true ↔ (step edge).lfp a b := by
  rw [matrixLfp, matrixClosure_iff elems complete edge edgeB hedge _ ⊥ decide_eq_iff_bot a b]
  exact Iff.of_eq (congrFun (congrFun
    (congrArg (fun S : Setoid α => (⇑S : α → α → Prop)) (iterate_fuel_eq_lfp edge)) a) b)

/-! ## Pictures -/

instance : Fintype Loop where
  elems := {Loop.node}
  complete a := by cases a; simp

theorem loop_card : Fintype.card Loop = 1 := by
  decide

def loopElems : List Loop := [Loop.node]

theorem loop_complete (a : Loop) : a ∈ loopElems := by
  cases a; simp [loopElems]

def loopEdgeB : Loop → Loop → Bool := fun _ _ => true

theorem loopEdgeB_iff (x y : Loop) : loopEdgeB x y = true ↔ loopEdge x y := by
  cases x
  cases y
  simp [loopEdgeB, loopEdge]

theorem loop_matrixLfp_true : matrixLfp loopElems loopEdgeB Loop.node Loop.node = true := by
  decide

theorem loop_lfp_node : (step loopEdge).lfp Loop.node Loop.node :=
  (matrixLfp_iff_lfp loopElems loop_complete loopEdge loopEdgeB loopEdgeB_iff _ _).mp
    loop_matrixLfp_true

instance : Fintype Cycle where
  elems := {.l, .r}
  complete a := by cases a <;> simp

theorem cycle_card : Fintype.card Cycle = 2 := by
  decide

def cycleElems : List Cycle := [.l, .r]

theorem cycle_complete (a : Cycle) : a ∈ cycleElems := by
  cases a <;> simp [cycleElems]

def cycleEdgeB : Cycle → Cycle → Bool
  | .l, .r => true
  | .r, .l => true
  | _, _ => false

theorem cycleEdgeB_iff (x y : Cycle) : cycleEdgeB x y = true ↔ cycleEdge x y := by
  cases x <;> cases y <;> simp [cycleEdgeB, cycleEdge]

theorem cycle_matrixLfp_values :
    matrixLfp cycleElems cycleEdgeB .l .l = true ∧
    matrixLfp cycleElems cycleEdgeB .l .r = false ∧
    matrixLfp cycleElems cycleEdgeB .r .l = false ∧
    matrixLfp cycleElems cycleEdgeB .r .r = true := by
  decide

theorem cycle_lfp_values :
    (step cycleEdge).lfp .l .l ∧ ¬ (step cycleEdge).lfp .l .r ∧
      ¬ (step cycleEdge).lfp .r .l ∧ (step cycleEdge).lfp .r .r := by
  simpa only [← matrixLfp_iff_lfp cycleElems cycle_complete cycleEdge cycleEdgeB
    cycleEdgeB_iff, ← Bool.eq_false_iff] using cycle_matrixLfp_values

theorem cycle_gfp_lr : (step cycleEdge).gfp .l .r := by
  rw [gfp_eq_bisimilar]
  exact cycle_l_bisim_r

instance : Fintype Scott where
  elems := {.s0, .s1}
  complete a := by cases a <;> simp

theorem scott_card : Fintype.card Scott = 2 := by
  decide

def scottElems : List Scott := [.s0, .s1]

theorem scott_complete (a : Scott) : a ∈ scottElems := by
  cases a <;> simp [scottElems]

def scottEdgeB : Scott → Scott → Bool
  | .s0, .s0 => true
  | .s1, .s0 => true
  | .s1, .s1 => true
  | .s0, .s1 => false

theorem scottEdgeB_iff (x y : Scott) : scottEdgeB x y = true ↔ scottEdge x y := by
  cases x <;> cases y <;> simp [scottEdgeB, scottEdge]

theorem scott_matrixLfp_values :
    matrixLfp scottElems scottEdgeB .s0 .s0 = true ∧
    matrixLfp scottElems scottEdgeB .s0 .s1 = false ∧
    matrixLfp scottElems scottEdgeB .s1 .s0 = false ∧
    matrixLfp scottElems scottEdgeB .s1 .s1 = true := by
  decide

theorem scott_lfp_values :
    (step scottEdge).lfp .s0 .s0 ∧ ¬ (step scottEdge).lfp .s0 .s1 ∧
      ¬ (step scottEdge).lfp .s1 .s0 ∧ (step scottEdge).lfp .s1 .s1 := by
  simpa only [← matrixLfp_iff_lfp scottElems scott_complete scottEdge scottEdgeB
    scottEdgeB_iff, ← Bool.eq_false_iff] using scott_matrixLfp_values

theorem scott_gfp_s0_s1 : (step scottEdge).gfp .s0 .s1 := by
  rw [gfp_eq_bisimilar]
  exact scott_s0_bisim_s1

instance : Fintype Fin3 where
  elems := {.n0, .n1, .n2}
  complete a := by cases a <;> simp

theorem fin_card : Fintype.card Fin3 = 3 := by
  decide

def finElems : List Fin3 := [.n0, .n1, .n2]

theorem fin_complete (a : Fin3) : a ∈ finElems := by
  cases a <;> simp [finElems]

def finEdgeB : Fin3 → Fin3 → Bool
  | .n0, .n1 => true
  | .n1, .n0 => true
  | .n1, .n2 => true
  | .n2, .n0 => true
  | .n2, .n1 => true
  | _, _ => false

theorem finEdgeB_iff (x y : Fin3) : finEdgeB x y = true ↔ finEdge x y := by
  cases x <;> cases y <;> simp [finEdgeB, finEdge]

theorem fin_matrixLfp_diag (x y : Fin3) :
    matrixLfp finElems finEdgeB x y = decide (x = y) := by
  cases x <;> cases y <;> decide

theorem fin_lfp_iff_eq (x y : Fin3) : (step finEdge).lfp x y ↔ x = y := by
  rw [← matrixLfp_iff_lfp finElems fin_complete finEdge finEdgeB finEdgeB_iff]
  rw [fin_matrixLfp_diag, decide_eq_true_eq]

theorem fin_gfp_total (x y : Fin3) : (step finEdge).gfp x y := by
  rw [gfp_eq_bisimilar]
  exact fin_total_bisim.bisimilar trivial

/-- The partition that pairs `n0` with `n1` and leaves `n2` alone. -/
def finPart01 : Setoid Fin3 :=
  Setoid.ker fun x =>
    match x with
    | .n0 => false
    | .n1 => false
    | .n2 => true

theorem finPart01_not_reading : step finEdge finPart01 ≠ finPart01 := by
  intro fixed
  have related : SameChildren finEdge (⇑finPart01) .n0 .n1 :=
    (step_apply _ _ _ _).mp (fixed.symm ▸ (rfl : finPart01 .n0 .n1))
  obtain ⟨a, available, same⟩ := related.2 .n2 (by trivial)
  cases a <;> simp [finEdge] at available
  change (false : Bool) = true at same
  cases same

instance : Fintype Nest where
  elems := {.blank, .point}
  complete a := by cases a <;> simp

theorem nest_card : Fintype.card Nest = 2 := by
  decide

def nestElems : List Nest := [.blank, .point]

theorem nest_complete (a : Nest) : a ∈ nestElems := by
  cases a <;> simp [nestElems]

def nestEdgeB : Nest → Nest → Bool
  | .point, .blank => true
  | .point, .point => true
  | _, _ => false

theorem nestEdgeB_iff (x y : Nest) : nestEdgeB x y = true ↔ nestEdge x y := by
  cases x <;> cases y <;> simp [nestEdgeB, nestEdge]

theorem nest_matrixLfp_values :
    matrixLfp nestElems nestEdgeB .blank .blank = true ∧
    matrixLfp nestElems nestEdgeB .blank .point = false ∧
    matrixLfp nestElems nestEdgeB .point .blank = false ∧
    matrixLfp nestElems nestEdgeB .point .point = true := by
  decide

theorem nest_lfp_values :
    (step nestEdge).lfp .blank .blank ∧ ¬ (step nestEdge).lfp .blank .point ∧
      ¬ (step nestEdge).lfp .point .blank ∧ (step nestEdge).lfp .point .point := by
  simpa only [← matrixLfp_iff_lfp nestElems nest_complete nestEdge nestEdgeB
    nestEdgeB_iff, ← Bool.eq_false_iff] using nest_matrixLfp_values

theorem nest_not_gfp_blank_point : ¬ (step nestEdge).gfp .blank .point := by
  rw [gfp_eq_bisimilar]
  intro h
  exact nest_point_not_bisim_blank ((bisimilarSetoid_iff nestEdge).mp h).symm

theorem nest_top_not_reading : step nestEdge ⊤ ≠ ⊤ := by
  intro same
  exact nest_not_gfp_blank_point ((step nestEdge).le_gfp same.symm.le (by trivial))

/-! ## Three loops: every equivalence is a reading -/

inductive ThreeLoop where
  | a
  | b
  | c
  deriving DecidableEq

instance : Fintype ThreeLoop where
  elems := {.a, .b, .c}
  complete x := by cases x <;> simp

/-- Each node is its own only child. -/
def threeEdge : Edge ThreeLoop := fun x y => x = y

theorem three_card : Fintype.card ThreeLoop = 3 := by
  decide

def threeElems : List ThreeLoop := [.a, .b, .c]

theorem three_complete (x : ThreeLoop) : x ∈ threeElems := by
  cases x <;> simp [threeElems]

def threeEdgeB (x y : ThreeLoop) : Bool := decide (x = y)

theorem threeEdgeB_iff (x y : ThreeLoop) : threeEdgeB x y = true ↔ threeEdge x y := by
  simp [threeEdgeB, threeEdge, decide_eq_true_eq]

theorem three_step_apply (R : Setoid ThreeLoop) {x y : ThreeLoop} :
    step threeEdge R x y ↔ R x y := by
  simp [step_apply, SameChildren, threeEdge]

/-- On three self-loops the child-class step fixes every equivalence. -/
theorem three_every_reading (R : Setoid ThreeLoop) : step threeEdge R = R := by
  ext x y
  exact three_step_apply R

def threePairAB : Setoid ThreeLoop :=
  Setoid.ker fun x =>
    match x with
    | .a => false
    | .b => false
    | .c => true

def threePairAC : Setoid ThreeLoop :=
  Setoid.ker fun x =>
    match x with
    | .a => false
    | .b => true
    | .c => false

def threePairBC : Setoid ThreeLoop :=
  Setoid.ker fun x =>
    match x with
    | .a => true
    | .b => false
    | .c => false

/-- The five partitions of a three-element carrier, each a reading. -/
theorem three_five_readings :
    step threeEdge ⊥ = ⊥ ∧
      step threeEdge threePairAB = threePairAB ∧
        step threeEdge threePairAC = threePairAC ∧
          step threeEdge threePairBC = threePairBC ∧
            step threeEdge ⊤ = ⊤ :=
  ⟨three_every_reading _, three_every_reading _, three_every_reading _,
    three_every_reading _, three_every_reading _⟩

theorem three_partition_table :
    ¬ (⊥ : Setoid ThreeLoop) .a .b ∧
      threePairAB .a .b ∧ ¬ threePairAB .a .c ∧
        threePairAC .a .c ∧ ¬ threePairAC .a .b ∧
          threePairBC .b .c ∧ ¬ threePairBC .a .b ∧
            (⊤ : Setoid ThreeLoop) .a .b := by
  change ¬ (ThreeLoop.a = ThreeLoop.b) ∧
    (false = false) ∧ ¬ (false = true) ∧
    (false = false) ∧ ¬ (false = true) ∧
    (false = false) ∧ ¬ (true = false) ∧ True
  decide

theorem three_matrixLfp_diag (x y : ThreeLoop) :
    matrixLfp threeElems threeEdgeB x y = decide (x = y) := by
  cases x <;> cases y <;> decide

theorem three_lfp_iff_eq (x y : ThreeLoop) : (step threeEdge).lfp x y ↔ x = y := by
  rw [← matrixLfp_iff_lfp threeElems three_complete threeEdge threeEdgeB threeEdgeB_iff]
  rw [three_matrixLfp_diag, decide_eq_true_eq]

theorem three_gfp_total (x y : ThreeLoop) : (step threeEdge).gfp x y := by
  have htop : (⊤ : Setoid ThreeLoop) ≤ (step threeEdge).gfp :=
    (step threeEdge).le_gfp (three_every_reading ⊤).symm.le
  exact htop (by simp [Setoid.top_def])

end Mettapedia.SetTheory.AntiFoundation
