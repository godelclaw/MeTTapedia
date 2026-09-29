import FourColor.Chromogram
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-!
# Exact translation of six-port component matchings

A noncrossing component matching retains which boundary changes must be made
together. Its chromogram records the same joint choices, including the parity
of the two endpoint colours. The difference of two matching traces selects a
union of complete components.

The trace-difference theorem is independent of interface width. Only the
translation from six cyclic ports to a well-bracketed word is checked finitely.
-/

namespace FourColor.KempeMatchingChromogram

open Color

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

inductive Slot
  | fixed | opening | closing
  deriving DecidableEq, Repr

def shape : Chromogram → List Slot := List.map fun s =>
  match s with
  | .skip => .fixed
  | .push => .opening
  | .pop0 | .pop1 => .closing

/-- A full boundary mask fixes the unpaired ports and agrees at paired ends. -/
def paired : List Bool → List Bool → List Slot → Bool
  | stack, [], [] => stack.isEmpty
  | stack, b :: bs, .fixed :: ss => !b && paired stack bs ss
  | stack, b :: bs, .opening :: ss => paired (b :: stack) bs ss
  | a :: stack, b :: bs, .closing :: ss => (a == b) && paired stack bs ss
  | _, _, _ => false

def difference (et et' : List Color) : List Bool :=
  List.zipWith (fun a b => decide (a ≠ b)) et et'

/-- Shared chromogram witnesses force changes at the two ends of each chord
to agree. This statement retains both complete traces and their common word. -/
theorem difference_paired : ∀ (w : Chromogram) (et et' : List Color)
    (stack stack' : List Bool), matchg stack et w → matchg stack' et' w →
    paired (List.zipWith xor stack stack') (difference et et') (shape w) := by
  intro w
  induction w with
  | nil =>
    intro et et' stack stack' h h'
    cases et <;> cases et' <;> cases stack <;> cases stack' <;>
      simp_all [matchg, paired, difference, shape]
  | cons s w ih =>
    intro et et' stack stack' h h'
    cases et with
    | nil => simp at h
    | cons a et =>
      cases et' with
      | nil => simp at h'
      | cons b et' =>
        cases s with
        | skip =>
          cases a <;> cases b <;>
            simp only [matchg, matchStep, Option.elim, Bool.false_eq_true] at h h'
          simpa [paired, difference, shape] using ih et et' stack stack' h h'
        | push =>
          cases a <;> cases b <;>
            simp only [matchg, matchStep, Option.elim, Bool.false_eq_true] at h h'
          all_goals simpa [paired, difference, shape] using ih et et' _ _ h h'
        | pop0 =>
          cases stack with
          | nil => cases a <;> simp [matchg, matchStep] at h
          | cons c stack =>
            cases stack' with
            | nil => cases b <;> simp [matchg, matchStep] at h'
            | cons d stack' =>
              cases a <;> cases b <;> cases c <;> cases d <;>
                simp only [matchg, matchStep, Option.elim, Bool.false_eq_true] at h h'
              all_goals simpa [paired, difference, shape] using ih et et' stack stack' h h'
        | pop1 =>
          cases stack with
          | nil => cases a <;> simp [matchg, matchStep] at h
          | cons c stack =>
            cases stack' with
            | nil => cases b <;> simp [matchg, matchStep] at h'
            | cons d stack' =>
              cases a <;> cases b <;> cases c <;> cases d <;>
                simp only [matchg, matchStep, Option.elim, Bool.false_eq_true] at h h'
              all_goals simpa [paired, difference, shape] using ih et et' stack stack' h h'

/-- At each port a second matching trace either keeps the colour or exchanges
the two active colours. Which exchanges can coexist is governed by `paired`. -/
theorem matches_related : ∀ (w : Chromogram) (et et' : List Color)
    (stack stack' : List Bool), matchg stack et w → matchg stack' et' w →
    List.Forall₂ (fun a b => b = a ∨ b = EdgePerm.e132 a) et et' := by
  intro w
  induction w with
  | nil =>
    intro et et' stack stack' h h'
    cases et <;> cases et' <;> simp_all
  | cons s w ih =>
    intro et et' stack stack' h h'
    cases et with
    | nil => simp at h
    | cons a et =>
      cases et' with
      | nil => simp at h'
      | cons b et' =>
        have step {a b : Color} {s : GramSymbol} {u v : List Bool}
            (ha : matchStep a s stack = some u)
            (hb : matchStep b s stack' = some v) :
            b = a ∨ b = EdgePerm.e132 a := by
          cases a <;> cases b <;> cases s <;>
            simp_all [matchStep, EdgePerm.apply]
        cases hs : matchStep a s stack with
        | none => simp [matchg, hs] at h
        | some u =>
          cases hs' : matchStep b s stack' with
          | none => simp [matchg, hs'] at h'
          | some v =>
            exact .cons (step hs hs')
              (ih et et' u v (by simpa [matchg, hs] using h)
                (by simpa [matchg, hs'] using h'))

abbrev Ports := Fin 6

def Noncrossing (mate : Ports → Ports) : Prop :=
  ∀ i j, ¬ ((min i.val (mate i).val < min j.val (mate j).val ∧
    min j.val (mate j).val < max i.val (mate i).val ∧
    max i.val (mate i).val < max j.val (mate j).val) ∨
    (min j.val (mate j).val < min i.val (mate i).val ∧
    min i.val (mate i).val < max j.val (mate j).val ∧
    max j.val (mate j).val < max i.val (mate i).val))

instance (mate : Ports → Ports) : Decidable (Noncrossing mate) := by
  unfold Noncrossing
  infer_instance

def layout (mate : Ports → Ports) : List Slot :=
  List.ofFn fun i => if mate i = i then .fixed
    else if i < mate i then .opening else .closing

/-- All choices of the active colours, with inactive ports fixed to `c1`. -/
def word (mate : Ports → Ports) (bits : Ports → Bool) : Ports → Color :=
  fun i => if mate i = i then .c1 else if bits i then .c3 else .c2

def gram (mate : Ports → Ports) (c : Ports → Color) : Chromogram :=
  List.ofFn fun i => if mate i = i then .skip else if i < mate i then .push
    else if c i = c (mate i) then .pop0 else .pop1

theorem shape_gram (mate : Ports → Ports) (c : Ports → Color) :
    shape (gram mate c) = layout mate := by
  simp only [shape, gram, layout, List.map_ofFn]
  congr 1
  funext i
  by_cases h : mate i = i
  · simp [h]
  by_cases h' : i < mate i
  · simp [h, h']
  by_cases h'' : c i = c (mate i) <;> simp [h, h', h'']

private theorem finite_translation : ∀ a b c d e f : Ports,
    let mate : Ports → Ports := ![a, b, c, d, e, f]
    (∀ i, mate (mate i) = i) → Noncrossing mate →
    ∀ bits : Ports → Bool,
      matchg [] (List.ofFn (word mate bits)) (gram mate (word mate bits)) ∧
        (paired [] (List.ofFn bits) (layout mate) → ∀ i, bits i = bits (mate i)) := by
  decide +kernel

theorem translation (mate : Ports → Ports)
    (hinv : ∀ i, mate (mate i) = i) (hplanar : Noncrossing mate)
    (bits : Ports → Bool) :
    matchg [] (List.ofFn (word mate bits)) (gram mate (word mate bits)) ∧
      (paired [] (List.ofFn bits) (layout mate) → ∀ i, bits i = bits (mate i)) := by
  have h := finite_translation (mate 0) (mate 1) (mate 2) (mate 3) (mate 4) (mate 5)
  have hm : (![mate 0, mate 1, mate 2, mate 3, mate 4, mate 5] : Ports → Ports) = mate := by
    funext i
    fin_cases i <;> rfl
  rw [hm] at h
  exact h hinv hplanar bits

end FourColor.KempeMatchingChromogram
