import FourColor.Chromogram
import Mathlib.Data.List.Forall2

/-!
# Joint trace differences for a shared chromogram

The matching syntax records which changes at the boundary must be made
simultaneously. These laws are independent of boundary length and retain the
same chromogram for both complete traces.
-/

namespace FourColor.KempeMatchingChromogram

open Color

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

end FourColor.KempeMatchingChromogram
