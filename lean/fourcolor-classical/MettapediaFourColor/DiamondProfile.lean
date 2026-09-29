import MettapediaFourColor.DiamondBoundarySummary

/-! # Joint colour-availability profiles of the diamond core

The boundary determines four sets of available colours. Both tips use the
same pair of distinct centre colours. The profile retains these four sets
jointly, modulo colour renaming and exchanges of the centres or the tips.
Boundary length is retained separately because it affects the Kempe game.

The terminal test reconstructs an actual colouring through the common diamond
summary. It does not assert that every proper boundary assignment extends.
-/

namespace FourColor.DiamondProfile

open Color
open Mettapedia.GraphTheory.FourColor

abbrev Shape := Fin 3

def left (s : Shape) : ℕ := if s = 0 then 0 else 1
def right (s : Shape) : ℕ := if s = 2 then 1 else 0
def size (s : Shape) : ℕ := 6 + left s + right s

def colors : List Color := [c0, c1, c2, c3]

def boundary (s : Shape) (et : List Color) (v : Fin (size s)) : Color :=
  (untrace 0 et).getD v.val 0

instance (s : Shape) (b : Fin (size s) → Color) (i : Fin 4) (c : Color) :
    Decidable (DiamondBoundaryElimination.Allows
      (DiamondBoundarySummary.attachments (left s) (right s)) b i c) := by
  unfold DiamondBoundaryElimination.Allows
  change Decidable (∀ v : Fin (size s),
    DiamondBoundarySummary.attachments (left s) (right s) i v → c ≠ b v)
  letI : DecidablePred (fun v : Fin (size s) =>
      DiamondBoundarySummary.attachments (left s) (right s) i v → c ≠ b v) := fun v => by
        unfold DiamondBoundarySummary.attachments
        split <;> infer_instance
  infer_instance

def palette (s : Shape) (et : List Color) (i : Fin 4) (c : Color) : Bool :=
  decide (DiamondBoundaryElimination.Allows
    (DiamondBoundarySummary.attachments (left s) (right s)) (boundary s et) i c)

def role (swapCentres swapTips : Bool) (i : Fin 4) : Fin 4 :=
  match i.val with
  | 0 => if swapCentres then 2 else 0
  | 1 => if swapTips then 3 else 1
  | 2 => if swapCentres then 0 else 2
  | _ => if swapTips then 1 else 3

/-- Which of the four roles allow this colour? -/
def signature (p : Fin 4 → Color → Bool) (sc st : Bool) (c : Color) : ℕ :=
  ((List.finRange 4).map fun i => if p (role sc st i) c then 2 ^ i.val else 0).sum

/-- A structural insertion keeps the four-column encoding reducible in the kernel. -/
def insertColumn (d : ℕ) : List ℕ → List ℕ
  | [] => [d]
  | e :: es => if d ≤ e then d :: e :: es else e :: insertColumn d es

/-- Sorting the four colour columns forgets only their names. -/
def codeAt (p : Fin 4 → Color → Bool) (sc st : Bool) : ℕ :=
  ((colors.map (signature p sc st)).foldr insertColumn []).foldr
    (fun d rest => d + 16 * rest) 0

def code (p : Fin 4 → Color → Bool) : ℕ :=
  min (min (codeAt p false false) (codeAt p false true))
    (min (codeAt p true false) (codeAt p true true))

def key (s : Shape) (et : List Color) : ℕ :=
  65536 * (size s - 6) + code (palette s et)

def tipAllows (p : Fin 4 → Color → Bool) (i : Fin 4) (a b c : Color) : Bool :=
  p i c && decide (c ≠ a) && decide (c ≠ b)

/-- Choose centres jointly, then choose each tip from its remaining list. -/
def solve (p : Fin 4 → Color → Bool) : Fin 4 → Color :=
  let pair := ((colors.product colors).find? fun (a, b) =>
    p 0 a && p 2 b && decide (a ≠ b) &&
      colors.any (tipAllows p 1 a b) && colors.any (tipAllows p 3 a b)).getD (0, 0)
  let lower := (colors.find? (tipAllows p 1 pair.1 pair.2)).getD 0
  let upper := (colors.find? (tipAllows p 3 pair.1 pair.2)).getD 0
  fun i => match i.val with
    | 0 => pair.1 | 1 => lower | 2 => pair.2 | _ => upper

/-- Validate the proposed boundary and all four interior colours literally. -/
def good (s : Shape) (et : List Color) : Bool :=
  let b := boundary s et
  let k := solve (palette s et)
  decide (
    (∀ v w, (SimpleGraph.cycleGraph (size s)).Adj v w → b v ≠ b w) ∧
    (∀ i, DiamondBoundaryElimination.Allows
      (DiamondBoundarySummary.attachments (left s) (right s)) b i (k i)) ∧
    (∀ i j, DiamondBoundaryElimination.coreAdj i j → k i ≠ k j) ∧
    et = trace ((List.finRange (size s)).map b))

def Supports (s : Shape) (et : List Color) : Prop :=
  ∃ p : DiamondBoundarySummary.Plan (left s) (right s) Color,
    et = trace ((List.finRange (size s)).map p.1)

/-- Every accepted terminal has genuine boundary and interior witnesses. -/
theorem good_supports (s : Shape) (et : List Color) (h : good s et = true) :
    Supports s et := by
  unfold good at h
  have h := of_decide_eq_true h
  obtain ⟨hb, ha, hc, ht⟩ := h
  let b : (SimpleGraph.cycleGraph (size s)).Coloring Color :=
    .mk (boundary s et) (fun {_ _} edge => hb _ _ edge)
  let k := solve (palette s et)
  let summary : DiamondBoundaryElimination.Summary
      (DiamondBoundarySummary.attachments (left s) (right s)) b := {
    first := k 0
    second := k 2
    centres_ne := hc 0 2 (by decide)
    first_allowed := ha 0
    second_allowed := ha 2
    lower := ⟨k 1, ha 1, hc 1 0 (by decide), hc 1 2 (by decide)⟩
    upper := ⟨k 3, ha 3, hc 3 0 (by decide), hc 3 2 (by decide)⟩ }
  exact ⟨⟨b, summary⟩, ht⟩

end FourColor.DiamondProfile
