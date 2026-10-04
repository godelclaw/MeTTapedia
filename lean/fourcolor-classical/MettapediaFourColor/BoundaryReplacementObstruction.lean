import MettapediaFourColor.NearLinearDiamondData
import Mathlib.Tactic.FinCases

/-!
# Noncrossing boundary constraints do not replace the six-port diamond

For every feasible conjunction of equalities and inequalities on noncrossing
diagonals of the six-port boundary, another proper boundary colouring satisfies
the same conjunction but does not extend into D0000. Thus no such conjunction
can ensure fixed-boundary reconstruction. The statement includes mixtures of
identifications and added edges. It does not exclude choosing or recolouring
a compatible exterior, larger replacement gadgets, or other reductions.

The exact source graph is the decoded MIT-licensed D0000 from Yuta Inoue's
catalogue, inherited from NearLinearDiamondData. The finite checks concern
nine possible diagonals, fourteen covering triangulations, and fifteen short
nonextension witnesses; no Kempe repair table is used.
-/

namespace FourColor.BoundaryReplacementObstruction

open SimpleGraph NearLinearDiamondData

set_option maxRecDepth 32768

abbrev Palette := Fin 4
abbrev Word := Fin 6 → Palette

def diagonals : Fin 9 → Fin 6 × Fin 6 :=
  ![(0,2),(0,3),(0,4),(1,3),(1,4),(1,5),(2,4),(2,5),(3,5)]

def crosses (a b : Fin 9) : Prop :=
  let (u,v) := diagonals a
  let (x,y) := diagonals b
  (u < x ∧ x < v ∧ v < y) ∨ (x < u ∧ u < y ∧ y < v)

instance (a b : Fin 9) : Decidable (crosses a b) := by unfold crosses; infer_instance

def triangulation : Fin 14 → Finset (Fin 9) :=
  ![{5,7,8},{5,6,7},{3,5,8},{4,5,6},{3,4,5},{0,7,8},{0,6,7},
    {1,3,8},{0,1,8},{2,4,6},{2,3,4},{0,2,6},{1,2,3},{0,1,2}]

/-- Every noncrossing diagonal set is covered; no maximality assumption is
needed from a proposed replacement. -/
theorem diagonal_cover (s : Finset (Fin 9))
    (plane : ∀ a ∈ s, ∀ b ∈ s, ¬ crosses a b) :
    ∃ t : Fin 14, s ⊆ triangulation t := by
  have checked : ∀ (a b c d e f g h i : Bool),
      let selected : Fin 9 → Bool := ![a,b,c,d,e,f,g,h,i]
      (∀ x, selected x = true → ∀ y, selected y = true → ¬ crosses x y) →
      ∃ t : Fin 14, ∀ x, selected x = true → x ∈ triangulation t := by
    decide +kernel
  have eq : ![decide (0 ∈ s), decide (1 ∈ s), decide (2 ∈ s),
      decide (3 ∈ s), decide (4 ∈ s), decide (5 ∈ s), decide (6 ∈ s),
      decide (7 ∈ s), decide (8 ∈ s)] = fun x : Fin 9 => decide (x ∈ s) := by
    funext x; fin_cases x <;> rfl
  have hc := checked (decide (0 ∈ s)) (decide (1 ∈ s)) (decide (2 ∈ s))
    (decide (3 ∈ s)) (decide (4 ∈ s)) (decide (5 ∈ s)) (decide (6 ∈ s))
    (decide (7 ∈ s)) (decide (8 ∈ s))
  dsimp only at hc
  rw [eq] at hc
  obtain ⟨t, ht⟩ := hc (fun x hx y hy => plane x (of_decide_eq_true hx) y
    (of_decide_eq_true hy))
  exact ⟨t, fun x hx => ht x (decide_eq_true hx)⟩

def wordData : String :=
  "010101010123010201010203010213012012012013012032012121012131012132012302012303012312012313"

def badWord (i : Fin 15) (j : Fin 6) : Palette :=
  ⟨((wordData.toUTF8[(6 * i.val + j.val)]?.getD 48).toNat - 48) % 4,
    Nat.mod_lt _ (by decide)⟩

def ringProper (w : Word) : Prop := ∀ i : Fin 6,
  w i ≠ w ⟨(i.val + 1) % 6, Nat.mod_lt _ (by decide)⟩

instance (w : Word) : Decidable (ringProper w) := by unfold ringProper; infer_instance

def sameDiagonal (w z : Word) (e : Fin 9) : Prop :=
  (w (diagonals e).1 = w (diagonals e).2) ↔
    (z (diagonals e).1 = z (diagonals e).2)

instance (w z : Word) (e : Fin 9) : Decidable (sameDiagonal w z e) := by
  unfold sameDiagonal; infer_instance

def sourceEdges : List (Fin 10 × Fin 10) :=
  [(0,1),(0,5),(0,8),(1,2),(1,7),(1,8),(2,3),(2,6),(2,7),(3,4),(3,6),
   (4,5),(4,6),(4,9),(5,8),(5,9),(6,7),(6,9),(7,8),(7,9),(8,9)]

theorem source_edges : ∀ e ∈ sourceEdges, input0000.graph.Adj e.1 e.2 := by
  decide +kernel

def fill (w : Word) (a b c d : Palette) (v : Fin 10) : Palette :=
  if h : v.val < 6 then w ⟨v.val, h⟩ else
    if v = 6 then a else if v = 7 then b else if v = 8 then c else d

theorem nonextension_checked : ∀ (i : Fin 15) (a b c d : Palette),
    sourceEdges.all (fun e => decide
      (fill (badWord i) a b c d e.1 ≠ fill (badWord i) a b c d e.2)) = false := by
  decide +kernel

/-- The obstruction concerns actual colourings of the decoded source. -/
theorem no_extension (i : Fin 15) (C : input0000.graph.Coloring Palette)
    (boundary : ∀ x : Fin 6, C (x.castAdd 4) = badWord i x) : False := by
  have values (v : Fin 10) : C v = fill (badWord i) (C 6) (C 7) (C 8) (C 9) v := by
    unfold fill
    split
    next h => exact boundary ⟨v.val, h⟩
    next h => fin_cases v <;> simp_all
  have valid : sourceEdges.all (fun e => decide
      (fill (badWord i) (C 6) (C 7) (C 8) (C 9) e.1 ≠
        fill (badWord i) (C 6) (C 7) (C 8) (C 9) e.2)) = true := by
    apply List.all_eq_true.mpr
    intro e he
    apply decide_eq_true
    rw [← values e.1, ← values e.2]
    exact C.valid (source_edges e he)
  rw [nonextension_checked] at valid
  contradiction

/-- Palette symmetry fixes the first two neighbouring colours. -/
theorem normalize (w : Word) (proper : ringProper w) :
    ∃ p : Equiv.Perm Palette, p (w 0) = 0 ∧ p (w 1) = 1 := by
  let q := Equiv.swap (w 0) (0 : Palette)
  have q0 : q (w 0) = 0 := Equiv.swap_apply_left _ _
  have ne : q (w 1) ≠ 0 := by
    rw [← q0]
    exact q.injective.ne (proper 0).symm
  refine ⟨q.trans (Equiv.swap (q (w 1)) 1), ?_, ?_⟩
  · change Equiv.swap (q (w 1)) 1 (q (w 0)) = 0
    rw [q0]
    exact Equiv.swap_apply_of_ne_of_ne ne.symm (by decide)
  · exact Equiv.swap_apply_left _ _

theorem signatures_checked : ∀ (t : Fin 14) (c d e f : Palette),
    ringProper ![0,1,c,d,e,f] →
    ∃ i : Fin 15, ringProper (badWord i) ∧
      ∀ j ∈ triangulation t, sameDiagonal ![0,1,c,d,e,f] (badWord i) j := by
  decide +kernel

theorem same_signature (t : Fin 14) (w : Word) (proper : ringProper w) :
    ∃ i : Fin 15, ringProper (badWord i) ∧
      ∀ j ∈ triangulation t, sameDiagonal w (badWord i) j := by
  obtain ⟨p, h0, h1⟩ := normalize w proper
  let z : Word := fun x => p (w x)
  have hz : ringProper z := fun x => p.injective.ne (proper x)
  have eq : ![0,1,z 2,z 3,z 4,z 5] = z := by
    funext x
    fin_cases x <;> simp [z, h0, h1]
  have hs := signatures_checked t (z 2) (z 3) (z 4) (z 5) (eq.symm ▸ hz)
  rw [eq] at hs
  obtain ⟨i, hi, hs⟩ := hs
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact (p.injective.eq_iff.symm).trans (hs j hj)

/-- Every feasible noncrossing mixture of equalities and inequalities admits
a boundary colouring that defeats fixed-boundary reconstruction. -/
theorem obstruction (equal different : Finset (Fin 9))
    (plane : ∀ a ∈ equal ∪ different, ∀ b ∈ equal ∪ different, ¬ crosses a b)
    (start : Word) (proper : ringProper start)
    (heq : ∀ e ∈ equal, start (diagonals e).1 = start (diagonals e).2)
    (hne : ∀ e ∈ different, start (diagonals e).1 ≠ start (diagonals e).2) :
    ∃ w : Word, ringProper w ∧
      (∀ e ∈ equal, w (diagonals e).1 = w (diagonals e).2) ∧
      (∀ e ∈ different, w (diagonals e).1 ≠ w (diagonals e).2) ∧
      ¬ ∃ C : input0000.graph.Coloring Palette, ∀ x : Fin 6, C (x.castAdd 4) = w x := by
  obtain ⟨t, covers⟩ := diagonal_cover (equal ∪ different) plane
  obtain ⟨i, hi, agrees⟩ := same_signature t start proper
  refine ⟨badWord i, hi, ?_, ?_, ?_⟩
  · intro e he
    exact (agrees e (covers (Finset.mem_union_left _ he))).mp (heq e he)
  · intro e he h
    exact hne e he ((agrees e (covers (Finset.mem_union_right _ he))).mpr h)
  · rintro ⟨C, h⟩
    exact no_extension i C h

end FourColor.BoundaryReplacementObstruction
