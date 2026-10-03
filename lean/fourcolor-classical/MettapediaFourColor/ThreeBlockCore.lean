import MettapediaFourColor.FiveTriangleCollapseObstruction

/-!
# Three boundary choices determine extension into D0092

For the displayed boundary class, the three runs using colours zero and
two may be switched independently only when the exterior separates them.
The source core extends exactly when the first two choices agree and the
third differs. Necessity follows by forcing core colours along their
actual source edges. Sufficiency supplies the complete source colouring.
No exterior separation or availability of a useful preparation is assumed
by the core calculation, or proved by it.

The decoded source and attribution are inherited from
`FiveTriangleCollapseObstruction`.
-/

namespace FourColor.ThreeBlockCore

open Color FiveTriangleCollapseObstruction

def bitColour (b : Bool) : Color := if b then c2 else c0

def word (a b c : Bool) : Fin 11 → Color :=
  ![c1,c3,bitColour (!a),c3,c1,bitColour b,c3,
    bitColour c,bitColour (!c),bitColour c,bitColour (!c)]

private theorem remaining (p : Bool) (x : Color)
    (h1 : x ≠ c1) (h3 : x ≠ c3) (hp : x ≠ bitColour p) :
    x = bitColour (!p) := by
  revert h1 h3 hp
  cases p <;> cases x <;> decide

private theorem only_one (p : Bool) (x : Color)
    (h0 : x ≠ bitColour p) (h2 : x ≠ bitColour (!p)) (h3 : x ≠ c3) :
    x = c1 := by
  revert h0 h2 h3
  cases p <;> cases x <;> decide

private theorem only_three (p : Bool) (x : Color)
    (h0 : x ≠ bitColour p) (h2 : x ≠ bitColour (!p)) (h1 : x ≠ c1) :
    x = c3 := by
  revert h0 h2 h1
  cases p <;> cases x <;> decide

/-- These two inequalities encode the entire remaining compatibility check. -/
private theorem choices_of_ne (a b c : Bool)
    (ha : bitColour (!c) ≠ bitColour (!a))
    (hb : bitColour (!c) ≠ bitColour (!b)) : a = b ∧ b ≠ c := by
  revert ha hb
  cases a <;> cases b <;> cases c <;> decide

/-- Every extension forces the two independent boundary choices to agree. -/
theorem necessary (a b c : Bool) (C : upper.graph.Coloring Color)
    (boundary : ∀ j : Fin 11, C (j.castAdd 7) = word a b c j) :
    a = b ∧ b ≠ c := by
  have edge (u v : Fin 18) (h : upper.graph.Adj u v) : C u ≠ C v := C.valid h
  have b0 := boundary 0
  have b1 := boundary 1
  have b2 := boundary 2
  have b3 := boundary 3
  have b4 := boundary 4
  have b5 := boundary 5
  have b6 := boundary 6
  have b7 := boundary 7
  have b8 := boundary 8
  have b10 := boundary 10
  change C 0 = c1 at b0
  change C 1 = c3 at b1
  change C 2 = bitColour (!a) at b2
  change C 3 = c3 at b3
  change C 4 = c1 at b4
  change C 5 = bitColour b at b5
  change C 6 = c3 at b6
  change C 7 = bitColour c at b7
  change C 8 = bitColour (!c) at b8
  change C 10 = bitColour (!c) at b10
  have k17 : C 17 = bitColour c := by
    have h := remaining (!c) (C 17)
      (b0 ▸ edge 17 0 (by decide +kernel))
      (b1 ▸ edge 17 1 (by decide +kernel))
      (b10 ▸ edge 17 10 (by decide +kernel))
    simpa using h
  have k12 : C 12 = bitColour (!b) := remaining b (C 12)
    (b4 ▸ edge 12 4 (by decide +kernel))
    (b3 ▸ edge 12 3 (by decide +kernel))
    (b5 ▸ edge 12 5 (by decide +kernel))
  have k13 : C 13 = c1 := only_one b (C 13)
    (b5 ▸ edge 13 5 (by decide +kernel))
    (k12 ▸ edge 13 12 (by decide +kernel))
    (b6 ▸ edge 13 6 (by decide +kernel))
  have k14 : C 14 = c3 := only_three c (C 14)
    (b7 ▸ edge 14 7 (by decide +kernel))
    (b8 ▸ edge 14 8 (by decide +kernel))
    (k13 ▸ edge 14 13 (by decide +kernel))
  have k11 : C 11 = c1 := only_one c (C 11)
    (k17 ▸ edge 11 17 (by decide +kernel))
    (b8 ▸ edge 11 8 (by decide +kernel))
    (k14 ▸ edge 11 14 (by decide +kernel))
  have k15 : C 15 = bitColour (!c) := remaining c (C 15)
    (k11 ▸ edge 15 11 (by decide +kernel))
    (b1 ▸ edge 15 1 (by decide +kernel))
    (k17 ▸ edge 15 17 (by decide +kernel))
  exact choices_of_ne a b c
    (k15 ▸ b2 ▸ edge 15 2 (by decide +kernel))
    (k15 ▸ k12 ▸ edge 15 12 (by decide +kernel))

def assignment (a b c : Bool) (v : Fin 18) : Color :=
  if h : v.val < 11 then word a b c ⟨v.val, h⟩
  else (![c1,bitColour (!b),c1,c3,bitColour (!c),c3,bitColour c] : Fin 7 → Color)
    ⟨v.val - 11, by omega⟩

/-- Check only the edges of the symbolic witness, over three Boolean choices. -/
theorem assignment_proper : ∀ a b c, a = b → b ≠ c →
    ∀ u v, upper.graph.Adj u v → assignment a b c u ≠ assignment a b c v := by
  decide +kernel

def colouring (a b c : Bool) (hab : a = b) (hbc : b ≠ c) : upper.graph.Coloring Color :=
  .mk (assignment a b c) (fun h => assignment_proper a b c hab hbc _ _ h)

theorem colouring_boundary (a b c : Bool) (hab : a = b) (hbc : b ≠ c) (j : Fin 11) :
    colouring a b c hab hbc (j.castAdd 7) = word a b c j := by
  change assignment a b c (j.castAdd 7) = _
  simp [assignment, j.isLt]

/-- An exact reconstruction criterion, not a count of possible core colourings. -/
theorem extension_iff (a b c : Bool) :
    (∃ C : upper.graph.Coloring Color,
      ∀ j : Fin 11, C (j.castAdd 7) = word a b c j) ↔ a = b ∧ b ≠ c := by
  constructor
  · rintro ⟨C, hC⟩
    exact necessary a b c C hC
  · rintro ⟨hab, hbc⟩
    exact ⟨colouring a b c hab hbc, colouring_boundary a b c hab hbc⟩

/-- A physical component may impose the same switch choice on several runs.
The third run can take the required opposite choice precisely when its
component is distinct from both others. The first two may share a component. -/
theorem component_choices_iff {ι : Type*} [DecidableEq ι] (A B C : ι) :
    (∃ choose : ι → Bool, ∃ k : upper.graph.Coloring Color,
      ∀ j : Fin 11, k (j.castAdd 7) = word (choose A) (choose B) (choose C) j) ↔
      A ≠ C ∧ B ≠ C := by
  constructor
  · rintro ⟨choose, k, hk⟩
    obtain ⟨hab, hbc⟩ := necessary _ _ _ k hk
    constructor
    · intro h
      apply hbc
      rw [← hab, h]
    · intro h
      exact hbc (congrArg choose h)
  · rintro ⟨hac, hbc⟩
    let choose : ι → Bool := fun x => decide (x = C)
    have ha : choose A = false := by simp [choose, hac]
    have hb : choose B = false := by simp [choose, hbc]
    have hc : choose C = true := by simp [choose]
    refine ⟨choose, colouring (choose A) (choose B) (choose C)
      (ha.trans hb.symm) (by simp [hb, hc]), ?_⟩
    exact colouring_boundary _ _ _ _ _

end FourColor.ThreeBlockCore
