import Mettapedia.GraphTheory.FourColor.GoertzelV24HexCycleBoundarySupport

/-!
# A literal six-port hexagonal cell

The recurrence in `GoertzelV24HexCycleBoundarySupport` is connected here to an
actual `PortTangle`: six cycle vertices, six cycle edges, and one boundary port
at every vertex.  The main theorem identifies a proper colouring of this
literal tangle with the six cyclic Klein-group equations.  Consequently its
physical boundary support is exactly the previously checked 63-word support.

This is a local semantic theorem.  It neither constructs a smaller replacement
nor claims a two-dimensional wall reduction.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24HexCellPortTangle

open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24RawNooseCountPumping
open GoertzelV24HexCycleBoundarySupport

/-- Cyclic successor on the six cycle positions. -/
def hexSucc (i : Fin 6) : Fin 6 := i + 1

@[simp] theorem hexPred_hexSucc (i : Fin 6) : hexPred (hexSucc i) = i := by
  fin_cases i <;> rfl

@[simp] theorem hexSucc_hexPred (i : Fin 6) : hexSucc (hexPred i) = i := by
  fin_cases i <;> rfl

/-- The vertex carrying a cycle dart.  The `false` half of edge `i` lies at
vertex `i`; its `true` half lies at the successor vertex. -/
def hexInteriorVert : Fin 6 × Bool → Fin 6
  | (i, false) => i
  | (i, true) => hexSucc i

/-- Pair the two halves of every cycle edge. -/
def hexAlpha : Fin 6 × Bool → Fin 6 × Bool
  | (i, false) => (i, true)
  | (i, true) => (i, false)

/-- The literal hexagonal cycle with one dangling port at every vertex. -/
def hexPortTangle : PortTangle (Fin 6) (Fin 6 × Bool) (Fin 6) where
  vert
    | Sum.inl d => hexInteriorVert d
    | Sum.inr p => p
  alpha := hexAlpha
  alpha_involutive := by rintro ⟨i, b⟩; cases b <;> rfl
  alpha_fixfree := by rintro ⟨i, b⟩; cases b <;> simp [hexAlpha]
  no_self_loops := by
    rintro ⟨i, b⟩
    cases b <;> fin_cases i <;> decide

@[simp] theorem hexPortTangle_vert_out (i : Fin 6) :
    hexPortTangle.vert (Sum.inl (i, false)) = i := rfl

@[simp] theorem hexPortTangle_vert_in (i : Fin 6) :
    hexPortTangle.vert (Sum.inl (i, true)) = hexSucc i := rfl

@[simp] theorem hexPortTangle_vert_port (i : Fin 6) :
    hexPortTangle.vert (Sum.inr i) = i := rfl

@[simp] theorem hexPortTangle_alpha_out (i : Fin 6) :
    hexPortTangle.alpha (i, false) = (i, true) := rfl

@[simp] theorem hexPortTangle_alpha_in (i : Fin 6) :
    hexPortTangle.alpha (i, true) = (i, false) := rfl

/-- For three nonzero Klein colours, pairwise distinctness is equivalent to the
local Tait flow equation. -/
theorem pairwise_ne_iff_sum_eq_zero_of_ne_zero
    {a b c : Color} (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    (a ≠ b ∧ a ≠ c ∧ b ≠ c) ↔ a + b + c = 0 := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl <;>
      rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero c hc with rfl | rfl | rfl <;>
        decide

/-- Edge-colour form of extension across the hexagonal cell. -/
def HexCycleExtends (word : CutWord (Fin 6)) : Prop :=
  ∃ edgeColor : Fin 6 → TaitColor, ∀ i,
    (edgeColor (hexPred i)).1 + (word i).1 + (edgeColor i).1 = 0

/-- Restrict a literal proper colouring to its six cycle-edge colours. -/
theorem hexCycleExtends_of_col {word : CutWord (Fin 6)}
    (c : Col hexPortTangle (liftWord word)) : HexCycleExtends word := by
  let edgeColor : Fin 6 → TaitColor := fun i =>
    ⟨c.1.color (Sum.inl (i, false)), c.2.1.1 _⟩
  refine ⟨edgeColor, ?_⟩
  intro i
  have hinvariant :
      c.1.color (Sum.inl (hexPred i, true)) =
        c.1.color (Sum.inl (hexPred i, false)) := by
    simpa using c.1.invariant (hexPred i, false)
  have hport : c.1.color (Sum.inr i) = (word i).1 := congrFun c.2.2 i
  have hpair :
      c.1.color (Sum.inl (hexPred i, true)) ≠ c.1.color (Sum.inr i) ∧
        c.1.color (Sum.inl (hexPred i, true)) ≠
          c.1.color (Sum.inl (i, false)) ∧
        c.1.color (Sum.inr i) ≠ c.1.color (Sum.inl (i, false)) := by
    constructor
    · apply c.2.1.2
      · simp
      · simp
    constructor
    · apply c.2.1.2
      · simp
      · simp
    · apply c.2.1.2
      · simp
      · simp
  have hsum := (pairwise_ne_iff_sum_eq_zero_of_ne_zero
    (c.2.1.1 (Sum.inl (hexPred i, true)))
    (c.2.1.1 (Sum.inr i))
    (c.2.1.1 (Sum.inl (i, false)))).1 hpair
  simpa [edgeColor, hinvariant, hport] using hsum

/-- Build a literal tangle colouring from six cycle-edge colours. -/
def hexColoringOfEdges (word : CutWord (Fin 6))
    (edgeColor : Fin 6 → TaitColor) : Coloring hexPortTangle where
  color
    | Sum.inl (i, _) => (edgeColor i).1
    | Sum.inr p => (word p).1
  invariant := by rintro ⟨i, b⟩; cases b <;> rfl

@[simp] theorem hexColoringOfEdges_color_out
    (word : CutWord (Fin 6)) (edgeColor : Fin 6 → TaitColor) (i : Fin 6) :
    (hexColoringOfEdges word edgeColor).color (Sum.inl (i, false)) = (edgeColor i).1 := rfl

@[simp] theorem hexColoringOfEdges_color_in
    (word : CutWord (Fin 6)) (edgeColor : Fin 6 → TaitColor) (i : Fin 6) :
    (hexColoringOfEdges word edgeColor).color (Sum.inl (i, true)) = (edgeColor i).1 := rfl

@[simp] theorem hexColoringOfEdges_color_port
    (word : CutWord (Fin 6)) (edgeColor : Fin 6 → TaitColor) (i : Fin 6) :
    (hexColoringOfEdges word edgeColor).color (Sum.inr i) = (word i).1 := rfl

theorem localPairwise_of_cycleEquation
    {word : CutWord (Fin 6)} {edgeColor : Fin 6 → TaitColor}
    (hcycle : ∀ i,
      (edgeColor (hexPred i)).1 + (word i).1 + (edgeColor i).1 = 0)
    (i : Fin 6) :
    (edgeColor (hexPred i)).1 ≠ (word i).1 ∧
      (edgeColor (hexPred i)).1 ≠ (edgeColor i).1 ∧
      (word i).1 ≠ (edgeColor i).1 := by
  exact (pairwise_ne_iff_sum_eq_zero_of_ne_zero
    (edgeColor (hexPred i)).2 (word i).2 (edgeColor i).2).2 (hcycle i)

theorem hexSucc_injective : Function.Injective hexSucc := by
  intro i j hij
  rw [← hexPred_hexSucc i, ← hexPred_hexSucc j, hij]

theorem hexColoringOfEdges_isProper
    {word : CutWord (Fin 6)} {edgeColor : Fin 6 → TaitColor}
    (hcycle : ∀ i,
      (edgeColor (hexPred i)).1 + (word i).1 + (edgeColor i).1 = 0) :
    IsProper (hexColoringOfEdges word edgeColor) := by
  constructor
  · rintro (⟨i, b⟩ | p)
    · exact (edgeColor i).2
    · exact (word p).2
  · intro d e hvert hne
    rcases d with ⟨i, bi⟩ | p <;> rcases e with ⟨j, bj⟩ | q
    · cases bi <;> cases bj
      · simp only [hexPortTangle_vert_out] at hvert
        subst j
        exact (hne rfl).elim
      · simp only [hexPortTangle_vert_out, hexPortTangle_vert_in] at hvert
        have hj : j = hexPred i := by
          calc
            j = hexPred (hexSucc j) := (hexPred_hexSucc j).symm
            _ = hexPred i := congrArg hexPred hvert.symm
        subst j
        exact (localPairwise_of_cycleEquation hcycle i).2.1.symm
      · simp only [hexPortTangle_vert_in, hexPortTangle_vert_out] at hvert
        have hi : i = hexPred j := by
          calc
            i = hexPred (hexSucc i) := (hexPred_hexSucc i).symm
            _ = hexPred j := congrArg hexPred hvert
        subst i
        exact (localPairwise_of_cycleEquation hcycle j).2.1
      · simp only [hexPortTangle_vert_in] at hvert
        have hij : i = j := hexSucc_injective hvert
        subst j
        exact (hne rfl).elim
    · cases bi
      · simp only [hexPortTangle_vert_out, hexPortTangle_vert_port] at hvert
        subst q
        exact (localPairwise_of_cycleEquation hcycle i).2.2.symm
      · simp only [hexPortTangle_vert_in, hexPortTangle_vert_port] at hvert
        subst q
        simpa using (localPairwise_of_cycleEquation hcycle (hexSucc i)).1
    · cases bj
      · simp only [hexPortTangle_vert_port, hexPortTangle_vert_out] at hvert
        subst p
        exact (localPairwise_of_cycleEquation hcycle j).2.2
      · simp only [hexPortTangle_vert_port, hexPortTangle_vert_in] at hvert
        subst p
        simpa using (localPairwise_of_cycleEquation hcycle (hexSucc j)).1.symm
    · simp only [hexPortTangle_vert_port] at hvert
      subst q
      exact (hne rfl).elim

/-- The edge equations construct a proper colouring of the literal tangle. -/
theorem col_of_hexCycleExtends {word : CutWord (Fin 6)}
    (h : HexCycleExtends word) : Nonempty (Col hexPortTangle (liftWord word)) := by
  rcases h with ⟨edgeColor, hcycle⟩
  refine ⟨⟨hexColoringOfEdges word edgeColor,
    hexColoringOfEdges_isProper hcycle, ?_⟩⟩
  rfl

/-- Literal proper colourings are exactly the six cyclic edge equations. -/
theorem nonempty_col_hexPortTangle_iff_cycleExtends (word : CutWord (Fin 6)) :
    Nonempty (Col hexPortTangle (liftWord word)) ↔ HexCycleExtends word := by
  constructor
  · rintro ⟨c⟩
    exact hexCycleExtends_of_col c
  · exact col_of_hexCycleExtends

theorem eq_add_of_add_add_eq_zero {a b c : Color} (h : a + b + c = 0) :
    c = a + b := by
  calc
    c = 0 + c := by simp
    _ = (a + b + c) + c := by rw [h]
    _ = a + b := by simp [add_assoc]

/-- The explicit start recurrence and the six edge equations are equivalent. -/
theorem hexBoundaryRealizable_iff_cycleExtends (word : CutWord (Fin 6)) :
    HexBoundaryRealizable word ↔ HexCycleExtends word := by
  constructor
  · rintro ⟨start, h⟩
    let edgeColor : Fin 6 → TaitColor := fun i =>
      ⟨hexEdgeFromStart word start.1 i, (h i).1⟩
    refine ⟨edgeColor, ?_⟩
    intro i
    exact (h i).2
  · rintro ⟨edgeColor, hcycle⟩
    let start : TaitColor := edgeColor 5
    have h0 : (edgeColor 0).1 = (edgeColor 5).1 + (word 0).1 :=
      eq_add_of_add_add_eq_zero (hcycle 0)
    have h1 : (edgeColor 1).1 = (edgeColor 0).1 + (word 1).1 :=
      eq_add_of_add_add_eq_zero (hcycle 1)
    have h2 : (edgeColor 2).1 = (edgeColor 1).1 + (word 2).1 :=
      eq_add_of_add_add_eq_zero (hcycle 2)
    have h3 : (edgeColor 3).1 = (edgeColor 2).1 + (word 3).1 :=
      eq_add_of_add_add_eq_zero (hcycle 3)
    have h4 : (edgeColor 4).1 = (edgeColor 3).1 + (word 4).1 :=
      eq_add_of_add_add_eq_zero (hcycle 4)
    have hedge : ∀ i, hexEdgeFromStart word start.1 i = (edgeColor i).1 := by
      intro i
      fin_cases i <;> simp [hexEdgeFromStart, start, h0, h1, h2, h3, h4]
    refine ⟨start, ?_⟩
    intro i
    constructor
    · rw [hedge i]
      exact (edgeColor i).2
    · simpa only [hedge] using hcycle i

/-- **Physical recurrence theorem.**  The executable recurrence accepts a word
exactly when the literal hexagonal port tangle has a proper colouring with that
boundary word. -/
theorem nonempty_col_hexPortTangle_iff (word : CutWord (Fin 6)) :
    Nonempty (Col hexPortTangle (liftWord word)) ↔ HexBoundaryRealizable word := by
  rw [nonempty_col_hexPortTangle_iff_cycleExtends,
    hexBoundaryRealizable_iff_cycleExtends]

/-- The physical support, represented by the already checked recurrence set. -/
def hexPortSupport : Finset (CutWord (Fin 6)) := hexCycleSupport

/-- Membership in `hexPortSupport` is literal physical realizability. -/
theorem mem_hexPortSupport_iff (word : CutWord (Fin 6)) :
    word ∈ hexPortSupport ↔ Nonempty (Col hexPortTangle (liftWord word)) := by
  rw [hexPortSupport, mem_hexCycleSupport_iff, nonempty_col_hexPortTangle_iff]

/-- **Exact physical census.**  The six-port hexagonal cell realizes precisely
63 boundary words. -/
theorem card_hexPortSupport : hexPortSupport.card = 63 := card_hexCycleSupport

end GoertzelV24HexCellPortTangle

end Mettapedia.GraphTheory.FourColor
