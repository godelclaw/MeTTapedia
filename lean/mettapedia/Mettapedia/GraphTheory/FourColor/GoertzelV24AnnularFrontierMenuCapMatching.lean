import Mettapedia.GraphTheory.FourColor.GoertzelV24AnnularFrontierMenuCapExtension
import Mettapedia.GraphTheory.FourColor.GoertzelDefinition48

/-!
# The restored cap pairing

With the pentagonal cap extension pinned down, the restored cap contributes a
definite pairing of the four active boundary positions.  This file supplies the
extension as a total function and proves the local degree facts that make that
pairing a perfect matching.

The arithmetic is entirely local.  At cap vertex `i` the boundary colour and the
two incident internal cap edges form a Tait triple, so they carry the three
colours once each.  Fix a colour pair `(p,q)` and call an internal cap edge
*selected* when its colour is `p` or `q`.

* If the boundary colour at `i` is `p` or `q`, the two internal colours are the
  remaining two, so **exactly one** of them is selected.
* If the boundary colour at `i` is the third colour, the two internal colours are
  `p` and `q`, so **both** are selected.

A good word has four active positions and one inactive one, so the selected cap
edges carry `4 · 1 + 1 · 2 = 6` endpoint incidences and there are three of them.
Three edges on the five cap positions with degrees `(2,1,1,1,1)` form a two-edge
path centred at the inactive position together with one disjoint edge — which is
exactly a perfect matching of the four active positions, one block joining the
inactive position's two neighbours and the other joining the remaining pair.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24AnnularFrontierMenuCapMatching

open GoertzelV24AnnularFrontierMenuCapExtension

variable {w : CAP5BoundaryWord} {x : CAP5InternalCycleColoring}

/-- The pentagonal cap extension as a total function of the boundary word.  It
is well defined precisely because the extension is unique. -/
noncomputable def capExtension (w : CAP5BoundaryWord) : CAP5InternalCycleColoring :=
  open Classical in
  if h : CAP5WordExtendsAcrossCycle w then h.choose else fun _ => 0

/-- On an extendable word the total function really is an extension. -/
theorem capExtension_spec (h : CAP5WordExtendsAcrossCycle w) :
    CAP5ExtendsAcrossCycleWith w (capExtension w) := by
  classical
  rw [capExtension, dif_pos h]
  exact h.choose_spec

/-- Any extension *is* the extension. -/
theorem capExtension_eq (hx : CAP5ExtendsAcrossCycleWith w x) :
    capExtension w = x :=
  unique (capExtension_spec ⟨x, hx⟩) hx

/-- Every good inner word has its cap extension. -/
theorem capExtension_spec_of_coloredBlock311
    (hgood : CAP5BoundaryWordHasColoredBlock311 w) :
    CAP5ExtendsAcrossCycleWith w (capExtension w) :=
  capExtension_spec (cap5_extendsAcrossCycle_of_coloredBlock311 hgood)

/-- An internal cap edge is selected when it carries one of the two chosen
colours. -/
def CapEdgeSelected (x : CAP5InternalCycleColoring) (p q : Color) (j : Fin 5) : Prop :=
  x j = p ∨ x j = q

instance (x : CAP5InternalCycleColoring) (p q : Color) (j : Fin 5) :
    Decidable (CapEdgeSelected x p q j) := by
  unfold CapEdgeSelected; infer_instance

set_option synthInstance.maxSize 4000 in
/-- **Exactly one selected cap edge at an active position.**  The boundary
colour already uses one of the pair, so the two internal colours are the other
one and the third colour. -/
theorem selected_xor_of_active {a b c p q : Color}
    (htriple : IsTaitColorTriple a b c) (hpair : ValidColorPair p q)
    (hactive : a = p ∨ a = q) :
    ((b = p ∨ b = q) ∧ ¬(c = p ∨ c = q)) ∨
      (¬(b = p ∨ b = q) ∧ (c = p ∨ c = q)) := by
  have key : ∀ u v z s t : Color, u ≠ 0 → v ≠ 0 → z ≠ 0 → u ≠ v → u ≠ z → v ≠ z →
      s ≠ 0 → t ≠ 0 → s ≠ t → (u = s ∨ u = t) →
      (((v = s ∨ v = t) ∧ ¬(z = s ∨ z = t)) ∨
        (¬(v = s ∨ v = t) ∧ (z = s ∨ z = t))) := by decide
  exact key a b c p q htriple.1 htriple.2.1 htriple.2.2.1 htriple.2.2.2.1
    htriple.2.2.2.2.1 htriple.2.2.2.2.2 hpair.1 hpair.2.1 hpair.2.2 hactive

set_option synthInstance.maxSize 4000 in
/-- **Both cap edges selected at the inactive position.**  The boundary colour
is the third colour, so the two internal colours are exactly the chosen pair. -/
theorem selected_both_of_inactive {a b c p q : Color}
    (htriple : IsTaitColorTriple a b c) (hpair : ValidColorPair p q)
    (hinactive : a ≠ p ∧ a ≠ q) :
    (b = p ∨ b = q) ∧ (c = p ∨ c = q) := by
  have key : ∀ u v z s t : Color, u ≠ 0 → v ≠ 0 → z ≠ 0 → u ≠ v → u ≠ z → v ≠ z →
      s ≠ 0 → t ≠ 0 → s ≠ t → u ≠ s → u ≠ t →
      ((v = s ∨ v = t) ∧ (z = s ∨ z = t)) := by decide
  exact key a b c p q htriple.1 htriple.2.1 htriple.2.2.1 htriple.2.2.2.1
    htriple.2.2.2.2.1 htriple.2.2.2.2.2 hpair.1 hpair.2.1 hpair.2.2
    hinactive.1 hinactive.2

/-- The triple of colours meeting cap vertex `i`: its boundary colour and the
two internal cap edges on either side. -/
theorem triple_at (hx : CAP5ExtendsAcrossCycleWith w x) (i : Fin 5) :
    IsTaitColorTriple (w i) (x (i - 1)) (x i) := by
  fin_cases i
  · exact hx.1
  · exact hx.2.1
  · exact hx.2.2.1
  · exact hx.2.2.2.1
  · exact hx.2.2.2.2

/-- The unique cap position whose boundary colour lies outside the chosen pair.
For a majority pair of a good word this is the position carrying the other
singleton colour. -/
structure InactivePosition (w : CAP5BoundaryWord) (p q : Color) (v : Fin 5) : Prop where
  not_active : w v ≠ p ∧ w v ≠ q
  eq_of_not_active : ∀ i : Fin 5, w i ≠ p → w i ≠ q → i = v

/-- Off the inactive position every cap position is active. -/
theorem active_of_ne {p q : Color} {v i : Fin 5} (hv : InactivePosition w p q v)
    (hi : i ≠ v) : w i = p ∨ w i = q := by
  by_contra hcontra
  push_neg at hcontra
  exact hi (hv.eq_of_not_active i hcontra.1 hcontra.2)

/-- Cap index arithmetic: every position is an offset of any chosen one. -/
private theorem fin5_cases (v j : Fin 5) :
    j = v ∨ j = v + 1 ∨ j = v + 2 ∨ j = v + 3 ∨ j = v + 4 := by
  revert v j; decide

private theorem fin5_add_ne (v : Fin 5) {k : Fin 5} (hk : k ≠ 0) : v + k ≠ v := by
  revert hk; revert v k; decide

private theorem fin5_sub_one (v : Fin 5) : v - 1 = v + 4 := by revert v; decide

private theorem fin5_s1 (v : Fin 5) : (v + 1) - 1 = v := by revert v; decide

private theorem fin5_s2 (v : Fin 5) : (v + 2) - 1 = v + 1 := by revert v; decide

private theorem fin5_s4 (v : Fin 5) : (v + 4) - 1 = v + 3 := by revert v; decide

/-- **The selected cap edges are exactly three, and their positions are forced.**
Both edges at the inactive position are selected; walking away from it, the
`exactly one at each active vertex` alternation pins the third. -/
theorem selected_iff (hx : CAP5ExtendsAcrossCycleWith w x)
    {p q : Color} (hpair : ValidColorPair p q) {v : Fin 5}
    (hv : InactivePosition w p q v) (j : Fin 5) :
    CapEdgeSelected x p q j ↔ (j = v + 4 ∨ j = v ∨ j = v + 2) := by
  classical
  have hactive : ∀ k : Fin 5, k ≠ 0 → (w (v + k) = p ∨ w (v + k) = q) := fun k hk =>
    active_of_ne hv (fin5_add_ne v hk)
  -- both cap edges at the inactive position are selected
  have hb := selected_both_of_inactive
    (by have h := triple_at hx v; rw [fin5_sub_one v] at h; exact h) hpair hv.not_active
  have s4 : CapEdgeSelected x p q (v + 4) := hb.1
  have s0 : CapEdgeSelected x p q v := hb.2
  -- the next vertex is active and already carries a selected edge
  have n1 : ¬ CapEdgeSelected x p q (v + 1) := by
    have htri := triple_at hx (v + 1)
    rw [fin5_s1 v] at htri
    rcases selected_xor_of_active htri hpair (hactive 1 (by decide)) with
      ⟨_, hno⟩ | ⟨hno, _⟩
    · exact hno
    · exact absurd s0 hno
  -- symmetrically the vertex before the inactive one blocks its far edge
  have n3 : ¬ CapEdgeSelected x p q (v + 3) := by
    have htri := triple_at hx (v + 4)
    rw [fin5_s4 v] at htri
    rcases selected_xor_of_active htri hpair (hactive 4 (by decide)) with
      ⟨_, hno⟩ | ⟨hno, _⟩
    · exact absurd s4 hno
    · exact hno
  -- and the blocked edge forces the third selected one
  have s2 : CapEdgeSelected x p q (v + 2) := by
    have htri := triple_at hx (v + 2)
    rw [fin5_s2 v] at htri
    rcases selected_xor_of_active htri hpair (hactive 2 (by decide)) with
      ⟨hyes, _⟩ | ⟨_, hyes⟩
    · exact absurd hyes n1
    · exact hyes
  constructor
  · intro hsel
    rcases fin5_cases v j with rfl | rfl | rfl | rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact absurd hsel n1
    · exact Or.inr (Or.inr rfl)
    · exact absurd hsel n3
    · exact Or.inl rfl
  · rintro (rfl | rfl | rfl)
    · exact s4
    · exact s0
    · exact s2

/-- **The restored cap pairing.**  Selected edges `v+4`, `v` and `v+2` join
`v+4 — v — v+1` and `v+2 — v+3`, so on the four active positions the cap
contributes exactly the perfect matching `{v+4, v+1} | {v+2, v+3}`. -/
def CapBlock (v : Fin 5) (i : Fin 5) : Prop := i = v + 4 ∨ i = v + 1

instance (v i : Fin 5) : Decidable (CapBlock v i) := by unfold CapBlock; infer_instance

/-- The cap pairing of two active positions: they share a cap block. -/
def CapPairRel (v : Fin 5) (i j : Fin 5) : Prop := CapBlock v i ↔ CapBlock v j

instance (v i j : Fin 5) : Decidable (CapPairRel v i j) := by
  unfold CapPairRel; infer_instance

/-- The cap pairing is an equivalence relation on cap positions. -/
theorem capPairRel_refl (v i : Fin 5) : CapPairRel v i i := Iff.rfl

theorem capPairRel_symm {v i j : Fin 5} (h : CapPairRel v i j) : CapPairRel v j i := h.symm

theorem capPairRel_trans {v i j k : Fin 5} (h : CapPairRel v i j)
    (h' : CapPairRel v j k) : CapPairRel v i k := h.trans h'

/-- On the four active positions the cap pairing has exactly the two source
blocks: the inactive position's two neighbours, and the remaining pair. -/
theorem capPairRel_iff (v i j : Fin 5) :
    CapPairRel v i j ↔
      ((i = v + 4 ∨ i = v + 1) ↔ (j = v + 4 ∨ j = v + 1)) := Iff.rfl

/-- The two blocks are genuinely different, so the cap alone never merges the
four active positions. -/
theorem not_capPairRel_cross (v : Fin 5) : ¬ CapPairRel v (v + 1) (v + 2) := by
  have key : ∀ u : Fin 5,
      ¬ ((u + 1 = u + 4 ∨ u + 1 = u + 1) ↔ (u + 2 = u + 4 ∨ u + 2 = u + 1)) := by decide
  exact key v

/-! ## Fidelity to the source's pentagonal cap table

The closed form above says the cap pairing depends only on the *inactive*
position `v`: the two blocks are `{v+4, v+1}` and `{v+2, v+3}`.  The source
instead publishes a ten-row table of explicit matchings.  The rows below check
that the two descriptions agree, on the table's first row and on both of its
majority pairs.  This is a reproduction of published data, not a new claim. -/

private instance decIsTaitColorTriple (a b c : Color) :
    Decidable (IsTaitColorTriple a b c) := by
  unfold IsTaitColorTriple; infer_instance

private instance decExtendsAcrossCycleWith (w : CAP5BoundaryWord)
    (x : CAP5InternalCycleColoring) :
    Decidable (CAP5ExtendsAcrossCycleWith w x) := by
  unfold CAP5ExtendsAcrossCycleWith; infer_instance

/-- The source table's first normalized good word `00012`, with the majority
colour red and singleton colours blue and purple. -/
def tableWord : CAP5BoundaryWord
  | 0 => red
  | 1 => red
  | 2 => red
  | 3 => blue
  | 4 => purple

/-- The source table's cap extension `21201` for that row. -/
def tableExtension : CAP5InternalCycleColoring
  | 0 => purple
  | 1 => blue
  | 2 => purple
  | 3 => red
  | 4 => blue

/-- The published extension really extends the published word. -/
theorem tableExtension_extends :
    CAP5ExtendsAcrossCycleWith tableWord tableExtension := by decide

/-- Hence it *is* the extension, by uniqueness. -/
theorem capExtension_tableWord : capExtension tableWord = tableExtension :=
  capExtension_eq tableExtension_extends

/-- For the red/blue pair the inactive position is the purple one, index four. -/
theorem tableWord_inactive_red_blue : InactivePosition tableWord red blue 4 :=
  ⟨by decide, by decide⟩

/-- For the red/purple pair the inactive position is the blue one, index three. -/
theorem tableWord_inactive_red_purple : InactivePosition tableWord red purple 3 :=
  ⟨by decide, by decide⟩

/-- Table row `00012`, pair `(0,1)`: the source records the matching `03 | 12`,
and the closed form at `v = 4` gives blocks `{4+4, 4+1} = {3, 0}` and
`{4+2, 4+3} = {1, 2}`. -/
theorem capPairRel_tableWord_red_blue :
    CapPairRel 4 0 3 ∧ CapPairRel 4 1 2 ∧ ¬ CapPairRel 4 0 1 := by decide

/-- Table row `00012`, pair `(0,2)`: the source records `01 | 24`, and the
closed form at `v = 3` gives `{3+4, 3+1} = {2, 4}` and `{3+2, 3+3} = {0, 1}`. -/
theorem capPairRel_tableWord_red_purple :
    CapPairRel 3 0 1 ∧ CapPairRel 3 2 4 ∧ ¬ CapPairRel 3 0 2 := by decide

/-- The selected cap edges of the published row are the three predicted by the
closed form. -/
theorem selected_tableWord_red_blue (j : Fin 5) :
    CapEdgeSelected tableExtension red blue j ↔ (j = 3 ∨ j = 4 ∨ j = 1) := by
  revert j; decide

end GoertzelV24AnnularFrontierMenuCapMatching

end Mettapedia.GraphTheory.FourColor
