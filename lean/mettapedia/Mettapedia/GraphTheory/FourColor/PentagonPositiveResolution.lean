import Mettapedia.GraphTheory.FourColor.CAP5BoundaryWord
import Mathlib.GroupTheory.Perm.Fin

/-!
# The pentagon count is not a positive sum of the two smaller support types

The two types are a cubic Y with a separate terminal wire, and a three-vertex
cubic path. Every boundary permutation is included, not only planar orders.
Five explicit rejected words exclude every type from a positive count identity.

The accompanying endpoint-pairing gate checks that every nonempty piece with
one or three cubic vertices is a positive scalar multiple of one of these
profiles. That exhaustive classification is a separate computation, not a
hypothesis disguised as a proved structural classification in this file.
-/

namespace Mettapedia.GraphTheory.FourColor.PentagonPositiveResolution

local instance (a b c : Color) : Decidable (IsTaitColorTriple a b c) := by
  unfold IsTaitColorTriple
  infer_instance

local instance (w : CAP5BoundaryWord) (x : CAP5InternalCycleColoring) :
    Decidable (CAP5ExtendsAcrossCycleWith w x) := by
  unfold CAP5ExtendsAcrossCycleWith
  infer_instance

def pentagonCount (w : CAP5BoundaryWord) : Nat :=
  (Finset.univ.filter (CAP5ExtendsAcrossCycleWith w)).card

/-- The three actual vertex constraints of the cubic path. Its two internal
edges have colours `x 0` and `x 1`. -/
def TreeExtension (w : CAP5BoundaryWord) (x : Fin 2 → Color) : Prop :=
  IsTaitColorTriple (w 0) (w 1) (x 0) ∧
  IsTaitColorTriple (x 0) (w 2) (x 1) ∧
  IsTaitColorTriple (x 1) (w 3) (w 4)

local instance (w : CAP5BoundaryWord) (x : Fin 2 → Color) :
    Decidable (TreeExtension w x) := by
  unfold TreeExtension
  infer_instance

def treeCount (w : CAP5BoundaryWord) : Nat :=
  (Finset.univ.filter (TreeExtension w)).card

/-- The Y has no internal edges; the separate wire must have equal, nonzero
colours at its two labelled terminals. -/
def starWireCount (w : CAP5BoundaryWord) : Nat :=
  if IsTaitColorTriple (w 0) (w 1) (w 2) ∧ w 3 = w 4 ∧ w 3 ≠ 0 then 1 else 0

abbrev Shape := Bool × Equiv.Perm (Fin 5)

def smallCount (s : Shape) (w : CAP5BoundaryWord) : Nat :=
  if s.1 then treeCount (w ∘ s.2) else starWireCount (w ∘ s.2)

def badWord : Fin 5 → CAP5BoundaryWord
  | 0 => ![blue, red, purple, red, red]
  | 1 => ![blue, red, red, purple, red]
  | 2 => ![red, blue, red, purple, red]
  | 3 => ![red, blue, red, red, purple]
  | 4 => ![red, red, blue, red, purple]

set_option maxRecDepth 100000 in
theorem badWord_count_zero : ∀ i, pentagonCount (badWord i) = 0 := by
  decide +kernel

theorem badWord_nonzero : ∀ i, CAP5BoundaryWordIsNonzero (badWord i) := by
  unfold CAP5BoundaryWordIsNonzero
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
theorem every_shape_accepts_badWord : ∀ s : Shape,
    ∃ i : Fin 5, 0 < smallCount s (badWord i) := by
  decide +kernel

theorem no_small_support_subset (s : Shape) :
    ¬ ∀ w, 0 < smallCount s w → 0 < pentagonCount w := by
  intro h
  obtain ⟨i, hi⟩ := every_shape_accepts_badWord s
  have hz := h _ hi
  rw [badWord_count_zero] at hz
  omega

set_option maxRecDepth 100000 in
theorem goodWord_count_one : pentagonCount ![red, red, red, blue, purple] = 1 := by
  decide +kernel

/-- Arbitrary nonnegative integer weights cannot give an exact resolution.
The weights are fixed across boundary words, as a count identity requires. -/
theorem no_positive_resolution (weight : Shape → Nat) :
    ¬ ∀ w, CAP5BoundaryWordIsNonzero w →
      pentagonCount w = ∑ s : Shape, weight s * smallCount s w := by
  intro h
  have hzero (s : Shape) : weight s = 0 := by
    obtain ⟨i, hi⟩ := every_shape_accepts_badWord s
    have hs : ∑ t : Shape, weight t * smallCount t (badWord i) = 0 := by
      rw [← h _ (badWord_nonzero i), badWord_count_zero]
    have ht := (Finset.sum_eq_zero_iff.mp hs) s (Finset.mem_univ s)
    exact (Nat.mul_eq_zero.mp ht).resolve_right (Nat.ne_of_gt hi)
  have hn : CAP5BoundaryWordIsNonzero ![red, red, red, blue, purple] := by
    intro i
    fin_cases i <;> decide
  have hg := h _ hn
  simp only [goodWord_count_one, hzero, zero_mul, Finset.sum_const_zero] at hg
  omega

end Mettapedia.GraphTheory.FourColor.PentagonPositiveResolution
