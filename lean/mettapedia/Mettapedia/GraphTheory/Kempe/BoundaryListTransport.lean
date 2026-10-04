import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.SDiff
import Mathlib.Data.Fintype.Basic

/-!
# Colour lists under a retained boundary cut

An evaluated list forgets which boundary ports forbid each colour. To
transport a boundary operation, retain the forbidden colours on each side
of its cut. This summary commutes exactly with any palette map applied to
the moving side, and with successive maps on that same cut.
-/

namespace SimpleGraph.BoundaryListTransport

variable {B V A : Type*} [DecidableEq B] [DecidableEq A] [Fintype A]

def allowed (ports : V → Finset B) (b : B → A) (v : V) : Finset A :=
  Finset.univ.filter fun a => ∀ i ∈ ports v, a ≠ b i

def summary (ports : V → Finset B) (cut : Finset B) (b : B → A) (v : V) :
    Finset A × Finset A :=
  (((ports v) \ cut).image b, ((ports v) ∩ cut).image b)

def interpret (q : Finset A × Finset A) : Finset A :=
  Finset.univ.filter fun a => ∀ c ∈ q.1 ∪ q.2, a ≠ c

def change (cut : Finset B) (f : A → A) (b : B → A) (i : B) : A :=
  if i ∈ cut then f (b i) else b i

def advance (f : A → A) (q : Finset A × Finset A) : Finset A × Finset A :=
  (q.1, q.2.image f)

/-- The cut summary still recovers exactly the original admissible colours. -/
theorem interpret_summary (ports : V → Finset B) (cut : Finset B) (b : B → A) (v : V) :
    interpret (summary ports cut b v) = allowed ports b v := by
  have split : ((ports v \ cut).image b) ∪ ((ports v ∩ cut).image b) =
      (ports v).image b := by rw [← Finset.image_union, Finset.sdiff_union_inter]
  ext a
  simp only [interpret, summary, Finset.mem_filter, Finset.mem_univ, true_and,
    allowed, split]
  simp

omit [Fintype A] in
/-- Both observations refer to the same original boundary assignment. -/
theorem transport (ports : V → Finset B) (cut : Finset B) (f : A → A)
    (b : B → A) (v : V) :
    summary ports cut (change cut f b) v = advance f (summary ports cut b v) := by
  apply Prod.ext
  · apply Finset.image_congr
    intro i hi
    exact ite_eq_right (Finset.mem_sdiff.mp hi).2
  · change (ports v ∩ cut).image (change cut f b) =
      ((ports v ∩ cut).image b).image f
    rw [Finset.image_image]
    apply Finset.image_congr
    intro i hi
    exact ite_eq_left (Finset.mem_inter.mp hi).2

theorem allowed_change (ports : V → Finset B) (cut : Finset B) (f : A → A)
    (b : B → A) (v : V) :
    allowed ports (change cut f b) v = interpret (advance f (summary ports cut b v)) := by
  rw [← interpret_summary ports cut (change cut f b) v, transport]

omit [Fintype A] in
/-- Repeated palette maps on the retained cut need no new boundary observation. -/
theorem advance_comp (f g : A → A) (q : Finset A × Finset A) :
    advance g (advance f q) = advance (g ∘ f) q := by
  simp [advance, Finset.image_image]

/-- Equality of the refined observations is preserved by the operation. -/
theorem congruence (ports : V → Finset B) (cut : Finset B) (f : A → A)
    (b c : B → A) (same : ∀ v, summary ports cut b v = summary ports cut c v) :
    allowed ports (change cut f b) = allowed ports (change cut f c) := by
  funext v
  rw [allowed_change, allowed_change, same v]

end SimpleGraph.BoundaryListTransport
