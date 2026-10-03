import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import Mathlib.Data.Finset.Filter

/-!
# Sound propagation of colouring lists along edges

A colour at one endpoint must have a different supported colour at the
other endpoint. Filtering by this necessary condition preserves every
proper list colouring. A finite trace ending with an empty list therefore
certifies nonextension without enumerating whole colourings. Nonempty
remaining lists do not establish existence of a colouring.
-/

namespace SimpleGraph.ColoringListPropagation

variable {V A : Type*} [DecidableEq V] [DecidableEq A]

def trim (L : V → Finset A) (e : V × V) : V → Finset A :=
  Function.update L e.2 ((L e.2).filter fun a => ∃ b ∈ L e.1, a ≠ b)

def run (L : V → Finset A) : List (V × V) → V → Finset A
  | [] => L
  | e :: es => run (trim L e) es

theorem trim_sound {G : SimpleGraph V} (C : G.Coloring A) (L : V → Finset A)
    (fits : ∀ x, C x ∈ L x) (e : V × V) (edge : G.Adj e.1 e.2) :
    ∀ x, C x ∈ trim L e x := by
  intro x
  by_cases hx : x = e.2
  · subst x
    simp only [trim, Function.update_self, Finset.mem_filter]
    exact ⟨fits _, C e.1, fits _, (C.valid edge).symm⟩
  · simpa only [trim, Function.update_of_ne hx] using fits x

theorem run_sound {G : SimpleGraph V} (C : G.Coloring A) (L : V → Finset A)
    (fits : ∀ x, C x ∈ L x) (es : List (V × V))
    (edges : ∀ e ∈ es, G.Adj e.1 e.2) : ∀ x, C x ∈ run L es x := by
  induction es generalizing L with
  | nil => exact fits
  | cons e es ih =>
      exact ih (trim L e) (trim_sound C L fits e (edges e (by simp)))
        (fun f hf => edges f (by simp [hf]))

theorem empty_refutes {G : SimpleGraph V} (L : V → Finset A)
    (es : List (V × V)) (edges : ∀ e ∈ es, G.Adj e.1 e.2)
    (x : V) (empty : run L es x = ∅) :
    ¬ ∃ C : G.Coloring A, ∀ v, C v ∈ L v := by
  rintro ⟨C, fits⟩
  have h := run_sound C L fits es edges x
  rw [empty] at h
  exact Finset.notMem_empty _ h

end SimpleGraph.ColoringListPropagation
