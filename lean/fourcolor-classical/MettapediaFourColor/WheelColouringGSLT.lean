import MettapediaFourColor.WheelColouring
import MettapediaFourColor.CyclicColourRoute

/-!
# Wheel colourings as closed GSLT routes

The centre colour is chosen once for the whole route. Each step excludes it
and all boundary colours adjacent to that rim vertex, then passes the next
rim colour onward. Closing the route recovers precisely a full colouring.
Splitting it retains both the common centre colour and the interface colour.
-/

namespace FourColor.WheelColouringGSLT

open CyclicColourRoute

variable {B C : Type*} {n : ℕ}
  (H : SimpleGraph B) (two : 2 ≤ n) (touch : Fin n → B → Prop)

def row (boundary : B → C) (center : C) (i : Fin n) (a b : C) : Prop :=
  a ≠ center ∧ (∀ p, touch i p → a ≠ boundary p) ∧ a ≠ b

instance [Fintype B] [DecidableEq C] [∀ i b, Decidable (touch i b)]
    (boundary : B → C) (center : C) (i : Fin n) (a b : C) :
    Decidable (row touch boundary center i a b) := by unfold row; infer_instance

def semantics (boundary : B → C) (center : C) :=
  CyclicColourRoute.semantics (fun i => row touch boundary center
    ⟨i % n, Nat.mod_lt _ (by omega)⟩)

theorem witness_iff (k : B → C) :
    Nonempty (WheelColouring.Witness (next (by omega)) touch k) ↔
      ∃ z a, (semantics two touch k z).Supports (route 0 n) a a := by
  constructor
  · rintro ⟨w⟩
    refine ⟨w.center, ?_⟩
    apply (closed_iff (by omega) (row touch k w.center)).mpr
    exact ⟨w.rim, fun i => ⟨w.center_ne i, w.boundary_ne i, w.rim_ne i⟩⟩
  · rintro ⟨z, a, h⟩
    obtain ⟨rim, good⟩ := (closed_iff (by omega) (row touch k z)).mp ⟨a, h⟩
    exact ⟨⟨z, rim, fun i => (good i).1, fun i => (good i).2.2,
      fun i => (good i).2.1⟩⟩

/-- Exact closed-route semantics for every width and every boundary incidence. -/
theorem extends_iff (k : H.Coloring C) :
    (∃ full : (WheelColouring.graph H (next (by omega)) touch (next_ne two)).Coloring C,
      ∀ b, full (.inl b) = k b) ↔
      ∃ z a, (semantics two touch k z).Supports (route 0 n) a a := by
  rw [WheelColouring.extends_iff]
  exact witness_iff two touch k

/-- Two independently interpreted sectors compose using the same shared choices. -/
theorem split_iff (k : B → C) (m l : ℕ) (length : m + l = n) :
    Nonempty (WheelColouring.Witness (next (by omega)) touch k) ↔
      ∃ z a b, (semantics two touch k z).Supports (route 0 m) a b ∧
        (semantics two touch k z).Supports (route m l) b a := by
  rw [witness_iff two touch]
  constructor
  · rintro ⟨z, a, h⟩
    rw [congrArg (route 0) length.symm] at h
    obtain ⟨b, first, last⟩ := (CyclicColourRoute.split_iff
      (fun i => row touch k z ⟨i % n, Nat.mod_lt _ (by omega)⟩) 0 m l a a).mp h
    exact ⟨z, a, b, first, by simpa only [Nat.zero_add, semantics] using last⟩
  · rintro ⟨z, a, b, first, last⟩
    refine ⟨z, a, ?_⟩
    rw [congrArg (route 0) length.symm]
    exact (CyclicColourRoute.split_iff
      (fun i => row touch k z ⟨i % n, Nat.mod_lt _ (by omega)⟩) 0 m l a a).mpr
        ⟨b, first, by simpa only [Nat.zero_add, semantics] using last⟩

end FourColor.WheelColouringGSLT
