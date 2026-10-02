import Mettapedia.GSLT.Core.RelationalRouteSemantics
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Closed colour-transfer routes

An indexed sequence of local relations is interpreted by the existing GSLT
semantics. Its witnesses retain every intermediate colour. Closing a route
identifies its two endpoint colours, rather than merely requiring each local
relation to be inhabited. The result supplies the cyclic witness used by the
wheel extension theorem.
-/

namespace FourColor.CyclicColourRoute

open Mettapedia.GSLT.Ultrainfinite Mettapedia.GSLT.RelationalRouteSemantics

universe u
variable {C : Type u}

inductive Event : Unit → Unit → Type where
  | at (i : ℕ) : Event () ()

def semantics (row : ℕ → C → C → Prop) : Semantics Event where
  State _ := C
  step event a b := match event with
    | .at i => ULift.{u} (PLift (row i a b))

def route (start : ℕ) : ℕ → Route Event () ()
  | 0 => .refl ()
  | n + 1 => .cons (.at start) (route (start + 1) n)

theorem route_append (start m n : ℕ) :
    (route start m).append (route (start + m) n) = route start (m + n) := by
  induction m generalizing start with
  | zero => simp [route]
  | succ m ih =>
    simpa [route, Route.append, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
      congrArg (Route.cons (Event.at start)) (ih (start + 1))

theorem split_iff (row : ℕ → C → C → Prop) (start m n : ℕ) (a b : C) :
    (semantics row).Supports (route start (m + n)) a b ↔
      ∃ c, (semantics row).Supports (route start m) a c ∧
        (semantics row).Supports (route (start + m) n) c b := by
  rw [← route_append]
  exact (semantics row).supports_append_iff _ _ _ _

theorem supports_zero (row : ℕ → C → C → Prop) (start : ℕ) (a b : C) :
    (semantics row).Supports (route start 0) a b ↔ a = b := by
  constructor
  · rintro ⟨h⟩; exact h.down.down
  · intro h; exact ⟨⟨⟨h⟩⟩⟩

theorem supports_succ (row : ℕ → C → C → Prop) (start n : ℕ) (a b : C) :
    (semantics row).Supports (route start (n + 1)) a b ↔
      ∃ c, row start a c ∧ (semantics row).Supports (route (start + 1) n) c b := by
  constructor
  · rintro ⟨⟨c, h, tail⟩⟩; exact ⟨c, h.down.down, ⟨tail⟩⟩
  · rintro ⟨c, h, ⟨tail⟩⟩; exact ⟨⟨c, ⟨⟨h⟩⟩, tail⟩⟩

/-- The GSLT witness is exactly a compatible sequence of all local choices. -/
theorem supports_iff (row : ℕ → C → C → Prop) (start n : ℕ) (a b : C) :
    (semantics row).Supports (route start n) a b ↔
      ∃ f : Fin (n + 1) → C, f 0 = a ∧ f (Fin.last n) = b ∧
        ∀ i : Fin n, row (start + i.val) (f i.castSucc) (f i.succ) := by
  induction n generalizing start a with
  | zero =>
    rw [supports_zero]
    constructor
    · intro h; exact ⟨fun _ => a, rfl, h, fun i => Fin.elim0 i⟩
    · rintro ⟨f, ha, hb, _⟩; exact ha.symm.trans hb
  | succ n ih =>
    rw [supports_succ]
    constructor
    · rintro ⟨c, head, tail⟩
      obtain ⟨f, first, last, steps⟩ := (ih (start + 1) c).mp tail
      refine ⟨Fin.cons a f, by simp, by simpa using last, ?_⟩
      intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simpa [first] using head
      · simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using steps j
    · rintro ⟨f, first, last, steps⟩
      refine ⟨f 1, ?_, (ih (start + 1) (f 1)).mpr ?_⟩
      · simpa [first] using steps 0
      · refine ⟨fun i => f i.succ, rfl, ?_, ?_⟩
        · simpa using last
        · intro i
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using steps i.succ

def next {n : ℕ} (positive : 0 < n) (i : Fin n) : Fin n :=
  ⟨(i.val + 1) % n, Nat.mod_lt _ positive⟩

theorem next_ne {n : ℕ} (two : 2 ≤ n) (i : Fin n) : next (by omega) i ≠ i := by
  intro h
  have e := congrArg Fin.val h
  dsimp [next] at e
  have := i.isLt
  by_cases last : i.val + 1 = n
  · simp [last] at e
    omega
  · rw [Nat.mod_eq_of_lt (by omega)] at e
    omega

/-- Closure uses one consistent colour at the seam. -/
theorem closed_iff {n : ℕ} (positive : 0 < n) (row : Fin n → C → C → Prop) :
    (∃ a, (semantics (fun i => row ⟨i % n, Nat.mod_lt _ positive⟩)).Supports
      (route 0 n) a a) ↔
    ∃ f : Fin n → C, ∀ i, row i (f i) (f (next positive i)) := by
  constructor
  · rintro ⟨a, h⟩
    obtain ⟨f, first, last, steps⟩ := (supports_iff _ 0 n a a).mp h
    refine ⟨fun i => f i.castSucc, ?_⟩
    intro i
    have step := steps i
    simp only [Nat.zero_add, Nat.mod_eq_of_lt i.isLt] at step
    have equal : f i.succ = f (next positive i).castSucc := by
      by_cases top : i.val + 1 = n
      · have hi : i.succ = Fin.last n := Fin.ext top
        have hn : (next positive i).castSucc = (0 : Fin (n + 1)) := by
          apply Fin.ext
          simp [next, top]
        rw [hi, hn, first, last]
      · congr 1
        apply Fin.ext
        dsimp [next]
        exact (Nat.mod_eq_of_lt (by have := i.isLt; omega)).symm
    simpa only [equal] using step
  · rintro ⟨f, steps⟩
    let a : Fin (n + 1) → C := fun i => f ⟨i.val % n, Nat.mod_lt _ positive⟩
    refine ⟨f ⟨0, positive⟩, (supports_iff _ 0 n _ _).mpr ⟨a, ?_, ?_, ?_⟩⟩
    · simp [a]
    · simp [a]
    · intro i
      simpa [a, next, Nat.mod_eq_of_lt i.isLt] using steps i

end FourColor.CyclicColourRoute
