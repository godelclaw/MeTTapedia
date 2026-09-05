import Mettapedia.GraphTheory.FourColor.PresentedEnum

/-!
# Correctness of the enumerator, part one: the semantics of one vertex step

`branch` returns the assignment itself when the slot is assigned and the three
one-slot extensions otherwise (`mem_branch_iff`); `set` on a slot leaves every
other slot's digit unchanged and reads back the new digit (`look_set_self`,
`look_set_other`); `properAt` is the pairwise distinctness of three assigned
digits (`properAt_iff`).  These are the tools for the soundness and
completeness of `runVertices` in the next file.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace TubeSlab
namespace Presented
namespace PA

variable {N k : Nat} (x : Fin k → Fin 3)

theorem look_set_self (σ : PA N k) (s : Slot N k) (d : Fin 3) (hs : ∀ i, s ≠ Slot.inp i) :
    (σ.set s d).look x s = some d := by
  cases s with
  | edge e => simp [set, look]
  | inp i => exact absurd rfl (hs i)
  | out i => simp [set, look]

theorem look_set_other (σ : PA N k) (s s' : Slot N k) (d : Fin 3) (hne : s' ≠ s) :
    (σ.set s d).look x s' = σ.look x s' := by
  cases s with
  | edge e =>
    cases s' with
    | edge e' =>
      have : e' ≠ e := fun h => hne (h ▸ rfl)
      simp [set, look, Function.update_of_ne this]
    | inp i => rfl
    | out i => rfl
  | inp i => rfl
  | out i =>
    cases s' with
    | edge e' => rfl
    | inp i' => rfl
    | out i' =>
      have : i' ≠ i := fun h => hne (h ▸ rfl)
      simp [set, look, Function.update_of_ne this]

theorem look_set_inp (σ : PA N k) (i : Fin k) (d : Fin 3) : σ.set (Slot.inp i) d = σ := rfl

/-- the digit of a slot once assigned never changes under later `set`s of other slots,
and `set` only ever targets unassigned slots in `branch` -/
theorem mem_branch_iff (σ σ' : PA N k) (s : Slot N k) :
    σ' ∈ branch x σ s ↔
      ((σ.look x s).isSome ∧ σ' = σ) ∨ (σ.look x s = none ∧ ∃ d, σ' = σ.set s d) := by
  unfold branch
  cases h : σ.look x s with
  | some v =>
    simp only [List.mem_singleton, Option.isSome_some, true_and, reduceCtorEq, false_and, or_false]
  | none =>
    simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false, Option.isSome_none,
      Bool.false_eq_true, false_and, true_and, false_or]
    constructor
    · rintro (rfl | rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
    · rintro ⟨d, rfl⟩
      fin_cases d <;> simp

theorem properAt_iff (σ : PA N k) (s0 s1 s2 : Slot N k) :
    properAt x σ s0 s1 s2 = true ↔
      ∃ a b c, σ.look x s0 = some a ∧ σ.look x s1 = some b ∧ σ.look x s2 = some c ∧
        a ≠ b ∧ a ≠ c ∧ b ≠ c := by
  unfold properAt
  cases h0 : σ.look x s0 <;> cases h1 : σ.look x s1 <;> cases h2 : σ.look x s2 <;>
    simp [bne_iff_ne, and_assoc]

/-- a slot assigned before a `set` of another slot keeps its digit -/
theorem look_set_of_isSome (σ : PA N k) (s s' : Slot N k) (d : Fin 3)
    (hs' : (σ.look x s').isSome) (hs : σ.look x s = none) :
    (σ.set s d).look x s' = σ.look x s' := by
  by_cases hss : s' = s
  · subst hss
    rw [hs] at hs'
    exact absurd hs' (by simp)
  · exact look_set_other x σ s s' d hss

end PA
end Presented
end TubeSlab
end Mettapedia.GraphTheory.FourColor
