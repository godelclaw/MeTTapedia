import Mettapedia.Logic.HostingStyles.Weighted.FibreSum

/-!
# Dividing by the fibre multiplicity

Giving every target match the source weight multiplies the fibre sum by the
number of matches. The sum is the source weight again when each match carries
a quotient of that weight by the multiplicity. A commutative semiring supplies
the quotient only when such an element exists. `ℕ` has no element `d` with
`2 * d = 1`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

open Mettapedia.GSLT.Dynamics.JoinAggregation

/-- The weight type supplies a quotient of `w` by a positive multiplicity.
The quotient is data, so this is not a `Prop`: proof irrelevance would erase it. -/
structure Splits (K : Type*) [CommSemiring K] (μ : ℕ) (w : K) where
  nonzero : μ ≠ 0
  quotient : K
  equation : (μ : K) * quotient = w

/-- **Positive.** Exact rational weights split by any positive multiplicity. -/
theorem rat_splits (μ : ℕ) (hμ : μ ≠ 0) (w : ℚ) : Nonempty (Splits ℚ μ w) :=
  ⟨{ nonzero := hμ
     quotient := w / (μ : ℚ)
     equation := by
       have nonzeroCast : (μ : ℚ) ≠ 0 := by exact_mod_cast hμ
       field_simp [nonzeroCast] }⟩

/-- **Negative.** Multiplicities in `ℕ` do not split `1` by `2`. -/
theorem nat_one_not_split_by_two : ¬ Nonempty (Splits ℕ 2 1) := by
  intro ⟨split⟩
  have eq := split.equation
  cases split.quotient with
  | zero =>
    simp at eq
  | succ n =>
    omega

/-- No commutative semiring is guaranteed to supply the quotient. -/
theorem not_every_commSemiring_splits :
    ¬ ∀ (K : Type) (_ : CommSemiring K) (μ : ℕ) (w : K),
        μ ≠ 0 → Nonempty (Splits K μ w) := by
  intro all
  exact nat_one_not_split_by_two (all ℕ inferInstance 2 1 (by decide))

/-- A positive multiplicity has a match in the fibre. -/
theorem split_fibre_nonempty {K : Type*} [CommSemiring K] (μ : ℕ) (w : K)
    (split : Splits K μ w) (b : Bool) : ∃ index : Fin μ, (b, index).1 = b := by
  exact ⟨⟨0, Nat.pos_of_ne_zero split.nonzero⟩, rfl⟩

/-- **The correction.** Dividing each target weight by the fibre multiplicity
restores weight preservation. -/
theorem splits_restore {K : Type*} [CommSemiring K] (μ : ℕ) (w : K) (split : Splits K μ w) :
    weightPreserving (fun _ : Bool => w) (fun p : Bool × Fin μ => p.1)
      (fun _ => split.quotient) (bothCopies μ) := by
  intro b
  rw [fibre_sum_mul, split.equation]

/-- **Negative.** `ℕ` supplies no corrected weight for a doubled unit event. -/
theorem nat_duplication_has_no_quotient :
    ¬ ∃ d : ℕ, weightPreserving (fun _ : Bool => (1 : ℕ)) (fun p : Bool × Fin 2 => p.1)
        (fun _ => d) (bothCopies 2) := by
  intro ⟨d, preserves⟩
  have eq : (2 : ℕ) * d = 1 := by
    have := preserves true
    rw [fibre_sum_mul] at this
    simpa [Nat.mul_comm] using this.symm
  cases d with
  | zero =>
    simp at eq
  | succ n =>
    omega

end Mettapedia.Logic.HostingStyles.Weighted
