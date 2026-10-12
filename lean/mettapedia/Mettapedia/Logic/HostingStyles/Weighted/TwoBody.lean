import Mettapedia.Logic.HostingStyles.Weighted.Division

/-!
# Two-body site of the collision correspondence

Meredith, *Collision and Scattering for Process Molecules*, Definition `def:mu`
and Theorem `thm:corr`. The fibre multiplicity is `μ = k! ∏_a T_a`. At a
two-body site with one atom and one admissible matrix, `k = 2` and `T_a = 1`,
so `μ = 2`.

The translation of Definition `def:translation` assigns each candidate the
weight `w_k g(σ) / μ`. The proof sketch of `thm:corr` sums `μ` such candidates
and obtains `w_k g(σ)`. Reading the same candidates at the undivided weight
`w_k g(σ)` makes the sum `μ` times too large, so that reading of the theorem
is false. The corrected equality is the one the sketch already computes, with
`μ` left as `k! ∏_a T_a`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Weighted

open Mettapedia.GSLT.Dynamics.JoinAggregation

/-- How many admissible matrices the two-body site has: one atom, one column,
row sums `(1, 1)`. -/
def twoBodyMatrixCount : ℕ := 1

/-- `μ = k! ∏_a T_a` at `k = 2` and `T_a = twoBodyMatrixCount`. -/
def twoBodyMultiplicity : ℕ := Nat.factorial 2 * twoBodyMatrixCount

theorem twoBodyMultiplicity_eq : twoBodyMultiplicity = 2 := by
  decide

/-- The candidates at the site, one per element of the fibre. -/
def twoBodyCandidates : List (Fin twoBodyMultiplicity) :=
  List.ofFn fun index => index

theorem const_fibre_sum {K : Type*} [CommSemiring K] (w : K) :
    groupSum (fun _ : Fin twoBodyMultiplicity => ()) (fun _ => w) twoBodyCandidates () =
      (twoBodyMultiplicity : K) * w := by
  unfold groupSum twoBodyCandidates
  have filtered :
      List.filter (fun _ : Fin twoBodyMultiplicity => () = ())
        (List.ofFn fun index => index) = List.ofFn fun index => index := by
    refine List.filter_eq_self.mpr ?_
    intro _ _
    exact decide_eq_true rfl
  rw [filtered]
  have mapped :
      (List.ofFn fun index : Fin twoBodyMultiplicity => index).map (fun _ => w) =
        List.ofFn fun _ : Fin twoBodyMultiplicity => w := by
    rw [List.map_ofFn]
    rfl
  rw [mapped, List.sum_ofFn, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The undivided reading is false.** Each of the `μ` candidates carrying `w`
sums to `μ * w`, not to `w`, whenever `w ≠ 0`. -/
theorem undivided_two_body_overcounts (w : ℕ) (hw : 0 < w) :
    groupSum (fun _ : Fin twoBodyMultiplicity => ()) (fun _ => w) twoBodyCandidates () ≠ w := by
  rw [const_fibre_sum, twoBodyMultiplicity_eq]
  intro same
  have : 2 * w = 1 * w := by simpa using same
  exact absurd (Nat.eq_of_mul_eq_mul_right hw this) (by decide)

/-- **The corrected statement.** With `μ = 2! · T_a` and each candidate weighted
by a quotient of `w` by `μ`, the fibre sum is `w`. -/
theorem corrected_two_body {K : Type*} [CommSemiring K] (w : K)
    (split : Splits K twoBodyMultiplicity w) :
    groupSum (fun _ : Fin twoBodyMultiplicity => ()) (fun _ => split.quotient)
      twoBodyCandidates () = w := by
  rw [const_fibre_sum, split.equation]

/-- **Negative.** `ℕ` does not supply the quotient for a unit two-body weight. -/
theorem nat_two_body_not_split : ¬ Nonempty (Splits ℕ twoBodyMultiplicity 1) := by
  intro ⟨split⟩
  have eq : (2 : ℕ) * split.quotient = 1 := split.equation
  cases split.quotient with
  | zero =>
    simp at eq
  | succ n =>
    omega

end Mettapedia.Logic.HostingStyles.Weighted
