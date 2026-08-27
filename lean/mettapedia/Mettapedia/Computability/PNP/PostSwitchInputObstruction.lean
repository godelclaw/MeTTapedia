import Mettapedia.Computability.PNP.BitVec
import Mathlib.Data.Prod.Basic

/-!
# P vs NP crux: the exact post-switch input is not `T_i`-invariant

The paper defines the per-bit post-switch input as `u_i = (z, a_i, b)` and the
promise-preserving involution `T_i` as toggling the VV right-hand side by `a_i`.

This file formalizes the exact bridge point:
- the full input `(z, a_i, b)` is preserved by `T_i` iff `a_i = 0`;
- the reduced projection `(z, a_i)` is always preserved.

So once the paper keeps the full VV right-hand side `b`, the claim that `T_i`
preserves the local input is false on every nonzero VV column. If it drops `b`,
it lands exactly in the invariant-feature regime analyzed by the other
obstruction files.
-/

namespace Mettapedia.Computability.PNP

section

structure PostSwitchInput (Z : Type*) (k : ℕ) where
  z : Z
  a : BitVec k
  b : BitVec k

/-- The exact local-input action induced by the paper's involution `T_i`. -/
def tiInputMap {Z : Type*} {k : ℕ} (u : PostSwitchInput Z k) : PostSwitchInput Z k :=
  ⟨u.z, u.a, vvToggle u.a u.b⟩

/-- The obvious `T_i`-invariant projection obtained by dropping the VV
right-hand side. -/
def invariantProjection {Z : Type*} {k : ℕ} (u : PostSwitchInput Z k) : Z × BitVec k :=
  (u.z, u.a)

@[simp] theorem invariantProjection_tiInputMap
    {Z : Type*} {k : ℕ} (u : PostSwitchInput Z k) :
    invariantProjection (tiInputMap u) = invariantProjection u := by
  rfl

lemma vvToggle_eq_self_iff_zero {n : ℕ} (a b : BitVec n) :
    vvToggle a b = b ↔ a = zeroVec := by
  constructor
  · intro h
    funext i
    have hi : Bool.xor (b i) (a i) = b i := by
      simpa [vvToggle] using congrFun h i
    cases hbi : b i <;> cases hai : a i <;> simp [Bool.xor, hbi, hai, zeroVec] at hi ⊢
  · intro h
    subst h
    funext i
    simp [vvToggle, zeroVec]

theorem tiInputMap_eq_self_iff_zeroColumn
    {Z : Type*} {k : ℕ} (u : PostSwitchInput Z k) :
    tiInputMap u = u ↔ u.a = zeroVec := by
  cases u
  simp [tiInputMap, vvToggle_eq_self_iff_zero]

lemma nonzeroColumn_iff_ne_zero {n : ℕ} (a : BitVec n) :
    nonzeroColumn a ↔ a ≠ zeroVec := by
  constructor
  · intro h
    rcases h with ⟨i, hi⟩
    intro hz
    have : a i = false := by simpa [zeroVec] using congrFun hz i
    simp [hi] at this
  · intro h
    by_contra hzero
    apply h
    funext i
    cases hai : a i with
    | false =>
        simp [zeroVec]
    | true =>
        exact False.elim (hzero ⟨i, hai⟩)

theorem tiInputMap_ne_self_of_nonzeroColumn
    {Z : Type*} {k : ℕ} (u : PostSwitchInput Z k)
    (ha : nonzeroColumn u.a) :
    tiInputMap u ≠ u := by
  intro h
  have hz : u.a = zeroVec := (tiInputMap_eq_self_iff_zeroColumn u).mp h
  exact (nonzeroColumn_iff_ne_zero u.a).mp ha hz

theorem tiInputMap_changes_b_of_nonzeroColumn
    {Z : Type*} {k : ℕ} (u : PostSwitchInput Z k)
    (ha : nonzeroColumn u.a) :
    (tiInputMap u).b ≠ u.b := by
  intro hb
  apply tiInputMap_ne_self_of_nonzeroColumn u ha
  cases u
  simpa [tiInputMap] using hb

/-- The exact calibration step cannot keep both the invariant projection and
the full post-switch input fixed on a nonzero VV column: `(z, a)` is preserved,
but `b` changes and hence the full input changes. -/
theorem calibrationFullInputPreservation_fails_of_nonzeroColumn
    {Z : Type*} {k : ℕ} (u : PostSwitchInput Z k)
    (ha : nonzeroColumn u.a) :
    invariantProjection (tiInputMap u) = invariantProjection u ∧
      tiInputMap u ≠ u ∧ (tiInputMap u).b ≠ u.b := by
  exact ⟨invariantProjection_tiInputMap u,
    tiInputMap_ne_self_of_nonzeroColumn u ha,
    tiInputMap_changes_b_of_nonzeroColumn u ha⟩

/-- Global no-go form: in every positive VV width with a concrete `z`, the
claim that `T_i` preserves the full local input on all nonzero columns is
false. -/
theorem not_calibrationFullInputPreservation_on_nonzeroColumns
    {Z : Type*} (z : Z) {k : ℕ} (hk : 0 < k) :
    ¬ (∀ u : PostSwitchInput Z k, nonzeroColumn u.a -> tiInputMap u = u) := by
  intro h
  let u : PostSwitchInput Z k := ⟨z, headOneVec hk, zeroVec⟩
  have ha : nonzeroColumn u.a := by
    refine ⟨⟨0, hk⟩, ?_⟩
    simp [u]
  exact tiInputMap_ne_self_of_nonzeroColumn u ha (h u ha)

/-- A concrete nonzero one-bit post-switch input for the finite domination
counterexample below. -/
def twoPointLocalInput : PostSwitchInput Unit 1 :=
  ⟨(), headOneVec (Nat.zero_lt_succ 0), zeroVec⟩

/-- The two full instances have the same local post-switch input. -/
def twoPointSameLocalInput (_fullInstance : Bool) : PostSwitchInput Unit 1 :=
  twoPointLocalInput

/-- A global decoder that sees the full two-point instance recovers the witness
bit exactly. -/
def twoPointGlobalDecoder (fullInstance : Bool) : Bool :=
  fullInstance

/-- A local decoder is forced to use only the common post-switch input, so in
this two-point witness it is just a fixed guess. -/
def twoPointLocalDecoder (guess : Bool) (_u : PostSwitchInput Unit 1) : Bool :=
  guess

/-- Success count on the two equally weighted full instances. -/
def boolSuccessCount (predict : Bool -> Bool) : Nat :=
  (if predict false = false then 1 else 0) +
    (if predict true = true then 1 else 0)

/-- Success count of a fixed local guess on the two-point witness. -/
def twoPointLocalSuccessCount (guess : Bool) : Nat :=
  boolSuccessCount (fun full => twoPointLocalDecoder guess (twoPointSameLocalInput full))

/-- Success count of the global decoder on the same two-point witness. -/
def twoPointGlobalSuccessCount : Nat :=
  boolSuccessCount twoPointGlobalDecoder

@[simp] theorem twoPointSameLocalInput_eq (fullInstance : Bool) :
    twoPointSameLocalInput fullInstance = twoPointLocalInput := by
  rfl

theorem twoPointLocalInput_nonzeroColumn :
    nonzeroColumn twoPointLocalInput.a := by
  refine ⟨⟨0, Nat.zero_lt_succ 0⟩, ?_⟩
  exact headOneVec_head (Nat.zero_lt_succ 0)

theorem twoPointLocalInput_calibration_fullInput_moves :
    tiInputMap twoPointLocalInput ≠ twoPointLocalInput ∧
      (tiInputMap twoPointLocalInput).b ≠ twoPointLocalInput.b := by
  exact ⟨tiInputMap_ne_self_of_nonzeroColumn twoPointLocalInput
      twoPointLocalInput_nonzeroColumn,
    tiInputMap_changes_b_of_nonzeroColumn twoPointLocalInput
      twoPointLocalInput_nonzeroColumn⟩

theorem twoPointGlobalSuccessCount_eq_two :
    twoPointGlobalSuccessCount = 2 := by
  rfl

theorem twoPointLocalSuccessCount_le_one (guess : Bool) :
    twoPointLocalSuccessCount guess ≤ 1 := by
  cases guess <;> decide

theorem twoPointLocalSuccessCount_lt_global (guess : Bool) :
    twoPointLocalSuccessCount guess < twoPointGlobalSuccessCount := by
  rw [twoPointGlobalSuccessCount_eq_two]
  have h := twoPointLocalSuccessCount_le_one guess
  omega

/-- Finite domination counterexample: the global decoder succeeds on both
full instances, while every decoder depending only on the shared local input
succeeds on at most one. -/
theorem finite_successDomination_counterexample :
    twoPointGlobalSuccessCount = 2 ∧
      (∀ guess : Bool, twoPointLocalSuccessCount guess ≤ 1) ∧
      (∀ guess : Bool, twoPointLocalSuccessCount guess < twoPointGlobalSuccessCount) := by
  exact ⟨twoPointGlobalSuccessCount_eq_two, twoPointLocalSuccessCount_le_one,
    twoPointLocalSuccessCount_lt_global⟩

end

end Mettapedia.Computability.PNP
