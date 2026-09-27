import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The bounded-interface Count law

Gluing two tangles along an ordered port set makes their colouring families a
fibre product over the middle word: a colouring of the composite restricts to a
pair agreeing on every identified port, and conversely any such pair glues.
Everything the corridor argument uses about `Count` is an algebraic consequence
of that one bijection, and this file seals those consequences.

The bijection itself is the single graph-level input, kept as an explicit
hypothesis `GluingEquivalence`.  It is the only place the geometry enters; no
result below reproves it or assumes anything else about tangles.

What follows from it:

* taking cardinalities turns the fibre product into matrix convolution;
* Booleanizing positive entries turns convolution into relational composition,
  so the support of a composite depends only on the supports of its factors;
* consequently two prefixes with equal cumulative support stay equal under any
  common suffix, which is what licenses deleting a repeated block; and
* relabelling the ports by an equivalence conjugates every matrix and support,
  and commutes with composition, so a canonical port ordering is a choice of
  representation and not a hypothesis.

Finiteness is recorded too: with finite ports the Boolean supports form a finite
type of size `2 ^ (|X| * |Y|)`, which is what a pigeonhole over cut positions
consumes.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BoundedInterfaceCountLaw

open scoped BigOperators

universe u

variable {X M Z X' M' Z' : Type*}

/-! ## Count matrices and their convolution -/

/-- The number of colourings realizing each ordered pair of boundary words. -/
def countMatrix {Col : X → Z → Type u} [∀ x z, Fintype (Col x z)] : X → Z → ℕ :=
  fun x z => Fintype.card (Col x z)

/-- Convolution over the identified middle ports. -/
def matMul [Fintype M] (A : X → M → ℕ) (B : M → Z → ℕ) : X → Z → ℕ :=
  fun x z => ∑ m : M, A x m * B m z

/-- **The gluing equivalence.**  This is the one graph-level input: a colouring
of the composite is exactly a middle word together with a colouring of each
piece realizing it. -/
def GluingEquivalence (Col₁ : X → M → Type u) (Col₂ : M → Z → Type u)
    (Colc : X → Z → Type u) : Prop :=
  ∀ x z, Nonempty (Colc x z ≃ Σ m : M, Col₁ x m × Col₂ m z)

/-- **Cardinalities turn the fibre product into convolution.** -/
theorem countMatrix_eq_matMul [Fintype M]
    {Col₁ : X → M → Type u} {Col₂ : M → Z → Type u} {Colc : X → Z → Type u}
    [∀ x m, Fintype (Col₁ x m)] [∀ m z, Fintype (Col₂ m z)]
    [∀ x z, Fintype (Colc x z)]
    (hglue : GluingEquivalence Col₁ Col₂ Colc) :
    (countMatrix (Col := Colc)) =
      matMul (countMatrix (Col := Col₁)) (countMatrix (Col := Col₂)) := by
  funext x z
  obtain ⟨e⟩ := hglue x z
  classical
  calc Fintype.card (Colc x z)
      = Fintype.card (Σ m : M, Col₁ x m × Col₂ m z) := Fintype.card_congr e
    _ = ∑ m : M, Fintype.card (Col₁ x m × Col₂ m z) := Fintype.card_sigma
    _ = ∑ m : M, Fintype.card (Col₁ x m) * Fintype.card (Col₂ m z) := by
        simp [Fintype.card_prod]

/-! ## Boolean supports -/

/-- The support relation: which ordered word pairs are realized at all. -/
def support (A : X → Z → ℕ) : X → Z → Prop := fun x z => 0 < A x z

/-- **Convolution Booleanizes to relational composition.**  The support of a
composite depends only on the supports of its factors. -/
theorem support_matMul_iff [Fintype M] (A : X → M → ℕ) (B : M → Z → ℕ) (x : X) (z : Z) :
    support (matMul A B) x z ↔ ∃ m : M, support A x m ∧ support B m z := by
  classical
  constructor
  · intro hpos
    by_contra hno
    push_neg at hno
    apply Nat.not_succ_le_self 0
    refine le_trans hpos (le_of_eq ?_)
    refine Finset.sum_eq_zero ?_
    intro m _
    rcases Nat.eq_zero_or_pos (A x m) with hzero | hposA
    · simp [hzero]
    · have := hno m hposA
      simp [Nat.le_zero.1 (Nat.not_lt.1 this)]
  · rintro ⟨m, hA, hB⟩
    have hpos : 0 < A x m * B m z := Nat.mul_pos hA hB
    have hsplit := Finset.add_sum_erase Finset.univ
      (fun k => A x k * B k z) (Finset.mem_univ m)
    show 0 < ∑ k : M, A x k * B k z
    omega

/-- The support of a composite is determined by the factors' supports. -/
theorem support_matMul_congr [Fintype M] {A A' : X → M → ℕ} {B B' : M → Z → ℕ}
    (hA : support A = support A') (hB : support B = support B') :
    support (matMul A B) = support (matMul A' B') := by
  funext x z
  rw [propext (support_matMul_iff A B x z), propext (support_matMul_iff A' B' x z)]
  have hAx : ∀ m, support A x m = support A' x m := fun m => congrFun (congrFun hA x) m
  have hBz : ∀ m, support B m z = support B' m z := fun m => congrFun (congrFun hB m) z
  simp only [hAx, hBz]

/-! ## Serial runs and block deletion -/

/-- One support update: the words extendable across one more piece. -/
def supportStep (R : M → M → Prop) (S : Set M) : Set M := {y | ∃ x ∈ S, R x y}

/-- The cumulative support after a serial word of pieces. -/
def runSupport : List (M → M → Prop) → Set M → Set M
  | [], S => S
  | R :: Rs, S => runSupport Rs (supportStep R S)

/-- Running a concatenation is running each part in turn. -/
theorem runSupport_append (Rs Ss : List (M → M → Prop)) (S : Set M) :
    runSupport (Rs ++ Ss) S = runSupport Ss (runSupport Rs S) := by
  induction Rs generalizing S with
  | nil => rfl
  | cons R Rs ih =>
      simp only [List.cons_append, runSupport]
      exact ih (supportStep R S)

/-- **Equal cumulative supports stay equal under a common suffix.** -/
theorem runSupport_congr {S S' : Set M} (h : S = S') (Rs : List (M → M → Prop)) :
    runSupport Rs S = runSupport Rs S' := by rw [h]

/-- **A repeated cumulative support licenses deleting the block between.**  The
final accepting support is unchanged. -/
theorem runSupport_delete_block
    (pre mid suf : List (M → M → Prop)) (S : Set M)
    (hrepeat : runSupport (pre ++ mid) S = runSupport pre S) :
    runSupport (pre ++ mid ++ suf) S = runSupport (pre ++ suf) S := by
  rw [runSupport_append, runSupport_append pre suf, hrepeat]

/-! ## Port relabelling -/

/-- Reading a matrix through a relabelling of both port sets. -/
def relabel (e : X ≃ X') (f : Z ≃ Z') (A : X → Z → ℕ) : X' → Z' → ℕ :=
  fun x' z' => A (e.symm x') (f.symm z')

/-- **Relabelling conjugates the support relation.** -/
theorem support_relabel (e : X ≃ X') (f : Z ≃ Z') (A : X → Z → ℕ) (x' : X') (z' : Z') :
    support (relabel e f A) x' z' ↔ support A (e.symm x') (f.symm z') := Iff.rfl

/-- **Relabelling commutes with composition.**  A canonical port ordering is
therefore a choice of representation, not an extra hypothesis. -/
theorem relabel_matMul [Fintype M] [Fintype M'] (e : X ≃ X') (g : M ≃ M') (f : Z ≃ Z')
    (A : X → M → ℕ) (B : M → Z → ℕ) :
    relabel e f (matMul A B) = matMul (relabel e g A) (relabel g f B) := by
  funext x' z'
  simp only [relabel, matMul, Equiv.symm_apply_apply]
  exact (Equiv.sum_comp g.symm (fun m => A (e.symm x') m * B m (f.symm z'))).symm

/-! ## Finiteness of the interface alphabet -/

/-- With finite ports the Boolean supports form a finite type, of size
`2 ^ (|X| * |Z|)`.  This is the pigeonhole alphabet for a corridor of bounded
interface width. -/
theorem card_boolSupports [Fintype X] [DecidableEq X] [Fintype Z] [DecidableEq Z] :
    Fintype.card (X → Z → Bool) = 2 ^ (Fintype.card X * Fintype.card Z) := by
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_bool, ← pow_mul, Nat.mul_comm]

end GoertzelV24BoundedInterfaceCountLaw

end Mettapedia.GraphTheory.FourColor
