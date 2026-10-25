import Mettapedia.Languages.MeTTa.SpaceQueryPolicy
import Mettapedia.Algebra.SupportTensor
import Mathlib.Data.Finsupp.Basic

/-!
# Tensors as weighted dictionaries

A tensor with entries in a semiring `K` and coordinates in `I` is a space of
coordinates annotated in `K` (`Space K I = I →₀ K`): a weighted dictionary
from coordinates to entries, in which an absent coordinate reads zero. It is
the annotated-relation reading of `WeightedAnswerAlgebra` with coordinates as
keys.

* **Slicing is a query with a partly ground key.** For a tensor over `I × J`,
  the slice at `i` is the `match` query of `(i, $j)` (`slice_eq_getValue`).
* **Contraction is join and sum, and it is Kleisli composition.** Contracting
  the shared index of `A` over `I × J` and `B` over `J × L` binds each row of
  `A` to the rows of `B` (`contract_row`); at a coordinate it is
  `∑ⱼ A(i, j) * B(j, l)` (`contract_apply`), the matrix product over finite
  index types (`contract_eq_matrix_mul`). Contraction is associative because
  the answer monad is (`contract_assoc`).
* **Contraction is bilinear** (`contract_add_left`, `contract_add_right`): the
  law incremental maintenance of a join uses (`SpaceDeltas`).
* **A change of annotation commutes with contraction** (`mapK_contract`). Over
  annotations without zero divisors and with no negative entries, such as
  counts, a coordinate of a contraction is present exactly when a shared index
  joins two present entries (`contract_ne_zero_iff`): presence of a weighted
  contraction is the composition of the two relations, the reading of the
  conjunctive query `(, (A $i $j) (B $j $l))` projected to `$i` and `$l`.
* **Graphs as spaces.** A counted space of edges contracted with itself
  counts the two-step paths (`Controls.two_paths_counted`); read as presence it
  is two-step reachability, the composition of the edge relation, and forgets
  how many paths there are (`Controls.presence_forgets_path_count`).
* **Stored zeros.** The weighted reading identifies a stored zero with an
  absent coordinate (`Controls.weighted_forgets_stored_zero`). A tensor that
  keeps presence (`SupportTensor.Value`, a partial function on coordinates) is
  a functional dictionary space of coordinate-value pairs that it describes
  (`presence_describes`, `presence_functional`), and that space keeps a stored
  zero apart from an absent coordinate (`Controls.dict_keeps_stored_zero`).
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.TensorSpaces

open Mettapedia.Languages.MeTTa.WeightedAnswerAlgebra
open Mettapedia.Languages.MeTTa.SpaceQueryPolicy

universe u

variable {K : Type u} {I J L M : Type*}

/-! ## Slicing and contraction -/

section Contraction

variable [Semiring K]

/-- The slice of a two-index tensor at its first index. -/
noncomputable def slice (tensor : Space K (I × J)) (i : I) : Ans K J := tensor.curry i

theorem slice_apply (tensor : Space K (I × J)) (i : I) (j : J) :
    slice tensor i j = tensor (i, j) :=
  Finsupp.curry_apply tensor i j

/-- Two tensors with the same slices are equal. -/
theorem ext_slice {first second : Space K (I × J)}
    (same : ∀ i, slice first i = slice second i) : first = second := by
  ext ⟨i, j⟩
  rw [← slice_apply, ← slice_apply, same]

/-- **Slicing is the query of `(i, $j)`**, a pattern whose key is ground in
its first coordinate. -/
theorem slice_eq_getValue [DecidableEq I] (tensor : Space K (I × J)) (i : I) :
    slice tensor i = getValue tensor i := by
  ext j
  rw [slice_apply, getValue_apply]

/-- Contract the shared index: bind each row of the left tensor to the rows of
the right one. -/
noncomputable def contract (left : Space K (I × J)) (right : Space K (J × L)) :
    Space K (I × L) :=
  Finsupp.uncurry
    (Finsupp.mapRange (fun row : J →₀ K => Ans.bind row (slice right)) (Ans.zero_bind _) left.curry)

/-- **A row of a contraction is the Kleisli composition of the rows.** -/
theorem contract_row (left : Space K (I × J)) (right : Space K (J × L)) (i : I) :
    slice (contract left right) i = Ans.bind (slice left i) (slice right) := by
  show (Finsupp.uncurry (Finsupp.mapRange _ _ left.curry)).curry i = _
  rw [Finsupp.curry_uncurry, Finsupp.mapRange_apply]
  rfl

/-- Contraction at a coordinate: join on the shared index and sum it out. -/
theorem contract_apply (left : Space K (I × J)) (right : Space K (J × L)) (i : I) (l : L) :
    contract left right (i, l) = (slice left i).sum fun j entry => entry * right (j, l) := by
  rw [← slice_apply, contract_row, Ans.bind_apply]
  simp only [slice_apply]

/-- Over finite index types, contraction is the matrix product. -/
theorem contract_eq_matrix_mul [Fintype J] (left : Space K (I × J)) (right : Space K (J × L))
    (i : I) (l : L) :
    contract left right (i, l) =
      (Matrix.of (fun i j => left (i, j)) * Matrix.of (fun j l => right (j, l))) i l := by
  rw [contract_apply, Finsupp.sum_fintype _ _ (fun _ => zero_mul _), Matrix.mul_apply]
  simp only [slice_apply, Matrix.of_apply]

/-- **Contraction is associative**, because binding is. -/
theorem contract_assoc (first : Space K (I × J)) (second : Space K (J × L))
    (third : Space K (L × M)) :
    contract (contract first second) third = contract first (contract second third) := by
  apply ext_slice
  intro i
  rw [contract_row, contract_row, contract_row, Ans.bind_assoc]
  congr 1
  funext j
  rw [contract_row]

theorem slice_add (first second : Space K (I × J)) (i : I) :
    slice (first + second) i = slice first i + slice second i := by
  ext j
  simp only [slice_apply, Finsupp.add_apply]

/-- **Contraction is additive in its left argument.** -/
theorem contract_add_left (first second : Space K (I × J)) (right : Space K (J × L)) :
    contract (first + second) right = contract first right + contract second right := by
  apply ext_slice
  intro i
  rw [slice_add, contract_row, contract_row, contract_row, slice_add, Ans.add_bind]

/-- **Contraction is additive in its right argument.** -/
theorem contract_add_right (left : Space K (I × J)) (first second : Space K (J × L)) :
    contract left (first + second) = contract left first + contract left second := by
  apply ext_slice
  intro i
  rw [slice_add, contract_row, contract_row, contract_row,
    show slice (first + second) = fun j => slice first j + slice second j from
      funext (slice_add first second)]
  exact Ans.bind_add_right _ _ _

theorem slice_zero (i : I) : slice (0 : Space K (I × J)) i = 0 := by
  ext j
  simp [slice_apply]

@[simp] theorem contract_zero_left (right : Space K (J × L)) :
    contract (0 : Space K (I × J)) right = 0 := by
  apply ext_slice
  intro i
  rw [contract_row, slice_zero, Ans.zero_bind, slice_zero]

@[simp] theorem contract_zero_right (left : Space K (I × J)) :
    contract left (0 : Space K (J × L)) = 0 := by
  apply ext_slice
  intro i
  rw [contract_row, slice_zero,
    show slice (0 : Space K (J × L)) = fun _ => (0 : Ans K L) from funext slice_zero,
    Ans.bind_zero_right]

/-- A change of annotation changes every slice. -/
theorem slice_mapK {L' : Type*} [Semiring L'] (φ : K →+* L') (tensor : Space K (I × J)) (i : I) :
    slice (Ans.mapK φ tensor) i = Ans.mapK φ (slice tensor i) := by
  ext j
  rw [slice_apply, Ans.mapK_apply, Ans.mapK_apply, slice_apply]

/-- **A change of annotation commutes with contraction.** -/
theorem mapK_contract {L' : Type*} [Semiring L'] (φ : K →+* L') (left : Space K (I × J))
    (right : Space K (J × L)) :
    Ans.mapK φ (contract left right) = contract (Ans.mapK φ left) (Ans.mapK φ right) := by
  apply ext_slice
  intro i
  rw [slice_mapK, contract_row, contract_row, Ans.mapK_bind, slice_mapK]
  congr 1
  funext j
  rw [slice_mapK]

end Contraction

/-! ## Presence of a contraction is relational composition -/

section Presence

variable [Semiring K] [PartialOrder K] [CanonicallyOrderedAdd K] [NoZeroDivisors K]

/-- **A coordinate of a contraction is present exactly when a shared index
joins two present entries.** -/
theorem contract_ne_zero_iff [DecidableEq L] (left : Space K (I × J)) (right : Space K (J × L))
    (i : I) (l : L) :
    contract left right (i, l) ≠ 0 ↔ ∃ j, left (i, j) ≠ 0 ∧ right (j, l) ≠ 0 := by
  rw [← slice_apply, contract_row, ← Finsupp.mem_support_iff, Ans.support_bind,
    Finset.mem_biUnion]
  simp only [Finsupp.mem_support_iff, slice_apply]

end Presence

/-! ## Tensors that keep presence -/

section KeepPresence

variable {R : Type*} [Fintype I] [DecidableEq I] [DecidableEq R]

/-- A tensor that keeps presence, read as a dictionary space of
coordinate-value pairs. -/
noncomputable def presenceDict (tensor : Mettapedia.Algebra.SupportTensor.Value I R) :
    Space ℕ (I × R) :=
  ∑ i, match tensor i with
    | some value => Finsupp.single (i, value) 1
    | none => 0

theorem presenceDict_apply (tensor : Mettapedia.Algebra.SupportTensor.Value I R) (i : I)
    (value : R) :
    presenceDict tensor (i, value) = if tensor i = some value then 1 else 0 := by
  unfold presenceDict
  rw [Finsupp.finsetSum_apply, Finset.sum_eq_single i]
  · cases stored : tensor i with
    | none => simp
    | some stored' =>
        simp only [Finsupp.single_apply, Prod.mk.injEq, true_and, Option.some.injEq]
  · intro other _ different
    cases stored : tensor other with
    | none => simp
    | some stored' =>
        simp only [Finsupp.single_apply, Prod.mk.injEq]
        rw [if_neg (fun same => different same.1)]
  · intro absent
    exact absurd (Finset.mem_univ i) absent

/-- **A tensor that keeps presence describes its dictionary space.** -/
theorem presence_describes (tensor : Mettapedia.Algebra.SupportTensor.Value I R) :
    Describes tensor (presenceDict tensor) := by
  intro i value
  rw [presenceDict_apply]
  split_ifs with stored <;> simp [stored]

/-- So that space has at most one value per coordinate. -/
theorem presence_functional (tensor : Mettapedia.Algebra.SupportTensor.Value I R) :
    Functional (presenceDict tensor) :=
  (exists_describes_iff_functional (presenceDict tensor)).mp ⟨tensor, presence_describes tensor⟩

end KeepPresence

/-! ## Controls -/

namespace Controls

/-- The weighted reading of a tensor that keeps presence: fill absent
coordinates with zero. -/
noncomputable def weighted {I : Type*} [Fintype I]
    (tensor : Mettapedia.Algebra.SupportTensor.Value I ℕ) : Space ℕ I :=
  Finsupp.equivFunOnFinite.symm (Mettapedia.Algebra.SupportTensor.fill 0 tensor)

/-- **The weighted reading forgets a stored zero**: an absent coordinate and a
stored zero read alike. -/
theorem weighted_forgets_stored_zero :
    weighted (fun _ : Unit => (none : Option ℕ)) = weighted (fun _ : Unit => some 0) ∧
      (fun _ : Unit => (none : Option ℕ)) ≠ fun _ : Unit => some 0 := by
  refine ⟨?_, ?_⟩
  · ext
    simp [weighted, Mettapedia.Algebra.SupportTensor.fill]
  · intro same
    have := congrFun same ()
    cases this

/-- **The dictionary space keeps a stored zero apart from an absent
coordinate.** -/
theorem dict_keeps_stored_zero :
    presenceDict (fun _ : Unit => (some 0 : Option ℕ)) ((), 0) = 1 ∧
      presenceDict (fun _ : Unit => (none : Option ℕ)) ((), 0) = 0 := by
  constructor <;> simp [presenceDict_apply]

/-- A counting contraction: `A = {(0, 0) ↦ 2, (0, 1) ↦ 3}` and
`B = {(0, 0) ↦ 5, (1, 0) ↦ 7}` give `2 * 5 + 3 * 7 = 31` at `(0, 0)`. -/
theorem counting_contraction :
    contract (Finsupp.single ((0 : Fin 2), (0 : Fin 2)) (2 : ℕ) + Finsupp.single (0, 1) 3)
        (Finsupp.single ((0 : Fin 2), (0 : Fin 1)) (5 : ℕ) + Finsupp.single (1, 0) 7) (0, 0) = 31 := by
  rw [contract_eq_matrix_mul, Matrix.mul_apply]
  simp [Fin.sum_univ_two, Finsupp.single_apply]

/-- A graph with two two-step paths from `0` to `3`: through `1` and through
`2`. -/
noncomputable def diamond : Space ℕ (Fin 4 × Fin 4) :=
  Finsupp.single (0, 1) 1 + Finsupp.single (1, 3) 1 + Finsupp.single (0, 2) 1 +
    Finsupp.single (2, 3) 1

/-- **Contracting the edges with themselves counts the two-step paths.** -/
theorem two_paths_counted : contract diamond diamond (0, 3) = 2 := by
  rw [contract_eq_matrix_mul, Matrix.mul_apply]
  simp [diamond, Fin.sum_univ_four, Finsupp.single_apply]

/-- **Presence forgets how many paths there are**: two-step reachability from
`0` to `3` holds, while the count is two. -/
theorem presence_forgets_path_count :
    (Ans.mapK supportOfCount (contract diamond diamond) (0, 3)).present = true ∧
      contract diamond diamond (0, 3) ≠ 1 := by
  rw [Ans.mapK_apply, two_paths_counted]
  exact ⟨rfl, by decide⟩

/-- A missing join: no shared index connects the two present entries, so the
contraction is absent there. -/
theorem missing_join_absent :
    contract (Finsupp.single ((0 : ℕ), (0 : ℕ)) (1 : ℕ)) (Finsupp.single ((1 : ℕ), (0 : ℕ)) 1)
      (0, 0) = 0 := by
  by_contra present
  obtain ⟨j, left, right⟩ := (contract_ne_zero_iff _ _ 0 0).mp present
  simp only [Finsupp.single_apply, Prod.mk.injEq] at left right
  split_ifs at left right with first second <;> simp_all

end Controls

end Mettapedia.Languages.MeTTa.TensorSpaces
