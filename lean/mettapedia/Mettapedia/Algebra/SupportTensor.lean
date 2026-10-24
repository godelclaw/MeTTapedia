import Mettapedia.Algebra.FiniteCoordinateBuffer
import Mettapedia.Algebra.SparseLinearMap

/-!
# Support-aware finite tensors

Presence is part of a tensor value. Filling absent coordinates is an explicit,
information-losing interpretation into ordinary finite functions and matrices.
The sparse contraction below executes only jointly present entries; its
agreement with filled contraction uses zero/annihilator laws, not a floating
point reassociation assumption. Coordinates are traversed in the given order.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.SupportTensor

universe u v

abbrev Shape := List Nat
abbrev Coord (shape : Shape) := (axis : Fin shape.length) → Fin shape[axis]
abbrev Value (I : Type u) (R : Type v) := I → Option R
abbrev Tensor (R : Type v) (shape : Shape) := Value (Coord shape) R

variable {I : Type u} {R S : Type v}

def dense (values : I → R) : Value I R := fun i => some (values i)
def fill (default : R) (tensor : Value I R) : I → R :=
  fun i => (tensor i).getD default
def present (tensor : Value I R) (i : I) : Bool := (tensor i).isSome
def map (f : R → S) (tensor : Value I R) : Value I S :=
  fun i => (tensor i).map f

@[simp] theorem fill_dense (default : R) (values : I → R) :
    fill default (dense values) = values := by
  funext i
  rfl

@[simp] theorem present_dense (values : I → R) (i : I) :
    present (dense values) i = true := rfl

@[simp] theorem present_map (f : R → S) (tensor : Value I R) (i : I) :
    present (map f tensor) i = present tensor i := by
  cases h : tensor i <;> simp [present, map, h]

theorem fill_map (f : R → S) (default : R) (tensor : Value I R) :
    fill (f default) (map f tensor) = fun i => f (fill default tensor i) := by
  funext i
  cases h : tensor i <;> simp [fill, map, h]

/-- Filling is faithful only when presence is retained as a separate observation. -/
theorem eq_iff_presence_and_fill (default : R) (left right : Value I R) :
    left = right ↔ present left = present right ∧ fill default left = fill default right := by
  constructor
  · intro h
    subst right
    exact ⟨rfl, rfl⟩
  · rintro ⟨hp, hv⟩
    funext i
    have hp' := congrFun hp i
    have hv' := congrFun hv i
    cases hl : left i <;> cases hr : right i <;>
      simp_all [present, fill]

/-- A masked dense representation retains exactly the information lost by filling. -/
def fromMasked (mask : I → Bool) (values : I → R) : Value I R :=
  fun i => if mask i then some (values i) else none

theorem masked_roundtrip (default : R) (tensor : Value I R) :
    fromMasked (present tensor) (fill default tensor) = tensor := by
  funext i
  cases h : tensor i <;> simp [fromMasked, present, fill, h]

theorem filled_equality_does_not_imply_value_equality :
    let absent : Value Unit Nat := fun _ => none
    let storedZero : Value Unit Nat := fun _ => some 0
    fill 0 absent = fill 0 storedZero ∧ absent ≠ storedZero := by
  constructor
  · rfl
  · intro h
    have := congrFun h ()
    contradiction

/-- Only present pairs generate products. Repeated coordinates remain occurrences. -/
def products [Mul R] (coordinates : List I) (left right : Value I R) : List R :=
  coordinates.filterMap fun i => do
    let a ← left i
    let b ← right i
    pure (a * b)

def contract [AddMonoid R] [Mul R]
    (coordinates : List I) (left right : Value I R) : R :=
  (products coordinates left right).sum

/-- The ordered sparse loop agrees with the ordered filled loop when missing
values are interpreted by a multiplicative annihilator and additive identity. -/
theorem contract_eq_filled [Semiring R]
    (coordinates : List I) (left right : Value I R) :
    contract coordinates left right =
      (coordinates.map fun i => fill 0 left i * fill 0 right i).sum := by
  induction coordinates with
  | nil => simp [contract, products]
  | cons i rest ih =>
      cases hl : left i <;> cases hr : right i <;>
        simp_all [contract, products, fill]

theorem contract_append [Semiring R]
    (first second : List I) (left right : Value I R) :
    contract (first ++ second) left right =
      contract first left right + contract second left right := by
  simp [contract, products, List.filterMap_append]

/-- Occurrences are not deduplicated by sparse contraction. -/
theorem duplicate_coordinates_contribute_twice [Semiring R]
    (i : I) (left right : Value I R) :
    contract [i, i] left right =
      fill 0 left i * fill 0 right i + fill 0 left i * fill 0 right i := by
  simp [contract_eq_filled]

def matrixFill [Zero R] {m n : Nat}
    (tensor : Value (Fin m × Fin n) R) : Matrix (Fin m) (Fin n) R :=
  fun row col => fill 0 tensor (row, col)

/-- A sparse row traversal, independent of Matrix.mulVec. -/
def matvec [AddMonoid R] [Mul R] {m n : Nat}
    (matrix : Value (Fin m × Fin n) R) (vector : Value (Fin n) R) : Fin m → R :=
  fun row => contract (List.finRange n) (fun col => matrix (row, col)) vector

theorem matvec_eq_mulVec [Semiring R] {m n : Nat}
    (matrix : Value (Fin m × Fin n) R) (vector : Value (Fin n) R) :
    matvec matrix vector = (matrixFill matrix).mulVec (fill 0 vector) := by
  funext row
  simp [matvec, contract_eq_filled, Matrix.mulVec, dotProduct,
    matrixFill, fill, List.finRange, List.map_ofFn, List.sum_ofFn]

/-- Existing flat-buffer decoding recovers the filled layer, not its support. -/
theorem rowMajor_filled_roundtrip [Zero R] {m n : Nat}
    (matrix : Value (Fin m × Fin n) R) :
    FiniteCoordinateBuffer.toMatrix m n
      (FiniteCoordinateBuffer.rowMajor (matrixFill matrix)) = matrixFill matrix := by
  exact FiniteCoordinateBuffer.toMatrix_rowMajor (matrixFill matrix)

/-- Canonical support extraction visits coordinates once and retains stored
zeroes. It is not the zero-pruning interpretation of a filled matrix. -/
def entries (coordinates : List I) (tensor : Value I R) : List (I × R) :=
  coordinates.filterMap fun i => (tensor i).map (i, ·)

/-- Ordered COO lookup. Duplicate policy is explicit, not an accidental
effect of a map constructor or a physical sort. -/
def lookupFirst [DecidableEq I] : List (I × R) → Value I R
  | [], _ => none
  | (coordinate, value) :: rest, wanted =>
      if coordinate = wanted then some value else lookupFirst rest wanted

def lookupLast [DecidableEq I] (occurrences : List (I × R)) : Value I R :=
  lookupFirst occurrences.reverse

theorem lookupFirst_entries [DecidableEq I]
    (coordinates : List I) (tensor : Value I R) (i : I) :
    lookupFirst (entries coordinates tensor) i =
      if i ∈ coordinates then tensor i else none := by
  induction coordinates with
  | nil => simp [entries, lookupFirst]
  | cons j rest ih =>
      by_cases same : j = i
      · subst j
        cases h : tensor i <;> simp_all [entries, lookupFirst]
      · cases h : tensor j <;> simp_all [entries, lookupFirst, Ne.symm same]

/-- Extracting and decoding complete coordinates preserves presence, not
just the filled numerical observation. -/
theorem entries_roundtrip [DecidableEq I] (coordinates : List I)
    (complete : ∀ i, i ∈ coordinates) (tensor : Value I R) :
    lookupFirst (entries coordinates tensor) = tensor := by
  funext i
  simp [lookupFirst_entries, complete i]

theorem finite_entries_roundtrip [Fintype I] [DecidableEq I] (tensor : Value I R) :
    lookupFirst (entries Finset.univ.toList tensor) = tensor := by
  apply entries_roundtrip
  simp

theorem duplicate_policy_observes_order :
    lookupFirst [((), 1), ((), 4)] () = some (1 : Nat) ∧
      lookupLast [((), 1), ((), 4)] () = some (4 : Nat) := by decide

theorem entries_products [Mul R] (coordinates : List I) (tensor : Value I R)
    (vector : I → R) :
    (entries coordinates tensor).map (fun entry => entry.2 * vector entry.1) =
      products coordinates tensor (dense vector) := by
  induction coordinates with
  | nil => rfl
  | cons i rest ih =>
      cases h : tensor i <;> simp_all [entries, products, dense]

def toSparseRows {m n : Nat} (matrix : Value (Fin m × Fin n) R) :
    SparseLinearMap (Fin n) (Fin m) R :=
  fun row => entries (List.finRange n) (fun col => matrix (row, col))

theorem sparseRows_apply [Semiring R] {m n : Nat}
    (matrix : Value (Fin m × Fin n) R) (vector : Fin n → R) :
    (toSparseRows matrix).apply vector = (matrixFill matrix).mulVec vector := by
  funext row
  rw [SparseLinearMap.apply_eq]
  unfold toSparseRows
  rw [entries_products]
  change contract (List.finRange n) (fun col => matrix (row, col)) (dense vector) = _
  rw [contract_eq_filled]
  simp [Matrix.mulVec, dotProduct, matrixFill, fill, dense,
    List.finRange, List.map_ofFn, List.sum_ofFn]

/-- The existing occurrence-preserving sparse operator is the filled layer
of the new support-aware representation. -/
theorem sparseRows_toMatrix [Semiring R] {m n : Nat}
    (matrix : Value (Fin m × Fin n) R) :
    (toSparseRows matrix).toMatrix = matrixFill matrix := by
  apply Matrix.ext
  intro row col
  have basis := congrFun (sparseRows_apply matrix (Pi.single col 1)) row
  simpa only [SparseLinearMap.apply_eq_mulVec, Matrix.mulVec_single_one, Matrix.col_apply] using basis

theorem extraction_retains_stored_zero :
    entries [()] (dense (fun _ : Unit => (0 : Nat))) = [((), 0)] ∧
      entries [()] (fun _ : Unit => (none : Option Nat)) = [] := by decide

theorem missing_right_operand_is_not_implicit_one :
    contract [()] (dense (fun _ : Unit => (3 : Nat))) (fun _ => none) = 0 := by
  decide

end Mettapedia.Algebra.SupportTensor
