import Mettapedia.TypeTheory.IndexedPolynomialRepresentation
import Mettapedia.TypeTheory.IndexedPolynomialInduction

/-!
# Vectors represented by length-checked lists

The polynomial vector family is represented by independently length-checked
Lean lists. Constructor preservation retains the payload as well as the index.
Dependent append is derived from a displayed algebra and compared with
ordinary list append. The same constructor methods determine append on the
represented family via generic transport of dependent elimination.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.IndexedPolynomial.VectorRepresentation

open VectorExample

universe u

noncomputable section

/-- An ordinary list together with its exact length, independently of the
polynomial syntax. -/
abbrev ListVector (A : Type u) (n : Nat) := { xs : List A // xs.length = n }

def listNil {A : Type u} : ListVector A 0 := ⟨[], rfl⟩

def listCons {A : Type u} {n : Nat} (a : A) (xs : ListVector A n) :
    ListVector A (n + 1) := ⟨a :: xs.val, by simp only [List.length_cons, xs.property]⟩

/-- The constructor algebra on independent list storage. -/
def listAlgebra (A : Type u) : Algebra (polynomial A) (fun _ n => ListVector A n) where
  act := fun _ _ layer => by
    rcases layer with ⟨shape, children⟩
    cases shape with
    | nil => exact listNil
    | cons n a => exact listCons a (children .star)

/-- Structural encoding, derived by the generic initial-algebra fold. -/
def encode {A : Type u} (n : Nat) (xs : VectorP A n) : ListVector A n :=
  Fix.fold (polynomial A) (listAlgebra A).act .star n xs

@[simp] theorem encode_nil {A : Type u} : encode 0 (nil : VectorP A 0) = listNil := rfl

@[simp] theorem encode_cons {A : Type u} {n : Nat} (a : A) (xs : VectorP A n) :
    encode (n + 1) (cons a xs) = listCons a (encode n xs) := rfl

/-- Decode by ordinary list recursion, not by choosing an inverse from a
surjectivity proof. -/
def fromList {A : Type u} : (xs : List A) → VectorP A xs.length
  | [] => nil
  | a :: xs => cons a (fromList xs)

def decode {A : Type u} {n : Nat} (xs : ListVector A n) : VectorP A n :=
  xs.property ▸ fromList xs.val

@[simp] theorem decode_nil {A : Type u} : decode (listNil : ListVector A 0) = nil := rfl

@[simp] theorem decode_cons {A : Type u} {n : Nat} (a : A) (xs : ListVector A n) :
    decode (listCons a xs) = cons a (decode xs) := by
  rcases xs with ⟨xs, h⟩
  cases h
  rfl

@[simp] theorem decode_encode {A : Type u} (n : Nat) (xs : VectorP A n) :
    decode (encode n xs) = xs := by
  apply eliminate (motive := fun n xs => decode (encode n xs) = xs)
  · rfl
  · intro n a xs ih
    simp only [encode_cons, decode_cons, ih]

@[simp] theorem encode_fromList {A : Type u} (xs : List A) :
    (encode xs.length (fromList xs)).val = xs := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      change a :: (encode xs.length (fromList xs)).val = a :: xs
      rw [ih]

@[simp] theorem encode_decode {A : Type u} {n : Nat} (xs : ListVector A n) :
    encode n (decode xs) = xs := by
  rcases xs with ⟨xs, h⟩
  cases h
  apply Subtype.ext
  exact encode_fromList xs

/-- The generic representation package is instantiated at every length fibre. -/
def listRepresentation (A : Type u) :
    Algebra.Representation (polynomial A) (listAlgebra A) where
  toEquiv := fun base n => by
    cases base
    exact { toFun := encode n
            invFun := decode
            left_inv := decode_encode n
            right_inv := encode_decode }
  commutes := by
    intro base n layer
    cases base
    rcases layer with ⟨shape, children⟩
    cases shape with
    | nil => rfl
    | cons n a => rfl

/-- The generic route-uniqueness theorem eliminates any storage automorphism
that claims to preserve these constructors. -/
theorem list_route_is_identity {A : Type u}
    (route : Algebra.Hom (listAlgebra A) (listAlgebra A))
    (n : Nat) (xs : ListVector A n) : route.toFun .star n xs = xs := by
  rw [Algebra.Representation.route_eq_change
    (listRepresentation A) (listRepresentation A) route]
  exact Algebra.Representation.change_identity (listRepresentation A) .star n xs

/-- Ordinary list append with its independently established length equation. -/
def listAppend {A : Type u} {n m : Nat}
    (xs : ListVector A n) (ys : ListVector A m) : ListVector A (n + m) :=
  ⟨xs.val ++ ys.val, by simp only [List.length_append, xs.property, ys.property]⟩

/-- Constructor methods for append depend on the input length. -/
def appendMethods (A : Type u) :
    Algebra.Displayed (Algebra.initial (polynomial A))
      (fun _ n _ => ∀ m, VectorP A m → VectorP A (n + m)) where
  act := by
    intro base n shape children ih
    cases base
    cases shape with
    | nil =>
        intro m ys
        exact cast (congrArg (VectorP A) (Nat.zero_add m).symm) ys
    | cons n a =>
        intro m ys
        exact cast (congrArg (VectorP A) (Nat.succ_add n m).symm)
          (cons a (ih .star m ys))

/-- Append is obtained from the generic displayed-algebra section. -/
def append {A : Type u} {n m : Nat} (xs : VectorP A n) (ys : VectorP A m) :
    VectorP A (n + m) :=
  (appendMethods A).initialSection.toFun .star n xs m ys

@[simp] theorem append_nil {A : Type u} {m : Nat} (ys : VectorP A m) :
    append (nil : VectorP A 0) ys = cast (congrArg (VectorP A) (Nat.zero_add m).symm) ys := by
  rfl

/-- The inherited dependent section satisfies the cons computation rule. -/
@[simp] theorem append_cons {A : Type u} {n m : Nat}
    (a : A) (xs : VectorP A n) (ys : VectorP A m) :
    append (cons a xs) ys =
      cast (congrArg (VectorP A) (Nat.succ_add n m).symm) (cons a (append xs ys)) := rfl

/-- Erasing an index transport changes no payload. -/
theorem encode_cast {A : Type u} {n m : Nat} (h : n = m) (xs : VectorP A n) :
    (encode m (cast (congrArg (VectorP A) h) xs)).val = (encode n xs).val := by
  cases h
  rfl

/-- Dependent polynomial append preserves the complete ordinary-list result,
not only the result length. -/
theorem append_payload {A : Type u} {n m : Nat} (xs : VectorP A n) (ys : VectorP A m) :
    (encode (n + m) (append xs ys)).val = (encode n xs).val ++ (encode m ys).val := by
  exact eliminate
    (motive := fun n xs => ∀ m (ys : VectorP A m),
      (encode (n + m) (append xs ys)).val =
        (encode n xs).val ++ (encode m ys).val)
    (by
      intro m ys
      rw [append_nil, encode_cast (Nat.zero_add m).symm ys]
      rfl)
    (by
      intro k a xs ih m ys
      change (encode ((k + 1) + m)
        (cast (congrArg (VectorP A) (Nat.succ_add k m).symm) (cons a (append xs ys)))).val = _
      rw [encode_cast (Nat.succ_add k m).symm (cons a (append xs ys))]
      change a :: (encode (k + m) (append xs ys)).val =
        (a :: (encode k xs).val) ++ (encode m ys).val
      rw [ih m ys]
      rfl) n xs m ys

/-- The same operation is transported to list storage with no loss of indices
or values. The reference on the right is ordinary list append. -/
theorem append_representation {A : Type u} {n m : Nat}
    (xs : VectorP A n) (ys : VectorP A m) :
    encode (n + m) (append xs ys) = listAppend (encode n xs) (encode m ys) := by
  apply Subtype.ext
  exact append_payload xs ys


/-- Index casts leave independent list storage unchanged. -/
theorem listVector_cast_val {A : Type u} {n m : Nat} (h : n = m)
    (xs : ListVector A n) :
    (cast (congrArg (ListVector A) h) xs).val = xs.val := by
  cases h
  rfl

/-- Append methods on represented values, retaining the dependent result index. -/
def representedAppendMethods (A : Type u) :
    Algebra.Displayed (listAlgebra A)
      (fun _ n _ => ∀ m, ListVector A m → ListVector A (n + m)) where
  act := by
    intro base n shape children ih
    cases base
    cases shape with
    | nil =>
        intro m ys
        exact cast (congrArg (ListVector A) (Nat.zero_add m).symm) ys
    | cons n a =>
        intro m ys
        exact cast (congrArg (ListVector A) (Nat.succ_add n m).symm)
          (listCons a (ih .star m ys))

/-- Ordinary list append independently satisfies the dependent constructor
methods. This is the implementation-side computation proof. -/
def referenceAppendSection (A : Type u) : (representedAppendMethods A).Section where
  toFun := fun _ _ xs _ ys => listAppend xs ys
  commutes := by
    intro base n shape children
    cases base
    funext m ys
    apply Subtype.ext
    cases shape with
    | nil =>
        change (listAppend listNil ys).val =
          (cast (congrArg (ListVector A) (Nat.zero_add m).symm) ys).val
        rw [listVector_cast_val (Nat.zero_add m).symm ys]
        rfl
    | cons n a =>
        change (listAppend (listCons a (children .star)) ys).val =
          (cast (congrArg (ListVector A) (Nat.succ_add n m).symm)
            (listCons a (listAppend (children .star) ys))).val
        rw [listVector_cast_val (Nat.succ_add n m).symm
          (listCons a (listAppend (children .star) ys))]
        rfl

/-- Dependent append inherited automatically from the algebra representation. -/
def representedAppend {A : Type u} {n m : Nat}
    (xs : ListVector A n) (ys : ListVector A m) : ListVector A (n + m) :=
  ((listRepresentation A).induction (representedAppendMethods A)).toFun .star n xs m ys

/-- Generic representation induction computes exactly independently implemented
list append. No selected judgmental equality of an object theory is assumed. -/
theorem representedAppend_eq_listAppend {A : Type u} {n m : Nat}
    (xs : ListVector A n) (ys : ListVector A m) :
    representedAppend xs ys = listAppend xs ys := by
  exact (congrFun (congrFun
    ((listRepresentation A).induction_unique (representedAppendMethods A)
      (referenceAppendSection A) .star n xs) m) ys).symm

/-- Polynomial dependent append and inherited represented append agree on
both payload and the result length fibre. -/
theorem append_transport {A : Type u} {n m : Nat}
    (xs : VectorP A n) (ys : VectorP A m) :
    encode (n + m) (append xs ys) = representedAppend (encode n xs) (encode m ys) := by
  rw [representedAppend_eq_listAppend]
  exact append_representation xs ys

end
end Mettapedia.TypeTheory.IndexedPolynomial.VectorRepresentation
