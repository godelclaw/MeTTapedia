import Mettapedia.GSLT.LanguageDef.IndexedInductiveElimination
import Mettapedia.TypeTheory.NaturalVectorCoherence

/-!
# Sequentially admitted naturals and indexed vectors

The vector declaration uses the carrier of the admitted natural declaration
as its index type and as its length-field type. Host naturals occur only in
the independently checked list representation. Payloads are parameterized by
`A : Type`; this source interpretation fixes universe zero.

Addition is derived from the admitted natural eliminator. The interpretation
uses the existing semantic polynomial recursor; it is not a compiled numeric
provider. These are semantic declarations and representation comparisons. Textual
lowering, guest typing authority and executable storage adapters are separate.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec

open Mettapedia.TypeTheory
open IndexedPolynomial IndexedPolynomial.Description

namespace Natural

def interface : Interface where
  SortCode := Empty
  Value := Empty.elim
  Index := Unit
  IndexExpr := fun _ => Unit
  evalIndex := fun expression _ => expression

def zeroCode : Code interface [] := .result ()
def succCode : Code interface [] := .recursive () (.result ())

def constructors : List (NamedConstructor interface []) :=
  [⟨"Zero", zeroCode⟩, ⟨"Succ", succCode⟩]

def admitted : IndexedInductive.Admitted interface [] :=
  ⟨constructors, by decide⟩

def source : IndexedInductive.Document interface [] := .bundle
  [.declaration ⟨"Zero", .result ()⟩,
   .declaration ⟨"Succ", .recursive () (.result ())⟩]

theorem source_admitted : IndexedInductive.admit? source = some admitted :=
  IndexedInductive.admit_quote admitted

abbrev polynomial := admitted.polynomial
abbrev Carrier := admitted.Family PUnit.unit ()

def zero : Carrier := by
  refine admitted.construct ⟨⟨0, by decide⟩, ?_⟩
  change ULift (PLift (() = ()))
  exact ⟨⟨rfl⟩⟩

def succ (n : Carrier) : Carrier := by
  refine admitted.construct ⟨⟨1, by decide⟩, ?_⟩
  change Carrier × ULift (PLift (() = ()))
  exact ⟨n, ⟨⟨rfl⟩⟩⟩

def naturalMethods : Algebra.Displayed (Algebra.initial polynomial)
    (fun _ _ _ => Nat) where
  act := by
    intro _ _ shape _children hypotheses
    rcases shape with ⟨occurrence, shape⟩
    refine Fin.cases ?_ (fun occurrence => ?_) occurrence shape hypotheses
    · intro _ _
      exact 0
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
      intro _ hypotheses
      exact Nat.succ (hypotheses none)

noncomputable def toNat (n : Carrier) : Nat :=
  (admitted.eliminate naturalMethods).toFun PUnit.unit () n

@[simp] theorem toNat_zero : toNat zero = 0 := rfl
@[simp] theorem toNat_succ (n : Carrier) : toNat (succ n) = Nat.succ (toNat n) := rfl

def fromNat : Nat → Carrier
  | 0 => zero
  | n + 1 => succ (fromNat n)

@[simp] theorem toNat_fromNat (n : Nat) : toNat (fromNat n) = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [fromNat, toNat_succ, ih]

@[simp] theorem fromNat_toNat (n : Carrier) : fromNat (toNat n) = n := by
  refine @Fix.rec _ _ polynomial PUnit.unit
    (fun _ tree => fromNat ((admitted.eliminate naturalMethods).toFun PUnit.unit _ tree) = tree)
    ?_ () n
  intro index shape children hypotheses
  cases index
  rcases shape with ⟨occurrence, shape⟩
  revert shape children hypotheses
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence
  · intro shape children _hypotheses
    rcases shape with ⟨⟨equation⟩⟩
    change Fix.roll _ _ = Fix.roll _ children
    apply congrArg (Fix.roll _)
    funext position
    exact PEmpty.elim position
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    intro shape children hypotheses
    change succ (fromNat (toNat (children none))) = Fix.roll _ children
    apply (congrArg succ (hypotheses none)).trans
    change Fix.roll _ _ = Fix.roll _ children
    apply congrArg (Fix.roll _)
    funext position
    cases position with
    | none => rfl
    | some impossible => exact PEmpty.elim impossible

noncomputable def representation : Carrier ≃ Nat where
  toFun := toNat
  invFun := fromNat
  left_inv := fromNat_toNat
  right_inv := toNat_fromNat

theorem succ_ne_zero (n : Carrier) : succ n ≠ zero := by
  intro same
  exact Nat.noConfusion (congrArg toNat same)

theorem succ_injective : Function.Injective succ := by
  intro n m same
  apply representation.injective
  exact Nat.succ.inj (show Nat.succ (toNat n) = Nat.succ (toNat m) from
    congrArg toNat same)

/-- Addition is defined by the admitted natural eliminator. -/
def addMethods : Algebra.Displayed (Algebra.initial polynomial)
    (fun _ _ _ => Carrier → Carrier) where
  act := by
    intro _ _ shape _children hypotheses
    rcases shape with ⟨occurrence, shape⟩
    refine Fin.cases ?_ (fun occurrence => ?_) occurrence shape hypotheses
    · intro _ _ m
      exact m
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
      intro _ hypotheses m
      exact succ (hypotheses none m)

noncomputable def add (n m : Carrier) : Carrier :=
  (admitted.eliminate addMethods).toFun PUnit.unit () n m

@[simp] theorem add_zero (m : Carrier) : add zero m = m := rfl
@[simp] theorem add_succ (n m : Carrier) : add (succ n) m = succ (add n m) := rfl

theorem toNat_add_fromNat (n : Nat) (m : Carrier) :
    toNat (add (fromNat n) m) = n + toNat m := by
  induction n with
  | zero => exact (Nat.zero_add (toNat m)).symm
  | succ n ih =>
    change Nat.succ (toNat (add (fromNat n) m)) = Nat.succ n + toNat m
    rw [ih, Nat.succ_add]

theorem toNat_add (n m : Carrier) : toNat (add n m) = toNat n + toNat m := by
  simpa only [fromNat_toNat] using toNat_add_fromNat (toNat n) m

end Natural

namespace Vectors

inductive DataSort where
  | length | payload
  deriving DecidableEq

def value (A : Type) : DataSort → Type
  | .length => Natural.Carrier
  | .payload => A

inductive LengthVariable : List DataSort → Type where
  | here {context} : LengthVariable (.length :: context)
  | there {context sort} : LengthVariable context → LengthVariable (sort :: context)

def LengthVariable.lookup {A : Type} : {context : List DataSort} →
    LengthVariable context → Env (value A) context → Natural.Carrier
  | _, .here, environment => environment.1
  | _, .there reference, environment => reference.lookup environment.2

inductive IndexExpr (context : List DataSort) where
  | zero
  | variable : LengthVariable context → IndexExpr context
  | successor : IndexExpr context → IndexExpr context
  | addition : IndexExpr context → IndexExpr context → IndexExpr context

noncomputable def IndexExpr.eval {A : Type} {context : List DataSort} :
    IndexExpr context → Env (value A) context → Natural.Carrier
  | .zero, _ => Natural.zero
  | .variable reference, environment => reference.lookup environment
  | .successor expression, environment => Natural.succ (expression.eval environment)
  | .addition left right, environment => Natural.add (left.eval environment) (right.eval environment)

/-- The previously admitted natural carrier supplies both index and data sorts. -/
noncomputable def interface (A : Type) : Interface where
  SortCode := DataSort
  Value := value A
  Index := Natural.Carrier
  IndexExpr := IndexExpr
  evalIndex := IndexExpr.eval

def nilCode (A : Type) : Code (interface A) [] := .result .zero
def consCode (A : Type) : Code (interface A) [] :=
  .data .length (.data .payload
    (.recursive (.variable (.there .here))
      (.result (.successor (.variable (.there .here))))))

def constructors (A : Type) : List (NamedConstructor (interface A) []) :=
  [⟨"Nil", nilCode A⟩, ⟨"Cons", consCode A⟩]

def admitted (A : Type) : IndexedInductive.Admitted (interface A) [] :=
  ⟨constructors A, by change (["Nil", "Cons"] : List String).Nodup; decide⟩

def source (A : Type) : IndexedInductive.Document (interface A) [] := .bundle
  [.declaration ⟨"Nil", .result .zero⟩,
   .declaration ⟨"Cons", .data .length (.data .payload
     (.recursive (.variable (.there .here))
       (.result (.successor (.variable (.there .here))))))⟩]

theorem source_admitted (A : Type) :
    IndexedInductive.admit? (source A) = some (admitted A) :=
  IndexedInductive.admit_quote (admitted A)

noncomputable abbrev polynomial (A : Type) := (admitted A).polynomial
abbrev Vector (A : Type) (length : Natural.Carrier) :=
  (admitted A).Family PUnit.unit length

noncomputable def nil {A : Type} : Vector A Natural.zero := by
  refine (admitted A).construct ⟨⟨0, by change 0 < 2; decide⟩, ?_⟩
  change ULift (PLift (Natural.zero = Natural.zero))
  exact ⟨⟨rfl⟩⟩

noncomputable def cons {A : Type} {length : Natural.Carrier} (head : A)
    (tail : Vector A length) : Vector A (Natural.succ length) := by
  refine (admitted A).construct ⟨⟨1, by change 1 < 2; decide⟩, ?_⟩
  change Σ n : Natural.Carrier, Σ _ : A,
    Vector A n × ULift (PLift (Natural.succ n = Natural.succ length))
  exact ⟨length, head, tail, ⟨⟨rfl⟩⟩⟩

abbrev ListVector (A : Type) (length : Natural.Carrier) :=
  { xs : List A // xs.length = Natural.toNat length }

noncomputable def listMethods (A : Type) :
    Algebra.Displayed (Algebra.initial (polynomial A))
      (fun _ length _ => ListVector A length) where
  act := by
    intro _ length shape children hypotheses
    rcases shape with ⟨occurrence, shape⟩
    refine Fin.cases ?_ (fun occurrence => ?_) occurrence shape children hypotheses
    · intro shape _children _hypotheses
      exact ⟨[], congrArg Natural.toNat shape.down.down⟩
    · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
      intro shape _children hypotheses
      rcases shape with ⟨tailLength, head, equation⟩
      exact ⟨head :: (hypotheses none).val,
        (congrArg Nat.succ (hypotheses none).property).trans
          (congrArg Natural.toNat equation.down.down)⟩

noncomputable def toList {A : Type} {length : Natural.Carrier}
    (vector : Vector A length) : ListVector A length :=
  ((admitted A).eliminate (listMethods A)).toFun PUnit.unit length vector

@[simp] theorem toList_nil {A : Type} : toList (nil (A := A)) = ⟨[], rfl⟩ := rfl
@[simp] theorem toList_cons {A : Type} {length : Natural.Carrier}
    (head : A) (tail : Vector A length) :
    (toList (cons head tail)).val = head :: (toList tail).val := rfl

noncomputable def fromList {A : Type} : (xs : List A) → Vector A (Natural.fromNat xs.length)
  | [] => nil
  | head :: tail => cons head (fromList tail)

theorem toList_fromList {A : Type} (xs : List A) :
    (toList (fromList xs)).val = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons head) ih

noncomputable def fromListVector {A : Type} {length : Natural.Carrier}
    (vector : ListVector A length) : Vector A length :=
  ((congrArg Natural.fromNat vector.property).trans
    (Natural.fromNat_toNat length)) ▸ fromList vector.val

noncomputable def listCons {A : Type} {length : Natural.Carrier}
    (head : A) (tail : ListVector A length) : ListVector A (Natural.succ length) :=
  ⟨head :: tail.val, congrArg Nat.succ tail.property⟩

theorem fromListVector_listCons {A : Type} {length : Natural.Carrier}
    (head : A) (tail : ListVector A length) :
    fromListVector (listCons head tail) = cons head (fromListVector tail) := by
  rcases tail with ⟨tail, equation⟩
  have same : Natural.fromNat tail.length = length :=
    (congrArg Natural.fromNat equation).trans (Natural.fromNat_toNat length)
  cases same
  simp only [fromListVector, listCons, fromList]

theorem toList_fromListVector {A : Type} {length : Natural.Carrier}
    (vector : ListVector A length) : toList (fromListVector vector) = vector := by
  rcases vector with ⟨values, equation⟩
  have same : Natural.fromNat values.length = length :=
    (congrArg Natural.fromNat equation).trans (Natural.fromNat_toNat length)
  cases same
  apply Subtype.ext
  exact toList_fromList values

theorem fromListVector_toList {A : Type} {length : Natural.Carrier}
    (vector : Vector A length) : fromListVector (toList vector) = vector := by
  refine @Fix.rec _ _ (polynomial A) PUnit.unit
    (fun _ tree => fromListVector (toList tree) = tree) ?_ length vector
  intro _length shape children hypotheses
  rcases shape with ⟨occurrence, shape⟩
  revert shape children hypotheses
  refine Fin.cases ?_ (fun occurrence => ?_) occurrence
  · intro shape children _hypotheses
    rcases shape with ⟨⟨equation⟩⟩
    cases equation
    change nil = Fix.roll _ children
    change Fix.roll _ _ = Fix.roll _ children
    apply congrArg (Fix.roll _)
    funext position
    exact PEmpty.elim position
  · refine Fin.cases ?_ (fun impossible => Fin.elim0 impossible) occurrence
    intro shape children hypotheses
    rcases shape with ⟨tailLength, head, ⟨⟨equation⟩⟩⟩
    cases equation
    change fromListVector (listCons head (toList (children none))) = Fix.roll _ children
    apply (fromListVector_listCons head (toList (children none))).trans
    apply (congrArg (cons head) (hypotheses none)).trans
    change Fix.roll _ _ = Fix.roll _ children
    apply congrArg (Fix.roll _)
    funext position
    cases position with
    | none => rfl
    | some impossible => exact PEmpty.elim impossible

noncomputable def listEquiv (A : Type) (length : Natural.Carrier) :
    Vector A length ≃ ListVector A length where
  toFun := toList
  invFun := fromListVector
  left_inv := fromListVector_toList
  right_inv := toList_fromListVector

/-- The existing dependent-vector client uses the independently decoded index. -/
noncomputable def representation (A : Type) (length : Natural.Carrier) :
    Vector A length ≃ VectorExample.VectorP A (Natural.toNat length) :=
  (listEquiv A length).trans
    ((VectorRepresentation.listRepresentation A).toEquiv .star (Natural.toNat length)).symm

@[simp] theorem representation_nil {A : Type} :
    representation A Natural.zero nil = VectorExample.nil := rfl

@[simp] theorem representation_cons {A : Type} {length : Natural.Carrier}
    (head : A) (tail : Vector A length) :
    representation A (Natural.succ length) (cons head tail) =
      VectorExample.cons head (representation A length tail) := by
  change VectorRepresentation.decode (toList (cons head tail)) =
    VectorExample.cons head (VectorRepresentation.decode (toList tail))
  have same : toList (cons head tail) =
      VectorRepresentation.listCons head (toList tail) :=
    Subtype.ext (toList_cons head tail)
  exact (congrArg (VectorRepresentation.decode (n := Natural.toNat length + 1)) same).trans
    (VectorRepresentation.decode_cons head (toList tail))

@[simp] theorem storage_representation {A : Type} {length : Natural.Carrier}
    (vector : Vector A length) :
    VectorRepresentation.encode (Natural.toNat length)
      (representation A length vector) = toList vector :=
  VectorRepresentation.encode_decode (toList vector)

@[simp] theorem storage_representation_symm {A : Type} {length : Natural.Carrier}
    (vector : VectorExample.VectorP A (Natural.toNat length)) :
    toList ((representation A length).symm vector) =
      VectorRepresentation.encode (Natural.toNat length) vector :=
  toList_fromListVector (VectorRepresentation.encode (Natural.toNat length) vector)

/-- Reuse the existing append, transporting its output to the authored sum. -/
noncomputable def append {A : Type} {n m : Natural.Carrier}
    (left : Vector A n) (right : Vector A m) : Vector A (Natural.add n m) :=
  (representation A (Natural.add n m)).symm
    (cast (congrArg (VectorExample.VectorP A) (Natural.toNat_add n m).symm)
      (NaturalVectorCoherence.append
        (representation A n left) (representation A m right)))

theorem append_representation {A : Type} {n m : Natural.Carrier}
    (left : Vector A n) (right : Vector A m) :
    representation A (Natural.add n m) (append left right) =
      cast (congrArg (VectorExample.VectorP A) (Natural.toNat_add n m).symm)
        (NaturalVectorCoherence.append
          (representation A n left) (representation A m right)) :=
  (representation A (Natural.add n m)).apply_symm_apply _

theorem append_payload {A : Type} {n m : Natural.Carrier}
    (left : Vector A n) (right : Vector A m) :
    (toList (append left right)).val = (toList left).val ++ (toList right).val := by
  unfold append
  rw [storage_representation_symm]
  apply (VectorRepresentation.encode_cast (Natural.toNat_add n m).symm _).trans
  change (VectorRepresentation.encode (Natural.toNat n + Natural.toNat m)
    (VectorRepresentation.append (representation A n left) (representation A m right))).val = _
  rw [VectorRepresentation.append_payload, storage_representation, storage_representation]

theorem append_length {A : Type} {n m : Natural.Carrier}
    (left : Vector A n) (right : Vector A m) :
    (toList (append left right)).val.length = Natural.toNat n + Natural.toNat m := by
  exact (toList (append left right)).property.trans (Natural.toNat_add n m)

@[simp] theorem append_nil {A : Type} {m : Natural.Carrier}
    (right : Vector A m) : append nil right = right := by
  apply (listEquiv A m).injective
  apply Subtype.ext
  exact append_payload nil right

@[simp] theorem append_cons {A : Type} {n m : Natural.Carrier}
    (head : A) (left : Vector A n) (right : Vector A m) :
    append (cons head left) right = cons head (append left right) := by
  apply (listEquiv A (Natural.succ (Natural.add n m))).injective
  apply Subtype.ext
  change (toList (append (cons head left) right)).val =
    head :: (toList (append left right)).val
  rw [append_payload, append_payload]
  rfl

/-- Observations use the same translated value, including its dependent index. -/
theorem append_observation_iff {A : Type} {n m : Natural.Carrier}
    (observation : VectorExample.VectorP A (Natural.toNat (Natural.add n m)) → Prop)
    (left : Vector A n) (right : Vector A m) :
    observation (representation A (Natural.add n m) (append left right)) ↔
      observation (cast (congrArg (VectorExample.VectorP A) (Natural.toNat_add n m).symm)
        (NaturalVectorCoherence.append
          (representation A n left) (representation A m right))) := by
  rw [append_representation]

theorem append_two_payloads {A : Type} (a b : A) :
    (toList (append (cons a nil) (cons b nil))).val = [a, b] := by
  rw [append_payload]
  rfl

theorem reversed_payload_rejected {A : Type} {a b : A} (different : a ≠ b) :
    (toList (append (cons a nil) (cons b nil))).val ≠ [b, a] := by
  rw [append_two_payloads]
  intro same
  exact different (List.cons.inj same).1

theorem missing_payload_rejected {A : Type} (a : A) :
    (toList (cons a nil)).val ≠ [] := List.cons_ne_nil _ _

theorem nil_at_wrong_index_rejected (A : Type) :
    ¬ Nonempty (Description.Shape (nilCode A) PUnit.unit
      (Natural.succ Natural.zero)) := by
  rintro ⟨equation⟩
  exact Natural.succ_ne_zero Natural.zero equation.down.down.symm

theorem boolean_append_control :
    (toList (append (cons true nil) (cons false nil))).val = [true, false] :=
  append_two_payloads true false

theorem boolean_reversal_control :
    (toList (append (cons true nil) (cons false nil))).val ≠ [false, true] :=
  reversed_payload_rejected (by decide)

end Vectors

#print axioms Natural.source_admitted
#print axioms Natural.fromNat_toNat
#print axioms Natural.toNat_add
#print axioms Vectors.source_admitted
#print axioms Vectors.fromListVector_toList
#print axioms Vectors.representation_cons
#print axioms Vectors.append_payload
#print axioms Vectors.append_length
#print axioms Vectors.append_cons
#print axioms Vectors.reversed_payload_rejected
#print axioms Vectors.nil_at_wrong_index_rejected

end Mettapedia.GSLT.LanguageDef.IndexedInductiveNatVec
