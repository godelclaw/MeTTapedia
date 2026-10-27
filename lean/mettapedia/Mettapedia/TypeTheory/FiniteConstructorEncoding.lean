import Mettapedia.TypeTheory.IndexedPolynomialDescription

/-!
# Function encodings of finite constructor data

Each constructor selects one typed predicate handler and supplies its complete
data tuple. Every predicate on the source sum has such a handler family, which
proves that encoding retains the constructor occurrence and every field. The
target function space also contains values outside the image; its image guard
is therefore essential, including for empty source families.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.FiniteConstructorEncoding

open IndexedPolynomial.Description
universe u s
variable {SortCode : Type s} (Value : SortCode → Type u)

def Curried (Result : Type u) : List SortCode → Type u
  | [] => Result
  | sort :: rest => Value sort → Curried Result rest

def apply {Result : Type u} : (fields : List SortCode) →
    Curried Value Result fields → Env Value fields → Result
  | [], value, _ => value
  | _ :: rest, function, data => apply rest (function data.1) data.2

def curry {Result : Type u} : (fields : List SortCode) →
    (Env Value fields → Result) → Curried Value Result fields
  | [], function => function PUnit.unit
  | _ :: rest, function => fun first => curry rest (fun data => function (first, data))

theorem apply_curry {Result : Type u} (fields : List SortCode)
    (function : Env Value fields → Result) (data : Env Value fields) :
    apply Value fields (curry Value fields function) data = function data := by
  induction fields with
  | nil => cases data; rfl
  | cons sort rest hypotheses =>
      exact hypotheses (fun remaining => function (data.1, remaining)) data.2

theorem curry_apply {Result : Type u} (fields : List SortCode)
    (function : Curried Value Result fields) :
    curry Value fields (apply Value fields function) = function := by
  induction fields with
  | nil => rfl
  | cons sort rest hypotheses =>
      funext first
      exact hypotheses (function first)

def curryEquivalence {Result : Type u} (fields : List SortCode) :
    (Env Value fields → Result) ≃ Curried Value Result fields where
  toFun := curry Value fields
  invFun := apply Value fields
  left_inv := fun function => funext (apply_curry Value fields function)
  right_inv := curry_apply Value fields

abbrev Signature := List (List SortCode)
abbrev Data (signature : Signature (SortCode := SortCode)) :=
  Σ occurrence : Fin signature.length, Env Value (signature.get occurrence)

abbrev Handler (fields : List SortCode) := Curried Value (ULift.{u} Prop) fields
abbrev Handlers (signature : Signature (SortCode := SortCode)) := Env (Handler Value) signature
abbrev Payload (signature : Signature (SortCode := SortCode)) :=
  Curried (Handler Value) (ULift.{u} Prop) signature

def select : (signature : Signature (SortCode := SortCode)) →
    (occurrence : Fin signature.length) → Handlers Value signature →
      Handler Value (signature.get occurrence)
  | [], occurrence, _ => Fin.elim0 occurrence
  | _ :: _, ⟨0, _⟩, handlers => handlers.1
  | _ :: rest, ⟨n + 1, bound⟩, handlers =>
      select rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩ handlers.2

def encode (signature : Signature (SortCode := SortCode))
    (data : Data Value signature) : Payload Value signature :=
  curry (Handler Value) signature (fun handlers =>
    apply Value (signature.get data.1) (select Value signature data.1 handlers) data.2)

def observe : (signature : Signature (SortCode := SortCode)) →
    (Data Value signature → Prop) → Handlers Value signature
  | [], _ => PUnit.unit
  | fields :: rest, predicate =>
      (curry Value fields (fun data => ULift.up (predicate ⟨⟨0, Nat.zero_lt_succ _⟩, data⟩)),
       observe rest (fun data => predicate
         ⟨⟨data.1.val + 1, Nat.succ_lt_succ data.1.isLt⟩, data.2⟩))

theorem select_observe (signature : Signature (SortCode := SortCode))
    (predicate : Data Value signature → Prop) (data : Data Value signature) :
    apply Value (signature.get data.1)
      (select Value signature data.1 (observe Value signature predicate)) data.2 = ULift.up (predicate data) := by
  induction signature with
  | nil => exact Fin.elim0 data.1
  | cons fields rest hypotheses =>
      rcases data with ⟨⟨n, bound⟩, data⟩
      cases n with
      | zero => exact apply_curry Value fields _ data
      | succ n =>
          exact hypotheses (fun item => predicate
            ⟨⟨item.1.val + 1, Nat.succ_lt_succ item.1.isLt⟩, item.2⟩)
            ⟨⟨n, Nat.lt_of_succ_lt_succ bound⟩, data⟩

theorem encode_observe (signature : Signature (SortCode := SortCode))
    (predicate : Data Value signature → Prop) (data : Data Value signature) :
    apply (Handler Value) signature (encode Value signature data)
      (observe Value signature predicate) = ULift.up (predicate data) := by
  rw [encode, apply_curry]
  exact select_observe Value signature predicate data

theorem encode_injective (signature : Signature (SortCode := SortCode)) :
    Function.Injective (encode Value signature) := by
  intro first second same
  have observed := congrArg (fun payload => apply (Handler Value) signature payload
    (observe Value signature (fun data => data = first))) same
  rw [encode_observe, encode_observe] at observed
  exact ((congrArg ULift.down observed).mp rfl).symm

def Valid (signature : Signature (SortCode := SortCode)) (payload : Payload Value signature) : Prop :=
  ∃ data, encode Value signature data = payload

noncomputable def representation (signature : Signature (SortCode := SortCode)) :
    Data Value signature ≃ {payload : Payload Value signature // Valid Value signature payload} where
  toFun data := ⟨encode Value signature data, data, rfl⟩
  invFun payload := payload.property.choose
  left_inv data := encode_injective Value signature (Exists.choose_spec (show Valid Value signature
    (encode Value signature data) from ⟨data, rfl⟩))
  right_inv payload := Subtype.ext payload.property.choose_spec

def unused (signature : Signature (SortCode := SortCode)) : Payload Value signature :=
  curry (Handler Value) signature (fun _ => ULift.up False)

theorem unused_not_valid (signature : Signature (SortCode := SortCode)) :
    ¬ Valid Value signature (unused Value signature) := by
  rintro ⟨data, same⟩
  have observed := congrArg (fun payload => apply (Handler Value) signature payload
    (observe Value signature (fun _ => True))) same
  rw [encode_observe, unused, apply_curry] at observed
  exact (congrArg ULift.down observed).mp True.intro

def encodeOption (signature : Signature (SortCode := SortCode)) :
    Option (Data Value signature) → Payload Value signature
  | none => unused Value signature
  | some data => encode Value signature data

theorem encodeOption_injective (signature : Signature (SortCode := SortCode)) :
    Function.Injective (encodeOption Value signature) := by
  intro first second same
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some data => exact False.elim (unused_not_valid Value signature ⟨data, same.symm⟩)
  | some first =>
      cases second with
      | none => exact False.elim (unused_not_valid Value signature ⟨first, same⟩)
      | some second => exact congrArg some (encode_injective Value signature same)

theorem empty_image (signature : Signature (SortCode := SortCode))
    (empty : IsEmpty (Data Value signature)) :
    ∀ payload, ¬ Valid Value signature payload := by
  rintro payload ⟨data, _⟩
  exact empty.false data

namespace Controls

inductive DataSort where | number | flag
def fieldValue : DataSort → Type
  | .number => Nat
  | .flag => Bool

def signature : Signature (SortCode := DataSort) := [[.number, .flag], [.number, .flag]]
def first : Data fieldValue signature := ⟨⟨0, by decide⟩, (2 : Nat), true, PUnit.unit⟩
def otherConstructor : Data fieldValue signature := ⟨⟨1, by decide⟩, (2 : Nat), true, PUnit.unit⟩
def otherField : Data fieldValue signature := ⟨⟨0, by decide⟩, (3 : Nat), true, PUnit.unit⟩

theorem first_roundtrip :
    (representation fieldValue signature).symm (representation fieldValue signature first) = first :=
  (representation fieldValue signature).symm_apply_apply first

theorem constructor_distinguished : encode fieldValue signature first ≠ encode fieldValue signature otherConstructor := by
  intro same
  have indices := congrArg (fun data => data.1.val) (encode_injective fieldValue signature same)
  change (0 : Nat) = 1 at indices
  cases indices

theorem field_distinguished : encode fieldValue signature first ≠ encode fieldValue signature otherField := by
  intro same
  have data := encode_injective fieldValue signature same
  have tuple := Sigma.mk.inj data
  have unequal : (2 : Nat) = 3 := congrArg Prod.fst (eq_of_heq tuple.2)
  cases unequal

theorem unused_refused : ¬ Valid fieldValue signature (unused fieldValue signature) :=
  unused_not_valid fieldValue signature

theorem no_constructors : ∀ payload, ¬ Valid fieldValue [] payload :=
  empty_image fieldValue [] ⟨fun data => Fin.elim0 data.1⟩

end Controls

#print axioms encode_injective
#print axioms representation
#print axioms unused_not_valid
#print axioms encodeOption_injective
#print axioms Controls.constructor_distinguished
#print axioms Controls.field_distinguished

end Mettapedia.TypeTheory.FiniteConstructorEncoding
