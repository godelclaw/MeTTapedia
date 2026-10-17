import Mettapedia.Languages.OpenTheory.Substitution
import Mettapedia.Languages.OpenTheory.Sequent
import Mettapedia.Languages.OpenTheory.BindingRules
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Structural storage sizes for shared simple type syntax

This account includes UTF-8 bytes in every name, binary digits of numeric
fields, symbol provenance, source type annotations, current hypotheses and
axiom-dependency sequents. Proof fields contribute no stored payload.

Constructor and list delimiters each contribute one unit. Binary digits are
counted individually, so multiplying this account by eight gives a conservative
bit account even if digits and delimiters are stored as whole octets. This
module states size laws; it makes no claim about running time.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.StorageSize

/-- A binary numeric field with its terminating delimiter. -/
def nat (value : Nat) : Nat := 1 + (Nat.digits 2 value).length

/-- Raw UTF-8 bytes together with a string delimiter. -/
def string (value : String) : Nat := 1 + value.utf8ByteSize

/-- A structural list with its end delimiter. -/
def list {α : Type} (size : α → Nat) (values : List α) : Nat :=
  1 + (values.map size).sum

def name (value : Name) : Nat :=
  1 + list string value.namespaceComponents + string value.component

mutual
  def ty : Ty → Nat
    | .var value => 1 + name value
    | .op operator arguments => 1 + typeOp operator + types arguments
  termination_by value => sizeOf value

  def types : List Ty → Nat
    | [] => 1
    | value :: values => ty value + types values
  termination_by values => sizeOf values

  def typeOp : TypeOp → Nat
    | .mk value provenance => 1 + name value + typeOpProvenance provenance
  termination_by value => sizeOf value

  def typeOpProvenance : TypeOpProvenance → Nat
    | .undefined => 1
    | .defined predicate parameters => 1 + sourceTerm predicate + list name parameters
  termination_by value => sizeOf value

  def constant : Const → Nat
    | .mk value provenance => 1 + name value + constantProvenance provenance
  termination_by value => sizeOf value

  def constantProvenance : ConstProvenance → Nat
    | .undefined => 1
    | .defined definition => 1 + sourceTerm definition
    | .abstraction operator | .representation operator => 1 + typeOp operator
  termination_by value => sizeOf value

  def sourceTerm : SourceTerm → Nat
    | .const symbol annotation => 1 + constant symbol + ty annotation
    | .var value annotation => 1 + name value + ty annotation
    | .app function argument => 1 + sourceTerm function + sourceTerm argument
    | .abs binder domain body => 1 + name binder + ty domain + sourceTerm body
  termination_by value => sizeOf value
end

def sourceVar (value : SourceVar) : Nat := 1 + name value.name + ty value.ty

def term : DBTerm → Nat
  | .const symbol annotation => 1 + constant symbol + ty annotation
  | .free value => 1 + sourceVar value
  | .bound index => 1 + nat index
  | .app function argument => 1 + term function + term argument
  | .abs domain body => 1 + ty domain + term body

def canonical (value : CanonicalTerm) : Nat := 1 + term value.term + ty value.ty

def checkedSource (value : CheckedSourceTerm) : Nat := 1 + sourceTerm value.source + ty value.ty

/-- Set serialization stores every actual element once. -/
def finset {α : Type} (size : α → Nat) (values : Finset α) : Nat :=
  1 + ∑ value ∈ values, size value

def sequent (value : Sequent) : Nat :=
  1 + finset canonical value.hyp + canonical value.concl

def theoremData (value : Theorem) : Nat :=
  1 + finset sequent value.axioms + sequent value.sequent

@[simp] theorem list_nil {α : Type} (size : α → Nat) : list size [] = 1 := rfl
@[simp] theorem list_cons {α : Type} (size : α → Nat) (value : α) (values : List α) :
    list size (value :: values) = size value + list size values := by
  simp [list]; omega

theorem list_append {α : Type} (size : α → Nat) (left right : List α) :
    list size (left ++ right) + 1 = list size left + list size right := by
  simp [list, List.sum_append]; omega

theorem list_member_le {α : Type} (size : α → Nat) {value : α} {values : List α}
    (member : value ∈ values) : size value < list size values := by
  induction values with
  | nil => simp at member
  | cons first rest ih =>
      rw [list_cons]
      rcases List.mem_cons.mp member with equal | inside
      · subst value; have positive : 0 < list size rest := by unfold list; omega
        omega
      · have bounded := ih inside
        omega

theorem name_namespace_le (value : Name) : value.namespaceComponents.length < name value := by
  have sized : value.namespaceComponents.length ≤ (value.namespaceComponents.map string).sum := by
    induction value.namespaceComponents with
    | nil => simp
    | cons first rest ih =>
        simp only [List.length_cons, List.map_cons, List.sum_cons]
        have positive : 1 ≤ string first := by unfold string; omega
        omega
  unfold name list
  omega

@[simp] theorem finset_empty {α : Type} (size : α → Nat) : finset size ∅ = 1 := by simp [finset]
@[simp] theorem finset_singleton {α : Type} [DecidableEq α] (size : α → Nat) (value : α) :
    finset size {value} = 1 + size value := by simp [finset]

theorem finset_mono {α : Type} (size : α → Nat) {left right : Finset α}
    (included : left ⊆ right) : finset size left ≤ finset size right := by
  unfold finset
  exact Nat.add_le_add_left (Finset.sum_le_sum_of_subset included) 1

theorem finset_union_le {α : Type} [DecidableEq α] (size : α → Nat) (left right : Finset α) :
    finset size (left ∪ right) ≤ finset size left + finset size right := by
  unfold finset
  have counted := Finset.sum_union_inter (s₁ := left) (s₂ := right) (f := size)
  omega


/-- Every serialized term has a constructor boundary. -/
theorem term_positive (value : DBTerm) : 1 ≤ term value := by
  cases value <;> simp only [term] <;> omega

theorem canonical_term_le (value : CanonicalTerm) : term value.term ≤ canonical value := by
  unfold canonical
  omega

theorem canonical_type_le (value : CanonicalTerm) : ty value.ty ≤ canonical value := by
  unfold canonical
  omega

theorem sequent_conclusion_le (value : Sequent) : canonical value.concl ≤ sequent value := by
  unfold sequent
  omega

theorem theorem_conclusion_le (value : Theorem) : canonical value.sequent.concl ≤ theoremData value := by
  unfold theoremData sequent
  omega

theorem theorem_hypotheses_le (value : Theorem) : finset canonical value.sequent.hyp ≤ theoremData value := by
  unfold theoremData sequent
  omega

theorem theorem_axioms_le (value : Theorem) : finset sequent value.axioms ≤ theoremData value := by
  unfold theoremData
  omega

@[simp] theorem emptyResult_size (hyp : Finset CanonicalTerm) (conclusion : CanonicalTerm) :
    theoremData (Theorem.emptyResult hyp conclusion) = 3 + finset canonical hyp + canonical conclusion := by
  simp [theoremData, sequent, Theorem.emptyResult]
  omega

/-- Replacing only the conclusion preserves the complete stored axiom and
hypothesis portions. -/
theorem preserveAxiomsResult_size (input : Theorem) (conclusion : CanonicalTerm) :
    theoremData (Theorem.preserveAxiomsResult input input.sequent.hyp conclusion) +
      canonical input.sequent.concl = theoremData input + canonical conclusion := by
  simp only [theoremData, sequent, Theorem.preserveAxiomsResult]
  omega

/-- Unary results may remove hypotheses without increasing their retained
payload beyond the input and the new conclusion. -/
theorem preserveAxiomsResult_le (input : Theorem) (hyp : Finset CanonicalTerm)
    (conclusion : CanonicalTerm) (contained : hyp ⊆ input.sequent.hyp) :
    theoremData (Theorem.preserveAxiomsResult input hyp conclusion) ≤
      theoremData input + canonical conclusion := by
  have hypotheses := finset_mono canonical contained
  simp only [theoremData, sequent, Theorem.preserveAxiomsResult]
  omega

/-- Binary results retain both provenance sets. Shared tags are stored once;
the upper bound still charges both incoming complete theorem payloads. -/
theorem unionResult_le (left right : Theorem) (hyp : Finset CanonicalTerm)
    (conclusion : CanonicalTerm) (contained : hyp ⊆ left.sequent.hyp ∪ right.sequent.hyp) :
    theoremData (Theorem.unionResult left right hyp conclusion) ≤
      theoremData left + theoremData right + canonical conclusion := by
  have tags := finset_union_le sequent left.axioms right.axioms
  have hypotheses := (finset_mono canonical contained).trans
    (finset_union_le canonical left.sequent.hyp right.sequent.hyp)
  simp only [theoremData, sequent, Theorem.unionResult]
  omega

/-- Stored child terms and binder types are part of the surrounding term's
payload, regardless of whether operational rules inspect them. -/
theorem application_function_le (function argument : DBTerm) : term function ≤ term (.app function argument) := by
  simp only [term]
  omega

theorem application_argument_le (function argument : DBTerm) : term argument ≤ term (.app function argument) := by
  simp only [term]
  omega

theorem abstraction_body_le (domain : Ty) (body : DBTerm) : term body ≤ term (.abs domain body) := by
  simp only [term]
  omega

theorem abstraction_type_le (domain : Ty) (body : DBTerm) : ty domain ≤ term (.abs domain body) := by
  simp only [term]
  omega

theorem functionType_storage (domain codomain : Ty) :
    ty (Ty.function domain codomain) =
      9 + ty domain + ty codomain := by
  rw [Ty.function, ty, types,
    types, types]
  have arrow : typeOp TypeOp.function = 7 := by decide +kernel
  rw [arrow]
  omega

theorem boolType_storage : ty Ty.bool = 11 := by decide +kernel

theorem equalityConstant_storage : constant Const.equality = 6 := by decide +kernel

end Mettapedia.Languages.OpenTheory.StorageSize
