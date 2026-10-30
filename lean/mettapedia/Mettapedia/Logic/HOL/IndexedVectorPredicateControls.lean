import Mettapedia.Logic.HOL.IndexedVectorPredicate
import Mettapedia.Logic.HOL.HOLLightStandardTheory

/-!
# Nonconstant models and separating controls for indexed membership

Natural indices and ordered Boolean lists interpret the constructor algebra.
The derived induction program proves length and element-admissibility
invariants of the actual HOL least predicate. Incorrect indices and forbidden
heads are consequently refuted, including empty element predicates.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.Logic.HOL.IndexedVectorPredicate.Controls

inductive BaseSort where | number | element | vector
  deriving DecidableEq
abbrev number : Ty BaseSort := .base .number
abbrev element : Ty BaseSort := .base .element
abbrev vector : Ty BaseSort := .base .vector

inductive Const : Ty BaseSort → Type where
  | zero : Const number
  | successor : Const (number ⇒ number)
  | nil : Const vector
  | cons : Const (number ⇒ element ⇒ vector ⇒ vector)
  | truth : Const element
  | falsity : Const element
  | allowed : Const (element ⇒ .prop)
  | lengthProperty : Const (number ⇒ vector ⇒ .prop)
  | allowedProperty : Const (number ⇒ vector ⇒ .prop)
  | queryIndex : Const number
  | queryVector : Const vector

def signature : Signature Const :=
  ⟨number, element, vector, .const .zero, .const .successor, .const .nil, .const .cons⟩
def elements : ClosedTerm Const (element ⇒ .prop) := .const .allowed
def lengthProperty : ClosedTerm Const signature.Property := .const .lengthProperty
def allowedProperty : ClosedTerm Const signature.Property := .const .allowedProperty
def queryIndex : ClosedTerm Const number := .const .queryIndex
def queryVector : ClosedTerm Const vector := .const .queryVector

def lengthProgram := signature.inductionImplication (Δ := []) elements lengthProperty queryIndex queryVector
def allowedProgram := signature.inductionImplication (Δ := []) elements allowedProperty queryIndex queryVector

theorem length_program_free : lengthProgram.FunctionExtensionalityFree := signature.inductionImplication_free _ _ _ _
theorem allowed_program_free : allowedProgram.FunctionExtensionalityFree := signature.inductionImplication_free _ _ _ _

def one : ClosedTerm Const number := .app signature.successor signature.zero
def singleton : ClosedTerm Const vector := signature.consValue signature.zero (.const .truth) signature.nil
def singletonProof : ProofSyntax Const [.app elements (.const .truth)]
    (signature.member elements one singleton) :=
  signature.cons_member elements signature.zero (.const .truth) signature.nil (.hyp 0)
    (signature.nil_member elements)
def singletonProgram : ProofSyntax Const [] (.imp (.app elements (.const .truth))
    (signature.member elements one singleton)) := .impI singletonProof

theorem singleton_program_free : singletonProgram.FunctionExtensionalityFree :=
  signature.cons_member_free _ _ _ _ _ _ True.intro (signature.nil_member_free _)

def carrier : BaseSort → Type 1
  | .number => ULift.{1} Nat
  | .element => ULift.{1} Bool
  | .vector => ULift.{1} (List Bool)

def meaning (permitted : Bool → Prop) (selectedIndex : Nat) (selectedVector : List Bool) :
    {type : Ty BaseSort} → Const type → Ty.denote.{0,0} carrier type
  | _, .zero => .up 0
  | _, .successor => fun n => .up (n.down + 1)
  | _, .nil => .up []
  | _, .cons => fun _ h t => .up (h.down :: t.down)
  | _, .truth => .up true
  | _, .falsity => .up false
  | _, .allowed => fun h => .up (permitted h.down)
  | _, .lengthProperty => fun n v => .up (n.down = v.down.length)
  | _, .allowedProperty => fun _ v => .up (∀ h ∈ v.down, permitted h)
  | _, .queryIndex => .up selectedIndex
  | _, .queryVector => .up selectedVector

def model (permitted : Bool → Prop) (selectedIndex : Nat) (selectedVector : List Bool) : HenkinModel.{0,0,0} BaseSort Const :=
  .standard carrier (meaning permitted selectedIndex selectedVector)

theorem length_base (permitted : Bool → Prop) (n : Nat) (values : List Bool) :
    (model permitted n values).models (PredicatePair.holds lengthProperty signature.zero signature.nil) := rfl

theorem length_step (permitted : Bool → Prop) (n : Nat) (values : List Bool) :
    (model permitted n values).models (signature.stepCondition elements lengthProperty) := by
  intro index _ head _ tail _ _ _ length
  change index.down = tail.down.length at length
  change index.down + 1 = (head.down :: tail.down).length
  simpa using congrArg Nat.succ length

theorem membership_length (permitted : Bool → Prop) (n : Nat) (values : List Bool)
    (member : (model permitted n values).models (signature.member elements queryIndex queryVector)) :
    n = values.length := by
  have valid := Soundness.extTheorem_sound lengthProgram.erase (model permitted n values)
    ((model permitted n values).functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
  exact valid (length_base permitted n values) (length_step permitted n values) member

theorem allowed_base (permitted : Bool → Prop) (n : Nat) (values : List Bool) :
    (model permitted n values).models (PredicatePair.holds allowedProperty signature.zero signature.nil) := by
  intro item present
  cases present

theorem allowed_step (permitted : Bool → Prop) (n : Nat) (values : List Bool) :
    (model permitted n values).models (signature.stepCondition elements allowedProperty) := by
  intro index _ head _ tail _ allowed _ previous
  change ∀ item ∈ tail.down, permitted item at previous
  change ∀ item ∈ head.down :: tail.down, permitted item
  intro item present
  rcases List.mem_cons.mp present with rfl | inside
  · exact allowed
  · exact previous item inside

theorem membership_elements (permitted : Bool → Prop) (n : Nat) (values : List Bool)
    (member : (model permitted n values).models (signature.member elements queryIndex queryVector)) :
    ∀ item ∈ values, permitted item := by
  have valid := Soundness.extTheorem_sound allowedProgram.erase (model permitted n values)
    ((model permitted n values).functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
  exact valid (allowed_base permitted n values) (allowed_step permitted n values) member

theorem nil_valid_for_empty_elements :
    (model (fun _ => False) 0 []).models (signature.member elements signature.zero signature.nil) :=
  Soundness.extTheorem_sound (signature.nil_member (Δ := []) elements).erase _
    ((model (fun _ => False) 0 []).functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))

theorem singleton_valid : (model (fun h => h = true) 1 [true]).models (signature.member elements one singleton) := by
  have valid := Soundness.extTheorem_sound singletonProgram.erase (model (fun h => h = true) 1 [true])
    ((model (fun h => h = true) 1 [true]).functionsRespectEqv_of_fullDomains (HenkinModel.fullDomains_standard _ _))
  exact valid rfl

theorem singleton_length_readback : 1 = ([true] : List Bool).length :=
  membership_length (fun h => h = true) 1 [true] singleton_valid

theorem singleton_elements_readback : ∀ item ∈ ([true] : List Bool), item = true :=
  membership_elements (fun h => h = true) 1 [true] singleton_valid

theorem singleton_head_allowed : (true : Bool) = true :=
  membership_elements (fun h => h = true) 1 [true] singleton_valid true (by decide)

theorem wrong_index_refused : ¬(model (fun _ => True) 1 []).models (signature.member elements queryIndex queryVector) := by
  intro member
  have impossible := membership_length _ _ _ member
  cases impossible

theorem forbidden_head_refused :
    ¬(model (fun h => h = true) 1 [false]).models (signature.member elements queryIndex queryVector) := by
  intro member
  have impossible := membership_elements _ _ _ member false (by simp)
  cases impossible

theorem empty_elements_refuse_nonempty :
    ¬(model (fun _ => False) 1 [true]).models (signature.member elements queryIndex queryVector) := by
  intro member
  exact membership_elements _ _ _ member true (by simp)

#print axioms membership_length
#print axioms membership_elements
#print axioms singleton_valid
#print axioms wrong_index_refused
#print axioms forbidden_head_refused
end Mettapedia.Logic.HOL.IndexedVectorPredicate.Controls
