import Mettapedia.Logic.HOL.RecursiveSpacePredicate
import Mettapedia.TypeTheory.RecursiveSpace

/-!
# Guard and padding controls for the positive recursive-space operator

The model uses real recursive-space trees. A zero node has no active children;
a successor node has exactly its zeroth child active. Hidden non-bottom padding
is refused even when every active child satisfies the predicate. Complementing
the recursive predicate violates monotonicity.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.RecursiveSpacePredicate.Controls

open Mettapedia.TypeTheory
abbrev Tree := RecursiveSpace.Tree Bool

inductive Base where | number | payload | space
abbrev number : Ty Base := .base .number
abbrev payload : Ty Base := .base .payload
abbrev space : Ty Base := .base .space

inductive Const : Ty Base → Type where
  | bottom : Const space
  | construct : Const (number ⇒ payload ⇒ (number ⇒ space) ⇒ space)
  | validShape : Const (number ⇒ payload ⇒ .prop)
  | active : Const (payload ⇒ number ⇒ .prop)
  | validEdge : Const (payload ⇒ number ⇒ space ⇒ .prop)

@[reducible] def signature : Signature Const :=
  ⟨number,payload,space,.const .bottom,.const .construct,.const .validShape,.const .active,.const .validEdge⟩

def shape (tag : Nat) (payload : Bool) : Prop :=
  (tag = 0 ∧ payload = false) ∨ (tag = 1 ∧ payload = true)

def active (payload : Bool) (position : Nat) : Prop := payload = true ∧ position = 0

def carrier : Base → Type 1
  | .number => ULift.{1} Nat
  | .payload => ULift.{1} Bool
  | .space => ULift.{1} Tree

@[reducible] def model : HenkinModel.{0,0,0} Base Const := .standard carrier (fun symbol => match symbol with
  | .bottom => .up RecursiveSpace.bottom
  | .construct => fun tag payload children => .up
      (RecursiveSpace.construct tag.down payload.down (fun n => (children (.up n)).down))
  | .validShape => fun tag payload => .up (shape tag.down payload.down)
  | .active => fun payload position => .up (active payload.down position.down)
  | .validEdge => fun _ _ _ => .up True)

theorem full : model.FullDomains := HenkinModel.fullDomains_standard _ _

def holds (predicate : Tree → Prop) (point : Tree) : Prop :=
  (Signature.denotes model signature.operator (fun value => .up (predicate value.down)) (.up point)).down

def step (predicate : Tree → Prop) (point : Tree) : Prop :=
  ∃ tag payload children, shape tag payload ∧ point = RecursiveSpace.construct tag payload children ∧
    ∀ n, (active payload n → predicate (children n)) ∧
      (¬ active payload n → children n = RecursiveSpace.bottom)

theorem holds_iff (predicate : Tree → Prop) (point : Tree) : holds predicate point ↔ step predicate point := by
  unfold holds
  refine (signature.operator_meaning model full (fun value => .up (predicate value.down)) (.up point)).trans ?_
  constructor
  · rintro ⟨⟨tag⟩,⟨payload⟩,children,valid,equal,conditions⟩
    refine ⟨tag,payload,(fun n => (children (.up n)).down),valid,congrArg ULift.down equal,?_⟩
    intro n
    exact ⟨fun present => ((conditions (.up n)).1 present).2,
      fun absent => congrArg ULift.down ((conditions (.up n)).2 absent)⟩
  · rintro ⟨tag,payload,children,valid,equal,conditions⟩
    refine ⟨.up tag,.up payload,(fun n => .up (children n.down)),valid,congrArg ULift.up equal,?_⟩
    rintro ⟨n⟩
    exact ⟨fun present => ⟨True.intro,(conditions n).1 present⟩,
      fun absent => congrArg ULift.up ((conditions n).2 absent)⟩

def zero : Tree := RecursiveSpace.construct 0 false (fun _ => RecursiveSpace.bottom)
def one : Tree := RecursiveSpace.construct 1 true (fun n => if n = 0 then zero else RecursiveSpace.bottom)
def hiddenTail : Tree := RecursiveSpace.construct 1 true
  (fun n => if n = 0 ∨ n = 1 then zero else RecursiveSpace.bottom)

theorem zero_from_empty_predicate : holds (fun _ => False) zero := by
  rw [holds_iff]
  refine ⟨0,false,_,Or.inl ⟨rfl,rfl⟩,rfl,?_⟩
  intro n
  exact ⟨fun present => Bool.noConfusion present.1,fun _ => rfl⟩

theorem one_from_zero : holds (fun tree => tree = zero) one := by
  rw [holds_iff]
  refine ⟨1,true,_,Or.inr ⟨rfl,rfl⟩,rfl,?_⟩
  intro n
  constructor
  · rintro ⟨_,rfl⟩
    rfl
  · intro absent
    have nonzero : n ≠ 0 := fun equal => absent ⟨rfl,equal⟩
    simp only [if_neg nonzero]

theorem hidden_tail_active_child_valid :
    ∀ n, active true n → (if n = 0 ∨ n = 1 then zero else RecursiveSpace.bottom) = zero := by
  intro n present
  rw [present.2]
  rfl

theorem hidden_tail_refused : ¬ holds (fun tree => tree = zero) hiddenTail := by
  rw [holds_iff]
  rintro ⟨tag,payload,children,_,equal,conditions⟩
  obtain ⟨rfl,rfl,same⟩ := (RecursiveSpace.construct_injective _ _ _ _ _ _).mp equal.symm
  have padding := (conditions 1).2 (by simp [active])
  have atOne := congrFun same 1
  simp only [Nat.one_ne_zero, or_true, if_true] at atOne
  exact RecursiveSpace.construct_ne_bottom 0 false _ (atOne.symm.trans padding)

def complement : ClosedTerm Const (PredicateFixedPoint.Operator space) :=
  .lam (.lam (.not (.app (.var (.vs .vz)) (.var .vz))))

theorem complement_not_monotone : ¬ model.models (PredicateFixedPoint.monotone complement) := by
  intro monotone
  have inclusion : ∀ value : ULift.{1} Tree, True → False → True := fun _ _ impossible => impossible.elim
  have contradiction := monotone (fun _ => ULift.up False) True.intro
    (fun _ => ULift.up True) True.intro inclusion (ULift.up RecursiveSpace.bottom) True.intro (fun impossible => impossible)
  exact contradiction True.intro

#print axioms holds_iff
#print axioms zero_from_empty_predicate
#print axioms one_from_zero
#print axioms hidden_tail_refused
#print axioms complement_not_monotone

end Mettapedia.Logic.HOL.RecursiveSpacePredicate.Controls
