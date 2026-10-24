import Mettapedia.Languages.MM0.HOLKernelSignature
import Mettapedia.Languages.MM0.Kernel.BoundRenaming

/-!
# Native sorting and independence controls for HOL syntax

Closed truth needs no spare binding slot; lambda requires an actual native
bound slot. Equal constructor profiles retain distinct named references.
Ordinary term sorting permits variable identification, while theorem
substitution retains MM0's separate bound-variable independence condition.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelSyntaxControls

open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax

variable {sorts : SortSignature} {terms : TermSignature}

abbrev NoConstants (_ : Ty Unit) := Empty

def noConstants {type : Ty Unit} (constant : NoConstants type) : Preterm := nomatch constant

def noPositions : Positions ([] : Ctx Unit) := fun index => nomatch index

def identity : Term NoConstants [] (.arr .prop .prop) := .lam (.var .vz)

theorem truth_without_binding_slots (signature : Signature sorts terms) (binders : Nat → Nat) :
    Preterm.HasType terms []
      (encodeTerm signature.symbol (fun _ : Unit => applySymbol signature.symbol .bool [])
        noConstants binders noPositions 0 (.top : Formula NoConstants []))
      [] signature.ids.object :=
  signature.application [] .truth [] .nil

theorem identity_sorted (signature : Signature sorts terms) :
    Preterm.HasType terms [.bound signature.ids.object]
      (encodeTerm signature.symbol (fun _ : Unit => applySymbol signature.symbol .bool [])
        noConstants (fun _ => 0) noPositions 0 identity)
      [] signature.ids.object := by
  apply encodeTerm_sorted signature [.bound signature.ids.object] _ _ _
    (fun _ => signature.application _ .bool [] .nil)
    (fun constant => nomatch constant) identity _ _
  · intro type index
    nomatch index
  · intro offset bounded
    rfl

theorem regular_slot_refused_as_lambda_binder (signature : Signature sorts terms) :
    Preterm.infer terms [.regular signature.ids.object ∅]
      (encodeTerm signature.symbol (fun _ : Unit => applySymbol signature.symbol .bool [])
        noConstants (fun _ => 0) noPositions 0 identity) = none := by
  simp [identity, encodeTerm, applySymbol, Preterm.applyArgs, Positions.extend,
    encodeType, Preterm.infer, signature.declared, Symbol.profile, Preterm.boundSort?]

theorem equal_profiles_distinct_names (signature : Signature sorts terms) :
    Symbol.andc.profile signature.ids = Symbol.orc.profile signature.ids ∧
      signature.symbol .andc ≠ signature.symbol .orc := by
  refine ⟨rfl, ?_⟩
  intro same
  have impossible := signature.symbol_injective same
  cases impossible

def identifiedPositions : Positions ([.prop, .prop] : Ctx Unit) := fun _ => 0

theorem distinct_source_variables :
    (Term.var .vz : Formula NoConstants [.prop, .prop]) ≠ .var (.vs .vz) := by
  intro same
  cases same

theorem identified_variables_have_same_code (references : Symbol → Nat)
    (base : Unit → Preterm) (binders : Nat → Nat) :
    encodeTerm references base noConstants binders identifiedPositions 0
        (Term.var .vz : Formula NoConstants [.prop, .prop]) =
      encodeTerm references base noConstants binders identifiedPositions 0
        (Term.var (.vs .vz) : Formula NoConstants [.prop, .prop]) := rfl

theorem identified_variable_sorted (signature : Signature sorts terms) :
    Preterm.HasType terms [.bound signature.ids.object]
      (encodeTerm signature.symbol (fun _ : Unit => applySymbol signature.symbol .bool [])
        noConstants (fun _ => 0) identifiedPositions 0
        (Term.var (.vs .vz) : Formula NoConstants [.prop, .prop])) [] signature.ids.object := by
  change Preterm.HasType terms [.bound signature.ids.object] (.var 0) [] signature.ids.object
  exact .var (binder := .bound signature.ids.object) rfl

theorem identified_bound_substitution_refused (signature : Signature sorts terms) :
    Substitution.checkAdmissible terms [.bound signature.ids.object, .bound signature.ids.object]
      [.bound signature.ids.object] [.var 0, .var 0] = false := by
  have condition := Substitution.two_bound_check_iff terms [.bound signature.ids.object]
    signature.ids.object 0 0 rfl rfl
  exact Bool.eq_false_iff.mpr (fun accepted => (condition.mp accepted) rfl)

#print axioms truth_without_binding_slots
#print axioms identity_sorted
#print axioms regular_slot_refused_as_lambda_binder
#print axioms equal_profiles_distinct_names
#print axioms identified_bound_substitution_refused

end Mettapedia.Languages.MM0.HOLKernelSyntaxControls
