import Mettapedia.Languages.MM0.HOLKernelTermTyping

/-!
# Binding controls for constructive MM0 HOL term typing

A closed quantified assumption can still contain a bound name in complete
occurrence support. Reusing that name as an independent abstraction parameter
is refused. Selecting the next bound slot constructs the identity typing
proof under the same assumption, without removing or changing it. A variable
term needs no unused fresh slot; its occupied context still refuses an
abstraction at that same slot.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLKernelTypingControls

open Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelJudgment HOLKernelTypingRules
open HOLKernelStructuralRules (CheckedProof ProofContext)

def quantifiedAntecedent (references : Symbol → Nat) : Preterm :=
  holds references (applySymbol references .allc [.var 0, boolType references, .var 0])

variable {sorts : SortSignature} {terms : TermSignature}

theorem quantifiedAntecedent_sorted (signature : Signature sorts terms) :
    Preterm.HasType terms [.bound signature.ids.object] (quantifiedAntecedent signature.symbol)
      [] signature.ids.wff := by
  apply holds_sorted signature
  apply signature.application _ .allc
  exact .cons (.bound rfl)
    (.cons (.regular (signature.application _ .bool [] .nil))
      (.cons (.regular (Preterm.HasType.var (binder := .bound signature.ids.object) rfl)) .nil))

theorem quantifiedAntecedent_occurrence (references : Symbol → Nat) (sort : Nat) :
    Preterm.HasVar [.bound sort] 0 (quantifiedAntecedent references) :=
  .argument (.argument (.bound rfl))

theorem reused_bound_slot_not_admissible (signature : Signature sorts terms)
    (domain result body : Preterm) :
    ¬ Substitution.Admissible terms
      (Rule.declaration signature.symbol signature.ids .lamT).arguments
      [.bound signature.ids.object]
      [quantifiedAntecedent signature.symbol, domain, result, .var 0, body] := by
  intro admitted
  exact admitted.single_bound_after_three_independence.1
    (quantifiedAntecedent_occurrence signature.symbol signature.ids.object)

theorem reused_bound_slot_refused (signature : Signature sorts terms)
    (domain result body : Preterm) :
    (Rule.declaration signature.symbol signature.ids .lamT).instantiate? terms
      [.bound signature.ids.object]
      [quantifiedAntecedent signature.symbol, domain, result, .var 0, body] = none := by
  apply (TheoremDecl.instantiate_none_iff _ _ _ _).mpr
  rintro ⟨instantiation, admitted⟩
  exact reused_bound_slot_not_admissible signature domain result body admitted.admissible

def NoConstants (_ : Ty Empty) : Type := Empty

def noBase (source : Empty) : Preterm := nomatch source

def noConstant {type : Ty Empty} (source : NoConstants type) : Preterm := nomatch source

def noPositions : Positions ([] : Ctx Empty) := fun index => nomatch index

def identity : Term NoConstants [] (.arr .prop .prop) := .lam (.var .vz)

def identityWithFreshSlot {theorems : TheoremSignature}
    (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : Rules theorems signature.symbol signature.ids) :
    CheckedProof (terms := terms) (definitions := fun _ => none) (theorems := theorems)
      (context := [.bound signature.ids.object, .bound signature.ids.object]) (hypotheses := [])
      (typed signature.symbol (quantifiedAntecedent signature.symbol)
        (applySymbol signature.symbol .lam [.var 1, boolType signature.symbol, .var 1])
        (functionType signature.symbol (boolType signature.symbol) (boolType signature.symbol))) := by
  apply HOLKernelTermTyping.compile signature structural typing noBase (@noConstant) Nat.succ
    (by intro source; cases source) (by intro type source; cases source) Nat.succ_injective
    (by intro slot source; cases source) identity noPositions 0 (quantifiedAntecedent signature.symbol)
  · apply holds_sorted signature
    apply signature.application _ .allc
    exact .cons (.bound rfl)
      (.cons (.regular (signature.application _ .bool [] .nil))
        (.cons (.regular (Preterm.HasType.var (binder := .bound signature.ids.object) rfl)) .nil))
  · intro type index
    cases index
  · intro offset smaller
    have same : offset = 0 := by simpa [identity, Term.binderDepth] using smaller
    subst offset
    rfl
  · intro offset
    simp [quantifiedAntecedent, holds, boolType, applySymbol, Preterm.applyArgs,
      Preterm.hasVar_app_iff, Preterm.hasVar_var_iff]
  · intro type index
    cases index
  · intro type source
    cases source

def variableAntecedent (references : Symbol → Nat) : Preterm :=
  hasType references (.var 0) (boolType references)

theorem variableAntecedent_occurrence (references : Symbol → Nat) (sort : Nat) :
    Preterm.HasVar [.bound sort] 0 (variableAntecedent references) :=
  .function (.argument (.bound rfl))

def variableInDependentContext {theorems : TheoremSignature}
    (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : Rules theorems signature.symbol signature.ids) :
    CheckedProof (terms := terms) (definitions := fun _ => none) (theorems := theorems)
      (context := [.bound signature.ids.object]) (hypotheses := [])
      (typed signature.symbol (variableAntecedent signature.symbol) (.var 0) (boolType signature.symbol)) := by
  let context : Context := [.bound signature.ids.object]
  let positions : Positions ([.prop] : Ctx Empty) := Positions.extend 0 noPositions
  let source : Term NoConstants [.prop] .prop := .var .vz
  have antecedentSorted : Preterm.HasType terms context (variableAntecedent signature.symbol)
      [] signature.ids.wff :=
    hasType_sorted signature context (.var (binder := .bound signature.ids.object) rfl)
      (signature.application context .bool [] .nil)
  apply HOLKernelTermTyping.compile signature structural typing noBase (@noConstant) id
    (by intro index; nomatch index) (by intro type symbol; nomatch symbol) (fun _ _ same => same)
    (by intro slot index; nomatch index) source positions 0 (variableAntecedent signature.symbol)
    antecedentSorted
  · intro type index
    cases index with
    | vz => rfl
    | vs index => nomatch index
  · simp [source, Term.binderDepth]
  · simp [source, Term.binderDepth]
  · intro type index
    cases index with
    | vz => exact HOLKernelStructuralRules.identity signature structural _ antecedentSorted
    | vs index => nomatch index
  · intro type symbol
    nomatch symbol

theorem abstraction_refused_in_variable_context (signature : Signature sorts terms)
    (domain result body : Preterm) :
    (Rule.declaration signature.symbol signature.ids .lamT).instantiate? terms
      [.bound signature.ids.object]
      [variableAntecedent signature.symbol, domain, result, .var 0, body] = none := by
  apply (TheoremDecl.instantiate_none_iff _ _ _ _).mpr
  rintro ⟨instantiation, admitted⟩
  exact admitted.admissible.single_bound_after_three_independence.1
    (variableAntecedent_occurrence signature.symbol signature.ids.object)

def identityViaFormationContext {theorems : TheoremSignature} (signature : Signature sorts terms)
    (structural : HOLKernelStructuralRules.Rules theorems signature.symbol signature.ids.wff)
    (typing : Rules theorems signature.symbol signature.ids) :
    CheckedProof (terms := terms) (definitions := fun _ => none) (theorems := theorems)
      (context := [.bound signature.ids.object]) (hypotheses := [])
      (typed signature.symbol (conjunction signature.symbol
        (holds signature.symbol (applySymbol signature.symbol .truth []))
        (quantifiedAntecedent signature.symbol))
        (applySymbol signature.symbol .lam [.var 0, boolType signature.symbol, .var 0])
        (functionType signature.symbol (boolType signature.symbol) (boolType signature.symbol))) := by
  let target : Context := [.bound signature.ids.object]
  let formation := holds signature.symbol (applySymbol signature.symbol .truth [])
  have formationSorted := holds_sorted signature target (signature.application target .truth [] .nil)
  let root := ProofContext.identity (definitions := fun _ => none) (hypotheses := [])
    signature structural formation formationSorted
  let logical := root.under signature structural (quantifiedAntecedent signature.symbol)
    (quantifiedAntecedent_sorted signature)
  let formationProof := HOLKernelTermTyping.compile (definitions := fun _ => none) (hypotheses := []) signature structural typing noBase (@noConstant) id
    (by intro index; nomatch index) (by intro type symbol; nomatch symbol) (fun _ _ same => same)
    (by intro slot index; nomatch index) identity noPositions 0 formation formationSorted
    (by intro type index; nomatch index)
    (by intro offset smaller; have zero : offset = 0 := by simpa [identity, Term.binderDepth] using smaller
        subst offset; rfl)
    (by intro offset smaller; simp [formation, holds, applySymbol, Preterm.applyArgs, Preterm.hasVar_app_iff])
    (by intro type index; nomatch index) (by intro type symbol; nomatch symbol)
  have boolSorted := signature.application target .bool [] .nil
  have lambdaSorted := signature.application target .lam [.var 0, boolType signature.symbol, .var 0]
    (.cons (.bound rfl) (.cons (.regular boolSorted)
      (.cons (.regular (.var (binder := .bound signature.ids.object) rfl)) .nil)))
  have functionSorted := signature.application target .function _
    (.cons (.regular boolSorted) (.cons (.regular boolSorted) .nil))
  exact logical.promote signature structural _ (hasType_sorted signature target lambdaSorted functionSorted) formationProof

theorem direct_abstraction_refused_under_logical_quantifier (signature : Signature sorts terms)
    (domain result body : Preterm) :
    (Rule.declaration signature.symbol signature.ids .lamT).instantiate? terms [.bound signature.ids.object]
      [conjunction signature.symbol (holds signature.symbol (applySymbol signature.symbol .truth []))
        (quantifiedAntecedent signature.symbol), domain, result, .var 0, body] = none := by
  apply (TheoremDecl.instantiate_none_iff _ _ _ _).mpr
  rintro ⟨instantiation, admitted⟩
  apply admitted.admissible.single_bound_after_three_independence.1
  exact .argument (quantifiedAntecedent_occurrence signature.symbol signature.ids.object)


#print axioms quantifiedAntecedent_sorted
#print axioms quantifiedAntecedent_occurrence
#print axioms reused_bound_slot_not_admissible
#print axioms reused_bound_slot_refused
#print axioms identityWithFreshSlot
#print axioms identityViaFormationContext
#print axioms direct_abstraction_refused_under_logical_quantifier
#print axioms variableAntecedent_occurrence
#print axioms variableInDependentContext
#print axioms abstraction_refused_in_variable_context

end Mettapedia.Languages.MM0.HOLKernelTypingControls
