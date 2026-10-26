import Mettapedia.Languages.MM0.HOLKernelProofReadbackCore
import Mettapedia.Languages.MM0.HOLKernelBindingRules

/-!
# Context-changing source proofs for native HOL binding rules

Bound native names extend an intrinsic variable frame only when they are
fresh for that frame and disjoint from the regular-parameter prefix. The
recursive child proof is checked at the extended frame. Its exact source
formula is compared with the weakening or substitution required by the
source rule before the corresponding ordinary HOL proof is constructed.

The interpretation reuses capture-safe proof substitution. Native theorem
headers and variable-independence conditions are checked by the shared
native evaluator; a matching name alone supplies no authority.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelBindingInterpretation

open Mettapedia.Logic Mettapedia.Logic.HOL
open Kernel HOLKernelSyntax HOLKernelTermReadback HOLKernelRuleReadback HOLKernelProofReadback
open NamedElaboration (SomeConst BinderNames)

universe u
variable {Const : Ty Unit → Type u} {gamma : Ctx Unit}

def fromAntecedent {antecedent conclusion : Formula Const gamma}
    (proof : ProofSyntax Const [] (.imp antecedent conclusion)) :
    ProofSyntax Const [antecedent] conclusion :=
  .impE (ProofSyntax.mono (ProofSyntax.emptyOccurrenceMap [antecedent]) proof) (.hyp 0)

def fromBoundFormation {domain : Ty Unit} (antecedent : Formula Const gamma)
    {conclusion : Formula Const (domain :: gamma)}
    (proof : ProofSyntax Const [] (.imp (.and (weaken antecedent) .top) conclusion)) :
    ProofSyntax Const (weakenHyps [antecedent]) conclusion :=
  ProofSyntax.castIndices (Δ := [weaken antecedent]) rfl rfl
    (.impE (ProofSyntax.mono (ProofSyntax.emptyOccurrenceMap [weaken antecedent]) proof)
      (.andI (.hyp 0) .topI))

def fromBoundExistential {domain : Ty Unit} (antecedent result : Formula Const gamma)
    {body : Formula Const (domain :: gamma)}
    (branch : ProofSyntax Const [] (.imp (.and (.and (weaken antecedent) .top) body) (weaken result))) :
    ProofSyntax Const (body :: weakenHyps [antecedent]) (weaken result) :=
  ProofSyntax.castIndices (Δ := [body, weaken antecedent]) rfl rfl
    (.impE (ProofSyntax.mono (ProofSyntax.emptyOccurrenceMap [body, weaken antecedent]) branch)
      (.andI (.andI (.hyp 1) .topI) (.hyp 0)))

def fromSubstitution {domain : Ty Unit} (antecedent conclusion : Formula Const gamma)
    (argument : Term Const gamma domain) {premise : Formula Const (domain :: gamma)}
    (proof : ProofSyntax Const [] premise)
    (same : HOL.subst (Subst.single argument) premise =
      .imp (.and antecedent (.eq argument argument)) conclusion) :
    ProofSyntax Const [antecedent] conclusion :=
  .impE (ProofSyntax.mono (ProofSyntax.emptyOccurrenceMap [antecedent])
      (ProofSyntax.castIndices rfl same (proof.subst (Subst.single argument))))
    (.andI (.hyp 0) (.eqRefl argument))

def freshName {gamma : Ctx Unit} (parameters : Nat) (names : Names gamma) (name : Nat) : Bool :=
  parameters ≤ name && (names.lookup? name).isNone

variable {terms : TermSignature} {definitions : Definition.Signature}
variable {references : HOLKernelSyntax.Symbol → Nat} {ids : SortIds}
variable {abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids}
variable {theorems : TheoremSignature} {context : Context}
variable {reader : TermReader Const} {parameters : Nat}

def bindingProof [∀ type, DecidableEq (Const type)]
    (recurse : Reader abbreviation theorems context reader parameters)
    (names : Names gamma) (rule : HOLKernelBindingRules.Rule)
    (arguments : List Preterm) (children : List ProofWitness)
    (goal : Formula Const gamma) : Option (ProofSyntax Const [] goal) :=
  match rule with
  | .universalIntroduction =>
      match arguments, children, goal with
      | [_, _, .var name, _], [child], .imp antecedent (@Term.all _ _ domain _ body) => do
          if freshName parameters names name then
            let proof ← recurse (BinderNames.cons (type := domain) name names) child
            if same : proof.source.formula = .imp (.and (weaken antecedent) .top) body then
              pure (.impI (.allI (fromBoundFormation antecedent
                (ProofSyntax.castIndices rfl same proof.source.proof))))
            else none
          else none
      | _, _, _ => none
  | .abstractionCongruence =>
      match arguments, children, goal with
      | [_, _, _, .var name, _, _], [child],
          .imp antecedent (.eq (@Term.lam _ _ domain _ _ first) secondTerm) =>
          match secondTerm with
          | .lam second => do
              if freshName parameters names name then
                let proof ← recurse (BinderNames.cons (type := domain) name names) child
                if same : proof.source.formula = .imp (.and (weaken antecedent) .top) (.eq first second) then
                  pure (.impI (.eqLam (fromBoundFormation antecedent
                    (ProofSyntax.castIndices rfl same proof.source.proof))))
                else none
              else none
          | _ => none
      | _, _, _ => none
  | .eta =>
      match arguments, children, goal with
      | [_, _, _, _, _], [_], .imp antecedent (@Term.eq _ _ _ (.arr domain _) first second) =>
          if same : first = .lam (.app (weaken (σ := domain) second) (.var .vz)) then
            some (ProofSyntax.castIndices rfl
              (congrArg (fun term => Term.imp antecedent (.eq term second)) same.symm) (.impI (.eta second)))
          else none
      | _, _, _ => none
  | .variableBeta =>
      match arguments, children, goal with
      | [_, _, _, _, _], [_], .imp antecedent (.eq (.app (.lam body) argument) result) =>
          if same : instantiate argument body = result then
            some (ProofSyntax.castIndices rfl
              (congrArg (fun term => Term.imp antecedent (.eq (.app (.lam body) argument) term)) same)
              (.impI (.beta argument body)))
          else none
      | _, _, _ => none
  | .constantAbstractionRenaming =>
      match arguments, children, goal with
      | [_, _, _, _, _, _], [_], .imp antecedent (.eq first second) =>
          if same : first = second then
            some (ProofSyntax.castIndices rfl
              (congrArg (fun term => Term.imp antecedent (.eq first term)) same) (.impI (.eqRefl first)))
          else none
      | _, _, _ => none
  | .abstractionRenaming =>
      match arguments, children, goal with
      | [_, _, _, _, _, _, _], [_, _, _], .imp antecedent (.eq first second) =>
          if same : first = second then
            some (ProofSyntax.castIndices rfl
              (congrArg (fun term => Term.imp antecedent (.eq first term)) same) (.impI (.eqRefl first)))
          else none
      | _, _, _ => none
  | .substitution =>
      match arguments, children, goal with
      | [_, typeCode, .var name, argumentCode, _], [_, _, child], .imp antecedent result =>
          match readType references typeCode with
          | none => none
          | some domain => do
              if freshName parameters names name then
                let argument ← readObjectWith reader names domain
                  (expandEquivalence references abbreviation.reference argumentCode)
                let proof ← recurse (BinderNames.cons (type := domain) name names) child
                if same : HOL.subst (Subst.single argument) proof.source.formula =
                    .imp (.and antecedent (.eq argument argument)) result then
                  pure (.impI (fromSubstitution antecedent result argument proof.source.proof same))
                else none
              else none
      | _, _, _ => none
  | .beta =>
      match arguments, children, goal with
      | [_, _, _, .var name, _, _, _], [_, _, _, child],
          .imp antecedent (.eq (.app (@Term.lam _ _ domain _ _ body) argument) result) => do
          if freshName parameters names name then
            let proof ← recurse (BinderNames.cons (type := domain) name names) child
            if same : HOL.subst (Subst.single argument) proof.source.formula =
                .imp (.and antecedent (.eq argument argument)) (.eq (instantiate argument body) result) then
              pure (.impI (.eqTrans (.beta argument body)
                (fromSubstitution antecedent _ argument proof.source.proof same)))
            else none
          else none
      | _, _, _ => none
  | .universalElimination =>
      match arguments, children, goal with
      | [_, _, .var name, argumentCode, _, _], [_, _, substitution, universal],
          .imp antecedent result => do
          let universalProof ← recurse names universal
          match universalFormula : universalProof.source.formula with
          | .imp sourceAntecedent (@Term.all _ _ domain _ body) =>
              if sameContext : sourceAntecedent = antecedent then
                if freshName parameters names name then
                  let argument ← readObjectWith reader names domain
                    (expandEquivalence references abbreviation.reference argumentCode)
                  let equation ← recurse (BinderNames.cons (type := domain) name names) substitution
                  if sameEquation : HOL.subst (Subst.single argument) equation.source.formula =
                      .imp (.and antecedent (.eq argument argument)) (.eq (instantiate argument body) result) then
                    let quantified := ProofSyntax.castIndices rfl
                      (universalFormula.trans (congrArg (fun term => Term.imp term (.all body)) sameContext))
                      universalProof.source.proof
                    pure (.impI (.impE
                      (.eqPropEL (fromSubstitution antecedent _ argument equation.source.proof sameEquation))
                      (.allE argument (fromAntecedent quantified))))
                  else none
                else none
              else none
          | _ => none
      | _, _, _ => none
  | .existentialIntroduction =>
      match arguments, children, goal with
      | [_, _, .var name, argumentCode, _, _], [_, _, substitution, resultProof],
          .imp antecedent (@Term.ex _ _ domain _ body) => do
          if freshName parameters names name then
            let argument ← readObjectWith reader names domain
              (expandEquivalence references abbreviation.reference argumentCode)
            let result ← recurse names resultProof
            match resultFormula : result.source.formula with
            | .imp sourceAntecedent conclusion =>
                if sameContext : sourceAntecedent = antecedent then
                  let equation ← recurse (BinderNames.cons (type := domain) name names) substitution
                  if sameEquation : HOL.subst (Subst.single argument) equation.source.formula =
                      .imp (.and antecedent (.eq argument argument)) (.eq (instantiate argument body) conclusion) then
                    let supplied := ProofSyntax.castIndices rfl
                      (resultFormula.trans (congrArg (fun term => Term.imp term conclusion) sameContext))
                      result.source.proof
                    pure (.impI (.exI argument (.impE
                      (.eqPropER (fromSubstitution antecedent _ argument equation.source.proof sameEquation))
                      (fromAntecedent supplied))))
                  else none
                else none
            | _ => none
          else none
      | _, _, _ => none
  | .existentialElimination =>
      match arguments, children, goal with
      | [_, _, .var name, _, _], [_, existential, child], .imp antecedent result => do
          let existentialProof ← recurse names existential
          match existentialFormula : existentialProof.source.formula with
          | .imp sourceAntecedent (@Term.ex _ _ domain _ body) =>
              if sameContext : sourceAntecedent = antecedent then
                if freshName parameters names name then
                  let proof ← recurse (BinderNames.cons (type := domain) name names) child
                  if sameBody : proof.source.formula =
                      .imp (.and (.and (weaken antecedent) .top) body) (weaken result) then
                    let supplied := ProofSyntax.castIndices rfl
                      (existentialFormula.trans (congrArg (fun term => Term.imp term (.ex body)) sameContext))
                      existentialProof.source.proof
                    let branch := ProofSyntax.castIndices rfl sameBody proof.source.proof
                    pure (.impI (.exE (fromAntecedent supplied)
                      (fromBoundExistential antecedent result branch)))
                  else none
                else none
              else none
          | _ => none
      | _, _, _ => none
  | .equalityLeftTyping | .equalityRightTyping => none

def readBinding [∀ type, DecidableEq (Const type)]
    (bindingAt : Nat → Option HOLKernelBindingRules.Rule) :
    BindingHandler abbreviation theorems context reader parameters :=
  fun recurse {_} names index arguments children native =>
    match bindingAt index with
    | none => none
    | some rule =>
        if theorems index = some (rule.declaration references ids abbreviation.reference) then
          match reading : readFormulaIn abbreviation reader parameters names native with
          | none => none
          | some formula =>
              (bindingProof recurse names rule arguments children formula).map fun proof =>
                ⟨⟨formula, proof⟩, reading⟩
        else none

/-- Proof-free local admission of the eleven native binding rules. Bound names
must be fresh for the active frame and disjoint from regular parameters, and
child premises are specified only by their source formulas at the appropriate
frames. -/
inductive AdmittedBindingStep
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (reader : TermReader Const) (parameters : Nat)
    (Child : {delta : Ctx Unit} → Names delta → ProofWitness → Formula Const delta → Type u)
    {gamma : Ctx Unit} (names : Names gamma) :
    HOLKernelBindingRules.Rule → List Preterm → List ProofWitness → Formula Const gamma → Type u where
  | universalIntroduction {antecedent : Formula Const gamma} {domain : Ty Unit}
      {body : Formula Const (domain :: gamma)} {arg1 arg2 arg4 : Preterm} {name : Nat}
      {child : ProofWitness}
      (fresh : freshName parameters names name = true)
      (childAdmitted : Child (BinderNames.cons (type := domain) name names) child
        (.imp (.and (weaken antecedent) .top) body)) :
      AdmittedBindingStep abbreviation reader parameters Child names .universalIntroduction
        [arg1, arg2, .var name, arg4] [child] (.imp antecedent (.all body))
  | abstractionCongruence {antecedent : Formula Const gamma} {domain codomain : Ty Unit}
      {first second : Term Const (domain :: gamma) codomain}
      {arg1 arg2 arg3 arg5 arg6 : Preterm} {name : Nat} {child : ProofWitness}
      (fresh : freshName parameters names name = true)
      (childAdmitted : Child (BinderNames.cons (type := domain) name names) child
        (.imp (.and (weaken antecedent) .top) (.eq first second))) :
      AdmittedBindingStep abbreviation reader parameters Child names .abstractionCongruence
        [arg1, arg2, arg3, .var name, arg5, arg6] [child]
        (.imp antecedent (.eq (.lam first) (.lam second)))
  | eta {antecedent : Formula Const gamma} {domain codomain : Ty Unit}
      {second : Term Const gamma (.arr domain codomain)}
      {arg1 arg2 arg3 arg4 arg5 : Preterm} {child : ProofWitness} :
      AdmittedBindingStep abbreviation reader parameters Child names .eta
        [arg1, arg2, arg3, arg4, arg5] [child]
        (.imp antecedent (.eq (.lam (.app (weaken (σ := domain) second) (.var .vz))) second))
  | variableBeta {antecedent : Formula Const gamma} {domain codomain : Ty Unit}
      {body : Term Const (domain :: gamma) codomain} {argument : Term Const gamma domain}
      {arg1 arg2 arg3 arg4 arg5 : Preterm} {child : ProofWitness} :
      AdmittedBindingStep abbreviation reader parameters Child names .variableBeta
        [arg1, arg2, arg3, arg4, arg5] [child]
        (.imp antecedent (.eq (.app (.lam body) argument) (instantiate argument body)))
  | constantAbstractionRenaming {antecedent : Formula Const gamma} {type : Ty Unit}
      {term : Term Const gamma type}
      {arg1 arg2 arg3 arg4 arg5 arg6 : Preterm} {child : ProofWitness} :
      AdmittedBindingStep abbreviation reader parameters Child names .constantAbstractionRenaming
        [arg1, arg2, arg3, arg4, arg5, arg6] [child] (.imp antecedent (.eq term term))
  | abstractionRenaming {antecedent : Formula Const gamma} {type : Ty Unit}
      {term : Term Const gamma type}
      {arg1 arg2 arg3 arg4 arg5 arg6 arg7 : Preterm} {c1 c2 c3 : ProofWitness} :
      AdmittedBindingStep abbreviation reader parameters Child names .abstractionRenaming
        [arg1, arg2, arg3, arg4, arg5, arg6, arg7] [c1, c2, c3] (.imp antecedent (.eq term term))
  | substitution {antecedent result : Formula Const gamma} {domain : Ty Unit}
      {argument : Term Const gamma domain} {premise : Formula Const (domain :: gamma)}
      {arg1 typeCode argumentCode arg5 : Preterm} {name : Nat} {c1 c2 child : ProofWitness}
      (typeRead : readType references typeCode = some domain)
      (fresh : freshName parameters names name = true)
      (argumentRead : readObjectWith reader names domain
        (expandEquivalence references abbreviation.reference argumentCode) = some argument)
      (childAdmitted : Child (BinderNames.cons (type := domain) name names) child premise)
      (same : HOL.subst (Subst.single argument) premise =
        .imp (.and antecedent (.eq argument argument)) result) :
      AdmittedBindingStep abbreviation reader parameters Child names .substitution
        [arg1, typeCode, .var name, argumentCode, arg5] [c1, c2, child] (.imp antecedent result)
  | beta {antecedent : Formula Const gamma} {domain codomain : Ty Unit}
      {body : Term Const (domain :: gamma) codomain} {argument : Term Const gamma domain}
      {result : Term Const gamma codomain} {premise : Formula Const (domain :: gamma)}
      {arg1 arg2 arg3 arg5 arg6 arg7 : Preterm} {name : Nat} {c1 c2 c3 child : ProofWitness}
      (fresh : freshName parameters names name = true)
      (childAdmitted : Child (BinderNames.cons (type := domain) name names) child premise)
      (same : HOL.subst (Subst.single argument) premise =
        .imp (.and antecedent (.eq argument argument)) (.eq (instantiate argument body) result)) :
      AdmittedBindingStep abbreviation reader parameters Child names .beta
        [arg1, arg2, arg3, .var name, arg5, arg6, arg7] [c1, c2, c3, child]
        (.imp antecedent (.eq (.app (.lam body) argument) result))
  | universalElimination {antecedent result : Formula Const gamma} {domain : Ty Unit}
      {body : Formula Const (domain :: gamma)} {argument : Term Const gamma domain}
      {premise : Formula Const (domain :: gamma)}
      {arg1 arg2 argumentCode arg5 arg6 : Preterm} {name : Nat}
      {c1 c2 substitution universal : ProofWitness}
      (universalAdmitted : Child names universal (.imp antecedent (.all body)))
      (fresh : freshName parameters names name = true)
      (argumentRead : readObjectWith reader names domain
        (expandEquivalence references abbreviation.reference argumentCode) = some argument)
      (substitutionAdmitted : Child (BinderNames.cons (type := domain) name names) substitution premise)
      (same : HOL.subst (Subst.single argument) premise =
        .imp (.and antecedent (.eq argument argument)) (.eq (instantiate argument body) result)) :
      AdmittedBindingStep abbreviation reader parameters Child names .universalElimination
        [arg1, arg2, .var name, argumentCode, arg5, arg6] [c1, c2, substitution, universal]
        (.imp antecedent result)
  | existentialIntroduction {antecedent conclusion : Formula Const gamma} {domain : Ty Unit}
      {body : Formula Const (domain :: gamma)} {argument : Term Const gamma domain}
      {premise : Formula Const (domain :: gamma)}
      {arg1 arg2 argumentCode arg5 arg6 : Preterm} {name : Nat}
      {c1 c2 substitution resultProof : ProofWitness}
      (fresh : freshName parameters names name = true)
      (argumentRead : readObjectWith reader names domain
        (expandEquivalence references abbreviation.reference argumentCode) = some argument)
      (resultAdmitted : Child names resultProof (.imp antecedent conclusion))
      (substitutionAdmitted : Child (BinderNames.cons (type := domain) name names) substitution premise)
      (same : HOL.subst (Subst.single argument) premise =
        .imp (.and antecedent (.eq argument argument)) (.eq (instantiate argument body) conclusion)) :
      AdmittedBindingStep abbreviation reader parameters Child names .existentialIntroduction
        [arg1, arg2, .var name, argumentCode, arg5, arg6] [c1, c2, substitution, resultProof]
        (.imp antecedent (.ex body))
  | existentialElimination {antecedent result : Formula Const gamma} {domain : Ty Unit}
      {body : Formula Const (domain :: gamma)}
      {arg1 arg2 arg4 arg5 : Preterm} {name : Nat} {c1 existential child : ProofWitness}
      (existentialAdmitted : Child names existential (.imp antecedent (.ex body)))
      (fresh : freshName parameters names name = true)
      (childAdmitted : Child (BinderNames.cons (type := domain) name names) child
        (.imp (.and (.and (weaken antecedent) .top) body) (weaken result))) :
      AdmittedBindingStep abbreviation reader parameters Child names .existentialElimination
        [arg1, arg2, .var name, arg4, arg5] [c1, existential, child] (.imp antecedent result)

def AdmittedBindingStep.mapChildren
    {names : Names gamma}
    {Child Next : {delta : Ctx Unit} → Names delta → ProofWitness → Formula Const delta → Type u}
    (transform : ∀ {delta} {nextNames : Names delta} {child formula},
      Child nextNames child formula → Next nextNames child formula)
    {rule : HOLKernelBindingRules.Rule} {arguments : List Preterm} {children : List ProofWitness}
    {formula : Formula Const gamma} :
    AdmittedBindingStep abbreviation reader parameters Child names rule arguments children formula →
    AdmittedBindingStep abbreviation reader parameters Next names rule arguments children formula
  | .universalIntroduction fresh child => .universalIntroduction fresh (transform child)
  | .abstractionCongruence fresh child => .abstractionCongruence fresh (transform child)
  | .eta => .eta
  | .variableBeta => .variableBeta
  | .constantAbstractionRenaming => .constantAbstractionRenaming
  | .abstractionRenaming => .abstractionRenaming
  | .substitution typeRead fresh argumentRead child same =>
      .substitution typeRead fresh argumentRead (transform child) same
  | .beta fresh child same => .beta fresh (transform child) same
  | .universalElimination universal fresh argumentRead substitutionAdmitted same =>
      .universalElimination (transform universal) fresh argumentRead (transform substitutionAdmitted) same
  | .existentialIntroduction fresh argumentRead result substitutionAdmitted same =>
      .existentialIntroduction fresh argumentRead (transform result) (transform substitutionAdmitted) same
  | .existentialElimination existential fresh child =>
      .existentialElimination (transform existential) fresh (transform child)

/-- Proof-free admission of a licensed binding application node. -/
structure AdmittedBinding
    (abbreviation : HOLKernelBooleanEquality.Abbreviation terms definitions references ids)
    (theorems : TheoremSignature) (reader : TermReader Const) (parameters : Nat)
    (bindingAt : Nat → Option HOLKernelBindingRules.Rule)
    (Child : {delta : Ctx Unit} → Names delta → ProofWitness → Formula Const delta → Type u)
    {gamma : Ctx Unit} (names : Names gamma)
    (index : Nat) (arguments : List Preterm) (children : List ProofWitness)
    (native : Preterm) (formula : Formula Const gamma) where
  rule : HOLKernelBindingRules.Rule
  selected : bindingAt index = some rule
  declared : theorems index = some (rule.declaration references ids abbreviation.reference)
  conclusion_read : readFormulaIn abbreviation reader parameters names native = some formula
  step : AdmittedBindingStep abbreviation reader parameters Child names rule arguments children formula

def AdmittedBinding.mapChildren
    {names : Names gamma}
    {Child Next : {delta : Ctx Unit} → Names delta → ProofWitness → Formula Const delta → Type u}
    (transform : ∀ {delta} {nextNames : Names delta} {child formula},
      Child nextNames child formula → Next nextNames child formula)
    {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
    {index : Nat} {arguments : List Preterm} {children : List ProofWitness}
    {native : Preterm} {formula : Formula Const gamma}
    (admitted : AdmittedBinding abbreviation theorems reader parameters bindingAt Child
      names index arguments children native formula) :
    AdmittedBinding abbreviation theorems reader parameters bindingAt Next
      names index arguments children native formula :=
  ⟨admitted.rule, admitted.selected, admitted.declared, admitted.conclusion_read,
    admitted.step.mapChildren transform⟩

theorem bindingProof_of_admitted [∀ type, DecidableEq (Const type)]
    {recurse : Reader abbreviation theorems context reader parameters}
    {Child : {delta : Ctx Unit} → Names delta → ProofWitness → Formula Const delta → Type u}
    (childrenOk : ∀ {delta} (nextNames : Names delta) (child : ProofWitness) (formula : Formula Const delta),
      Child nextNames child formula →
      ∃ out : ProofReadback abbreviation theorems context reader parameters nextNames child,
        recurse nextNames child = some out ∧ out.source.formula = formula)
    {names : Names gamma} {rule : HOLKernelBindingRules.Rule}
    {arguments : List Preterm} {children : List ProofWitness} {goal : Formula Const gamma}
    (step : AdmittedBindingStep abbreviation reader parameters Child names rule arguments children goal) :
    ∃ proof : ProofSyntax Const [] goal,
      bindingProof recurse names rule arguments children goal = some proof := by
  cases step with
  | universalIntroduction fresh childAdmitted =>
      obtain ⟨out, hout, hform⟩ := childrenOk _ _ _ childAdmitted
      delta bindingProof; dsimp only
      simp only [fresh, ↓reduceIte, hout, Option.bind_eq_bind, Option.bind_some, hform, ↓reduceDIte]
      exact ⟨_, rfl⟩
  | abstractionCongruence fresh childAdmitted =>
      obtain ⟨out, hout, hform⟩ := childrenOk _ _ _ childAdmitted
      delta bindingProof; dsimp only
      simp only [fresh, ↓reduceIte, hout, Option.bind_eq_bind, Option.bind_some, hform, ↓reduceDIte]
      exact ⟨_, rfl⟩
  | eta =>
      delta bindingProof; dsimp only
      simp only [↓reduceDIte]
      exact ⟨_, rfl⟩
  | variableBeta =>
      delta bindingProof; dsimp only
      simp only [↓reduceDIte]
      exact ⟨_, rfl⟩
  | constantAbstractionRenaming =>
      delta bindingProof; dsimp only
      simp only [↓reduceDIte]
      exact ⟨_, rfl⟩
  | abstractionRenaming =>
      delta bindingProof; dsimp only
      simp only [↓reduceDIte]
      exact ⟨_, rfl⟩
  | substitution typeRead fresh argumentRead childAdmitted same =>
      obtain ⟨out, hout, hform⟩ := childrenOk _ _ _ childAdmitted
      rw [← hform] at same
      delta bindingProof; dsimp only
      simp only [typeRead, fresh, ↓reduceIte, argumentRead, Option.bind_eq_bind,
        Option.bind_some, hout, same, ↓reduceDIte]
      exact ⟨_, rfl⟩
  | beta fresh childAdmitted same =>
      obtain ⟨out, hout, hform⟩ := childrenOk _ _ _ childAdmitted
      rw [← hform] at same
      delta bindingProof; dsimp only
      simp only [fresh, ↓reduceIte, hout, Option.bind_eq_bind, Option.bind_some, same, ↓reduceDIte]
      exact ⟨_, rfl⟩
  | universalElimination universalAdmitted fresh argumentRead substitutionAdmitted same =>
      obtain ⟨⟨uNative, uAccepted, ⟨uFormula, uProof⟩, uReading⟩, huOut, huForm⟩ :=
        childrenOk _ _ _ universalAdmitted
      dsimp only at huForm
      subst huForm
      obtain ⟨eqOut, heqOut, heqForm⟩ := childrenOk _ _ _ substitutionAdmitted
      rw [← heqForm] at same
      delta bindingProof; dsimp only
      simp only [huOut, Option.bind_eq_bind, Option.bind_some, ↓reduceDIte,
        fresh, ↓reduceIte, argumentRead, heqOut, same]
      exact ⟨_, rfl⟩
  | existentialIntroduction fresh argumentRead resultAdmitted substitutionAdmitted same =>
      obtain ⟨⟨rNative, rAccepted, ⟨rFormula, rProof⟩, rReading⟩, hrOut, hrForm⟩ :=
        childrenOk _ _ _ resultAdmitted
      dsimp only at hrForm
      subst hrForm
      obtain ⟨eqOut, heqOut, heqForm⟩ := childrenOk _ _ _ substitutionAdmitted
      rw [← heqForm] at same
      delta bindingProof; dsimp only
      simp only [fresh, ↓reduceIte, argumentRead, Option.bind_eq_bind, Option.bind_some,
        hrOut, ↓reduceDIte, heqOut, same]
      exact ⟨_, rfl⟩
  | existentialElimination existentialAdmitted fresh childAdmitted =>
      obtain ⟨⟨eNative, eAccepted, ⟨eFormula, eProof⟩, eReading⟩, heOut, heForm⟩ :=
        childrenOk _ _ _ existentialAdmitted
      dsimp only at heForm
      subst heForm
      obtain ⟨out, hout, hform⟩ := childrenOk _ _ _ childAdmitted
      delta bindingProof; dsimp only
      simp only [heOut, Option.bind_eq_bind, Option.bind_some, ↓reduceDIte,
        fresh, ↓reduceIte, hout, hform]
      exact ⟨_, rfl⟩

theorem readBinding_of_admitted [∀ type, DecidableEq (Const type)]
    {bindingAt : Nat → Option HOLKernelBindingRules.Rule}
    {recurse : Reader abbreviation theorems context reader parameters}
    {Child : {delta : Ctx Unit} → Names delta → ProofWitness → Formula Const delta → Type u}
    (childrenOk : ∀ {delta} (nextNames : Names delta) (child : ProofWitness) (formula : Formula Const delta),
      Child nextNames child formula →
      ∃ out : ProofReadback abbreviation theorems context reader parameters nextNames child,
        recurse nextNames child = some out ∧ out.source.formula = formula)
    {names : Names gamma} {index : Nat} {arguments : List Preterm}
    {children : List ProofWitness} {native : Preterm} {formula : Formula Const gamma}
    (admitted : AdmittedBinding abbreviation theorems reader parameters bindingAt Child names index arguments children native formula) :
    ∃ source : SourceReading abbreviation reader parameters names native,
      readBinding bindingAt recurse names index arguments children native = some source ∧
      source.source.formula = formula := by
  obtain ⟨proof, hproof⟩ := bindingProof_of_admitted childrenOk admitted.step
  refine ⟨⟨⟨formula, proof⟩, admitted.conclusion_read⟩, ?_, rfl⟩
  delta readBinding; dsimp only
  simp only [admitted.selected, admitted.declared, ↓reduceIte]
  split
  next refused =>
    have accepted := admitted.conclusion_read
    rw [refused] at accepted
    contradiction
  next decoded reading =>
    have same : decoded = formula := Option.some.inj (reading.symm.trans admitted.conclusion_read)
    subst decoded
    simp only [hproof, Option.map_some]

#print axioms bindingProof
#print axioms readBinding
#print axioms fromSubstitution
#print axioms readBinding_of_admitted

end Mettapedia.Languages.MM0.HOLKernelBindingInterpretation
