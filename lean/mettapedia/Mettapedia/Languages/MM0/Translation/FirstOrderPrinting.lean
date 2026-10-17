import Mettapedia.Languages.MM0.Translation.FirstOrderModules
import Mettapedia.Languages.MM0.Translation.FirstOrderAdmission
import Mettapedia.Languages.MM0.Kernel.ProofSharing

/-!
# Human-facing MM0 text from the compiled first-order presentation

The printer reads actual MM0 declaration payloads and resolves their numeric
references through the retained authored names. Ordinary identifiers remain
unchanged when unambiguous. Other names receive explicit namespace-qualified
identifiers. Local parameters keep their authored names when these do not
collide with global declarations.

Simple nullary, prefix and fully parenthesized infix notation is retained when
its token is unique. Other grammar patterns use MM0's standard constructor
application syntax. Formula grouping is explicit, so the printer does not
infer associativity or precedence from a grammar pattern.

Primitive constructors are printed as terms and defined constructors as
definitions, in the order of admission: every definition follows the terms
its body mentions. A body is printed in application syntax, since notation
is declared after all constructors.

A conversion step of a proof is printed, for the reference producer, as its
child proof ascribed to the converted statement; the producer supplies the
upstream conversion evidence. The upstream conversion grammar has no
transitivity, so the kernel model's evidence has no direct text form and a
proof with a conversion step has no MMU text here.

Chronological certificates retain every submitted saved goal and initializer,
including unused entries. MMU uses lexical `:let` bindings; MM1 uses the
reference producer's goal-bearing `have` interface. Initializers and roots are
checked by the original MM0 kernel before the saved proof file is emitted.
Ordinary and saved certificates share declaration assembly.

The output follows the pinned upstream `mm0.md` declaration and secondary
expression grammar. This text interface is qualified independently on the
native MM0 parsers; it is not a byte-parser correctness theorem.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Translation.FirstOrderPrinting

open Mettapedia.OSLF.MeTTaIL.Syntax
open Kernel FirstOrderSyntax FirstOrderTyping FirstOrderRules FirstOrderAdmission

def identifier (text : String) : Bool :=
  match text.toList with
  | [] => false
  | first :: rest => text != "_" &&
      (first.isAlpha || first == '_') && first.toNat < 128 &&
      rest.all (fun character => character.toNat < 128 &&
        (character.isAlphanum || character == '_'))

def allNames (source : Presentation) : List String :=
  source.syntaxSignature.sorts ++ source.syntaxSignature.names ++ source.rules.map (fun row => row.row.id)

def externalName (inventory : List String) (kind : String) (index : Nat) (authored : String) : String :=
  if identifier authored && !authored.startsWith "mm0__" && inventory.count authored == 1 then authored
  else "mm0__" ++ kind ++ "_" ++ toString index

def sortNames (source : Presentation) : List String :=
  source.syntaxSignature.sorts.mapIdx (externalName (allNames source) "sort")

def constructorNames (source : Presentation) : List String :=
  source.syntaxSignature.names.mapIdx (externalName (allNames source) "term")

def ruleNames (source : Presentation) : List String :=
  (source.rules.map (fun row => row.row.id)).mapIdx (externalName (allNames source) "rule")

def parameterNames (globals authored : List String) : List String :=
  authored.mapIdx (fun index original =>
    if identifier original && !original.startsWith "mm0__" &&
        !globals.contains original && authored.count original == 1 then original
    else "mm0__var_" ++ toString index)

inductive Notation where
  | prefixToken (token : String)
  | infixToken (token : String)
  deriving DecidableEq, Repr

def Notation.token : Notation → String
  | .prefixToken token | .infixToken token => token

def notationCandidate? (row : GrammarRule) : Option Notation :=
  let pattern := match row.syntaxPattern with
    | [.terminal "(", a, b, c, .terminal ")"] => [a, b, c]
    | other => other
  match row.params.map TermParam.bodyName, pattern with
  | [], [.terminal token] => some (.prefixToken token)
  | [formal], [.terminal token, .nonTerminal actual] =>
      if formal = actual then some (.prefixToken token) else none
  | [first, second], [.nonTerminal a, .terminal token, .nonTerminal b] =>
      if first = a ∧ second = b then some (.infixToken token) else none
  | _, _ => none

def notation? (source : Presentation) (index : Nat) : Option Notation := do
  let row ← source.syntaxSignature.language.terms[index]?
  let candidate ← notationCandidate? row
  let token := candidate.token
  if !token.isEmpty && token != "(" && token != ")" &&
      token.toList.all (fun character => !character.isWhitespace && character != '$') &&
      !(sortNames source ++ constructorNames source ++ ruleNames source).contains token &&
      (source.syntaxSignature.language.terms.filterMap notationCandidate?).countP
        (fun other => other.token == token) == 1 then some candidate else none

mutual
  def patternText? (source : Presentation) (locals : List String) (useNotation : Bool) :
      Pattern → Option String
    | .bvar index => locals[index]?
    | .apply label arguments => do
        let index ← index? source.syntaxSignature.names label
        let row ← source.syntaxSignature.language.terms[index]?
        if arguments.length != row.params.length then none else do
          let displayName ← (constructorNames source)[index]?
          let arguments' ← patternTexts? source locals useNotation arguments
          match if useNotation then notation? source index else none, arguments' with
          | some (.infixToken token), [first, second] =>
              pure ("(" ++ first ++ " " ++ token ++ " " ++ second ++ ")")
          | some (.prefixToken token), values =>
              pure ("(" ++ String.intercalate " " (token :: values) ++ ")")
          | _, values => pure ("(" ++ String.intercalate " " (displayName :: values) ++ ")")
    | _ => none
  termination_by pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  def patternTexts? (source : Presentation) (locals : List String) (useNotation : Bool) :
      List Pattern → Option (List String)
    | [] => some []
    | first :: rest => do
        let first' ← patternText? source locals useNotation first
        let rest' ← patternTexts? source locals useNotation rest
        pure (first' :: rest')
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

/-! Printer evaluation retains one computed constructor inventory throughout
an expression. The refinement below keeps the original text semantics. -/
private def notationTable (source : Presentation) : List (Option Notation) :=
  (List.range source.syntaxSignature.language.terms.length).map (notation? source)

private theorem notationTable_lookup (source : Presentation) (index : Nat) :
    (notationTable source)[index]?.getD none = notation? source index := by
  by_cases bounded : index < source.syntaxSignature.language.terms.length
  · simp [notationTable, List.getElem?_map, List.getElem?_range bounded]
  · have missing : source.syntaxSignature.language.terms[index]? = none :=
      List.getElem?_eq_none (by omega)
    have missingRange : (List.range source.syntaxSignature.language.terms.length)[index]? = none :=
      List.getElem?_eq_none (by simpa only [List.length_range] using Nat.le_of_not_gt bounded)
    simp only [notationTable, List.getElem?_map, missingRange, Option.map_none, Option.getD_none]
    simp only [notation?, missing]
    rfl

private def selectedNotations (source : Presentation) (useNotation : Bool) : List (Option Notation) :=
  if useNotation then notationTable source else []

private theorem selectedNotations_lookup (source : Presentation) (useNotation : Bool) (index : Nat) :
    (if useNotation then (selectedNotations source useNotation)[index]?.getD none else none) =
      (if useNotation then notation? source index else none) := by
  cases useNotation with
  | false => rfl
  | true => simpa only [selectedNotations, ↓reduceIte] using notationTable_lookup source index

mutual
  private def patternTextWith? (source : Presentation) (displayNames : List String)
      (notations : List (Option Notation)) (locals : List String) (useNotation : Bool) : Pattern → Option String
    | .bvar index => locals[index]?
    | .apply label arguments => do
        let index ← index? source.syntaxSignature.names label
        let row ← source.syntaxSignature.language.terms[index]?
        if arguments.length != row.params.length then none else do
          let displayName ← displayNames[index]?
          let arguments' ← patternTextsWith? source displayNames notations locals useNotation arguments
          match if useNotation then notations[index]?.getD none else none, arguments' with
          | some (.infixToken token), [first, second] =>
              pure ("(" ++ first ++ " " ++ token ++ " " ++ second ++ ")")
          | some (.prefixToken token), values =>
              pure ("(" ++ String.intercalate " " (token :: values) ++ ")")
          | _, values => pure ("(" ++ String.intercalate " " (displayName :: values) ++ ")")
    | _ => none
  termination_by pattern => sizeOf pattern
  decreasing_by all_goals sizeOf_pattern_dec

  private def patternTextsWith? (source : Presentation) (displayNames : List String)
      (notations : List (Option Notation)) (locals : List String) (useNotation : Bool) : List Pattern → Option (List String)
    | [] => some []
    | first :: rest => do
        let first' ← patternTextWith? source displayNames notations locals useNotation first
        let rest' ← patternTextsWith? source displayNames notations locals useNotation rest
        pure (first' :: rest')
  termination_by patterns => sizeOf patterns
  decreasing_by all_goals sizeOf_pattern_dec
end

mutual
  private theorem patternTextWith?_eq (source : Presentation) (locals : List String)
      (useNotation : Bool) (pattern : Pattern) :
      patternTextWith? source (constructorNames source) (selectedNotations source useNotation) locals useNotation pattern =
        patternText? source locals useNotation pattern := by
    cases pattern with
    | apply label arguments =>
      simp only [patternTextWith?, patternText?]
      rw [patternTextsWith?_eq source locals useNotation arguments]
      simp_rw [selectedNotations_lookup]
    | _ => simp only [patternTextWith?, patternText?]
  termination_by sizeOf pattern
  decreasing_by all_goals simp_wf

  private theorem patternTextsWith?_eq (source : Presentation) (locals : List String)
      (useNotation : Bool) (patterns : List Pattern) :
      patternTextsWith? source (constructorNames source) (selectedNotations source useNotation) locals useNotation patterns =
        patternTexts? source locals useNotation patterns := by
    cases patterns with
    | nil => simp only [patternTextsWith?, patternTexts?]
    | cons first rest =>
      simp only [patternTextsWith?, patternTexts?]
      rw [patternTextWith?_eq source locals useNotation first, patternTextsWith?_eq source locals useNotation rest]
  termination_by sizeOf patterns
  decreasing_by all_goals simp_wf; all_goals omega
end

private def patternTextFast? (source : Presentation) (locals : List String)
    (useNotation : Bool) : Pattern → Option String :=
  patternTextWith? source (constructorNames source) (selectedNotations source useNotation) locals useNotation

@[csimp] theorem patternText?_cached : patternText? = patternTextFast? := by
  funext source locals useNotation pattern
  exact (patternTextWith?_eq source locals useNotation pattern).symm

def expression? (source : Presentation) (locals : List String) (expression : Preterm)
    (useNotation : Bool := true) : Option String := do
  let named ← decode source.syntaxSignature.names expression
  patternText? source locals useNotation named

def binders? (source : Presentation) (locals : List String) (context : Context) : Option String := do
  if locals.length != context.length then none else do
    let entries ← (locals.zip context).mapM fun (label, binder) =>
      match binder with
      | .bound _ => none
      | .regular sort dependencies => do
          if dependencies ≠ ∅ then none else do
            let sortName ← (sortNames source)[sort]?
            pure ("(" ++ label ++ ": " ++ sortName ++ ")")
    pure (if entries.isEmpty then "" else " " ++ String.intercalate " " entries)

def sortDeclaration? (source : Presentation) (entry : Nat × SortInfo) : Option String := do
  let label ← (sortNames source)[entry.1]?
  let info := entry.2
  pure ((if info.pure then "pure " else "") ++ (if info.strict then "strict " else "") ++
    (if info.provable then "provable " else "") ++ (if info.free then "free " else "") ++
    "sort " ++ label ++ ";")

def termDeclaration? (source : Presentation) (entry : Nat × TermDecl) : Option String := do
  let label ← (constructorNames source)[entry.1]?
  let row ← source.syntaxSignature.language.terms[entry.1]?
  let locals := parameterNames (sortNames source ++ constructorNames source ++ ruleNames source)
    (row.params.map TermParam.bodyName)
  let arguments ← binders? source locals entry.2.arguments
  let result ← (sortNames source)[entry.2.resultSort]?
  pure ("term " ++ label ++ arguments ++ ": " ++ result ++ ";")

/-- A defined constructor, with its body in application syntax. -/
def definitionDeclaration? (source : Presentation)
    (entry : Nat × TermDecl × Definition.Body) : Option String := do
  let label ← (constructorNames source)[entry.1]?
  let row ← source.syntaxSignature.language.terms[entry.1]?
  let locals := parameterNames (sortNames source ++ constructorNames source ++ ruleNames source)
    (row.params.map TermParam.bodyName)
  let arguments ← binders? source locals entry.2.1.arguments
  let result ← (sortNames source)[entry.2.1.resultSort]?
  if entry.2.2.dummies ≠ [] then none else do
    let body ← expression? source locals entry.2.2.expression false
    pure ("def " ++ label ++ arguments ++ ": " ++ result ++ " = $ " ++ body ++ " $;")

def notationDeclaration? (source : Presentation) (index : Nat) : Option String := do
  let displayNotation ← notation? source index
  let label ← (constructorNames source)[index]?
  match displayNotation with
  | .prefixToken token => pure ("prefix " ++ label ++ ": $" ++ token ++ "$ prec max;")
  | .infixToken token => pure ("infixl " ++ label ++ ": $" ++ token ++ "$ prec 25;")

def assertion? (source : Presentation) (kind label : String) (authoredLocals : List String)
    (declaration : TheoremDecl) : Option String := do
  let locals := parameterNames (sortNames source ++ constructorNames source ++ ruleNames source) authoredLocals
  let arguments ← binders? source locals declaration.arguments
  let hypotheses ← declaration.hypotheses.mapM (fun term => expression? source locals term)
  let conclusion ← expression? source locals declaration.conclusion
  let formulas := (hypotheses ++ [conclusion]).map (fun formula => "$ " ++ formula ++ " $")
  pure (kind ++ " " ++ label ++ arguments ++ ":\n  " ++ String.intercalate " >\n  " formulas)

def axiomDeclaration? (source : Presentation) (entry : Nat × TheoremDecl) : Option String := do
  let label ← (ruleNames source)[entry.1]?
  let row ← source.rules[entry.1]?
  let text ← assertion? source "axiom" label row.row.vars entry.2
  pure (text ++ ";")

/-- Print the compiled theory, with syntax declarations before all
assertions: sorts, primitive constructors, definitions in authored order,
then notation. -/
def theory? (source : Presentation) : Option String := do
  let sorts ← source.theory.sorts.mapM (sortDeclaration? source)
  let constructors ← (primitiveTerms source).mapM (termDeclaration? source)
  let definitions ← (definitionRows source).mapM (definitionDeclaration? source)
  let notations := (List.range source.syntaxSignature.names.length).filterMap (notationDeclaration? source)
  let axioms ← source.theory.theorems.mapM (axiomDeclaration? source)
  pure ("delimiter $ ( ) $;\n" ++
    String.intercalate "\n" (sorts ++ constructors ++ definitions ++ notations) ++
    "\n\n" ++ String.intercalate "\n\n" axioms ++ "\n")

/-- The two upstream textual evidence interfaces share the same compiled proof. -/
inductive ProofFormat where
  | mmu
  | mm1
  deriving DecidableEq

mutual
  def proofText? (source : Presentation) (context : Context) (locals hypotheses : List String)
      (format : ProofFormat) : ProofWitness → Option String
    | .hyp index => hypotheses[index]?
    | .theoremApp index arguments children => do
        let label ← (ruleNames source)[index]?
        let declaration ← source.theory.theoremSignature index
        if arguments.length != declaration.arguments.length ||
            children.length != declaration.hypotheses.length then none else do
          let arguments' ← arguments.mapM (fun argument => expression? source locals argument false)
          let children' ← proofTexts? source context locals hypotheses format children
          match format with
          | .mmu => pure ("(" ++ label ++ " (" ++ String.intercalate " " arguments' ++ ")" ++
              (if children'.isEmpty then "" else " " ++ String.intercalate " " children') ++ ")")
          | .mm1 => pure ("(! " ++ label ++
              (String.join (arguments'.map (fun argument => " $ " ++ argument ++ " $"))) ++
              (if children'.isEmpty then "" else " " ++ String.intercalate " " children') ++ ")")
    | .conversion witness child => do
        match format with
        | .mmu => none
        | .mm1 =>
            let converted ← witness.conversion? source.theory.termSignature
              source.theory.definitionSignature context
            let target ← expression? source locals converted.right false
            let child' ← proofText? source context locals hypotheses format child
            pure ("{" ++ child' ++ " : $ " ++ target ++ " $}")
  termination_by proof => sizeOf proof
  decreasing_by all_goals simp_wf

  def proofTexts? (source : Presentation) (context : Context) (locals hypotheses : List String)
      (format : ProofFormat) : List ProofWitness → Option (List String)
    | [] => some []
    | first :: rest => do
        let first' ← proofText? source context locals hypotheses format first
        let rest' ← proofTexts? source context locals hypotheses format rest
        pure (first' :: rest')
  termination_by proofs => sizeOf proofs
  decreasing_by
    all_goals simp_wf
    all_goals omega
end

private def expressionWith? (source : Presentation) (displayNames locals : List String)
    (expression : Preterm) : Option String := do
  let named ← decode source.syntaxSignature.names expression
  patternTextWith? source displayNames (selectedNotations source false) locals false named

private theorem expressionWith?_eq (source : Presentation) (locals : List String)
    (expression : Preterm) :
    expressionWith? source (constructorNames source) locals expression =
      expression? source locals expression false := by
  simp only [expressionWith?, expression?]
  simp_rw [patternTextWith?_eq]

private theorem expressionWith?_function_eq (source : Presentation) (locals : List String) :
    expressionWith? source (constructorNames source) locals =
      fun expression => expression? source locals expression false := by
  funext expression
  exact expressionWith?_eq source locals expression

mutual
  private def proofTextWith? (source : Presentation) (context : Context)
      (displayNames rules locals hypotheses : List String) (format : ProofFormat) :
      ProofWitness → Option String
    | .hyp index => hypotheses[index]?
    | .theoremApp index arguments children => do
        let label ← rules[index]?
        let declaration ← source.theory.theoremSignature index
        if arguments.length != declaration.arguments.length ||
            children.length != declaration.hypotheses.length then none else do
          let arguments' ← arguments.mapM (expressionWith? source displayNames locals)
          let children' ← proofTextsWith? source context displayNames rules locals hypotheses format children
          match format with
          | .mmu => pure ("(" ++ label ++ " (" ++ String.intercalate " " arguments' ++ ")" ++
              (if children'.isEmpty then "" else " " ++ String.intercalate " " children') ++ ")")
          | .mm1 => pure ("(! " ++ label ++
              (String.join (arguments'.map (fun argument => " $ " ++ argument ++ " $"))) ++
              (if children'.isEmpty then "" else " " ++ String.intercalate " " children') ++ ")")
    | .conversion witness child => do
        match format with
        | .mmu => none
        | .mm1 =>
            let converted ← witness.conversion? source.theory.termSignature
              source.theory.definitionSignature context
            let target ← expressionWith? source displayNames locals converted.right
            let child' ← proofTextWith? source context displayNames rules locals hypotheses format child
            pure ("{" ++ child' ++ " : $ " ++ target ++ " $}")
  termination_by proof => sizeOf proof
  decreasing_by all_goals simp_wf

  private def proofTextsWith? (source : Presentation) (context : Context)
      (displayNames rules locals hypotheses : List String) (format : ProofFormat) :
      List ProofWitness → Option (List String)
    | [] => some []
    | first :: rest => do
        let first' ← proofTextWith? source context displayNames rules locals hypotheses format first
        let rest' ← proofTextsWith? source context displayNames rules locals hypotheses format rest
        pure (first' :: rest')
  termination_by proofs => sizeOf proofs
  decreasing_by all_goals simp_wf; all_goals omega
end

mutual
  private theorem proofTextWith?_eq (source : Presentation) (context : Context)
      (locals hypotheses : List String) (format : ProofFormat) (proof : ProofWitness) :
      proofTextWith? source context (constructorNames source) (ruleNames source) locals hypotheses format proof =
        proofText? source context locals hypotheses format proof := by
    cases proof with
    | hyp index => simp only [proofTextWith?, proofText?]
    | theoremApp index arguments children =>
      simp only [proofTextWith?, proofText?]
      rw [expressionWith?_function_eq]
      rw [proofTextsWith?_eq source context locals hypotheses format children]
    | conversion witness child =>
      cases format with
      | mmu => simp only [proofTextWith?, proofText?]
      | mm1 =>
        simp only [proofTextWith?, proofText?]
        simp_rw [expressionWith?_eq]
        rw [proofTextWith?_eq source context locals hypotheses .mm1 child]
  termination_by sizeOf proof
  decreasing_by all_goals simp_wf

  private theorem proofTextsWith?_eq (source : Presentation) (context : Context)
      (locals hypotheses : List String) (format : ProofFormat) (proofs : List ProofWitness) :
      proofTextsWith? source context (constructorNames source) (ruleNames source) locals hypotheses format proofs =
        proofTexts? source context locals hypotheses format proofs := by
    cases proofs with
    | nil => simp only [proofTextsWith?, proofTexts?]
    | cons first rest =>
      simp only [proofTextsWith?, proofTexts?]
      rw [proofTextWith?_eq source context locals hypotheses format first,
        proofTextsWith?_eq source context locals hypotheses format rest]
  termination_by sizeOf proofs
  decreasing_by all_goals simp_wf; all_goals omega
end

private def proofTextFast? (source : Presentation) (context : Context)
    (locals hypotheses : List String) (format : ProofFormat) : ProofWitness → Option String :=
  proofTextWith? source context (constructorNames source) (ruleNames source) locals hypotheses format

@[csimp] theorem proofText?_cached : proofText? = proofTextFast? := by
  funext source context locals hypotheses format proof
  exact (proofTextWith?_eq source context locals hypotheses format proof).symm

def mmuBinders? (source : Presentation) (locals : List String) (context : Context) : Option String := do
  if locals.length != context.length then none else do
    let entries ← (locals.zip context).mapM fun (label, binder) =>
      match binder with
      | .bound _ => none
      | .regular sort dependencies => do
          if dependencies ≠ ∅ then none else do
            let sortName ← (sortNames source)[sort]?
            pure ("(" ++ label ++ " " ++ sortName ++ " ())")
    pure ("(" ++ String.intercalate " " entries ++ ")")

def mmuSort? (source : Presentation) (entry : Nat × SortInfo) : Option String := do
  let label ← (sortNames source)[entry.1]?
  let info := entry.2
  pure ("(sort " ++ label ++ (if info.pure then " pure" else "") ++
    (if info.strict then " strict" else "") ++ (if info.provable then " provable" else "") ++
    (if info.free then " free" else "") ++ ")")

def mmuTerm? (source : Presentation) (entry : Nat × TermDecl) : Option String := do
  let label ← (constructorNames source)[entry.1]?
  let row ← source.syntaxSignature.language.terms[entry.1]?
  let locals := parameterNames (sortNames source ++ constructorNames source ++ ruleNames source)
    (row.params.map TermParam.bodyName)
  let arguments ← mmuBinders? source locals entry.2.arguments
  let result ← (sortNames source)[entry.2.resultSort]?
  pure ("(term " ++ label ++ " " ++ arguments ++ " (" ++ result ++ " ()))")

def mmuDefinition? (source : Presentation)
    (entry : Nat × TermDecl × Definition.Body) : Option String := do
  let label ← (constructorNames source)[entry.1]?
  let row ← source.syntaxSignature.language.terms[entry.1]?
  let locals := parameterNames (sortNames source ++ constructorNames source ++ ruleNames source)
    (row.params.map TermParam.bodyName)
  let arguments ← mmuBinders? source locals entry.2.1.arguments
  let result ← (sortNames source)[entry.2.1.resultSort]?
  if entry.2.2.dummies ≠ [] then none else do
    let body ← expression? source locals entry.2.2.expression false
    pure ("(def " ++ label ++ " " ++ arguments ++ " (" ++ result ++ " ()) () " ++ body ++ ")")

def mmuAxiom? (source : Presentation) (entry : Nat × TheoremDecl) : Option String := do
  let label ← (ruleNames source)[entry.1]?
  let row ← source.rules[entry.1]?
  let locals := parameterNames (sortNames source ++ constructorNames source ++ ruleNames source) row.row.vars
  let arguments ← mmuBinders? source locals entry.2.arguments
  let hypotheses ← entry.2.hypotheses.mapM (fun expression => expression? source locals expression false)
  let conclusion ← expression? source locals entry.2.conclusion false
  pure ("(axiom " ++ label ++ " " ++ arguments ++ " (" ++ String.intercalate " " hypotheses ++
    ") " ++ conclusion ++ ")")

def mmuTheory? (source : Presentation) : Option String := do
  let sorts ← source.theory.sorts.mapM (mmuSort? source)
  let constructors ← (primitiveTerms source).mapM (mmuTerm? source)
  let definitions ← (definitionRows source).mapM (mmuDefinition? source)
  let axioms ← source.theory.theorems.mapM (mmuAxiom? source)
  pure (String.intercalate "\n" (sorts ++ constructors ++ definitions ++ axioms) ++ "\n")

def hypothesisNames (count : Nat) : List String :=
  (List.range count).map (fun index => "mm0__hyp_" ++ toString index)

/-- A new public theorem cannot shadow any compiled declaration. -/
def freshLabel (source : Presentation) (label : String) : Bool :=
  identifier label && !(sortNames source ++ constructorNames source ++ ruleNames source).contains label

def specification? (source : Presentation) (label : String) (authoredLocals : List String)
    (declaration : TheoremDecl) : Option String := do
  if !freshLabel source label then none else do
    let theory ← theory? source
    let statement ← assertion? source "theorem" label authoredLocals declaration
    pure (theory ++ "\n" ++ statement ++ ";\n")

/-- Assemble either native proof file from already printed evidence. Both
ordinary and chronological certificates share the same declaration and name
resolution path. MM1 evidence is a complete Lisp expression. -/
def proofFile? (source : Presentation) (label : String) (authoredLocals : List String)
    (declaration : TheoremDecl) (format : ProofFormat) (evidence : String) : Option String := do
  if !freshLabel source label then none else do
    let locals := parameterNames (sortNames source ++ constructorNames source ++ ruleNames source) authoredLocals
    match format with
    | .mmu =>
      let theory ← mmuTheory? source
      let arguments ← mmuBinders? source locals declaration.arguments
      let hypotheses ← declaration.hypotheses.mapM (fun expression => expression? source locals expression false)
      let names := hypothesisNames hypotheses.length
      let named := (names.zip hypotheses).map (fun (name, expression) => "(" ++ name ++ " " ++ expression ++ ")")
      let conclusion ← expression? source locals declaration.conclusion false
      pure (theory ++ "\n(theorem " ++ label ++ " " ++ arguments ++ " (" ++
        String.intercalate " " named ++ ") " ++ conclusion ++ " () " ++ evidence ++ ")\n")
    | .mm1 =>
      let theory ← theory? source
      let arguments ← binders? source locals declaration.arguments
      let hypotheses ← declaration.hypotheses.mapM (fun expression => expression? source locals expression)
      let names := hypothesisNames hypotheses.length
      let named := (names.zip hypotheses).map (fun (name, expression) =>
        " (" ++ name ++ ": $ " ++ expression ++ " $)")
      let conclusion ← expression? source locals declaration.conclusion
      pure (theory ++ "\npub theorem " ++ label ++ arguments ++ String.join named ++
        ": $ " ++ conclusion ++ " $ = " ++ evidence ++ ";\n")

def mmu? (source : Presentation) (label : String) (authoredLocals : List String)
    (declaration : TheoremDecl) (proof : ProofWitness) : Option String := do
  let locals := parameterNames (sortNames source ++ constructorNames source ++ ruleNames source) authoredLocals
  let evidence ← proofText? source declaration.arguments locals (hypothesisNames declaration.hypotheses.length) .mmu proof
  proofFile? source label authoredLocals declaration .mmu evidence

/-- Explicit MM1 arguments prevent the reference producer from filling in a
different argument vector. Its output is used only by the independent binary checker. -/
def mm1? (source : Presentation) (label : String) (authoredLocals : List String)
    (declaration : TheoremDecl) (proof : ProofWitness) : Option String := do
  let locals := parameterNames (sortNames source ++ constructorNames source ++ ruleNames source) authoredLocals
  let evidence ← proofText? source declaration.arguments locals (hypothesisNames declaration.hypotheses.length) .mm1 proof
  proofFile? source label authoredLocals declaration .mm1 ("'" ++ evidence)

/-- Each chronological entry gets its own local name, including duplicates
and entries unused by the root. These names occupy a separate printer namespace. -/
def savedNames (count : Nat) : List String :=
  (List.range count).map (fun index => "mm0__saved_" ++ toString index)

/-- Check and print each submitted initializer against the original kernel
and the previously saved claims. The returned rows retain the exact explicit
claim and the supplied proof; later names are unavailable while printing. -/
def savedEntries? (source : Presentation) (context : Context) (locals : List String)
    (format : ProofFormat) : List Preterm → List String → Nat →
      List (Preterm × ProofWitness) → Option (List (String × String × String))
  | _, _, _, [] => some []
  | hypotheses, names, next, (claim, proof) :: rest => do
      if !ProofWitness.check source.theory.termSignature source.theory.definitionSignature
          source.theory.theoremSignature context hypotheses proof claim then none else do
        let name := "mm0__saved_" ++ toString next
        if (sortNames source ++ constructorNames source ++ ruleNames source ++ locals ++ names).contains name
          then none else do
          let claimText ← expression? source locals claim false
          let proofText ← proofText? source context locals names format proof
          let remaining ← savedEntries? source context locals format
            (hypotheses ++ [claim]) (names ++ [name]) (next + 1) rest
          pure ((name, claimText, proofText) :: remaining)

/-- MMU uses its original lexical `:let`; the reflexive conversion ascription
also records the submitted saved goal. MM1 uses goal-bearing `have` steps in
one `focus` block, the reference producer's local proof-sharing interface. -/
def savedProofText? (source : Presentation) (context : Context) (locals names : List String)
    (hypotheses : List Preterm) (format : ProofFormat)
    (saved : List (Preterm × ProofWitness)) (claim : Preterm) (proof : ProofWitness) : Option String := do
  let entries ← savedEntries? source context locals format hypotheses names 0 saved
  if !ProofWitness.check source.theory.termSignature source.theory.definitionSignature
      source.theory.theoremSignature context (hypotheses ++ saved.map Prod.fst) proof claim then none else do
    let root ← proofText? source context locals (names ++ savedNames saved.length) format proof
    match format with
    | .mmu => pure (entries.foldr (fun (name, goal, initializer) body =>
        "(:let " ++ name ++ " (:conv " ++ goal ++ " " ++ goal ++ " " ++ initializer ++ ")\n" ++ body ++ ")") root)
    | .mm1 => pure ("(focus\n" ++ String.join (entries.map (fun (name, goal, initializer) =>
        "  (have '" ++ name ++ " $ " ++ goal ++ " $ '" ++ initializer ++ ")\n")) ++ "  '" ++ root ++ ")")

/-- A saved proof file checks every submitted initializer and its root before
emission. All entries, including unused ones, survive as chronological local
proof bindings. The specification is the existing `specification?` output. -/
def savedMmu? (source : Presentation) (label : String) (authoredLocals : List String)
    (declaration : TheoremDecl) (certificate : List (Preterm × ProofWitness) × ProofWitness) : Option String := do
  let locals := parameterNames (sortNames source ++ constructorNames source ++ ruleNames source) authoredLocals
  let evidence ← savedProofText? source declaration.arguments locals (hypothesisNames declaration.hypotheses.length)
    declaration.hypotheses .mmu certificate.1 declaration.conclusion certificate.2
  proofFile? source label authoredLocals declaration .mmu evidence

/-- The reference MM1 producer receives the same explicit goals, ordered
initializers, original root and local proof references as the MMU printer. -/
def savedMm1? (source : Presentation) (label : String) (authoredLocals : List String)
    (declaration : TheoremDecl) (certificate : List (Preterm × ProofWitness) × ProofWitness) : Option String := do
  let locals := parameterNames (sortNames source ++ constructorNames source ++ ruleNames source) authoredLocals
  let evidence ← savedProofText? source declaration.arguments locals (hypothesisNames declaration.hypotheses.length)
    declaration.hypotheses .mm1 certificate.1 declaration.conclusion certificate.2
  proofFile? source label authoredLocals declaration .mm1 evidence

theorem savedEntries?_checked (source : Presentation) (context : Context)
    (locals : List String) (format : ProofFormat) (hypotheses : List Preterm)
    (before : List (Preterm × ProofWitness)) (checked : SavedWitnessesChecked
      source.theory.termSignature source.theory.definitionSignature source.theory.theoremSignature
      context hypotheses before) (names : List String) (next : Nat)
    (saved : List (Preterm × ProofWitness)) (rows : List (String × String × String))
    (printed : savedEntries? source context locals format (hypotheses ++ before.map Prod.fst)
      names next saved = some rows) :
    SavedWitnessesChecked source.theory.termSignature source.theory.definitionSignature
      source.theory.theoremSignature context hypotheses (before ++ saved) := by
  induction saved generalizing before names next rows with
  | nil => simpa using checked
  | cons entry rest ih =>
    rcases entry with ⟨claim,proof⟩
    cases accepted : ProofWitness.check source.theory.termSignature source.theory.definitionSignature
      source.theory.theoremSignature context (hypotheses ++ before.map Prod.fst) proof claim with
    | false => simp [savedEntries?,accepted] at printed
    | true =>
      let name := "mm0__saved_" ++ toString next
      simp only [savedEntries?,accepted,Bool.not_true,Bool.false_eq_true,↓reduceIte] at printed
      split at printed
      · cases printed
      · cases goalText : expression? source locals claim false with
        | none => simp only [goalText] at printed; cases printed
        | some goalText =>
          simp only [goalText] at printed
          cases proofText : proofText? source context locals names format proof with
          | none => simp only [proofText] at printed; cases printed
          | some proofText =>
            simp only [proofText] at printed
            cases remainingEq : savedEntries? source context locals format
              ((hypotheses ++ before.map Prod.fst) ++ [claim]) (names ++ [name]) (next+1) rest with
            | none => simp only [name,remainingEq] at printed; cases printed
            | some remaining =>
              have recorded := SavedWitnessesChecked.record checked accepted
              have inherited : savedEntries? source context locals format
                (hypotheses ++ (before ++ [(claim,proof)]).map Prod.fst)
                (names ++ [name]) (next+1) rest=some remaining := by
                simpa only [List.map_append,List.map_cons,List.map_nil,List.append_assoc] using remainingEq
              have joined:=ih (before ++[(claim,proof)]) recorded (names++[name]) (next+1) remaining inherited
              simpa only [List.append_assoc,List.cons_append,List.nil_append] using joined

theorem savedProofText?_checked (source : Presentation) (context : Context)
    (locals names : List String) (hypotheses : List Preterm) (format : ProofFormat)
    (saved : List (Preterm × ProofWitness)) (claim : Preterm) (proof : ProofWitness) (text : String)
    (printed : savedProofText? source context locals names hypotheses format saved claim proof=some text) :
    SavedWitnessesChecked source.theory.termSignature source.theory.definitionSignature
      source.theory.theoremSignature context hypotheses saved ∧
    ProofWitness.check source.theory.termSignature source.theory.definitionSignature
      source.theory.theoremSignature context (hypotheses ++ saved.map Prod.fst) proof claim=true := by
  cases entries : savedEntries? source context locals format hypotheses names 0 saved with
  | none => simp [savedProofText?,entries] at printed
  | some rows =>
    cases accepted : ProofWitness.check source.theory.termSignature source.theory.definitionSignature
      source.theory.theoremSignature context (hypotheses ++ saved.map Prod.fst) proof claim with
    | false => simp [savedProofText?,entries,accepted] at printed
    | true =>
      refine ⟨?_,rfl⟩
      have entries' : savedEntries? source context locals format (hypotheses ++ ([] : List (Preterm × ProofWitness)).map Prod.fst) names 0 saved=some rows := by
        simpa using entries
      simpa using savedEntries?_checked source context locals format hypotheses [] .nil names 0 saved rows entries'

theorem savedProofText?_sound (source : Presentation) (context : Context)
    (locals names : List String) (hypotheses : List Preterm) (format : ProofFormat)
    (saved : List (Preterm × ProofWitness)) (claim : Preterm) (proof : ProofWitness) (text : String)
    (printed : savedProofText? source context locals names hypotheses format saved claim proof=some text) :
    Kernel.Derives source.theory.termSignature source.theory.definitionSignature
      source.theory.theoremSignature context hypotheses claim := by
  obtain ⟨stored,root⟩:=savedProofText?_checked source context locals names hypotheses format saved claim proof text printed
  exact stored.root_sound root

theorem savedMmu?_sound (source : Presentation) (label : String) (authoredLocals : List String)
    (declaration : TheoremDecl) (certificate : List (Preterm × ProofWitness) × ProofWitness)
    (text : String) (printed : savedMmu? source label authoredLocals declaration certificate=some text) :
    Kernel.Derives source.theory.termSignature source.theory.definitionSignature
      source.theory.theoremSignature declaration.arguments declaration.hypotheses declaration.conclusion := by
  cases generated : savedProofText? source declaration.arguments
    (parameterNames (sortNames source ++ constructorNames source ++ ruleNames source) authoredLocals)
    (hypothesisNames declaration.hypotheses.length) declaration.hypotheses .mmu
    certificate.1 declaration.conclusion certificate.2 with
  | none => simp only [savedMmu?,generated] at printed; cases printed
  | some evidence =>
    exact savedProofText?_sound source declaration.arguments _ _ declaration.hypotheses .mmu
      certificate.1 declaration.conclusion certificate.2 evidence generated

theorem savedMm1?_sound (source : Presentation) (label : String) (authoredLocals : List String)
    (declaration : TheoremDecl) (certificate : List (Preterm × ProofWitness) × ProofWitness)
    (text : String) (printed : savedMm1? source label authoredLocals declaration certificate=some text) :
    Kernel.Derives source.theory.termSignature source.theory.definitionSignature
      source.theory.theoremSignature declaration.arguments declaration.hypotheses declaration.conclusion := by
  cases generated : savedProofText? source declaration.arguments
    (parameterNames (sortNames source ++ constructorNames source ++ ruleNames source) authoredLocals)
    (hypothesisNames declaration.hypotheses.length) declaration.hypotheses .mm1
    certificate.1 declaration.conclusion certificate.2 with
  | none => simp only [savedMm1?,generated] at printed; cases printed
  | some evidence =>
    exact savedProofText?_sound source declaration.arguments _ _ declaration.hypotheses .mm1
      certificate.1 declaration.conclusion certificate.2 evidence generated

end Mettapedia.Languages.MM0.Translation.FirstOrderPrinting
