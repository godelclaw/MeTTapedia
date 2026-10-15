import Mettapedia.Languages.MM0.Translation.FirstOrderModules
import Mettapedia.Languages.MM0.Translation.FirstOrderAdmission

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

def mmu? (source : Presentation) (label : String) (authoredLocals : List String)
    (declaration : TheoremDecl) (proof : ProofWitness) : Option String := do
  if !freshLabel source label then none else do
    let theory ← mmuTheory? source
    let locals := parameterNames (sortNames source ++ constructorNames source ++ ruleNames source) authoredLocals
    let arguments ← mmuBinders? source locals declaration.arguments
    let hypotheses ← declaration.hypotheses.mapM (fun expression => expression? source locals expression false)
    let names := hypothesisNames hypotheses.length
    let named := (names.zip hypotheses).map (fun (name, expression) => "(" ++ name ++ " " ++ expression ++ ")")
    let conclusion ← expression? source locals declaration.conclusion false
    let evidence ← proofText? source declaration.arguments locals names .mmu proof
    pure (theory ++ "\n(theorem " ++ label ++ " " ++ arguments ++ " (" ++
      String.intercalate " " named ++ ") " ++ conclusion ++ " () " ++ evidence ++ ")\n")

/-- Explicit MM1 arguments prevent the reference producer from filling in a
different argument vector. Its output is used only by the independent binary checker. -/
def mm1? (source : Presentation) (label : String) (authoredLocals : List String)
    (declaration : TheoremDecl) (proof : ProofWitness) : Option String := do
  if !freshLabel source label then none else do
    let theory ← theory? source
    let locals := parameterNames (sortNames source ++ constructorNames source ++ ruleNames source) authoredLocals
    let arguments ← binders? source locals declaration.arguments
    let hypotheses ← declaration.hypotheses.mapM (fun expression => expression? source locals expression)
    let names := hypothesisNames hypotheses.length
    let named := (names.zip hypotheses).map (fun (name, expression) =>
      " (" ++ name ++ ": $ " ++ expression ++ " $)")
    let conclusion ← expression? source locals declaration.conclusion
    let evidence ← proofText? source declaration.arguments locals names .mm1 proof
    pure (theory ++ "\npub theorem " ++ label ++ arguments ++ String.join named ++
      ": $ " ++ conclusion ++ " $ = '" ++ evidence ++ ";\n")

end Mettapedia.Languages.MM0.Translation.FirstOrderPrinting
