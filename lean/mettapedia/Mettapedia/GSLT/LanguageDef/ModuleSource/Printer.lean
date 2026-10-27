import Mettapedia.GSLT.LanguageDef.ModuleSource.Elaborate
import Mettapedia.OSLF.MeTTaIL.Export

/-!
# Printing `.module` text

`print` writes a module back in the format: imports, the module's theories and its entry. Rows are
written as `languageDef!` writes them; a bound variable is written by its binder's name, an
application of an authored abstraction as `(subst body argument)`, a nullary constructor as
`(Zero)`, a curried binder type as `[A -> B -> C]` (an arrow domain in parentheses). Equations are anonymous in the format and are written without their generated names.

`#module_roundtrip X` (in `ModuleSource.Commands`) prints `X.module`, reads the text back with the
same syntax and checks that the data is unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.Printer

open Mettapedia.OSLF.MeTTaIL.Syntax

private def quote (text : String) : String := "\"" ++ text ++ "\""

private def commas (parts : List String) : String := ", ".intercalate parts

/-! ## Rows -/

/-- A type as rows write it: an arrow's codomain without brackets, an arrow domain in parentheses. -/
def type : TypeExpr → String
  | .base name => name
  | .arrow domain codomain =>
      let left := match domain with
        | .arrow _ _ => "(" ++ type domain ++ ")"
        | _ => type domain
      left ++ " -> " ++ type codomain
  | .multiBinder element => type element ++ "*"
  | .collection kind element =>
      let collection := match kind with | .vec => "Vec" | .hashBag => "HashBag" | .hashSet => "HashSet"
      collection ++ "(" ++ type element ++ ")"

/-- Whether a label reads as an identifier. -/
private def identifierLike (label : String) : Bool :=
  match label.toList with
  | [] => false
  | first :: rest => (first.isAlpha || first == '_') && rest.all fun c => c.isAlphanum || c == '_'

/-- A pattern, with the names of the enclosing binders, innermost first. A constant whose label is not an identifier
is written as a string, which reads back as that constant. -/
def pattern (names : List String) : Pattern → String
  | .bvar index => (names[index]?).getD s!"#{index}"
  | .fvar name => name
  | .apply label [] => if identifierLike label then s!"({label})" else quote label
  | .apply label arguments =>
      if label == Pattern.evalHead then
        "(subst " ++ " ".intercalate (arguments.map (pattern names)) ++ ")"
      else
        "(" ++ label ++ " " ++ " ".intercalate (arguments.map (pattern names)) ++ ")"
  | .lambda binder body =>
      let name := binder.getD s!"x{names.length}"
      s!"^{name}." ++ pattern (name :: names) body
  | .multiLambda _ binders body =>
      "^[" ++ ",".intercalate binders ++ "]." ++ pattern (binders.reverse ++ names) body
  | .subst body replacement => "(eval " ++ pattern names body ++ " " ++ pattern names replacement ++ ")"
  | .collection kind elements rest =>
      let open_ := match kind with | .hashBag => "{" | .vec => "[" | .hashSet => "#{"
      let close := match kind with | .hashBag => "}" | .vec => "]" | .hashSet => "}"
      let items := elements.map (pattern names) ++ (rest.map (fun name => s!"...{name}")).toList
      open_ ++ commas items ++ close
decreasing_by all_goals sizeOf_pattern_dec

def premise : Premise → String
  | .freshness condition =>
      match condition.term with
      | .collection _ [] (some rest) => s!"{condition.varName} # ...{rest}"
      | term => s!"{condition.varName} # {pattern [] term}"
  | .congruence source target => s!"{pattern [] source} ~> {pattern [] target}"
  | .scopedStep step =>
      s!"scopedStep([{commas (step.binders.map type)}], {type step.resultType}, " ++
        s!"{pattern [] step.source}, {pattern [] step.target})"
  | .relationQuery relation arguments => s!"{relation}({commas (arguments.map (pattern []))})"
  | .forAll collection param body => s!"forAll({collection}, {param}, {premise body})"

def termParam : TermParam → String
  | .simple name sort => s!"{name}:{type sort}"
  | .abstractionNamed binder name sort => s!"^{binder.getD "x"}.{name}:[{type sort}]"
  | .multiAbstractionNamed binders name sort => s!"^[{",".intercalate binders}].{name}:[{type sort}]"

mutual

def syntaxOp : SyntaxPatternOp → String
  | .var name => name
  | .sep collection separator none => s!"{collection}.*sep({quote separator})"
  | .sep _ separator (some source) => s!"{syntaxOp source}.*sep({quote separator})"
  | .zip left right => s!"*zip({left}, {right})"
  | .map source params body => s!"{syntaxOp source}.*map(|{commas params}| {" ".intercalate (body.map syntaxItem)})"
  | .opt inner => s!"*opt({" ".intercalate (inner.map syntaxItem)})"

def syntaxItem : SyntaxItem → String
  | .terminal text => quote text
  | .nonTerminal name => name
  | .separator text => quote text
  | .delimiter left right => quote left ++ " " ++ quote right
  | .op op => syntaxOp op

end

def evalPolicy : Option TermEvalPolicy → String
  | none => ""
  | some .rewrite => " ![rewrite]"
  | some .fold => " ![fold]"
  | some .oracle => " ![oracle]"

def rule (row : GrammarRule) : String :=
  s!"{quote row.label} . {commas (row.params.map termParam)} |- {" ".intercalate (row.syntaxPattern.map syntaxItem)} : " ++
    s!"{row.category}{evalPolicy row.evalPolicy?};"

private def guarded (premises : List Premise) (body : String) : String :=
  if premises.isEmpty then body else s!"if {commas (premises.map premise)} then {body}"

def equation (row : Equation) : String :=
  guarded row.premises s!"{pattern [] row.left} == {pattern [] row.right};"

def rewrite (row : RewriteRule) : String :=
  s!"{row.name} : " ++ guarded row.premises s!"{pattern [] row.left} ~> {pattern [] row.right};"

/-! ## Modules -/

private def blockLines (title : String) (rows : List String) : List String :=
  [title ++ " {"] ++ rows.map ("  " ++ ·) ++ ["}"]

/-- A type row: the sort, with its carrier when it is not the abstract syntax. CeTTa's core names the builtin
carriers `String`, `Int` and `Bool`; the token carriers keep the names of `languageDef!`. -/
def typeRow (declaration : TypeDecl) : String :=
  match declaration.carrier with
  | .ast => declaration.name ++ ";"
  | .builtinString => declaration.name ++ " = String;"
  | .builtinInt => declaration.name ++ " = Int;"
  | .builtinBool => declaration.name ++ " = Bool;"
  | .tokenLabel => declaration.name ++ " = label;"
  | .tokenRaw => declaration.name ++ " = raw;"
  | .tokenProof => declaration.name ++ " = proofTok;"
  | .tokenPath => declaration.name ++ " = path;"

def block : Block → List String
  | .types declarations => blockLines "Types" (declarations.map typeRow)
  | .exports rows => blockLines "Exports" (rows.map fun row => match row.renamed with
      | none => row.sort ++ ";"
      | some target => s!"{row.sort} => {target};")
  | .terms rows => blockLines "Terms" (rows.map rule)
  | .replacements rows => blockLines "Replacements" (rows.map fun row => s!"{row.old} => {rule row.rule}")
  | .equations rows => blockLines "Equations" (rows.map equation)
  | .rewrites rows => blockLines "Rewrites" (rows.map rewrite)
  | .inductives families => blockLines "Inductives" (families.map InductiveSyntax.Family.print)

def path (parts : Path) : String := ".".intercalate parts

/-- A theory expression at a precedence: a join is 10, an extension 50, an atom 100. -/
partial def expr (context : Nat) : Expr → List String
  | .ref name => [name]
  | .apply target args => [path target ++ "(" ++ commas (args.map fun arg => " ".intercalate (expr 0 arg)) ++ ")"]
  | .join left right =>
      let text := expr 10 left ++ ["\\/"] ++ expr 11 right
      if context > 10 then ["{"] ++ text ++ ["}"] else text
  | .extend none [] => ["Empty"]
  | .extend base blocks =>
      let text := (base.map (expr 51)).getD [] ++ blocks.flatMap block
      if context > 50 then ["{"] ++ text ++ ["}"] else text
  | .letIn name value body =>
      let text := [s!"let {name} = " ++ " ".intercalate (expr 0 value) ++ " in ("] ++ expr 0 body ++ [")"]
      if context > 0 then ["("] ++ text ++ [")"] else text

def theory (row : Theory) : List String :=
  let params := commas (row.params.map fun param => s!"{param.name}: {path param.theory}")
  ["Theory " ++ row.name ++ "(" ++ params ++ ") {"] ++ (expr 0 row.body).map ("  " ++ ·) ++ ["}"]

/-- **A module as `.module` text.** -/
def print (module : Module) : String :=
  let imports := module.imports.map fun item => s!"import {quote item.file} as {item.qualifier}"
  let entry := match module.entry with
    | some (target, args) => [s!"theory {path target}(" ++ commas (args.map fun arg => " ".intercalate (expr 0 arg)) ++ ")"]
    | none => []
  let body := module.theories.flatMap theory ++ entry
  "\n".intercalate (imports ++ ["Module " ++ module.name ++ " {"] ++ body.map ("  " ++ ·) ++ ["}"]) ++ "\n"

end Mettapedia.GSLT.LanguageDef.ModuleSource.Printer
