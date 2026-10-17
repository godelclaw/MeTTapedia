import Mettapedia.GSLT.LanguageDef.ModuleSource.Syntax
import Mettapedia.Languages.MeTTa.PeTTa.SpaceSemantics

/-!
# `.module` data from a grammar-driven parse

The `.module` grammar (`metta/gslt/module/module_v1.cf`) is LBNF data. CeTTa's grammar library
lowers it and parses `.module` files to labelled syntax trees: a node names its category and
production, a list carries its items, a token its decoded text. `decode` reads such a tree as
`ModuleSource.Module`, the data the Lean commands produce, row for row as `languageDef!` writes
them: a binder's name binds its occurrences by index, `(subst b a)` applies an abstraction, and
equations are named `Theory:equation:i` in order.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)

abbrev Decode := Except String

/-- Scalar text: `(bnf-v1:text-cons codepoint rest)` ending in `(bnf-v1:text-nil)`. -/
partial def text : Atom → Decode String
  | .expression [.symbol "bnf-v1:text-cons", .grounded (.int point), rest] => do
      pure (String.singleton (Char.ofNat point.toNat) ++ (← text rest))
  | .expression [.symbol "bnf-v1:text-nil"] => pure ""
  | .symbol "bnf-v1:text-nil" => pure ""
  | other => throw s!"not scalar text: {repr other}"

/-- A finite list `(LCons item rest)` ending in `LNil`. -/
partial def items : Atom → Decode (List Atom)
  | .expression [.symbol "LCons", item, rest] => do pure (item :: (← items rest))
  | .symbol "LNil" => pure []
  | other => throw s!"not a list: {repr other}"

/-- A node: its production label and children. -/
def node : Atom → Decode (String × List Atom)
  | .expression [.symbol "LbnfAstNodeV1", _, .grounded (.string label), _, children] => do
      pure (label, ← items children)
  | other => throw s!"not a node: {repr other}"

/-- A list node's items. -/
def list : Atom → Decode (List Atom)
  | .expression [.symbol "LbnfAstListV1", _, _, children] => items children
  | other => throw s!"not a list node: {repr other}"

/-- A token's decoded text. -/
def token : Atom → Decode String
  | .expression [.symbol "LbnfAstTokenV1", _, _, value, _, _, _] => text value
  | other => throw s!"not a token: {repr other}"

partial def path (atom : Atom) : Decode Path := do
  match ← node atom with
  | ("MPathOne", [name]) => pure [← token name]
  | ("MPathMore", [name, rest]) => pure ((← token name) :: (← path rest))
  | (label, _) => throw s!"unexpected path {label}"

/-! ## Rows -/

partial def typeExpr (atom : Atom) : Decode TypeExpr := do
  match ← node atom with
  | ("TyBase", [name]) => pure (.base (← token name))
  | ("TyColl", [kind, element]) =>
      let kind ← match ← token kind with
        | "HashBag" => pure CollType.hashBag
        | "HashSet" => pure CollType.hashSet
        | "Vec" => pure CollType.vec
        | other => throw s!"unknown collection {other}"
      pure (.collection kind (← typeExpr element))
  | ("TyArrow", [domain, codomain]) => pure (.arrow (← typeExpr domain) (← typeExpr codomain))
  | (label, _) => throw s!"unexpected type {label}"

def termParam (atom : Atom) : Decode TermParam := do
  match ← node atom with
  | ("TPSimple", [name, type]) => pure (.simple (← token name) (← typeExpr type))
  | ("TPBinder", [binder, name, type]) => pure (.abstractionNamed (some (← token binder)) (← token name) (← typeExpr type))
  | (label, _) => throw s!"unexpected parameter {label}"

def syntaxItem (atom : Atom) : Decode SyntaxItem := do
  match ← node atom with
  | ("SITerminal", [lexeme]) => pure (.terminal (← token lexeme))
  | ("SIVariable", [name]) => pure (.nonTerminal (← token name))
  | ("SISep", [name, separator]) => pure (.op (.sep (← token name) (← token separator) none))
  | (label, _) => throw s!"unexpected syntax item {label}"

def termDecl (atom : Atom) : Decode GrammarRule := do
  match ← node atom with
  | ("TDecl", [label, params, items, category]) =>
      pure { label := ← token label, category := ← token category,
             params := ← (← list params).mapM termParam, syntaxPattern := ← (← list items).mapM syntaxItem }
  | (label, _) => throw s!"unexpected constructor {label}"

/-- A pattern under binders, innermost first. -/
partial def pattern (binders : List String) (atom : Atom) : Decode Pattern := do
  match ← node atom with
  | ("PVar", [name]) =>
      let name ← token name
      pure (match binders.idxOf? name with
        | some index => .bvar index
        | none => .fvar name)
  | ("PApp", [label, arguments]) =>
      let arguments ← (← list arguments).mapM fun argument => do
        match ← node argument with
        | ("AArg", [inner]) => pattern binders inner
        | (label, _) => throw s!"unexpected argument {label}"
      -- `(One)` is the name `One`, resolved against the nullary constructors where the theory is
      -- elaborated, as `languageDef!` reads it.
      let label ← token label
      pure (if arguments.isEmpty then .fvar label else .apply label arguments)
  | ("PSubst", [body, argument]) => pure (.apply Pattern.evalHead [← pattern binders body, ← pattern binders argument])
  | ("PBag", [elements]) => pure (.collection .hashBag (← elementsOf binders elements) none)
  | ("PBagRest", [elements, rest]) => pure (.collection .hashBag (← elementsOf binders elements) (some (← token rest)))
  | ("PRestOnly", [rest]) => pure (.collection .hashBag [] (some (← token rest)))
  | ("PEmpty", []) => pure (.collection .hashBag [] none)
  | ("PBinder", [binder, body]) =>
      let name ← token binder
      pure (.lambda (some name) (← pattern (name :: binders) body))
  | (label, _) => throw s!"unexpected pattern {label}"
where
  elementsOf (binders : List String) (atom : Atom) : Decode (List Pattern) := do
    (← list atom).mapM fun element => do
      match ← node element with
      | ("EElem", [inner]) => pattern binders inner
      | (label, _) => throw s!"unexpected element {label}"

def premise (atom : Atom) : Decode Premise := do
  match ← node atom with
  | ("PrFresh", [name, term]) => pure (.freshness ⟨← token name, ← pattern [] term⟩)
  | ("PrStep", [source, target]) => pure (.congruence (← pattern [] source) (← pattern [] target))
  | (label, _) => throw s!"unexpected premise {label}"

/-! ## Theories -/

/-- Equations are numbered within their theory. -/
abbrev Numbered := StateT (String × Nat) Decode

def nextEquation : Numbered String := do
  let (owner, count) ← get
  set (owner, count + 1)
  pure s!"{owner}:equation:{count}"

def equationRow (atom : Atom) : Numbered Equation := do
  match ← node atom with
  | ("EqPlain", [left, right]) =>
      pure { name := ← nextEquation, typeContext := [], premises := [],
             left := ← pattern [] left, right := ← pattern [] right }
  | ("EqIf", [premises, left, right]) =>
      let premises ← ((← list premises).mapM premise : Decode _)
      pure { name := ← nextEquation, typeContext := [], premises,
             left := ← pattern [] left, right := ← pattern [] right }
  | (label, _) => throw s!"unexpected equation {label}"

def rewriteRow (atom : Atom) : Decode RewriteRule := do
  match ← node atom with
  | ("RwPlain", [label, left, right]) =>
      pure { name := ← token label, typeContext := [], premises := [],
             left := ← pattern [] left, right := ← pattern [] right }
  | ("RwIf", [label, premises, left, right]) =>
      pure { name := ← token label, typeContext := [], premises := ← (← list premises).mapM premise,
             left := ← pattern [] left, right := ← pattern [] right }
  | (label, _) => throw s!"unexpected rewrite {label}"

def block (atom : Atom) : Numbered Block := do
  match ← node atom with
  | ("BTypes", [rows]) =>
      pure (.types (← (← list rows).mapM fun row => do
        match ← node row with
        | ("SRow", [name]) => token name
        | (label, _) => throw s!"unexpected sort {label}"))
  | ("BExports", [rows]) =>
      pure (.exports (← (← list rows).mapM fun row => do
        match ← node row with
        | ("ERow", [name]) => pure ⟨← token name, none⟩
        | ("ERename", [name, target]) => pure ⟨← token name, some (← token target)⟩
        | (label, _) => throw s!"unexpected export {label}"))
  | ("BTerms", [rows]) => pure (.terms (← ((← list rows).mapM termDecl : Decode _)))
  | ("BReplacements", [rows]) =>
      pure (.replacements (← (← list rows).mapM fun row => do
        match ← node row with
        | ("RRow", [old, rule]) => pure ⟨← token old, ← termDecl rule⟩
        | (label, _) => throw s!"unexpected replacement {label}"))
  | ("BEquations", [rows]) => pure (.equations (← (← list rows).mapM equationRow))
  | ("BRewrites", [rows]) => pure (.rewrites (← ((← list rows).mapM rewriteRow : Decode _)))
  | (label, _) => throw s!"unexpected block {label}"

partial def expr (atom : Atom) : Numbered Expr := do
  match ← node atom with
  | ("MRef", [name]) => pure (.ref (← token name))
  | ("MApply", [target, args]) => pure (.apply (← path target) (← (← list args).mapM expr))
  | ("MJoin", [left, right]) => pure (.join (← expr left) (← expr right))
  | ("MLet", [name, value, body]) => pure (.letIn (← token name) (← expr value) (← expr body))
  | ("MExtend", [base, first, rest]) =>
      pure (.extend (some (← expr base)) ((← block first) :: (← (← list rest).mapM block)))
  | ("MBlocks", [first, rest]) => pure (.extend none ((← block first) :: (← (← list rest).mapM block)))
  | (label, _) => throw s!"unexpected expression {label}"

def theory (atom : Atom) : Decode Theory := do
  match ← node atom with
  | ("MTheory", [name, params, body]) =>
      let name ← token name
      let params ← (← list params).mapM fun param => do
        match ← node param with
        | ("MParam", [paramName, target]) => pure ⟨← token paramName, ← path target⟩
        | (label, _) => throw s!"unexpected parameter {label}"
      let (body, _) ← (expr body).run (name, 0)
      pure { name, params, body }
  | (label, _) => throw s!"unexpected theory {label}"

/-- **A parsed `.module` file as module data.** -/
def decode (atom : Atom) : Decode Module := do
  match ← node atom with
  | ("MFile", [imports, name, theories, entry]) =>
      let imports ← (← list imports).mapM fun item => do
        match ← node item with
        | ("MImport", [file, qualifier]) => pure ⟨← token file, ← token qualifier⟩
        | (label, _) => throw s!"unexpected import {label}"
      let entry ← match ← node entry with
        | ("MEntry", [target, args]) => do
            let (args, _) ← ((← list args).mapM expr).run ("entry", 0)
            pure (some (← path target, args))
        | ("MNoEntry", []) => pure none
        | (label, _) => throw s!"unexpected entry {label}"
      pure { imports, name := ← token name, theories := ← (← list theories).mapM theory, entry }
  | (label, _) => throw s!"unexpected module file {label}"

/-- The trees of a `(LangDef:AuthoredParseAccepted …)` result. -/
def acceptedTrees : Atom → Decode (List Atom)
  | .expression (.symbol "LangDef:AuthoredParseAccepted" :: rest) =>
      match rest.getLast? with
      | some (.expression trees) => pure trees
      | _ => throw "no trees in the accepted parse"
  | other => throw s!"not an accepted parse: {repr other}"

end Mettapedia.GSLT.LanguageDef.ModuleSource.LbnfDecode
