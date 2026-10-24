import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# ExportGF — Grammatical Framework grammars from a language definition

A `LanguageDef` fuses two things in each constructor: its abstract signature
(label, parameter sorts, binders, result sort) and one concrete syntax (the
authored `syntaxPattern`). Grammatical Framework (GF) keeps them apart: an
abstract syntax of categories and functions, and any number of concrete
syntaxes that linearize its trees. This module separates a `LanguageDef` the
GF way.

* `abstractOf` gives the GF abstract syntax. A sort is a category. A
  collection parameter `HashBag(S)`, `HashSet(S)` or `Vec(S)` is a list
  category with a nil and a cons function, so a tree presents one ordering of
  the collection; the quotient by order and multiplicity stays on the
  `LanguageDef` side. A binder parameter `^x.p:[D -> C]` is a higher-order
  argument `D -> C`. A binder over several variables, `[D₁ -> … -> Dₖ -> C]`,
  is a chain of one-variable abstractions through auxiliary categories, so
  every GF abstraction binds exactly one variable. (GF 3.12 numbers the
  variable fields `$0`, `$1` of a two-variable abstraction in opposite orders
  when it linearizes and when it parses, so such an abstraction does not read
  back; one-variable abstractions do.)
* `notationOf` gives the concrete syntax that the `syntaxPattern`s already
  state, written as a GF concrete syntax over that abstract syntax. The
  authored binder name is the variable field `$0` of the abstraction. Every
  argument is used in its linearization, even where it contributes no tokens
  (the empty tail of a list): GF parses an argument that a linearization
  never uses into a metavariable, so an unused argument would not read back.
* `treeOf` writes a closed, well-sorted `Pattern` as a GF tree of that abstract
  syntax.

A binder that names every variable of a curried type, `^[X, d].p:[A -> B -> C]`,
is the same chain with every name displayed: the first is `$0` of the argument,
the others are fields `x1`, `x2`, … carried up the chain. An optional segment
`*opt(…)` is a GF `variants`: parsing accepts the text with or without it, and
linearization prints the first variant, the full segment, so a printed term
always reads back. (GF linearization cannot ask whether a bound variable occurs
in a body, so the policy "print the name exactly when it is used" belongs to a
printer of our own, not to the generated grammar.) The chain reading of
`^[X, d]` is the GF backend's: it reads `treeOf`'s nested abstractions in
declaration order.

Constructions with no GF counterpart are refused with a reason rather than
approximated: a variadic binder `^[xs].p:[S* -> T]`, a `^[…]` binder naming
fewer variables than its type binds, a function-typed parameter without a
binder, collection-typed binder bodies, and the syntax operators other than
`*sep` and `*opt`. Free variables (metavariables), explicit substitutions and
simultaneous abstractions (`multiLambda`) are not closed constructor terms of
this encoding and are refused by `treeOf`.

Nothing here asserts that GF's own parser or linearizer is correct. The
generated grammars are inputs for GF, which checks them independently.

It sits beside the Rust exporter:

```
GF (.gf)  ←renderGFAbstract─  Lean (LanguageDef)  ─renderLanguage→  Rust (language!)
    │                              ↑                                    ↑
    └─── GFCore.check ────────────┘                                    │
                                    └──── languageDef! macro ──────────┘
```

`renderGFAbstract` is the exporter entry point: the abstract syntax, followed by
the names of the equations and rewrites as comments.

## References

- GF Reference Manual: http://www.grammaticalframework.org/doc/gf-refman.html
-/

namespace Mettapedia.OSLF.MeTTaIL.ExportGF

open Mettapedia.OSLF.MeTTaIL.Syntax

/-! ## Names -/

/-- Words that GF reserves; a parameter name among them is renamed in `lin`
rows. -/
def reservedWords : List String :=
  ["abstract", "case", "cat", "concrete", "data", "def", "flags", "fn", "fun",
   "in", "incomplete", "instance", "interface", "let", "lin", "lincat",
   "lindef", "linref", "of", "open", "oper", "param", "pre", "printname",
   "resource", "strs", "table", "transfer", "variants", "where", "with"]

/-- A GF identifier: a letter followed by letters, digits, `_` or `'`. -/
def isIdentifier (name : String) : Bool :=
  match name.toList with
  | [] => false
  | first :: rest =>
      first.isAlpha && rest.all fun c => c.isAlphanum || c == '_' || c == '\''

/-- The variable that stands for a parameter in a `lin` row. -/
def linVariable (name : String) : String :=
  if reservedWords.contains name then name ++ "_" else name

/-- The list category presenting a collection of a sort. -/
def collectionCategory : CollType → String → String
  | .hashBag, sort => "Bag_" ++ sort
  | .hashSet, sort => "Set_" ++ sort
  | .vec, sort => "Vec_" ++ sort

/-- A GF string literal. -/
def gfString (text : String) : String :=
  "\"" ++ String.join (text.toList.map fun c =>
    if c == '"' then "\\\"" else if c == '\\' then "\\\\" else c.toString) ++ "\""

/-! ## Abstract syntax -/

/-- An argument of a GF function: a category, or an abstraction binding one
variable of the domain category in a body of the codomain category. -/
inductive GFArgument where
  | category (name : String)
  | abstraction (domain codomain : String)
  deriving DecidableEq, Repr

/-- Where a generated function comes from. -/
inductive GFOrigin where
  | constructor
  | collectionNil
  | collectionCons
  | binderStep
  deriving DecidableEq, Repr

/-- A function of the generated abstract syntax. -/
structure GFFunction where
  name : String
  arguments : List GFArgument
  result : String
  origin : GFOrigin
  deriving DecidableEq, Repr

/-- A generated abstract syntax. -/
structure GFAbstract where
  name : String
  categories : List String
  functions : List GFFunction
  deriving Repr

/-- Whether a type mentions a variadic binder domain `S*`. -/
def mentionsMultiBinder : TypeExpr → Bool
  | .base _ => false
  | .arrow domain codomain => mentionsMultiBinder domain || mentionsMultiBinder codomain
  | .multiBinder _ => true
  | .collection _ element => mentionsMultiBinder element

/-- The domains and codomain of a binder type `D₁ -> … -> Dₖ -> C` over base
sorts. -/
def binderShape : TypeExpr → Except String (List String × String)
  | .base codomain => pure ([], codomain)
  | .arrow (.base domain) rest => do
      let (domains, codomain) ← binderShape rest
      pure (domain :: domains, codomain)
  | other => throw s!"binder type {repr other} is not a chain of base sorts"

/-- The auxiliary category after the `i`-th variable of a binder parameter. -/
def stepCategory (label body : String) (index : Nat) : String :=
  s!"{label}_{body}_{index}"

/-- The function building the auxiliary category `stepCategory label body i`. -/
def stepFunction (label body : String) (index : Nat) : String :=
  stepCategory label body index ++ "_mk"

/-- The binder chain: the argument for the first variable and the functions
binding the others. -/
def binderChain (label body : String) (domains : List String) (codomain : String) :
    Except String (GFArgument × List GFFunction) := do
  match domains with
  | [] => throw s!"{label}: binder parameter {body} binds no variable"
  | [domain] => pure (.abstraction domain codomain, [])
  | first :: rest =>
      let count := rest.length
      let target (i : Nat) := if i = count then codomain else stepCategory label body i
      let steps := (List.range count).map fun i =>
        { name := stepFunction label body (i + 1)
          arguments := [.abstraction (rest.getD i "") (target (i + 1))]
          result := stepCategory label body (i + 1)
          origin := .binderStep : GFFunction }
      pure (.abstraction first (stepCategory label body 1), steps)

/-- The GF argument of one constructor parameter, with the auxiliary functions
it needs. -/
def argumentOf (label : String) : TermParam → Except String (GFArgument × List GFFunction)
  | .simple _ (.base sort) => pure (.category sort, [])
  | .simple _ (.collection kind (.base sort)) =>
      pure (.category (collectionCategory kind sort), [])
  | .simple name (.arrow _ _) =>
      throw s!"{label}: parameter {name} has a function type without a binder"
  | .simple name other =>
      throw s!"{label}: parameter {name} has type {repr other}, which has no GF category"
  | .abstractionNamed _ body type => do
      let (domains, codomain) ← binderShape type
      binderChain label body domains codomain
  | .multiAbstractionNamed names body type =>
      if mentionsMultiBinder type then
        throw s!"{label}: the variadic binder of {body} has no GF counterpart"
      else do
        let (domains, codomain) ← binderShape type
        unless names.length = domains.length do
          throw s!"{label}: binder {body} names {names.length} of its {domains.length} variables"
        binderChain label body domains codomain

/-- The collection categories `(kind, sort)` that a constructor's parameters
use. -/
def collectionsOf (rule : GrammarRule) : List (CollType × String) :=
  rule.params.filterMap fun
    | .simple _ (.collection kind (.base sort)) => some (kind, sort)
    | _ => none

/-- Remove repeated entries, keeping first occurrences. -/
def dedup {α : Type} [BEq α] (items : List α) : List α :=
  items.foldl (fun seen item => if seen.contains item then seen else seen ++ [item]) []

/-- The GF abstract syntax of a language definition. -/
def abstractOf (language : LanguageDef) : Except String GFAbstract := do
  unless isIdentifier language.name do
    throw s!"language name {language.name} is not a GF identifier"
  for type in language.types do
    unless isIdentifier type.name do
      throw s!"sort {type.name} is not a GF identifier"
  let mut functions : List GFFunction := []
  let mut steps : List GFFunction := []
  for rule in language.terms do
    unless isIdentifier rule.label do
      throw s!"label {rule.label} is not a GF identifier"
    let mut arguments : List GFArgument := []
    for param in rule.params do
      let (argument, chain) ← argumentOf rule.label param
      arguments := arguments ++ [argument]
      steps := steps ++ chain
    functions := functions ++
      [{ name := rule.label, arguments, result := rule.category, origin := .constructor }]
  let collections := dedup (language.terms.flatMap collectionsOf)
  let collectionFunctions := collections.flatMap fun (kind, sort) =>
    let category := collectionCategory kind sort
    [{ name := category ++ "_nil", arguments := [], result := category
       origin := .collectionNil : GFFunction },
     { name := category ++ "_cons"
       arguments := [.category sort, .category category]
       result := category, origin := .collectionCons }]
  let categories := language.types.map (·.name) ++
    collections.map (fun (kind, sort) => collectionCategory kind sort) ++
    steps.map (·.result)
  let all := functions ++ collectionFunctions ++ steps
  let names := all.map (·.name)
  if (dedup names).length != names.length then
    throw "two generated functions share a name"
  if (dedup categories).length != categories.length then
    throw "two generated categories share a name"
  pure { name := language.name, categories, functions := all }

/-- The text of an argument type. -/
def GFArgument.render : GFArgument → String
  | .category name => name
  | .abstraction domain codomain => s!"({domain} -> {codomain})"

/-- The text of a function declaration. -/
def GFFunction.render (function : GFFunction) : String :=
  let parts := function.arguments.map GFArgument.render ++ [function.result]
  s!"  fun {function.name} : {" -> ".intercalate parts} ;"

/-- The text of the abstract syntax module, one declaration per line. -/
def GFAbstract.render (grammar : GFAbstract) : String :=
  let start := grammar.categories.headD "S"
  String.intercalate "\n"
    ([s!"abstract {grammar.name} = \{", s!"  flags startcat = {start} ;"] ++
      grammar.categories.map (fun category => s!"  cat {category} ;") ++
      grammar.functions.map GFFunction.render ++ ["}", ""])

/-! ## The authored notation as a concrete syntax -/

/-- The separators a list category is printed with, in order of first use. -/
def separatorsOf (language : LanguageDef) (category : String) : List String :=
  dedup <| language.terms.flatMap fun rule =>
    rule.syntaxPattern.filterMap fun
      | .op (.sep name separator none) =>
          match rule.params.find? (fun
              | .simple other _ => other == name
              | _ => false) with
          | some (.simple _ (.collection kind (.base sort))) =>
              if collectionCategory kind sort = category then some separator else none
          | _ => none
      | _ => none

/-- The parameter value naming the `index`-th separator of a list category. -/
def separatorValue (category : String) (index : Nat) : String :=
  s!"Sep_{category}_{index}"

/-- The parameter type of a list category's separators. -/
def separatorType (category : String) : String := "Sep_" ++ category

/-- The binder parameters of a constructor with their number of variables. -/
def binderArities (rule : GrammarRule) : List (String × Nat) :=
  rule.params.filterMap fun
    | .abstractionNamed _ body type =>
        (binderShape type).toOption.map fun (domains, _) => (body, domains.length)
    | .multiAbstractionNamed _ body type =>
        if mentionsMultiBinder type then none
        else (binderShape type).toOption.map fun (domains, _) => (body, domains.length)
    | .simple _ _ => none

/-- Each auxiliary step category of a binder chain, with the indices of the
variables whose names it carries: step `i` of a `k`-variable binder carries
variables `i` to `k - 1`. -/
def stepFieldsOf (language : LanguageDef) : List (String × List Nat) :=
  language.terms.flatMap fun rule =>
    (binderArities rule).flatMap fun (body, count) =>
      (List.range (count - 1)).map fun i =>
        (stepCategory rule.label body (i + 1), (List.range (count - 1 - i)).map (· + i + 1))

/-- The field holding the name of variable `j` of a binder chain. -/
def variableField (index : Nat) : String := s!"x{index}"

/-- The tokens of a terminal: GF tokens contain no blanks. -/
def terminalTokens (text : String) : List String :=
  (text.splitOn " ").filter (· ≠ "")

/-- The linearization of one syntax item of a constructor. -/
partial def itemText (language : LanguageDef) (rule : GrammarRule) :
    SyntaxItem → Except String (List String)
  | .terminal text => pure ((terminalTokens text).map gfString)
  | .nonTerminal name =>
      let found := rule.params.filterMap fun
        | .simple other _ => if other = name then some s!"{linVariable other}.s" else none
        | .abstractionNamed binder body _ =>
            if body = name then some s!"{linVariable body}.s"
            else if binder = some name then some s!"{linVariable body}.$0"
            else none
        | .multiAbstractionNamed names body type =>
            if body = name then some s!"{linVariable body}.s"
            else if mentionsMultiBinder type then none
            else match names.idxOf? name with
              | some 0 => some s!"{linVariable body}.$0"
              | some index => some s!"{linVariable body}.{variableField index}"
              | none => none
      match found with
      | [one] => pure [one]
      | [] => throw s!"{rule.label}: syntax item {name} names no parameter or binder"
      | _ => throw s!"{rule.label}: syntax item {name} is ambiguous"
  | .op (.sep name separator none) =>
      match rule.params.find? (fun
          | .simple other _ => other = name
          | _ => false) with
      | some (.simple _ (.collection kind (.base sort))) =>
          let category := collectionCategory kind sort
          match (separatorsOf language category).idxOf? separator with
          | some index => pure [s!"{linVariable name}.s ! {separatorValue category index}"]
          | none => throw s!"{rule.label}: separator {separator} is not recorded"
      | _ => throw s!"{rule.label}: {name}.*sep is not over a collection parameter"
  | .op (.opt inner) => do
      let mut tokens : List String := []
      for item in inner do
        tokens := tokens ++ (← itemText language rule item)
      let present := if tokens.isEmpty then "[]" else " ++ ".intercalate tokens
      pure [s!"variants \{{present} ; []}"]
  | .op _ => throw s!"{rule.label}: syntax operators other than *sep and *opt have no generated GF form"
  | .separator _ => throw s!"{rule.label}: bare separator items have no generated GF form"
  | .delimiter _ _ => throw s!"{rule.label}: delimiter items have no generated GF form"

/-- The `lin` variable of a constructor parameter. -/
def paramVariable : TermParam → String
  | .simple name _ => linVariable name
  | .abstractionNamed _ body _ => linVariable body
  | .multiAbstractionNamed _ body _ => linVariable body

/-- The `lin` row of a constructor. -/
def linRow (language : LanguageDef) (rule : GrammarRule) : Except String String := do
  let mut tokens : List String := []
  for item in rule.syntaxPattern do
    tokens := tokens ++ (← itemText language rule item)
  let body := if tokens.isEmpty then "[]" else " ++ ".intercalate tokens
  let parameterVariables := rule.params.map paramVariable
  let head := " ".intercalate (rule.label :: parameterVariables)
  pure s!"    {head} = \{s = {body}} ;"

/-- The concrete syntax module stating the authored notation. -/
def notationOf (language : LanguageDef) (concreteName : String) : Except String String := do
  let grammar ← abstractOf language
  let lists := grammar.functions.filterMap fun function =>
    if function.origin = .collectionNil then some function.result else none
  let mut lines : List String :=
    [s!"concrete {concreteName} of {grammar.name} = \{",
     "  param Emp = E | NE ;"]
  for category in lists do
    let separators := separatorsOf language category
    let values := (List.range (max separators.length 1)).map (separatorValue category)
    lines := lines ++ [s!"  param {separatorType category} = {" | ".intercalate values} ;"]
    let cases := (List.range separators.length).map fun i =>
      s!"{separatorValue category i} => {gfString (separators.getD i "")}"
    let caseText := if cases.isEmpty then s!"_ => []" else " ; ".intercalate cases
    lines := lines ++
      [s!"  oper sep_{category} : {separatorType category} -> Str = \\sp -> case sp of \{{caseText}} ;"]
  let steps := stepFieldsOf language
  let plain := grammar.categories.filter (fun category =>
    !lists.contains category && !(steps.map Prod.fst).contains category)
  unless plain.isEmpty do
    lines := lines ++ [s!"  lincat {", ".intercalate plain} = \{s : Str} ;"]
  for (category, fields) in steps do
    let declared := fields.map fun j => s!" ; {variableField j} : Str"
    lines := lines ++ [s!"  lincat {category} = \{s : Str{String.join declared}} ;"]
  for category in lists do
    lines := lines ++
      [s!"  lincat {category} = \{s : {separatorType category} => Str ; e : Emp} ;"]
  lines := lines ++ ["  lin"]
  for rule in language.terms do
    lines := lines ++ [← linRow language rule]
  for function in grammar.functions do
    match function.origin with
    | .collectionNil =>
        lines := lines ++ [s!"    {function.name} = \{s = \\\\_ => [] ; e = E} ;"]
    | .collectionCons =>
        let category := function.result
        lines := lines ++
          [s!"    {function.name} x xs = \{s = \\\\sp => x.s ++ case xs.e of \{E => xs.s ! sp ; NE => sep_{category} sp ++ xs.s ! sp} ; e = NE} ;"]
    | .binderStep =>
        let fields := ((steps.find? (·.1 = function.result)).map (·.2)).getD []
        let assigned := fields.zipIdx.map fun (j, position) =>
          if position = 0 then s!" ; {variableField j} = b.$0"
          else s!" ; {variableField j} = b.{variableField j}"
        lines := lines ++ [s!"    {function.name} b = \{s = b.s{String.join assigned}} ;"]
    | .constructor => pure ()
  pure ("\n".intercalate (lines ++ ["}", ""]))

/-! ## Trees -/

/-- The name of a bound variable: its authored name when that is free of
clashes, otherwise a numbered one. -/
def variableName (display : Option String) (scope : List String) (labels : List String) :
    String :=
  let base := match display with
    | some name => if isIdentifier name && !reservedWords.contains name then name else "v"
    | none => "v"
  if scope.contains base || labels.contains base then s!"{base}{scope.length}" else base

/-- The GF tree of a closed pattern at an expected type, under the names of
the enclosing binders (innermost first). -/
partial def treeOf (language : LanguageDef) (scope : List String) :
    TypeExpr → Pattern → Except String String
  | _, .bvar index =>
      match scope[index]? with
      | some name => pure name
      | none => throw s!"loose bound variable {index}"
  | _, .fvar name => throw s!"free variable {name} is not a closed constructor term"
  | _, .subst _ _ => throw "an explicit substitution is not a constructor term"
  | _, .lambda _ _ => throw "an abstraction outside a binder parameter"
  | _, .multiLambda _ _ _ => throw "a variadic abstraction has no GF counterpart"
  | .collection kind (.base sort), .collection kind' elements none => do
      unless kind = kind' do throw "collection kind does not match its parameter"
      let category := collectionCategory kind sort
      let mut text := category ++ "_nil"
      for element in elements.reverse do
        text := s!"({category}_cons {← treeOf language scope (.base sort) element} {text})"
      pure text
  | _, .collection _ _ (some rest) => throw s!"collection rest {rest} is not a closed term"
  | expected, .apply label arguments => do
      let some rule := language.terms.find? (·.label = label)
        | throw s!"unknown constructor {label}"
      unless expected = .base rule.category do
        throw s!"{label} builds {rule.category}, not {repr expected}"
      unless rule.params.length = arguments.length do
        throw s!"{label} takes {rule.params.length} arguments"
      let labels := language.terms.map (·.label)
      let mut parts : List String := [label]
      for (param, argument) in rule.params.zip arguments do
        match param with
        | .simple _ type => parts := parts ++ [← treeOf language scope type argument]
        | .abstractionNamed display body type =>
            let (domains, codomain) ← binderShape type
            parts := parts ++
              [← binderTree language scope labels label body [display] domains codomain 0 argument]
        | .multiAbstractionNamed names body type =>
            if mentionsMultiBinder type then throw s!"{label}: variadic binder"
            let (domains, codomain) ← binderShape type
            parts := parts ++
              [← binderTree language scope labels label body (names.map some) domains codomain 0
                argument]
      pure (if parts.length = 1 then label else "(" ++ " ".intercalate parts ++ ")")
  | expected, other => throw s!"pattern {repr other} does not fit {repr expected}"
where
  /-- The abstraction chain of a binder parameter, read as nested one-variable
  abstractions; `displays` are the authored names of its variables, in order. -/
  binderTree (language : LanguageDef) (scope labels : List String) (label body : String)
      (displays : List (Option String)) (domains : List String) (codomain : String)
      (index : Nat) : Pattern → Except String String
    | .lambda name inner => do
        let shown := name.orElse fun _ => (displays[index]?).getD none
        let bound := variableName shown scope labels
        match domains with
        | [] => throw s!"{label}: more abstractions than binder variables"
        | [_] => pure s!"(\\{bound} -> {← treeOf language (bound :: scope) (.base codomain) inner})"
        | _ :: rest =>
            let step := stepFunction label body (index + 1)
            let innerTree ← binderTree language (bound :: scope) labels label body displays
              rest codomain (index + 1) inner
            pure s!"(\\{bound} -> ({step} {innerTree}))"
    | _ => throw s!"{label}: binder parameter {body} needs an abstraction"


/-! ## The exporter entry point -/

/-- Render a full LanguageDef as a GF abstract syntax module, followed by the
names of its equations and rewrites as comments (GF abstract syntax has no
equations or rewrites). -/
def renderGFAbstract (lang : LanguageDef) : Except String String := do
  let grammar ← abstractOf lang
  let header := s!"-- Generated from LanguageDef \"{lang.name}\"\n" ++
    s!"-- Types: {lang.types.length}, Terms: {lang.terms.length}\n" ++
    s!"-- Equations: {lang.equations.length}, Rewrites: {lang.rewrites.length}\n\n"
  let eqComments := lang.equations.map fun eq => s!"-- equation: {eq.name}"
  let rwComments := lang.rewrites.map fun rw => s!"-- rewrite: {rw.name}"
  pure <| header ++ grammar.render ++
    (if eqComments.isEmpty then "" else
      "-- Semantic equations (OSLF extension, not native GF)\n" ++
      String.intercalate "\n" eqComments ++ "\n") ++
    (if rwComments.isEmpty then "" else
      "-- Semantic rewrites (OSLF extension, not native GF)\n" ++
      String.intercalate "\n" rwComments ++ "\n")


/-! ## Controls -/

namespace Controls

/-- A small language: names, a lambda over names, a bag of processes, and a
receive binding a process and a name. -/
def sample : LanguageDef :=
  { name := "Sample"
    types := [{ name := "Proc" }, { name := "Name" }]
    terms :=
      [ { label := "Zero", category := "Proc", params := [], syntaxPattern := [.terminal "0"] },
        { label := "Par", category := "Proc",
          params := [.simple "ps" (.collection .hashBag (.base "Proc"))],
          syntaxPattern := [.terminal "{", .op (.sep "ps" "|" none), .terminal "}"] },
        { label := "Quote", category := "Name", params := [.simple "p" (.base "Proc")],
          syntaxPattern := [.terminal "@", .terminal "(", .nonTerminal "p", .terminal ")"] },
        { label := "New", category := "Proc",
          params := [.abstractionNamed (some "x") "p" (.arrow (.base "Name") (.base "Proc"))],
          syntaxPattern := [.terminal "new", .nonTerminal "x", .terminal "in", .nonTerminal "p"] },
        { label := "Recv", category := "Proc",
          params := [.simple "n" (.base "Name"),
            .abstractionNamed (some "X") "p"
              (.arrow (.base "Proc") (.arrow (.base "Name") (.base "Proc")))],
          syntaxPattern := [.terminal "for", .terminal "(", .nonTerminal "X", .terminal "<-",
            .nonTerminal "n", .terminal ")", .terminal "{", .nonTerminal "p", .terminal "}"] },
        { label := "Drop", category := "Proc", params := [.simple "n" (.base "Name")],
          syntaxPattern := [.terminal "*", .nonTerminal "n"] } ]
    equations := []
    rewrites := [] }

/-- The functions of a generated abstract syntax, rendered. -/
def functions (language : LanguageDef) : List String :=
  match abstractOf language with
  | .ok grammar => grammar.functions.map GFFunction.render
  | .error _ => []

/-! Positive: one category per sort, the bag's list category, and one auxiliary
category for the receive's second variable. -/
#guard (abstractOf sample).toOption.map (·.categories) ==
  some ["Proc", "Name", "Bag_Proc", "Recv_p_1"]

/-! Positive: each constructor is one function with its arguments in parameter
order; a one-variable binder is one abstraction, a two-variable binder is a
chain. -/
#guard functions sample ==
  ["  fun Zero : Proc ;", "  fun Par : Bag_Proc -> Proc ;", "  fun Quote : Proc -> Name ;",
   "  fun New : (Name -> Proc) -> Proc ;", "  fun Recv : Name -> (Proc -> Recv_p_1) -> Proc ;",
   "  fun Drop : Name -> Proc ;",
   "  fun Bag_Proc_nil : Bag_Proc ;", "  fun Bag_Proc_cons : Proc -> Bag_Proc -> Bag_Proc ;",
   "  fun Recv_p_1_mk : (Name -> Proc) -> Recv_p_1 ;"]

/-- A constructor of the sample language, by label. -/
def rule (label : String) : Option GrammarRule :=
  sample.terms.find? (·.label = label)

/-! Positive: the authored binder name is the abstraction's variable field. -/
#guard ((rule "New").map fun r => (linRow sample r).toOption) ==
  some (some "    New p = {s = \"new\" ++ p.$0 ++ \"in\" ++ p.s} ;")
#guard ((rule "Par").map fun r => (linRow sample r).toOption) ==
  some (some "    Par ps = {s = \"{\" ++ ps.s ! Sep_Bag_Proc_0 ++ \"}\"} ;")

/-- A closed term with a bag and both binders. -/
def sampleTerm : Pattern :=
  .apply "Par" [.collection .hashBag
    [.apply "New" [.lambda (some "x") (.apply "Drop" [.bvar 0])],
     .apply "Recv" [.apply "Quote" [.apply "Zero" []],
       .lambda none (.lambda none (.apply "Drop" [.bvar 0]))]] none]

/-! Positive: the closed term as a GF tree; the receive's unnamed second
variable gets a fresh name. -/
#guard (treeOf sample [] (.base "Proc") sampleTerm).toOption ==
  some ("(Par (Bag_Proc_cons (New (\\x -> (Drop x))) (Bag_Proc_cons (Recv (Quote Zero) " ++
    "(\\X -> (Recv_p_1_mk (\\v -> (Drop v))))) Bag_Proc_nil)))")

/-- A variadic binder, `^[xs].p:[Name* -> Proc]`. -/
def variadic : LanguageDef :=
  { sample with
    terms := [
      { label := "NewMany", category := "Proc",
        params := [.multiAbstractionNamed ["xs"] "p" (.arrow (.multiBinder (.base "Name")) (.base "Proc"))],
        syntaxPattern := [.terminal "new", .nonTerminal "p"] }] }

/-- A binder naming both of its variables, with the second name optional in
the text. -/
def bothNamed : GrammarRule :=
  { label := "Recv2", category := "Proc",
    params := [.simple "n" (.base "Name"),
      .multiAbstractionNamed ["X", "d"] "p"
        (.arrow (.base "Proc") (.arrow (.base "Name") (.base "Proc")))],
    syntaxPattern := [.terminal "for", .terminal "(", .nonTerminal "X",
      .op (.opt [.terminal ",", .nonTerminal "d"]), .terminal "<-", .nonTerminal "n",
      .terminal ")", .terminal "{", .nonTerminal "p", .terminal "}"] }

/-- The sample language with that binder. -/
def sampleBothNamed : LanguageDef :=
  { sample with terms := sample.terms ++ [bothNamed] }

/-- A binder naming one of its two variables in the `^[...]` form. -/
def underNamed : LanguageDef :=
  { sample with
    terms := [
      { label := "Half", category := "Proc",
        params := [.multiAbstractionNamed ["x"] "p"
          (.arrow (.base "Name") (.arrow (.base "Name") (.base "Proc")))],
        syntaxPattern := [.terminal "half", .nonTerminal "p"] }] }

/-- A function-typed parameter without a binder. -/
def functionParameter : LanguageDef :=
  { sample with
    terms := [
      { label := "Bee", category := "Proc",
        params := [.simple "f" (.arrow (.base "Name") (.base "Proc"))],
        syntaxPattern := [.terminal "bee", .nonTerminal "f"] }] }

/-- A syntax item naming nothing. -/
def danglingItem : GrammarRule :=
  { label := "Bad", category := "Proc", params := [],
    syntaxPattern := [.nonTerminal "q"] }

/-! Negative: a variadic binder is refused, not approximated. -/
#guard (abstractOf variadic).toOption.isNone

/-! Positive: a binder naming both variables is a chain; the second name is
the step's field, and the optional segment is a parse-time alternative whose
first variant, the named form, is what linearization prints. -/
#guard (linRow sampleBothNamed bothNamed).toOption ==
  some ("    Recv2 n p = {s = \"for\" ++ \"(\" ++ p.$0 ++ variants {\",\" ++ p.x1 ; []} ++ " ++
    "\"<-\" ++ n.s ++ \")\" ++ \"{\" ++ p.s ++ \"}\"} ;")
#guard (treeOf sampleBothNamed [] (.base "Proc")
    (.apply "Recv2" [.apply "Quote" [.apply "Zero" []],
      .lambda none (.lambda none (.apply "Drop" [.bvar 0]))])).toOption ==
  some "(Recv2 (Quote Zero) (\\X -> (Recv2_p_1_mk (\\d -> (Drop d)))))"

/-! Negative: a `^[...]` binder that names fewer variables than it binds is refused. -/
#guard (abstractOf underNamed).toOption.isNone

/-! Negative: a function-typed parameter without a binder is refused. -/
#guard (abstractOf functionParameter).toOption.isNone

/-! Negative: a syntax item naming nothing is refused. -/
#guard (linRow sample danglingItem).toOption.isNone

/-! Negative: free variables, explicit substitutions and ill-sorted arguments
are not trees. -/
#guard (treeOf sample [] (.base "Proc") (.fvar "P")).toOption.isNone
#guard (treeOf sample [] (.base "Proc") (.subst (.apply "Zero" []) (.apply "Zero" []))).toOption.isNone
#guard (treeOf sample [] (.base "Name") (.apply "Zero" [])).toOption.isNone

end Controls

end Mettapedia.OSLF.MeTTaIL.ExportGF
