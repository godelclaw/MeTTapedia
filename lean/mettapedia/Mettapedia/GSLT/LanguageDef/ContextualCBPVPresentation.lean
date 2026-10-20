import Mettapedia.OSLF.MeTTaIL.Syntax
import Mettapedia.GSLT.LanguageDef.ModuleFormat.Text
import Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring
import Mettapedia.TypeTheory.ContextualCBPVOperational

/-!
# The contextual CBPV calculus as an authored module presentation

`language` presents the calculus of `TypeTheory.ContextualCBPV*` as a
five-field `LanguageDef`: sorts `Value`, `Computation`, `Kind` and `Datum`;
one grammar rule per value and computation former (binders as authored
abstractions); and one rewrite rule per head step and per evaluation frame,
in the locally nameless rule format with explicit binder dependencies.

The two raise kinds of Prime's runtime no-value carrier are the `Kind`
constructors `ErrorKind` and `InertKind`. A handler that meets another kind
raises it again; the side condition is the relation premise
`KindDistinct raised handled`.

`moduleText` is the canonical portable text of this presentation. It reads
back to the same `LanguageDef` (`readModule_moduleText`). The constructor
labels and rule names are the Lean constructors' names, so the rendered
module, the Lean operational reading (`HeadStep`, `Step`) and the Prime
library realization use one vocabulary (`grammar_labels`, `rewrite_names`).
The typed Lean syntax is the elaborated payload of this presentation; a
checked elaboration from the raw presentation to it is not part of this file.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ContextualCBPVPresentation

open Mettapedia.OSLF.MeTTaIL.Syntax

def value : TypeExpr := .base "Value"
def computation : TypeExpr := .base "Computation"
def kind : TypeExpr := .base "Kind"
def datum : TypeExpr := .base "Datum"

private def node (head : String) (arguments : List Pattern) : Pattern := .apply head arguments
private def bind₁ (body : Pattern) : Pattern := .lambda none body
private def mv (name : String) : Pattern := .fvar name

private def occurrence (name : String) (site : RulePatternSite) (path : List Nat)
    (arguments : List Pattern) : MetavariableOccurrence :=
  { «name» := name, site := site, path := path, arguments := arguments }

/-! ## Grammar -/

def grammar : List GrammarRule :=
  [ { label := "Const", category := "Value", params := [.simple "datum" datum], syntaxPattern := [] },
    { label := "Prim", category := "Value",
      params := [.simple "operation" datum, .simple "argument" value], syntaxPattern := [] },
    { label := "Unit", category := "Value", params := [], syntaxPattern := [] },
    { label := "Pair", category := "Value",
      params := [.simple "left" value, .simple "right" value], syntaxPattern := [] },
    { label := "Thunk", category := "Value",
      params := [.simple "body" computation], syntaxPattern := [] },
    { label := "Return", category := "Computation",
      params := [.simple "value" value], syntaxPattern := [] },
    { label := "Bind", category := "Computation",
      params := [.simple "first" computation, .abstraction "body" (.arrow value computation)],
      syntaxPattern := [] },
    { label := "Force", category := "Computation",
      params := [.simple "suspended" value], syntaxPattern := [] },
    { label := "Lam", category := "Computation",
      params := [.abstraction "body" (.arrow value computation)], syntaxPattern := [] },
    { label := "App", category := "Computation",
      params := [.simple "function" computation, .simple "argument" value], syntaxPattern := [] },
    { label := "Split", category := "Computation",
      params := [.simple "pair" value,
        .abstraction "body" (.arrow value (.arrow value computation))], syntaxPattern := [] },
    { label := "Choose", category := "Computation",
      params := [.simple "left" computation, .simple "right" computation], syntaxPattern := [] },
    { label := "Read", category := "Computation",
      params := [.abstraction "body" (.arrow value computation)], syntaxPattern := [] },
    { label := "Write", category := "Computation",
      params := [.simple "state" value, .simple "next" computation], syntaxPattern := [] },
    { label := "Intent", category := "Computation",
      params := [.simple "request" value, .simple "next" computation], syntaxPattern := [] },
    { label := "Raise", category := "Computation",
      params := [.simple "kind" kind, .simple "payload" value], syntaxPattern := [] },
    { label := "Handle", category := "Computation",
      params := [.simple "first" computation, .simple "kind" kind,
        .abstraction "onReturn" (.arrow value computation),
        .abstraction "onRaise" (.arrow value computation)], syntaxPattern := [] },
    { label := "ErrorKind", category := "Kind", params := [], syntaxPattern := [] },
    { label := "InertKind", category := "Kind", params := [], syntaxPattern := [] } ]

/-! ## Rewrites: head steps -/

private def oneDependency (names : List String) (bound : List String) :
    List (String × List TypeExpr) :=
  names.map (fun name => (name, if bound.contains name then [value] else []))

def forceThunk : RewriteRule where
  «name» := "ForceThunk"
  typeContext := [("M", computation)]
  premises := []
  left := node "Force" [node "Thunk" [mv "M"]]
  right := mv "M"

def bindReturn : RewriteRule where
  «name» := "BindReturn"
  typeContext := [("V", value), ("N", computation)]
  premises := []
  left := node "Bind" [node "Return" [mv "V"], bind₁ (mv "N")]
  right := .subst (mv "N") (mv "V")
  bindings := some
    { dependencies := oneDependency ["V", "N"] ["N"]
      occurrences := [occurrence "N" .left [1, 0] [.bvar 0], occurrence "N" .right [0] [.bvar 0]] }

def appLam : RewriteRule where
  «name» := "AppLam"
  typeContext := [("M", computation), ("V", value)]
  premises := []
  left := node "App" [node "Lam" [bind₁ (mv "M")], mv "V"]
  right := .subst (mv "M") (mv "V")
  bindings := some
    { dependencies := oneDependency ["M", "V"] ["M"]
      occurrences := [occurrence "M" .left [0, 0, 0] [.bvar 0], occurrence "M" .right [0] [.bvar 0]] }

def splitPair : RewriteRule where
  «name» := "SplitPair"
  typeContext := [("L", value), ("R", value), ("B", computation)]
  premises := []
  left := node "Split" [node "Pair" [mv "L", mv "R"], bind₁ (bind₁ (mv "B"))]
  right := .subst (.subst (mv "B") (mv "R")) (mv "L")
  bindings := some
    { dependencies := [("L", []), ("R", []), ("B", [value, value])]
      occurrences :=
        [occurrence "B" .left [1, 0, 0] [.bvar 1, .bvar 0],
         occurrence "B" .right [0, 0] [.bvar 1, .bvar 0]] }

def bindChoose : RewriteRule where
  «name» := "BindChoose"
  typeContext := [("M", computation), ("K", computation), ("N", computation)]
  premises := []
  left := node "Bind" [node "Choose" [mv "M", mv "K"], bind₁ (mv "N")]
  right := node "Choose"
    [node "Bind" [mv "M", bind₁ (mv "N")], node "Bind" [mv "K", bind₁ (mv "N")]]
  bindings := some
    { dependencies := oneDependency ["M", "K", "N"] ["N"]
      occurrences :=
        [occurrence "N" .left [1, 0] [.bvar 0], occurrence "N" .right [0, 1, 0] [.bvar 0],
         occurrence "N" .right [1, 1, 0] [.bvar 0]] }

def bindRead : RewriteRule where
  «name» := "BindRead"
  typeContext := [("F", computation), ("N", computation)]
  premises := []
  left := node "Bind" [node "Read" [bind₁ (mv "F")], bind₁ (mv "N")]
  right := node "Read" [bind₁ (node "Bind" [mv "F", bind₁ (mv "N")])]
  bindings := some
    { dependencies := oneDependency ["F", "N"] ["F", "N"]
      occurrences :=
        [occurrence "F" .left [0, 0, 0] [.bvar 0], occurrence "N" .left [1, 0] [.bvar 0],
         occurrence "F" .right [0, 0, 0] [.bvar 0], occurrence "N" .right [0, 0, 1, 0] [.bvar 0]] }

private def bindThrough (ruleName head : String) (field : String) : RewriteRule where
  «name» := ruleName
  typeContext := [(field, value), ("M", computation), ("N", computation)]
  premises := []
  left := node "Bind" [node head [mv field, mv "M"], bind₁ (mv "N")]
  right := node head [mv field, node "Bind" [mv "M", bind₁ (mv "N")]]
  bindings := some
    { dependencies := oneDependency [field, "M", "N"] ["N"]
      occurrences := [occurrence "N" .left [1, 0] [.bvar 0], occurrence "N" .right [1, 1, 0] [.bvar 0]] }

def bindWrite : RewriteRule := bindThrough "BindWrite" "Write" "S"
def bindIntent : RewriteRule := bindThrough "BindIntent" "Intent" "Q"

def bindRaise : RewriteRule where
  «name» := "BindRaise"
  typeContext := [("J", kind), ("P", value), ("N", computation)]
  premises := []
  left := node "Bind" [node "Raise" [mv "J", mv "P"], bind₁ (mv "N")]
  right := node "Raise" [mv "J", mv "P"]
  bindings := some
    { dependencies := oneDependency ["J", "P", "N"] ["N"]
      occurrences := [occurrence "N" .left [1, 0] [.bvar 0]] }

def appChoose : RewriteRule where
  «name» := "AppChoose"
  typeContext := [("M", computation), ("K", computation), ("V", value)]
  premises := []
  left := node "App" [node "Choose" [mv "M", mv "K"], mv "V"]
  right := node "Choose" [node "App" [mv "M", mv "V"], node "App" [mv "K", mv "V"]]

def appRead : RewriteRule where
  «name» := "AppRead"
  typeContext := [("F", computation), ("V", value)]
  premises := []
  left := node "App" [node "Read" [bind₁ (mv "F")], mv "V"]
  right := node "Read" [bind₁ (node "App" [mv "F", mv "V"])]
  bindings := some
    { dependencies := oneDependency ["F", "V"] ["F"]
      occurrences := [occurrence "F" .left [0, 0, 0] [.bvar 0], occurrence "F" .right [0, 0, 0] [.bvar 0]] }

private def appThrough (ruleName head : String) (field : String) : RewriteRule where
  «name» := ruleName
  typeContext := [(field, value), ("M", computation), ("V", value)]
  premises := []
  left := node "App" [node head [mv field, mv "M"], mv "V"]
  right := node head [mv field, node "App" [mv "M", mv "V"]]

def appWrite : RewriteRule := appThrough "AppWrite" "Write" "S"
def appIntent : RewriteRule := appThrough "AppIntent" "Intent" "Q"

def appRaise : RewriteRule where
  «name» := "AppRaise"
  typeContext := [("J", kind), ("P", value), ("V", value)]
  premises := []
  left := node "App" [node "Raise" [mv "J", mv "P"], mv "V"]
  right := node "Raise" [mv "J", mv "P"]

private def handleOf (first : Pattern) (kindPattern : Pattern) : Pattern :=
  node "Handle" [first, kindPattern, bind₁ (mv "N"), bind₁ (mv "H")]

private def handlerOccurrences (path : List Nat) (site : RulePatternSite) :
    List MetavariableOccurrence :=
  [occurrence "N" site (path ++ [2, 0]) [.bvar 0], occurrence "H" site (path ++ [3, 0]) [.bvar 0]]

def handleReturn : RewriteRule where
  «name» := "HandleReturn"
  typeContext := [("V", value), ("K", kind), ("N", computation), ("H", computation)]
  premises := []
  left := handleOf (node "Return" [mv "V"]) (mv "K")
  right := .subst (mv "N") (mv "V")
  bindings := some
    { dependencies := oneDependency ["V", "K", "N", "H"] ["N", "H"]
      occurrences := handlerOccurrences [] .left ++ [occurrence "N" .right [0] [.bvar 0]] }

def handleCaught : RewriteRule where
  «name» := "HandleCaught"
  typeContext := [("K", kind), ("P", value), ("N", computation), ("H", computation)]
  premises := []
  left := handleOf (node "Raise" [mv "K", mv "P"]) (mv "K")
  right := .subst (mv "H") (mv "P")
  bindings := some
    { dependencies := oneDependency ["K", "P", "N", "H"] ["N", "H"]
      occurrences := handlerOccurrences [] .left ++ [occurrence "H" .right [0] [.bvar 0]] }

def handleOther : RewriteRule where
  «name» := "HandleOther"
  typeContext := [("J", kind), ("K", kind), ("P", value), ("N", computation), ("H", computation)]
  premises := [.relationQuery "KindDistinct" [mv "J", mv "K"]]
  left := handleOf (node "Raise" [mv "J", mv "P"]) (mv "K")
  right := node "Raise" [mv "J", mv "P"]
  bindings := some
    { dependencies := oneDependency ["J", "K", "P", "N", "H"] ["N", "H"]
      occurrences := handlerOccurrences [] .left }

def handleChoose : RewriteRule where
  «name» := "HandleChoose"
  typeContext := [("M", computation), ("L", computation), ("K", kind), ("N", computation),
    ("H", computation)]
  premises := []
  left := handleOf (node "Choose" [mv "M", mv "L"]) (mv "K")
  right := node "Choose" [handleOf (mv "M") (mv "K"), handleOf (mv "L") (mv "K")]
  bindings := some
    { dependencies := oneDependency ["M", "L", "K", "N", "H"] ["N", "H"]
      occurrences := handlerOccurrences [] .left ++ handlerOccurrences [0] .right ++
        handlerOccurrences [1] .right }

def handleRead : RewriteRule where
  «name» := "HandleRead"
  typeContext := [("F", computation), ("K", kind), ("N", computation), ("H", computation)]
  premises := []
  left := handleOf (node "Read" [bind₁ (mv "F")]) (mv "K")
  right := node "Read" [bind₁ (handleOf (mv "F") (mv "K"))]
  bindings := some
    { dependencies := oneDependency ["F", "K", "N", "H"] ["F", "N", "H"]
      occurrences :=
        [occurrence "F" .left [0, 0, 0] [.bvar 0], occurrence "F" .right [0, 0, 0] [.bvar 0]] ++
          handlerOccurrences [] .left ++ handlerOccurrences [0, 0] .right }

private def handleThrough (ruleName head field : String) : RewriteRule where
  «name» := ruleName
  typeContext := [(field, value), ("M", computation), ("K", kind), ("N", computation),
    ("H", computation)]
  premises := []
  left := handleOf (node head [mv field, mv "M"]) (mv "K")
  right := node head [mv field, handleOf (mv "M") (mv "K")]
  bindings := some
    { dependencies := oneDependency [field, "M", "K", "N", "H"] ["N", "H"]
      occurrences := handlerOccurrences [] .left ++ handlerOccurrences [1] .right }

def handleWrite : RewriteRule := handleThrough "HandleWrite" "Write" "S"
def handleIntent : RewriteRule := handleThrough "HandleIntent" "Intent" "Q"

/-! ## Rewrites: evaluation frames -/

def bindLeft : RewriteRule where
  «name» := "BindLeft"
  typeContext := [("E", computation), ("F", computation), ("N", computation)]
  premises := [.scopedStep ⟨[], computation, mv "E", mv "F"⟩]
  left := node "Bind" [mv "E", bind₁ (mv "N")]
  right := node "Bind" [mv "F", bind₁ (mv "N")]
  bindings := some
    { dependencies := oneDependency ["E", "F", "N"] ["N"]
      occurrences := [occurrence "N" .left [1, 0] [.bvar 0], occurrence "N" .right [1, 0] [.bvar 0]] }

def appLeft : RewriteRule where
  «name» := "AppLeft"
  typeContext := [("E", computation), ("F", computation), ("V", value)]
  premises := [.scopedStep ⟨[], computation, mv "E", mv "F"⟩]
  left := node "App" [mv "E", mv "V"]
  right := node "App" [mv "F", mv "V"]

def handleLeft : RewriteRule where
  «name» := "HandleLeft"
  typeContext := [("E", computation), ("F", computation), ("K", kind), ("N", computation),
    ("H", computation)]
  premises := [.scopedStep ⟨[], computation, mv "E", mv "F"⟩]
  left := handleOf (mv "E") (mv "K")
  right := handleOf (mv "F") (mv "K")
  bindings := some
    { dependencies := oneDependency ["E", "F", "K", "N", "H"] ["N", "H"]
      occurrences := handlerOccurrences [] .left ++ handlerOccurrences [] .right }

def rewrites : List RewriteRule :=
  [forceThunk, bindReturn, appLam, splitPair, bindChoose, bindRead, bindWrite, bindIntent,
    bindRaise, appChoose, appRead, appWrite, appIntent, appRaise, handleReturn, handleCaught,
    handleOther, handleChoose, handleRead, handleWrite, handleIntent, bindLeft, appLeft, handleLeft]

/-- The presentation. -/
def language : LanguageDef where
  name := "ContextualCBPV"
  types := [{ name := "Value" }, { name := "Computation" }, { name := "Kind" },
    { name := "Datum", carrier := .builtinString }]
  terms := grammar
  equations := []
  rewrites := rewrites

/-! ## One vocabulary -/

/-- Grammar labels, in the order of the Lean value and computation formers. -/
theorem grammar_labels :
    language.terms.map (·.label) =
      ["Const", "Prim", "Unit", "Pair", "Thunk", "Return", "Bind", "Force", "Lam", "App",
        "Split", "Choose", "Read", "Write", "Intent", "Raise", "Handle", "ErrorKind",
        "InertKind"] := rfl

/-- Rule names, in the order of the Lean `HeadStep` and `Step` constructors. -/
theorem rewrite_names :
    language.rewrites.map (·.name) =
      ["ForceThunk", "BindReturn", "AppLam", "SplitPair", "BindChoose", "BindRead", "BindWrite",
        "BindIntent", "BindRaise", "AppChoose", "AppRead", "AppWrite", "AppIntent", "AppRaise",
        "HandleReturn", "HandleCaught", "HandleOther", "HandleChoose", "HandleRead",
        "HandleWrite", "HandleIntent", "BindLeft", "AppLeft", "HandleLeft"] := rfl

/-! ## Portable module text -/

open Mettapedia.GSLT.LanguageDef.ModuleAlgebra.NativeAuthoring

/-- The canonical portable module text of the presentation. -/
def moduleText : String := ModuleFormat.Text.render (Wire.language language)

/-- Read portable module text as a language definition. -/
def readModule (source : String) : Option LanguageDef := do
  Wire.language? (← ModuleFormat.Text.read? source)

/-- **The module text reads back as the presentation.** -/
theorem readModule_moduleText : readModule moduleText = some language := by
  change (ModuleFormat.Text.read? (ModuleFormat.Text.render (Wire.language language))).bind
      Wire.language? = some language
  rw [ModuleFormat.Text.read_render, Option.bind_some, Wire.language_roundtrip]

#print axioms readModule_moduleText

end Mettapedia.GSLT.LanguageDef.ContextualCBPVPresentation
