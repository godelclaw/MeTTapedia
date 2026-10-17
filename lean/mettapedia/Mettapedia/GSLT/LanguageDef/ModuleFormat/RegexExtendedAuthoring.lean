import Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSelectionAuthoring
import Mettapedia.GSLT.LanguageDef.RegexSelectionEquationExecution

/-!
# Authored context- and capture-dependent regex compilation

The regular compiler is retained literally as a prefix. The additional pattern
constructors are data and the additional equations specify their compilation.
Assertion bodies have separate structural addresses and local accepting rows.
Reverse lookbehind reverses concatenation, not branch priority or group names.
This finite presentation does not assert native execution adequacy.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexExtendedAuthoring

open Mettapedia.OSLF.MeTTaIL.Syntax

private def op (label : String) (parameters : List String) : GrammarRule where
  label := label
  category := "ReValue"
  params := parameters.map fun name => .simple name (.base "ReValue")
  syntaxPattern := .terminal label :: parameters.map .nonTerminal

def addedTerms : List GrammarRule := [
  op "re:backref" ["group", "comparison"],
  op "re:lookahead" ["body"], op "re:not-lookahead" ["body"],
  op "re:lookbehind" ["direction", "body"], op "re:not-lookbehind" ["direction", "body"],
  op "re:backref-at" ["at", "group", "comparison", "next"],
  op "re:look-at" ["at", "body", "kind", "next"],
  op "re:look-body" ["at"], op "re:look-end" ["at"],
  op "Forward" [], op "Reverse" [], op "Exact" [], op "AsciiFold" [], op "UnicodeFold" [],
  op "Ahead" [], op "NotAhead" [], op "Behind" [], op "NotBehind" [],
  op "ReverseBehind" [], op "ReverseNotBehind" [], op "re:reverse" ["body"]]

private def v (name : String) : Pattern := .fvar name
private def a (name : String) (arguments : List Pattern := []) : Pattern := .apply name arguments
private def eqn (name : String) (parameters : List String) (left right : Pattern) : Equation where
  name := name
  typeContext := parameters.map fun name => (name, .base "ReValue")
  premises := []
  left := left
  right := right

private def emit (body k origin : Pattern) := a "re:emit" [body, k, origin]
private def emitAcc (body k origin tail : Pattern) := a "re:emit-acc" [body, k, origin, tail]
private def cons (head tail : Pattern) := a "LCons" [head, tail]
private def reverse (body : Pattern) := a "re:reverse" [body]

private def emitLook (name source kind : String) (direction : Option String := none)
    (accumulator : Bool := false) : Equation :=
  let body := v "p"
  let pattern := a source (direction.toList.map a ++ [v "p"])
  let finish := a "re:look-end" [v "at"]
  let entry := a "re:look-body" [v "at"]
  let tail := if accumulator then v "tail" else a "LNil"
  eqn name (["p", "k", "at"] ++ if accumulator then ["tail"] else [])
    (if accumulator then emitAcc pattern (v "k") (v "at") (v "tail")
     else emit pattern (v "k") (v "at"))
    (cons (a "re:look-at" [v "at", entry, a kind, v "k"])
      (cons (a "re:match" [finish])
        (if accumulator then emitAcc body finish entry tail else emit body finish entry)))

private def lookEquations (accumulator : Bool) : List Equation :=
  let stem := if accumulator then "emit-acc-" else "emit-"
  [emitLook (stem ++ "lookahead") "re:lookahead" "Ahead" none accumulator,
   emitLook (stem ++ "not-lookahead") "re:not-lookahead" "NotAhead" none accumulator,
   emitLook (stem ++ "lookbehind-forward") "re:lookbehind" "Behind" (some "Forward") accumulator,
   emitLook (stem ++ "not-lookbehind-forward") "re:not-lookbehind" "NotBehind" (some "Forward") accumulator,
   emitLook (stem ++ "lookbehind-reverse") "re:lookbehind" "ReverseBehind" (some "Reverse") accumulator,
   emitLook (stem ++ "not-lookbehind-reverse") "re:not-lookbehind" "ReverseNotBehind" (some "Reverse") accumulator]

private def lowerUnary (name source : String) : Equation :=
  eqn name ["p"] (a "re:lower" [a source [v "p"]])
    (a source [a "re:lower" [v "p"]])

private def reverseUnary (name source : String) : Equation :=
  eqn name ["p", "g"] (reverse (a source [v "p", v "g"]))
    (a source [reverse (v "p"), v "g"])

def addedEquations : List Equation := [
  eqn "emit-backref" ["g", "mode", "k", "at"]
    (emit (a "re:backref" [v "g", v "mode"]) (v "k") (v "at"))
    (cons (a "re:backref-at" [v "at", v "g", v "mode", v "k"]) (a "LNil")),
  eqn "emit-acc-backref" ["g", "mode", "k", "at", "tail"]
    (emitAcc (a "re:backref" [v "g", v "mode"]) (v "k") (v "at") (v "tail"))
    (cons (a "re:backref-at" [v "at", v "g", v "mode", v "k"]) (v "tail"))] ++
  lookEquations false ++ lookEquations true ++ [
  eqn "lower-backref" ["g", "mode"]
    (a "re:lower" [a "re:backref" [v "g", v "mode"]])
    (a "re:backref" [v "g", v "mode"]),
  lowerUnary "lower-lookahead" "re:lookahead",
  lowerUnary "lower-not-lookahead" "re:not-lookahead",
  eqn "lower-lookbehind-forward" ["p"]
    (a "re:lower" [a "re:lookbehind" [a "Forward", v "p"]])
    (a "re:lookbehind" [a "Forward", a "re:lower" [v "p"]]),
  eqn "lower-lookbehind-reverse" ["p"]
    (a "re:lower" [a "re:lookbehind" [a "Reverse", v "p"]])
    (a "re:lookbehind" [a "Reverse", reverse (a "re:lower" [v "p"])]),
  eqn "lower-not-lookbehind-forward" ["p"]
    (a "re:lower" [a "re:not-lookbehind" [a "Forward", v "p"]])
    (a "re:not-lookbehind" [a "Forward", a "re:lower" [v "p"]]),
  eqn "lower-not-lookbehind-reverse" ["p"]
    (a "re:lower" [a "re:not-lookbehind" [a "Reverse", v "p"]])
    (a "re:not-lookbehind" [a "Reverse", reverse (a "re:lower" [v "p"])]),
  eqn "reverse-zero" [] (reverse (a "re:zero")) (a "re:zero"),
  eqn "reverse-epsilon" [] (reverse (a "re:epsilon")) (a "re:epsilon"),
  eqn "reverse-literal" ["a"] (reverse (a "re:literal" [v "a"])) (a "re:literal" [v "a"]),
  eqn "reverse-any" [] (reverse (a "re:any")) (a "re:any"),
  eqn "reverse-class" ["ranges"] (reverse (a "re:class" [v "ranges"])) (a "re:class" [v "ranges"]),
  eqn "reverse-assertion" ["which"] (reverse (a "re:assert" [v "which"])) (a "re:assert" [v "which"]),
  eqn "reverse-sequence" ["p", "q"] (reverse (a "re:seq" [v "p", v "q"]))
    (a "re:seq" [reverse (v "q"), reverse (v "p")]),
  eqn "reverse-alternative" ["p", "q"] (reverse (a "re:alt" [v "p", v "q"]))
    (a "re:alt" [reverse (v "p"), reverse (v "q")]),
  reverseUnary "reverse-optional" "re:optional",
  reverseUnary "reverse-star" "re:star", reverseUnary "reverse-plus" "re:plus",
  eqn "reverse-capture" ["g", "p"] (reverse (a "re:capture" [v "g", v "p"]))
    (a "re:capture" [v "g", reverse (v "p")]),
  eqn "reverse-exact" ["p", "n"] (reverse (a "re:repeat-exact" [v "p", v "n"]))
    (a "re:repeat-exact" [reverse (v "p"), v "n"]),
  eqn "reverse-at-least" ["p", "n", "g"]
    (reverse (a "re:repeat-at-least" [v "p", v "n", v "g"]))
    (a "re:repeat-at-least" [reverse (v "p"), v "n", v "g"]),
  eqn "reverse-bounded" ["p", "low", "extra", "g"]
    (reverse (a "re:repeat-bounded" [v "p", v "low", v "extra", v "g"]))
    (a "re:repeat-bounded" [reverse (v "p"), v "low", v "extra", v "g"]),
  eqn "reverse-backref" ["g", "mode"] (reverse (a "re:backref" [v "g", v "mode"]))
    (a "re:backref" [v "g", v "mode"]),
  eqn "reverse-lookahead" ["p"] (reverse (a "re:lookahead" [v "p"])) (a "re:lookahead" [v "p"]),
  eqn "reverse-not-lookahead" ["p"] (reverse (a "re:not-lookahead" [v "p"]))
    (a "re:not-lookahead" [v "p"]),
  eqn "reverse-lookbehind" ["direction", "p"]
    (reverse (a "re:lookbehind" [v "direction", v "p"])) (a "re:lookbehind" [v "direction", v "p"]),
  eqn "reverse-not-lookbehind" ["direction", "p"]
    (reverse (a "re:not-lookbehind" [v "direction", v "p"]))
    (a "re:not-lookbehind" [v "direction", v "p"])]

def theory : LanguageDef := { RegexSelectionAuthoring.theory with
  name := "RegexExtendedCompilerV1"
  terms := RegexSelectionAuthoring.terms ++ addedTerms
  equations := RegexSelectionAuthoring.equations ++ addedEquations }

theorem regular_equations_retained (equation : Equation)
    (member : equation ∈ RegexSelectionAuthoring.theory.equations) :
    equation ∈ theory.equations := List.mem_append_left _ member

theorem regular_terms_retained (term : GrammarRule)
    (member : term ∈ RegexSelectionAuthoring.theory.terms) : term ∈ theory.terms :=
  List.mem_append_left _ member

theorem no_implicit_host_rewrites : theory.rewrites = [] := rfl

def portableText : String := Text.render (Portable.coreCodec.encode theory)
def readPortable? (text : String) : Option LanguageDef :=
  (Text.read? text).bind Portable.coreCodec.decode

theorem portable_recovery : readPortable? portableText = some theory := by
  simp [readPortable?, portableText, Portable.coreCodec.decode_encode]

def program : DeterministicEquations.Program :=
  (theory.equations.mapM RegexSelection.EquationExecution.equation?).getD []

set_option maxRecDepth 8192 in
theorem extraction_exact :
    theory.equations.mapM RegexSelection.EquationExecution.equation? = some program := rfl

theorem term_count : theory.terms.length = 71 := by decide
theorem equation_count : theory.equations.length = 99 := by decide

end Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexExtendedAuthoring
