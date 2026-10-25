import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
import Mettapedia.OSLF.MeTTaIL.ContextualStep

/-!
# Controls: binder spellings reduce to one core

A receive binds a process and a datum, `In x (^X.^d.P)` at the curried type `Proc -> Data -> Proc`,
and communication substitutes both: `Out x Q V | In x P ~> P[Q, V]`. The author may write the binder
nested (`^X.^d.P`), simultaneous (`^[X, d].P`), or leave the slot's metavariable bare (`P`), and may
write the application as `(eval (eval P Q) V)`. All three reduce to one core rule: the left side has
two single binders, and the right side two substitutions. Firing it substitutes both, in the core
semantics.

A constructor may declare the binder with every name, `^[X, d].p:[Proc -> Data -> Proc]`; its core
declaration names the first binder and its syntax no longer prints the second, exactly as if it had
been declared `^X.p`.

Negative controls: an application chain whose second argument mentions the first binder's name renames
the binder rather than capturing; a simultaneous spelling with more names than the type's telescope
has no core.
-/

namespace Mettapedia.OSLF.MeTTaIL.BinderSpellingControls

open Syntax CoreReduction

def processType : TypeExpr := .base "Proc"
def dataType : TypeExpr := .base "Data"
def nameType : TypeExpr := .base "Name"

/-- The receive declared with one binder name. -/
def inputSingle : GrammarRule :=
  { label := "In", category := "Proc",
    params := [.simple "x" nameType, .abstractionNamed (some "X") "p" (.arrow processType (.arrow dataType processType))],
    syntaxPattern := [.terminal "for", .terminal "(", .nonTerminal "X", .terminal "<-", .nonTerminal "x", .terminal ")",
      .terminal "{", .nonTerminal "p", .terminal "}"] }

/-- The receive declared with both binder names, the datum's name printed optionally. -/
def inputNamed : GrammarRule :=
  { inputSingle with
    params := [.simple "x" nameType, .multiAbstractionNamed ["X", "d"] "p" (.arrow processType (.arrow dataType processType))],
    syntaxPattern := [.terminal "for", .terminal "(", .nonTerminal "X",
      .op (.opt [.terminal ",", .nonTerminal "d"]), .terminal "<-", .nonTerminal "x", .terminal ")",
      .terminal "{", .nonTerminal "p", .terminal "}"] }

def otherTerms : List GrammarRule := [
  { label := "Nil", category := "Proc", params := [], syntaxPattern := [.terminal "0"] },
  { label := "Out", category := "Proc", params := [.simple "x" nameType, .simple "q" processType, .simple "v" dataType],
    syntaxPattern := [.nonTerminal "x", .terminal "!", .nonTerminal "q", .nonTerminal "v"] },
  { label := "Par", category := "Proc", params := [.simple "l" processType, .simple "r" processType],
    syntaxPattern := [.nonTerminal "l", .terminal "|", .nonTerminal "r"] },
  { label := "D", category := "Data", params := [], syntaxPattern := [.terminal "d"] },
  { label := "N", category := "Name", params := [], syntaxPattern := [.terminal "n"] }]

def apply (function argument : Pattern) : Pattern := .apply Pattern.evalHead [function, argument]

/-- Communication, with the receive's binder written by the given spelling. -/
def communication (binder : Pattern) (applied : Pattern) : RewriteRule :=
  { name := "Comm", typeContext := [("x", nameType), ("Q", processType), ("V", dataType)], premises := [],
    left := .apply "Par" [.apply "Out" [.fvar "x", .fvar "Q", .fvar "V"], .apply "In" [.fvar "x", binder]],
    right := apply (apply applied (.fvar "Q")) (.fvar "V") }

def nested : Pattern := .lambda (some "X") (.lambda (some "d") (.fvar "P"))
def simultaneous : Pattern := .multiLambda 2 ["X", "d"] (.fvar "P")

def withRule (input : GrammarRule) (rule : RewriteRule) : LanguageDef :=
  { name := "Receive", types := ["Proc", "Data", "Name"], terms := input :: otherTerms, equations := [],
    rewrites := [rule] }

def nestedLanguage := withRule inputSingle (communication nested nested)
def bareLanguage := withRule inputSingle (communication (.fvar "P") (.fvar "P"))
def simultaneousLanguage := withRule inputSingle (communication simultaneous simultaneous)
def namedLanguage := withRule inputNamed (communication simultaneous simultaneous)

/-- The core rule, if the language has a core. -/
def coreRule (language : LanguageDef) : Option (Pattern × Pattern) :=
  match language.toCore with
  | .ok core => core.language.rewrites.head?.map fun rule => (rule.left, rule.right)
  | .error _ => none

/-- Two binders on the left, two substitutions on the right. -/
def expected : Pattern × Pattern :=
  (.apply "Par" [.apply "Out" [.fvar "x", .fvar "Q", .fvar "V"],
      .apply "In" [.fvar "x", .lambda none (.lambda none (.fvar "P"))]],
    .subst (.subst (.fvar "P") (.fvar "V")) (.fvar "Q"))

#guard coreRule nestedLanguage == some expected
#guard coreRule bareLanguage == some expected
#guard coreRule simultaneousLanguage == some expected
#guard coreRule namedLanguage == some expected

/-- The named declaration's core form is the single-name declaration. -/
def coreReceive (language : LanguageDef) : Option (List TermParam × List SyntaxItem) :=
  match language.toCore with
  | .ok core => (core.language.terms.find? (·.label == "In")).map fun rule => (rule.params, rule.syntaxPattern)
  | .error _ => none

#guard (coreReceive namedLanguage).map (·.1) == some inputSingle.params
#guard reprStr ((coreReceive namedLanguage).map (·.2)) == reprStr (some inputSingle.syntaxPattern)

/-- Receive `0` and the datum `D` on `N`, and continue as `0 | N!(0, D)`. -/
def receiving : Pattern :=
  .apply "Par" [.apply "Out" [.apply "N" [], .apply "Nil" [], .apply "D" []],
    .apply "In" [.apply "N" [], .lambda none (.lambda none
      (.apply "Par" [.bvar 1, .apply "Out" [.apply "N" [], .bvar 1, .bvar 0]]))]]

def received : Pattern := .apply "Par" [.apply "Nil" [], .apply "Out" [.apply "N" [], .apply "Nil" [], .apply "D" []]]

def coreOf (language : LanguageDef) : LanguageDef :=
  match language.toCore with
  | .ok core => core.language
  | .error _ => language

-- Both substitutions happen: no application is left in the result.
#guard ContextualStep.reducts (coreOf nestedLanguage) 3 receiving == [received]
#guard ContextualStep.reducts (coreOf namedLanguage) 3 receiving == [received]

-- Negative: the second argument mentions `x`, so the binder `x` is renamed, not captured.
#guard betaNormal (apply (apply (.lambda (some "x") (.lambda (some "y") (.apply "Pair" [.fvar "x", .fvar "y"])))
    (.fvar "a")) (.fvar "x")) ==
  apply (.lambda (some "x'") (apply (.lambda (some "y") (.apply "Pair" [.fvar "x'", .fvar "y"])) (.fvar "x")))
    (.fvar "a")

-- Negative: three names for a telescope of two has no core.
#guard coreRule (withRule inputSingle (communication (.multiLambda 3 ["X", "d", "e"] (.fvar "P")) (.fvar "P"))) == none

end Mettapedia.OSLF.MeTTaIL.BinderSpellingControls
