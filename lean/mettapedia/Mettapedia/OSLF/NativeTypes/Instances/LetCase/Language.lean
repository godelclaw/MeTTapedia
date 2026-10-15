import Mettapedia.OSLF.MeTTaIL.Syntax

/-!
# A sorted value/computation language with let and pair case

Values and computations are distinct carriers. Let binds one value in its
continuation; pair case binds two values in its ordered continuation. The
authored congruence premises select exactly computation positions. Values
have no reduction rule.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Instances.LetCase

open Mettapedia.OSLF.MeTTaIL.Syntax

def value : TypeExpr := .base "Value"
def computation : TypeExpr := .base "Computation"

def returnValue (term : Pattern) : Pattern := .apply "Return" [term]
def letTerm (initial body : Pattern) : Pattern := .apply "Let" [initial, .lambda none body]
def pair (first second : Pattern) : Pattern := .apply "Pair" [first, second]
def caseTerm (scrutinee body : Pattern) : Pattern :=
  .apply "Case" [scrutinee, .lambda none (.lambda none body)]

def letRule : RewriteRule where
  «name» := "LetReturn"
  typeContext := [("V", value), ("B", computation)]
  premises := []
  left := letTerm (returnValue (.fvar "V")) (.fvar "B")
  right := .subst (.fvar "B") (.fvar "V")
  bindings := some
    { dependencies := [("V", []), ("B", [value])]
      occurrences :=
        [{ «name» := "B", site := .left, path := [1, 0], arguments := [.bvar 0] },
         { «name» := "B", site := .right, path := [0], arguments := [.bvar 0] }] }

def caseRule : RewriteRule where
  «name» := "CasePair"
  typeContext := [("L", value), ("R", value), ("B", computation)]
  premises := []
  left := caseTerm (pair (.fvar "L") (.fvar "R")) (.fvar "B")
  right := .subst (.subst (.fvar "B") (.fvar "R")) (.fvar "L")
  bindings := some
    { dependencies := [("L", []), ("R", []), ("B", [value, value])]
      occurrences :=
        [{ «name» := "B", site := .left, path := [1, 0, 0], arguments := [.bvar 1, .bvar 0] },
         { «name» := "B", site := .right, path := [0, 0], arguments := [.bvar 1, .bvar 0] }] }

def letInitialCongruence : RewriteRule where
  «name» := "LetInitialCongruence"
  typeContext := [("E", computation), ("F", computation), ("B", computation)]
  premises := [.scopedStep ⟨[], computation, .fvar "E", .fvar "F"⟩]
  left := letTerm (.fvar "E") (.fvar "B")
  right := letTerm (.fvar "F") (.fvar "B")
  bindings := some
    { dependencies := [("E", []), ("F", []), ("B", [value])]
      occurrences :=
        [{ «name» := "B", site := .left, path := [1, 0], arguments := [.bvar 0] },
         { «name» := "B", site := .right, path := [1, 0], arguments := [.bvar 0] }] }

def letBodyCongruence : RewriteRule where
  «name» := "LetBodyCongruence"
  typeContext := [("E", computation), ("B", computation), ("C", computation)]
  premises := [.scopedStep ⟨[value], computation, .fvar "B", .fvar "C"⟩]
  left := letTerm (.fvar "E") (.fvar "B")
  right := letTerm (.fvar "E") (.fvar "C")
  bindings := some
    { dependencies := [("E", []), ("B", [value]), ("C", [value])]
      occurrences :=
        [{ «name» := "B", site := .left, path := [1, 0], arguments := [.bvar 0] },
         { «name» := "C", site := .right, path := [1, 0], arguments := [.bvar 0] },
         { «name» := "B", site := .premise 0 0 0, path := [], arguments := [.bvar 0] },
         { «name» := "C", site := .premise 0 0 1, path := [], arguments := [.bvar 0] }] }

def caseBodyCongruence : RewriteRule where
  «name» := "CaseBodyCongruence"
  typeContext := [("V", value), ("B", computation), ("C", computation)]
  premises := [.scopedStep ⟨[value, value], computation, .fvar "B", .fvar "C"⟩]
  left := caseTerm (.fvar "V") (.fvar "B")
  right := caseTerm (.fvar "V") (.fvar "C")
  bindings := some
    { dependencies := [("V", []), ("B", [value, value]), ("C", [value, value])]
      occurrences :=
        [{ «name» := "B", site := .left, path := [1, 0, 0], arguments := [.bvar 1, .bvar 0] },
         { «name» := "C", site := .right, path := [1, 0, 0], arguments := [.bvar 1, .bvar 0] },
         { «name» := "B", site := .premise 0 0 0, path := [], arguments := [.bvar 1, .bvar 0] },
         { «name» := "C", site := .premise 0 0 1, path := [], arguments := [.bvar 1, .bvar 0] }] }

def language : LanguageDef where
  name := "SortedLetCase"
  types := ["Value", "Computation"]
  terms :=
    [{ label := "Unit", category := "Value", params := [], syntaxPattern := [] },
     { label := "Pair", category := "Value",
       params := [.simple "left" value, .simple "right" value], syntaxPattern := [] },
     { label := "Return", category := "Computation",
       params := [.simple "value" value], syntaxPattern := [] },
     { label := "Let", category := "Computation",
       params := [.simple "initial" computation, .abstraction "body" (.arrow value computation)],
       syntaxPattern := [] },
     { label := "Case", category := "Computation",
       params := [.simple "value" value,
         .abstraction "body" (.arrow value (.arrow value computation))], syntaxPattern := [] }]
  equations := []
  rewrites := [letRule, caseRule, letInitialCongruence, letBodyCongruence, caseBodyCongruence]

end Mettapedia.OSLF.NativeTypes.Instances.LetCase
