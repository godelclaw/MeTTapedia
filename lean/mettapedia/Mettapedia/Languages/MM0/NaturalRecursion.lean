import Mettapedia.Languages.MM0.NaturalType
import Mettapedia.Logic.HOL.NaturalFacts

/-!
# Native HOL primitive-recursion reference

The native proof derives a least binary graph, totality and functionality,
then selects its unique value. The step takes the prior result before the
predecessor. The final statement is printed from intrinsic HOL syntax and
compared semantically with the shared natural-fact statement in its standard
interpretation, where numeral wrapping denotes identity. This is not a
source-to-MM0 checker refinement or a comparison of arbitrary Henkin models.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.NaturalRecursion

open Mettapedia.Logic.HOL
open HOLSyntaxWire NaturalClosure

abbrev Source := Mettapedia.Logic.HOL.NaturalFacts.Const
abbrev number := Mettapedia.Logic.HOL.NaturalFacts.number
abbrev target := Mettapedia.Logic.HOL.NaturalFacts.target
abbrev method := target ⇒ number ⇒ target

def encodeBase : Mettapedia.Logic.HOL.NaturalFacts.Base → Wire
  | .natural => NaturalType.numbers
  | .result => symbol "A"

def encodeConst {type} : Source type → Wire
  | .zero => NaturalType.origin
  | .successor => node "holSuccessor" []
  | .numeral => node "lam" [symbol "numeralInput", NaturalType.numbers, symbol "numeralInput"]

def formula : ClosedFormula Source :=
  .all (σ := target) (.all (σ := method)
    (.ex (σ := number ⇒ target)
      (.and (.eq (.app (.var .vz) (.const .zero)) (.var (.vs (.vs .vz))))
        (.all (σ := number)
          (.eq (.app (.var (.vs .vz)) (.app (.const .successor) (.var .vz)))
            (.app (.app (.var (.vs (.vs .vz))) (.app (.var (.vs .vz)) (.var .vz)))
              (.var .vz)))))))

def closedNames : Names ([] : Ctx Mettapedia.Logic.HOL.NaturalFacts.Base)
  | _, index => nomatch index

def binderName : Nat → String
  | 0 => "a"
  | 1 => "f"
  | 2 => "g"
  | 3 => "n"
  | index + 4 => "bound" ++ toString (index + 4)

def recursionBody : Wire := encodeTerm encodeBase encodeConst binderName closedNames 0 formula

theorem formula_meaning {numbers : Type 1} (origin : numbers) (next : numbers → numbers)
    (result : Type 1) :
    (Mettapedia.Logic.HOL.NaturalFacts.model origin next result).models formula ↔
      ∀ (base : result) (step : result → numbers → result), ∃ function : numbers → result,
        function origin = base ∧ ∀ n, function (next n) = step (function n) n := by
  constructor
  · intro valid base step
    obtain ⟨function, _, atZero, atNext⟩ := valid base trivial step trivial
    exact ⟨function, atZero, fun n => atNext n trivial⟩
  · intro existsFunction base _ step _
    obtain ⟨function, atZero, atNext⟩ := existsFunction base step
    exact ⟨function, trivial, atZero, fun n _ => atNext n⟩

/-- Comparison of independently stated formulas in the declared standard
interpretation. It does not identify the unwrapped and wrapped syntax. -/
theorem shared_fact_meaning {numbers : Type 1} (origin : numbers) (next : numbers → numbers)
    (result : Type 1) :
    (Mettapedia.Logic.HOL.NaturalFacts.model origin next result).models formula ↔
      (Mettapedia.Logic.HOL.NaturalFacts.model origin next result).models
        Mettapedia.Logic.HOL.NaturalFacts.recursion :=
  (formula_meaning origin next result).trans
    (Mettapedia.Logic.HOL.NaturalFacts.recursion_meaning origin next result).symm

/-- The full primitive-recursion statement has a concrete nonempty instance. -/
theorem standard_natural_recursion (result : Type 1) :
    (Mettapedia.Logic.HOL.NaturalFacts.model (ULift.up 0 : ULift.{1} Nat)
      (fun n => ULift.up (n.down + 1)) result).models formula := by
  apply (formula_meaning _ _ _).mpr
  intro base step
  refine ⟨fun n => Nat.rec base (fun previous prior => step prior (ULift.up previous)) n.down,
    rfl, ?_⟩
  intro n
  cases n
  rfl

/-- A collapsed constructor does not satisfy the exported recursion statement. -/
theorem fixed_zero_refuses_recursion :
    ¬ (Mettapedia.Logic.HOL.NaturalFacts.model (ULift.up false : ULift.{1} Bool)
      id (ULift.{1} Bool)).models formula := by
  intro accepted
  obtain ⟨function, atZero, atNext⟩ :=
    (formula_meaning _ _ _).mp accepted (ULift.up false) (fun _ _ => ULift.up true)
  have impossible := atNext (ULift.up false)
  change function (ULift.up false) = ULift.up true at impossible
  rw [atZero] at impossible
  exact Bool.false_ne_true (congrArg ULift.down impossible)

def valueType : Wire := symbol "A"
def naturalType : Wire := NaturalType.numbers
def stepType : Wire := arrow valueType (arrow naturalType valueType)
def relationType : Wire := arrow naturalType (arrow valueType (node "bool" []))
def graph (n v : Wire) : Wire := node "holRecursionGraph"
  [valueType, symbol "a", symbol "f", n, v]
def recursor : Wire := node "holRecursor" [valueType, symbol "a", symbol "f"]
def applyNext (n : Wire) : Wire := NaturalType.next n

def graphStep (relation : Wire) : Wire := node "allc"
  [symbol "previousIndex", naturalType, node "allc" [symbol "previousValue", valueType,
    node "impc" [application (application relation (symbol "previousIndex")) (symbol "previousValue"),
      application (application relation (applyNext (symbol "previousIndex")))
        (application (application (symbol "f") (symbol "previousValue")) (symbol "previousIndex"))]]]

def graphBody : Wire := node "allc" [symbol "r", relationType,
  node "impc" [application (application (symbol "r") NaturalType.origin) (symbol "a"),
    node "impc" [node "allc" [symbol "k", naturalType, node "allc" [symbol "w", valueType,
      node "impc" [application (application (symbol "r") (symbol "k")) (symbol "w"),
        application (application (symbol "r") (applyNext (symbol "k")))
          (application (application (symbol "f") (symbol "w")) (symbol "k"))]]],
      application (application (symbol "r") (symbol "n")) (symbol "v")]]]

def recursorBody : Wire := node "lam" [symbol "number", naturalType,
  application (node "sel" [valueType])
    (node "lam" [symbol "value", valueType, graph (symbol "number") (symbol "value")])]

structure Parameters where
  native : String
  declaration : String

def parameters (names : List String) (bounds : List String := []) : Parameters where
  native := "((var G wff ()) (var A type ())" ++
    String.join (names.map fun name => " (var " ++ name ++ " term ())") ++
    String.join (bounds.map fun name => " (bound " ++ name ++ " term)") ++ ")"
  declaration := " (G: wff) (A: type)" ++
    (if names.isEmpty then "" else " (" ++ String.intercalate " " names ++ ": term)") ++
    (if bounds.isEmpty then "" else " {" ++ String.intercalate " " bounds ++ ": term}")

def claim (name : String) (parameters : Parameters) (hypotheses : List Wire)
    (conclusion : Wire) : String × String :=
  (statement name parameters.native hypotheses conclusion,
   "theorem " ++ name ++ parameters.declaration ++ ":\n " ++
     String.join (hypotheses.map fun hypothesis => "$ " ++ hypothesis.render ++ " $ >\n ") ++
     "$ " ++ conclusion.render ++ " $;\n")

def commonTyping : List Wire := [typed (symbol "a") valueType, typed (symbol "f") stepType]
def inverse : Wire := node "exc" [symbol "prior", valueType,
  node "andc" [graph (symbol "n") (symbol "prior"),
    NaturalType.equality valueType (symbol "v")
      (application (application (symbol "f") (symbol "prior")) (symbol "n"))]]

def eliminationClaim : String × String := claim "holRecursionGraphElimination"
  (parameters ["a", "f", "n", "v", "r"] ["previousIndex", "previousValue"])
  (commonTyping ++ [typed (symbol "n") naturalType, typed (symbol "v") valueType,
    typed (symbol "r") relationType, asserts (graph (symbol "n") (symbol "v")),
    asserts (application (application (symbol "r") NaturalType.origin) (symbol "a")),
    asserts (graphStep (symbol "r"))])
  (asserts (application (application (symbol "r") (symbol "n")) (symbol "v")))

def claims : List (String × (String × String)) := [
  ("holRecursionGraphElimination", eliminationClaim),
  ("holRecursionGraphZero", claim "holRecursionGraphZero" (parameters ["a", "f"])
    commonTyping (asserts (graph NaturalType.origin (symbol "a")))),
  ("holRecursionGraphSuccessor", claim "holRecursionGraphSuccessor"
    (parameters ["a", "f", "n", "v"])
    (commonTyping ++ [typed (symbol "n") naturalType, typed (symbol "v") valueType,
      asserts (graph (symbol "n") (symbol "v"))])
    (asserts (graph (applyNext (symbol "n"))
      (application (application (symbol "f") (symbol "v")) (symbol "n"))))),
  ("holRecursionGraphExists", claim "holRecursionGraphExists"
    (parameters ["a", "f", "n"] ["value"])
    (commonTyping ++ [typed (symbol "n") naturalType])
    (asserts (node "exc" [symbol "value", valueType, graph (symbol "n") (symbol "value")]))),
  ("holRecursionGraphZeroUnique", claim "holRecursionGraphZeroUnique"
    (parameters ["a", "f", "v"])
    (commonTyping ++ [typed (symbol "v") valueType, asserts (graph NaturalType.origin (symbol "v"))])
    (asserts (NaturalType.equality valueType (symbol "v") (symbol "a")))),
  ("holRecursionGraphSuccessorInverse", claim "holRecursionGraphSuccessorInverse"
    (parameters ["a", "f", "n", "v"] ["prior"])
    (commonTyping ++ [typed (symbol "n") naturalType, typed (symbol "v") valueType,
      asserts (graph (applyNext (symbol "n")) (symbol "v"))]) (asserts inverse)),
  ("holRecursionGraphFunctional", claim "holRecursionGraphFunctional"
    (parameters ["a", "f", "n", "v", "w"])
    (commonTyping ++ [typed (symbol "n") naturalType, typed (symbol "v") valueType,
      typed (symbol "w") valueType, asserts (graph (symbol "n") (symbol "v")),
      asserts (graph (symbol "n") (symbol "w"))])
    (asserts (NaturalType.equality valueType (symbol "v") (symbol "w")))),
  ("holRecursorT", claim "holRecursorT" (parameters ["a", "f"])
    commonTyping (typed recursor (arrow naturalType valueType))),
  ("holRecursorGraph", claim "holRecursorGraph" (parameters ["a", "f", "n"])
    (commonTyping ++ [typed (symbol "n") naturalType])
    (asserts (graph (symbol "n") (application recursor (symbol "n"))))),
  ("holRecursorZero", claim "holRecursorZero" (parameters ["a", "f"])
    commonTyping (asserts (NaturalType.equality valueType
      (application recursor NaturalType.origin) (symbol "a")))),
  ("holRecursorSuccessor", claim "holRecursorSuccessor" (parameters ["a", "f", "n"])
    (commonTyping ++ [typed (symbol "n") naturalType])
    (asserts (NaturalType.equality valueType (application recursor (applyNext (symbol "n")))
      (application (application (symbol "f") (application recursor (symbol "n"))) (symbol "n"))))),
  ("holNaturalRecursion", claim "holNaturalRecursion" (parameters [] ["a", "f", "g", "n"])
    [] (asserts recursionBody))]

def statements : List (String × String) := claims.map fun entry => (entry.1, entry.2.1)

def definitions : List (String × Wire) :=
  [("holRecursionGraph", graphBody), ("holRecursor", recursorBody)]

-- Declarations follow the proof stream's public order, including the recursor
-- definition after the graph's existence and functionality results.
def specification : String := NaturalType.specification ++
  "def holRecursionGraph (A: type) (a f n v: term) {.r .k .w: term}: term = $ " ++
    graphBody.render ++ " $;\n" ++
  String.join (claims.take 7 |>.map fun entry => entry.2.2) ++
  "def holRecursor (A: type) (a f: term) {.number .value: term}: term = $ " ++
    recursorBody.render ++ " $;\n" ++
  String.join (claims.drop 7 |>.map fun entry => entry.2.2)

def verdicts : List (String × Bool) := [
  ("MM0 recursion retains its arbitrary result type", (encodeBase .result).render == "A"),
  ("MM0 recursion public statements have distinct names", decide ((statements.map Prod.fst).Nodup)),
  ("MM0 recursion definitions have distinct names", decide ((definitions.map Prod.fst).Nodup)),
  ("MM0 recursion preserves result-before-predecessor order",
    (graph (symbol "n") (symbol "v")).render != (graph (symbol "v") (symbol "n")).render),
  ("MM0 functionality retains both graph witnesses", statements.length == 12)]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

end Mettapedia.Languages.MM0.NaturalRecursion
