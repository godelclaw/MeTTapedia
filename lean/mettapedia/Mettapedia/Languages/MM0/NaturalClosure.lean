import Mettapedia.Logic.HOL.NaturalClosure
import Mettapedia.Languages.MM0.HOLSyntaxWire

/-!
# The typed reference for MM0's HOL natural-closure proofs

The MM1 proofs are checked against a specification whose definition body is
printed from the shared intrinsic HOL term. The public rule statements retain
their object-typing hypotheses; native replay and exact statement comparison
are qualified by the accompanying driver.

This component establishes zero, successor and ordinary closure elimination.
It does not yet export primitive recursion, no-confusion or infinity. The
supplied HOL presentation and its full axiom inventory are not identified with
the independently verified configured HOL-to-MM0 translation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.NaturalClosure

open Mettapedia.Logic.HOL
open HOLSyntaxWire

universe u v w

variable {Base : Type u} {Const : Ty Base → Type v}

theorem definition_meaning (model : HenkinModel.{u, v, w} Base Const) (type : Ty Base)
    (valuation : model.Valuation [type, type ⇒ type, type]) :
    (model.denote (Mettapedia.Logic.HOL.NaturalClosure.declarationBody type) valuation).down ↔
      Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder model type
        (valuation (.vs (.vs .vz))) (valuation (.vs .vz)) (valuation .vz) := Iff.rfl

abbrev EmptyConstants : Ty Unit → Type := fun _ => Empty

def carrier : Ty Unit := .base ()

def names : Names [carrier, carrier ⇒ carrier, carrier]
  | _, .vz => "n"
  | _, .vs .vz => "s"
  | _, .vs (.vs .vz) => "z"

def binders : Nat → String
  | 0 => "p"
  | 1 => "k"
  | index + 2 => "bound" ++ toString (index + 2)

def definitionBody : Wire :=
  encodeTerm (Const := EmptyConstants) (fun _ => .symbol "A")
    (fun name => nomatch name) binders names 0
    (Mettapedia.Logic.HOL.NaturalClosure.declarationBody carrier)

theorem reference_names_distinct :
    ["G", "A", "z", "s", "n", "p", "k"].Nodup := by decide +kernel

def symbol (name : String) : Wire := .symbol name
def node (head : String) (arguments : List Wire) : Wire := .application head arguments
def application (function argument : Wire) : Wire := node "app" [function, argument]
def arrow (domain result : Wire) : Wire := node "fun" [domain, result]
def entails (formula : Wire) : Wire := node "im" [symbol "G", formula]
def typed (value type : Wire) : Wire := entails (node "ty" [value, type])
def asserts (formula : Wire) : Wire := entails (node "thm" [formula])
def member (number : Wire) : Wire :=
  node "naturalClosure" [symbol "A", symbol "z", symbol "s", number]

def step : Wire :=
  node "allc" [symbol "k", symbol "A", node "impc"
    [application (symbol "p") (symbol "k"),
     application (symbol "p") (application (symbol "s") (symbol "k"))]]

def objectBinders : String :=
  "((var G wff ()) (var A type ()) (var z term ()) (var s term ()))"

def statement (name context : String) (hypotheses : List Wire) (conclusion : Wire) : String :=
  "(theorem " ++ name ++ " " ++ context ++ " (" ++
    String.intercalate " " (hypotheses.map (fun term => term.render)) ++ ") " ++ conclusion.render ++ ")"

def zeroStatement : String :=
  statement "naturalClosureZero" objectBinders
    [typed (symbol "z") (symbol "A"), typed (symbol "s") (arrow (symbol "A") (symbol "A"))]
    (asserts (member (symbol "z")))

def successorStatement : String :=
  statement "naturalClosureSuccessor"
    "((var G wff ()) (var A type ()) (var z term ()) (var s term ()) (var n term ()))"
    [typed (symbol "z") (symbol "A"), typed (symbol "s") (arrow (symbol "A") (symbol "A")),
     typed (symbol "n") (symbol "A"), asserts (member (symbol "n"))]
    (asserts (member (application (symbol "s") (symbol "n"))))

def eliminationStatement : String :=
  statement "naturalClosureElimination"
    "((var G wff ()) (var A type ()) (var z term ()) (var s term ()) (var n term ()) (var p term ()) (bound k term))"
    [typed (symbol "z") (symbol "A"), typed (symbol "s") (arrow (symbol "A") (symbol "A")),
     typed (symbol "n") (symbol "A"), typed (symbol "p") (arrow (symbol "A") (node "bool" [])),
     asserts (member (symbol "n")), asserts (application (symbol "p") (symbol "z")), asserts step]
    (asserts (application (symbol "p") (symbol "n")))

/-- Prefix constructor syntax is parsed by the existing MM0 reader. -/
def specification : String :=
  "def naturalClosure (A: type) (z s n: term) {.p .k: term}: term = $ " ++
    definitionBody.render ++ " $;\n" ++
  "theorem naturalClosureZero (G: wff) (A: type) (z s: term):\n" ++
  " $ G |- z: A $ > $ G |- s: A -> A $ > $ G |- naturalClosure A z s z $;\n" ++
  "theorem naturalClosureSuccessor (G: wff) (A: type) (z s n: term):\n" ++
  " $ G |- z: A $ > $ G |- s: A -> A $ > $ G |- n: A $ >\n" ++
  " $ G |- naturalClosure A z s n $ > $ G |- naturalClosure A z s (s @ n) $;\n" ++
  "theorem naturalClosureElimination (G: wff) (A: type) (z s n p: term) {k: term}:\n" ++
  " $ G |- z: A $ > $ G |- s: A -> A $ > $ G |- n: A $ >\n" ++
  " $ G |- p: A -> bool $ > $ G |- naturalClosure A z s n $ >\n" ++
  " $ G |- p @ z $ > $ G |- !k: A. p @ k ==> p @ (s @ k) $ > $ G |- p @ n $;\n"

def finiteModel : HenkinModel.{0, 0, 0} Unit EmptyConstants :=
  .standard (fun _ => ULift.{1} Bool) (fun name => nomatch name)

theorem finite_zero :
    Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder finiteModel carrier
      (ULift.up false) (fun _ => ULift.up false) (ULift.up false) :=
  Mettapedia.Logic.HOL.NaturalClosure.closedUnder_zero _ _ _ _

/-- Closure alone does not imply that another inhabitant is generated. -/
theorem finite_other_refused :
    ¬ Mettapedia.Logic.HOL.NaturalClosure.ClosedUnder finiteModel carrier
      (ULift.up false) (fun _ => ULift.up false) (ULift.up true) := by
  intro closed
  have impossible := closed (fun value => .up (value.down = false)) (by trivial) rfl (by
    intro _ _ _
    rfl)
  cases impossible

def verdicts : List (String × Bool) :=
  [("MM0 HOL native names distinct", decide (["G", "A", "z", "s", "n", "p", "k"].Nodup)),
   ("MM0 HOL zero and successor claims differ", zeroStatement != successorStatement),
   ("MM0 HOL predicate and carrier arguments differ", binders 0 != names (.vz))]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

end Mettapedia.Languages.MM0.NaturalClosure
