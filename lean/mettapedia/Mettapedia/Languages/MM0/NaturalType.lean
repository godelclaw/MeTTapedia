import Mettapedia.Languages.MM0.NaturalCarrier

/-!
# Native HOL natural-subtype statements

The construction uses the existing nonempty-predicate type definition and
transports the established closure induction theorem. Its constructor and
induction statements retain all object-typing premises. This format interface
reuses the common HOL wire constructors; native replay checks the actual
proofs. It does not supply primitive recursion or full compiler refinement.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.NaturalType

open HOLSyntaxWire NaturalClosure

def individuals : Wire := node "ind" []
def numbers : Wire := node "holNatural" []
def predicate : Wire := node "holNaturalPredicate" []
def origin : Wire := node "holZero" []
def next (value : Wire) : Wire := application (node "holSuccessor" []) value
def abstraction (value : Wire) : Wire := application (node "abs" [predicate]) value
def representation (value : Wire) : Wire := application (node "rep" [predicate]) value
def equality (type first second : Wire) : Wire := node "eqc" [type, first, second]

def predicateBody : Wire := node "lam" [symbol "n", individuals,
  node "naturalClosure" [individuals, node "infiniteZero" [],
    node "infiniteSuccessor" [], symbol "n"]]
def typeBody : Wire := node "tydef" [predicate]
def zeroBody : Wire := abstraction (node "infiniteZero" [])
def successorBody : Wire := node "lam" [symbol "n", numbers,
  abstraction (application (node "infiniteSuccessor" []) (representation (symbol "n")))]
def pullbackBody : Wire := node "lam" [symbol "n", individuals,
  application (symbol "p") (abstraction (symbol "n"))]

def zeroTyped : String := statement "holZeroT" "((var G wff ()))" [] (typed origin numbers)
def successorTyped : String := statement "holSuccessorT" "((var G wff ()))" []
  (typed (node "holSuccessor" []) (arrow numbers numbers))

def noConfusion : Wire := node "notc" [equality numbers origin (next (symbol "n"))]
def noConfusionStatement : String :=
  statement "holZeroNotSuccessor" "((var G wff ()) (var n term ()))"
    [typed (symbol "n") numbers] (asserts noConfusion)

/-- The native presentation retains its `bi` abbreviation for Boolean equality. -/
def injectivity : Wire := node "bi"
  [equality numbers (next (symbol "m")) (next (symbol "n")),
   equality numbers (symbol "m") (symbol "n")]
def injectivityStatement : String :=
  statement "holSuccessorInjective" "((var G wff ()) (var m term ()) (var n term ()))"
    [typed (symbol "m") numbers, typed (symbol "n") numbers] (asserts injectivity)

def inductionStep : Wire := node "allc" [symbol "k", numbers,
  node "impc" [application (symbol "p") (symbol "k"),
    application (symbol "p") (next (symbol "k"))]]
def inductionStatement : String :=
  statement "holNaturalInduction"
    "((var G wff ()) (var n term ()) (var p term ()) (bound k term))"
    [typed (symbol "n") numbers, typed (symbol "p") (arrow numbers (node "bool" [])),
     asserts (application (symbol "p") origin), asserts inductionStep]
    (asserts (application (symbol "p") (symbol "n")))

def infinity : Wire := node "exc" [symbol "f", arrow numbers numbers,
  node "andc" [application (node "one_one" [numbers, numbers]) (symbol "f"),
    node "notc" [application (node "onto" [numbers, numbers]) (symbol "f")]]]
def infinityStatement : String := statement "holNaturalInfinity"
  "((var G wff ()) (bound f term))" [] (asserts infinity)

def definitions : List (String × Wire) := [
  ("holNaturalPredicate", predicateBody), ("holNatural", typeBody),
  ("holZero", zeroBody), ("holSuccessor", successorBody), ("holPullback", pullbackBody)]
def statements : List (String × String) := [
  ("holZeroT", zeroTyped), ("holSuccessorT", successorTyped),
  ("holZeroNotSuccessor", noConfusionStatement), ("holSuccessorInjective", injectivityStatement),
  ("holNaturalInduction", inductionStatement), ("holNaturalInfinity", infinityStatement)]

def specification : String := NaturalCarrier.specification ++
  "def holNaturalPredicate {.n: term}: term = $ " ++ predicateBody.render ++ " $;\n" ++
  "def holNatural: type = $ " ++ typeBody.render ++ " $;\n" ++
  "def holZero: term = $ " ++ zeroBody.render ++ " $;\n" ++
  "def holSuccessor {.n: term}: term = $ " ++ successorBody.render ++ " $;\n" ++
  "def holPullback (p: term) {.n: term}: term = $ " ++ pullbackBody.render ++ " $;\n" ++
  "theorem holZeroT (G: wff): $ G |- holZero: holNatural $;\n" ++
  "theorem holSuccessorT (G: wff): $ G |- holSuccessor: holNatural -> holNatural $;\n" ++
  "theorem holZeroNotSuccessor (G: wff) (n: term):\n" ++
  " $ G |- n: holNatural $ > $ G |- ~(=[holNatural] holZero = holSuccessor @ n) $;\n" ++
  "theorem holSuccessorInjective (G: wff) (m n: term):\n" ++
  " $ G |- m: holNatural $ > $ G |- n: holNatural $ >\n" ++
  " $ G |- (=[holNatural] holSuccessor @ m = holSuccessor @ n) <=> (=[holNatural] m = n) $;\n" ++
  "theorem holNaturalInduction (G: wff) (n p: term) {k: term}:\n" ++
  " $ G |- n: holNatural $ > $ G |- p: holNatural -> bool $ > $ G |- p @ holZero $ >\n" ++
  " $ G |- !k: holNatural. p @ k ==> p @ (holSuccessor @ k) $ > $ G |- p @ n $;\n" ++
  "theorem holNaturalInfinity (G: wff) {f: term}:\n" ++
  " $ G |- ?f: holNatural -> holNatural.\n" ++
  " one_one holNatural holNatural @ f /\\ ~(onto holNatural holNatural @ f) $;\n"

def verdicts : List (String × Bool) := [
  ("MM0 natural subtype differs from the ambient individual type", numbers.render != individuals.render),
  ("MM0 natural subtype retains its membership predicate", typeBody.render != individuals.render),
  ("MM0 natural induction uses the natural rather than ambient domain",
    inductionStep.render != NaturalClosure.step.render),
  ("MM0 natural no-confusion keeps its argument typing",
    noConfusionStatement != statement "holZeroNotSuccessor"
      "((var G wff ()) (var n term ()))" [] (asserts noConfusion))]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

end Mettapedia.Languages.MM0.NaturalType
