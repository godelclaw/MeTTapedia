import Mettapedia.Languages.MM0.NaturalClosure
import Mettapedia.Logic.HOL.NaturalClosureInduction

/-!
# The MM0 HOL closure-premised induction interface

The strengthened predicate is a local definitional extension of the existing
closure presentation. The independent public statement retains the closure
guard in its step premise. Native replay checks the compiled MM1 proof against
this specification; printing alone confers no theorem authority.

The common intrinsic formula has its Henkin meaning without full domains.
The native source/format comparison remains an executed qualification, not a
formal refinement of the MM1 compiler or the full HOL presentation.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.NaturalInduction

open Mettapedia.Logic.HOL
open HOLSyntaxWire NaturalClosure

def strengtheningBody : Wire :=
  node "lam" [symbol "n", symbol "A", node "andc"
    [member (symbol "n"), application (symbol "p") (symbol "n")]]

def guardedStep : Wire :=
  node "allc" [symbol "k", symbol "A", node "impc"
    [member (symbol "k"), node "impc"
      [application (symbol "p") (symbol "k"),
       application (symbol "p") (application (symbol "s") (symbol "k"))]]]

def inductionStatement : String :=
  statement "naturalClosureInduction"
    "((var G wff ()) (var A type ()) (var z term ()) (var s term ()) (var n term ()) (var p term ()) (bound k term))"
    [typed (symbol "z") (symbol "A"), typed (symbol "s") (arrow (symbol "A") (symbol "A")),
     typed (symbol "n") (symbol "A"), typed (symbol "p") (arrow (symbol "A") (node "bool" [])),
     asserts (member (symbol "n")), asserts (application (symbol "p") (symbol "z")),
     asserts guardedStep]
    (asserts (application (symbol "p") (symbol "n")))

def specification : String :=
  NaturalClosure.specification ++
  "def naturalStrengthening (A: type) (z s p: term) {.n: term}: term = $ " ++
    strengtheningBody.render ++ " $;\n" ++
  "theorem naturalClosureInduction (G: wff) (A: type) (z s n p: term) {k: term}:\n" ++
  " $ G |- z: A $ > $ G |- s: A -> A $ > $ G |- n: A $ >\n" ++
  " $ G |- p: A -> bool $ > $ G |- naturalClosure A z s n $ >\n" ++
  " $ G |- p @ z $ >\n" ++
  " $ G |- !k: A. naturalClosure A z s k ==> p @ k ==> p @ (s @ k) $ > $ G |- p @ n $;\n"

def verdicts : List (String × Bool) := [
  ("MM0 guarded and ordinary closure steps differ", guardedStep.render != NaturalClosure.step.render),
  ("MM0 induction strengthens by closure as well as the property",
    strengtheningBody.render != (node "lam" [symbol "n", symbol "A",
      application (symbol "p") (symbol "n")]).render)]

theorem all_verdicts : verdicts.all Prod.snd = true := by decide +kernel

end Mettapedia.Languages.MM0.NaturalInduction
