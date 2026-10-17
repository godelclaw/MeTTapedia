import Mettapedia.OSLF.MeTTaIL.Upstream.Ambient
import Mettapedia.OSLF.MeTTaIL.LanguageProfiles

/-!
# Upstream MeTTaIL's ambient-calculus tests

The 29 inputs of upstream's `languages/tests/ambient_tests.rs`, in order, as core patterns: a
bag is `PPar`'s collection, `new(x, P)` binds by index, and every free name carries the sort
upstream's parser gives it. `complex_mobility_with_binding` uses its bound name `x` as a
process (`in(m, x)`); upstream is untyped there, and here the input is ill-sorted.

`conformanceLanguage` is the language the tests run in: upstream's text as written
(`upstreamLiteral`) with the standard collection-laws profile, in core form.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Upstream.AmbientTests

open Mettapedia.OSLF.MeTTaIL Syntax

/-- Upstream's literal declaration with collection laws, in core form. -/
def conformanceLanguage : LanguageDef :=
  match (LanguageProfiles.collectionLaws Ambient.upstreamLiteral).toCore with
  | .ok core => core.language
  | .error _ => Ambient.upstreamLiteral

#guard (LanguageProfiles.collectionLaws Ambient.upstreamLiteral).toCore matches .ok _

/-- Upstream's test inputs: name, free names with their sorts, and the source term. -/
def tests : List (String × List (String × TypeExpr) × Pattern) := [
  ("enter_empty_rest", [("m", .base "Name"), ("n", .base "Name"), ("p", .base "Proc"), ("r", .base "Proc")], (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.fvar "p")])] none)]), (.apply "PAmb" [(.fvar "m"), (.fvar "r")])] none)),
  ("exit_empty_rest", [("m", .base "Name"), ("n", .base "Name"), ("p", .base "Proc"), ("r", .base "Proc")], (.apply "PAmb" [(.fvar "m"), (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "POut" [(.fvar "m"), (.fvar "p")])] none)]), (.fvar "r")] none)])),
  ("open_basic", [("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc")], (.collection .hashBag [(.apply "POpen" [(.fvar "n"), (.fvar "p")]), (.apply "PAmb" [(.fvar "n"), (.fvar "q")])] none)),
  ("enter_nonempty_rest", [("m", .base "Name"), ("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc"), ("r", .base "Proc")], (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.fvar "p")]), (.fvar "q")] none)]), (.apply "PAmb" [(.fvar "m"), (.fvar "r")])] none)),
  ("enter_multiple_rest", [("m", .base "Name"), ("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc"), ("r", .base "Proc"), ("s", .base "Proc")], (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.fvar "p")]), (.fvar "q"), (.fvar "s")] none)]), (.apply "PAmb" [(.fvar "m"), (.fvar "r")])] none)),
  ("exit_nonempty_rest", [("m", .base "Name"), ("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc"), ("r", .base "Proc")], (.apply "PAmb" [(.fvar "m"), (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "POut" [(.fvar "m"), (.fvar "p")]), (.fvar "q")] none)]), (.fvar "r")] none)])),
  ("exit_multiple_rest", [("m", .base "Name"), ("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc"), ("r", .base "Proc"), ("s", .base "Proc"), ("t", .base "Proc")], (.apply "PAmb" [(.fvar "m"), (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "POut" [(.fvar "m"), (.fvar "p")]), (.fvar "q"), (.fvar "s"), (.fvar "t")] none)]), (.fvar "r")] none)])),
  ("context_preservation", [("m", .base "Name"), ("n", .base "Name"), ("local", .base "Proc"), ("p", .base "Proc"), ("r", .base "Proc"), ("state1", .base "Proc"), ("state2", .base "Proc")], (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.fvar "p")]), (.fvar "state1"), (.fvar "state2")] none)]), (.apply "PAmb" [(.fvar "m"), (.collection .hashBag [(.fvar "r"), (.fvar "local")] none)])] none)),
  ("parallel_entry", [("a", .base "Name"), ("b", .base "Name"), ("parent", .base "Name"), ("x", .base "Proc"), ("y", .base "Proc"), ("z", .base "Proc")], (.collection .hashBag [(.apply "PAmb" [(.fvar "a"), (.collection .hashBag [(.apply "PIn" [(.fvar "parent"), (.fvar "x")])] none)]), (.apply "PAmb" [(.fvar "b"), (.collection .hashBag [(.apply "PIn" [(.fvar "parent"), (.fvar "y")])] none)]), (.apply "PAmb" [(.fvar "parent"), (.fvar "z")])] none)),
  ("sequential_mobility", [("agent", .base "Name"), ("loc1", .base "Name"), ("loc2", .base "Name")], (.collection .hashBag [(.apply "PAmb" [(.fvar "agent"), (.collection .hashBag [(.apply "PIn" [(.fvar "loc1"), (.apply "PIn" [(.fvar "loc2"), (.collection .hashBag [] none)])])] none)]), (.apply "PAmb" [(.fvar "loc1"), (.collection .hashBag [] none)]), (.apply "PAmb" [(.fvar "loc2"), (.collection .hashBag [] none)])] none)),
  ("nested_mobility", [("child", .base "Name"), ("grandparent", .base "Name"), ("parent", .base "Name")], (.collection .hashBag [(.apply "PAmb" [(.fvar "parent"), (.collection .hashBag [(.apply "PIn" [(.fvar "grandparent"), (.collection .hashBag [] none)]), (.apply "PAmb" [(.fvar "child"), (.collection .hashBag [] none)])] none)]), (.apply "PAmb" [(.fvar "grandparent"), (.collection .hashBag [] none)])] none)),
  ("entry_then_exit", [("m", .base "Name"), ("n", .base "Name"), ("p", .base "Proc"), ("r", .base "Proc")], (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.apply "POut" [(.fvar "m"), (.fvar "p")])])] none)]), (.apply "PAmb" [(.fvar "m"), (.fvar "r")])] none)),
  ("open_after_entry", [("agent", .base "Name"), ("container", .base "Name"), ("result", .base "Proc")], (.collection .hashBag [(.apply "PAmb" [(.fvar "agent"), (.collection .hashBag [(.apply "PIn" [(.fvar "container"), (.collection .hashBag [] none)])] none)]), (.apply "PAmb" [(.fvar "container"), (.collection .hashBag [(.apply "POpen" [(.fvar "agent"), (.fvar "result")])] none)])] none)),
  ("nested_ambients_in_rest", [("inner", .base "Name"), ("m", .base "Name"), ("n", .base "Name"), ("data", .base "Proc"), ("p", .base "Proc"), ("r", .base "Proc")], (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.fvar "p")]), (.apply "PAmb" [(.fvar "inner"), (.fvar "data")])] none)]), (.apply "PAmb" [(.fvar "m"), (.fvar "r")])] none)),
  ("congruence_in_ambient", [("m", .base "Name"), ("n", .base "Name"), ("outer", .base "Name"), ("p", .base "Proc"), ("r", .base "Proc")], (.apply "PAmb" [(.fvar "outer"), (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.fvar "p")])] none)]), (.apply "PAmb" [(.fvar "m"), (.fvar "r")])] none)])),
  ("congruence_in_parallel", [("m", .base "Name"), ("n", .base "Name"), ("observer", .base "Proc"), ("p", .base "Proc"), ("r", .base "Proc")], (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.fvar "p")])] none)]), (.apply "PAmb" [(.fvar "m"), (.fvar "r")]), (.fvar "observer")] none)),
  ("equation_then_rewrite_extrusion_in", [("m", .base "Name"), ("n", .base "Name")], (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.collection .hashBag [] none)])] none)]), (.apply "PNew" [.lambda none (.apply "PAmb" [(.fvar "m"), (.collection .hashBag [] none)])])] none)),
  ("equation_zero_then_rewrite", [("m", .base "Name"), ("n", .base "Name"), ("p", .base "Proc")], (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.fvar "p")])] none)]), (.apply "PAmb" [(.fvar "m"), (.collection .hashBag [] none)]), (.collection .hashBag [] none)] none)),
  ("nested_extrusion_in", [("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc")], (.apply "PNew" [.lambda none (.apply "PNew" [.lambda none (.collection .hashBag [(.fvar "p"), (.apply "PIn" [(.fvar "n"), (.fvar "q")])] none)])])),
  ("extrusion_enables_out", [("m", .base "Name"), ("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc")], (.collection .hashBag [(.apply "POpen" [(.fvar "n"), (.fvar "p")]), (.apply "PNew" [.lambda none (.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "POut" [(.fvar "m"), (.fvar "q")])] none)])])] none)),
  ("parallel_with_extrusion", [("m", .base "Name"), ("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc"), ("r", .base "Proc")], (.collection .hashBag [(.apply "PNew" [.lambda none (.collection .hashBag [(.fvar "p"), (.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.fvar "q")])] none)])] none)]), (.apply "PAmb" [(.fvar "m"), (.fvar "r")])] none)),
  ("zero_in_multiple_contexts", [("p", .base "Proc"), ("q", .base "Proc")], (.collection .hashBag [(.collection .hashBag [] none), (.fvar "p"), (.collection .hashBag [(.collection .hashBag [] none), (.fvar "q")] none)] none)),
  ("extrusion_amb_then_open", [("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc"), ("r", .base "Proc")], (.collection .hashBag [(.apply "POpen" [(.fvar "n"), (.fvar "p")]), (.apply "PNew" [.lambda none (.collection .hashBag [(.fvar "q"), (.apply "PAmb" [(.fvar "n"), (.fvar "r")])] none)])] none)),
  ("complex_mobility_with_binding", [("m", .base "Name"), ("n", .base "Name")], (.apply "PNew" [.lambda none (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.bvar 0)])] none)]), (.apply "PAmb" [(.fvar "m"), (.collection .hashBag [] none)])] none)])),
  ("sequential_extrusions", [("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc")], (.apply "PNew" [.lambda none (.apply "PNew" [.lambda none (.collection .hashBag [(.fvar "p"), (.apply "PIn" [(.fvar "n"), (.fvar "q")])] none)])])),
  ("zero_elimination_cascade", [], (.collection .hashBag [(.collection .hashBag [] none), (.collection .hashBag [] none), (.collection .hashBag [] none), (.collection .hashBag [] none)] none)),
  ("extrusion_with_out_and_in", [("k", .base "Name"), ("m", .base "Name"), ("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc"), ("r", .base "Proc")], (.apply "PNew" [.lambda none (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.fvar "p")]), (.apply "POut" [(.fvar "k"), (.fvar "q")])] none)]), (.apply "PAmb" [(.fvar "m"), (.fvar "r")])] none)])),
  ("open_after_amb_extrusion", [("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc"), ("r", .base "Proc")], (.collection .hashBag [(.apply "POpen" [(.fvar "n"), (.fvar "p")]), (.apply "PNew" [.lambda none (.collection .hashBag [(.apply "PAmb" [(.bvar 0), (.fvar "q")]), (.apply "PAmb" [(.fvar "n"), (.fvar "r")])] none)])] none)),
  ("in_with_zero_elimination", [("m", .base "Name"), ("n", .base "Name"), ("p", .base "Proc"), ("q", .base "Proc")], (.collection .hashBag [(.apply "PAmb" [(.fvar "n"), (.collection .hashBag [(.apply "PIn" [(.fvar "m"), (.collection .hashBag [(.fvar "p"), (.collection .hashBag [] none)] none)])] none)]), (.apply "PAmb" [(.fvar "m"), (.fvar "q")])] none))
]

/-- Every free name of every test, once, with its sort. -/
def free : List (String × TypeExpr) := (tests.flatMap fun row => row.2.1).eraseDups

#guard tests.length == 29
-- No name is given two sorts.
#guard (free.map Prod.fst).Nodup

end Mettapedia.OSLF.MeTTaIL.Upstream.AmbientTests
