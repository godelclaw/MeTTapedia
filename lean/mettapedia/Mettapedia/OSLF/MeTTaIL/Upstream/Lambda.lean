import Mettapedia.OSLF.MeTTaIL.LanguageDefDSL
import Mettapedia.OSLF.MeTTaIL.CoreLanguageDef
import Mettapedia.OSLF.MeTTaIL.Substitution

/-!
# Upstream MeTTaIL's lambda calculus, as authored

`language` is upstream's `languages/src/lambda.rs` declaration, rule for rule, in the
`languageDef!` notation (upstream's variable `fun` is spelled `fn`): one sort, abstraction and
application, β by substitution, and congruence on both sides of an application and under an
abstraction. Upstream has no test
file for it; `tests` are inputs chosen to exercise each rule: β with and without discarding,
redexes on both sides, reduction under binders, capture avoidance, a self-reproducing term and
combinators.

Controls:

- the declaration reduces and passes the core predicate;
- `Beta` applies the abstraction's body to the argument;
- `LamCong`'s premise is a step under one `Term` binder;
- every test is closed under its binders, and no free name is bound twice.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.Upstream.Lambda

open Mettapedia.OSLF.MeTTaIL Syntax

open LanguageDefDSL in
/-- Upstream's declaration. -/
def language : LanguageDef :=
  languageDef! {
    name : "Lambda"
    types {
      Term
    }
    terms {
      Lam . ^x.body:[Term -> Term] |- "lam " x "." body : Term;
      App . fn:Term, arg:Term |- "(" fn "," arg ")" : Term;
    }
    equations {
    }
    rewrites {
      Beta . |- (App (Lam fn) arg) ~> (eval fn arg);
      AppCongL . | M0 ~> M1 |- (App M0 N) ~> (App M1 N);
      AppCongR . | N0 ~> N1 |- (App M N0) ~> (App M N1);
      LamCong . | S ~> T |- (Lam ^x.S) ~> (Lam ^x.T);
    }
  }

/-- The language in core form. -/
def reduced : LanguageDef :=
  match language.toCore with
  | .ok core => core.language
  | .error _ => language

#guard language.toCore.toOption.isSome
#guard CoreReduction.isCore reduced
#guard reduced.rewrites.map (·.name) == ["Beta", "AppCongL", "AppCongR", "LamCong"]

-- `Beta`: `fn` stands for the abstraction, so it depends on one `Term`, and `(eval fn arg)`
-- is the substitution of `arg` for that dependency.
#guard (reduced.rewrites[0]?).map (fun rule => (rule.left, rule.right)) == some
  (.apply "App" [.apply "Lam" [.lambda none (.fvar "fn")], .fvar "arg"], .subst (.fvar "fn") (.fvar "arg"))
#guard (reduced.rewrites[0]?.bind (·.bindings)).map (·.dependencies) ==
  some [("fn", [.base "Term"]), ("arg", [])]

-- `LamCong`: a step under one `Term` binder.
#guard (reduced.rewrites[3]?).map (·.premises) ==
  some [.scopedStep ⟨[.base "Term"], .base "Term", .fvar "S", .fvar "T"⟩]

/-! ## Test inputs -/

/-- Lambda terms with named binders, written as upstream writes them. -/
inductive Source where
  | var (name : String)
  | lam (binder : String) (body : Source)
  | app (function argument : Source)

/-- A core pattern: a name bound by an enclosing `lam` becomes its index. -/
def Source.pattern (binders : List String) : Source → Pattern
  | .var name => match binders.idxOf? name with
      | some index => .bvar index
      | none => .fvar name
  | .lam binder body => .apply "Lam" [.lambda none (body.pattern (binder :: binders))]
  | .app function argument => .apply "App" [function.pattern binders, argument.pattern binders]

/-- The names a term uses free. -/
def Source.free (binders : List String) : Source → List String
  | .var name => if binders.contains name then [] else [name]
  | .lam binder body => body.free (binder :: binders)
  | .app function argument => function.free binders ++ argument.free binders

/-- Upstream's concrete syntax. -/
def Source.render : Source → String
  | .var name => name
  | .lam binder body => s!"lam {binder}.{body.render}"
  | .app function argument => s!"({function.render},{argument.render})"

open Source in
private def identity (x : String) : Source := lam x (var x)

open Source in
private def church (n : Nat) : Source :=
  lam "f" (lam "x" ((List.replicate n ()).foldr (fun _ body => app (var "f") body) (var "x")))

open Source in
private def combK : Source := lam "x" (lam "y" (var "x"))

open Source in
private def combS : Source :=
  lam "x" (lam "y" (lam "z" (app (app (var "x") (var "z")) (app (var "y") (var "z")))))

open Source in
/-- The inputs: name and term. -/
def sources : List (String × Source) := [
  ("beta_identity", app (identity "x") (var "y")),
  ("self_application", app (lam "x" (app (var "x") (var "x"))) (identity "y")),
  ("k_combinator", app (app combK (var "a")) (var "b")),
  ("both_sides", app (lam "x" (app (identity "y") (var "x"))) (app (identity "z") (var "w"))),
  ("capture_avoidance", app (lam "x" (lam "y" (app (var "x") (var "y")))) (var "y")),
  ("under_binder", lam "x" (app (identity "y") (var "x"))),
  ("omega", app (lam "x" (app (var "x") (var "x"))) (lam "x" (app (var "x") (var "x")))),
  ("church_two", app (app (church 2) (var "g")) (var "a")),
  ("church_three", app (app (church 3) (var "g")) (var "a")),
  ("skk", app (app (app combS combK) combK) (var "a")),
  ("free_head", app (var "f") (app (identity "x") (var "a"))),
  ("under_two_binders", lam "a" (lam "b" (app (app (identity "x") (var "a")) (app (identity "y") (var "b"))))),
  ("discarding", app (app (lam "x" (identity "y")) (app (identity "z") (var "w"))) (var "v")),
  ("nested_redexes", app (identity "x") (app (identity "y") (app (identity "z") (var "a"))))
]

/-- Every test as a name, its free names with their sort, and its core pattern. -/
def tests : List (String × List (String × TypeExpr) × Pattern) :=
  sources.map fun (name, term) => (name, (term.free []).eraseDups.map (·, .base "Term"), term.pattern [])

/-- Every free name of every test, once, with its sort. -/
def free : List (String × TypeExpr) := (tests.flatMap fun row => row.2.1).eraseDups

#guard tests.length == 14
#guard (free.map Prod.fst).Nodup
-- Every pattern is closed under its binders.
#guard tests.all fun row => Substitution.lc row.2.2
-- `capture_avoidance`: the argument `y` is free, the inner `y` is bound.
#guard (tests[4]?).map (·.2.1) == some [("y", .base "Term")]
#guard (tests[4]?).map (·.2.2) == some
  (.apply "App" [.apply "Lam" [.lambda none (.apply "Lam" [.lambda none (.apply "App" [.bvar 1, .bvar 0])])],
    .fvar "y"])

end Mettapedia.OSLF.MeTTaIL.Upstream.Lambda
