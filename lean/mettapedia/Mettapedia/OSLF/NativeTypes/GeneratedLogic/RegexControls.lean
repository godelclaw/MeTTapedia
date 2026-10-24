import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Controls: regular expressions by derivatives

The regex language of the CeTTa runtime (`RegexCore`), as its module reader elaborates it (`regex`). Regular
expressions match words by Brzozowski derivatives. Each rule is big-step: `match(p, word)` rewrites to its
Boolean result in one step, and the steps of its premises (nullability, derivatives, the next match) are
the derivation of that step. Letters are compared by the relations `rx:scalar_eq` and `rx:scalar_ne`, which
a relation environment provides (`scalars`). The language has no equation, so closed regions decide its
formulas.

- `a*` matches `aa`: the match steps, and every step ends at `rx:true` (`star_matches`); no step ends at
  `rx:false` (`star_never_false`).
- `a` does not match `b` (`literal_mismatch`), nor the empty word (`literal_empty`).
- `ab*` matches `abb`, with exactly one result (`concat_star_one_result`).
- Without the letter relations, `a` cannot even be compared with `a`, so the match does not step
  (`no_letters_stuck`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.RegexControls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)

/-- The regex language, as the runtime's module reader elaborates it. -/
def regex : LanguageDef :=
  { «name» := "RegexDerivatives",
    «types» := [⟨"Scalar", .builtinString⟩, ⟨"Regex", .ast⟩, ⟨"Word", .ast⟩, ⟨"Bool", .ast⟩],
    «terms» := [
      { label := "rx:zero", category := "Regex", params := [],
        syntaxPattern := [.terminal "rx:zero"] },
      { label := "rx:epsilon", category := "Regex", params := [],
        syntaxPattern := [.terminal "rx:epsilon"] },
      { label := "rx:literal", category := "Regex", params := [.simple "a" (.base "Scalar")],
        syntaxPattern := [.terminal "rx:literal", .nonTerminal "a"] },
      { label := "rx:any", category := "Regex", params := [],
        syntaxPattern := [.terminal "rx:any"] },
      { label := "rx:union", category := "Regex", params := [.simple "p" (.base "Regex"), .simple "q" (.base "Regex")],
        syntaxPattern := [.terminal "rx:union", .nonTerminal "p", .nonTerminal "q"] },
      { label := "rx:concat", category := "Regex", params := [.simple "p" (.base "Regex"), .simple "q" (.base "Regex")],
        syntaxPattern := [.terminal "rx:concat", .nonTerminal "p", .nonTerminal "q"] },
      { label := "rx:star", category := "Regex", params := [.simple "p" (.base "Regex")],
        syntaxPattern := [.terminal "rx:star", .nonTerminal "p"] },
      { label := "rx:false", category := "Bool", params := [],
        syntaxPattern := [.terminal "rx:false"] },
      { label := "rx:true", category := "Bool", params := [],
        syntaxPattern := [.terminal "rx:true"] },
      { label := "rx:nil", category := "Word", params := [],
        syntaxPattern := [.terminal "rx:nil"] },
      { label := "rx:cons", category := "Word", params := [.simple "a" (.base "Scalar"), .simple "rest" (.base "Word")],
        syntaxPattern := [.terminal "rx:cons", .nonTerminal "a", .nonTerminal "rest"] },
      { label := "rx:nullable", category := "Bool", params := [.simple "p" (.base "Regex")],
        syntaxPattern := [.terminal "rx:nullable", .nonTerminal "p"] },
      { label := "rx:derivative", category := "Regex", params := [.simple "a" (.base "Scalar"), .simple "p" (.base "Regex")],
        syntaxPattern := [.terminal "rx:derivative", .nonTerminal "a", .nonTerminal "p"] },
      { label := "rx:match", category := "Bool", params := [.simple "p" (.base "Regex"), .simple "input" (.base "Word")],
        syntaxPattern := [.terminal "rx:match", .nonTerminal "p", .nonTerminal "input"] },
      { label := "rx:or", category := "Bool", params := [.simple "left" (.base "Bool"), .simple "right" (.base "Bool")],
        syntaxPattern := [.terminal "rx:or", .nonTerminal "left", .nonTerminal "right"] },
      { label := "rx:and", category := "Bool", params := [.simple "left" (.base "Bool"), .simple "right" (.base "Bool")],
        syntaxPattern := [.terminal "rx:and", .nonTerminal "left", .nonTerminal "right"] }],
    «equations» := [],
    «rewrites» := [
      { «name» := "OR-FF", typeContext := [],
        premises := [],
        left := .apply "rx:or" [.apply "rx:false" [], .apply "rx:false" []],
        right := .apply "rx:false" [] },
      { «name» := "OR-FT", typeContext := [],
        premises := [],
        left := .apply "rx:or" [.apply "rx:false" [], .apply "rx:true" []],
        right := .apply "rx:true" [] },
      { «name» := "OR-TF", typeContext := [],
        premises := [],
        left := .apply "rx:or" [.apply "rx:true" [], .apply "rx:false" []],
        right := .apply "rx:true" [] },
      { «name» := "OR-TT", typeContext := [],
        premises := [],
        left := .apply "rx:or" [.apply "rx:true" [], .apply "rx:true" []],
        right := .apply "rx:true" [] },
      { «name» := "AND-FF", typeContext := [],
        premises := [],
        left := .apply "rx:and" [.apply "rx:false" [], .apply "rx:false" []],
        right := .apply "rx:false" [] },
      { «name» := "AND-FT", typeContext := [],
        premises := [],
        left := .apply "rx:and" [.apply "rx:false" [], .apply "rx:true" []],
        right := .apply "rx:false" [] },
      { «name» := "AND-TF", typeContext := [],
        premises := [],
        left := .apply "rx:and" [.apply "rx:true" [], .apply "rx:false" []],
        right := .apply "rx:false" [] },
      { «name» := "AND-TT", typeContext := [],
        premises := [],
        left := .apply "rx:and" [.apply "rx:true" [], .apply "rx:true" []],
        right := .apply "rx:true" [] },
      { «name» := "NULL-ZERO", typeContext := [],
        premises := [],
        left := .apply "rx:nullable" [.apply "rx:zero" []],
        right := .apply "rx:false" [] },
      { «name» := "NULL-EPSILON", typeContext := [],
        premises := [],
        left := .apply "rx:nullable" [.apply "rx:epsilon" []],
        right := .apply "rx:true" [] },
      { «name» := "NULL-LITERAL", typeContext := [("a", .base "Scalar")],
        premises := [],
        left := .apply "rx:nullable" [.apply "rx:literal" [.fvar "a"]],
        right := .apply "rx:false" [] },
      { «name» := "NULL-ANY", typeContext := [],
        premises := [],
        left := .apply "rx:nullable" [.apply "rx:any" []],
        right := .apply "rx:false" [] },
      { «name» := "NULL-UNION", typeContext := [("p", .base "Regex"), ("q", .base "Regex"), ("left", .base "Bool"), ("right", .base "Bool"), ("result", .base "Bool")],
        premises := [.congruence (.apply "rx:nullable" [.fvar "p"]) (.fvar "left"), .congruence (.apply "rx:nullable" [.fvar "q"]) (.fvar "right"), .congruence (.apply "rx:or" [.fvar "left", .fvar "right"]) (.fvar "result")],
        left := .apply "rx:nullable" [.apply "rx:union" [.fvar "p", .fvar "q"]],
        right := .fvar "result" },
      { «name» := "NULL-CONCAT", typeContext := [("p", .base "Regex"), ("q", .base "Regex"), ("left", .base "Bool"), ("right", .base "Bool"), ("result", .base "Bool")],
        premises := [.congruence (.apply "rx:nullable" [.fvar "p"]) (.fvar "left"), .congruence (.apply "rx:nullable" [.fvar "q"]) (.fvar "right"), .congruence (.apply "rx:and" [.fvar "left", .fvar "right"]) (.fvar "result")],
        left := .apply "rx:nullable" [.apply "rx:concat" [.fvar "p", .fvar "q"]],
        right := .fvar "result" },
      { «name» := "NULL-STAR", typeContext := [("p", .base "Regex")],
        premises := [],
        left := .apply "rx:nullable" [.apply "rx:star" [.fvar "p"]],
        right := .apply "rx:true" [] },
      { «name» := "DERIV-ZERO", typeContext := [("a", .base "Scalar")],
        premises := [],
        left := .apply "rx:derivative" [.fvar "a", .apply "rx:zero" []],
        right := .apply "rx:zero" [] },
      { «name» := "DERIV-EPSILON", typeContext := [("a", .base "Scalar")],
        premises := [],
        left := .apply "rx:derivative" [.fvar "a", .apply "rx:epsilon" []],
        right := .apply "rx:zero" [] },
      { «name» := "DERIV-LITERAL-EQ", typeContext := [("a", .base "Scalar"), ("expected", .base "Scalar")],
        premises := [.relationQuery "rx:scalar_eq" [.fvar "expected", .fvar "a"]],
        left := .apply "rx:derivative" [.fvar "a", .apply "rx:literal" [.fvar "expected"]],
        right := .apply "rx:epsilon" [] },
      { «name» := "DERIV-LITERAL-NE", typeContext := [("a", .base "Scalar"), ("expected", .base "Scalar")],
        premises := [.relationQuery "rx:scalar_ne" [.fvar "expected", .fvar "a"]],
        left := .apply "rx:derivative" [.fvar "a", .apply "rx:literal" [.fvar "expected"]],
        right := .apply "rx:zero" [] },
      { «name» := "DERIV-ANY", typeContext := [("a", .base "Scalar")],
        premises := [],
        left := .apply "rx:derivative" [.fvar "a", .apply "rx:any" []],
        right := .apply "rx:epsilon" [] },
      { «name» := "DERIV-UNION", typeContext := [("a", .base "Scalar"), ("p", .base "Regex"), ("q", .base "Regex"), ("dp", .base "Regex"), ("dq", .base "Regex")],
        premises := [.congruence (.apply "rx:derivative" [.fvar "a", .fvar "p"]) (.fvar "dp"), .congruence (.apply "rx:derivative" [.fvar "a", .fvar "q"]) (.fvar "dq")],
        left := .apply "rx:derivative" [.fvar "a", .apply "rx:union" [.fvar "p", .fvar "q"]],
        right := .apply "rx:union" [.fvar "dp", .fvar "dq"] },
      { «name» := "DERIV-CONCAT-NULLABLE", typeContext := [("a", .base "Scalar"), ("p", .base "Regex"), ("q", .base "Regex"), ("dp", .base "Regex"), ("dq", .base "Regex")],
        premises := [.congruence (.apply "rx:nullable" [.fvar "p"]) (.apply "rx:true" []), .congruence (.apply "rx:derivative" [.fvar "a", .fvar "p"]) (.fvar "dp"), .congruence (.apply "rx:derivative" [.fvar "a", .fvar "q"]) (.fvar "dq")],
        left := .apply "rx:derivative" [.fvar "a", .apply "rx:concat" [.fvar "p", .fvar "q"]],
        right := .apply "rx:union" [.apply "rx:concat" [.fvar "dp", .fvar "q"], .fvar "dq"] },
      { «name» := "DERIV-CONCAT-NONNULLABLE", typeContext := [("a", .base "Scalar"), ("p", .base "Regex"), ("q", .base "Regex"), ("dp", .base "Regex")],
        premises := [.congruence (.apply "rx:nullable" [.fvar "p"]) (.apply "rx:false" []), .congruence (.apply "rx:derivative" [.fvar "a", .fvar "p"]) (.fvar "dp")],
        left := .apply "rx:derivative" [.fvar "a", .apply "rx:concat" [.fvar "p", .fvar "q"]],
        right := .apply "rx:concat" [.fvar "dp", .fvar "q"] },
      { «name» := "DERIV-STAR", typeContext := [("a", .base "Scalar"), ("p", .base "Regex"), ("dp", .base "Regex")],
        premises := [.congruence (.apply "rx:derivative" [.fvar "a", .fvar "p"]) (.fvar "dp")],
        left := .apply "rx:derivative" [.fvar "a", .apply "rx:star" [.fvar "p"]],
        right := .apply "rx:concat" [.fvar "dp", .apply "rx:star" [.fvar "p"]] },
      { «name» := "MATCH-NIL", typeContext := [("p", .base "Regex"), ("result", .base "Bool")],
        premises := [.congruence (.apply "rx:nullable" [.fvar "p"]) (.fvar "result")],
        left := .apply "rx:match" [.fvar "p", .apply "rx:nil" []],
        right := .fvar "result" },
      { «name» := "MATCH-CONS", typeContext := [("p", .base "Regex"), ("a", .base "Scalar"), ("rest", .base "Word"), ("next", .base "Regex"), ("result", .base "Bool")],
        premises := [.congruence (.apply "rx:derivative" [.fvar "a", .fvar "p"]) (.fvar "next"), .congruence (.apply "rx:match" [.fvar "next", .fvar "rest"]) (.fvar "result")],
        left := .apply "rx:match" [.fvar "p", .apply "rx:cons" [.fvar "a", .fvar "rest"]],
        right := .fvar "result" }] }

/-- Letters are equal or different as patterns. -/
def scalars : RelationEnv := ⟨fun relation arguments =>
  match relation, arguments with
  | "rx:scalar_eq", [first, second] => if first = second then [[first, second]] else []
  | "rx:scalar_ne", [first, second] => if first = second then [] else [[first, second]]
  | _, _ => []⟩

abbrev Regex := referenceStructure scalars regex

def letter (name : String) : Pattern := .apply name []
def literal (name : String) : Pattern := .apply "rx:literal" [letter name]
def star (p : Pattern) : Pattern := .apply "rx:star" [p]
def concat (p q : Pattern) : Pattern := .apply "rx:concat" [p, q]
def word : List String → Pattern
  | [] => .apply "rx:nil" []
  | a :: rest => .apply "rx:cons" [letter a, word rest]
def matching (p : Pattern) (w : List String) : Pattern := .apply "rx:match" [p, word w]

def yes : Pattern := .apply "rx:true" []
def no : Pattern := .apply "rx:false" []

/-- The match steps, and every step ends at `result`. -/
def endsAt (result : Pattern) : Formula 0 := .and (.possibly .any .top) (.necessarily .any (.is result))

/-- **`a*` matches `aa`.** -/
theorem star_matches : Regex.sat Env.closed (endsAt yes) (matching (star (literal "a")) ["a", "a"]) :=
  ask_proved (signature := []) (fuel := 12) (hint := none) (rounds := 6) (forms := none)
    (evidence := .closedRegion 6) (by decide +kernel)

/-- **No step ends at `rx:false`.** -/
theorem star_never_false :
    ¬ Regex.sat Env.closed (.possibly .any (.is no)) (matching (star (literal "a")) ["a", "a"]) :=
  ask_refuted (signature := []) (fuel := 12) (hint := none) (rounds := 6) (forms := none)
    (evidence := .closedRegion 6) (by decide +kernel)

/-- **`a` does not match `b`.** -/
theorem literal_mismatch : Regex.sat Env.closed (endsAt no) (matching (literal "a") ["b"]) :=
  ask_proved (signature := []) (fuel := 12) (hint := none) (rounds := 6) (forms := none)
    (evidence := .closedRegion 6) (by decide +kernel)

/-- **Nor the empty word.** -/
theorem literal_empty : Regex.sat Env.closed (endsAt no) (matching (literal "a") []) :=
  ask_proved (signature := []) (fuel := 12) (hint := none) (rounds := 6) (forms := none)
    (evidence := .closedRegion 6) (by decide +kernel)

/-- **`ab*` matches `abb`, with exactly one result.** -/
theorem concat_star_one_result :
    Regex.sat Env.closed (.and (endsAt yes) (Formula.exactlyOne .forward .any))
      (matching (concat (literal "a") (star (literal "b"))) ["a", "b", "b"]) :=
  ask_proved (signature := []) (fuel := 12) (hint := none) (rounds := 8) (forms := none)
    (evidence := .closedRegion 8) (by decide +kernel)

/-- **Without the letter relations, the match does not step.** -/
theorem no_letters_stuck :
    ¬ (referenceStructure RelationEnv.empty regex).sat Env.closed (.possibly .any .top) (matching (literal "a") ["a"]) :=
  ask_refuted (signature := []) (fuel := 12) (hint := none) (rounds := 6) (forms := none)
    (evidence := .closedRegion 6) (by decide +kernel)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.RegexControls
