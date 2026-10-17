import Mettapedia.GSLT.LanguageDef.RegexExtendedAccumulatorExecution

/-!
# Authored lowering and reversal of dependent regex patterns

The source interpretation is independent of equation evaluation. Reverse
lookbehind reverses an already lowered body exactly once, before structural
emission. Counted repetition retains the dedicated plus construction.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.RegexExtendedLoweringExecution

open DeterministicEquations RegexExtendedCompilerSemantics RegexExtendedEquationExecution
open RegexDependentObservation (Comparison LookKind)

def count : Nat → Term
  | 0 => .sym "re:count-zero"
  | n + 1 => .expr [.sym "re:count-succ", count n]

def prependCopies (body : Pattern) : Nat → Pattern → Pattern
  | 0, tail => tail
  | n + 1, tail => .seq body (prependCopies body n tail)

def options (body : Pattern) : Nat → Bool → Pattern
  | 0, _ => .epsilon
  | n + 1, greedy => .optional (.seq body (options body n greedy)) greedy

def exactCopies (body : Pattern) (n : Nat) : Pattern := prependCopies body n .epsilon

def atLeast (body : Pattern) : Nat → Bool → Pattern
  | 0, greedy => .star body greedy
  | n + 1, greedy => prependCopies body n (.plus body greedy)

def bounded (body : Pattern) (lower extra : Nat) (greedy : Bool) : Pattern :=
  prependCopies body lower (options body extra greedy)

inductive Lowers : Term → Pattern → Prop where
  | zero : Lowers (.sym "re:zero") .zero
  | epsilon : Lowers (.sym "re:epsilon") .epsilon
  | literal (value : Nat) : Lowers (.expr [.sym "re:literal", natural value]) (.literal value)
  | any : Lowers (.sym "re:any") .any
  | class_ (values : List ScalarRange) : Lowers (.expr [.sym "re:class", ranges values]) (.class_ values)
  | assertion (name : String) : Lowers (.expr [.sym "re:assert", .lit name]) (.assertion name)
  | seq {first second : Term} {left right : Pattern} : Lowers first left → Lowers second right →
      Lowers (.expr [.sym "re:seq", first, second]) (.seq left right)
  | alt {first second : Term} {left right : Pattern} : Lowers first left → Lowers second right →
      Lowers (.expr [.sym "re:alt", first, second]) (.alt left right)
  | optional {input : Term} {body : Pattern} (greedy : Bool) : Lowers input body →
      Lowers (.expr [.sym "re:optional", input, preference greedy]) (.optional body greedy)
  | star {input : Term} {body : Pattern} (greedy : Bool) : Lowers input body →
      Lowers (.expr [.sym "re:star", input, preference greedy]) (.star body greedy)
  | plus {input : Term} {body : Pattern} (greedy : Bool) : Lowers input body →
      Lowers (.expr [.sym "re:plus", input, preference greedy]) (.plus body greedy)
  | capture {input : Term} {body : Pattern} (group : Nat) : Lowers input body →
      Lowers (.expr [.sym "re:capture", natural group, input]) (.capture group body)
  | exact {input : Term} {body : Pattern} (n : Nat) : Lowers input body →
      Lowers (.expr [.sym "re:repeat-exact", input, count n]) (exactCopies body n)
  | atLeast {input : Term} {body : Pattern} (n : Nat) (greedy : Bool) : Lowers input body →
      Lowers (.expr [.sym "re:repeat-at-least", input, count n, preference greedy]) (atLeast body n greedy)
  | bounded {input : Term} {body : Pattern} (lower extra : Nat) (greedy : Bool) : Lowers input body →
      Lowers (.expr [.sym "re:repeat-bounded", input, count lower, count extra, preference greedy])
        (bounded body lower extra greedy)
  | backref (group : Nat) (mode : Comparison) :
      Lowers (.expr [.sym "re:backref", natural group, comparison mode]) (.backref group mode)
  | lookahead {input : Term} {body : Pattern} : Lowers input body →
      Lowers (.expr [.sym "re:lookahead", input]) (.look .ahead body)
  | notLookahead {input : Term} {body : Pattern} : Lowers input body →
      Lowers (.expr [.sym "re:not-lookahead", input]) (.look .notAhead body)
  | lookbehind {input : Term} {body : Pattern} : Lowers input body →
      Lowers (.expr [.sym "re:lookbehind", .sym "Forward", input]) (.look .behind body)
  | notLookbehind {input : Term} {body : Pattern} : Lowers input body →
      Lowers (.expr [.sym "re:not-lookbehind", .sym "Forward", input]) (.look .notBehind body)
  | reverseLookbehind {input : Term} {body : Pattern} : Lowers input body →
      Lowers (.expr [.sym "re:lookbehind", .sym "Reverse", input]) (.look .reverseBehind body.reverse)
  | reverseNotLookbehind {input : Term} {body : Pattern} : Lowers input body →
      Lowers (.expr [.sym "re:not-lookbehind", .sym "Reverse", input]) (.look .reverseNotBehind body.reverse)

private theorem call {environment : Env} {head : String} {arguments values : List Term} {result : Term}
    (ordinary : ¬ Special head arguments)
    (children : List.Forall₂ (Evaluates program host environment) arguments values)
    (operation : Applies program host head values result) :
    Evaluates program host environment (.expr (.sym head :: arguments)) result :=
  Evaluates.call ordinary children operation

private theorem node1 {environment : Env} {head : String} {first firstValue : Term}
    (undefined : program.defines head = false) (ordinary : ¬ Special head [first])
    (one : Evaluates program host environment first firstValue) :
    Evaluates program host environment (.expr [.sym head, first]) (.expr [.sym head, firstValue]) :=
  call ordinary (.cons one .nil) (.constructor undefined rfl)

private theorem node2 {environment : Env} {head : String} {first second firstValue secondValue : Term}
    (undefined : program.defines head = false) (ordinary : ¬ Special head [first, second])
    (one : Evaluates program host environment first firstValue)
    (two : Evaluates program host environment second secondValue) :
    Evaluates program host environment (.expr [.sym head, first, second])
      (.expr [.sym head, firstValue, secondValue]) :=
  call ordinary (.cons one (.cons two .nil)) (.constructor undefined rfl)

theorem reverse_computes (pattern : Pattern) :
    Applies program host "re:reverse" [source pattern] (source pattern.reverse) := by
  induction pattern with
  | zero =>
      refine Applies.equation (equation := program[79]) (environment := []) (by rfl) (by rfl) ?_
      exact .symbol program host [] _
  | epsilon =>
      refine Applies.equation (equation := program[80]) (environment := []) (by rfl) (by rfl) ?_
      exact .symbol program host [] _
  | literal value =>
      refine Applies.equation (equation := program[81]) (environment := [("a", natural value)]) (by rfl) (by rfl) ?_
      exact node1 (by rfl) (by simp [Special]) (.variable (by rfl))
  | any =>
      refine Applies.equation (equation := program[82]) (environment := []) (by rfl) (by rfl) ?_
      exact .symbol program host [] _
  | class_ values =>
      refine Applies.equation (equation := program[83]) (environment := [("ranges", ranges values)]) (by rfl) (by rfl) ?_
      exact node1 (by rfl) (by simp [Special]) (.variable (by rfl))
  | assertion name =>
      refine Applies.equation (equation := program[84]) (environment := [("which", .lit name)]) (by rfl) (by rfl) ?_
      exact node1 (by rfl) (by simp [Special]) (.variable (by rfl))
  | seq first second one two =>
      refine Applies.equation (equation := program[85])
        (environment := [("p", source first), ("q", source second)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (call (by simp [Special]) (.cons (.variable (by rfl)) .nil) two)
        (call (by simp [Special]) (.cons (.variable (by rfl)) .nil) one)
  | alt first second one two =>
      refine Applies.equation (equation := program[86])
        (environment := [("p", source first), ("q", source second)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (call (by simp [Special]) (.cons (.variable (by rfl)) .nil) one)
        (call (by simp [Special]) (.cons (.variable (by rfl)) .nil) two)
  | optional body greedy ih | star body greedy ih | plus body greedy ih =>
      first
        | refine Applies.equation (equation := program[87])
            (environment := [("p", source body), ("g", preference greedy)]) (by rfl) (by rfl) ?_
        | refine Applies.equation (equation := program[88])
            (environment := [("p", source body), ("g", preference greedy)]) (by rfl) (by rfl) ?_
        | refine Applies.equation (equation := program[89])
            (environment := [("p", source body), ("g", preference greedy)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (call (by simp [Special]) (.cons (.variable (by rfl)) .nil) ih) (.variable (by rfl))
  | capture group body ih =>
      refine Applies.equation (equation := program[90])
        (environment := [("g", natural group), ("p", source body)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special]) (.variable (by rfl))
        (call (by simp [Special]) (.cons (.variable (by rfl)) .nil) ih)
  | backref group mode =>
      refine Applies.equation (equation := program[94])
        (environment := [("g", natural group), ("mode", comparison mode)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))
  | look which body _ =>
      cases which
      case ahead =>
        refine Applies.equation (equation := program[95]) (environment := [("p", source body)]) (by rfl) (by rfl) ?_
        exact node1 (by rfl) (by simp [Special]) (.variable (by rfl))
      case notAhead =>
        refine Applies.equation (equation := program[96]) (environment := [("p", source body)]) (by rfl) (by rfl) ?_
        exact node1 (by rfl) (by simp [Special]) (.variable (by rfl))
      all_goals first
        | refine Applies.equation (equation := program[97])
            (environment := [("direction", .sym "Forward"), ("p", source body)]) (by rfl) (by rfl) ?_
        | refine Applies.equation (equation := program[98])
            (environment := [("direction", .sym "Forward"), ("p", source body)]) (by rfl) (by rfl) ?_
        | refine Applies.equation (equation := program[97])
            (environment := [("direction", .sym "Reverse"), ("p", source body)]) (by rfl) (by rfl) ?_
        | refine Applies.equation (equation := program[98])
            (environment := [("direction", .sym "Reverse"), ("p", source body)]) (by rfl) (by rfl) ?_
      all_goals exact node2 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))

theorem prefix_computes (body tail : Pattern) (n : Nat) :
    Applies program host "re:repeat-prefix" [source body, count n, source tail]
      (source (prependCopies body n tail)) := by
  induction n with
  | zero =>
      refine Applies.equation (equation := program[18])
        (environment := [("p", source body), ("tail", source tail)]) (by rfl) (by rfl) ?_
      exact .variable (by rfl)
  | succ n ih =>
      refine Applies.equation (equation := program[19])
        (environment := [("p", source body), ("n", count n), ("tail", source tail)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special]) (.variable (by rfl))
        (call (by simp [Special]) (.cons (.variable (by rfl))
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ih)

theorem options_computes (body : Pattern) (n : Nat) (greedy : Bool) :
    Applies program host "re:repeat-options" [source body, count n, preference greedy]
      (source (options body n greedy)) := by
  induction n with
  | zero =>
      refine Applies.equation (equation := program[20])
        (environment := [("p", source body), ("g", preference greedy)]) (by rfl) (by rfl) ?_
      exact .symbol program host _ _
  | succ n ih =>
      refine Applies.equation (equation := program[21])
        (environment := [("p", source body), ("n", count n), ("g", preference greedy)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (node2 (by rfl) (by simp [Special]) (.variable (by rfl))
          (call (by simp [Special]) (.cons (.variable (by rfl))
            (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) ih))
        (.variable (by rfl))

theorem exact_computes (body : Pattern) (n : Nat) :
    Applies program host "re:repeat-exact" [source body, count n] (source (exactCopies body n)) := by
  refine Applies.equation (equation := program[22])
    (environment := [("p", source body), ("n", count n)]) (by rfl) (by rfl) ?_
  exact call (by simp [Special]) (.cons (.variable (by rfl))
    (.cons (.variable (by rfl)) (.cons (.symbol program host _ _) .nil))) (prefix_computes body .epsilon n)

theorem atLeast_computes (body : Pattern) (n : Nat) (greedy : Bool) :
    Applies program host "re:repeat-at-least" [source body, count n, preference greedy]
      (source (atLeast body n greedy)) := by
  cases n with
  | zero =>
      refine Applies.equation (equation := program[23])
        (environment := [("p", source body), ("g", preference greedy)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))
  | succ n =>
      refine Applies.equation (equation := program[24])
        (environment := [("p", source body), ("n", count n), ("g", preference greedy)]) (by rfl) (by rfl) ?_
      exact call (by simp [Special]) (.cons (.variable (by rfl))
        (.cons (.variable (by rfl)) (.cons
          (node2 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))) .nil)))
        (prefix_computes body (.plus body greedy) n)

theorem bounded_computes (body : Pattern) (lower extra : Nat) (greedy : Bool) :
    Applies program host "re:repeat-bounded" [source body, count lower, count extra, preference greedy]
      (source (bounded body lower extra greedy)) := by
  refine Applies.equation (equation := program[25])
    (environment := [("p", source body), ("low", count lower), ("extra", count extra),
      ("g", preference greedy)]) (by rfl) (by rfl) ?_
  exact call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
    (.cons (call (by simp [Special]) (.cons (.variable (by rfl))
      (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) (options_computes body extra greedy)) .nil)))
    (prefix_computes body (options body extra greedy) lower)

private theorem lower_variable {environment : Env} {variableName : String} {input : Term} {target : Pattern}
    (found : environment.lookup variableName = some input)
    (lowered : Applies program host "re:lower" [input] (source target)) :
    Evaluates program host environment (.expr [.sym "re:lower", .var variableName]) (source target) :=
  call (by simp [Special]) (.cons (.variable found) .nil) lowered

/-- Every structurally interpreted source, including nested counts, actually
normalizes through the extracted authored equations to that interpretation. -/
theorem lower_computes {input : Term} {target : Pattern} (lowered : Lowers input target) :
    Applies program host "re:lower" [input] (source target) := by
  induction lowered with
  | zero =>
      refine Applies.equation (equation := program[26]) (environment := []) (by rfl) (by rfl) ?_
      exact .symbol program host [] _
  | epsilon =>
      refine Applies.equation (equation := program[27]) (environment := []) (by rfl) (by rfl) ?_
      exact .symbol program host [] _
  | literal value =>
      refine Applies.equation (equation := program[28]) (environment := [("a", natural value)]) (by rfl) (by rfl) ?_
      exact node1 (by rfl) (by simp [Special]) (.variable (by rfl))
  | any =>
      refine Applies.equation (equation := program[29]) (environment := []) (by rfl) (by rfl) ?_
      exact .symbol program host [] _
  | class_ values =>
      refine Applies.equation (equation := program[30]) (environment := [("ranges", ranges values)]) (by rfl) (by rfl) ?_
      exact node1 (by rfl) (by simp [Special]) (.variable (by rfl))
  | assertion name =>
      refine Applies.equation (equation := program[31]) (environment := [("which", .lit name)]) (by rfl) (by rfl) ?_
      exact node1 (by rfl) (by simp [Special]) (.variable (by rfl))
  | @seq first second left right _ _ one two =>
      refine Applies.equation (equation := program[32])
        (environment := [("p", first), ("q", second)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (lower_variable (by rfl) one) (lower_variable (by rfl) two)
  | @alt first second left right _ _ one two =>
      refine Applies.equation (equation := program[33])
        (environment := [("p", first), ("q", second)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (lower_variable (by rfl) one) (lower_variable (by rfl) two)
  | @optional input body greedy _ ih =>
      refine Applies.equation (equation := program[34])
        (environment := [("p", input), ("g", preference greedy)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special]) (lower_variable (by rfl) ih) (.variable (by rfl))
  | @star input body greedy _ ih =>
      refine Applies.equation (equation := program[35])
        (environment := [("p", input), ("g", preference greedy)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special]) (lower_variable (by rfl) ih) (.variable (by rfl))
  | @plus input body greedy _ ih =>
      refine Applies.equation (equation := program[36])
        (environment := [("p", input), ("g", preference greedy)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special]) (lower_variable (by rfl) ih) (.variable (by rfl))
  | @capture input body group _ ih =>
      refine Applies.equation (equation := program[37])
        (environment := [("g", natural group), ("p", input)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special]) (.variable (by rfl)) (lower_variable (by rfl) ih)
  | @exact input body n _ ih =>
      refine Applies.equation (equation := program[38])
        (environment := [("p", input), ("n", count n)]) (by rfl) (by rfl) ?_
      exact call (by simp [Special]) (.cons (lower_variable (by rfl) ih)
        (.cons (.variable (by rfl)) .nil)) (exact_computes body n)
  | @atLeast input body n greedy _ ih =>
      refine Applies.equation (equation := program[39])
        (environment := [("p", input), ("n", count n), ("g", preference greedy)]) (by rfl) (by rfl) ?_
      exact call (by simp [Special]) (.cons (lower_variable (by rfl) ih)
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))) (atLeast_computes body n greedy)
  | @bounded input body lower extra greedy _ ih =>
      refine Applies.equation (equation := program[40])
        (environment := [("p", input), ("low", count lower), ("extra", count extra),
          ("g", preference greedy)]) (by rfl) (by rfl) ?_
      exact call (by simp [Special]) (.cons (lower_variable (by rfl) ih)
        (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil))))
        (bounded_computes body lower extra greedy)



  | backref group mode =>
      refine Applies.equation (equation := program[72])
        (environment := [("g", natural group), ("mode", comparison mode)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))
  | @lookahead input body _ ih =>
      refine Applies.equation (equation := program[73]) (environment := [("p", input)]) (by rfl) (by rfl) ?_
      exact node1 (by rfl) (by simp [Special]) (lower_variable (by rfl) ih)
  | @notLookahead input body _ ih =>
      refine Applies.equation (equation := program[74]) (environment := [("p", input)]) (by rfl) (by rfl) ?_
      exact node1 (by rfl) (by simp [Special]) (lower_variable (by rfl) ih)
  | @lookbehind input body _ ih =>
      refine Applies.equation (equation := program[75]) (environment := [("p", input)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special]) (.symbol program host _ _) (lower_variable (by rfl) ih)
  | @notLookbehind input body _ ih =>
      refine Applies.equation (equation := program[77]) (environment := [("p", input)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special]) (.symbol program host _ _) (lower_variable (by rfl) ih)
  | @reverseLookbehind input body _ ih =>
      refine Applies.equation (equation := program[76]) (environment := [("p", input)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special]) (.symbol program host _ _)
        (call (by simp [Special]) (.cons (lower_variable (by rfl) ih) .nil) (reverse_computes body))
  | @reverseNotLookbehind input body _ ih =>
      refine Applies.equation (equation := program[78]) (environment := [("p", input)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special]) (.symbol program host _ _)
        (call (by simp [Special]) (.cons (lower_variable (by rfl) ih) .nil) (reverse_computes body))

theorem lower_result_exact {input : Term} {target : Pattern} (lowered : Lowers input target) (result : Term) :
    Applies program host "re:lower" [input] result ↔ result = source target := by
  constructor
  · exact fun computed => computed.deterministic (lower_computes lowered)
  · rintro rfl; exact lower_computes lowered

theorem compile_authored_computes {input : Term} {target : Pattern} (lowered : Lowers input target) :
    Applies program host "re:compile-authored" [input] (RegexExtendedAccumulatorExecution.code (compile target)) := by
  refine Applies.equation (equation := program[41]) (environment := [("p", input)]) (by rfl) (by rfl) ?_
  exact call (by simp [Special]) (.cons (lower_variable (by rfl) (lower_computes lowered)) .nil)
    (RegexExtendedAccumulatorExecution.compileAcc_computes target)

theorem compile_authored_result_exact {input : Term} {target : Pattern} (lowered : Lowers input target)
    (result : Term) : Applies program host "re:compile-authored" [input] result ↔
      result = RegexExtendedAccumulatorExecution.code (compile target) := by
  constructor
  · exact fun computed => computed.deterministic (compile_authored_computes lowered)
  · rintro rfl; exact compile_authored_computes lowered

theorem compile_authored_completed {input : Term} {target : Pattern} (lowered : Lowers input target)
    (fuel : Nat) (finished : apply program host fuel "re:compile-authored" [input] ≠ .exhausted) :
    apply program host fuel "re:compile-authored" [input] =
      .value (RegexExtendedAccumulatorExecution.code (compile target)) :=
  (compile_authored_computes lowered).completed fuel finished

end Mettapedia.GSLT.LanguageDef.RegexExtendedLoweringExecution
