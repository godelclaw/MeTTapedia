import Mettapedia.GSLT.LanguageDef.RegexSelectionEquationExecution
import Mettapedia.GSLT.LanguageDef.RegexAccumulatorEquationExecution
import Mettapedia.GSLT.LanguageDef.RegexRepetitionLowering
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.ProgramExtension

/-!+# Executing authored source normalization and counted repetition

The source interpretation below is a structural judgment on inert data. It is
independent of equation evaluation and does not execute source subterms.
The extracted LanguageDef equations compute its target, then use the existing
symbolic graph compiler. Unsupported source data has no interpretation here;
this does not claim that no other interpretation can exist.
-/

set_option autoImplicit false
open scoped Computability

namespace Mettapedia.GSLT.LanguageDef.RegexSelection.RepetitionExecution

open DeterministicEquations EquationExecution
open RepetitionLowering

def count : Nat → Term
  | 0 => .sym "re:count-zero"
  | n + 1 => .expr [.sym "re:count-succ", count n]

theorem count_injective : Function.Injective count := by
  intro first second same
  induction first generalizing second with
  | zero => cases second <;> simp_all [count]
  | succ first ih =>
      cases second with
      | zero => simp [count] at same
      | succ second =>
          apply congrArg Nat.succ
          exact ih (by simpa [count] using same)

/-- Layout is observed on source data, before counts can erase executable work.
The identifiers retain their explicit payload representation. -/
def sourceGroups : Term → List Term
  | .expr [.sym "re:capture", group, body] => group :: sourceGroups body
  | .expr [.sym "re:seq", first, second] | .expr [.sym "re:alt", first, second] =>
      sourceGroups first ++ sourceGroups second
  | .expr [.sym "re:optional", body, _] | .expr [.sym "re:star", body, _]
  | .expr [.sym "re:plus", body, _] | .expr [.sym "re:repeat-exact", body, _]
  | .expr [.sym "re:repeat-at-least", body, _, _]
  | .expr [.sym "re:repeat-bounded", body, _, _, _] => sourceGroups body
  | _ => []

/-- Source lowering, not a definition in terms of running the compiler. -/
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
      Lowers (.expr [.sym "re:repeat-exact", input, count n]) (RepetitionLowering.exact body n)
  | atLeast {input : Term} {body : Pattern} (n : Nat) (greedy : Bool) : Lowers input body →
      Lowers (.expr [.sym "re:repeat-at-least", input, count n, preference greedy]) (atLeast body n greedy)
  | bounded {input : Term} {body : Pattern} (lower extra : Nat) (greedy : Bool) : Lowers input body →
      Lowers (.expr [.sym "re:repeat-bounded", input, count lower, count extra, preference greedy])
        (bounded body lower extra greedy)

theorem canonical_source_lowers (pattern : Pattern) : Lowers (source pattern) pattern := by
  induction pattern with
  | zero => exact .zero
  | epsilon => exact .epsilon
  | literal value => exact .literal value
  | any => exact .any
  | class_ values => exact .class_ values
  | assertion name => exact .assertion name
  | seq first second one two => exact .seq one two
  | alt first second one two => exact .alt one two
  | optional body greedy ih => exact .optional greedy ih
  | star body greedy ih => exact .star greedy ih
  | plus body greedy ih => exact .plus greedy ih
  | capture group body ih => exact .capture group ih

theorem canonical_source_groups (pattern : Pattern) :
    sourceGroups (source pattern) = (captureGroups pattern).map natural := by
  induction pattern <;> simp_all [source, sourceGroups, captureGroups]

/-- Count expansion never invents a group identity, even if some source
identities no longer have executable writes under a zero count. -/
theorem lowered_groups_declared {input : Term} {target : Pattern} (lowered : Lowers input target)
    (group : Nat) (member : group ∈ captureGroups target) : natural group ∈ sourceGroups input := by
  induction lowered with
  | zero | epsilon | literal _ | any | class_ _ | assertion _ => cases member
  | seq _ _ one two | alt _ _ one two =>
      simp only [captureGroups, List.mem_append] at member
      simp only [sourceGroups, List.mem_append]
      exact member.elim (fun h => Or.inl (one h)) (fun h => Or.inr (two h))
  | optional _ _ ih | star _ _ ih | plus _ _ ih => exact ih member
  | capture declared _ ih =>
      simp only [captureGroups, List.mem_cons] at member
      simp only [sourceGroups, List.mem_cons]
      exact member.elim (fun h => Or.inl (congrArg natural h)) (fun h => Or.inr (ih h))
  | exact n _ ih =>
      have permitted := prefix_no_new_group _ .epsilon n group member
      rcases permitted with fromBody | impossible
      · exact ih fromBody
      · cases impossible
  | atLeast n greedy _ ih => exact ih (atLeast_no_new_group _ n group greedy member)
  | bounded lower extra greedy _ ih => exact ih (bounded_no_new_group _ lower extra group greedy member)

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
    Applies program host "re:repeat-exact" [source body, count n] (source (RepetitionLowering.exact body n)) := by
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

theorem lower_result_exact {input : Term} {target : Pattern} (lowered : Lowers input target) (result : Term) :
    Applies program host "re:lower" [input] result ↔ result = source target := by
  constructor
  · exact fun computed => computed.deterministic (lower_computes lowered)
  · rintro rfl; exact lower_computes lowered

theorem compile_authored_computes {input : Term} {target : Pattern} (lowered : Lowers input target) :
    Applies program host "re:compile-authored" [input] (code (compile target)) := by
  refine Applies.equation (equation := program[41]) (environment := [("p", input)]) (by rfl) (by rfl) ?_
  exact call (by simp [Special]) (.cons (lower_variable (by rfl) (lower_computes lowered)) .nil)
    (AccumulatorExecution.compileAcc_computes target)

theorem compile_authored_result_exact {input : Term} {target : Pattern} (lowered : Lowers input target)
    (result : Term) : Applies program host "re:compile-authored" [input] result ↔ result = code (compile target) := by
  constructor
  · exact fun computed => computed.deterministic (compile_authored_computes lowered)
  · rintro rfl; exact compile_authored_computes lowered

theorem compile_authored_completed {input : Term} {target : Pattern} (lowered : Lowers input target)
    (fuel : Nat) (finished : apply program host fuel "re:compile-authored" [input] ≠ .exhausted) :
    apply program host fuel "re:compile-authored" [input] = .value (code (compile target)) :=
  (compile_authored_computes lowered).completed fuel finished

def legacyProgram : DeterministicEquations.Program := program.take 18
def countExtension : DeterministicEquations.Program := program.drop 18

theorem count_extension_disjoint :
    ∀ equation ∈ countExtension, equation.head ∉ legacyProgram.calledHeads := by decide

/-- The extension preserves every old direct-call outcome at every fuel,
including refusal and exhaustion, not merely recognition. -/
theorem legacy_outcomes_unchanged (fuel : Nat) (head : String)
    (used : head ∈ legacyProgram.calledHeads) (arguments : List Term) :
    apply program host fuel head arguments = apply legacyProgram host fuel head arguments := by
  have split : legacyProgram ++ countExtension = program := List.take_append_drop 18 program
  simpa only [split] using apply_append_eq legacyProgram countExtension host count_extension_disjoint
    fuel head used arguments

open Mettapedia.Computability.RegularLanguages

private theorem graph_recognition_of_language (pattern : Pattern) (L : Language Nat)
    (meaning : language? pattern = some L) (word : List Nat) :
    Recognition.Path (compile pattern).rows .root word .ending ↔ word ∈ L := by
  have agrees := erase_language pattern
  cases erased : erase? pattern with
  | none => simp [erased, meaning] at agrees
  | some regex =>
      have equal : language regex = L := by simpa [erased, meaning] using agrees
      simpa only [equal, compile] using Recognition.compile_recognition_iff pattern regex erased word

/-- The actual emitted graph, reached by the authored count equations, accepts
exactly the independent inclusive factor-count semantics. -/
theorem bounded_graph_recognition (body : Pattern) (lower extra : Nat) (greedy : Bool)
    (regex : Regex Nat) (erased : erase? body = some regex) (word : List Nat) :
    Recognition.Path (compile (bounded body lower extra greedy)).rows .root word .ending ↔
      ∃ count, lower ≤ count ∧ count ≤ lower + extra ∧ word ∈ language regex ^ count := by
  have bodyMeaning : language? body = some (language regex) := by
    simpa [erased] using (erase_language body).symm
  exact (graph_recognition_of_language _ _ (language_bounded body lower extra greedy regex bodyMeaning) word).trans
    (mem_language_boundedRepeat regex lower (lower + extra) word)

theorem atLeast_graph_recognition (body : Pattern) (minimum : Nat) (greedy : Bool)
    (regex : Regex Nat) (erased : erase? body = some regex) (word : List Nat) :
    Recognition.Path (compile (atLeast body minimum greedy)).rows .root word .ending ↔
      word ∈ language regex ^ minimum * (language regex)∗ := by
  have bodyMeaning : language? body = some (language regex) := by
    simpa [erased] using (erase_language body).symm
  exact graph_recognition_of_language _ _ (language_atLeast body minimum greedy regex bodyMeaning) word

namespace Controls

/-- Payload validation is a later boundary. Normalization does not execute
even a call-shaped value stored in a literal payload position. -/
theorem literal_payload_remains_inert (payload : Term) :
    Applies program host "re:lower" [.expr [.sym "re:literal", payload]]
      (.expr [.sym "re:literal", payload]) := by
  refine Applies.equation (equation := program[28]) (environment := [("a", payload)]) (by rfl) (by rfl) ?_
  exact node1 (by rfl) (by simp [Special]) (.variable (by rfl))

theorem authored_nullable_one_or_more_is_plus :
    Applies program host "re:compile-authored"
      [.expr [.sym "re:repeat-at-least", source (.capture 1 (.alt (.literal 97) .epsilon)), count 1, preference true]]
      (code (compile (.plus (.capture 1 (.alt (.literal 97) .epsilon)) true))) :=
  compile_authored_computes (.atLeast 1 true (canonical_source_lowers _))

theorem authored_nested_counts_run :
    Applies program host "re:compile-authored"
      [.expr [.sym "re:repeat-bounded", .expr [.sym "re:repeat-exact", source (.capture 2 (.literal 97)), count 2],
        count 1, count 2, preference false]]
      (code (compile (bounded (RepetitionLowering.exact (.capture 2 (.literal 97)) 2) 1 2 false))) :=
  compile_authored_computes (.bounded 1 2 false (.exact 2 (canonical_source_lowers _)))

theorem authored_zero_count_compiles_epsilon :
    Applies program host "re:compile-authored"
      [.expr [.sym "re:repeat-exact", source (.capture 3 (.literal 97)), count 0]]
      (code (compile .epsilon)) :=
  compile_authored_computes (.exact 0 (canonical_source_lowers _))

theorem nested_zero_count_retains_source_group :
    sourceGroups (.expr [.sym "re:repeat-at-least", .expr [.sym "re:repeat-exact",
      source (.capture 3 (.literal 97)), count 0], count 1, preference true]) = [natural 3] := rfl

theorem decimal_atom_is_not_a_peano_count (body : Pattern) (target : Pattern) :
    ¬ Lowers (.expr [.sym "re:repeat-exact", source body, .lit "1"]) target := by
  intro lowered
  have notCount (n : Nat) : (.lit "1" : Term) ≠ count n := by cases n <;> simp [count]
  generalize shape : (.expr [.sym "re:repeat-exact", source body, .lit "1"] : Term) = input at lowered
  cases lowered <;> simp_all [Term.expr.injEq, List.cons.injEq]

theorem authored_lowering_cannot_invent_empty_graph :
    ¬ Applies program host "re:compile-authored"
      [.expr [.sym "re:repeat-at-least", source (.capture 1 (.alt (.literal 97) .epsilon)), count 1, preference true]]
      (code (compile .epsilon)) := by
  intro computed
  have equal := computed.deterministic authored_nullable_one_or_more_is_plus
  cases equal

end Controls
end Mettapedia.GSLT.LanguageDef.RegexSelection.RepetitionExecution
