import Mettapedia.GSLT.LanguageDef.RegexExtendedEquationExecution

/-!
# Executing the authored tail-threaded regex emitter

The actual extracted equation program computes the independently structural
accumulator emitter. Equality with the original ordered rows then preserves
the entire graph. This establishes result refinement, not a native cost bound
or equality of intermediate fuel consumption between the two compilers.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexExtendedAccumulatorExecution

open DeterministicEquations RegexExtendedEquationExecution RegexExtendedCompilerSemantics

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

private theorem node3 {environment : Env} {head : String}
    {first second third firstValue secondValue thirdValue : Term}
    (undefined : program.defines head = false) (ordinary : ¬ Special head [first, second, third])
    (one : Evaluates program host environment first firstValue)
    (two : Evaluates program host environment second secondValue)
    (three : Evaluates program host environment third thirdValue) :
    Evaluates program host environment (.expr [.sym head, first, second, third])
      (.expr [.sym head, firstValue, secondValue, thirdValue]) :=
  call ordinary (.cons one (.cons two (.cons three .nil))) (.constructor undefined rfl)

private theorem node4 {environment : Env} {head : String}
    {first second third fourth firstValue secondValue thirdValue fourthValue : Term}
    (undefined : program.defines head = false) (ordinary : ¬ Special head [first, second, third, fourth])
    (one : Evaluates program host environment first firstValue)
    (two : Evaluates program host environment second secondValue)
    (three : Evaluates program host environment third thirdValue)
    (four : Evaluates program host environment fourth fourthValue) :
    Evaluates program host environment (.expr [.sym head, first, second, third, fourth])
      (.expr [.sym head, firstValue, secondValue, thirdValue, fourthValue]) :=
  call ordinary (.cons one (.cons two (.cons three (.cons four .nil)))) (.constructor undefined rfl)

set_option maxHeartbeats 2000000 in
theorem emitAcc_computes (pattern : Pattern) (continuation origin : Address) (tail : List Instruction) :
    Applies program host "re:emit-acc" [source pattern, address continuation, address origin, rows tail]
      (rows (emitAcc pattern continuation origin tail)) := by
  induction pattern generalizing continuation origin tail with
  | zero =>
      refine Applies.equation (equation := program[43])
        (environment := [("k", address continuation), ("at", address origin), ("tail", rows tail)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.variable (by rfl))
  | epsilon =>
      refine Applies.equation (equation := program[44])
        (environment := [("k", address continuation), ("at", address origin), ("tail", rows tail)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (node2 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))) (.variable (by rfl))
  | literal value =>
      refine Applies.equation (equation := program[45])
        (environment := [("a", natural value), ("k", address continuation), ("at", address origin),
          ("tail", rows tail)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (node3 (by rfl) (by simp [Special]) (.variable (by rfl))
          (.variable (by rfl)) (.variable (by rfl))) (.variable (by rfl))
  | any =>
      refine Applies.equation (equation := program[46])
        (environment := [("k", address continuation), ("at", address origin), ("tail", rows tail)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (node2 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))) (.variable (by rfl))
  | class_ values =>
      refine Applies.equation (equation := program[47])
        (environment := [("ranges", ranges values), ("k", address continuation), ("at", address origin),
          ("tail", rows tail)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (node3 (by rfl) (by simp [Special]) (.variable (by rfl))
          (.variable (by rfl)) (.variable (by rfl))) (.variable (by rfl))
  | assertion name =>
      refine Applies.equation (equation := program[48])
        (environment := [("which", .lit name), ("k", address continuation), ("at", address origin),
          ("tail", rows tail)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (node3 (by rfl) (by simp [Special]) (.variable (by rfl))
          (.variable (by rfl)) (.variable (by rfl))) (.variable (by rfl))
  | seq first second ihFirst ihSecond =>
      let environment : Env := [("p", source first), ("q", source second),
        ("k", address continuation), ("at", address origin), ("tail", rows tail)]
      refine Applies.equation (equation := program[49]) (environment := environment) (by rfl) (by rfl) ?_
      have secondRuns : Evaluates program host environment
          (.expr [.sym "re:emit-acc", .var "q", .var "k", .expr [.sym "re:right", .var "at"], .var "tail"])
          (rows (emitAcc second continuation (.right origin) tail)) :=
        call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.cons (.variable (by rfl)) .nil)))) (ihSecond continuation (.right origin) tail)
      have firstRuns : Evaluates program host environment
          (.expr [.sym "re:emit-acc", .var "p", .expr [.sym "re:right", .var "at"],
            .expr [.sym "re:left", .var "at"],
            .expr [.sym "re:emit-acc", .var "q", .var "k", .expr [.sym "re:right", .var "at"], .var "tail"]])
          (rows (emitAcc first (.right origin) (.left origin) (emitAcc second continuation (.right origin) tail))) :=
        call (by simp [Special]) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.cons secondRuns .nil))))
          (ihFirst (.right origin) (.left origin) (emitAcc second continuation (.right origin) tail))
      exact node2 (by rfl) (by simp [Special])
        (node2 (by rfl) (by simp [Special]) (.variable (by rfl))
          (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))) firstRuns
  | alt first second ihFirst ihSecond =>
      let environment : Env := [("p", source first), ("q", source second),
        ("k", address continuation), ("at", address origin), ("tail", rows tail)]
      refine Applies.equation (equation := program[50]) (environment := environment) (by rfl) (by rfl) ?_
      have secondRuns : Evaluates program host environment
          (.expr [.sym "re:emit-acc", .var "q", .var "k", .expr [.sym "re:right", .var "at"], .var "tail"])
          (rows (emitAcc second continuation (.right origin) tail)) :=
        call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.cons (.variable (by rfl)) .nil)))) (ihSecond continuation (.right origin) tail)
      have firstRuns : Evaluates program host environment
          (.expr [.sym "re:emit-acc", .var "p", .var "k", .expr [.sym "re:left", .var "at"],
            .expr [.sym "re:emit-acc", .var "q", .var "k", .expr [.sym "re:right", .var "at"], .var "tail"]])
          (rows (emitAcc first continuation (.left origin) (emitAcc second continuation (.right origin) tail))) :=
        call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.cons secondRuns .nil))))
          (ihFirst continuation (.left origin) (emitAcc second continuation (.right origin) tail))
      exact node2 (by rfl) (by simp [Special])
        (node3 (by rfl) (by simp [Special]) (.variable (by rfl))
          (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
          (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))) firstRuns
  | optional body greedy ih =>
      let environment : Env := [("p", source body), ("k", address continuation),
        ("at", address origin), ("tail", rows tail)]
      have bodyRuns : Evaluates program host environment
          (.expr [.sym "re:emit-acc", .var "p", .var "k", .expr [.sym "re:body", .var "at"], .var "tail"])
          (rows (emitAcc body continuation (.body origin) tail)) :=
        call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.cons (.variable (by rfl)) .nil)))) (ih continuation (.body origin) tail)
      cases greedy with
      | false =>
          refine Applies.equation (equation := program[52]) (environment := environment) (by rfl) (by rfl) ?_
          exact node2 (by rfl) (by simp [Special])
            (node3 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))
              (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))) bodyRuns
      | true =>
          refine Applies.equation (equation := program[51]) (environment := environment) (by rfl) (by rfl) ?_
          exact node2 (by rfl) (by simp [Special])
            (node3 (by rfl) (by simp [Special]) (.variable (by rfl))
              (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.variable (by rfl))) bodyRuns
  | star body greedy ih =>
      let environment : Env := [("p", source body), ("k", address continuation),
        ("at", address origin), ("tail", rows tail)]
      have bodyRuns : Evaluates program host environment
          (.expr [.sym "re:emit-acc", .var "p", .expr [.sym "re:loop", .var "at"],
            .expr [.sym "re:body", .var "at"], .var "tail"])
          (rows (emitAcc body (.loop origin) (.body origin) tail)) :=
        call (by simp [Special]) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
              (.cons (.variable (by rfl)) .nil)))) (ih (.loop origin) (.body origin) tail)
      cases greedy with
      | false =>
          refine Applies.equation (equation := program[54]) (environment := environment) (by rfl) (by rfl) ?_
          exact node2 (by rfl) (by simp [Special])
            (node3 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))
              (node1 (by rfl) (by simp [Special]) (.variable (by rfl))))
            (node2 (by rfl) (by simp [Special])
              (node3 (by rfl) (by simp [Special])
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.variable (by rfl))
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))) bodyRuns)
      | true =>
          refine Applies.equation (equation := program[53]) (environment := environment) (by rfl) (by rfl) ?_
          exact node2 (by rfl) (by simp [Special])
            (node3 (by rfl) (by simp [Special]) (.variable (by rfl))
              (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.variable (by rfl)))
            (node2 (by rfl) (by simp [Special])
              (node3 (by rfl) (by simp [Special])
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.variable (by rfl))) bodyRuns)
  | plus body greedy ih =>
      let environment : Env := [("p", source body), ("k", address continuation),
        ("at", address origin), ("tail", rows tail)]
      have bodyRuns : Evaluates program host environment
          (.expr [.sym "re:emit-acc", .var "p", .expr [.sym "re:loop", .var "at"],
            .expr [.sym "re:body", .var "at"], .var "tail"])
          (rows (emitAcc body (.loop origin) (.body origin) tail)) :=
        call (by simp [Special]) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
              (.cons (.variable (by rfl)) .nil)))) (ih (.loop origin) (.body origin) tail)
      cases greedy with
      | false =>
          refine Applies.equation (equation := program[56]) (environment := environment) (by rfl) (by rfl) ?_
          exact node2 (by rfl) (by simp [Special])
            (node2 (by rfl) (by simp [Special]) (.variable (by rfl))
              (node1 (by rfl) (by simp [Special]) (.variable (by rfl))))
            (node2 (by rfl) (by simp [Special])
              (node3 (by rfl) (by simp [Special])
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.variable (by rfl))
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))) bodyRuns)
      | true =>
          refine Applies.equation (equation := program[55]) (environment := environment) (by rfl) (by rfl) ?_
          exact node2 (by rfl) (by simp [Special])
            (node2 (by rfl) (by simp [Special]) (.variable (by rfl))
              (node1 (by rfl) (by simp [Special]) (.variable (by rfl))))
            (node2 (by rfl) (by simp [Special])
              (node3 (by rfl) (by simp [Special])
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.variable (by rfl))) bodyRuns)
  | capture group body ih =>
      let environment : Env := [("g", natural group), ("p", source body), ("k", address continuation),
        ("at", address origin), ("tail", rows tail)]
      refine Applies.equation (equation := program[57]) (environment := environment) (by rfl) (by rfl) ?_
      have bodyRuns : Evaluates program host environment
          (.expr [.sym "re:emit-acc", .var "p", .expr [.sym "re:close", .var "at"],
            .expr [.sym "re:body", .var "at"], .var "tail"])
          (rows (emitAcc body (.close origin) (.body origin) tail)) :=
        call (by simp [Special]) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
              (.cons (.variable (by rfl)) .nil)))) (ih (.close origin) (.body origin) tail)
      exact node2 (by rfl) (by simp [Special])
        (node4 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))
          (.symbol program host _ _) (node1 (by rfl) (by simp [Special]) (.variable (by rfl))))
        (node2 (by rfl) (by simp [Special])
          (node4 (by rfl) (by simp [Special])
            (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.variable (by rfl)) (.symbol program host _ _) (.variable (by rfl))) bodyRuns)


  | backref group mode =>
      let environment : Env := [("g", natural group), ("mode", comparison mode),
        ("k", address continuation), ("at", address origin), ("tail", rows tail)]
      refine Applies.equation (equation := program[59]) (environment := environment) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (node4 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))
          (.variable (by rfl)) (.variable (by rfl))) (.variable (by rfl))
  | look which body ih =>
      let environment : Env := [("p", source body), ("k", address continuation),
        ("at", address origin), ("tail", rows tail)]
      have bodyRuns : Evaluates program host environment
          (.expr [.sym "re:emit-acc", .var "p", .expr [.sym "re:look-end", .var "at"],
            .expr [.sym "re:look-body", .var "at"], .var "tail"])
          (rows (emitAcc body (.lookEnd origin) (.lookBody origin) tail)) :=
        call (by simp [Special]) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
              (.cons (.variable (by rfl)) .nil))))
          (ih (.lookEnd origin) (.lookBody origin) tail)
      cases which
      all_goals first
        | refine Applies.equation (equation := program[66]) (environment := environment) (by rfl) (by rfl) ?_
        | refine Applies.equation (equation := program[67]) (environment := environment) (by rfl) (by rfl) ?_
        | refine Applies.equation (equation := program[68]) (environment := environment) (by rfl) (by rfl) ?_
        | refine Applies.equation (equation := program[69]) (environment := environment) (by rfl) (by rfl) ?_
        | refine Applies.equation (equation := program[70]) (environment := environment) (by rfl) (by rfl) ?_
        | refine Applies.equation (equation := program[71]) (environment := environment) (by rfl) (by rfl) ?_
      all_goals
        exact node2 (by rfl) (by simp [Special])
          (node4 (by rfl) (by simp [Special]) (.variable (by rfl))
            (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.symbol program host _ _) (.variable (by rfl)))
          (node2 (by rfl) (by simp [Special])
            (node1 (by rfl) (by simp [Special])
              (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))) bodyRuns)

theorem emitAcc_result_exact (pattern : Pattern) (continuation origin : Address)
    (tail : List Instruction) (result : Term) :
    Applies program host "re:emit-acc" [source pattern, address continuation, address origin, rows tail] result ↔
      result = rows (emit pattern continuation origin ++ tail) := by
  constructor
  · intro computed
    simpa only [emitAcc_eq] using computed.deterministic (emitAcc_computes pattern continuation origin tail)
  · rintro rfl
    simpa only [emitAcc_eq] using emitAcc_computes pattern continuation origin tail

def code (compiled : RegexExtendedCompilerSemantics.Program) : Term :=
  .expr [.sym "re:code", address compiled.entry, rows compiled.rows]

theorem compileAcc_computes (pattern : Pattern) :
    Applies program host "re:compile-acc" [source pattern] (code (compile pattern)) := by
  refine Applies.equation (equation := program[42]) (environment := [("p", source pattern)]) (by rfl) (by rfl) ?_
  have emitted : Evaluates program host [("p", source pattern)]
      (.expr [.sym "re:emit-acc", .var "p", .sym "re:end", .sym "re:root", .sym "LNil"])
      (rows (emitAcc pattern .ending .root [])) :=
    call (by simp [Special]) (.cons (.variable (by rfl))
      (.cons (.symbol program host _ _) (.cons (.symbol program host _ _)
        (.cons (.symbol program host _ _) .nil)))) (emitAcc_computes pattern .ending .root [])
  have result : Evaluates program host [("p", source pattern)] program[42].body
      (code (compileAcc pattern)) :=
    node2 (head := "re:code") (by rfl) (by simp [Special]) (.symbol program host _ "re:root")
    (node2 (head := "LCons") (by rfl) (by simp [Special])
      (node1 (head := "re:match") (by rfl) (by simp [Special]) (.symbol program host _ "re:end")) emitted)
  simpa only [compileAcc_eq] using result

theorem compileAcc_result_exact (pattern : Pattern) (result : Term) :
    Applies program host "re:compile-acc" [source pattern] result ↔ result = code (compile pattern) := by
  constructor
  · exact fun computed => computed.deterministic (compileAcc_computes pattern)
  · rintro rfl; exact compileAcc_computes pattern

end Mettapedia.GSLT.LanguageDef.RegexExtendedAccumulatorExecution

