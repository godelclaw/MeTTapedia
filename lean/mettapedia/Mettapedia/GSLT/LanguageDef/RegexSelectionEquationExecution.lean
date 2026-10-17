import Mettapedia.GSLT.LanguageDef.ModuleFormat.RegexSelectionAuthoring
import Mettapedia.GSLT.LanguageDef.DeterministicEquations.Computation

/-!
# Executing the authored selection compiler equations

The program below is extracted from the actual finite LanguageDef equation
list. The existing fuelled deterministic-equation evaluator supplies its
operational interpretation. A separately structural symbolic emitter supplies
the result specification; it is not the definition of equation evaluation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.RegexSelection.EquationExecution


mutual
  /-- The admitted first-order equation schema has no hidden binder erasure. -/
  def term? : Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Option DeterministicEquations.Term
    | .fvar variableName => some (.var variableName)
    | .apply head [] => some (.sym head)
    | .apply head arguments => do return .expr (.sym head :: (← terms? arguments))
    | _ => none

  def terms? : List Mettapedia.OSLF.MeTTaIL.Syntax.Pattern → Option (List DeterministicEquations.Term)
    | [] => some []
    | first :: rest => do return (← term? first) :: (← terms? rest)
end

def equation? (equation : Mettapedia.OSLF.MeTTaIL.Syntax.Equation) : Option DeterministicEquations.Equation := do
  if !equation.premises.isEmpty || equation.bindings.isSome then none else do
    match equation.left with
    | .apply head arguments =>
        return ⟨equation.name, head, ← terms? arguments, ← term? equation.right⟩
    | _ => none

def program : DeterministicEquations.Program := (ModuleFormat.RegexSelectionAuthoring.theory.equations.mapM equation?).getD []

set_option maxRecDepth 4096 in
/-- Extraction succeeds on every actual authored equation, in its declared order. -/
theorem program_extraction_exact : ModuleFormat.RegexSelectionAuthoring.theory.equations.mapM equation? = some program := rfl

def host : DeterministicEquations.Host := ⟨fun _ _ => .unhandled⟩

def natural (value : Nat) : DeterministicEquations.Term := .lit (Nat.repr value)

def address : Address → DeterministicEquations.Term
  | .root => .sym "re:root"
  | .ending => .sym "re:end"
  | .left parent => .expr [.sym "re:left", address parent]
  | .right parent => .expr [.sym "re:right", address parent]
  | .body parent => .expr [.sym "re:body", address parent]
  | .loop parent => .expr [.sym "re:loop", address parent]
  | .close parent => .expr [.sym "re:close", address parent]

def list (items : List DeterministicEquations.Term) : DeterministicEquations.Term :=
  items.foldr (fun first rest => .expr [.sym "LCons", first, rest]) (.sym "LNil")

def ranges (items : List ScalarRange) : DeterministicEquations.Term :=
  list (items.map fun range => .expr [.sym "re:range", natural range.1, natural range.2])

def preference (greedy : Bool) : DeterministicEquations.Term := .sym (if greedy then "Greedy" else "Lazy")

def source : Pattern → DeterministicEquations.Term
  | .zero => .sym "re:zero"
  | .epsilon => .sym "re:epsilon"
  | .literal value => .expr [.sym "re:literal", natural value]
  | .any => .sym "re:any"
  | .class_ values => .expr [.sym "re:class", ranges values]
  | .assertion name => .expr [.sym "re:assert", .lit name]
  | .seq first second => .expr [.sym "re:seq", source first, source second]
  | .alt first second => .expr [.sym "re:alt", source first, source second]
  | .optional body greedy => .expr [.sym "re:optional", source body, preference greedy]
  | .star body greedy => .expr [.sym "re:star", source body, preference greedy]
  | .plus body greedy => .expr [.sym "re:plus", source body, preference greedy]
  | .capture group body => .expr [.sym "re:capture", natural group, source body]

def boundary : Boundary → DeterministicEquations.Term
  | .start => .sym "Start"
  | .finish => .sym "End"

def instruction : Instruction → DeterministicEquations.Term
  | .fail origin => .expr [.sym "re:fail", address origin]
  | .accept origin => .expr [.sym "re:match", address origin]
  | .jump origin next => .expr [.sym "re:jump", address origin, address next]
  | .scalar origin value next => .expr [.sym "re:char", address origin, natural value, address next]
  | .any origin next => .expr [.sym "re:any-at", address origin, address next]
  | .class_ origin values next => .expr [.sym "re:class-at", address origin, ranges values, address next]
  | .split origin first second => .expr [.sym "re:split", address origin, address first, address second]
  | .save origin group edge next => .expr [.sym "re:save", address origin, natural group, boundary edge, address next]
  | .assertion origin name next => .expr [.sym "re:assert-at", address origin, .lit name, address next]

def rows (instructions : List Instruction) : DeterministicEquations.Term := list (instructions.map instruction)

private theorem constructor {environment : DeterministicEquations.Env} {head : String}
    {arguments values : List DeterministicEquations.Term}
    (undefined : program.defines head = false)
    (ordinary : ¬ DeterministicEquations.Special head arguments)
    (children : List.Forall₂ (DeterministicEquations.Evaluates program host environment) arguments values) :
    DeterministicEquations.Evaluates program host environment (.expr (.sym head :: arguments))
      (.expr (.sym head :: values)) :=
  DeterministicEquations.Evaluates.call ordinary children (DeterministicEquations.Applies.constructor undefined rfl)

private theorem call {environment : DeterministicEquations.Env} {head : String}
    {arguments values : List DeterministicEquations.Term} {result : DeterministicEquations.Term}
    (ordinary : ¬ DeterministicEquations.Special head arguments)
    (children : List.Forall₂ (DeterministicEquations.Evaluates program host environment) arguments values)
    (operation : DeterministicEquations.Applies program host head values result) :
    DeterministicEquations.Evaluates program host environment (.expr (.sym head :: arguments)) result :=
  DeterministicEquations.Evaluates.call ordinary children operation

private theorem append_computes (first second : List DeterministicEquations.Term) :
    DeterministicEquations.Applies program host "re:append" [list first, list second] (list (first ++ second)) := by
  induction first with
  | nil =>
      refine DeterministicEquations.Applies.equation (equation := program[1])
        (environment := [("tail", list second)]) (by rfl) (by rfl) ?_
      exact DeterministicEquations.Evaluates.variable (by rfl)
  | cons first rest ih =>
      refine DeterministicEquations.Applies.equation (equation := program[2])
        (environment := [("h", first), ("t", list rest), ("tail", list second)]) (by rfl) (by rfl) ?_
      refine constructor (by rfl) (by simp [DeterministicEquations.Special]) (.cons ?_ (.cons ?_ .nil))
      · exact DeterministicEquations.Evaluates.variable (by rfl)
      · exact call (by simp [DeterministicEquations.Special])
          (.cons (.variable (by rfl)) (.cons (.variable (by rfl)) .nil)) ih

theorem append_result_exact (first second : List DeterministicEquations.Term) (result : DeterministicEquations.Term) :
    DeterministicEquations.Applies program host "re:append" [list first, list second] result ↔
      result = list (first ++ second) := by
  constructor
  · exact fun evaluated => evaluated.deterministic (append_computes first second)
  · rintro rfl
    exact append_computes first second

open DeterministicEquations

private theorem node1 {environment : Env} {head : String} {first firstValue : Term}
    (undefined : program.defines head = false) (ordinary : ¬ Special head [first])
    (one : Evaluates program host environment first firstValue) :
    Evaluates program host environment (.expr [.sym head, first]) (.expr [.sym head, firstValue]) :=
  constructor undefined ordinary (.cons one .nil)

private theorem node2 {environment : Env} {head : String} {first second firstValue secondValue : Term}
    (undefined : program.defines head = false) (ordinary : ¬ Special head [first, second])
    (one : Evaluates program host environment first firstValue)
    (two : Evaluates program host environment second secondValue) :
    Evaluates program host environment (.expr [.sym head, first, second])
      (.expr [.sym head, firstValue, secondValue]) :=
  constructor undefined ordinary (.cons one (.cons two .nil))

private theorem node3 {environment : Env} {head : String}
    {first second third firstValue secondValue thirdValue : Term}
    (undefined : program.defines head = false) (ordinary : ¬ Special head [first, second, third])
    (one : Evaluates program host environment first firstValue)
    (two : Evaluates program host environment second secondValue)
    (three : Evaluates program host environment third thirdValue) :
    Evaluates program host environment (.expr [.sym head, first, second, third])
      (.expr [.sym head, firstValue, secondValue, thirdValue]) :=
  constructor undefined ordinary (.cons one (.cons two (.cons three .nil)))

private theorem node4 {environment : Env} {head : String}
    {first second third fourth firstValue secondValue thirdValue fourthValue : Term}
    (undefined : program.defines head = false) (ordinary : ¬ Special head [first, second, third, fourth])
    (one : Evaluates program host environment first firstValue)
    (two : Evaluates program host environment second secondValue)
    (three : Evaluates program host environment third thirdValue)
    (four : Evaluates program host environment fourth fourthValue) :
    Evaluates program host environment (.expr [.sym head, first, second, third, fourth])
      (.expr [.sym head, firstValue, secondValue, thirdValue, fourthValue]) :=
  constructor undefined ordinary (.cons one (.cons two (.cons three (.cons four .nil))))

/-- All canonical source patterns execute through the actual extracted
equations to the independently specified emitter, including capture writes
and the two distinct nullable-loop choices. -/
theorem emit_computes (pattern : Pattern) (continuation origin : Address) :
    Applies program host "re:emit" [source pattern, address continuation, address origin]
      (rows (emit pattern continuation origin)) := by
  induction pattern generalizing continuation origin with
  | zero =>
      refine Applies.equation (equation := program[3])
        (environment := [("k", address continuation), ("at", address origin)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
        (.symbol program host _ _)
  | epsilon =>
      refine Applies.equation (equation := program[4])
        (environment := [("k", address continuation), ("at", address origin)]) (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (node2 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl)))
        (.symbol program host _ _)
  | literal value =>
      refine Applies.equation (equation := program[5])
        (environment := [("a", natural value), ("k", address continuation), ("at", address origin)])
        (by rfl) (by rfl) ?_
      exact node2 (by rfl) (by simp [Special])
        (node3 (by rfl) (by simp [Special]) (.variable (by rfl))
          (.variable (by rfl)) (.variable (by rfl))) (.symbol program host _ _)
  | any =>
      refine Applies.equation (equation := program[6])
        (environment := [("k", address continuation), ("at", address origin)]) (by rfl) (by rfl) ?_
      change Evaluates program host [("k", address continuation), ("at", address origin)]
        (.expr [.sym "LCons", .expr [.sym "re:any-at", .var "at", .var "k"], .sym "LNil"])
        (.expr [.sym "LCons", .expr [.sym "re:any-at", address origin, address continuation], .sym "LNil"])
      exact node2 (by rfl) (by simp [Special])
        (node2 (head := "re:any-at") (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl)))
        (.symbol program host _ _)
  | class_ values =>
      refine Applies.equation (equation := program[7])
        (environment := [("ranges", ranges values), ("k", address continuation), ("at", address origin)])
        (by rfl) (by rfl) ?_
      change Evaluates program host [("ranges", ranges values), ("k", address continuation), ("at", address origin)]
        (.expr [.sym "LCons", .expr [.sym "re:class-at", .var "at", .var "ranges", .var "k"], .sym "LNil"])
        (.expr [.sym "LCons", .expr [.sym "re:class-at", address origin, ranges values, address continuation], .sym "LNil"])
      exact node2 (by rfl) (by simp [Special])
        (node3 (head := "re:class-at") (by rfl) (by simp [Special]) (.variable (by rfl))
          (.variable (by rfl)) (.variable (by rfl))) (.symbol program host _ _)
  | assertion name =>
      refine Applies.equation (equation := program[8])
        (environment := [("which", .lit name), ("k", address continuation), ("at", address origin)])
        (by rfl) (by rfl) ?_
      change Evaluates program host [("which", .lit name), ("k", address continuation), ("at", address origin)]
        (.expr [.sym "LCons", .expr [.sym "re:assert-at", .var "at", .var "which", .var "k"], .sym "LNil"])
        (.expr [.sym "LCons", .expr [.sym "re:assert-at", address origin, .lit name, address continuation], .sym "LNil"])
      exact node2 (by rfl) (by simp [Special])
        (node3 (head := "re:assert-at") (by rfl) (by simp [Special]) (.variable (by rfl))
          (.variable (by rfl)) (.variable (by rfl))) (.symbol program host _ _)
  | seq first second ihFirst ihSecond =>
      let environment : Env := [("p", source first), ("q", source second),
        ("k", address continuation), ("at", address origin)]
      refine Applies.equation (equation := program[9]) (environment := environment) (by rfl) (by rfl) ?_
      change Evaluates program host environment
        (.expr [.sym "LCons", .expr [.sym "re:jump", .var "at", .expr [.sym "re:left", .var "at"]],
          .expr [.sym "re:append", .expr [.sym "re:emit", .var "p", .expr [.sym "re:right", .var "at"],
            .expr [.sym "re:left", .var "at"]], .expr [.sym "re:emit", .var "q", .var "k",
              .expr [.sym "re:right", .var "at"]]]]) (rows (emit (.seq first second) continuation origin))
      have firstRuns : Evaluates program host environment
          (.expr [.sym "re:emit", .var "p", .expr [.sym "re:right", .var "at"],
            .expr [.sym "re:left", .var "at"]])
          (rows (emit first (.right origin) (.left origin))) :=
        call (by simp [Special])
          (.cons (.variable (by rfl))
            (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
              (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) .nil)))
          (ihFirst (.right origin) (.left origin))
      have secondRuns : Evaluates program host environment
          (.expr [.sym "re:emit", .var "q", .var "k", .expr [.sym "re:right", .var "at"]])
          (rows (emit second continuation (.right origin))) :=
        call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) .nil)))
          (ihSecond continuation (.right origin))
      have joined := call (head := "re:append") (by simp [Special]) (.cons firstRuns (.cons secondRuns .nil))
        (append_computes ((emit first (.right origin) (.left origin)).map instruction)
          ((emit second continuation (.right origin)).map instruction))
      simpa only [emit, rows, List.map_cons, List.map_append, list, List.foldr_cons, instruction, address] using
        node2 (head := "LCons") (by rfl) (by simp [Special])
          (node2 (head := "re:jump") (by rfl) (by simp [Special]) (.variable (name := "at") (by rfl))
            (node1 (head := "re:left") (by rfl) (by simp [Special]) (.variable (name := "at") (by rfl)))) joined
  | alt first second ihFirst ihSecond =>
      let environment : Env := [("p", source first), ("q", source second),
        ("k", address continuation), ("at", address origin)]
      refine Applies.equation (equation := program[10]) (environment := environment) (by rfl) (by rfl) ?_
      change Evaluates program host environment
        (.expr [.sym "LCons", .expr [.sym "re:split", .var "at", .expr [.sym "re:left", .var "at"],
          .expr [.sym "re:right", .var "at"]], .expr [.sym "re:append",
            .expr [.sym "re:emit", .var "p", .var "k", .expr [.sym "re:left", .var "at"]],
            .expr [.sym "re:emit", .var "q", .var "k", .expr [.sym "re:right", .var "at"]]]])
        (rows (emit (.alt first second) continuation origin))
      have firstRuns : Evaluates program host environment
          (.expr [.sym "re:emit", .var "p", .var "k", .expr [.sym "re:left", .var "at"]])
          (rows (emit first continuation (.left origin))) :=
        call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) .nil)))
          (ihFirst continuation (.left origin))
      have secondRuns : Evaluates program host environment
          (.expr [.sym "re:emit", .var "q", .var "k", .expr [.sym "re:right", .var "at"]])
          (rows (emit second continuation (.right origin))) :=
        call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) .nil)))
          (ihSecond continuation (.right origin))
      have joined := call (head := "re:append") (by simp [Special]) (.cons firstRuns (.cons secondRuns .nil))
        (append_computes ((emit first continuation (.left origin)).map instruction)
          ((emit second continuation (.right origin)).map instruction))
      simpa only [emit, rows, List.map_cons, List.map_append, list, List.foldr_cons, instruction, address] using
        node2 (head := "LCons") (by rfl) (by simp [Special])
          (node3 (head := "re:split") (by rfl) (by simp [Special]) (.variable (name := "at") (by rfl))
            (node1 (head := "re:left") (by rfl) (by simp [Special]) (.variable (name := "at") (by rfl)))
            (node1 (head := "re:right") (by rfl) (by simp [Special]) (.variable (name := "at") (by rfl)))) joined
  | optional body greedy ih =>
      let environment : Env := [("p", source body), ("k", address continuation), ("at", address origin)]
      have bodyRuns : Evaluates program host environment
          (.expr [.sym "re:emit", .var "p", .var "k", .expr [.sym "re:body", .var "at"]])
          (rows (emit body continuation (.body origin))) :=
        call (by simp [Special]) (.cons (.variable (by rfl)) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) .nil)))
          (ih continuation (.body origin))
      cases greedy with
      | false =>
          refine Applies.equation (equation := program[12]) (environment := environment) (by rfl) (by rfl) ?_
          exact node2 (by rfl) (by simp [Special])
            (node3 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))
              (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))) bodyRuns
      | true =>
          refine Applies.equation (equation := program[11]) (environment := environment) (by rfl) (by rfl) ?_
          exact node2 (by rfl) (by simp [Special])
            (node3 (by rfl) (by simp [Special]) (.variable (by rfl))
              (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.variable (by rfl))) bodyRuns
  | star body greedy ih =>
      let environment : Env := [("p", source body), ("k", address continuation), ("at", address origin)]
      have bodyRuns : Evaluates program host environment
          (.expr [.sym "re:emit", .var "p", .expr [.sym "re:loop", .var "at"],
            .expr [.sym "re:body", .var "at"]]) (rows (emit body (.loop origin) (.body origin))) :=
        call (by simp [Special]) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) .nil)))
          (ih (.loop origin) (.body origin))
      cases greedy with
      | false =>
          refine Applies.equation (equation := program[14]) (environment := environment) (by rfl) (by rfl) ?_
          exact node2 (by rfl) (by simp [Special])
            (node3 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))
              (node1 (by rfl) (by simp [Special]) (.variable (by rfl))))
            (node2 (by rfl) (by simp [Special])
              (node3 (by rfl) (by simp [Special])
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.variable (by rfl))
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))) bodyRuns)
      | true =>
          refine Applies.equation (equation := program[13]) (environment := environment) (by rfl) (by rfl) ?_
          exact node2 (by rfl) (by simp [Special])
            (node3 (by rfl) (by simp [Special]) (.variable (by rfl))
              (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.variable (by rfl)))
            (node2 (by rfl) (by simp [Special])
              (node3 (by rfl) (by simp [Special])
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.variable (by rfl))) bodyRuns)
  | plus body greedy ih =>
      let environment : Env := [("p", source body), ("k", address continuation), ("at", address origin)]
      have bodyRuns : Evaluates program host environment
          (.expr [.sym "re:emit", .var "p", .expr [.sym "re:loop", .var "at"],
            .expr [.sym "re:body", .var "at"]]) (rows (emit body (.loop origin) (.body origin))) :=
        call (by simp [Special]) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) .nil)))
          (ih (.loop origin) (.body origin))
      cases greedy with
      | false =>
          refine Applies.equation (equation := program[16]) (environment := environment) (by rfl) (by rfl) ?_
          exact node2 (by rfl) (by simp [Special])
            (node2 (by rfl) (by simp [Special]) (.variable (by rfl))
              (node1 (by rfl) (by simp [Special]) (.variable (by rfl))))
            (node2 (by rfl) (by simp [Special])
              (node3 (by rfl) (by simp [Special])
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.variable (by rfl))
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))) bodyRuns)
      | true =>
          refine Applies.equation (equation := program[15]) (environment := environment) (by rfl) (by rfl) ?_
          exact node2 (by rfl) (by simp [Special])
            (node2 (by rfl) (by simp [Special]) (.variable (by rfl))
              (node1 (by rfl) (by simp [Special]) (.variable (by rfl))))
            (node2 (by rfl) (by simp [Special])
              (node3 (by rfl) (by simp [Special])
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
                (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) (.variable (by rfl))) bodyRuns)
  | capture group body ih =>
      let environment : Env := [("g", natural group), ("p", source body),
        ("k", address continuation), ("at", address origin)]
      refine Applies.equation (equation := program[17]) (environment := environment) (by rfl) (by rfl) ?_
      have bodyRuns : Evaluates program host environment
          (.expr [.sym "re:emit", .var "p", .expr [.sym "re:close", .var "at"],
            .expr [.sym "re:body", .var "at"]]) (rows (emit body (.close origin) (.body origin))) :=
        call (by simp [Special]) (.cons (.variable (by rfl))
          (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.cons (node1 (by rfl) (by simp [Special]) (.variable (by rfl))) .nil)))
          (ih (.close origin) (.body origin))
      exact node2 (by rfl) (by simp [Special])
        (node4 (by rfl) (by simp [Special]) (.variable (by rfl)) (.variable (by rfl))
          (.symbol program host _ _) (node1 (by rfl) (by simp [Special]) (.variable (by rfl))))
        (node2 (by rfl) (by simp [Special])
          (node4 (by rfl) (by simp [Special])
            (node1 (by rfl) (by simp [Special]) (.variable (by rfl)))
            (.variable (by rfl)) (.symbol program host _ _) (.variable (by rfl))) bodyRuns)

theorem emit_result_exact (pattern : Pattern) (continuation origin : Address) (result : Term) :
    Applies program host "re:emit" [source pattern, address continuation, address origin] result ↔
      result = rows (emit pattern continuation origin) := by
  constructor
  · exact fun computation => computation.deterministic (emit_computes pattern continuation origin)
  · rintro rfl
    exact emit_computes pattern continuation origin

/-- Completion cannot fabricate an empty result, a fault, or another graph;
insufficient fuel remains the existing exhausted outcome. -/
theorem emit_completed (pattern : Pattern) (continuation origin : Address) (fuel : Nat)
    (finished : apply program host fuel "re:emit"
      [source pattern, address continuation, address origin] ≠ .exhausted) :
    apply program host fuel "re:emit" [source pattern, address continuation, address origin] =
      .value (rows (emit pattern continuation origin)) :=
  (emit_computes pattern continuation origin).completed fuel finished

def code (compiled : Mettapedia.GSLT.LanguageDef.RegexSelection.Program) : Term :=
  .expr [.sym "re:code", address compiled.entry, rows compiled.rows]

theorem compile_computes (pattern : Pattern) :
    Applies program host "re:compile" [source pattern] (code (compile pattern)) := by
  let environment : Env := [("p", source pattern)]
  refine Applies.equation (equation := program[0]) (environment := environment) (by rfl) (by rfl) ?_
  have emitted : Evaluates program host environment
      (.expr [.sym "re:emit", .var "p", .sym "re:end", .sym "re:root"])
      (rows (emit pattern .ending .root)) :=
    call (by simp [Special]) (.cons (.variable (by rfl))
      (.cons (.symbol program host _ _) (.cons (.symbol program host _ _) .nil)))
      (emit_computes pattern .ending .root)
  exact node2 (by rfl) (by simp [Special]) (.symbol program host _ _)
    (node2 (by rfl) (by simp [Special])
      (node1 (by rfl) (by simp [Special]) (.symbol program host _ _)) emitted)

theorem compile_result_exact (pattern : Pattern) (result : Term) :
    Applies program host "re:compile" [source pattern] result ↔ result = code (compile pattern) := by
  constructor
  · exact fun computation => computation.deterministic (compile_computes pattern)
  · rintro rfl
    exact compile_computes pattern

/-- The native optional and plus layouts are observations of the same
recursively authored Pattern compiler, including arbitrary nesting. -/
def optionalRows (pattern : Pattern) (greedy : Bool) (continuation origin : Address) : List Instruction :=
  choice origin (.body origin) continuation greedy :: emit pattern continuation (.body origin)

def plusRows (pattern : Pattern) (greedy : Bool) (continuation origin : Address) : List Instruction :=
  .jump origin (.body origin) :: choice (.loop origin) (.body origin) continuation greedy ::
    emit pattern (.loop origin) (.body origin)

theorem optional_computes (pattern : Pattern) (greedy : Bool) (continuation origin : Address) :
    Applies program host "re:emit"
      [.expr [.sym "re:optional", source pattern, preference greedy], address continuation, address origin]
      (rows (optionalRows pattern greedy continuation origin)) :=
  emit_computes (.optional pattern greedy) continuation origin

theorem plus_computes (pattern : Pattern) (greedy : Bool) (continuation origin : Address) :
    Applies program host "re:emit"
      [.expr [.sym "re:plus", source pattern, preference greedy], address continuation, address origin]
      (rows (plusRows pattern greedy continuation origin)) :=
  emit_computes (.plus pattern greedy) continuation origin

theorem optional_result_exact (pattern : Pattern) (greedy : Bool) (continuation origin : Address) (result : Term) :
    Applies program host "re:emit"
      [.expr [.sym "re:optional", source pattern, preference greedy], address continuation, address origin] result ↔
      result = rows (optionalRows pattern greedy continuation origin) := by
  constructor
  · exact fun computation => computation.deterministic (optional_computes pattern greedy continuation origin)
  · rintro rfl
    exact optional_computes pattern greedy continuation origin

theorem plus_result_exact (pattern : Pattern) (greedy : Bool) (continuation origin : Address) (result : Term) :
    Applies program host "re:emit"
      [.expr [.sym "re:plus", source pattern, preference greedy], address continuation, address origin] result ↔
      result = rows (plusRows pattern greedy continuation origin) := by
  constructor
  · exact fun computation => computation.deterministic (plus_computes pattern greedy continuation origin)
  · rintro rfl
    exact plus_computes pattern greedy continuation origin

namespace Controls

theorem compiled_nullable_capture_runs :
    Applies program host "re:compile" [source (.star (.capture 1 .epsilon) true)]
      (code (compile (.star (.capture 1 .epsilon) true))) := compile_computes _

theorem compiled_nested_optional_plus_runs :
    Applies program host "re:compile"
      [source (.optional (.plus (.capture 1 .epsilon) false) true)]
      (code (compile (.optional (.plus (.capture 1 .epsilon) false) true))) := compile_computes _

theorem compiled_nested_plus_optional_runs :
    Applies program host "re:compile"
      [source (.plus (.capture 2 (.optional (.literal 97) true)) false)]
      (code (compile (.plus (.capture 2 (.optional (.literal 97) true)) false))) := compile_computes _

theorem authored_append_keeps_call_shaped_data_inert :
    Applies program host "re:append"
      [list [.expr [.sym "re:emit", .sym "not-a-pattern"]], list []]
      (list [.expr [.sym "re:emit", .sym "not-a-pattern"]]) := append_computes _ _

theorem authored_compiler_cannot_omit_literal_instruction :
    ¬ Applies program host "re:emit" [source (.literal 97), address .ending, address .root]
      (rows []) := by
  intro computation
  have wrong := computation.deterministic (emit_computes (.literal 97) .ending .root)
  cases wrong

theorem authored_nested_plus_cannot_omit_instructions :
    ¬ Applies program host "re:emit"
      [source (.plus (.optional (.capture 3 .epsilon) false) true), address .ending, address .root]
      (rows []) := by
  intro computation
  have wrong := computation.deterministic
    (emit_computes (.plus (.optional (.capture 3 .epsilon) false) true) .ending .root)
  cases wrong

end Controls

end Mettapedia.GSLT.LanguageDef.RegexSelection.EquationExecution
