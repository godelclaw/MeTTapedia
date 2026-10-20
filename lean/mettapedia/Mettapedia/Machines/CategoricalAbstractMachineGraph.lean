import Mettapedia.Machines.CategoricalAbstractMachine
import Mettapedia.Machines.RationalTermGraph
import Mettapedia.Machines.BranchLocalNeed.CacheLaws
import Mettapedia.GSLT.Distinction.SpanTransport

/-!
# The categorical abstract machine on a value graph

Cousineau, Curien and Mauny, *The Categorical Abstract Machine* (1987),
describe the machine term as "a graph in an actual implementation" and extend
it in Section 4 (pp. 191--196, Tables 6 and 7) and Section 5 (pp. 196--200):

* recursion `F(M) = Λ(M) ∘ ⟨Id, F(M)⟩` for `Y(λf.λn.M)`, compiled as
  `push; quote (); cons; push; cur C; wind`, where `wind` physically replaces
  the right part of the couple on the stack by the closure (LISP's `rplacd`),
  leaving the cyclic closure `c = C:(s, c)` in the register (Table 6);
* delayed evaluation: `freeze C` builds a laze `C.s`, `unfreeze` runs a laze's
  code in its environment and forces the result again, and is a skip on any
  other term (Table 7). Lazes are not updated after forcing (call by name);
* the strict primitives `plus`, `minus`, `times`, `eq`, `leq` on couples of
  integers (p. 198).

Values live in a heap of cells (couples, closures, lazes) addressed by natural
numbers; allocation appends and `wind` updates one existing couple. The
instruction table is the one of `CategoricalAbstractMachine`; the tree-valued
machine there has no rule for the four instructions above.

A separate source grammar `Term` with an independent big-step judgment
(`Evaluation`, `Invocation`, `Force`) forces exactly at the strict positions:
source projections, the operator of an application, both operands of a
primitive, and the condition of a conditional. Variables are environment
accesses and are not forced (p. 200). The 1987 listing omits the condition;
by its own rule ("insert those instructions before the 'strict' instructions",
p. 194) the compiler also places `unfreeze` before `branch`.

The listing's `unfa = [push; snd; swap; fst; unfreeze; cons]` and
`unfb = [unfreeze; push; snd; unfreeze; swap; fst; unfreeze; cons]` take `snd`
before `fst`; with Table 1's `swap` and `cons` they rebuild the couple with its
components exchanged, so `app` would not find the closure on the left and
`minus`, `leq` would receive their operands reversed. `forceOperator` and
`forceOperands` take `fst` first and rebuild the couple in place order. The
Section 5 `letrec` code has a `swap` before `wind` that leaves a closure, not a
couple, on the stack; the Table 6 code of Section 4 is used.

A heap word `Represents` a source value by a finite derivation. A closure node
whose environment couple points back to the node represents
`recursive body environment`; the same node also represents the one-step
unfolding `closure body (pair environment (recursive body environment))`, so
the representation is a relation and not a function (`Represents.not_functional`).

Main results:

* `Evaluation.execution` (soundness) and `execution_complete` (completeness):
  compiled code runs from any represented environment to a represented value,
  retaining the caller's code and stack and never changing cells that existed
  before the run; every completed run constructs the source derivation of the
  value its answer represents. No termination is assumed.
* `evaluates_iff_completes`, `execution_represents_evaluation` and
  `evaluation_iff_execution`: completion agrees with evaluation, the answer
  represents the unique evaluated value, and a value is evaluated up to the
  rational term it denotes exactly when every finite observation of the answer
  shows it. Equality of source syntax is not observable on the graph.
* `Represents.observe`, `Represents.bisimilar_iff`, `observation_iff_execution`:
  the heap is a `RationalTermGraph.LayerReader`; represented words observe the
  depth-indexed unfolding of their values, and bisimilarity in an admitted table
  is agreement at every depth.
* `refinement`, `abstraction`, `refinement_stuck`, `abstraction_stuck`: on the
  tree machine's own instructions the value graph and the strict tree machine
  move in lock step through the common `CostSimulation` interface;
  `tree_source_completion` and `tree_source_execution` transfer the tree source
  correspondence. Allocation keeps a heap topologically ordered
  (`Transition.ordered`, `ordered_unfolds`); `wind` does not
  (`windHeap_not_ordered`, `windHeap_no_unfolding`).
* `treeStrict_iff_graph`: on the tree machine's quotation/conditional source the
  graph judgment is exactly the active-rule part of the tree judgment.
* `core`, `answerCore`, `machine`, `instructionContract`, `loadImage`: the
  common machine, answer, runner, dynamic-legality and checked-loading
  interfaces.
* `Need.evaluation_iff_execution`, `Need.evaluation_iff_finished` and
  `Need.source_iff_run`: a separate memoizing realization agrees in both
  directions with an independent source judgment over the shared arena and
  demand store. First forcing owns an update continuation; nested forcing
  returns through it; later forcing reuses the committed word. The common
  Need cell lifecycle proves that completed producers never restart.
  Paused or blocked producers remain retained and are not completed answers.
  This theorem concerns the explicit Need strategy, not equality of its trace
  or raw allocation layout with the historical call-by-name machine.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CategoricalAbstractMachine.Graph

/-! ## Source grammar and independent judgment -/

/-- The source grammar of the value-graph machine: the constructs shared with
the tree machine, strict primitives on a couple of integers, recursive
functions `fix body` (CCM's `F(M)`) and frozen bodies. In `fix body`, index 0 is
the argument, index 1 the recursive function itself and index `k + 2` the
outer index `k`. -/
inductive Term where
  | var (index : Nat)
  | lam (body : Term)
  | app (operator argument : Term)
  | pair (left right : Term)
  | first (term : Term)
  | second (term : Term)
  | literal (value : Literal)
  | conditional (condition whenTrue whenFalse : Term)
  | primitive (operation : Primitive) (argument : Term)
  | fix (body : Term)
  | freeze (body : Term)
  deriving DecidableEq, Repr

/-- Source values. `recursive body environment` is the value of
`fix body` in `environment`; `laze body environment` is a frozen body. -/
inductive Value where
  | unit
  | literal (value : Literal)
  | pair (left right : Value)
  | closure (body : Term) (environment : Value)
  | recursive (body : Term) (environment : Value)
  | laze (body : Term) (environment : Value)
  deriving DecidableEq, Repr

/-- Values on which forcing performs no action. -/
def Value.NotLaze : Value → Prop
  | .laze _ _ => False
  | _ => True

mutual
/-- Completed strict evaluation. Forcing occurs exactly at the strict
positions; instruction lists do not occur in this judgment. -/
inductive Evaluation : Term → Value → Value → Prop where
  | varZero (environment value : Value) : Evaluation (.var 0) (.pair environment value) value
  | varSucc {index : Nat} {environment value : Value} (saved : Value)
      (rest : Evaluation (.var index) environment value) :
      Evaluation (.var (index + 1)) (.pair environment saved) value
  | literal (value : Literal) (environment : Value) :
      Evaluation (.literal value) environment (.literal value)
  | lam (body : Term) (environment : Value) :
      Evaluation (.lam body) environment (.closure body environment)
  | fix (body : Term) (environment : Value) :
      Evaluation (.fix body) environment (.recursive body environment)
  | freeze (body : Term) (environment : Value) :
      Evaluation (.freeze body) environment (.laze body environment)
  | pair {left right : Term} {environment leftValue rightValue : Value}
      (leftEval : Evaluation left environment leftValue)
      (rightEval : Evaluation right environment rightValue) :
      Evaluation (.pair left right) environment (.pair leftValue rightValue)
  | first {term : Term} {environment before left right : Value}
      (termEval : Evaluation term environment before) (forced : Force before (.pair left right)) :
      Evaluation (.first term) environment left
  | second {term : Term} {environment before left right : Value}
      (termEval : Evaluation term environment before) (forced : Force before (.pair left right)) :
      Evaluation (.second term) environment right
  | app {operator argument : Term} {environment function operand callee value : Value}
      (operatorEval : Evaluation operator environment function)
      (argumentEval : Evaluation argument environment operand)
      (forced : Force function callee) (invocation : Invocation callee operand value) :
      Evaluation (.app operator argument) environment value
  | conditional {condition whenTrue whenFalse : Term} {environment before value : Value}
      {selected : Bool} (conditionEval : Evaluation condition environment before)
      (forced : Force before (.literal (.boolean selected)))
      (selectedEval : Evaluation (if selected then whenTrue else whenFalse) environment value) :
      Evaluation (.conditional condition whenTrue whenFalse) environment value
  | primitive {operation : Primitive} {argument : Term} {environment before left right : Value}
      {leftValue rightValue : Int} (argumentEval : Evaluation argument environment before)
      (forced : Force before (.pair left right))
      (leftForced : Force left (.literal (.integer leftValue)))
      (rightForced : Force right (.literal (.integer rightValue))) :
      Evaluation (.primitive operation argument) environment
        (.literal (operation.apply leftValue rightValue))
/-- Application of a forced function value. A recursive function sees itself at
index 1 of the body environment. -/
inductive Invocation : Value → Value → Value → Prop where
  | closure {body : Term} {environment argument value : Value}
      (bodyEval : Evaluation body (.pair environment argument) value) :
      Invocation (.closure body environment) argument value
  | recursive {body : Term} {environment argument value : Value}
      (bodyEval : Evaluation body
        (.pair (.pair environment (.recursive body environment)) argument) value) :
      Invocation (.recursive body environment) argument value
/-- Repetitive forcing (Table 7): a laze evaluates its body in its captured
environment and the result is forced again; any other value is itself. -/
inductive Force : Value → Value → Prop where
  | laze {body : Term} {environment value result : Value}
      (bodyEval : Evaluation body environment value) (again : Force value result) :
      Force (.laze body environment) result
  | value (value : Value) (notLaze : value.NotLaze) : Force value value
end

theorem Force.notLaze : {value result : Value} → Force value result → result.NotLaze
  | _, _, .laze _ again => Force.notLaze again
  | _, _, .value _ notLaze => notLaze

mutual
/-- The source judgment is deterministic. -/
theorem Evaluation.unique : {term : Term} → {environment first second : Value} →
    Evaluation term environment first → Evaluation term environment second → first = second
  | _, _, _, _, .varZero _ _, .varZero _ _ => rfl
  | _, _, _, _, .varSucc _ rest, .varSucc _ rest' => Evaluation.unique rest rest'
  | _, _, _, _, .literal _ _, .literal _ _ => rfl
  | _, _, _, _, .lam _ _, .lam _ _ => rfl
  | _, _, _, _, .fix _ _, .fix _ _ => rfl
  | _, _, _, _, .freeze _ _, .freeze _ _ => rfl
  | _, _, _, _, .pair leftEval rightEval, .pair leftEval' rightEval' => by
      rw [Evaluation.unique leftEval leftEval', Evaluation.unique rightEval rightEval']
  | _, _, _, _, .first termEval forced, .first termEval' forced' => by
      cases Evaluation.unique termEval termEval'
      cases Force.unique forced forced'
      rfl
  | _, _, _, _, .second termEval forced, .second termEval' forced' => by
      cases Evaluation.unique termEval termEval'
      cases Force.unique forced forced'
      rfl
  | _, _, _, _, .app operatorEval argumentEval forced invocation,
      .app operatorEval' argumentEval' forced' invocation' => by
      cases Evaluation.unique operatorEval operatorEval'
      cases Evaluation.unique argumentEval argumentEval'
      cases Force.unique forced forced'
      exact Invocation.unique invocation invocation'
  | _, _, _, _, .conditional (selected := selected) conditionEval forced selectedEval,
      .conditional (selected := selected') conditionEval' forced' selectedEval' => by
      cases Evaluation.unique conditionEval conditionEval'
      have same : selected = selected' := by
        have literal := Force.unique forced forced'
        cases literal
        rfl
      subst same
      exact Evaluation.unique selectedEval selectedEval'
  | _, _, _, _, .primitive argumentEval forced leftForced rightForced,
      .primitive argumentEval' forced' leftForced' rightForced' => by
      cases Evaluation.unique argumentEval argumentEval'
      cases Force.unique forced forced'
      cases Force.unique leftForced leftForced'
      cases Force.unique rightForced rightForced'
      rfl
theorem Invocation.unique : {function argument first second : Value} →
    Invocation function argument first → Invocation function argument second → first = second
  | _, _, _, _, .closure bodyEval, .closure bodyEval' => Evaluation.unique bodyEval bodyEval'
  | _, _, _, _, .recursive bodyEval, .recursive bodyEval' => Evaluation.unique bodyEval bodyEval'
theorem Force.unique : {value first second : Value} →
    Force value first → Force value second → first = second
  | _, _, _, .laze bodyEval again, .laze bodyEval' again' => by
      cases Evaluation.unique bodyEval bodyEval'
      exact Force.unique again again'
  | _, _, _, .laze _ _, .value _ notLaze => False.elim notLaze
  | _, _, _, .value _ notLaze, .laze _ _ => False.elim notLaze
  | _, _, _, .value _ _, .value _ _ => rfl
end

/-! ## Compiler -/

/-- CCM's `unfa` with its projections in place order: force the operator of
the couple `(function, argument)` in the register and rebuild the couple. -/
def forceOperator : Code := [.push, .first, .unfreeze, .swap, .second, .cons]

/-- CCM's `unfb` with its projections in place order: force a couple, then its
left and its right component, and rebuild the couple. -/
def forceOperands : Code :=
  [.unfreeze, .push, .first, .unfreeze, .swap, .second, .unfreeze, .cons]

/-- The compiler of Sections 4 and 5, with `unfreeze` before every strict
instruction and none on environment access. -/
def compile : Term → Code
  | .var index => List.replicate index .first ++ [.second]
  | .lam body => [.cur (compile body)]
  | .app operator argument =>
      [.push] ++ compile operator ++ [.swap] ++ compile argument ++ [.cons] ++ forceOperator ++ [.app]
  | .pair left right => [.push] ++ compile left ++ [.swap] ++ compile right ++ [.cons]
  | .first term => compile term ++ [.unfreeze, .first]
  | .second term => compile term ++ [.unfreeze, .second]
  | .literal value => [.quote value]
  | .conditional condition whenTrue whenFalse =>
      .push :: compile condition ++ [.unfreeze, .branch (compile whenTrue) (compile whenFalse)]
  | .primitive operation argument => compile argument ++ forceOperands ++ [.operation operation]
  | .fix body => [.push, .quote .unit, .cons, .push, .cur (compile body), .wind]
  | .freeze body => [.freeze (compile body)]

theorem compile_nonempty (term : Term) : compile term ≠ [] := by
  cases term <;> simp [compile]

@[simp] theorem compile_var_succ (index : Nat) :
    compile (.var (index + 1)) = .first :: compile (.var index) := by
  simp [compile, List.replicate_succ]

/-! ## Code readback -/

private inductive Symbolic where
  | environment (depth : Nat)
  | term (expression : Term)
  | forced (expression : Term)
  | operator (couple : Term)
  | operands (left : Term)
  | recursion
  | recursive (body : Term)

private structure SymbolicState where
  register : Symbolic
  stack : List Symbolic

/-- Symbolically execute compiled code. The final canonical check in `decode`
separates compiler output from any other instruction list. -/
@[simp] private def decodeAux : Code → SymbolicState → Option SymbolicState
  | [], state => some state
  | .first :: rest, ⟨.environment depth, stack⟩ =>
      decodeAux rest ⟨.environment (depth + 1), stack⟩
  | .first :: rest, ⟨.forced expression, stack⟩ =>
      decodeAux rest ⟨.term (.first expression), stack⟩
  | .first :: rest, ⟨.term couple, stack⟩ => decodeAux rest ⟨.operator couple, stack⟩
  | .second :: rest, ⟨.environment depth, stack⟩ => decodeAux rest ⟨.term (.var depth), stack⟩
  | .second :: rest, ⟨.forced expression, stack⟩ =>
      decodeAux rest ⟨.term (.second expression), stack⟩
  | .second :: rest, ⟨.term couple, stack⟩ => decodeAux rest ⟨.operator couple, stack⟩
  | .unfreeze :: rest, ⟨.term expression, stack⟩ => decodeAux rest ⟨.forced expression, stack⟩
  | .unfreeze :: rest, ⟨.operator couple, stack⟩ => decodeAux rest ⟨.operator couple, stack⟩
  | .cur body :: rest, ⟨.environment 0, stack⟩ =>
      match decodeAux body ⟨.environment 0, []⟩ with
      | some ⟨.term expression, []⟩ => decodeAux rest ⟨.term (.lam expression), stack⟩
      | _ => none
  | .cur body :: rest, ⟨.recursion, stack⟩ =>
      match decodeAux body ⟨.environment 0, []⟩ with
      | some ⟨.term expression, []⟩ => decodeAux rest ⟨.recursive expression, stack⟩
      | _ => none
  | .freeze body :: rest, ⟨.environment 0, stack⟩ =>
      match decodeAux body ⟨.environment 0, []⟩ with
      | some ⟨.term expression, []⟩ => decodeAux rest ⟨.term (.freeze expression), stack⟩
      | _ => none
  | .push :: rest, ⟨value, stack⟩ => decodeAux rest ⟨value, value :: stack⟩
  | .swap :: rest, ⟨value, saved :: stack⟩ => decodeAux rest ⟨saved, value :: stack⟩
  | .cons :: rest, ⟨.term right, .term left :: stack⟩ =>
      decodeAux rest ⟨.term (.pair left right), stack⟩
  | .cons :: rest, ⟨.forced _, .forced left :: stack⟩ => decodeAux rest ⟨.operands left, stack⟩
  | .cons :: rest, ⟨.operator _, .operator couple :: stack⟩ =>
      decodeAux rest ⟨.operator couple, stack⟩
  | .cons :: rest, ⟨.term (.literal .unit), .environment 0 :: stack⟩ =>
      decodeAux rest ⟨.recursion, stack⟩
  | .app :: rest, ⟨.operator (.pair operator argument), stack⟩ =>
      decodeAux rest ⟨.term (.app operator argument), stack⟩
  | .quote value :: rest, ⟨.environment 0, stack⟩ => decodeAux rest ⟨.term (.literal value), stack⟩
  | .branch whenTrue whenFalse :: rest, ⟨.forced condition, .environment 0 :: stack⟩ =>
      match decodeAux whenTrue ⟨.environment 0, []⟩, decodeAux whenFalse ⟨.environment 0, []⟩ with
      | some ⟨.term left, []⟩, some ⟨.term right, []⟩ =>
          decodeAux rest ⟨.term (.conditional condition left right), stack⟩
      | _, _ => none
  | .operation operation :: rest, ⟨.operands (.first argument), stack⟩ =>
      decodeAux rest ⟨.term (.primitive operation argument), stack⟩
  | .wind :: rest, ⟨.recursive body, .recursion :: stack⟩ => decodeAux rest ⟨.term (.fix body), stack⟩
  | _, _ => none

private theorem decodeAux_lookup (index depth : Nat) (rest : Code) (stack : List Symbolic) :
    decodeAux (List.replicate index .first ++ .second :: rest) ⟨.environment depth, stack⟩ =
      decodeAux rest ⟨.term (.var (depth + index)), stack⟩ := by
  induction index generalizing depth with
  | zero => simp [decodeAux]
  | succ index ih =>
      simp only [List.replicate_succ, List.cons_append, decodeAux]
      simpa only [Nat.add_assoc, Nat.add_comm 1 index] using ih (depth + 1)

private theorem decodeAux_compile (expression : Term) (rest : Code) (stack : List Symbolic) :
    decodeAux (compile expression ++ rest) ⟨.environment 0, stack⟩ =
      decodeAux rest ⟨.term expression, stack⟩ := by
  induction expression generalizing rest stack with
  | var index =>
      simpa only [compile, List.append_assoc, List.singleton_append, Nat.zero_add]
        using decodeAux_lookup index 0 rest stack
  | lam body ih =>
      have bodyDecoded := ih [] []
      simp only [List.append_nil, decodeAux] at bodyDecoded
      simp only [compile, List.singleton_append, decodeAux, bodyDecoded]
  | app operator argument operatorIH argumentIH =>
      simp only [compile, forceOperator, List.append_assoc, List.cons_append, List.nil_append,
        decodeAux]
      rw [operatorIH]
      simp only [decodeAux]
      rw [argumentIH]
      simp only [decodeAux]
  | pair left right leftIH rightIH =>
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append, decodeAux]
      rw [leftIH]
      simp only [decodeAux]
      rw [rightIH]
      simp only [decodeAux]
  | first term ih =>
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append]
      rw [ih]
      simp only [decodeAux]
  | second term ih =>
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append]
      rw [ih]
      simp only [decodeAux]
  | literal value => simp [compile, decodeAux]
  | conditional condition whenTrue whenFalse conditionIH trueIH falseIH =>
      simp only [compile, List.cons_append, List.append_assoc, decodeAux]
      rw [conditionIH]
      have trueDecoded := trueIH [] []
      have falseDecoded := falseIH [] []
      simp only [List.append_nil, decodeAux] at trueDecoded falseDecoded
      simp [decodeAux, trueDecoded, falseDecoded]
  | primitive operation argument ih =>
      simp only [compile, forceOperands, List.append_assoc, List.cons_append, List.nil_append]
      rw [ih]
      simp only [decodeAux]
  | fix body ih =>
      have bodyDecoded := ih [] []
      simp only [List.append_nil, decodeAux] at bodyDecoded
      simp only [compile, List.cons_append, List.nil_append, decodeAux, bodyDecoded]
  | freeze body ih =>
      have bodyDecoded := ih [] []
      simp only [List.append_nil, decodeAux] at bodyDecoded
      simp only [compile, List.singleton_append, decodeAux, bodyDecoded]

/-- Code readback: symbolic execution followed by the canonical check. -/
def decode (code : Code) : Option Term :=
  match decodeAux code ⟨.environment 0, []⟩ with
  | some ⟨.term expression, []⟩ => if compile expression = code then some expression else none
  | _ => none

@[simp] theorem decode_compile (expression : Term) : decode (compile expression) = some expression := by
  have reconstructed := decodeAux_compile expression [] []
  simp only [List.append_nil, decodeAux] at reconstructed
  simp [decode, reconstructed]

theorem compile_decode {code : Code} {expression : Term} (decoded : decode code = some expression) :
    compile expression = code := by
  unfold decode at decoded
  split at decoded
  · split at decoded
    · cases decoded
      assumption
    · contradiction
  · contradiction

theorem compile_injective : Function.Injective compile := by
  intro left right same
  have decoded := congrArg decode same
  simpa only [decode_compile, Option.some.injEq] using decoded


/-! ## The value graph and its machine -/

/-- A machine word: the empty environment, a quoted constant, or the address of
a heap cell. -/
inductive Word where
  | unit
  | literal (value : Literal)
  | ref (address : Nat)
  deriving DecidableEq, Repr

/-- Heap cells: couples, closures `C:s` and lazes `C.s` (Tables 1 and 7). -/
inductive Cell where
  | pair (left right : Word)
  | closure (body : Code) (environment : Word)
  | laze (body : Code) (environment : Word)
  deriving DecidableEq, Repr

/-- The value graph. The address of a cell is its position; allocation appends. -/
abbrev Heap := List Cell

/-- A configuration: the term register, the code, the stack of words and the heap. -/
structure State where
  register : Word
  code : Code
  stack : List Word
  heap : Heap
  deriving DecidableEq, Repr

/-- The word addresses a laze cell. -/
def LazeAt (heap : Heap) (word : Word) : Prop :=
  ∃ address body environment, word = .ref address ∧ heap[address]? = some (.laze body environment)

/-- The executable instruction table of the strict profile. `cur`, `cons`, `app`
and `freeze` allocate one cell; `app` allocates the new couple `(s, t)` of the
body environment (Table 8). `wind` updates the couple addressed by the stack top
and keeps the closure in the register (Table 6). `unfreeze` on a laze prefixes
the laze code and itself to the code (Table 7); on any other term it is a skip.
Projections, `app`, `branch` and `operation` have no rule on other terms. -/
def step : State → Option State
  | ⟨_, [], _, _⟩ => none
  | ⟨.ref address, .first :: code, stack, heap⟩ =>
      match heap[address]? with
      | some (.pair left _) => some ⟨left, code, stack, heap⟩
      | _ => none
  | ⟨.ref address, .second :: code, stack, heap⟩ =>
      match heap[address]? with
      | some (.pair _ right) => some ⟨right, code, stack, heap⟩
      | _ => none
  | ⟨word, .cur body :: code, stack, heap⟩ =>
      some ⟨.ref heap.length, code, stack, heap ++ [.closure body word]⟩
  | ⟨word, .push :: code, stack, heap⟩ => some ⟨word, code, word :: stack, heap⟩
  | ⟨word, .swap :: code, saved :: stack, heap⟩ => some ⟨saved, code, word :: stack, heap⟩
  | ⟨word, .cons :: code, saved :: stack, heap⟩ =>
      some ⟨.ref heap.length, code, stack, heap ++ [.pair saved word]⟩
  | ⟨.ref address, .app :: code, stack, heap⟩ =>
      match heap[address]? with
      | some (.pair (.ref function) argument) =>
          match heap[function]? with
          | some (.closure body environment) =>
              some ⟨.ref heap.length, body ++ code, stack, heap ++ [.pair environment argument]⟩
          | _ => none
      | _ => none
  | ⟨_, .quote value :: code, stack, heap⟩ => some ⟨.literal value, code, stack, heap⟩
  | ⟨.literal (.boolean selected), .branch whenTrue whenFalse :: code, saved :: stack, heap⟩ =>
      some ⟨saved, (if selected then whenTrue else whenFalse) ++ code, stack, heap⟩
  | ⟨.ref address, .operation primitive :: code, stack, heap⟩ =>
      match heap[address]? with
      | some (.pair (.literal (.integer left)) (.literal (.integer right))) =>
          some ⟨.literal (primitive.apply left right), code, stack, heap⟩
      | _ => none
  | ⟨word, .wind :: code, .ref address :: stack, heap⟩ =>
      match heap[address]? with
      | some (.pair left _) => some ⟨word, code, stack, heap.set address (.pair left word)⟩
      | _ => none
  | ⟨word, .freeze body :: code, stack, heap⟩ =>
      some ⟨.ref heap.length, code, stack, heap ++ [.laze body word]⟩
  | ⟨.ref address, .unfreeze :: code, stack, heap⟩ =>
      match heap[address]? with
      | some (.laze body environment) => some ⟨environment, body ++ .unfreeze :: code, stack, heap⟩
      | _ => some ⟨.ref address, code, stack, heap⟩
  | ⟨word, .unfreeze :: code, stack, heap⟩ => some ⟨word, code, stack, heap⟩
  | _ => none

/-- The instruction table as independent operational rules. -/
inductive Transition : State → State → Prop where
  | first {address : Nat} {left right : Word} (code : Code) (stack : List Word) (heap : Heap)
      (cell : heap[address]? = some (.pair left right)) :
      Transition ⟨.ref address, .first :: code, stack, heap⟩ ⟨left, code, stack, heap⟩
  | second {address : Nat} {left right : Word} (code : Code) (stack : List Word) (heap : Heap)
      (cell : heap[address]? = some (.pair left right)) :
      Transition ⟨.ref address, .second :: code, stack, heap⟩ ⟨right, code, stack, heap⟩
  | cur (word : Word) (body code : Code) (stack : List Word) (heap : Heap) :
      Transition ⟨word, .cur body :: code, stack, heap⟩
        ⟨.ref heap.length, code, stack, heap ++ [.closure body word]⟩
  | push (word : Word) (code : Code) (stack : List Word) (heap : Heap) :
      Transition ⟨word, .push :: code, stack, heap⟩ ⟨word, code, word :: stack, heap⟩
  | swap (word saved : Word) (code : Code) (stack : List Word) (heap : Heap) :
      Transition ⟨word, .swap :: code, saved :: stack, heap⟩ ⟨saved, code, word :: stack, heap⟩
  | cons (word saved : Word) (code : Code) (stack : List Word) (heap : Heap) :
      Transition ⟨word, .cons :: code, saved :: stack, heap⟩
        ⟨.ref heap.length, code, stack, heap ++ [.pair saved word]⟩
  | app {address function : Nat} {argument environment : Word} {body : Code}
      (code : Code) (stack : List Word) (heap : Heap)
      (couple : heap[address]? = some (.pair (.ref function) argument))
      (closure : heap[function]? = some (.closure body environment)) :
      Transition ⟨.ref address, .app :: code, stack, heap⟩
        ⟨.ref heap.length, body ++ code, stack, heap ++ [.pair environment argument]⟩
  | quote (word : Word) (value : Literal) (code : Code) (stack : List Word) (heap : Heap) :
      Transition ⟨word, .quote value :: code, stack, heap⟩ ⟨.literal value, code, stack, heap⟩
  | branch (selected : Bool) (saved : Word) (whenTrue whenFalse code : Code) (stack : List Word)
      (heap : Heap) :
      Transition ⟨.literal (.boolean selected), .branch whenTrue whenFalse :: code, saved :: stack, heap⟩
        ⟨saved, (if selected then whenTrue else whenFalse) ++ code, stack, heap⟩
  | operation {address : Nat} {left right : Int} (primitive : Primitive) (code : Code)
      (stack : List Word) (heap : Heap)
      (cell : heap[address]? = some (.pair (.literal (.integer left)) (.literal (.integer right)))) :
      Transition ⟨.ref address, .operation primitive :: code, stack, heap⟩
        ⟨.literal (primitive.apply left right), code, stack, heap⟩
  | wind {address : Nat} {left right : Word} (word : Word) (code : Code) (stack : List Word)
      (heap : Heap) (cell : heap[address]? = some (.pair left right)) :
      Transition ⟨word, .wind :: code, .ref address :: stack, heap⟩
        ⟨word, code, stack, heap.set address (.pair left word)⟩
  | freeze (word : Word) (body code : Code) (stack : List Word) (heap : Heap) :
      Transition ⟨word, .freeze body :: code, stack, heap⟩
        ⟨.ref heap.length, code, stack, heap ++ [.laze body word]⟩
  | force {address : Nat} {body : Code} {environment : Word} (code : Code) (stack : List Word)
      (heap : Heap) (cell : heap[address]? = some (.laze body environment)) :
      Transition ⟨.ref address, .unfreeze :: code, stack, heap⟩
        ⟨environment, body ++ .unfreeze :: code, stack, heap⟩
  | skip (word : Word) (code : Code) (stack : List Word) (heap : Heap) (notLaze : ¬ LazeAt heap word) :
      Transition ⟨word, .unfreeze :: code, stack, heap⟩ ⟨word, code, stack, heap⟩

theorem step_complete {before after : State} (transition : Transition before after) :
    step before = some after := by
  cases transition with
  | first _ _ _ cell => simp [step, cell]
  | second _ _ _ cell => simp [step, cell]
  | cur => rfl
  | push => rfl
  | swap => rfl
  | cons => rfl
  | app _ _ _ couple closure => simp [step, couple, closure]
  | quote => rfl
  | branch => rfl
  | operation _ _ _ _ cell => simp [step, cell]
  | wind _ _ _ _ cell => simp [step, cell]
  | freeze => rfl
  | force _ _ _ cell => simp [step, cell]
  | skip word code stack heap notLaze =>
      cases word with
      | ref address =>
          cases cell : heap[address]? with
          | none => simp [step, cell]
          | some found =>
              cases found with
              | laze body environment => exact False.elim (notLaze ⟨_, _, _, rfl, cell⟩)
              | pair _ _ | closure _ _ => simp [step, cell]
      | unit | literal _ => rfl

theorem step_sound {before after : State} (execution : step before = some after) :
    Transition before after := by
  rcases before with ⟨register, code, stack, heap⟩
  cases code with
  | nil => simp [step] at execution
  | cons instruction code =>
      cases instruction with
      | first =>
          cases register with
          | ref address =>
              cases cell : heap[address]? with
              | none => simp [step, cell] at execution
              | some found =>
                  cases found with
                  | pair left right =>
                      simp only [step, cell, Option.some.injEq] at execution
                      subst after
                      exact .first _ _ _ cell
                  | closure _ _ | laze _ _ => simp [step, cell] at execution
          | unit | literal _ => simp [step] at execution
      | second =>
          cases register with
          | ref address =>
              cases cell : heap[address]? with
              | none => simp [step, cell] at execution
              | some found =>
                  cases found with
                  | pair left right =>
                      simp only [step, cell, Option.some.injEq] at execution
                      subst after
                      exact .second _ _ _ cell
                  | closure _ _ | laze _ _ => simp [step, cell] at execution
          | unit | literal _ => simp [step] at execution
      | cur body =>
          simp only [step, Option.some.injEq] at execution
          subst after
          exact .cur _ _ _ _ _
      | push =>
          simp only [step, Option.some.injEq] at execution
          subst after
          exact .push _ _ _ _
      | swap =>
          cases stack with
          | nil => simp [step] at execution
          | cons saved stack =>
              simp only [step, Option.some.injEq] at execution
              subst after
              exact .swap _ _ _ _ _
      | cons =>
          cases stack with
          | nil => simp [step] at execution
          | cons saved stack =>
              simp only [step, Option.some.injEq] at execution
              subst after
              exact .cons _ _ _ _ _
      | app =>
          cases register with
          | ref address =>
              cases couple : heap[address]? with
              | none => simp [step, couple] at execution
              | some found =>
                  cases found with
                  | pair function argument =>
                      cases function with
                      | ref function =>
                          cases closure : heap[function]? with
                          | none => simp [step, couple, closure] at execution
                          | some target =>
                              cases target with
                              | closure body environment =>
                                  simp only [step, couple, closure, Option.some.injEq] at execution
                                  subst after
                                  exact .app _ _ _ couple closure
                              | pair _ _ | laze _ _ => simp [step, couple, closure] at execution
                      | unit | literal _ => simp [step, couple] at execution
                  | closure _ _ | laze _ _ => simp [step, couple] at execution
          | unit | literal _ => simp [step] at execution
      | quote value =>
          simp only [step, Option.some.injEq] at execution
          subst after
          exact .quote _ _ _ _ _
      | branch whenTrue whenFalse =>
          cases register with
          | literal value =>
              cases value with
              | boolean selected =>
                  cases stack with
                  | nil => simp [step] at execution
                  | cons saved stack =>
                      simp only [step, Option.some.injEq] at execution
                      subst after
                      exact .branch _ _ _ _ _ _ _
              | integer _ | unit => simp [step] at execution
          | unit | ref _ => simp [step] at execution
      | operation primitive =>
          cases register with
          | ref address =>
              cases cell : heap[address]? with
              | none => simp [step, cell] at execution
              | some found =>
                  cases found with
                  | pair left right =>
                      cases left with
                      | literal left =>
                          cases left with
                          | integer left =>
                              cases right with
                              | literal right =>
                                  cases right with
                                  | integer right =>
                                      simp only [step, cell, Option.some.injEq] at execution
                                      subst after
                                      exact .operation _ _ _ _ cell
                                  | boolean _ | unit => simp [step, cell] at execution
                              | unit | ref _ => simp [step, cell] at execution
                          | boolean _ | unit => simp [step, cell] at execution
                      | unit | ref _ => simp [step, cell] at execution
                  | closure _ _ | laze _ _ => simp [step, cell] at execution
          | unit | literal _ => simp [step] at execution
      | wind =>
          cases stack with
          | nil => simp [step] at execution
          | cons saved stack =>
              cases saved with
              | ref address =>
                  cases cell : heap[address]? with
                  | none => simp [step, cell] at execution
                  | some found =>
                      cases found with
                      | pair left right =>
                          simp only [step, cell, Option.some.injEq] at execution
                          subst after
                          exact .wind _ _ _ _ cell
                      | closure _ _ | laze _ _ => simp [step, cell] at execution
              | unit | literal _ => simp [step] at execution
      | freeze body =>
          simp only [step, Option.some.injEq] at execution
          subst after
          exact .freeze _ _ _ _ _
      | unfreeze =>
          cases register with
          | ref address =>
              cases cell : heap[address]? with
              | none =>
                  simp only [step, cell, Option.some.injEq] at execution
                  subst after
                  refine .skip _ _ _ _ ?_
                  rintro ⟨_, _, _, same, found⟩
                  cases same
                  simp [cell] at found
              | some found =>
                  cases found with
                  | laze body environment =>
                      simp only [step, cell, Option.some.injEq] at execution
                      subst after
                      exact .force _ _ _ cell
                  | pair _ _ | closure _ _ =>
                      simp only [step, cell, Option.some.injEq] at execution
                      subst after
                      refine .skip _ _ _ _ ?_
                      rintro ⟨_, _, _, same, laze⟩
                      cases same
                      simp [cell] at laze
          | unit =>
              simp only [step, Option.some.injEq] at execution
              subst after
              refine .skip _ _ _ _ ?_
              rintro ⟨_, _, _, same, _⟩
              cases same
          | literal _ =>
              simp only [step, Option.some.injEq] at execution
              subst after
              refine .skip _ _ _ _ ?_
              rintro ⟨_, _, _, same, _⟩
              cases same

theorem step_iff (before after : State) : step before = some after ↔ Transition before after :=
  ⟨step_sound, step_complete⟩

theorem Transition.deterministic {state first second : State}
    (one : Transition state first) (two : Transition state second) : first = second :=
  Option.some.inj ((step_complete one).symm.trans (step_complete two))

abbrev Steps := Relation.ReflTransGen Transition

/-- Append a code suffix and a stack suffix, keeping the heap. -/
def extend (state : State) (code : Code) (stack : List Word) : State :=
  ⟨state.register, state.code ++ code, state.stack ++ stack, state.heap⟩

/-- The remark in the proof of Proposition 3.1: a transition is unchanged by any
code suffix and any stack suffix. -/
theorem Transition.extend {before after : State} (transition : Transition before after) (code : Code)
    (stack : List Word) : Transition (Graph.extend before code stack) (Graph.extend after code stack) := by
  cases transition <;> simp only [Graph.extend, List.cons_append, List.append_assoc]
  all_goals first
    | exact .first _ _ _ ‹_›
    | exact .second _ _ _ ‹_›
    | exact .cur _ _ _ _ _
    | exact .push _ _ _ _
    | exact .swap _ _ _ _ _
    | exact .cons _ _ _ _ _
    | exact .app _ _ _ ‹_› ‹_›
    | exact .quote _ _ _ _ _
    | exact .branch _ _ _ _ _ _ _
    | exact .operation _ _ _ _ ‹_›
    | exact .wind _ _ _ _ ‹_›
    | exact .freeze _ _ _ _ _
    | exact .force _ _ _ ‹_›
    | exact .skip _ _ _ _ ‹_›

theorem Steps.extend {before after : State} (run : Steps before after) (code : Code) (stack : List Word) :
    Steps (Graph.extend before code stack) (Graph.extend after code stack) := by
  induction run with
  | refl => exact .refl
  | tail _ transition ih => exact ih.tail (transition.extend code stack)

/-- Executions counted by their number of transitions. -/
inductive StepsIn : Nat → State → State → Prop where
  | refl (state : State) : StepsIn 0 state state
  | head {count : Nat} {state next final : State} (transition : Transition state next)
      (rest : StepsIn count next final) : StepsIn (count + 1) state final

theorem StepsIn.steps {count : Nat} {state final : State} (run : StepsIn count state final) :
    Steps state final := by
  induction run with
  | refl => exact .refl
  | head transition _ ih => exact .head transition ih

theorem Steps.stepsIn {state final : State} (run : Steps state final) :
    ∃ count, StepsIn count state final := by
  induction run using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, .refl _⟩
  | head transition _ ih =>
      obtain ⟨count, rest⟩ := ih
      exact ⟨count + 1, .head transition rest⟩

theorem StepsIn.trans {first second : Nat} {state middle final : State}
    (one : StepsIn first state middle) (two : StepsIn second middle final) :
    StepsIn (first + second) state final := by
  induction one with
  | refl => simpa only [Nat.zero_add] using two
  | head transition _ ih =>
      simpa only [Nat.add_right_comm] using StepsIn.head transition (ih two)

/-- A run that stops with no code leaves any configuration that still has code
by an actual first transition. -/
theorem StepsIn.first_transition {count : Nat} {state final : State}
    (run : StepsIn count state final) (stopped : final.code = []) (pending : state.code ≠ []) :
    ∃ next rest, count = rest + 1 ∧ Transition state next ∧ StepsIn rest next final := by
  cases run with
  | refl => exact False.elim (pending stopped)
  | head transition rest => exact ⟨_, _, rfl, transition, rest⟩

/-! ## Representation of source values in the graph -/

theorem lookup_prefix {heap heap' : Heap} (extended : heap <+: heap') {address : Nat} {cell : Cell}
    (found : heap[address]? = some cell) : heap'[address]? = some cell := by
  obtain ⟨suffix, rfl⟩ := extended
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- A word represents a source value by a finite derivation. The recursive case
reads a closure node whose environment couple has the node itself as its right
component. This is a relation: the same node also represents the one-step
unfolding of the recursive value (`Represents.unfolding`). -/
inductive Represents (heap : Heap) : Word → Value → Prop where
  | unit : Represents heap .unit .unit
  | literal (value : Literal) : Represents heap (.literal value) (.literal value)
  | pair {address : Nat} {leftWord rightWord : Word} {left right : Value}
      (cell : heap[address]? = some (.pair leftWord rightWord))
      (leftRep : Represents heap leftWord left) (rightRep : Represents heap rightWord right) :
      Represents heap (.ref address) (.pair left right)
  | closure {address : Nat} {body : Term} {environmentWord : Word} {environment : Value}
      (cell : heap[address]? = some (.closure (compile body) environmentWord))
      (environmentRep : Represents heap environmentWord environment) :
      Represents heap (.ref address) (.closure body environment)
  | laze {address : Nat} {body : Term} {environmentWord : Word} {environment : Value}
      (cell : heap[address]? = some (.laze (compile body) environmentWord))
      (environmentRep : Represents heap environmentWord environment) :
      Represents heap (.ref address) (.laze body environment)
  | recursive {address couple : Nat} {body : Term} {environmentWord : Word} {environment : Value}
      (cell : heap[address]? = some (.closure (compile body) (.ref couple)))
      (coupleCell : heap[couple]? = some (.pair environmentWord (.ref address)))
      (environmentRep : Represents heap environmentWord environment) :
      Represents heap (.ref address) (.recursive body environment)

/-- Cells already present are kept by heap extension, so representation is too. -/
theorem Represents.mono {heap heap' : Heap} {word : Word} {value : Value}
    (represented : Represents heap word value) (extended : heap <+: heap') :
    Represents heap' word value := by
  induction represented with
  | unit => exact .unit
  | literal value => exact .literal value
  | pair cell _ _ leftIH rightIH => exact .pair (lookup_prefix extended cell) leftIH rightIH
  | closure cell _ ih => exact .closure (lookup_prefix extended cell) ih
  | laze cell _ ih => exact .laze (lookup_prefix extended cell) ih
  | recursive cell coupleCell _ ih =>
      exact .recursive (lookup_prefix extended cell) (lookup_prefix extended coupleCell) ih

/-- The cyclic node also represents the one-step unfolding of its recursive value. -/
theorem Represents.unfolding {heap : Heap} {address : Nat} {body : Term} {environment : Value}
    (represented : Represents heap (.ref address) (.recursive body environment)) :
    Represents heap (.ref address)
      (.closure body (.pair environment (.recursive body environment))) := by
  cases represented with
  | recursive cell coupleCell environmentRep =>
      exact .closure cell (.pair coupleCell environmentRep (.recursive cell coupleCell environmentRep))

/-- Representation is not a function: one cyclic node represents two distinct values. -/
theorem Represents.not_functional {heap : Heap} {address : Nat} {body : Term} {environment : Value}
    (represented : Represents heap (.ref address) (.recursive body environment)) :
    ∃ first second, first ≠ second ∧ Represents heap (.ref address) first ∧
      Represents heap (.ref address) second :=
  ⟨_, _, by simp, represented, represented.unfolding⟩

theorem Represents.pair_inv {heap : Heap} {address : Nat} {leftWord rightWord : Word} {value : Value}
    (represented : Represents heap (.ref address) value)
    (cell : heap[address]? = some (.pair leftWord rightWord)) :
    ∃ left right, value = .pair left right ∧ Represents heap leftWord left ∧
      Represents heap rightWord right := by
  cases represented with
  | pair found leftRep rightRep =>
      rw [cell] at found
      cases found
      exact ⟨_, _, rfl, leftRep, rightRep⟩
  | closure found _ | laze found _ | recursive found _ _ =>
      rw [cell] at found
      cases found

theorem Represents.laze_inv {heap : Heap} {address : Nat} {code : Code} {environmentWord : Word}
    {value : Value} (represented : Represents heap (.ref address) value)
    (cell : heap[address]? = some (.laze code environmentWord)) :
    ∃ body environment, value = .laze body environment ∧ code = compile body ∧
      Represents heap environmentWord environment := by
  cases represented with
  | laze found environmentRep =>
      rw [cell] at found
      cases found
      exact ⟨_, _, rfl, rfl, environmentRep⟩
  | pair found _ _ | closure found _ | recursive found _ _ =>
      rw [cell] at found
      cases found

/-- A represented value that is not a laze is not stored in a laze cell. -/
theorem Represents.not_lazeAt {heap : Heap} {word : Word} {value : Value}
    (represented : Represents heap word value) (notLaze : value.NotLaze) : ¬ LazeAt heap word := by
  rintro ⟨address, body, environment, rfl, cell⟩
  obtain ⟨_, _, rfl, _, _⟩ := represented.laze_inv cell
  exact notLaze

theorem Represents.laze_cell {heap : Heap} {word : Word} {body : Term} {environment : Value}
    (represented : Represents heap word (.laze body environment)) :
    ∃ address environmentWord, word = .ref address ∧
      heap[address]? = some (.laze (compile body) environmentWord) ∧
      Represents heap environmentWord environment := by
  cases represented with
  | laze cell environmentRep => exact ⟨_, _, rfl, cell, environmentRep⟩

theorem Represents.literal_inv {heap : Heap} {word : Word} {value : Literal}
    (represented : Represents heap word (.literal value)) : word = .literal value := by
  cases represented
  rfl

theorem Represents.pair_cell {heap : Heap} {word : Word} {left right : Value}
    (represented : Represents heap word (.pair left right)) :
    ∃ address leftWord rightWord, word = .ref address ∧
      heap[address]? = some (.pair leftWord rightWord) ∧
      Represents heap leftWord left ∧ Represents heap rightWord right := by
  cases represented with
  | pair cell leftRep rightRep => exact ⟨_, _, _, rfl, cell, leftRep, rightRep⟩

theorem Represents.closure_cell {heap : Heap} {word : Word} {body : Term} {environment : Value}
    (represented : Represents heap word (.closure body environment)) :
    ∃ address environmentWord, word = .ref address ∧
      heap[address]? = some (.closure (compile body) environmentWord) ∧
      Represents heap environmentWord environment := by
  cases represented with
  | closure cell environmentRep => exact ⟨_, _, rfl, cell, environmentRep⟩

theorem Represents.recursive_cell {heap : Heap} {word : Word} {body : Term} {environment : Value}
    (represented : Represents heap word (.recursive body environment)) :
    ∃ address couple environmentWord, word = .ref address ∧
      heap[address]? = some (.closure (compile body) (.ref couple)) ∧
      heap[couple]? = some (.pair environmentWord (.ref address)) ∧
      Represents heap environmentWord environment := by
  cases represented with
  | recursive cell coupleCell environmentRep => exact ⟨_, _, _, rfl, cell, coupleCell, environmentRep⟩


/-! ## Soundness -/

/-- The heap after the recursion code of Section 4: the couple `(s, c)` and the
closure `c = C:(s, c)` that addresses it. -/
def windHeap (heap : Heap) (word : Word) (body : Code) : Heap :=
  heap ++ [.pair word (.ref (heap.length + 1)), .closure body (.ref heap.length)]

theorem windHeap_eq (heap : Heap) (word : Word) (body : Code) :
    (heap ++ [Cell.pair word (.literal .unit)] ++ [Cell.closure body (.ref heap.length)]).set
        heap.length (.pair word (.ref (heap ++ [Cell.pair word (.literal .unit)]).length)) =
      windHeap heap word body := by
  simp [windHeap, List.append_assoc, List.set_append_right]

theorem windHeap_couple (heap : Heap) (word : Word) (body : Code) :
    (windHeap heap word body)[heap.length]? = some (.pair word (.ref (heap.length + 1))) := by
  simp [windHeap]

theorem windHeap_closure (heap : Heap) (word : Word) (body : Code) :
    (windHeap heap word body)[heap.length + 1]? = some (.closure body (.ref heap.length)) := by
  simp [windHeap]

theorem windHeap_prefix (heap : Heap) (word : Word) (body : Code) : heap <+: windHeap heap word body :=
  List.prefix_append _ _

/-- The six instructions of `F(C)` build the cyclic closure in place. -/
theorem fix_run (word : Word) (body code : Code) (stack : List Word) (heap : Heap) :
    Steps ⟨word, [.push, .quote .unit, .cons, .push, .cur body, .wind] ++ code, stack, heap⟩
      ⟨.ref (heap.length + 1), code, stack, windHeap heap word body⟩ := by
  have wound := Transition.wind (address := heap.length) (left := word) (right := .literal .unit)
    (.ref (heap ++ [Cell.pair word (.literal .unit)]).length) code stack
    (heap ++ [Cell.pair word (.literal .unit)] ++ [Cell.closure body (.ref heap.length)])
    (by simp)
  have run : Steps ⟨word, [.push, .quote .unit, .cons, .push, .cur body, .wind] ++ code, stack, heap⟩
      ⟨.ref (heap ++ [Cell.pair word (.literal .unit)]).length, code, stack,
        (heap ++ [Cell.pair word (.literal .unit)] ++ [Cell.closure body (.ref heap.length)]).set
          heap.length (.pair word (.ref (heap ++ [Cell.pair word (.literal .unit)]).length))⟩ :=
    .head (.push _ _ _ _) (.head (.quote _ _ _ _ _) (.head (.cons _ _ _ _ _)
      (.head (.push _ _ _ _) (.head (.cur _ _ _ _ _) (.single wound)))))
  rw [windHeap_eq, List.length_append, List.length_singleton] at run
  exact run

theorem allocated {heap : Heap} {cell : Cell} : (heap ++ [cell])[heap.length]? = some cell :=
  List.getElem?_concat_length

mutual
/-- Soundness (the analogue of Proposition 3.1, left to right): compiled code
runs from any word representing the environment to a word representing the
value, with arbitrary caller code and stack retained. Cells present before the
run are never changed. -/
theorem Evaluation.execution : {term : Term} → {environment value : Value} → {heap : Heap} →
    {word : Word} → Evaluation term environment value → Represents heap word environment →
    (code : Code) → (stack : List Word) →
    ∃ result final, Steps ⟨word, compile term ++ code, stack, heap⟩ ⟨result, code, stack, final⟩ ∧
      heap <+: final ∧ Represents final result value
  | _, _, _, heap, _, .varZero _ _, represented, code, stack => by
      obtain ⟨address, _, rightWord, rfl, cell, _, rightRep⟩ := represented.pair_cell
      exact ⟨rightWord, heap, .single (.second code stack heap cell), List.prefix_refl _, rightRep⟩
  | _, _, _, heap, word, .varSucc _ rest, represented, code, stack => by
      obtain ⟨address, leftWord, _, rfl, cell, leftRep, _⟩ := represented.pair_cell
      obtain ⟨result, final, run, extended, resultRep⟩ := Evaluation.execution rest leftRep code stack
      refine ⟨result, final, ?_, extended, resultRep⟩
      rw [compile_var_succ, List.cons_append]
      exact .head (.first _ _ _ cell) run
  | _, _, _, heap, word, .literal value _, _, code, stack => by
      exact ⟨.literal value, heap, .single (.quote _ _ _ _ _), List.prefix_refl _, .literal value⟩
  | _, _, _, heap, word, .lam body _, represented, code, stack => by
      exact ⟨.ref heap.length, heap ++ [.closure (compile body) word], .single (.cur _ _ _ _ _),
        List.prefix_append _ _, .closure allocated (represented.mono (List.prefix_append _ _))⟩
  | _, _, _, heap, word, .fix body _, represented, code, stack => by
      exact ⟨.ref (heap.length + 1), windHeap heap word (compile body), fix_run word _ code stack heap,
        windHeap_prefix _ _ _, .recursive (windHeap_closure _ _ _) (windHeap_couple _ _ _)
          (represented.mono (windHeap_prefix _ _ _))⟩
  | _, _, _, heap, word, .freeze body _, represented, code, stack => by
      exact ⟨.ref heap.length, heap ++ [.laze (compile body) word], .single (.freeze _ _ _ _ _),
        List.prefix_append _ _, .laze allocated (represented.mono (List.prefix_append _ _))⟩
  | _, _, _, heap, word, .pair (left := left) (right := right) leftEval rightEval, represented, code, stack => by
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append]
      obtain ⟨leftWord, heap₁, leftRun, extended₁, leftRep⟩ :=
        Evaluation.execution leftEval represented (.swap :: (compile right ++ .cons :: code)) (word :: stack)
      obtain ⟨rightWord, heap₂, rightRun, extended₂, rightRep⟩ :=
        Evaluation.execution rightEval (represented.mono extended₁) (.cons :: code) (leftWord :: stack)
      have extended₃ : heap₂ <+: heap₂ ++ [Cell.pair leftWord rightWord] := List.prefix_append _ _
      refine ⟨.ref heap₂.length, heap₂ ++ [.pair leftWord rightWord], ?_,
        extended₁.trans (extended₂.trans extended₃),
        .pair allocated ((leftRep.mono extended₂).mono extended₃) (rightRep.mono extended₃)⟩
      exact .head (.push _ _ _ _) (leftRun.trans (.head (.swap _ _ _ _ _)
        (rightRun.trans (.single (.cons _ _ _ _ _)))))
  | _, _, _, heap, word, .first (term := term) termEval forced, represented, code, stack => by
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append]
      obtain ⟨beforeWord, heap₁, termRun, extended₁, beforeRep⟩ :=
        Evaluation.execution termEval represented (.unfreeze :: .first :: code) stack
      obtain ⟨coupleWord, heap₂, forceRun, extended₂, coupleRep⟩ :=
        Force.execution forced beforeRep (.first :: code) stack
      obtain ⟨address, leftWord, _, rfl, cell, leftRep, _⟩ := coupleRep.pair_cell
      exact ⟨leftWord, heap₂, termRun.trans (forceRun.tail (.first _ _ _ cell)),
        extended₁.trans extended₂, leftRep⟩
  | _, _, _, heap, word, .second (term := term) termEval forced, represented, code, stack => by
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append]
      obtain ⟨beforeWord, heap₁, termRun, extended₁, beforeRep⟩ :=
        Evaluation.execution termEval represented (.unfreeze :: .second :: code) stack
      obtain ⟨coupleWord, heap₂, forceRun, extended₂, coupleRep⟩ :=
        Force.execution forced beforeRep (.second :: code) stack
      obtain ⟨address, _, rightWord, rfl, cell, _, rightRep⟩ := coupleRep.pair_cell
      exact ⟨rightWord, heap₂, termRun.trans (forceRun.tail (.second _ _ _ cell)),
        extended₁.trans extended₂, rightRep⟩
  | _, _, _, heap, word, .app (operator := operator) (argument := argument) operatorEval argumentEval forced
      invocation, represented, code, stack => by
      simp only [compile, forceOperator, List.append_assoc, List.cons_append, List.nil_append]
      obtain ⟨functionWord, heap₁, operatorRun, extended₁, functionRep⟩ :=
        Evaluation.execution operatorEval represented
          (.swap :: (compile argument ++ [.cons, .push, .first, .unfreeze, .swap, .second, .cons, .app] ++
            code)) (word :: stack)
      obtain ⟨argumentWord, heap₂, argumentRun, extended₂, argumentRep⟩ :=
        Evaluation.execution argumentEval (represented.mono extended₁)
          (.cons :: .push :: .first :: .unfreeze :: .swap :: .second :: .cons :: .app :: code)
          (functionWord :: stack)
      have extended₃ : heap₂ <+: heap₂ ++ [Cell.pair functionWord argumentWord] := List.prefix_append _ _
      obtain ⟨calleeWord, heap₄, forceRun, extended₄, calleeRep⟩ :=
        Force.execution forced ((functionRep.mono extended₂).mono extended₃)
          (.swap :: .second :: .cons :: .app :: code) (.ref heap₂.length :: stack)
      have couple₄ := lookup_prefix extended₄ (allocated (heap := heap₂))
      have extended₅ : heap₄ <+: heap₄ ++ [Cell.pair calleeWord argumentWord] := List.prefix_append _ _
      obtain ⟨result, heap₆, callRun, extended₆, resultRep⟩ :=
        Invocation.execution invocation allocated (calleeRep.mono extended₅)
          (((argumentRep.mono extended₃).mono extended₄).mono extended₅) code stack
      refine ⟨result, heap₆, ?_,
        extended₁.trans (extended₂.trans (extended₃.trans (extended₄.trans (extended₅.trans extended₆)))),
        resultRep⟩
      have argumentRun' : Steps ⟨word, compile argument ++ .cons :: .push :: .first :: .unfreeze :: .swap ::
          .second :: .cons :: .app :: code, functionWord :: stack, heap₁⟩
          ⟨argumentWord, .cons :: .push :: .first :: .unfreeze :: .swap :: .second :: .cons :: .app :: code,
            functionWord :: stack, heap₂⟩ := argumentRun
      simp only [List.cons_append, List.nil_append, List.append_assoc] at operatorRun
      exact .head (.push _ _ _ _) (operatorRun.trans (.head (.swap _ _ _ _ _) (argumentRun'.trans
        (.head (.cons _ _ _ _ _) (.head (.push _ _ _ _) (.head (.first _ _ _ allocated)
          (forceRun.trans (.head (.swap _ _ _ _ _) (.head (.second _ _ _ couple₄)
            (.head (.cons _ _ _ _ _) callRun))))))))))
  | _, _, _, heap, word, .conditional (whenTrue := whenTrue) (whenFalse := whenFalse) (selected := selected)
      conditionEval forced selectedEval, represented, code, stack => by
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append]
      obtain ⟨conditionWord, heap₁, conditionRun, extended₁, conditionRep⟩ :=
        Evaluation.execution conditionEval represented
          (.unfreeze :: .branch (compile whenTrue) (compile whenFalse) :: code) (word :: stack)
      obtain ⟨testWord, heap₂, forceRun, extended₂, testRep⟩ :=
        Force.execution forced conditionRep (.branch (compile whenTrue) (compile whenFalse) :: code)
          (word :: stack)
      have testWord_eq := testRep.literal_inv
      subst testWord_eq
      obtain ⟨result, heap₃, selectedRun, extended₃, resultRep⟩ :=
        Evaluation.execution selectedEval ((represented.mono extended₁).mono extended₂) code stack
      refine ⟨result, heap₃, ?_, extended₁.trans (extended₂.trans extended₃), resultRep⟩
      have chosen := Transition.branch selected word (compile whenTrue) (compile whenFalse) code stack heap₂
      cases selected
      · exact .head (.push _ _ _ _) (conditionRun.trans (forceRun.trans (.head chosen selectedRun)))
      · exact .head (.push _ _ _ _) (conditionRun.trans (forceRun.trans (.head chosen selectedRun)))
  | _, _, _, heap, word, .primitive (operation := operation) (argument := argument)
      (leftValue := leftValue) (rightValue := rightValue) argumentEval forced leftForced rightForced,
      represented, code, stack => by
      simp only [compile, forceOperands, List.append_assoc, List.cons_append, List.nil_append]
      obtain ⟨beforeWord, heap₁, argumentRun, extended₁, beforeRep⟩ :=
        Evaluation.execution argumentEval represented
          (.unfreeze :: .push :: .first :: .unfreeze :: .swap :: .second :: .unfreeze :: .cons ::
            .operation operation :: code) stack
      obtain ⟨coupleWord, heap₂, coupleRun, extended₂, coupleRep⟩ :=
        Force.execution forced beforeRep
          (.push :: .first :: .unfreeze :: .swap :: .second :: .unfreeze :: .cons :: .operation operation ::
            code) stack
      obtain ⟨address, leftWord, rightWord, rfl, cell, leftRep, rightRep⟩ := coupleRep.pair_cell
      obtain ⟨leftResult, heap₃, leftRun, extended₃, leftResultRep⟩ :=
        Force.execution leftForced leftRep
          (.swap :: .second :: .unfreeze :: .cons :: .operation operation :: code) (.ref address :: stack)
      have leftResult_eq := leftResultRep.literal_inv
      subst leftResult_eq
      obtain ⟨rightResult, heap₄, rightRun, extended₄, rightResultRep⟩ :=
        Force.execution rightForced (rightRep.mono extended₃)
          (.cons :: .operation operation :: code) (.literal (.integer leftValue) :: stack)
      have rightResult_eq := rightResultRep.literal_inv
      subst rightResult_eq
      have extended₅ : heap₄ <+: heap₄ ++
          [Cell.pair (.literal (.integer leftValue)) (.literal (.integer rightValue))] :=
        List.prefix_append _ _
      refine ⟨_, _, ?_, extended₁.trans (extended₂.trans (extended₃.trans (extended₄.trans extended₅))),
        .literal _⟩
      exact argumentRun.trans (coupleRun.trans (.head (.push _ _ _ _) (.head (.first _ _ _ cell)
        (leftRun.trans (.head (.swap _ _ _ _ _) (.head (.second _ _ _ (lookup_prefix extended₃ cell))
          (rightRun.trans (.head (.cons _ _ _ _ _) (.single (.operation _ _ _ _ allocated))))))))))
/-- Soundness of `app` on a couple whose left component represents a forced function. -/
theorem Invocation.execution : {function argument value : Value} → {heap : Heap} →
    {address : Nat} → {functionWord argumentWord : Word} → Invocation function argument value →
    heap[address]? = some (.pair functionWord argumentWord) →
    Represents heap functionWord function → Represents heap argumentWord argument →
    (code : Code) → (stack : List Word) →
    ∃ result final, Steps ⟨.ref address, .app :: code, stack, heap⟩ ⟨result, code, stack, final⟩ ∧
      heap <+: final ∧ Represents final result value
  | _, _, _, heap, _, _, argumentWord, .closure bodyEval, couple, functionRep, argumentRep, code, stack => by
      obtain ⟨_, environmentWord, rfl, cell, environmentRep⟩ := functionRep.closure_cell
      have extended : heap <+: heap ++ [Cell.pair environmentWord argumentWord] := List.prefix_append _ _
      obtain ⟨result, final, bodyRun, extended', resultRep⟩ :=
        Evaluation.execution bodyEval
          (.pair allocated (environmentRep.mono extended) (argumentRep.mono extended)) code stack
      exact ⟨result, final, .head (.app _ _ _ couple cell) bodyRun, extended.trans extended', resultRep⟩
  | _, _, _, heap, _, _, argumentWord, .recursive bodyEval, couple, functionRep, argumentRep, code,
      stack => by
      obtain ⟨_, environmentCouple, environmentWord, rfl, cell, coupleCell, environmentRep⟩ :=
        functionRep.recursive_cell
      have extended : heap <+: heap ++ [Cell.pair (.ref environmentCouple) argumentWord] :=
        List.prefix_append _ _
      have selfRep := (Represents.recursive cell coupleCell environmentRep).mono extended
      obtain ⟨result, final, bodyRun, extended', resultRep⟩ :=
        Evaluation.execution bodyEval
          (.pair allocated (.pair (lookup_prefix extended coupleCell) (environmentRep.mono extended) selfRep)
            (argumentRep.mono extended)) code stack
      exact ⟨result, final, .head (.app _ _ _ couple cell) bodyRun, extended.trans extended', resultRep⟩
/-- Soundness of `unfreeze`: repetitive forcing runs each laze body and stops at
the first value that is not a laze. -/
theorem Force.execution : {value result : Value} → {heap : Heap} → {word : Word} →
    Force value result → Represents heap word value → (code : Code) → (stack : List Word) →
    ∃ forced final, Steps ⟨word, .unfreeze :: code, stack, heap⟩ ⟨forced, code, stack, final⟩ ∧
      heap <+: final ∧ Represents final forced result
  | _, _, _, _, .laze bodyEval again, represented, code, stack => by
      obtain ⟨address, environmentWord, rfl, cell, environmentRep⟩ := represented.laze_cell
      obtain ⟨valueWord, heap₁, bodyRun, extended₁, valueRep⟩ :=
        Evaluation.execution bodyEval environmentRep (.unfreeze :: code) stack
      obtain ⟨forced, heap₂, againRun, extended₂, forcedRep⟩ := Force.execution again valueRep code stack
      exact ⟨forced, heap₂, .head (.force _ _ _ cell) (bodyRun.trans againRun),
        extended₁.trans extended₂, forcedRep⟩
  | _, _, heap, word, .value _ notLaze, represented, code, stack => by
      exact ⟨word, heap, .single (.skip _ _ _ _ (represented.not_lazeAt notLaze)), List.prefix_refl _,
        represented⟩
end


/-! ## Completeness

A completed run is followed backwards through counted transitions. Each
instruction of compiled code either takes its unique transition or leaves a
stopped configuration that still has code, which cannot be the completed end.
The run therefore passes through the return point of every evaluated subterm,
of every forced value and of every invocation, with fewer remaining transitions.
-/

section Inversion

variable {count : Nat} {word : Word} {code : Code} {stack : List Word} {heap : Heap} {final : State}

theorem StepsIn.push_inv (run : StepsIn count ⟨word, .push :: code, stack, heap⟩ final)
    (stopped : final.code = []) :
    ∃ rest, count = rest + 1 ∧ StepsIn rest ⟨word, code, word :: stack, heap⟩ final := by
  obtain ⟨next, rest, rfl, transition, run⟩ := run.first_transition stopped (by simp)
  cases transition
  exact ⟨rest, rfl, run⟩

theorem StepsIn.swap_inv {saved : Word} (run : StepsIn count ⟨word, .swap :: code, saved :: stack, heap⟩ final)
    (stopped : final.code = []) :
    ∃ rest, count = rest + 1 ∧ StepsIn rest ⟨saved, code, word :: stack, heap⟩ final := by
  obtain ⟨next, rest, rfl, transition, run⟩ := run.first_transition stopped (by simp)
  cases transition
  exact ⟨rest, rfl, run⟩

theorem StepsIn.cons_inv {saved : Word} (run : StepsIn count ⟨word, .cons :: code, saved :: stack, heap⟩ final)
    (stopped : final.code = []) :
    ∃ rest, count = rest + 1 ∧
      StepsIn rest ⟨.ref heap.length, code, stack, heap ++ [.pair saved word]⟩ final := by
  obtain ⟨next, rest, rfl, transition, run⟩ := run.first_transition stopped (by simp)
  cases transition
  exact ⟨rest, rfl, run⟩

theorem StepsIn.quote_inv {value : Literal} (run : StepsIn count ⟨word, .quote value :: code, stack, heap⟩ final)
    (stopped : final.code = []) :
    ∃ rest, count = rest + 1 ∧ StepsIn rest ⟨.literal value, code, stack, heap⟩ final := by
  obtain ⟨next, rest, rfl, transition, run⟩ := run.first_transition stopped (by simp)
  cases transition
  exact ⟨rest, rfl, run⟩

theorem StepsIn.cur_inv {body : Code} (run : StepsIn count ⟨word, .cur body :: code, stack, heap⟩ final)
    (stopped : final.code = []) :
    ∃ rest, count = rest + 1 ∧
      StepsIn rest ⟨.ref heap.length, code, stack, heap ++ [.closure body word]⟩ final := by
  obtain ⟨next, rest, rfl, transition, run⟩ := run.first_transition stopped (by simp)
  cases transition
  exact ⟨rest, rfl, run⟩

theorem StepsIn.freeze_inv {body : Code} (run : StepsIn count ⟨word, .freeze body :: code, stack, heap⟩ final)
    (stopped : final.code = []) :
    ∃ rest, count = rest + 1 ∧
      StepsIn rest ⟨.ref heap.length, code, stack, heap ++ [.laze body word]⟩ final := by
  obtain ⟨next, rest, rfl, transition, run⟩ := run.first_transition stopped (by simp)
  cases transition
  exact ⟨rest, rfl, run⟩

theorem StepsIn.first_inv (run : StepsIn count ⟨word, .first :: code, stack, heap⟩ final)
    (stopped : final.code = []) :
    ∃ address left right rest, word = .ref address ∧ heap[address]? = some (.pair left right) ∧
      count = rest + 1 ∧ StepsIn rest ⟨left, code, stack, heap⟩ final := by
  obtain ⟨next, rest, rfl, transition, run⟩ := run.first_transition stopped (by simp)
  cases transition with
  | first _ _ _ cell => exact ⟨_, _, _, rest, rfl, cell, rfl, run⟩

theorem StepsIn.second_inv (run : StepsIn count ⟨word, .second :: code, stack, heap⟩ final)
    (stopped : final.code = []) :
    ∃ address left right rest, word = .ref address ∧ heap[address]? = some (.pair left right) ∧
      count = rest + 1 ∧ StepsIn rest ⟨right, code, stack, heap⟩ final := by
  obtain ⟨next, rest, rfl, transition, run⟩ := run.first_transition stopped (by simp)
  cases transition with
  | second _ _ _ cell => exact ⟨_, _, _, rest, rfl, cell, rfl, run⟩

theorem StepsIn.app_inv (run : StepsIn count ⟨word, .app :: code, stack, heap⟩ final)
    (stopped : final.code = []) :
    ∃ address function argument body environment rest, word = .ref address ∧
      heap[address]? = some (.pair (.ref function) argument) ∧
      heap[function]? = some (.closure body environment) ∧ count = rest + 1 ∧
      StepsIn rest ⟨.ref heap.length, body ++ code, stack, heap ++ [.pair environment argument]⟩ final := by
  obtain ⟨next, rest, rfl, transition, run⟩ := run.first_transition stopped (by simp)
  cases transition with
  | app _ _ _ couple closure => exact ⟨_, _, _, _, _, rest, rfl, couple, closure, rfl, run⟩

theorem StepsIn.branch_inv {saved : Word} {whenTrue whenFalse : Code}
    (run : StepsIn count ⟨word, .branch whenTrue whenFalse :: code, saved :: stack, heap⟩ final)
    (stopped : final.code = []) :
    ∃ selected rest, word = .literal (.boolean selected) ∧ count = rest + 1 ∧
      StepsIn rest ⟨saved, (if selected then whenTrue else whenFalse) ++ code, stack, heap⟩ final := by
  obtain ⟨next, rest, rfl, transition, run⟩ := run.first_transition stopped (by simp)
  cases transition with
  | branch selected => exact ⟨selected, rest, rfl, rfl, run⟩

theorem StepsIn.operation_inv {primitive : Primitive}
    (run : StepsIn count ⟨word, .operation primitive :: code, stack, heap⟩ final)
    (stopped : final.code = []) :
    ∃ address left right rest, word = .ref address ∧
      heap[address]? = some (.pair (.literal (.integer left)) (.literal (.integer right))) ∧
      count = rest + 1 ∧ StepsIn rest ⟨.literal (primitive.apply left right), code, stack, heap⟩ final := by
  obtain ⟨next, rest, rfl, transition, run⟩ := run.first_transition stopped (by simp)
  cases transition with
  | operation _ _ _ _ cell => exact ⟨_, _, _, rest, rfl, cell, rfl, run⟩

theorem StepsIn.wind_inv {address : Nat}
    (run : StepsIn count ⟨word, .wind :: code, .ref address :: stack, heap⟩ final)
    (stopped : final.code = []) :
    ∃ left right rest, heap[address]? = some (.pair left right) ∧ count = rest + 1 ∧
      StepsIn rest ⟨word, code, stack, heap.set address (.pair left word)⟩ final := by
  obtain ⟨next, rest, rfl, transition, run⟩ := run.first_transition stopped (by simp)
  cases transition with
  | wind _ _ _ _ cell => exact ⟨_, _, rest, cell, rfl, run⟩

theorem StepsIn.unfreeze_inv (run : StepsIn count ⟨word, .unfreeze :: code, stack, heap⟩ final)
    (stopped : final.code = []) :
    (∃ address body environment rest, word = .ref address ∧
        heap[address]? = some (.laze body environment) ∧ count = rest + 1 ∧
        StepsIn rest ⟨environment, body ++ .unfreeze :: code, stack, heap⟩ final) ∨
      (∃ rest, ¬ LazeAt heap word ∧ count = rest + 1 ∧ StepsIn rest ⟨word, code, stack, heap⟩ final) := by
  obtain ⟨next, rest, rfl, transition, run⟩ := run.first_transition stopped (by simp)
  cases transition with
  | force _ _ _ cell => exact .inl ⟨_, _, _, rest, rfl, cell, rfl, run⟩
  | skip _ _ _ _ notLaze => exact .inr ⟨rest, notLaze, rfl, run⟩

end Inversion

/-- A word in a closure cell represents a closure of that code or the recursive
value whose couple points back at the cell. -/
theorem Represents.closure_inv {heap : Heap} {address : Nat} {body : Code} {environmentWord : Word}
    {value : Value} (represented : Represents heap (.ref address) value)
    (cell : heap[address]? = some (.closure body environmentWord)) :
    (∃ source environment, value = .closure source environment ∧ body = compile source ∧
        Represents heap environmentWord environment) ∨
    (∃ source environment couple coupleWord, value = .recursive source environment ∧
        body = compile source ∧ environmentWord = .ref couple ∧
        heap[couple]? = some (.pair coupleWord (.ref address)) ∧
        Represents heap coupleWord environment) := by
  cases represented with
  | closure found environmentRep =>
      rw [cell] at found
      cases found
      exact .inl ⟨_, _, rfl, rfl, environmentRep⟩
  | recursive found coupleCell environmentRep =>
      rw [cell] at found
      cases found
      exact .inr ⟨_, _, _, _, rfl, rfl, rfl, coupleCell, environmentRep⟩
  | pair found _ _ | laze found _ =>
      rw [cell] at found
      cases found

theorem Represents.notLaze {heap : Heap} {word : Word} {value : Value}
    (represented : Represents heap word value) (notLaze : ¬ LazeAt heap word) : value.NotLaze := by
  cases represented with
  | laze cell _ => exact notLaze ⟨_, _, _, rfl, cell⟩
  | unit | literal _ | pair _ _ _ | closure _ _ | recursive _ _ _ => trivial

/-- Return points of compiled evaluation within a counted completed run. -/
private def EvaluationReturns (count : Nat) : Prop :=
  ∀ (term : Term) (environment : Value) (heap : Heap) (word : Word) (code : Code) (stack : List Word)
    (final : State), Represents heap word environment →
    StepsIn count ⟨word, compile term ++ code, stack, heap⟩ final → final.code = [] →
    ∃ value result heap' rest, Evaluation term environment value ∧ Represents heap' result value ∧
      heap <+: heap' ∧ rest < count ∧ StepsIn rest ⟨result, code, stack, heap'⟩ final

/-- Return points of `unfreeze` within a counted completed run. -/
private def ForceReturns (count : Nat) : Prop :=
  ∀ (value : Value) (heap : Heap) (word : Word) (code : Code) (stack : List Word) (final : State),
    Represents heap word value → StepsIn count ⟨word, .unfreeze :: code, stack, heap⟩ final →
    final.code = [] →
    ∃ forced result heap' rest, Force value forced ∧ Represents heap' result forced ∧
      heap <+: heap' ∧ rest < count ∧ StepsIn rest ⟨result, code, stack, heap'⟩ final

/-- Return points of `app` within a counted completed run. -/
private def InvocationReturns (count : Nat) : Prop :=
  ∀ (function argument : Value) (heap : Heap) (address : Nat) (functionWord argumentWord : Word)
    (code : Code) (stack : List Word) (final : State),
    heap[address]? = some (.pair functionWord argumentWord) → Represents heap functionWord function →
    Represents heap argumentWord argument → StepsIn count ⟨.ref address, .app :: code, stack, heap⟩ final →
    final.code = [] →
    ∃ value result heap' rest, Invocation function argument value ∧ Represents heap' result value ∧
      heap <+: heap' ∧ rest < count ∧ StepsIn rest ⟨result, code, stack, heap'⟩ final

private theorem returns (count : Nat) :
    EvaluationReturns count ∧ ForceReturns count ∧ InvocationReturns count := by
  induction count using Nat.strong_induction_on with
  | _ count ih =>
  have forceReturns : ForceReturns count := by
    intro value heap word code stack final represented run₀ stopped
    rcases run₀.unfreeze_inv stopped with
      ⟨address, body, environmentWord, rest, rfl, cell, rfl, run₁⟩ | ⟨rest, notLaze, rfl, run₁⟩
    · obtain ⟨source, environment, rfl, rfl, environmentRep⟩ := represented.laze_inv cell
      obtain ⟨value, result, heap₁, rest₁, evaluated, valueRep, extended₁, less₁, run₂⟩ :=
        (ih rest (by omega)).1 source environment heap environmentWord (.unfreeze :: code) stack final
          environmentRep run₁ stopped
      obtain ⟨forced, result₂, heap₂, rest₂, again, forcedRep, extended₂, less₂, run₃⟩ :=
        (ih rest₁ (by omega)).2.1 value heap₁ result code stack final valueRep run₂ stopped
      exact ⟨forced, result₂, heap₂, rest₂, .laze evaluated again, forcedRep, extended₁.trans extended₂,
        by omega, run₃⟩
    · exact ⟨value, word, heap, rest, .value value (represented.notLaze notLaze), represented,
        List.prefix_refl _, by omega, run₁⟩
  have invocationReturns : InvocationReturns count := by
    intro function argument heap address functionWord argumentWord code stack final couple functionRep
      argumentRep run₀ stopped
    obtain ⟨address', function', argument', body, environmentWord, rest, same, couple', closure, rfl, run₁⟩ :=
      run₀.app_inv stopped
    cases same
    rw [couple] at couple'
    cases couple'
    have extended : heap <+: heap ++ [Cell.pair environmentWord argumentWord] := List.prefix_append _ _
    rcases functionRep.closure_inv closure with
      ⟨source, environment, rfl, rfl, environmentRep⟩ |
      ⟨source, environment, coupleAddress, coupleWord, rfl, rfl, rfl, coupleCell, environmentRep⟩
    · obtain ⟨value, result, heap', rest', evaluated, valueRep, extended', less, run₂⟩ :=
        (ih rest (by omega)).1 source (.pair environment argument) _ _ code stack final
          (.pair allocated (environmentRep.mono extended) (argumentRep.mono extended)) run₁ stopped
      exact ⟨value, result, heap', rest', .closure evaluated, valueRep, extended.trans extended', by omega, run₂⟩
    · have selfRep := (Represents.recursive closure coupleCell environmentRep).mono extended
      obtain ⟨value, result, heap', rest', evaluated, valueRep, extended', less, run₂⟩ :=
        (ih rest (by omega)).1 source (.pair (.pair environment (.recursive source environment)) argument) _ _
          code stack final
          (.pair allocated (.pair (lookup_prefix extended coupleCell) (environmentRep.mono extended) selfRep)
            (argumentRep.mono extended)) run₁ stopped
      exact ⟨value, result, heap', rest', .recursive evaluated, valueRep, extended.trans extended', by omega,
        run₂⟩
  have evaluationReturns : EvaluationReturns count := by
    intro term
    induction term with
    | var index =>
        intro environment heap word code stack final represented run₀ stopped
        cases index with
        | zero =>
            obtain ⟨address, left, right, rest, rfl, cell, rfl, run₁⟩ :=
              StepsIn.second_inv (code := code) run₀ stopped
            obtain ⟨_, value, rfl, _, valueRep⟩ := represented.pair_inv cell
            exact ⟨value, right, heap, rest, .varZero _ value, valueRep, List.prefix_refl _, by omega, run₁⟩
        | succ index =>
            rw [compile_var_succ, List.cons_append] at run₀
            obtain ⟨address, left, right, rest, rfl, cell, rfl, run₁⟩ := run₀.first_inv stopped
            obtain ⟨environment', saved, rfl, environmentRep, _⟩ := represented.pair_inv cell
            obtain ⟨value, result, heap', rest', evaluated, valueRep, extended, less, run₂⟩ :=
              (ih rest (by omega)).1 (.var index) environment' heap left code stack final environmentRep run₁
                stopped
            exact ⟨value, result, heap', rest', .varSucc saved evaluated, valueRep, extended, by omega, run₂⟩
    | literal value =>
        intro environment heap word code stack final represented run₀ stopped
        obtain ⟨rest, rfl, run₁⟩ := StepsIn.quote_inv (code := code) run₀ stopped
        exact ⟨.literal value, .literal value, heap, rest, .literal value environment, .literal value,
          List.prefix_refl _, by omega, run₁⟩
    | lam body _ =>
        intro environment heap word code stack final represented run₀ stopped
        obtain ⟨rest, rfl, run₁⟩ := StepsIn.cur_inv (code := code) run₀ stopped
        exact ⟨.closure body environment, _, _, rest, .lam body environment,
          .closure allocated (represented.mono (List.prefix_append _ _)), List.prefix_append _ _, by omega,
          run₁⟩
    | freeze body _ =>
        intro environment heap word code stack final represented run₀ stopped
        obtain ⟨rest, rfl, run₁⟩ := StepsIn.freeze_inv (code := code) run₀ stopped
        exact ⟨.laze body environment, _, _, rest, .freeze body environment,
          .laze allocated (represented.mono (List.prefix_append _ _)), List.prefix_append _ _, by omega, run₁⟩
    | fix body _ =>
        intro environment heap word code stack final represented run₀ stopped
        simp only [compile, List.cons_append, List.nil_append] at run₀
        obtain ⟨rest₁, rfl, run₁⟩ := run₀.push_inv stopped
        obtain ⟨rest₂, rfl, run₂⟩ := run₁.quote_inv stopped
        obtain ⟨rest₃, rfl, run₃⟩ := run₂.cons_inv stopped
        obtain ⟨rest₄, rfl, run₄⟩ := run₃.push_inv stopped
        obtain ⟨rest₅, rfl, run₅⟩ := run₄.cur_inv stopped
        obtain ⟨left, right, rest₆, cell, rfl, run₆⟩ := run₅.wind_inv stopped
        have couple : (heap ++ [Cell.pair word (.literal .unit)] ++
            [Cell.closure (compile body) (.ref heap.length)])[heap.length]? =
              some (.pair word (.literal .unit)) := by simp
        rw [couple] at cell
        cases cell
        rw [windHeap_eq, List.length_append, List.length_singleton] at run₆
        exact ⟨.recursive body environment, _, _, rest₆, .fix body environment,
          .recursive (windHeap_closure _ _ _) (windHeap_couple _ _ _) (represented.mono (windHeap_prefix _ _ _)),
          windHeap_prefix _ _ _, by omega, run₆⟩
    | pair left right _ _ =>
        intro environment heap word code stack final represented run₀ stopped
        simp only [compile, List.append_assoc, List.cons_append, List.nil_append] at run₀
        obtain ⟨rest₁, rfl, run₁⟩ := run₀.push_inv stopped
        obtain ⟨leftValue, leftWord, heap₁, rest₂, leftEval, leftRep, extended₁, less₂, run₂⟩ :=
          (ih rest₁ (by omega)).1 left environment heap word _ _ final represented run₁ stopped
        obtain ⟨rest₃, rfl, run₃⟩ := run₂.swap_inv stopped
        obtain ⟨rightValue, rightWord, heap₂, rest₄, rightEval, rightRep, extended₂, less₄, run₄⟩ :=
          (ih rest₃ (by omega)).1 right environment heap₁ word _ _ final (represented.mono extended₁) run₃
            stopped
        obtain ⟨rest₅, rfl, run₅⟩ := run₄.cons_inv stopped
        have extended₃ : heap₂ <+: heap₂ ++ [Cell.pair leftWord rightWord] := List.prefix_append _ _
        exact ⟨.pair leftValue rightValue, _, _, rest₅, .pair leftEval rightEval,
          .pair allocated ((leftRep.mono extended₂).mono extended₃) (rightRep.mono extended₃),
          extended₁.trans (extended₂.trans extended₃), by omega, run₅⟩
    | first term termIH =>
        intro environment heap word code stack final represented run₀ stopped
        simp only [compile, List.append_assoc, List.cons_append, List.nil_append] at run₀
        obtain ⟨before, beforeWord, heap₁, rest₁, termEval, beforeRep, extended₁, less₁, run₁⟩ :=
          termIH environment heap word _ stack final represented run₀ stopped
        obtain ⟨forced, coupleWord, heap₂, rest₂, force, coupleRep, extended₂, less₂, run₂⟩ :=
          (ih rest₁ less₁).2.1 before heap₁ beforeWord _ stack final beforeRep run₁ stopped
        obtain ⟨address, leftWord, rightWord, rest₃, rfl, cell, rfl, run₃⟩ := run₂.first_inv stopped
        obtain ⟨left, right, rfl, leftRep, _⟩ := coupleRep.pair_inv cell
        exact ⟨left, leftWord, heap₂, rest₃, .first termEval force, leftRep, extended₁.trans extended₂,
          by omega, run₃⟩
    | second term termIH =>
        intro environment heap word code stack final represented run₀ stopped
        simp only [compile, List.append_assoc, List.cons_append, List.nil_append] at run₀
        obtain ⟨before, beforeWord, heap₁, rest₁, termEval, beforeRep, extended₁, less₁, run₁⟩ :=
          termIH environment heap word _ stack final represented run₀ stopped
        obtain ⟨forced, coupleWord, heap₂, rest₂, force, coupleRep, extended₂, less₂, run₂⟩ :=
          (ih rest₁ less₁).2.1 before heap₁ beforeWord _ stack final beforeRep run₁ stopped
        obtain ⟨address, leftWord, rightWord, rest₃, rfl, cell, rfl, run₃⟩ := run₂.second_inv stopped
        obtain ⟨left, right, rfl, _, rightRep⟩ := coupleRep.pair_inv cell
        exact ⟨right, rightWord, heap₂, rest₃, .second termEval force, rightRep, extended₁.trans extended₂,
          by omega, run₃⟩
    | app operator argument _ _ =>
        intro environment heap word code stack final represented run₀ stopped
        simp only [compile, forceOperator, List.append_assoc, List.cons_append, List.nil_append] at run₀
        obtain ⟨rest₁, rfl, run₁⟩ := run₀.push_inv stopped
        obtain ⟨function, functionWord, heap₁, rest₂, operatorEval, functionRep, extended₁, less₂,
          run₂⟩ :=
          (ih rest₁ (by omega)).1 operator environment heap word _ _ final represented run₁ stopped
        obtain ⟨rest₃, rfl, run₃⟩ := run₂.swap_inv stopped
        obtain ⟨operand, argumentWord, heap₂, rest₄, argumentEval, argumentRep, extended₂, less₄, run₄⟩ :=
          (ih rest₃ (by omega)).1 argument environment heap₁ word _ _ final (represented.mono extended₁) run₃
            stopped
        obtain ⟨rest₅, rfl, run₅⟩ := run₄.cons_inv stopped
        obtain ⟨rest₆, rfl, run₆⟩ := run₅.push_inv stopped
        obtain ⟨address, left, right, rest₇, same, cell, rfl, run₇⟩ := run₆.first_inv stopped
        cases same
        rw [allocated] at cell
        cases cell
        have extended₃ : heap₂ <+: heap₂ ++ [Cell.pair functionWord argumentWord] := List.prefix_append _ _
        obtain ⟨callee, calleeWord, heap₄, rest₈, force, calleeRep, extended₄, less₈, run₈⟩ :=
          (ih rest₇ (by omega)).2.1 function _ functionWord _ _ final
            ((functionRep.mono extended₂).mono extended₃) run₇ stopped
        obtain ⟨rest₉, rfl, run₉⟩ := run₈.swap_inv stopped
        obtain ⟨address', left', right', rest₁₀, same', cell', rfl, run₁₀⟩ := run₉.second_inv stopped
        cases same'
        rw [lookup_prefix extended₄ allocated] at cell'
        cases cell'
        obtain ⟨rest₁₁, rfl, run₁₁⟩ := run₁₀.cons_inv stopped
        have extended₅ : heap₄ <+: heap₄ ++ [Cell.pair calleeWord argumentWord] := List.prefix_append _ _
        obtain ⟨value, result, heap₆, rest₁₂, invocation, valueRep, extended₆, less₁₂, run₁₂⟩ :=
          (ih rest₁₁ (by omega)).2.2 callee operand _ _ calleeWord argumentWord code stack final allocated
            (calleeRep.mono extended₅) (((argumentRep.mono extended₃).mono extended₄).mono extended₅) run₁₁
            stopped
        exact ⟨value, result, heap₆, rest₁₂, .app operatorEval argumentEval force invocation, valueRep,
          extended₁.trans (extended₂.trans (extended₃.trans (extended₄.trans (extended₅.trans extended₆)))),
          by omega, run₁₂⟩
    | conditional condition whenTrue whenFalse _ _ _ =>
        intro environment heap word code stack final represented run₀ stopped
        simp only [compile, List.append_assoc, List.cons_append, List.nil_append] at run₀
        obtain ⟨rest₁, rfl, run₁⟩ := run₀.push_inv stopped
        obtain ⟨before, conditionWord, heap₁, rest₂, conditionEval, conditionRep, extended₁, less₂,
          run₂⟩ :=
          (ih rest₁ (by omega)).1 condition environment heap word _ _ final represented run₁ stopped
        obtain ⟨test, testWord, heap₂, rest₃, force, testRep, extended₂, less₃, run₃⟩ :=
          (ih rest₂ (by omega)).2.1 before heap₁ conditionWord _ _ final conditionRep run₂ stopped
        obtain ⟨selected, rest₄, rfl, rfl, run₄⟩ := run₃.branch_inv stopped
        cases testRep
        have chosen : StepsIn rest₄ ⟨word, compile (if selected then whenTrue else whenFalse) ++ code, stack,
            heap₂⟩ final := by
          cases selected <;> exact run₄
        obtain ⟨value, result, heap₃, rest₅, selectedEval, valueRep, extended₃, less₅, run₅⟩ :=
          (ih rest₄ (by omega)).1 _ environment heap₂ word code stack final
            ((represented.mono extended₁).mono extended₂) chosen stopped
        exact ⟨value, result, heap₃, rest₅, .conditional conditionEval force selectedEval, valueRep,
          extended₁.trans (extended₂.trans extended₃), by omega, run₅⟩
    | primitive operation argument argumentIH =>
        intro environment heap word code stack final represented run₀ stopped
        simp only [compile, forceOperands, List.append_assoc, List.cons_append, List.nil_append] at run₀
        obtain ⟨before, beforeWord, heap₁, rest₁, argumentEval, beforeRep, extended₁, less₁, run₁⟩ :=
          argumentIH environment heap word _ stack final represented run₀ stopped
        obtain ⟨couple, coupleWord, heap₂, rest₂, force, coupleRep, extended₂, less₂, run₂⟩ :=
          (ih rest₁ less₁).2.1 before heap₁ beforeWord _ stack final beforeRep run₁ stopped
        obtain ⟨rest₃, rfl, run₃⟩ := run₂.push_inv stopped
        obtain ⟨address, leftWord, rightWord, rest₄, rfl, cell, rfl, run₄⟩ := run₃.first_inv stopped
        obtain ⟨left, right, rfl, leftRep, rightRep⟩ := coupleRep.pair_inv cell
        obtain ⟨leftForced, leftResult, heap₃, rest₅, leftForce, leftResultRep, extended₃, less₅, run₅⟩ :=
          (ih rest₄ (by omega)).2.1 left heap₂ leftWord _ _ final leftRep run₄ stopped
        obtain ⟨rest₆, rfl, run₆⟩ := run₅.swap_inv stopped
        obtain ⟨address', left', right', rest₇, same, cell', rfl, run₇⟩ := run₆.second_inv stopped
        cases same
        rw [lookup_prefix extended₃ cell] at cell'
        cases cell'
        obtain ⟨rightForced, rightResult, heap₄, rest₈, rightForce, rightResultRep, extended₄, less₈,
          run₈⟩ :=
          (ih rest₇ (by omega)).2.1 right heap₃ rightWord _ _ final (rightRep.mono extended₃) run₇ stopped
        obtain ⟨rest₉, rfl, run₉⟩ := run₈.cons_inv stopped
        obtain ⟨address'', leftValue, rightValue, rest₁₀, same'', cell'', rfl, run₁₀⟩ :=
          run₉.operation_inv stopped
        cases same''
        rw [allocated] at cell''
        cases cell''
        cases leftResultRep
        cases rightResultRep
        exact ⟨.literal (operation.apply leftValue rightValue), _, _, rest₁₀,
          .primitive argumentEval force leftForce rightForce, .literal _,
          extended₁.trans (extended₂.trans (extended₃.trans (extended₄.trans (List.prefix_append _ _)))),
          by omega, run₁₀⟩
  exact ⟨evaluationReturns, forceReturns, invocationReturns⟩

/-- Completeness (the analogue of Proposition 3.1, right to left): every
completed execution of compiled code from a represented environment constructs
a source evaluation whose value the final register represents. No termination
is assumed; stuck and divergent runs simply have no completed endpoint. -/
theorem execution_complete {term : Term} {environment : Value} {heap final : Heap} {word result : Word}
    (represented : Represents heap word environment)
    (run : Steps ⟨word, compile term, [], heap⟩ ⟨result, [], [], final⟩) :
    ∃ value, Evaluation term environment value ∧ Represents final result value ∧ heap <+: final := by
  obtain ⟨count, counted⟩ := run.stepsIn
  obtain ⟨value, result', final', rest, evaluated, valueRep, extended, _, back⟩ :=
    (returns count).1 term environment heap word [] [] _ represented (by simpa only [List.append_nil] using counted)
      rfl
  cases back with
  | refl => exact ⟨value, evaluated, valueRep, extended⟩
  | head transition _ => cases transition

/-- Soundness with an empty caller: the completed answer represents the value. -/
theorem execution_sound {term : Term} {environment value : Value} {heap : Heap} {word : Word}
    (represented : Represents heap word environment) (evaluated : Evaluation term environment value) :
    ∃ result final, Steps ⟨word, compile term, [], heap⟩ ⟨result, [], [], final⟩ ∧ heap <+: final ∧
      Represents final result value := by
  simpa only [List.append_nil] using evaluated.execution represented [] []

/-- Completion agreement: compiled code completes from a represented environment
exactly when the source term evaluates there. -/
theorem evaluates_iff_completes {term : Term} {environment : Value} {heap : Heap} {word : Word}
    (represented : Represents heap word environment) :
    (∃ value, Evaluation term environment value) ↔
      ∃ result final, Steps ⟨word, compile term, [], heap⟩ ⟨result, [], [], final⟩ := by
  constructor
  · rintro ⟨value, evaluated⟩
    obtain ⟨result, final, run, _, _⟩ := execution_sound represented evaluated
    exact ⟨result, final, run⟩
  · rintro ⟨result, final, run⟩
    obtain ⟨value, evaluated, _, _⟩ := execution_complete represented run
    exact ⟨value, evaluated⟩

/-- The completed answer represents the evaluated value, which is unique. -/
theorem execution_represents_evaluation {term : Term} {environment value : Value} {heap final : Heap}
    {word result : Word} (represented : Represents heap word environment)
    (evaluated : Evaluation term environment value)
    (run : Steps ⟨word, compile term, [], heap⟩ ⟨result, [], [], final⟩) :
    Represents final result value := by
  obtain ⟨value', evaluated', valueRep, _⟩ := execution_complete represented run
  rwa [evaluated.unique evaluated']


/-! ## Layout of source values -/

/-- Lay a source value out by appending its cells. A recursive value becomes
the cyclic couple and closure of Section 4. -/
def place : Value → Heap → Word × Heap
  | .unit, heap => (.unit, heap)
  | .literal value, heap => (.literal value, heap)
  | .pair left right, heap =>
      (.ref (place right (place left heap).2).2.length,
        (place right (place left heap).2).2 ++ [.pair (place left heap).1 (place right (place left heap).2).1])
  | .closure body environment, heap =>
      (.ref (place environment heap).2.length,
        (place environment heap).2 ++ [.closure (compile body) (place environment heap).1])
  | .recursive body environment, heap =>
      (.ref ((place environment heap).2.length + 1),
        windHeap (place environment heap).2 (place environment heap).1 (compile body))
  | .laze body environment, heap =>
      (.ref (place environment heap).2.length,
        (place environment heap).2 ++ [.laze (compile body) (place environment heap).1])

/-- Layout only appends, and the placed word represents the value. -/
theorem place_spec (value : Value) (heap : Heap) :
    heap <+: (place value heap).2 ∧ Represents (place value heap).2 (place value heap).1 value := by
  induction value generalizing heap with
  | unit => exact ⟨List.prefix_refl _, .unit⟩
  | literal value => exact ⟨List.prefix_refl _, .literal value⟩
  | pair left right leftIH rightIH =>
      obtain ⟨leftExtended, leftRep⟩ := leftIH heap
      obtain ⟨rightExtended, rightRep⟩ := rightIH (place left heap).2
      exact ⟨leftExtended.trans (rightExtended.trans (List.prefix_append _ _)),
        .pair allocated ((leftRep.mono rightExtended).mono (List.prefix_append _ _))
          (rightRep.mono (List.prefix_append _ _))⟩
  | closure body environment ih =>
      obtain ⟨extended, environmentRep⟩ := ih heap
      exact ⟨extended.trans (List.prefix_append _ _),
        .closure allocated (environmentRep.mono (List.prefix_append _ _))⟩
  | recursive body environment ih =>
      obtain ⟨extended, environmentRep⟩ := ih heap
      exact ⟨extended.trans (windHeap_prefix _ _ _),
        .recursive (windHeap_closure _ _ _) (windHeap_couple _ _ _) (environmentRep.mono (windHeap_prefix _ _ _))⟩
  | laze body environment ih =>
      obtain ⟨extended, environmentRep⟩ := ih heap
      exact ⟨extended.trans (List.prefix_append _ _),
        .laze allocated (environmentRep.mono (List.prefix_append _ _))⟩

theorem place_represents (value : Value) (heap : Heap) :
    Represents (place value heap).2 (place value heap).1 value :=
  (place_spec value heap).2

/-! ## The common machine interfaces -/

open Mettapedia.GSLT.Distinction.ProductiveBlocks

/-- Load a source question: lay out the environment in an empty heap and start
the compiled code with an empty stack. -/
def load (question : Term × Value) : State :=
  ⟨(place question.2 []).1, compile question.1, [], (place question.2 []).2⟩

def core : MachineCore (Term × Value) where
  State := State
  load := load
  step := step

/-- A completed answer: the root word with the value graph it addresses. -/
structure Answer where
  root : Word
  heap : Heap
  deriving DecidableEq, Repr

/-- Completed answers require empty code and an empty stack. -/
def answer : State → Option Answer
  | ⟨root, [], [], heap⟩ => some ⟨root, heap⟩
  | _ => none

theorem answer_iff (state : State) (completed : Answer) :
    answer state = some completed ↔ state = ⟨completed.root, [], [], completed.heap⟩ := by
  rcases state with ⟨register, code, stack, heap⟩
  rcases completed with ⟨root, finalHeap⟩
  cases code <;> cases stack <;> simp [answer]

theorem answer_final (state : State) (completed : Answer) (observed : answer state = some completed) :
    step state = none := by
  rw [(answer_iff state completed).mp observed]
  rfl

def answerCore : AnswerMachineCore (Term × Value) Answer where
  toMachineCore := core
  answer := answer
  answer_final := answer_final

abbrev Occurrence := ProductiveCoreAdapters.Occurrence State

/-- The value-graph machine in the common finite-run interface. Each
computational occurrence records its actual source and destination states,
including the heap; there is no silent administration. -/
def machine : Machine State Occurrence Answer Empty :=
  ProductiveCoreAdapters.answerMachine answerCore

theorem core_steps_iff (state final : State) : core.Steps state final ↔ Steps state final := by
  constructor
  · exact Relation.ReflTransGen.mono (fun left right edge => (step_iff left right).mp edge) state final
  · exact Relation.ReflTransGen.mono (fun left right edge => (step_iff left right).mpr edge) state final

theorem produces_iff (term : Term) (environment : Value) (completed : Answer) :
    answerCore.Produces (term, environment) completed ↔
      Steps (load (term, environment)) ⟨completed.root, [], [], completed.heap⟩ := by
  constructor
  · rintro ⟨final, reached, observed⟩
    rw [(answer_iff final completed).mp observed] at reached
    exact (core_steps_iff _ _).mp reached
  · intro reached
    exact ⟨_, (core_steps_iff _ _).mpr reached, rfl⟩

/-- A loaded question produces an answer exactly when its source term evaluates. -/
theorem produces_iff_evaluates (term : Term) (environment : Value) :
    (∃ completed, answerCore.Produces (term, environment) completed) ↔
      ∃ value, Evaluation term environment value := by
  rw [evaluates_iff_completes (place_represents environment [])]
  constructor
  · rintro ⟨completed, produced⟩
    exact ⟨completed.root, completed.heap, (produces_iff term environment completed).mp produced⟩
  · rintro ⟨root, heap, reached⟩
    exact ⟨⟨root, heap⟩, (produces_iff term environment ⟨root, heap⟩).mpr reached⟩

/-- The produced answer represents the evaluated source value. -/
theorem produces_represents {term : Term} {environment value : Value} {completed : Answer}
    (produced : answerCore.Produces (term, environment) completed)
    (evaluated : Evaluation term environment value) : Represents completed.heap completed.root value :=
  execution_represents_evaluation (place_represents environment []) evaluated
    ((produces_iff term environment completed).mp produced)

/-- Completion at the common runner's answer boundary. -/
theorem evaluates_iff_finished (term : Term) (environment : Value) :
    (∃ value, Evaluation term environment value) ↔
      ∃ budget events completed, machine.run budget (load (term, environment)) = (events, .finished completed) := by
  rw [← produces_iff_evaluates]
  constructor
  · rintro ⟨completed, produced⟩
    obtain ⟨budget, events, ran⟩ :=
      (ProductiveCoreAdapters.produces_iff_finished answerCore (term, environment) completed).mp produced
    exact ⟨budget, events, completed, ran⟩
  · rintro ⟨budget, events, completed, ran⟩
    exact ⟨completed,
      (ProductiveCoreAdapters.produces_iff_finished answerCore (term, environment) completed).mpr
        ⟨budget, events, ran⟩⟩

theorem finished_represents {term : Term} {environment value : Value} {budget : Nat}
    {events : List Occurrence} {completed : Answer}
    (ran : machine.run budget (load (term, environment)) = (events, .finished completed))
    (evaluated : Evaluation term environment value) : Represents completed.heap completed.root value :=
  produces_represents
    ((ProductiveCoreAdapters.produces_iff_finished answerCore (term, environment) completed).mpr
      ⟨budget, events, ran⟩) evaluated

/-- A finished run certifies the source evaluation of its loaded question. -/
theorem finished_evaluation {term : Term} {environment : Value} {budget : Nat}
    {events : List Occurrence} {completed : Answer}
    (ran : machine.run budget (load (term, environment)) = (events, .finished completed)) :
    ∃ value, Evaluation term environment value ∧ Represents completed.heap completed.root value := by
  have produced :=
    (ProductiveCoreAdapters.produces_iff_finished answerCore (term, environment) completed).mpr
      ⟨budget, events, ran⟩
  obtain ⟨value, evaluated, valueRep, _⟩ :=
    execution_complete (place_represents environment []) ((produces_iff term environment completed).mp produced)
  exact ⟨value, evaluated, valueRep⟩

theorem machine_no_administration (state next : State) : machine.step state ≠ some (.silent next) :=
  ProductiveCoreAdapters.answer_no_administration answerCore state next

theorem occurrences_le_budget (budget : Nat) (state : State) :
    (machine.run budget state).1.length ≤ budget :=
  ProductiveCoreAdapters.answer_occurrences_le_budget answerCore budget state

/-! ## Dynamic instruction legality -/

/-- A legal instruction is the actual head of the retained code with an
independent instruction-table transition. -/
def InstructionLegal (state : State) (opcode : Instruction) : Prop :=
  ∃ rest next, state.code = opcode :: rest ∧ Transition state next

theorem Transition.has_instruction {before after : State} (transition : Transition before after) :
    ∃ opcode, before.code.head? = some opcode := by
  cases transition <;> simp

def instructionContract : MachineCore.InstructionContract core Instruction where
  fetch state := state.code.head?
  Legal := InstructionLegal
  enabled_iff state := by
    constructor
    · rintro ⟨next, advanced⟩
      have transition := step_sound advanced
      cases code : state.code with
      | nil =>
          obtain ⟨opcode, fetched⟩ := transition.has_instruction
          simp [code] at fetched
      | cons opcode rest => exact ⟨opcode, rfl, rest, next, code, transition⟩
    · rintro ⟨opcode, _, rest, next, _, transition⟩
      exact ⟨next, step_complete transition⟩

/-- `wind` is legal exactly when the stack top addresses a couple. -/
theorem wind_legal_iff (state : State) :
    InstructionLegal state .wind ↔
      ∃ rest address stack left right, state.code = .wind :: rest ∧ state.stack = .ref address :: stack ∧
        state.heap[address]? = some (.pair left right) := by
  rcases state with ⟨register, code, stack, heap⟩
  constructor
  · rintro ⟨rest, next, same, transition⟩
    simp only at same
    subst same
    cases transition with
    | wind _ _ _ _ cell => exact ⟨_, _, _, _, _, rfl, rfl, cell⟩
  · rintro ⟨rest, address, stack, left, right, same, stackSame, cell⟩
    simp only at same stackSame cell
    subst same stackSame
    exact ⟨rest, _, rfl, .wind _ _ _ _ cell⟩

/-- `unfreeze` is always legal: it forces a laze and is a skip on anything else. -/
theorem unfreeze_legal (state : State) (rest : Code) (head : state.code = .unfreeze :: rest) :
    InstructionLegal state .unfreeze := by
  rcases state with ⟨register, code, stack, heap⟩
  simp only at head
  subst head
  by_cases laze : LazeAt heap register
  · obtain ⟨address, body, environment, rfl, cell⟩ := laze
    exact ⟨rest, _, rfl, .force _ _ _ cell⟩
  · exact ⟨rest, _, rfl, .skip _ _ _ _ laze⟩

/-! ## Checked loading of compiled images -/

/-- A code image retains its source environment; decoding the instruction
stream cannot supply or replace it. -/
def decodeImage (image : Code × Value) : Option (Term × Value) :=
  (decode image.1).map fun term => (term, image.2)

def compileImage (question : Term × Value) : Code × Value :=
  (compile question.1, question.2)

@[simp] theorem decodeImage_compileImage (question : Term × Value) :
    decodeImage (compileImage question) = some question := by
  rcases question with ⟨term, environment⟩
  simp [decodeImage, compileImage]

def loadImage (image : Code × Value) : Option State :=
  core.loadCode decodeImage image

@[simp] theorem loadImage_compileImage (question : Term × Value) :
    loadImage (compileImage question) = some (core.load question) :=
  MachineCore.loadCode_encode core compileImage decodeImage decodeImage_compileImage question

@[simp] theorem loadImage_refused_iff (code : Code) (environment : Value) :
    loadImage (code, environment) = none ↔ decode code = none := by
  cases decoded : decode code with
  | none =>
      simp only [loadImage, MachineCore.loadCode, decodeImage, decoded, Option.map_none]
      exact iff_true_intro rfl
  | some term => simp [loadImage, MachineCore.loadCode, decodeImage, decoded]

/-- Every admitted image executes exactly its decoded source term. -/
theorem admitted_iff_evaluates (code : Code) (environment : Value) (term : Term)
    (decoded : decode code = some term) :
    (∃ initial final completed, loadImage (code, environment) = some initial ∧ core.Steps initial final ∧
      answer final = some completed) ↔ ∃ value, Evaluation term environment value := by
  have canonical := compile_decode decoded
  have loaded : loadImage (code, environment) = some (core.load (term, environment)) := by
    rw [← canonical]
    exact loadImage_compileImage (term, environment)
  rw [loaded, ← produces_iff_evaluates]
  constructor
  · rintro ⟨initial, final, completed, same, reached, observed⟩
    cases same
    exact ⟨completed, final, reached, observed⟩
  · rintro ⟨completed, final, reached, observed⟩
    exact ⟨_, final, completed, rfl, reached, observed⟩


/-! ## The tree machine's extended source inside the graph source -/

/-- The quotation/conditional source of the tree machine, constructor by constructor. -/
def embed : Source true → Term
  | .var index => .var index
  | .lam body => .lam (embed body)
  | .app operator argument => .app (embed operator) (embed argument)
  | .pair left right => .pair (embed left) (embed right)
  | .first term => .first (embed term)
  | .second term => .second (embed term)
  | .literal _ value => .literal value
  | .conditional _ condition whenTrue whenFalse =>
      .conditional (embed condition) (embed whenTrue) (embed whenFalse)

theorem embed_injective : Function.Injective embed := by
  intro left right same
  induction left generalizing right with
  | var index => cases right <;> simp_all [embed]
  | lam body ih =>
      cases right <;> simp only [embed, reduceCtorEq, Term.lam.injEq] at same
      rw [ih same]
  | app operator argument operatorIH argumentIH =>
      cases right <;> simp only [embed, reduceCtorEq, Term.app.injEq] at same
      rw [operatorIH same.1, argumentIH same.2]
  | pair left right leftIH rightIH =>
      cases right <;> simp only [embed, reduceCtorEq, Term.pair.injEq] at same
      rw [leftIH same.1, rightIH same.2]
  | first term ih =>
      cases right <;> simp only [embed, reduceCtorEq, Term.first.injEq] at same
      rw [ih same]
  | second term ih =>
      cases right <;> simp only [embed, reduceCtorEq, Term.second.injEq] at same
      rw [ih same]
  | literal enabled value => cases right <;> simp_all [embed]
  | conditional enabled condition whenTrue whenFalse conditionIH trueIH falseIH =>
      cases right <;> simp only [embed, reduceCtorEq, Term.conditional.injEq] at same
      rw [conditionIH same.1, trueIH same.2.1, falseIH same.2.2]

theorem embed_ite (selected : Bool) (whenTrue whenFalse : Source true) :
    embed (if selected then whenTrue else whenFalse) =
      if selected then embed whenTrue else embed whenFalse := by
  cases selected <;> rfl

/-- Tree values without neutral nodes. The neutral projection and application
values of Table 5 have no counterpart in the strict graph source. -/
def embedValue : SourceValue true → Option Value
  | .unit => some .unit
  | .literal _ value => some (.literal value)
  | .pair left right =>
      match embedValue left, embedValue right with
      | some left, some right => some (.pair left right)
      | _, _ => none
  | .closure body environment => (embedValue environment).map (.closure (embed body))
  | .first _ | .second _ | .app _ => none

theorem embedValue_pair {left right : SourceValue true} {value : Value}
    (embedded : embedValue (.pair left right) = some value) :
    ∃ left' right', value = .pair left' right' ∧ embedValue left = some left' ∧
      embedValue right = some right' := by
  cases leftFound : embedValue left with
  | none => simp [embedValue, leftFound] at embedded
  | some left' =>
      cases rightFound : embedValue right with
      | none => simp [embedValue, leftFound, rightFound] at embedded
      | some right' =>
          simp only [embedValue, leftFound, rightFound, Option.some.injEq] at embedded
          exact ⟨left', right', embedded.symm, rfl, rfl⟩

theorem embedValue_injective {first second : SourceValue true} {value : Value}
    (one : embedValue first = some value) (two : embedValue second = some value) : first = second := by
  induction first generalizing second value with
  | unit =>
      simp only [embedValue, Option.some.injEq] at one
      subst one
      cases second with
      | unit => rfl
      | pair left right =>
          obtain ⟨_, _, same, _, _⟩ := embedValue_pair two
          cases same
      | closure body environment => cases found : embedValue environment <;> simp [embedValue, found] at two
      | literal _ _ | first _ | second _ | app _ => simp [embedValue] at two
  | literal enabled literal =>
      simp only [embedValue, Option.some.injEq] at one
      subst one
      cases second with
      | literal _ literal' =>
          simp only [embedValue, Option.some.injEq, Value.literal.injEq] at two
          subst two
          rfl
      | pair left right =>
          obtain ⟨_, _, same, _, _⟩ := embedValue_pair two
          cases same
      | closure body environment => cases found : embedValue environment <;> simp [embedValue, found] at two
      | unit | first _ | second _ | app _ => simp [embedValue] at two
  | pair left right leftIH rightIH =>
      obtain ⟨left', right', rfl, leftFound, rightFound⟩ := embedValue_pair one
      cases second with
      | pair left₂ right₂ =>
          obtain ⟨left₂', right₂', same, leftFound₂, rightFound₂⟩ := embedValue_pair two
          cases same
          rw [leftIH leftFound leftFound₂, rightIH rightFound rightFound₂]
      | closure body environment => cases found : embedValue environment <;> simp [embedValue, found] at two
      | unit | literal _ _ | first _ | second _ | app _ => simp [embedValue] at two
  | closure body environment ih =>
      cases found : embedValue environment with
      | none => simp [embedValue, found] at one
      | some environment' =>
          simp only [embedValue, found, Option.map_some, Option.some.injEq] at one
          subst one
          cases second with
          | closure body₂ environment₂ =>
              cases found₂ : embedValue environment₂ with
              | none => simp [embedValue, found₂] at two
              | some environment₂' =>
                  simp only [embedValue, found₂, Option.map_some, Option.some.injEq, Value.closure.injEq] at two
                  obtain ⟨sameBody, sameEnvironment⟩ := two
                  subst sameEnvironment
                  rw [embed_injective sameBody.symm, ih found found₂]
          | pair left right =>
              obtain ⟨_, _, same, _, _⟩ := embedValue_pair two
              cases same
          | unit | literal _ _ | first _ | second _ | app _ => simp [embedValue] at two
  | first _ _ | second _ _ | app _ _ => simp [embedValue] at one

theorem embedValue_notLaze {value : SourceValue true} {value' : Value}
    (embedded : embedValue value = some value') : value'.NotLaze := by
  cases value with
  | pair left right =>
      obtain ⟨_, _, rfl, _, _⟩ := embedValue_pair embedded
      trivial
  | closure body environment =>
      cases found : embedValue environment <;> simp [embedValue, found] at embedded
      subst embedded
      trivial
  | unit | literal _ _ => simp only [embedValue, Option.some.injEq] at embedded; subst embedded; trivial
  | first _ | second _ | app _ => simp [embedValue] at embedded

theorem Force.of_notLaze {value result : Value} (forced : Force value result) (notLaze : value.NotLaze) :
    result = value := by
  cases forced with
  | laze _ _ => exact False.elim notLaze
  | value _ _ => rfl

/-- The derivations of the tree judgment that use only its active rules:
projections of couples and invocations of closures. -/
inductive TreeStrict : Source true → SourceValue true → SourceValue true → Prop where
  | varZero (environment value : SourceValue true) : TreeStrict (.var 0) (.pair environment value) value
  | varSucc {index : Nat} {environment value : SourceValue true} (saved : SourceValue true)
      (rest : TreeStrict (.var index) environment value) :
      TreeStrict (.var (index + 1)) (.pair environment saved) value
  | literal (value : Literal) (environment : SourceValue true) :
      TreeStrict (.literal rfl value) environment (.literal rfl value)
  | conditional {condition whenTrue whenFalse : Source true} {environment value : SourceValue true}
      {selected : Bool} (conditionEval : TreeStrict condition environment (.literal rfl (.boolean selected)))
      (selectedEval : TreeStrict (if selected then whenTrue else whenFalse) environment value) :
      TreeStrict (.conditional rfl condition whenTrue whenFalse) environment value
  | lam (body : Source true) (environment : SourceValue true) :
      TreeStrict (.lam body) environment (.closure body environment)
  | pair {left right : Source true} {environment leftValue rightValue : SourceValue true}
      (leftEval : TreeStrict left environment leftValue) (rightEval : TreeStrict right environment rightValue) :
      TreeStrict (.pair left right) environment (.pair leftValue rightValue)
  | app {operator argument body : Source true} {environment captured operand value : SourceValue true}
      (operatorEval : TreeStrict operator environment (.closure body captured))
      (argumentEval : TreeStrict argument environment operand)
      (bodyEval : TreeStrict body (.pair captured operand) value) :
      TreeStrict (.app operator argument) environment value
  | first {term : Source true} {environment left right : SourceValue true}
      (termEval : TreeStrict term environment (.pair left right)) : TreeStrict (.first term) environment left
  | second {term : Source true} {environment left right : SourceValue true}
      (termEval : TreeStrict term environment (.pair left right)) : TreeStrict (.second term) environment right

/-- Every active-rule derivation is a derivation of the tree judgment. -/
theorem TreeStrict.evaluation {term : Source true} {environment value : SourceValue true}
    (derivation : TreeStrict term environment value) :
    CategoricalAbstractMachine.Evaluation term environment value := by
  induction derivation with
  | varZero => exact .varZero (.pair _ _)
  | varSucc _ _ ih => exact .varSucc (.pair _ _) ih
  | literal value environment => exact .literal rfl value environment
  | conditional _ _ conditionIH selectedIH => exact .conditional conditionIH selectedIH
  | lam body environment => exact .lam body environment
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | app _ _ _ operatorIH argumentIH bodyIH => exact .app operatorIH argumentIH (.closure bodyIH)
  | first _ ih => exact .first ih (.pair _ _)
  | second _ ih => exact .second ih (.pair _ _)

/-- An active-rule tree derivation is a graph-source derivation of the embedded term. -/
theorem TreeStrict.graph {term : Source true} {environment value : SourceValue true}
    (derivation : TreeStrict term environment value) :
    ∀ {environment' : Value}, embedValue environment = some environment' →
      ∃ value', embedValue value = some value' ∧ Evaluation (embed term) environment' value' := by
  induction derivation with
  | varZero environment value =>
      intro environment' embedded
      obtain ⟨_, value', rfl, _, valueFound⟩ := embedValue_pair embedded
      exact ⟨value', valueFound, .varZero _ _⟩
  | varSucc saved _ ih =>
      intro environment' embedded
      obtain ⟨inner, saved', rfl, innerFound, _⟩ := embedValue_pair embedded
      obtain ⟨value', valueFound, evaluated⟩ := ih innerFound
      exact ⟨value', valueFound, .varSucc saved' evaluated⟩
  | literal value environment =>
      intro environment' _
      exact ⟨.literal value, rfl, .literal value environment'⟩
  | conditional _ _ conditionIH selectedIH =>
      rename_i whenTrue whenFalse environment value selected
      intro environment' embedded
      obtain ⟨test', testFound, conditionEval⟩ := conditionIH embedded
      simp only [embedValue, Option.some.injEq] at testFound
      subst testFound
      obtain ⟨value', valueFound, selectedEval⟩ := selectedIH embedded
      refine ⟨value', valueFound, .conditional conditionEval (.value _ trivial) ?_⟩
      simpa only [embed_ite] using selectedEval
  | lam body environment =>
      intro environment' embedded
      exact ⟨.closure (embed body) environment', by simp [embedValue, embedded], .lam _ _⟩
  | pair _ _ leftIH rightIH =>
      intro environment' embedded
      obtain ⟨left', leftFound, leftEval⟩ := leftIH embedded
      obtain ⟨right', rightFound, rightEval⟩ := rightIH embedded
      exact ⟨.pair left' right', by simp [embedValue, leftFound, rightFound], .pair leftEval rightEval⟩
  | @app operator argument body environment captured operand value _ _ _ operatorIH argumentIH bodyIH =>
      intro environment' embedded
      obtain ⟨function', functionFound, operatorEval⟩ := operatorIH embedded
      obtain ⟨operand', operandFound, argumentEval⟩ := argumentIH embedded
      cases capturedFound : embedValue captured with
      | none => simp [embedValue, capturedFound] at functionFound
      | some captured' =>
          simp only [embedValue, capturedFound, Option.map_some, Option.some.injEq] at functionFound
          subst functionFound
          obtain ⟨value', valueFound, bodyEval⟩ :=
            bodyIH (environment' := .pair captured' operand') (by simp [embedValue, capturedFound, operandFound])
          exact ⟨value', valueFound, .app operatorEval argumentEval (.value _ trivial) (.closure bodyEval)⟩
  | first _ ih =>
      intro environment' embedded
      obtain ⟨couple', coupleFound, termEval⟩ := ih embedded
      obtain ⟨left', right', rfl, leftFound, _⟩ := embedValue_pair coupleFound
      exact ⟨left', leftFound, .first termEval (.value _ trivial)⟩
  | second _ ih =>
      intro environment' embedded
      obtain ⟨couple', coupleFound, termEval⟩ := ih embedded
      obtain ⟨left', right', rfl, _, rightFound⟩ := embedValue_pair coupleFound
      exact ⟨right', rightFound, .second termEval (.value _ trivial)⟩

mutual
/-- A graph-source derivation of an embedded term from an embedded environment
is an active-rule tree derivation. -/
theorem Evaluation.treeStrict : {term : Term} → {environment' value' : Value} →
    Evaluation term environment' value' → (source : Source true) → (environment : SourceValue true) →
    embed source = term → embedValue environment = some environment' →
    ∃ value, embedValue value = some value' ∧ TreeStrict source environment value
  | _, _, _, .varZero _ _, source, environment, embedded, environmentFound => by
      cases source <;> simp only [embed, reduceCtorEq, Term.var.injEq] at embedded
      subst embedded
      cases environment with
      | pair inner value =>
          obtain ⟨_, value', same, _, valueFound⟩ := embedValue_pair environmentFound
          cases same
          exact ⟨value, valueFound, .varZero _ _⟩
      | closure _ environment =>
          cases found : embedValue environment <;> simp [embedValue, found] at environmentFound
      | unit | literal _ _ | first _ | second _ | app _ => simp [embedValue] at environmentFound
  | _, _, _, .varSucc _ rest, source, environment, embedded, environmentFound => by
      cases source <;> simp only [embed, reduceCtorEq, Term.var.injEq] at embedded
      subst embedded
      cases environment with
      | pair inner saved =>
          obtain ⟨inner', _, same, innerFound, _⟩ := embedValue_pair environmentFound
          cases same
          obtain ⟨value, valueFound, derivation⟩ := Evaluation.treeStrict rest (.var _) inner rfl innerFound
          exact ⟨value, valueFound, .varSucc saved derivation⟩
      | closure _ environment =>
          cases found : embedValue environment <;> simp [embedValue, found] at environmentFound
      | unit | literal _ _ | first _ | second _ | app _ => simp [embedValue] at environmentFound
  | _, _, _, .literal _ _, source, environment, embedded, _ => by
      cases source <;> simp only [embed, reduceCtorEq, Term.literal.injEq] at embedded
      subst embedded
      exact ⟨.literal rfl _, rfl, .literal _ environment⟩
  | _, _, _, .lam _ _, source, environment, embedded, environmentFound => by
      cases source <;> simp only [embed, reduceCtorEq, Term.lam.injEq] at embedded
      subst embedded
      exact ⟨.closure _ environment, by simp [embedValue, environmentFound], .lam _ environment⟩
  | _, _, _, .fix _ _, source, _, embedded, _ => by
      cases source <;> simp [embed] at embedded
  | _, _, _, .freeze _ _, source, _, embedded, _ => by
      cases source <;> simp [embed] at embedded
  | _, _, _, .primitive _ _ _ _, source, _, embedded, _ => by
      cases source <;> simp [embed] at embedded
  | _, _, _, .pair leftEval rightEval, source, environment, embedded, environmentFound => by
      cases source <;> simp only [embed, reduceCtorEq, Term.pair.injEq] at embedded
      obtain ⟨left, leftFound, leftDerivation⟩ :=
        Evaluation.treeStrict leftEval _ environment embedded.1 environmentFound
      obtain ⟨right, rightFound, rightDerivation⟩ :=
        Evaluation.treeStrict rightEval _ environment embedded.2 environmentFound
      exact ⟨.pair left right, by simp [embedValue, leftFound, rightFound], .pair leftDerivation rightDerivation⟩
  | _, _, _, .first termEval forced, source, environment, embedded, environmentFound => by
      cases source <;> simp only [embed, reduceCtorEq, Term.first.injEq] at embedded
      obtain ⟨before, beforeFound, derivation⟩ :=
        Evaluation.treeStrict termEval _ environment embedded environmentFound
      have same := forced.of_notLaze (embedValue_notLaze beforeFound)
      subst same
      cases before with
      | pair left right =>
          obtain ⟨_, _, same, leftFound, _⟩ := embedValue_pair beforeFound
          cases same
          exact ⟨left, leftFound, .first derivation⟩
      | closure _ environment =>
          cases found : embedValue environment <;> simp [embedValue, found] at beforeFound
      | unit | literal _ _ | first _ | second _ | app _ => simp [embedValue] at beforeFound
  | _, _, _, .second termEval forced, source, environment, embedded, environmentFound => by
      cases source <;> simp only [embed, reduceCtorEq, Term.second.injEq] at embedded
      obtain ⟨before, beforeFound, derivation⟩ :=
        Evaluation.treeStrict termEval _ environment embedded environmentFound
      have same := forced.of_notLaze (embedValue_notLaze beforeFound)
      subst same
      cases before with
      | pair left right =>
          obtain ⟨_, _, same, _, rightFound⟩ := embedValue_pair beforeFound
          cases same
          exact ⟨right, rightFound, .second derivation⟩
      | closure _ environment =>
          cases found : embedValue environment <;> simp [embedValue, found] at beforeFound
      | unit | literal _ _ | first _ | second _ | app _ => simp [embedValue] at beforeFound
  | _, _, _, .app (callee := callee) operatorEval argumentEval forced invocation, source, environment, embedded,
      environmentFound => by
      cases source <;> simp only [embed, reduceCtorEq, Term.app.injEq] at embedded
      obtain ⟨function, functionFound, operatorDerivation⟩ :=
        Evaluation.treeStrict operatorEval _ environment embedded.1 environmentFound
      obtain ⟨operand, operandFound, argumentDerivation⟩ :=
        Evaluation.treeStrict argumentEval _ environment embedded.2 environmentFound
      have same := forced.of_notLaze (embedValue_notLaze functionFound)
      have calleeFound : embedValue function = some callee := by rw [same]; exact functionFound
      obtain ⟨body, captured, value, rfl, valueFound, bodyDerivation⟩ :=
        Invocation.treeStrict invocation function operand calleeFound operandFound
      exact ⟨value, valueFound, .app operatorDerivation argumentDerivation bodyDerivation⟩
  | _, _, _, .conditional (selected := selected) conditionEval forced selectedEval, source, environment,
      embedded, environmentFound => by
      cases source
      case conditional enabled sourceCondition sourceTrue sourceFalse =>
        simp only [embed, Term.conditional.injEq] at embedded
        obtain ⟨test, testFound, conditionDerivation⟩ :=
          Evaluation.treeStrict conditionEval sourceCondition environment embedded.1 environmentFound
        have same := forced.of_notLaze (embedValue_notLaze testFound)
        rw [← same] at testFound
        cases test with
        | literal _ literal =>
            simp only [embedValue, Option.some.injEq, Value.literal.injEq] at testFound
            subst testFound
            obtain ⟨value, valueFound, selectedDerivation⟩ :=
              Evaluation.treeStrict selectedEval (if selected then sourceTrue else sourceFalse) environment
                (by rw [embed_ite, embedded.2.1, embedded.2.2]) environmentFound
            exact ⟨value, valueFound, .conditional conditionDerivation selectedDerivation⟩
        | pair left right =>
            obtain ⟨_, _, same, _, _⟩ := embedValue_pair testFound
            cases same
        | closure _ environment =>
            cases found : embedValue environment <;> simp [embedValue, found] at testFound
        | unit | first _ | second _ | app _ => simp [embedValue] at testFound
      all_goals simp [embed] at embedded
/-- Graph invocation of an embedded function value is closure invocation. -/
theorem Invocation.treeStrict : {function' argument' value' : Value} →
    Invocation function' argument' value' → (function argument : SourceValue true) →
    embedValue function = some function' → embedValue argument = some argument' →
    ∃ body captured value, function = .closure body captured ∧ embedValue value = some value' ∧
      TreeStrict body (.pair captured argument) value
  | _, _, _, .closure bodyEval, function, argument, functionFound, argumentFound => by
      cases function with
      | closure body captured =>
          cases capturedFound : embedValue captured with
          | none => simp [embedValue, capturedFound] at functionFound
          | some captured' =>
              simp only [embedValue, capturedFound, Option.map_some, Option.some.injEq,
                Value.closure.injEq] at functionFound
              obtain ⟨value, valueFound, derivation⟩ :=
                Evaluation.treeStrict bodyEval body (.pair captured argument) functionFound.1
                  (by rw [← functionFound.2]; simp [embedValue, capturedFound, argumentFound])
              exact ⟨body, captured, value, rfl, valueFound, derivation⟩
      | pair left right =>
          obtain ⟨_, _, same, _, _⟩ := embedValue_pair functionFound
          cases same
      | unit | literal _ _ | first _ | second _ | app _ => simp [embedValue] at functionFound
  | _, _, _, .recursive _, function, _, functionFound, _ => by
      cases function with
      | closure body captured =>
          cases capturedFound : embedValue captured <;> simp [embedValue, capturedFound] at functionFound
      | pair left right =>
          obtain ⟨_, _, same, _, _⟩ := embedValue_pair functionFound
          cases same
      | unit | literal _ _ | first _ | second _ | app _ => simp [embedValue] at functionFound
end

/-- On embedded terms and environments, the graph judgment is exactly the
active-rule part of the tree judgment. -/
theorem treeStrict_iff_graph (source : Source true) (environment value : SourceValue true)
    {environment' : Value} (embedded : embedValue environment = some environment') :
    TreeStrict source environment value ↔
      ∃ value', embedValue value = some value' ∧ Evaluation (embed source) environment' value' := by
  constructor
  · intro derivation
    exact derivation.graph embedded
  · rintro ⟨value', valueFound, evaluated⟩
    obtain ⟨value₂, valueFound₂, derivation⟩ := evaluated.treeStrict source environment rfl embedded
    rwa [embedValue_injective valueFound valueFound₂]


/-! ## Finite observation of the value graph -/

/-- Node labels of the value graph: constants, couples, and closures and lazes
with their code. -/
inductive Label where
  | unit
  | literal (value : Literal)
  | pair
  | closure (body : Code)
  | laze (body : Code)
  deriving DecidableEq, Repr

/-- The heap as a structural layer reader over words. A dangling address is unreadable. -/
def reader (heap : Heap) : RationalTermGraph.LayerReader Word Label
  | .unit => some (.unit, [])
  | .literal value => some (.literal value, [])
  | .ref address =>
      match heap[address]? with
      | some (.pair left right) => some (.pair, [left, right])
      | some (.closure body environment) => some (.closure body, [environment])
      | some (.laze body environment) => some (.laze body, [environment])
      | none => none

/-- Depth-bounded unfolding of source values. A recursive value unfolds as the
closure over its environment couple, whose right component is the value again. -/
def unfold : Nat → Value → RationalTermGraph.Observation Label
  | 0, _ => .cut
  | _ + 1, .unit => .node .unit []
  | _ + 1, .literal value => .node (.literal value) []
  | depth + 1, .pair left right => .node .pair [unfold depth left, unfold depth right]
  | depth + 1, .closure body environment => .node (.closure (compile body)) [unfold depth environment]
  | depth + 1, .laze body environment => .node (.laze (compile body)) [unfold depth environment]
  | depth + 1, .recursive body environment =>
      .node (.closure (compile body)) [unfold depth (.pair environment (.recursive body environment))]

/-- A recursive value and its one-step unrolling are observationally equal. -/
theorem unfold_recursive (depth : Nat) (body : Term) (environment : Value) :
    unfold depth (.recursive body environment) =
      unfold depth (.closure body (.pair environment (.recursive body environment))) := by
  cases depth <;> rfl

/-- Every finite observation of a represented word is the unfolding of the value. -/
theorem Represents.observe {heap : Heap} {word : Word} {value : Value}
    (represented : Represents heap word value) (depth : Nat) :
    (reader heap).observe depth word = some (unfold depth value) := by
  induction depth generalizing word value with
  | zero =>
      cases represented with
      | unit | literal _ => rfl
      | pair cell _ _ | closure cell _ | laze cell _ | recursive cell _ _ =>
          simp [RationalTermGraph.LayerReader.observe, reader, cell, unfold]
  | succ depth ih =>
      cases represented with
      | unit | literal _ => rfl
      | pair cell leftRep rightRep =>
          simp [RationalTermGraph.LayerReader.observe, reader, cell, unfold, ih leftRep, ih rightRep]
      | closure cell environmentRep =>
          simp [RationalTermGraph.LayerReader.observe, reader, cell, unfold, ih environmentRep]
      | laze cell environmentRep =>
          simp [RationalTermGraph.LayerReader.observe, reader, cell, unfold, ih environmentRep]
      | recursive cell coupleCell environmentRep =>
          have unrolled := ih (Represents.pair coupleCell environmentRep (.recursive cell coupleCell environmentRep))
          simp [RationalTermGraph.LayerReader.observe, reader, cell, unfold, unrolled]

/-- All values represented by one word have the same finite observations. -/
theorem Represents.unfold_eq {heap : Heap} {word : Word} {first second : Value}
    (one : Represents heap word first) (two : Represents heap word second) (depth : Nat) :
    unfold depth first = unfold depth second :=
  Option.some.inj ((one.observe depth).symm.trans (two.observe depth))

/-- In an admitted keyed table of the heap, represented nodes are bisimilar exactly
when their values agree at every finite depth. -/
theorem Represents.bisimilar_iff {heap : Heap} {keys : List Word}
    {table : RationalTermGraph.KeyedTable Word Label} (read : (reader heap).readTable? keys = some table)
    {left right : table.Node} {leftValue rightValue : Value}
    (leftRep : Represents heap (table.key left) leftValue) (rightRep : Represents heap (table.key right) rightValue) :
    RationalTermGraph.Bisimilar table.graph table.graph left right ↔
      ∀ depth, unfold depth leftValue = unfold depth rightValue := by
  rw [RationalTermGraph.LayerReader.readTable?_bisimilar_iff read read left right]
  simp only [leftRep.observe, rightRep.observe, Option.some.injEq]

/-- Execution and evaluation agree at every finite observation depth. -/
theorem observation_iff_execution {term : Term} {environment : Value} {heap : Heap} {word : Word}
    (represented : Represents heap word environment) (depth : Nat)
    (observation : RationalTermGraph.Observation Label) :
    (∃ value, Evaluation term environment value ∧ unfold depth value = observation) ↔
      ∃ result final, Steps ⟨word, compile term, [], heap⟩ ⟨result, [], [], final⟩ ∧
        (reader final).observe depth result = some observation := by
  constructor
  · rintro ⟨value, evaluated, rfl⟩
    obtain ⟨result, final, run, _, valueRep⟩ := execution_sound represented evaluated
    exact ⟨result, final, run, valueRep.observe depth⟩
  · rintro ⟨result, final, run, observed⟩
    obtain ⟨value, evaluated, valueRep, _⟩ := execution_complete represented run
    exact ⟨value, evaluated, Option.some.inj ((valueRep.observe depth).symm.trans observed)⟩


/-- Source values that denote the same rational term: their unfoldings agree at
every finite depth. A recursive value and its unrolling are such values. -/
def SameUnfolding (first second : Value) : Prop := ∀ depth, unfold depth first = unfold depth second

theorem SameUnfolding.recursive (body : Term) (environment : Value) :
    SameUnfolding (.recursive body environment) (.closure body (.pair environment (.recursive body environment))) :=
  fun depth => unfold_recursive depth body environment

/-- Compiled code computes the source value up to the rational term it denotes:
a value has the unfoldings of the evaluated value exactly when every finite
observation of the completed answer shows them. Equality of the source syntax
itself is not observable on the graph, because one cyclic node represents a
recursive value and its unrollings (`Represents.not_functional`). -/
theorem evaluation_iff_execution {term : Term} {environment : Value} {heap : Heap} {word : Word}
    (represented : Represents heap word environment) (value : Value) :
    (∃ evaluated, Evaluation term environment evaluated ∧ SameUnfolding evaluated value) ↔
      ∃ result final, Steps ⟨word, compile term, [], heap⟩ ⟨result, [], [], final⟩ ∧
        ∀ depth, (reader final).observe depth result = some (unfold depth value) := by
  constructor
  · rintro ⟨evaluated, evaluation, same⟩
    obtain ⟨result, final, run, _, evaluatedRep⟩ := execution_sound represented evaluation
    exact ⟨result, final, run, fun depth => (evaluatedRep.observe depth).trans (congrArg some (same depth))⟩
  · rintro ⟨result, final, run, observed⟩
    obtain ⟨evaluated, evaluation, evaluatedRep, _⟩ := execution_complete represented run
    exact ⟨evaluated, evaluation, fun depth =>
      Option.some.inj ((evaluatedRep.observe depth).symm.trans (observed depth))⟩

/-! ## Refinement to the tree machine on tree code

On code built from the tree machine's own instructions, the value-graph
machine and the strict tree machine move in lock step: a store configuration
whose words unfold to the tree configuration's values takes a transition exactly
when the tree configuration does, and the results are again related. Only
allocation changes the heap, so no cell is ever updated. Lazes and cyclic
nodes have no finite unfolding; a configuration holding one is related to no
tree configuration.
-/

mutual
/-- An instruction of the tree machine's table, with tree code in nested bodies. -/
inductive TreeInstruction : Instruction → Prop where
  | first : TreeInstruction .first
  | second : TreeInstruction .second
  | cur {body : Code} (bodyTree : TreeCode body) : TreeInstruction (.cur body)
  | push : TreeInstruction .push
  | swap : TreeInstruction .swap
  | cons : TreeInstruction .cons
  | app : TreeInstruction .app
  | quote (value : Literal) : TreeInstruction (.quote value)
  | branch {whenTrue whenFalse : Code} (trueTree : TreeCode whenTrue) (falseTree : TreeCode whenFalse) :
      TreeInstruction (.branch whenTrue whenFalse)
/-- Code without `operation`, `wind`, `freeze` or `unfreeze`, nested bodies included. -/
inductive TreeCode : Code → Prop where
  | nil : TreeCode []
  | cons {instruction : Instruction} {rest : Code} (head : TreeInstruction instruction)
      (tail : TreeCode rest) : TreeCode (instruction :: rest)
end

theorem TreeCode.head {instruction : Instruction} {rest : Code} (tree : TreeCode (instruction :: rest)) :
    TreeInstruction instruction := by
  cases tree with
  | cons head _ => exact head

theorem TreeCode.tail {instruction : Instruction} {rest : Code} (tree : TreeCode (instruction :: rest)) :
    TreeCode rest := by
  cases tree with
  | cons _ tail => exact tail

theorem TreeCode.append {left right : Code} (leftTree : TreeCode left) (rightTree : TreeCode right) :
    TreeCode (left ++ right) := by
  induction left with
  | nil => exact rightTree
  | cons instruction rest ih => exact .cons leftTree.head (ih leftTree.tail)

theorem TreeCode.replicate (count : Nat) : TreeCode (List.replicate count .first) := by
  induction count with
  | zero => exact .nil
  | succ count ih => simpa only [List.replicate_succ] using TreeCode.cons .first ih

/-- The tree compiler emits tree code. -/
theorem compileSource_tree {extended : Bool} (term : Source extended) : TreeCode (compileSource term) := by
  induction term with
  | var index => exact (TreeCode.replicate index).append (.cons .second .nil)
  | lam body ih => exact .cons (.cur ih) .nil
  | app operator argument operatorIH argumentIH =>
      exact ((((TreeCode.cons .push .nil).append operatorIH).append (.cons .swap .nil)).append
        argumentIH).append (.cons .cons (.cons .app .nil))
  | pair left right leftIH rightIH =>
      exact ((((TreeCode.cons .push .nil).append leftIH).append (.cons .swap .nil)).append
        rightIH).append (.cons .cons .nil)
  | first term ih => exact ih.append (.cons .first .nil)
  | second term ih => exact ih.append (.cons .second .nil)
  | literal _ value => exact .cons (.quote value) .nil
  | conditional _ condition whenTrue whenFalse conditionIH trueIH falseIH =>
      exact .cons .push (conditionIH.append (.cons (.branch trueIH falseIH) .nil))

/-- A word unfolds to a tree value by a finite derivation. Lazes and cyclic
nodes have no tree counterpart. -/
inductive Unfolds (heap : Heap) : Word → NativeValue → Prop where
  | unit : Unfolds heap .unit .unit
  | literal (value : Literal) : Unfolds heap (.literal value) (.literal value)
  | pair {address : Nat} {leftWord rightWord : Word} {left right : NativeValue}
      (cell : heap[address]? = some (.pair leftWord rightWord))
      (leftUnfolds : Unfolds heap leftWord left) (rightUnfolds : Unfolds heap rightWord right) :
      Unfolds heap (.ref address) (.pair left right)
  | closure {address : Nat} {body : Code} {environmentWord : Word} {environment : NativeValue}
      (cell : heap[address]? = some (.closure body environmentWord)) (bodyTree : TreeCode body)
      (environmentUnfolds : Unfolds heap environmentWord environment) :
      Unfolds heap (.ref address) (.closure body environment)

theorem Unfolds.mono {heap heap' : Heap} {word : Word} {native : NativeValue}
    (unfolds : Unfolds heap word native) (extended : heap <+: heap') : Unfolds heap' word native := by
  induction unfolds with
  | unit => exact .unit
  | literal value => exact .literal value
  | pair cell _ _ leftIH rightIH => exact .pair (lookup_prefix extended cell) leftIH rightIH
  | closure cell bodyTree _ ih => exact .closure (lookup_prefix extended cell) bodyTree ih

theorem Unfolds.unique {heap : Heap} {word : Word} {first second : NativeValue}
    (one : Unfolds heap word first) (two : Unfolds heap word second) : first = second := by
  induction one generalizing second with
  | unit => cases two; rfl
  | literal value => cases two; rfl
  | pair cell _ _ leftIH rightIH =>
      cases two with
      | pair cell' leftUnfolds rightUnfolds =>
          rw [cell] at cell'
          cases cell'
          rw [leftIH leftUnfolds, rightIH rightUnfolds]
      | closure cell' _ _ =>
          rw [cell] at cell'
          cases cell'
  | closure cell _ _ ih =>
      cases two with
      | closure cell' _ environmentUnfolds =>
          rw [cell] at cell'
          cases cell'
          rw [ih environmentUnfolds]
      | pair cell' _ _ =>
          rw [cell] at cell'
          cases cell'

theorem Unfolds.pair_inv {heap : Heap} {word : Word} {left right : NativeValue}
    (unfolds : Unfolds heap word (.pair left right)) :
    ∃ address leftWord rightWord, word = .ref address ∧ heap[address]? = some (.pair leftWord rightWord) ∧
      Unfolds heap leftWord left ∧ Unfolds heap rightWord right := by
  cases unfolds with
  | pair cell leftUnfolds rightUnfolds => exact ⟨_, _, _, rfl, cell, leftUnfolds, rightUnfolds⟩

theorem Unfolds.closure_inv {heap : Heap} {word : Word} {body : Code} {environment : NativeValue}
    (unfolds : Unfolds heap word (.closure body environment)) :
    ∃ address environmentWord, word = .ref address ∧
      heap[address]? = some (.closure body environmentWord) ∧ TreeCode body ∧
      Unfolds heap environmentWord environment := by
  cases unfolds with
  | closure cell bodyTree environmentUnfolds => exact ⟨_, _, rfl, cell, bodyTree, environmentUnfolds⟩

theorem Unfolds.cell_pair {heap : Heap} {address : Nat} {leftWord rightWord : Word} {native : NativeValue}
    (unfolds : Unfolds heap (.ref address) native) (cell : heap[address]? = some (.pair leftWord rightWord)) :
    ∃ left right, native = .pair left right ∧ Unfolds heap leftWord left ∧ Unfolds heap rightWord right := by
  cases unfolds with
  | pair found leftUnfolds rightUnfolds =>
      rw [cell] at found
      cases found
      exact ⟨_, _, rfl, leftUnfolds, rightUnfolds⟩
  | closure found _ _ =>
      rw [cell] at found
      cases found

theorem Unfolds.cell_closure {heap : Heap} {address : Nat} {body : Code} {environmentWord : Word}
    {native : NativeValue} (unfolds : Unfolds heap (.ref address) native)
    (cell : heap[address]? = some (.closure body environmentWord)) :
    ∃ environment, native = .closure body environment ∧ TreeCode body ∧
      Unfolds heap environmentWord environment := by
  cases unfolds with
  | closure found bodyTree environmentUnfolds =>
      rw [cell] at found
      cases found
      exact ⟨_, rfl, bodyTree, environmentUnfolds⟩
  | pair found _ _ =>
      rw [cell] at found
      cases found

/-- A value-graph configuration over tree code and a tree configuration with the
same code, whose register and stack words unfold to the tree values. -/
structure Related (state : State) (tree : CategoricalAbstractMachine.State) : Prop where
  register : Unfolds state.heap state.register tree.register
  code : state.code = tree.code
  treeCode : TreeCode state.code
  stack : List.Forall₂ (Unfolds state.heap) state.stack tree.stack

theorem forall₂_mono {heap heap' : Heap} (extended : heap <+: heap') {words : List Word}
    {natives : List NativeValue} (related : List.Forall₂ (Unfolds heap) words natives) :
    List.Forall₂ (Unfolds heap') words natives :=
  related.imp fun _ _ unfolds => unfolds.mono extended

/-- Every value-graph transition on tree code is one strict tree transition. -/
theorem Related.transition {state next : State} {tree : CategoricalAbstractMachine.State}
    (related : Related state tree) (transition : Transition state next) :
    ∃ tree', CategoricalAbstractMachine.Transition .strict tree tree' ∧ Related next tree' := by
  rcases state with ⟨register, code, stack, heap⟩
  rcases tree with ⟨treeRegister, treeCode, treeStack⟩
  obtain ⟨registerUnfolds, codeSame, codeTree, stackUnfolds⟩ := related
  simp only at registerUnfolds codeSame codeTree stackUnfolds
  subst codeSame
  cases transition with
  | first code stack heap cell =>
      obtain ⟨left, right, rfl, leftUnfolds, _⟩ := registerUnfolds.cell_pair cell
      exact ⟨_, .firstPair .strict left right code treeStack, leftUnfolds, rfl, codeTree.tail, stackUnfolds⟩
  | second code stack heap cell =>
      obtain ⟨left, right, rfl, _, rightUnfolds⟩ := registerUnfolds.cell_pair cell
      exact ⟨_, .secondPair .strict left right code treeStack, rightUnfolds, rfl, codeTree.tail, stackUnfolds⟩
  | cur word body code stack heap =>
      have bodyTree : TreeCode body := by
        cases codeTree.head with
        | cur bodyTree => exact bodyTree
      exact ⟨_, .cur .strict treeRegister body code treeStack,
        .closure allocated bodyTree (registerUnfolds.mono (List.prefix_append _ _)), rfl, codeTree.tail,
        forall₂_mono (List.prefix_append _ _) stackUnfolds⟩
  | push word code stack heap =>
      exact ⟨_, .push .strict treeRegister code treeStack, registerUnfolds, rfl, codeTree.tail,
        .cons registerUnfolds stackUnfolds⟩
  | swap word saved code stack heap =>
      cases stackUnfolds with
      | cons savedUnfolds restUnfolds =>
          exact ⟨_, .swap .strict treeRegister _ code _, savedUnfolds, rfl, codeTree.tail,
            .cons registerUnfolds restUnfolds⟩
  | cons word saved code stack heap =>
      cases stackUnfolds with
      | cons savedUnfolds restUnfolds =>
          exact ⟨_, .cons .strict treeRegister _ code _,
            .pair allocated (savedUnfolds.mono (List.prefix_append _ _))
              (registerUnfolds.mono (List.prefix_append _ _)), rfl, codeTree.tail,
            forall₂_mono (List.prefix_append _ _) restUnfolds⟩
  | app code stack heap couple closure =>
      obtain ⟨function, argument, rfl, functionUnfolds, argumentUnfolds⟩ := registerUnfolds.cell_pair couple
      obtain ⟨environment, rfl, bodyTree, environmentUnfolds⟩ := functionUnfolds.cell_closure closure
      exact ⟨_, .appClosure .strict environment argument _ code treeStack,
        .pair allocated (environmentUnfolds.mono (List.prefix_append _ _))
          (argumentUnfolds.mono (List.prefix_append _ _)), rfl, bodyTree.append codeTree.tail,
        forall₂_mono (List.prefix_append _ _) stackUnfolds⟩
  | quote word value code stack heap =>
      exact ⟨_, .quote .strict treeRegister value code treeStack, .literal value, rfl, codeTree.tail,
        stackUnfolds⟩
  | branch selected saved whenTrue whenFalse code stack heap =>
      cases registerUnfolds
      cases stackUnfolds with
      | cons savedUnfolds restUnfolds =>
          have arms : TreeCode whenTrue ∧ TreeCode whenFalse := by
            cases codeTree.head with
            | branch trueTree falseTree => exact ⟨trueTree, falseTree⟩
          cases selected
          · exact ⟨_, .branchFalse .strict _ whenTrue whenFalse code _, savedUnfolds, rfl,
              arms.2.append codeTree.tail, restUnfolds⟩
          · exact ⟨_, .branchTrue .strict _ whenTrue whenFalse code _, savedUnfolds, rfl,
              arms.1.append codeTree.tail, restUnfolds⟩
  | operation | wind | freeze | force | skip => cases codeTree.head

/-- Every strict tree transition is matched by one value-graph transition. -/
theorem Related.tree_transition {state : State} {tree tree' : CategoricalAbstractMachine.State}
    (related : Related state tree) (transition : CategoricalAbstractMachine.Transition .strict tree tree') :
    ∃ next, Transition state next ∧ Related next tree' := by
  rcases state with ⟨register, code, stack, heap⟩
  rcases tree with ⟨treeRegister, treeCode, treeStack⟩
  obtain ⟨registerUnfolds, codeSame, codeTree, stackUnfolds⟩ := related
  simp only at registerUnfolds codeSame codeTree stackUnfolds
  subst codeSame
  cases transition with
  | firstPair _ left right code _ =>
      obtain ⟨address, leftWord, rightWord, rfl, cell, leftUnfolds, _⟩ := registerUnfolds.pair_inv
      exact ⟨_, .first code stack heap cell, leftUnfolds, rfl, codeTree.tail, stackUnfolds⟩
  | secondPair _ left right code _ =>
      obtain ⟨address, leftWord, rightWord, rfl, cell, _, rightUnfolds⟩ := registerUnfolds.pair_inv
      exact ⟨_, .second code stack heap cell, rightUnfolds, rfl, codeTree.tail, stackUnfolds⟩
  | cur _ _ body code _ =>
      have bodyTree : TreeCode body := by
        cases codeTree.head with
        | cur bodyTree => exact bodyTree
      exact ⟨_, .cur register body code stack heap,
        .closure allocated bodyTree (registerUnfolds.mono (List.prefix_append _ _)), rfl, codeTree.tail,
        forall₂_mono (List.prefix_append _ _) stackUnfolds⟩
  | push _ _ code _ =>
      exact ⟨_, .push register code stack heap, registerUnfolds, rfl, codeTree.tail,
        .cons registerUnfolds stackUnfolds⟩
  | swap _ _ saved code _ =>
      cases stackUnfolds with
      | cons savedUnfolds restUnfolds =>
          exact ⟨_, .swap register _ code _ heap, savedUnfolds, rfl, codeTree.tail,
            .cons registerUnfolds restUnfolds⟩
  | cons _ _ saved code _ =>
      cases stackUnfolds with
      | cons savedUnfolds restUnfolds =>
          exact ⟨_, .cons register _ code _ heap,
            .pair allocated (savedUnfolds.mono (List.prefix_append _ _))
              (registerUnfolds.mono (List.prefix_append _ _)), rfl, codeTree.tail,
            forall₂_mono (List.prefix_append _ _) restUnfolds⟩
  | appClosure _ environment argument body code _ =>
      obtain ⟨address, functionWord, argumentWord, rfl, couple, functionUnfolds, argumentUnfolds⟩ :=
        registerUnfolds.pair_inv
      obtain ⟨function, environmentWord, rfl, closure, bodyTree, environmentUnfolds⟩ :=
        functionUnfolds.closure_inv
      exact ⟨_, .app code stack heap couple closure,
        .pair allocated (environmentUnfolds.mono (List.prefix_append _ _))
          (argumentUnfolds.mono (List.prefix_append _ _)), rfl, bodyTree.append codeTree.tail,
        forall₂_mono (List.prefix_append _ _) stackUnfolds⟩
  | quote _ _ value code _ =>
      exact ⟨_, .quote register value code stack heap, .literal value, rfl, codeTree.tail, stackUnfolds⟩
  | branchTrue _ _ whenTrue whenFalse code _ =>
      cases registerUnfolds
      cases stackUnfolds with
      | cons savedUnfolds restUnfolds =>
          have arms : TreeCode whenTrue := by
            cases codeTree.head with
            | branch trueTree _ => exact trueTree
          exact ⟨_, .branch true _ whenTrue whenFalse code _ heap, savedUnfolds, rfl,
            arms.append codeTree.tail, restUnfolds⟩
  | branchFalse _ _ whenTrue whenFalse code _ =>
      cases registerUnfolds
      cases stackUnfolds with
      | cons savedUnfolds restUnfolds =>
          have arms : TreeCode whenFalse := by
            cases codeTree.head with
            | branch _ falseTree => exact falseTree
          exact ⟨_, .branch false _ whenTrue whenFalse code _ heap, savedUnfolds, rfl,
            arms.append codeTree.tail, restUnfolds⟩

theorem Related.steps {state final : State} {tree : CategoricalAbstractMachine.State}
    (related : Related state tree) (run : Steps state final) :
    ∃ tree', CategoricalAbstractMachine.Steps .strict tree tree' ∧ Related final tree' := by
  induction run with
  | refl => exact ⟨tree, .refl, related⟩
  | tail _ transition ih =>
      obtain ⟨middle, middleRun, middleRelated⟩ := ih
      obtain ⟨tree', treeTransition, related'⟩ := middleRelated.transition transition
      exact ⟨tree', middleRun.tail treeTransition, related'⟩

theorem Related.tree_steps {state : State} {tree final : CategoricalAbstractMachine.State}
    (related : Related state tree) (run : CategoricalAbstractMachine.Steps .strict tree final) :
    ∃ state', Steps state state' ∧ Related state' final := by
  induction run with
  | refl => exact ⟨state, .refl, related⟩
  | tail _ transition ih =>
      obtain ⟨middle, middleRun, middleRelated⟩ := ih
      obtain ⟨next, storeTransition, related'⟩ := middleRelated.tree_transition transition
      exact ⟨next, middleRun.tail storeTransition, related'⟩

theorem Related.completed_iff {state : State} {tree : CategoricalAbstractMachine.State}
    (related : Related state tree) :
    (state.code = [] ∧ state.stack = []) ↔ (tree.code = [] ∧ tree.stack = []) := by
  rw [related.code]
  constructor
  · rintro ⟨code, stack⟩
    have lengths := related.stack.length_eq
    rw [stack] at lengths
    exact ⟨code, List.eq_nil_of_length_eq_zero lengths.symm⟩
  · rintro ⟨code, stack⟩
    have lengths := related.stack.length_eq
    rw [stack] at lengths
    exact ⟨code, List.eq_nil_of_length_eq_zero lengths⟩

/-- Related configurations complete together; the answer word unfolds to the tree answer. -/
theorem Related.completes_iff {state : State} {tree : CategoricalAbstractMachine.State}
    (related : Related state tree) :
    (∃ result final, Steps state ⟨result, [], [], final⟩) ↔
      ∃ native, CategoricalAbstractMachine.Steps .strict tree ⟨native, [], []⟩ := by
  constructor
  · rintro ⟨result, final, run⟩
    obtain ⟨tree', treeRun, related'⟩ := related.steps run
    obtain ⟨code, stack⟩ := related'.completed_iff.mp ⟨rfl, rfl⟩
    rcases tree' with ⟨native, treeCode, treeStack⟩
    simp only at code stack
    subst code stack
    exact ⟨native, treeRun⟩
  · rintro ⟨native, treeRun⟩
    obtain ⟨state', run, related'⟩ := related.tree_steps treeRun
    obtain ⟨code, stack⟩ := related'.completed_iff.mpr ⟨rfl, rfl⟩
    rcases state' with ⟨result, storeCode, storeStack, final⟩
    simp only at code stack
    subst code stack
    exact ⟨result, final, run⟩

/-- The tree compiler's code runs on the value graph exactly as the tree
machine's strict profile runs it; its completed answers are tree source values. -/
theorem tree_source_completion {term : Source true} {environment : SourceValue true} {heap final : Heap}
    {word result : Word} (unfolds : Unfolds heap word (encodeSourceValue environment))
    (run : Steps ⟨word, compileSource term, [], heap⟩ ⟨result, [], [], final⟩) :
    ∃ value, CategoricalAbstractMachine.Evaluation term environment value ∧
      Unfolds final result (encodeSourceValue value) := by
  have related : Related ⟨word, compileSource term, [], heap⟩
      ⟨encodeSourceValue environment, compileSource term, []⟩ :=
    ⟨unfolds, rfl, compileSource_tree term, .nil⟩
  obtain ⟨tree', treeRun, related'⟩ := related.steps run
  obtain ⟨code, stack⟩ := related'.completed_iff.mp ⟨rfl, rfl⟩
  rcases tree' with ⟨native, treeCode, treeStack⟩
  simp only at code stack
  subst code stack
  obtain ⟨value, evaluated, encoded⟩ :=
    CategoricalAbstractMachine.execution_complete (CategoricalAbstractMachine.Typed.strict_steps_neutral treeRun)
  exact ⟨value, evaluated, encoded ▸ related'.register⟩

/-! ### The common simulation interface -/

open Mettapedia.GSLT.Distinction.ProductiveBlocks in
/-- The value-graph runner observed by occurrence count and completion only. -/
def storeTicks : Machine State Unit Unit Empty := machine.relabel (fun _ => ()) (fun _ => ()) id

open Mettapedia.GSLT.Distinction.ProductiveBlocks in
/-- The strict tree runner observed by occurrence count and completion only. -/
def treeTicks : Machine CategoricalAbstractMachine.State Unit Unit Empty :=
  (CategoricalAbstractMachine.machine .strict).relabel (fun _ => ()) (fun _ => ()) id

open Mettapedia.GSLT.Distinction.ProductiveBlocks in
theorem storeTicks_step (state : State) :
    storeTicks.step state =
      match answer state with
      | some _ => some (.finish ())
      | none => (step state).map fun next => .publish [()] next := by
  simp only [storeTicks, machine, Machine.relabel, ProductiveCoreAdapters.answerMachine, answerCore, core]
  cases answer state <;> cases step state <;> rfl

open Mettapedia.GSLT.Distinction.ProductiveBlocks in
theorem treeTicks_step (state : CategoricalAbstractMachine.State) :
    treeTicks.step state =
      match CategoricalAbstractMachine.answer state with
      | some _ => some (.finish ())
      | none => (CategoricalAbstractMachine.step .strict state).map fun next => .publish [()] next := by
  simp only [treeTicks, CategoricalAbstractMachine.machine, Machine.relabel,
    ProductiveCoreAdapters.answerMachine, CategoricalAbstractMachine.answerCore,
    CategoricalAbstractMachine.sourceAnswerCore, CategoricalAbstractMachine.sourceCore]
  cases CategoricalAbstractMachine.answer state <;> cases CategoricalAbstractMachine.step .strict state <;> rfl

theorem answer_none_iff (state : State) : answer state = none ↔ ¬ (state.code = [] ∧ state.stack = []) := by
  rcases state with ⟨register, code, stack, heap⟩
  cases code <;> cases stack <;> simp [answer]

theorem tree_answer_none_iff (state : CategoricalAbstractMachine.State) :
    CategoricalAbstractMachine.answer state = none ↔ ¬ (state.code = [] ∧ state.stack = []) := by
  rcases state with ⟨register, code, stack⟩
  cases code <;> cases stack <;> simp [CategoricalAbstractMachine.answer]

open Mettapedia.GSLT.Distinction.ProductiveBlocks in
/-- Lock-step refinement: each value-graph occurrence on tree code is one strict
tree occurrence, and completion is matched at the same boundary. -/
theorem refinement : CostSimulation storeTicks treeTicks Related 1 where
  silent := by
    intro state tree next _ stepped
    rw [storeTicks_step] at stepped
    cases observed : answer state <;> cases advanced : step state <;> simp [observed, advanced] at stepped
  publish := by
    intro state tree events next related stepped
    rw [storeTicks_step] at stepped
    cases observed : answer state with
    | some _ => simp [observed] at stepped
    | none =>
        cases advanced : step state with
        | none => simp [observed, advanced] at stepped
        | some following =>
            simp only [observed, advanced, Option.map_some, Option.some.injEq, Transition.publish.injEq] at stepped
            obtain ⟨rfl, rfl⟩ := stepped
            obtain ⟨tree', treeTransition, related'⟩ := related.transition (step_sound advanced)
            have treeObserved : CategoricalAbstractMachine.answer tree = none :=
              (tree_answer_none_iff tree).mpr fun completed =>
                ((answer_none_iff state).mp observed) (related.completed_iff.mpr completed)
            refine ⟨1, le_rfl, tree', ?_, related'⟩
            simp only [Machine.run, treeTicks_step, treeObserved,
              CategoricalAbstractMachine.step_complete treeTransition, Option.map_some]
            rfl
  finish := by
    intro state tree verdict related stepped
    rw [storeTicks_step] at stepped
    cases observed : answer state with
    | none => cases advanced : step state <;> simp [observed, advanced] at stepped
    | some completed =>
        have done : state.code = [] ∧ state.stack = [] := by
          have := (answer_iff state completed).mp observed
          rw [this]
          exact ⟨rfl, rfl⟩
        obtain ⟨code, stack⟩ := related.completed_iff.mp done
        rcases tree with ⟨native, treeCode, treeStack⟩
        simp only at code stack
        subst code stack
        refine ⟨1, le_rfl, ?_⟩
        simp only [Machine.run, treeTicks_step, CategoricalAbstractMachine.answer]
  fail := by
    intro state tree events _ stepped
    rw [storeTicks_step] at stepped
    cases observed : answer state <;> cases advanced : step state <;> simp [observed, advanced] at stepped
  call := by
    intro state tree request saved _ stepped
    rw [storeTicks_step] at stepped
    cases observed : answer state <;> cases advanced : step state <;> simp [observed, advanced] at stepped

open Mettapedia.GSLT.Distinction.ProductiveBlocks in
/-- The converse lock-step simulation: each strict tree occurrence on tree code is
one value-graph occurrence. -/
theorem abstraction : CostSimulation treeTicks storeTicks (fun tree state => Related state tree) 1 where
  silent := by
    intro tree state next _ stepped
    rw [treeTicks_step] at stepped
    cases observed : CategoricalAbstractMachine.answer tree <;>
      cases advanced : CategoricalAbstractMachine.step .strict tree <;> simp [observed, advanced] at stepped
  publish := by
    intro tree state events next related stepped
    rw [treeTicks_step] at stepped
    cases observed : CategoricalAbstractMachine.answer tree with
    | some _ => simp [observed] at stepped
    | none =>
        cases advanced : CategoricalAbstractMachine.step .strict tree with
        | none => simp [observed, advanced] at stepped
        | some following =>
            simp only [observed, advanced, Option.map_some, Option.some.injEq, Transition.publish.injEq] at stepped
            obtain ⟨rfl, rfl⟩ := stepped
            obtain ⟨state', storeTransition, related'⟩ :=
              related.tree_transition (CategoricalAbstractMachine.step_sound advanced)
            have storeObserved : answer state = none :=
              (answer_none_iff state).mpr fun completed =>
                ((tree_answer_none_iff tree).mp observed) (related.completed_iff.mp completed)
            refine ⟨1, le_rfl, state', ?_, related'⟩
            simp only [Machine.run, storeTicks_step, storeObserved, step_complete storeTransition,
              Option.map_some]
            rfl
  finish := by
    intro tree state verdict related stepped
    rw [treeTicks_step] at stepped
    cases observed : CategoricalAbstractMachine.answer tree with
    | none => cases advanced : CategoricalAbstractMachine.step .strict tree <;> simp [observed, advanced] at stepped
    | some completed =>
        have done : tree.code = [] ∧ tree.stack = [] := by
          have := (CategoricalAbstractMachine.answer_iff tree completed).mp observed
          rw [this]
          exact ⟨rfl, rfl⟩
        obtain ⟨code, stack⟩ := related.completed_iff.mpr done
        rcases state with ⟨register, storeCode, storeStack, heap⟩
        simp only at code stack
        subst code stack
        refine ⟨1, le_rfl, ?_⟩
        simp only [Machine.run, storeTicks_step, answer]
  fail := by
    intro tree state events _ stepped
    rw [treeTicks_step] at stepped
    cases observed : CategoricalAbstractMachine.answer tree <;>
      cases advanced : CategoricalAbstractMachine.step .strict tree <;> simp [observed, advanced] at stepped
  call := by
    intro tree state request saved _ stepped
    rw [treeTicks_step] at stepped
    cases observed : CategoricalAbstractMachine.answer tree <;>
      cases advanced : CategoricalAbstractMachine.step .strict tree <;> simp [observed, advanced] at stepped

open Mettapedia.GSLT.Distinction.ProductiveBlocks in
/-- Stopped configurations are matched in both directions at the same lookup. -/
theorem refinement_stuck : MatchesStuck storeTicks treeTicks Related 1 := by
  intro state tree related stopped
  rw [storeTicks_step] at stopped
  cases observed : answer state with
  | some _ => simp [observed] at stopped
  | none =>
      have advanced : step state = none := by
        cases found : step state <;> simp_all
      have treeObserved : CategoricalAbstractMachine.answer tree = none :=
        (tree_answer_none_iff tree).mpr fun completed =>
          ((answer_none_iff state).mp observed) (related.completed_iff.mpr completed)
      have treeAdvanced : CategoricalAbstractMachine.step .strict tree = none := by
        cases found : CategoricalAbstractMachine.step .strict tree with
        | none => rfl
        | some following =>
            obtain ⟨next, storeTransition, _⟩ :=
              related.tree_transition (CategoricalAbstractMachine.step_sound found)
            rw [step_complete storeTransition] at advanced
            cases advanced
      refine ⟨1, le_rfl, tree, ?_, related⟩
      simp only [Machine.run, treeTicks_step, treeObserved, treeAdvanced, Option.map_none]

open Mettapedia.GSLT.Distinction.ProductiveBlocks in
theorem abstraction_stuck : MatchesStuck treeTicks storeTicks (fun tree state => Related state tree) 1 := by
  intro tree state related stopped
  rw [treeTicks_step] at stopped
  cases observed : CategoricalAbstractMachine.answer tree with
  | some _ => simp [observed] at stopped
  | none =>
      have advanced : CategoricalAbstractMachine.step .strict tree = none := by
        cases found : CategoricalAbstractMachine.step .strict tree <;> simp_all
      have storeObserved : answer state = none :=
        (answer_none_iff state).mpr fun completed =>
          ((tree_answer_none_iff tree).mp observed) (related.completed_iff.mp completed)
      have storeAdvanced : step state = none := by
        cases found : step state with
        | none => rfl
        | some following =>
            obtain ⟨tree', treeTransition, _⟩ := related.transition (step_sound found)
            rw [CategoricalAbstractMachine.step_complete treeTransition] at advanced
            cases advanced
      refine ⟨1, le_rfl, state, ?_, related⟩
      simp only [Machine.run, storeTicks_step, storeObserved, storeAdvanced, Option.map_none]

open Mettapedia.GSLT.Distinction.ProductiveBlocks in
/-- The actual graph/tree refinement is a client of relational block
composition for every declared public readout. Its stuck law is supplied by
the graph/tree comparison, rather than assumed away by the adapter. -/
theorem relational_refinement {PublicEvent PublicVerdict PublicRequest : Type}
    (readout : ExecutionReadout Unit Unit Empty PublicEvent PublicVerdict PublicRequest) :
    DerivationSimulation (fun state action => storeTicks.step state = action)
      (fun state action => treeTicks.step state = action) Related readout readout :=
  refinement.toDerivationSimulation refinement_stuck readout

open Mettapedia.GSLT.Distinction.ProductiveBlocks in
theorem relational_abstraction {PublicEvent PublicVerdict PublicRequest : Type}
    (readout : ExecutionReadout Unit Unit Empty PublicEvent PublicVerdict PublicRequest) :
    DerivationSimulation (fun state action => treeTicks.step state = action)
      (fun state action => storeTicks.step state = action) (fun tree state => Related state tree) readout readout :=
  abstraction.toDerivationSimulation abstraction_stuck readout

open Mettapedia.GSLT.Distinction.ProductiveBlocks ProductiveCoreAdapters in
/-- Scheduling the graph realization preserves the tree machine's public
occurrences and related retained endpoint, at independently priced allowances.
This uses the graph/tree representation relation, including the caller stack;
it does not identify heap words with tree syntax. -/
theorem scheduled_refinement {PublicEvent PublicVerdict PublicRequest : Type}
    (readout : ExecutionReadout Unit Unit Empty PublicEvent PublicVerdict PublicRequest)
    (graphPrice : State → Nat) (treePrice : CategoricalAbstractMachine.State → Nat)
    (fuel : Nat) {state : State} {tree : CategoricalAbstractMachine.State} (related : Related state tree) :
    ∃ count,
      let graphRun := Cursor.advance (EventCursor.provider storeTicks) EventCursor.client
        (EventCursor.charge storeTicks graphPrice) fuel (EventCursor.packet storeTicks ([], .exhausted state))
      let treeRun := Cursor.advance (EventCursor.provider treeTicks) EventCursor.client
        (EventCursor.charge treeTicks treePrice) count (EventCursor.packet treeTicks ([], .exhausted tree))
      graphRun.1 = storeTicks.spent graphPrice fuel state ∧
      treeRun.1 = treeTicks.spent treePrice count tree ∧
      (EventCursor.read storeTicks graphRun.2).1.flatMap readout.event =
        (EventCursor.read treeTicks treeRun.2).1.flatMap readout.event ∧
      OutcomeRel Related ((EventCursor.read storeTicks graphRun.2).2.relabel readout.verdict readout.request)
        ((EventCursor.read treeTicks treeRun.2).2.relabel readout.verdict readout.request) :=
  EventCursor.advance_machines storeTicks treeTicks (relational_refinement readout)
    graphPrice treePrice fuel related

open Mettapedia.GSLT.Distinction.ProductiveBlocks ProductiveCoreAdapters in
/-- The converse scheduled comparison is constructed from the tree-to-graph
simulation. Forward scheduled transport alone would not give reflection. -/
theorem scheduled_abstraction {PublicEvent PublicVerdict PublicRequest : Type}
    (readout : ExecutionReadout Unit Unit Empty PublicEvent PublicVerdict PublicRequest)
    (treePrice : CategoricalAbstractMachine.State → Nat) (graphPrice : State → Nat)
    (fuel : Nat) {tree : CategoricalAbstractMachine.State} {state : State} (related : Related state tree) :
    ∃ count,
      let treeRun := Cursor.advance (EventCursor.provider treeTicks) EventCursor.client
        (EventCursor.charge treeTicks treePrice) fuel (EventCursor.packet treeTicks ([], .exhausted tree))
      let graphRun := Cursor.advance (EventCursor.provider storeTicks) EventCursor.client
        (EventCursor.charge storeTicks graphPrice) count (EventCursor.packet storeTicks ([], .exhausted state))
      treeRun.1 = treeTicks.spent treePrice fuel tree ∧
      graphRun.1 = storeTicks.spent graphPrice count state ∧
      (EventCursor.read treeTicks treeRun.2).1.flatMap readout.event =
        (EventCursor.read storeTicks graphRun.2).1.flatMap readout.event ∧
      OutcomeRel (fun tree state => Related state tree)
        ((EventCursor.read treeTicks treeRun.2).2.relabel readout.verdict readout.request)
        ((EventCursor.read storeTicks graphRun.2).2.relabel readout.verdict readout.request) :=
  EventCursor.advance_machines treeTicks storeTicks (relational_abstraction readout)
    treePrice graphPrice fuel related

/-- An active-rule tree derivation runs on the strict tree profile, with arbitrary
caller code and stack retained. -/
theorem TreeStrict.strict_execution_tail {term : Source true} {environment value : SourceValue true}
    (derivation : TreeStrict term environment value) (code : Code) (stack : List NativeValue) :
    CategoricalAbstractMachine.Steps .strict
      ⟨encodeSourceValue environment, compileSource term ++ code, stack⟩
      ⟨encodeSourceValue value, code, stack⟩ := by
  induction derivation generalizing code stack with
  | varZero environment value => exact .single (.secondPair .strict _ _ _ _)
  | @varSucc index environment value saved _ ih =>
      simpa only [CategoricalAbstractMachine.compile_var_succ, List.cons_append, encodeSourceValue] using
        Relation.ReflTransGen.head (CategoricalAbstractMachine.Transition.firstPair .strict
          (encodeSourceValue environment) (encodeSourceValue saved)
          (compileSource (extended := true) (.var index) ++ code) stack) (ih code stack)
  | literal value environment => exact .single (.quote .strict _ _ _ _)
  | @conditional condition whenTrue whenFalse environment value selected _ _ conditionIH selectedIH =>
      simp only [compileSource, List.cons_append, List.append_assoc]
      have conditionRun := conditionIH (.branch (compileSource whenTrue) (compileSource whenFalse) :: code)
        (encodeSourceValue environment :: stack)
      have selectedRun := selectedIH code stack
      have chosen := CategoricalAbstractMachine.step_sound (CategoricalAbstractMachine.branch_step .strict
        selected (encodeSourceValue environment) (compileSource whenTrue) (compileSource whenFalse) code stack)
      cases selected <;> simp only [Bool.false_eq_true, if_false, if_true] at selectedRun chosen
      · exact .head (.push .strict _ _ _) (conditionRun.trans (.head chosen selectedRun))
      · exact .head (.push .strict _ _ _) (conditionRun.trans (.head chosen selectedRun))
  | lam body environment => exact .single (.cur .strict _ _ _ _)
  | @pair left right environment leftValue rightValue _ _ leftIH rightIH =>
      simp only [compileSource, List.append_assoc, List.cons_append, List.nil_append]
      have leftRun := leftIH (.swap :: (compileSource right ++ .cons :: code))
        (encodeSourceValue environment :: stack)
      have rightRun := rightIH (.cons :: code) (encodeSourceValue leftValue :: stack)
      exact .head (.push .strict _ _ _) (leftRun.trans
        (.head (.swap .strict _ _ _ _) (rightRun.tail (.cons .strict _ _ _ _))))
  | @app operator argument body environment captured operand value _ _ _ operatorIH argumentIH bodyIH =>
      simp only [compileSource, List.append_assoc, List.cons_append, List.nil_append]
      have operatorRun := operatorIH
        (.swap :: (compileSource argument ++ .cons :: .app :: code)) (encodeSourceValue environment :: stack)
      have argumentRun := argumentIH (.cons :: .app :: code)
        (encodeSourceValue (.closure body captured) :: stack)
      have bodyRun := bodyIH code stack
      exact .head (.push .strict _ _ _) (operatorRun.trans
        (.head (.swap .strict _ _ _ _) ((argumentRun.tail (.cons .strict _ _ _ _)).trans
          (.head (.appClosure .strict _ _ _ _ _) bodyRun))))
  | @first term environment left right _ ih =>
      simpa only [compileSource, List.append_assoc, List.singleton_append] using
        (ih (.first :: code) stack).tail (.firstPair .strict _ _ _ _)
  | @second term environment left right _ ih =>
      simpa only [compileSource, List.append_assoc, List.singleton_append] using
        (ih (.second :: code) stack).tail (.secondPair .strict _ _ _ _)

/-- Conversely, an active-rule tree derivation runs on the value graph from any
heap in which the environment word unfolds to the environment. -/
theorem tree_source_execution {term : Source true} {environment value : SourceValue true} {heap : Heap}
    {word : Word} (derivation : TreeStrict term environment value)
    (unfolds : Unfolds heap word (encodeSourceValue environment)) :
    ∃ result final, Steps ⟨word, compileSource term, [], heap⟩ ⟨result, [], [], final⟩ ∧
      Unfolds final result (encodeSourceValue value) := by
  have related : Related ⟨word, compileSource term, [], heap⟩
      ⟨encodeSourceValue environment, compileSource term, []⟩ :=
    ⟨unfolds, rfl, compileSource_tree term, .nil⟩
  have treeRun := derivation.strict_execution_tail [] []
  simp only [List.append_nil] at treeRun
  obtain ⟨state', run, related'⟩ := related.tree_steps treeRun
  obtain ⟨code, stack⟩ := related'.completed_iff.mpr ⟨rfl, rfl⟩
  rcases state' with ⟨result, storeCode, storeStack, final⟩
  simp only at code stack
  subst code stack
  exact ⟨result, final, run, related'.register⟩

/-! ### Topological order -/

/-- The word refers only below the bound. -/
def Word.Below : Word → Nat → Prop
  | .ref address, bound => address < bound
  | _, _ => True

/-- The words stored in a cell. -/
def Cell.words : Cell → List Word
  | .pair left right => [left, right]
  | .closure _ environment => [environment]
  | .laze _ environment => [environment]

/-- Each cell refers only to smaller addresses. -/
def Ordered (heap : Heap) : Prop :=
  ∀ (address : Nat) (cell : Cell), heap[address]? = some cell → ∀ word ∈ cell.words, word.Below address

/-- Cells with a tree counterpart: couples and closures over tree code. -/
def TreeCell : Cell → Prop
  | .pair _ _ => True
  | .closure body _ => TreeCode body
  | .laze _ _ => False

def TreeHeap (heap : Heap) : Prop :=
  ∀ (address : Nat) (cell : Cell), heap[address]? = some cell → TreeCell cell

/-- On an ordered heap of tree cells, every word below the heap length unfolds. -/
theorem ordered_unfolds {heap : Heap} (ordered : Ordered heap) (treeHeap : TreeHeap heap) :
    ∀ word, word.Below heap.length → ∃ native, Unfolds heap word native := by
  have references : ∀ address, address < heap.length → ∃ native, Unfolds heap (.ref address) native := by
    intro address
    induction address using Nat.strong_induction_on with
    | _ address ih =>
    intro bounded
    have words : ∀ word, word.Below address → ∃ native, Unfolds heap word native := by
      intro word below
      cases word with
      | unit => exact ⟨_, .unit⟩
      | literal value => exact ⟨_, .literal value⟩
      | ref target => exact ih target below (Nat.lt_trans below bounded)
    cases found : heap[address]? with
    | none => simp at found; omega
    | some cell =>
        have below := ordered address cell found
        cases cell with
        | pair left right =>
            obtain ⟨leftNative, leftUnfolds⟩ := words left (below left (by simp [Cell.words]))
            obtain ⟨rightNative, rightUnfolds⟩ := words right (below right (by simp [Cell.words]))
            exact ⟨_, .pair found leftUnfolds rightUnfolds⟩
        | closure body environment =>
            obtain ⟨environmentNative, environmentUnfolds⟩ :=
              words environment (below environment (by simp [Cell.words]))
            exact ⟨_, .closure found (treeHeap address _ found) environmentUnfolds⟩
        | laze body environment => exact False.elim (treeHeap address _ found)
  intro word below
  cases word with
  | unit => exact ⟨_, .unit⟩
  | literal value => exact ⟨_, .literal value⟩
  | ref address => exact references address below

theorem Word.Below.mono {word : Word} {bound bound' : Nat} (below : word.Below bound) (larger : bound ≤ bound') :
    word.Below bound' := by
  cases word with
  | ref address => exact Nat.lt_of_lt_of_le below larger
  | unit | literal _ => trivial

/-- Allocating a cell whose words lie below the heap length keeps the heap ordered. -/
theorem Ordered.allocate {heap : Heap} {cell : Cell} (ordered : Ordered heap)
    (below : ∀ word ∈ cell.words, word.Below heap.length) : Ordered (heap ++ [cell]) := by
  intro address found lookup word member
  rcases Nat.lt_or_ge address heap.length with inside | outside
  · rw [List.getElem?_append_left inside] at lookup
    exact ordered address found lookup word member
  · rw [List.getElem?_append_right outside] at lookup
    have same : address = heap.length := by
      have := (List.getElem?_eq_some_iff.mp lookup).1
      simp at this
      omega
    subst same
    simp only [Nat.sub_self, List.getElem?_cons_zero, Option.some.injEq] at lookup
    subst lookup
    exact below word member

theorem TreeHeap.allocate {heap : Heap} {cell : Cell} (treeHeap : TreeHeap heap) (tree : TreeCell cell) :
    TreeHeap (heap ++ [cell]) := by
  intro address found lookup
  rcases Nat.lt_or_ge address heap.length with inside | outside
  · rw [List.getElem?_append_left inside] at lookup
    exact treeHeap address found lookup
  · rw [List.getElem?_append_right outside] at lookup
    have same : address - heap.length = 0 := by
      have := (List.getElem?_eq_some_iff.mp lookup).1
      simp at this
      omega
    rw [same] at lookup
    simp only [List.getElem?_cons_zero, Option.some.injEq] at lookup
    subst lookup
    exact tree

/-- The configuration refers only into its heap. -/
def Bounded (state : State) : Prop :=
  state.register.Below state.heap.length ∧ ∀ word ∈ state.stack, word.Below state.heap.length

theorem cell_word_below {heap : Heap} (ordered : Ordered heap) {address : Nat} {cell : Cell}
    (found : heap[address]? = some cell) {word : Word} (member : word ∈ cell.words) :
    word.Below heap.length :=
  (ordered address cell found word member).mono
    (Nat.le_of_lt (List.getElem?_eq_some_iff.mp found).1)

/-- Transitions on tree code allocate below the heap length and never update a
cell, so a bounded configuration over an ordered heap of tree cells stays so. -/
theorem Transition.ordered {state next : State} (transition : Transition state next)
    (codeTree : TreeCode state.code) (ordered : Ordered state.heap) (treeHeap : TreeHeap state.heap)
    (bounded : Bounded state) : Ordered next.heap ∧ TreeHeap next.heap ∧ Bounded next := by
  obtain ⟨registerBelow, stackBelow⟩ := bounded
  cases transition with
  | first code stack heap cell =>
      exact ⟨ordered, treeHeap, cell_word_below ordered cell (by simp [Cell.words]), stackBelow⟩
  | second code stack heap cell =>
      exact ⟨ordered, treeHeap, cell_word_below ordered cell (by simp [Cell.words]), stackBelow⟩
  | cur word body code stack heap =>
      have bodyTree : TreeCode body := by
        cases codeTree.head with
        | cur bodyTree => exact bodyTree
      refine ⟨ordered.allocate (by simpa [Cell.words] using registerBelow), treeHeap.allocate bodyTree,
        by simp [Word.Below], ?_⟩
      intro word member
      exact (stackBelow word member).mono (by simp)
  | push word code stack heap =>
      refine ⟨ordered, treeHeap, registerBelow, ?_⟩
      intro word member
      rcases List.mem_cons.mp member with rfl | member
      · exact registerBelow
      · exact stackBelow word member
  | swap word saved code stack heap =>
      refine ⟨ordered, treeHeap, stackBelow saved (by simp), ?_⟩
      intro word' member
      rcases List.mem_cons.mp member with rfl | member
      · exact registerBelow
      · exact stackBelow word' (List.mem_cons_of_mem _ member)
  | cons word saved code stack heap =>
      refine ⟨ordered.allocate ?_, treeHeap.allocate trivial, by simp [Word.Below], ?_⟩
      · intro word' member
        simp only [Cell.words, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact stackBelow word' (by simp)
        · exact registerBelow
      · intro word' member
        exact (stackBelow word' (List.mem_cons_of_mem _ member)).mono (by simp)
  | app code stack heap couple closure =>
      refine ⟨ordered.allocate ?_, treeHeap.allocate trivial, by simp [Word.Below], ?_⟩
      · intro word' member
        simp only [Cell.words, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl
        · exact cell_word_below ordered closure (by simp [Cell.words])
        · exact cell_word_below ordered couple (by simp [Cell.words])
      · intro word' member
        exact (stackBelow word' member).mono (by simp)
  | quote word value code stack heap => exact ⟨ordered, treeHeap, trivial, stackBelow⟩
  | branch selected saved whenTrue whenFalse code stack heap =>
      refine ⟨ordered, treeHeap, stackBelow saved (by simp), ?_⟩
      intro word member
      exact stackBelow word (List.mem_cons_of_mem _ member)
  | operation | wind | freeze | force | skip => cases codeTree.head


/-- `wind` breaks topological order: its couple refers to the later closure. -/
theorem windHeap_not_ordered (heap : Heap) (word : Word) (body : Code) :
    ¬ Ordered (windHeap heap word body) := by
  intro ordered
  have below := ordered heap.length _ (windHeap_couple heap word body) (.ref (heap.length + 1))
    (by simp [Cell.words])
  simp [Word.Below] at below

/-- The cycle built by `wind` has no finite unfolding to a tree value. -/
theorem windHeap_no_unfolding (heap : Heap) (word : Word) (body : Code) (native : NativeValue) :
    ¬ Unfolds (windHeap heap word body) (.ref (heap.length + 1)) native := by
  have both : ∀ native : NativeValue, ¬ Unfolds (windHeap heap word body) (.ref (heap.length + 1)) native ∧
      ¬ Unfolds (windHeap heap word body) (.ref heap.length) native := by
    intro native
    induction native with
    | closure code environment environmentIH =>
        refine ⟨?_, ?_⟩
        · intro unfolds
          obtain ⟨environment', same, _, environmentUnfolds⟩ :=
            unfolds.cell_closure (windHeap_closure heap word body)
          cases same
          exact environmentIH.2 environmentUnfolds
        · intro unfolds
          obtain ⟨_, _, same, _, _⟩ := unfolds.cell_pair (windHeap_couple heap word body)
          cases same
    | pair left right _ rightIH =>
        refine ⟨?_, ?_⟩
        · intro unfolds
          obtain ⟨_, same, _, _⟩ := unfolds.cell_closure (windHeap_closure heap word body)
          cases same
        · intro unfolds
          obtain ⟨_, _, same, _, rightUnfolds⟩ := unfolds.cell_pair (windHeap_couple heap word body)
          cases same
          exact rightIH.1 rightUnfolds
    | unit | literal _ | first _ _ | second _ _ | app _ _ =>
        refine ⟨?_, ?_⟩ <;> intro unfolds <;> cases unfolds
  exact (both native).1


/-! ## Memoizing forcing on the value graph

The historical `unfreeze` instruction remains call by name. This realization
retains the same code, graph words, and append-only thunk identities, with a
separate persistent Need cache and an explicit stack of update continuations.
A producer runs to a forced value before its caller resumes; nested producers
therefore retain distinct pending updates. A completed cache is never reopened.
-/

namespace Need

open Mettapedia.Machines.BranchLocalNeed.NeedReference
open Mettapedia.Machines.BranchLocalNeed.NeedCacheLaws

abbrev Origin := Code × Word
abbrev Store := Mettapedia.Machines.BranchLocalNeed.NeedReference.Heap Origin Word Empty
abbrev Record := CellRecord Origin Word Empty

/-- A graph address is a stable cell identity within this sequential arena.
Branching hosts supply their own lineage/birth transport before sharing it. -/
def cellId (address : Nat) : CellId := ⟨0, [], address, 0⟩

theorem cellId_injective : Function.Injective cellId := by
  intro first second same
  exact congrArg CellId.slot same

def laze? (heap : Graph.Heap) : Word → Option Origin
  | .ref address => match heap[address]? with
    | some (.laze body environment) => some (body, environment)
    | _ => none
  | _ => none

@[simp] theorem laze?_eq_none (heap : Graph.Heap) (word : Word) :
    laze? heap word = none ↔ ¬ LazeAt heap word := by
  cases word with
  | unit | literal _ => simp [laze?, LazeAt]
  | ref address =>
      cases found : heap[address]? with
      | none => simp [laze?, found, LazeAt]
      | some cell => cases cell <;> simp [laze?, found, LazeAt]

structure Update where
  cell : CellId
  origin : Origin
  owner : Nat
  code : Code
  stack : List Word
  deriving DecidableEq, Repr

structure State where
  graph : Graph.State
  store : Store
  updates : List Update := []
  nextOwner : Nat := 0

def load (term : Term) : State :=
  ⟨⟨.unit, compile term, [], []⟩, .empty, [], 0⟩

/-- Allocation and ownership transfer are separate steps of the common Need
lifecycle. An already evaluating cell has no successful force transition. -/
def step (state : State) : Option State :=
  match state.graph with
  | ⟨word, [], [], heap⟩ =>
      match state.updates with
      | [] => none
      | update :: rest =>
          match state.store.lookup update.cell with
          | some record =>
              if record.origin = update.origin ∧ record.cache = .evaluating update.owner ∧
                  laze? heap word = none then
                some { state with
                  graph := ⟨word, update.code, update.stack, heap⟩
                  store := state.store.setKnownCache update.cell record (.value word)
                  updates := rest }
              else none
          | none => none
  | ⟨.ref address, .unfreeze :: code, stack, heap⟩ =>
      match heap[address]? with
      | some (.laze body environment) =>
          match state.store.lookup (cellId address) with
          | none => (state.store.allocate? (cellId address) (body, environment)).map fun store =>
              { state with store := store }
          | some record =>
              if record.origin = (body, environment) then
                match record.cache with
                | .suspended => some { state with
                    graph := ⟨environment, body ++ [.unfreeze], [], heap⟩
                    store := state.store.setKnownCache (cellId address) record (.evaluating state.nextOwner)
                    updates := ⟨cellId address, record.origin, state.nextOwner, code, stack⟩ :: state.updates
                    nextOwner := state.nextOwner + 1 }
                | .value value => some { state with graph := ⟨value, code, stack, heap⟩ }
                | .evaluating _ => none
                | .stableFault impossible => nomatch impossible
              else none
      | _ => some { state with graph := ⟨.ref address, code, stack, heap⟩ }
  | ⟨word, .unfreeze :: code, stack, heap⟩ =>
      some { state with graph := ⟨word, code, stack, heap⟩ }
  | graph => (Graph.step graph).map fun next => { state with graph := next }

/-- Independent rules for the memoizing realization. Ordinary instructions
reuse the independently stated graph transition table. -/
inductive Transition : State → State → Prop where
  | ordinary {state : State} {next : Graph.State}
      (ordinary : state.graph.code.head? ≠ some .unfreeze)
      (transition : Graph.Transition state.graph next) :
      Transition state { state with graph := next }
  | skip (word : Word) (code : Code) (stack : List Word) (heap : Graph.Heap)
      (store : Store) (updates : List Update) (nextOwner : Nat)
      (notLaze : ¬ LazeAt heap word) :
      Transition ⟨⟨word, .unfreeze :: code, stack, heap⟩, store, updates, nextOwner⟩
        ⟨⟨word, code, stack, heap⟩, store, updates, nextOwner⟩
  | allocate {address : Nat} {body : Code} {environment : Word}
      (code : Code) (stack : List Word) (heap : Graph.Heap) (store next : Store)
      (updates : List Update) (nextOwner : Nat)
      (cell : heap[address]? = some (.laze body environment))
      (fresh : store.lookup (cellId address) = none)
      (allocated : store.allocate? (cellId address) (body, environment) = some next) :
      Transition ⟨⟨.ref address, .unfreeze :: code, stack, heap⟩, store, updates, nextOwner⟩
        ⟨⟨.ref address, .unfreeze :: code, stack, heap⟩, next, updates, nextOwner⟩
  | begin {address : Nat} {body : Code} {environment : Word}
      (code : Code) (stack : List Word) (heap : Graph.Heap) (store : Store)
      (updates : List Update) (owner : Nat)
      (cell : heap[address]? = some (.laze body environment))
      (suspended : store.lookup (cellId address) = some ⟨(body, environment), .suspended⟩) :
      Transition ⟨⟨.ref address, .unfreeze :: code, stack, heap⟩, store, updates, owner⟩
        ⟨⟨environment, body ++ [.unfreeze], [], heap⟩,
          store.setKnownCache (cellId address) ⟨(body, environment), .suspended⟩ (.evaluating owner),
          ⟨cellId address, (body, environment), owner, code, stack⟩ :: updates, owner + 1⟩
  | cached {address : Nat} {body : Code} {environment value : Word}
      (code : Code) (stack : List Word) (heap : Graph.Heap) (store : Store)
      (updates : List Update) (nextOwner : Nat)
      (cell : heap[address]? = some (.laze body environment))
      (cached : store.lookup (cellId address) = some ⟨(body, environment), .value value⟩) :
      Transition ⟨⟨.ref address, .unfreeze :: code, stack, heap⟩, store, updates, nextOwner⟩
        ⟨⟨value, code, stack, heap⟩, store, updates, nextOwner⟩
  | update (word : Word) (heap : Graph.Heap) (store : Store) (frame : Update)
      (rest : List Update) (nextOwner : Nat)
      (owned : store.lookup frame.cell = some ⟨frame.origin, .evaluating frame.owner⟩)
      (forced : ¬ LazeAt heap word) :
      Transition ⟨⟨word, [], [], heap⟩, store, frame :: rest, nextOwner⟩
        ⟨⟨word, frame.code, frame.stack, heap⟩,
          store.setKnownCache frame.cell ⟨frame.origin, .evaluating frame.owner⟩ (.value word), rest, nextOwner⟩

private theorem ordinary_step {state : State} {next : Graph.State}
    (ordinary : state.graph.code.head? ≠ some .unfreeze)
    (transition : Graph.Transition state.graph next) :
    step state = some { state with graph := next } := by
  rcases state with ⟨⟨word, code, stack, heap⟩, store, updates, owner⟩
  cases transition <;> simp_all [step, Graph.step, List.head?]

theorem step_complete {before after : State} (transition : Transition before after) :
    step before = some after := by
  cases transition with
  | ordinary ordinary transition => exact ordinary_step ordinary transition
  | skip word code stack heap store updates owner notLaze =>
      cases word with
      | unit | literal _ => rfl
      | ref address =>
          cases cell : heap[address]? with
          | none => simp [step, cell]
          | some found =>
              cases found with
              | pair _ _ | closure _ _ => simp [step, cell]
              | laze body environment => exact False.elim (notLaze ⟨_, _, _, rfl, cell⟩)
  | allocate _ _ _ _ _ _ _ cell fresh allocated => simp [step, cell, fresh, allocated]
  | begin _ _ _ _ _ _ cell suspended => simp [step, cell, suspended]
  | cached _ _ _ _ _ _ cell cached => simp [step, cell, cached]
  | update word heap store frame rest owner owned forced =>
      simp [step, owned, (laze?_eq_none heap word).mpr forced]

theorem step_sound {before after : State} (execution : step before = some after) :
    Transition before after := by
  rcases before with ⟨⟨word, code, stack, heap⟩, store, updates, owner⟩
  cases code with
  | nil =>
      cases stack with
      | cons saved stack => simp [step, Graph.step] at execution
      | nil =>
          cases updates with
          | nil => simp [step] at execution
          | cons frame rest =>
              cases found : store.lookup frame.cell with
              | none => simp [step, found] at execution
              | some record =>
                  simp only [step, found] at execution
                  split at execution
                  next valid =>
                    obtain ⟨origin, cache, forced⟩ := valid
                    have same : record = ⟨frame.origin, .evaluating frame.owner⟩ := by
                      cases record
                      simp_all only
                    subst record
                    cases execution
                    exact .update _ _ _ _ _ _ found ((laze?_eq_none _ _).mp forced)
                  next invalid => simp at execution
  | cons instruction code =>
      cases instruction with
      | unfreeze =>
          cases word with
          | unit =>
              cases execution
              exact .skip _ _ _ _ _ _ _ (by simp [LazeAt])
          | literal value =>
              cases execution
              exact .skip _ _ _ _ _ _ _ (by simp [LazeAt])
          | ref address =>
              cases cell : heap[address]? with
              | none =>
                  simp only [step, cell, Option.some.injEq] at execution
                  subst after
                  exact .skip _ _ _ _ _ _ _ ((laze?_eq_none _ _).mp (by simp [laze?, cell]))
              | some cellValue =>
                  cases cellValue with
                  | pair left right | closure body environment =>
                      simp only [step, cell, Option.some.injEq] at execution
                      subst after
                      exact .skip _ _ _ _ _ _ _ ((laze?_eq_none _ _).mp (by simp [laze?, cell]))
                  | laze body environment =>
                      cases found : store.lookup (cellId address) with
                      | none =>
                          have mapped : (store.allocate? (cellId address) (body, environment)).map
                              (fun next => State.mk ⟨.ref address, .unfreeze :: code, stack, heap⟩ next updates owner) =
                              some after := by simpa only [step, cell, found] using execution
                          obtain ⟨next, allocated, rfl⟩ := Option.map_eq_some_iff.mp mapped
                          exact .allocate _ _ _ _ _ _ _ cell found allocated
                      | some record =>
                          simp only [step, cell, found] at execution
                          split at execution
                          next sameOrigin =>
                            rcases record with ⟨origin, cache⟩
                            change origin = (body, environment) at sameOrigin
                            subst origin
                            cases cache with
                            | suspended =>
                                cases execution
                                exact .begin _ _ _ _ _ _ cell found
                            | evaluating n => simp at execution
                            | value value =>
                                cases execution
                                exact .cached _ _ _ _ _ _ cell found
                            | stableFault impossible => cases impossible
                          next otherOrigin => simp at execution
      | cur body => cases execution; exact .ordinary (by simp) (.cur _ _ _ _ _)
      | freeze body => cases execution; exact .ordinary (by simp) (.freeze _ _ _ _ _)
      | push => cases execution; exact .ordinary (by simp) (.push _ _ _ _)
      | quote value => cases execution; exact .ordinary (by simp) (.quote _ _ _ _ _)
      | first | second | swap | cons | app | branch whenTrue whenFalse | operation primitive | wind =>
          obtain ⟨next, moved, rfl⟩ := Option.map_eq_some_iff.mp execution
          exact .ordinary (by simp) (Graph.step_sound moved)

theorem step_iff (before after : State) : step before = some after ↔ Transition before after :=
  ⟨step_sound, step_complete⟩


def answer (state : State) : Option Graph.Answer :=
  match state.graph, state.updates with
  | ⟨word, [], [], heap⟩, [] => some ⟨word, heap⟩
  | _, _ => none

abbrev Steps := Relation.ReflTransGen Transition

/-- One actual transition changes each shared Need cell by at most one
permitted lifecycle edge. Allocation never overwrites an existing cell. -/
theorem Transition.cell_lifecycle {before after : State} (transition : Transition before after)
    (queried : CellId) : HeapCellStep (before.store.lookup queried) (after.store.lookup queried) := by
  cases transition with
  | ordinary | skip | cached => exact .untouched _
  | @allocate address body environment code stack heap store next updates owner cell fresh allocated =>
      by_cases same : queried = cellId address
      · subst queried
        rw [fresh, Heap.allocate?_lookup_same allocated]
        exact .allocate _
      · rw [Heap.allocate?_preserves_other allocated same]
        exact .untouched _
  | @begin address body environment code stack heap store updates owner cell suspended =>
      by_cases same : queried = cellId address
      · subst queried
        rw [suspended, Heap.setKnownCache_lookup_same]
        exact .beginEval _ _
      · rw [Heap.setKnownCache_preserves_other _ _ _ same]
        exact .untouched _
  | update word heap store frame rest owner owned forced =>
      by_cases same : queried = frame.cell
      · subst queried
        rw [owned, Heap.setKnownCache_lookup_same]
        exact .commit _ _ _
      · rw [Heap.setKnownCache_preserves_other _ _ _ same]
        exact .untouched _

theorem Steps.preserves_completed {before after : State} (run : Steps before after)
    {cell : CellId} {record : Record} (cached : before.store.lookup cell = some record)
    (completed : Cache.Completed record.cache) : after.store.lookup cell = some record := by
  induction run with
  | refl => exact cached
  | tail _ transition ih => exact (transition.cell_lifecycle cell).completed_untouched ih completed

/-- A completed producer cannot be started again later in the same retained
execution. This statement counts cell identity, not equality of its result. -/
theorem Steps.no_second_production {before after : State} (run : Steps before after)
    {cell : CellId} {origin : Origin} {value : Word}
    (cached : before.store.lookup cell = some ⟨origin, .value value⟩) :
    after.store.lookup cell ≠ some ⟨origin, .suspended⟩ ∧
      ∀ owner, after.store.lookup cell ≠ some ⟨origin, .evaluating owner⟩ := by
  have kept := run.preserves_completed cached (.value value)
  simp [kept]

/-- Completion retains the cache and allocation/ownership counters as well as
the returned graph. It cannot discard an outstanding producer update. -/
def completed (state : State) : Option State :=
  match state.graph.code, state.graph.stack, state.updates with
  | [], [], [] => some state
  | _, _, _ => none

theorem completed_final (state final : State) (observed : completed state = some final) :
    step state = none := by
  rcases state with ⟨⟨word, code, stack, heap⟩, store, updates, owner⟩
  cases code <;> cases stack <;> cases updates <;> simp_all [completed, step]

def core : MachineCore Term where
  State := State
  load := load
  step := step

def answerCore : AnswerMachineCore Term State where
  toMachineCore := core
  answer := completed
  answer_final := completed_final

abbrev Occurrence := ProductiveCoreAdapters.Occurrence State

def machine : Machine State Occurrence State Empty :=
  ProductiveCoreAdapters.answerMachine answerCore

theorem core_steps_iff (before after : State) : core.Steps before after ↔ Steps before after := by
  constructor
  · exact Relation.ReflTransGen.mono (fun left right edge => (step_iff left right).mp edge) before after
  · exact Relation.ReflTransGen.mono (fun left right edge => (step_iff left right).mpr edge) before after

/-- The general retained runner resumes the actual update stack and persistent
cache. Pausing cannot reset either producer ownership or completed work. -/
theorem trace_resume {state residual : State} {events : List Occurrence}
    (trace : ProductiveCoreAdapters.Trace core state events residual) (second : Nat) :
    machine.run (events.length + second) state =
      (events ++ (machine.run second residual).1, (machine.run second residual).2) :=
  ProductiveCoreAdapters.trace_answer_resume answerCore trace second

/-- A cached delivery takes one instruction, allocates no graph node, does not
change the cache, and retains all caller and outer-producer continuations. -/
theorem force_cached {address : Nat} {body : Code} {environment value : Word}
    (code : Code) (stack : List Word) (heap : Graph.Heap) (store : Store)
    (updates : List Update) (nextOwner : Nat)
    (cell : heap[address]? = some (.laze body environment))
    (cached : store.lookup (cellId address) = some ⟨(body, environment), .value value⟩) :
    step ⟨⟨.ref address, .unfreeze :: code, stack, heap⟩, store, updates, nextOwner⟩ =
      some ⟨⟨value, code, stack, heap⟩, store, updates, nextOwner⟩ :=
  step_complete (.cached code stack heap store updates nextOwner cell cached)

/-- A producer's return publishes its forced value under the same origin and
cell identity, and removes exactly its own update frame. -/
theorem update_publishes (word : Word) (heap : Graph.Heap) (store : Store)
    (frame : Update) (rest : List Update) (nextOwner : Nat)
    (owned : store.lookup frame.cell = some ⟨frame.origin, .evaluating frame.owner⟩)
    (forced : ¬ LazeAt heap word) :
    ∃ next, step ⟨⟨word, [], [], heap⟩, store, frame :: rest, nextOwner⟩ = some next ∧
      next.graph = ⟨word, frame.code, frame.stack, heap⟩ ∧ next.updates = rest ∧
      next.store.lookup frame.cell = some ⟨frame.origin, .value word⟩ := by
  refine ⟨_, step_complete (.update word heap store frame rest nextOwner owned forced), rfl, rfl, ?_⟩
  exact Heap.setKnownCache_lookup_same _ _ _ _

/-- Attempting to force an active producer is retained as a blocked state;
it cannot be mistaken for a completed answer or a completed cache. -/
theorem force_busy {address : Nat} {body : Code} {environment : Word}
    (code : Code) (stack : List Word) (heap : Graph.Heap) (store : Store)
    (updates : List Update) (nextOwner owner : Nat)
    (cell : heap[address]? = some (.laze body environment))
    (busy : store.lookup (cellId address) = some ⟨(body, environment), .evaluating owner⟩) :
    step ⟨⟨.ref address, .unfreeze :: code, stack, heap⟩, store, updates, nextOwner⟩ = none ∧
      completed ⟨⟨.ref address, .unfreeze :: code, stack, heap⟩, store, updates, nextOwner⟩ = none := by
  simp [step, cell, busy, completed]


/-- Erase update delimiters by restoring their saved code and stack suffixes.
Allocation and committing an update become stuttering; entering a producer
becomes the historical `unfreeze` transition. Cache reuse is the remaining
semantic shortcut and is deliberately not erased by an equality claim. -/
def flattenUpdates : Graph.State → List Update → Graph.State
  | state, [] => state
  | state, frame :: rest => flattenUpdates (Graph.extend state frame.code frame.stack) rest

def flatten (state : State) : Graph.State := flattenUpdates state.graph state.updates

theorem transition_flattenUpdates {before after : Graph.State}
    (transition : Graph.Transition before after) (updates : List Update) :
    Graph.Transition (flattenUpdates before updates) (flattenUpdates after updates) := by
  induction updates generalizing before after with
  | nil => exact transition
  | cons frame rest ih => exact ih (transition.extend frame.code frame.stack)

/-- Actual reuse is determined by a matching heap origin and a completed cache
record, rather than by equality of returned values. -/
def Reuses (state : State) : Prop :=
  ∃ address body environment value,
    state.graph.register = .ref address ∧ state.graph.code.head? = some .unfreeze ∧
      state.graph.heap[address]? = some (.laze body environment) ∧
      state.store.lookup (cellId address) = some ⟨(body, environment), .value value⟩

theorem Transition.flatten_without_reuse {before after : State}
    (transition : Transition before after) (notReused : ¬ Reuses before) :
    flatten before = flatten after ∨ Graph.Transition (flatten before) (flatten after) := by
  cases transition with
  | ordinary _ moved => exact .inr (transition_flattenUpdates moved _)
  | skip word code stack heap store updates owner notLaze =>
      exact .inr (transition_flattenUpdates (.skip word code stack heap notLaze) updates)
  | allocate => exact .inl rfl
  | @begin address body environment code stack heap store updates owner cell suspended =>
      apply Or.inr
      change Graph.Transition
        (flattenUpdates ⟨.ref address, .unfreeze :: code, stack, heap⟩ updates)
        (flattenUpdates (Graph.extend ⟨environment, body ++ [.unfreeze], [], heap⟩ code stack) updates)
      have move := transition_flattenUpdates (Graph.Transition.force code stack heap cell) updates
      simpa only [Graph.extend, List.append_assoc, List.cons_append, List.nil_append] using move
  | cached _ _ _ _ _ _ cell cached =>
      exact False.elim (notReused ⟨_, _, _, _, rfl, rfl, cell, cached⟩)
  | update => exact .inl rfl

private theorem trace_map_with_event_condition {Program Target : Type}
    (driver : MachineCore Program) (view : driver.State → Target)
    (relation : Target → Target → Prop) (condition : driver.State → Prop)
    (one : ∀ left right, driver.StepRel left right → condition left →
      view left = view right ∨ relation (view left) (view right))
    {before after : driver.State} {events : List (ProductiveCoreAdapters.Occurrence driver.State)}
    (trace : ProductiveCoreAdapters.Trace driver before events after)
    (conditionHolds : ∀ event ∈ events, condition event.1) :
    Relation.ReflTransGen relation (view before) (view after) := by
  induction trace with
  | empty => exact .refl
  | @cons state next final events moved following ih =>
      have tail := ih (fun event member => conditionHolds event (by simp [member]))
      rcases one state next moved (conditionHolds (state, next) (by simp)) with same | move
      · exact same ▸ tail
      · exact .head move tail

theorem trace_flatten_without_reuse {before after : State} {events : List Occurrence}
    (trace : ProductiveCoreAdapters.Trace core before events after)
    (notReused : ∀ event ∈ events, ¬ Reuses event.1) :
    Graph.Steps (flatten before) (flatten after) :=
  trace_map_with_event_condition core flatten Graph.Transition (fun state => ¬ Reuses state)
    (fun _ _ moved notReused => (step_sound moved).flatten_without_reuse notReused) trace notReused

/-- Source soundness for a completed run before any completed producer is
reused. This includes arbitrary nesting of first forces and ordinary compiled
recursion. General reuse requires a relation between the cached graph and
fresh graph allocations; it is not inferred merely from cache stability. -/
theorem first_productions_source_sound {term : Term} {final : State} {events : List Occurrence}
    (trace : ProductiveCoreAdapters.Trace core (load term) events final)
    (notReused : ∀ event ∈ events, ¬ Reuses event.1)
    (finished : completed final = some final) :
    ∃ value, Graph.Evaluation term .unit value ∧
      Graph.Represents final.graph.heap final.graph.register value := by
  rcases final with ⟨⟨word, code, stack, heap⟩, store, updates, owner⟩
  cases code with
  | cons => simp [completed] at finished
  | nil =>
      cases stack with
      | cons => simp [completed] at finished
      | nil =>
          cases updates with
          | cons => simp [completed] at finished
          | nil =>
              have run : Graph.Steps ⟨.unit, compile term, [], []⟩ ⟨word, [], [], heap⟩ :=
                trace_flatten_without_reuse trace notReused
              obtain ⟨value, evaluation, represented, _⟩ :=
                Graph.execution_complete (.unit : Graph.Represents [] .unit .unit) run
              exact ⟨value, evaluation, represented⟩

/-! ## Independent memoizing source evaluation

The source judgment evaluates source syntax against a shared value arena and
an explicit demand store. It has no instruction or transition premise.
Closure and suspension records retain the compiled representation of their
source body. The arena also retains the intermediate pairs allocated by the
CAM; these addresses are observable sharing identities, not copied trees.
-/

/-- The persistent part of a source configuration, without machine control. -/
structure World where
  heap : Graph.Heap
  store : Store
  nextOwner : Nat := 0

namespace World

def empty : World := ⟨[], .empty, 0⟩
def append (world : World) (cell : Cell) : World :=
  { world with heap := world.heap ++ [cell] }
def recursive (world : World) (environment : Word) (body : Term) : World :=
  { world with heap := windHeap world.heap environment (compile body) }
def begin (world : World) (address : Nat) (origin : Origin) : World :=
  { world with
    store := world.store.setKnownCache (cellId address) ⟨origin, .suspended⟩ (.evaluating world.nextOwner)
    nextOwner := world.nextOwner + 1 }
def commit (world : World) (address : Nat) (origin : Origin) (owner : Nat) (value : Word) : World :=
  { world with store := world.store.setKnownCache (cellId address) ⟨origin, .evaluating owner⟩ (.value value) }

def config (world : World) (word : Word) (code : Code) (stack : List Word) (updates : List Update) : State :=
  ⟨⟨word, code, stack, world.heap⟩, world.store, updates, world.nextOwner⟩

end World

mutual
/-- Source evaluation with shared addresses and memoizing demand. The premises
follow the source constructors and strict positions, independently of the
native instruction table. -/
inductive Evaluation : Term → Word → World → Word → World → Prop where
  | varZero {world : World} {address : Nat} {environment value : Word}
      (cell : world.heap[address]? = some (.pair environment value)) :
      Evaluation (.var 0) (.ref address) world value world
  | varSucc {world final : World} {address index : Nat} {environment saved value : Word}
      (cell : world.heap[address]? = some (.pair environment saved))
      (rest : Evaluation (.var index) environment world value final) :
      Evaluation (.var (index + 1)) (.ref address) world value final
  | literal (value : Literal) (environment : Word) (world : World) :
      Evaluation (.literal value) environment world (.literal value) world
  | lam (body : Term) (environment : Word) (world : World) :
      Evaluation (.lam body) environment world (.ref world.heap.length)
        (world.append (.closure (compile body) environment))
  | fix (body : Term) (environment : Word) (world : World) :
      Evaluation (.fix body) environment world (.ref (world.heap.length + 1)) (world.recursive environment body)
  | freeze (body : Term) (environment : Word) (world : World) :
      Evaluation (.freeze body) environment world (.ref world.heap.length)
        (world.append (.laze (compile body) environment))
  | pair {left right : Term} {environment leftValue rightValue : Word} {world middle final : World}
      (leftEval : Evaluation left environment world leftValue middle)
      (rightEval : Evaluation right environment middle rightValue final) :
      Evaluation (.pair left right) environment world (.ref final.heap.length)
        (final.append (.pair leftValue rightValue))
  | first {term : Term} {environment before left right : Word} {world middle final : World} {address : Nat}
      (termEval : Evaluation term environment world before middle)
      (forced : Force before middle (.ref address) final)
      (cell : final.heap[address]? = some (.pair left right)) :
      Evaluation (.first term) environment world left final
  | second {term : Term} {environment before left right : Word} {world middle final : World} {address : Nat}
      (termEval : Evaluation term environment world before middle)
      (forced : Force before middle (.ref address) final)
      (cell : final.heap[address]? = some (.pair left right)) :
      Evaluation (.second term) environment world right final
  | app {operator argument : Term} {environment function operand callee value : Word}
      {world first second third final : World}
      (operatorEval : Evaluation operator environment world function first)
      (argumentEval : Evaluation argument environment first operand second)
      (forced : Force function (second.append (.pair function operand)) callee third)
      (invocation : Invocation callee operand third value final) :
      Evaluation (.app operator argument) environment world value final
  | conditional {condition whenTrue whenFalse : Term} {environment before value : Word}
      {world first second final : World} {selected : Bool}
      (conditionEval : Evaluation condition environment world before first)
      (forced : Force before first (.literal (.boolean selected)) second)
      (selectedEval : Evaluation (if selected then whenTrue else whenFalse) environment second value final) :
      Evaluation (.conditional condition whenTrue whenFalse) environment world value final
  | primitive {operation : Primitive} {argument : Term} {environment before left right : Word}
      {world first second third fourth : World} {address : Nat} {leftValue rightValue : Int}
      (argumentEval : Evaluation argument environment world before first)
      (forced : Force before first (.ref address) second)
      (cell : second.heap[address]? = some (.pair left right))
      (leftForced : Force left second (.literal (.integer leftValue)) third)
      (rightForced : Force right third (.literal (.integer rightValue)) fourth) :
      Evaluation (.primitive operation argument) environment world
        (.literal (operation.apply leftValue rightValue))
        (fourth.append (.pair (.literal (.integer leftValue)) (.literal (.integer rightValue))))
/-- A source call allocates the argument pair and the lexical environment.
Recursive functions use the cyclic environment already created by `fix`. -/
inductive Invocation : Word → Word → World → Word → World → Prop where
  | closure {address : Nat} {body : Term} {environment argument value : Word} {world final : World}
      (cell : (world.append (.pair (.ref address) argument)).heap[address]? =
        some (.closure (compile body) environment))
      (bodyEval : Evaluation body (.ref (world.heap.length + 1))
        ((world.append (.pair (.ref address) argument)).append (.pair environment argument)) value final) :
      Invocation (.ref address) argument world value final
/-- Forcing consults the independent demand store. A completed demand is
reused; a fresh demand is allocated; its first evaluation owns an update until
its body and every returned suspension have finished. An active demand has
no successful rule. -/
inductive Force : Word → World → Word → World → Prop where
  | value (word : Word) (world : World) (notLaze : ¬ LazeAt world.heap word) :
      Force word world word world
  | cached {address : Nat} {body : Code} {environment value : Word} {world : World}
      (cell : world.heap[address]? = some (.laze body environment))
      (cached : world.store.lookup (cellId address) = some ⟨(body, environment), .value value⟩) :
      Force (.ref address) world value world
  | allocate {address : Nat} {body : Code} {environment value : Word} {world final : World} {next : Store}
      (cell : world.heap[address]? = some (.laze body environment))
      (fresh : world.store.lookup (cellId address) = none)
      (allocated : world.store.allocate? (cellId address) (body, environment) = some next)
      (again : Force (.ref address) { world with store := next } value final) :
      Force (.ref address) world value final
  | evaluate {address : Nat} {body : Term} {environment before value : Word}
      {world first second : World}
      (cell : world.heap[address]? = some (.laze (compile body) environment))
      (suspended : world.store.lookup (cellId address) = some ⟨(compile body, environment), .suspended⟩)
      (bodyEval : Evaluation body environment (world.begin address (compile body, environment)) before first)
      (again : Force before first value second)
      (owned : second.store.lookup (cellId address) =
        some ⟨(compile body, environment), .evaluating world.nextOwner⟩)
      (forced : ¬ LazeAt second.heap value) :
      Force (.ref address) world value
        (second.commit address (compile body, environment) world.nextOwner value)
end

mutual
theorem Evaluation.heap_prefix : {term : Term} → {environment value : Word} → {world final : World} →
    Evaluation term environment world value final → world.heap <+: final.heap
  | _, _, _, _, _, .varZero _ => List.prefix_refl _
  | _, _, _, _, _, .varSucc _ rest => Evaluation.heap_prefix rest
  | _, _, _, _, _, .literal _ _ _ => List.prefix_refl _
  | _, _, _, _, _, .lam _ _ _ => List.prefix_append _ _
  | _, _, _, _, _, .fix _ _ _ => windHeap_prefix _ _ _
  | _, _, _, _, _, .freeze _ _ _ => List.prefix_append _ _
  | _, _, _, _, _, .pair left right =>
      (Evaluation.heap_prefix left).trans ((Evaluation.heap_prefix right).trans (List.prefix_append _ _))
  | _, _, _, _, _, .first term forced _ => (Evaluation.heap_prefix term).trans (Force.heap_prefix forced)
  | _, _, _, _, _, .second term forced _ => (Evaluation.heap_prefix term).trans (Force.heap_prefix forced)
  | _, _, _, _, _, .app operator argument forced invocation =>
      (Evaluation.heap_prefix operator).trans ((Evaluation.heap_prefix argument).trans
        ((List.prefix_append _ _).trans ((Force.heap_prefix forced).trans (Invocation.heap_prefix invocation))))
  | _, _, _, _, _, .conditional condition forced selected =>
      (Evaluation.heap_prefix condition).trans ((Force.heap_prefix forced).trans (Evaluation.heap_prefix selected))
  | _, _, _, _, _, .primitive argument forced _ left right =>
      (Evaluation.heap_prefix argument).trans ((Force.heap_prefix forced).trans
        ((Force.heap_prefix left).trans ((Force.heap_prefix right).trans (List.prefix_append _ _))))
theorem Invocation.heap_prefix : {function argument value : Word} → {world final : World} →
    Invocation function argument world value final → world.heap <+: final.heap
  | _, _, _, _, _, .closure _ body =>
      (List.prefix_append _ _).trans ((List.prefix_append _ _).trans (Evaluation.heap_prefix body))
theorem Force.heap_prefix : {word value : Word} → {world final : World} →
    Force word world value final → world.heap <+: final.heap
  | _, _, _, _, .value _ _ _ => List.prefix_refl _
  | _, _, _, _, .cached _ _ => List.prefix_refl _
  | _, _, world, final, .allocate (next := next) _ _ _ again =>
      Force.heap_prefix (world := { world with store := next }) (final := final) again
  | _, _, _, _, .evaluate _ _ body again _ _ => by
      simpa only [World.begin, World.commit] using
        (Evaluation.heap_prefix body).trans (Force.heap_prefix again)
end

/-- A graph cell contains source code exactly when every stored body is an
actual compilation. Pairs impose no additional code restriction. -/
def SourceCell : Cell → Prop
  | .pair _ _ => True
  | .closure body _ | .laze body _ => ∃ term, body = compile term

def SourceHeap (heap : Graph.Heap) : Prop := ∀ cell ∈ heap, SourceCell cell

theorem SourceHeap.empty : SourceHeap [] := by simp [SourceHeap]

theorem SourceHeap.append {heap : Graph.Heap} (admitted : SourceHeap heap)
    {cell : Cell} (source : SourceCell cell) : SourceHeap (heap ++ [cell]) := by
  intro item member
  rcases List.mem_append.mp member with old | fresh
  · exact admitted item old
  · simpa using List.mem_singleton.mp fresh ▸ source

theorem SourceHeap.lookup {heap : Graph.Heap} (admitted : SourceHeap heap)
    {address : Nat} {cell : Cell} (found : heap[address]? = some cell) : SourceCell cell :=
  admitted cell (List.mem_of_getElem? found)

theorem SourceHeap.recursive {world : World} (admitted : SourceHeap world.heap)
    (environment : Word) (body : Term) : SourceHeap (world.recursive environment body).heap := by
  change SourceHeap (world.heap ++ [.pair environment (.ref (world.heap.length + 1)),
    .closure (compile body) (.ref world.heap.length)])
  simpa only [List.append_assoc, List.singleton_append] using
    (admitted.append (cell := .pair environment (.ref (world.heap.length + 1))) trivial).append
      (cell := .closure (compile body) (.ref world.heap.length)) ⟨body, rfl⟩

mutual
theorem Evaluation.source_heap : {term : Term} → {environment value : Word} → {world final : World} →
    Evaluation term environment world value final → SourceHeap world.heap → SourceHeap final.heap
  | _, _, _, _, _, .varZero _, source => source
  | _, _, _, _, _, .varSucc _ rest, source => Evaluation.source_heap rest source
  | _, _, _, _, _, .literal _ _ _, source => source
  | _, _, _, _, _, .lam body _ _, source => source.append ⟨body, rfl⟩
  | _, _, _, _, _, .fix body environment _, source => source.recursive environment body
  | _, _, _, _, _, .freeze body _ _, source => source.append ⟨body, rfl⟩
  | _, _, _, _, _, .pair left right, source =>
      (Evaluation.source_heap right (Evaluation.source_heap left source)).append trivial
  | _, _, _, _, _, .first term forced _, source => Force.source_heap forced (Evaluation.source_heap term source)
  | _, _, _, _, _, .second term forced _, source => Force.source_heap forced (Evaluation.source_heap term source)
  | _, _, _, _, _, .app operator argument forced invocation, source =>
      Invocation.source_heap invocation (Force.source_heap forced
        ((Evaluation.source_heap argument (Evaluation.source_heap operator source)).append trivial))
  | _, _, _, _, _, .conditional condition forced selected, source =>
      Evaluation.source_heap selected (Force.source_heap forced (Evaluation.source_heap condition source))
  | _, _, _, _, _, .primitive argument forced _ left right, source =>
      (Force.source_heap right (Force.source_heap left
        (Force.source_heap forced (Evaluation.source_heap argument source)))).append trivial
theorem Invocation.source_heap : {function argument value : Word} → {world final : World} →
    Invocation function argument world value final → SourceHeap world.heap → SourceHeap final.heap
  | _, _, _, _, _, .closure _ body, source =>
      Evaluation.source_heap body ((source.append (cell := .pair _ _) trivial).append (cell := .pair _ _) trivial)
theorem Force.source_heap : {word value : Word} → {world final : World} →
    Force word world value final → SourceHeap world.heap → SourceHeap final.heap
  | _, _, _, _, .value _ _ _, source => source
  | _, _, _, _, .cached _ _, source => source
  | _, _, _, _, .allocate _ _ _ again, source => Force.source_heap again source
  | _, _, _, _, .evaluate (first := first) (second := second) _ _ body again _ _, source =>
      Force.source_heap (world := first) (final := second) again (Evaluation.source_heap body source)
end

private theorem ordinary {world : World} {word : Word} {instruction : Instruction}
    {code nextCode : Code} {stack nextStack : List Word} {result : Word} {heap : Graph.Heap}
    (updates : List Update) (notForce : instruction ≠ .unfreeze)
    (move : Graph.Transition ⟨word, instruction :: code, stack, world.heap⟩
      ⟨result, nextCode, nextStack, heap⟩) :
    Transition (world.config word (instruction :: code) stack updates)
      ({ world with heap := heap }.config result nextCode nextStack updates) :=
  .ordinary (by simpa [World.config] using notForce) move

mutual
/-- Source evaluation runs in every caller code, data stack and producer-update
context, returning the same retained demand store and world. -/
theorem Evaluation.execution : {term : Term} → {environment value : Word} → {world final : World} →
    Evaluation term environment world value final → (code : Code) → (stack : List Word) →
    (updates : List Update) →
    Steps (world.config environment (compile term ++ code) stack updates)
      (final.config value code stack updates)
  | _, _, _, _, _, .varZero cell, code, stack, updates =>
      .single (ordinary updates (by simp) (.second code stack _ cell))
  | _, _, _, _, _, .varSucc cell rest, code, stack, updates => by
      rw [compile_var_succ, List.cons_append]
      exact .head (ordinary updates (by simp) (.first _ _ _ cell)) (Evaluation.execution rest code stack updates)
  | _, _, _, _, _, .literal value environment world, code, stack, updates =>
      .single (ordinary updates (by simp) (.quote environment value code stack world.heap))
  | _, _, _, _, _, .lam body environment world, code, stack, updates =>
      .single (ordinary updates (by simp) (.cur environment (compile body) code stack world.heap))
  | _, _, _, _, _, .freeze body environment world, code, stack, updates =>
      .single (ordinary updates (by simp) (.freeze environment (compile body) code stack world.heap))
  | _, _, _, _, _, .fix body environment world, code, stack, updates => by
      have wound := ordinary (world := { world with heap := world.heap ++
        [.pair environment (.literal .unit)] ++ [.closure (compile body) (.ref world.heap.length)] })
        updates (by simp) (Graph.Transition.wind (address := world.heap.length)
          (left := environment) (right := .literal .unit)
          (.ref (world.heap ++ [Cell.pair environment (.literal .unit)]).length) code stack _ (by simp))
      let finalHeap := (world.heap ++ [Cell.pair environment (.literal .unit)] ++
        [Cell.closure (compile body) (.ref world.heap.length)]).set world.heap.length
          (.pair environment (.ref (world.heap ++ [Cell.pair environment (.literal .unit)]).length))
      have run : Steps (world.config environment (compile (.fix body) ++ code) stack updates)
          (({ world with heap := finalHeap } : World).config
            (.ref (world.heap ++ [Cell.pair environment (.literal .unit)]).length) code stack updates) :=
        .head (ordinary updates (by simp) (.push _ _ _ _))
          (.head (ordinary updates (by simp) (.quote _ _ _ _ _))
          (.head (ordinary updates (by simp) (.cons _ _ _ _ _))
          (.head (ordinary updates (by simp) (.push _ _ _ _))
          (.head (ordinary updates (by simp) (.cur _ _ _ _ _)) (.single wound)))))
      simpa only [finalHeap, windHeap_eq, List.length_append, List.length_singleton, World.recursive] using run
  | _, _, _, _, _, .pair (left := left) (right := right) leftEval rightEval, code, stack, updates => by
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append]
      exact .head (ordinary updates (by simp) (.push _ _ _ _))
        ((Evaluation.execution leftEval (.swap :: compile right ++ .cons :: code) (_ :: stack) updates).trans
          (.head (ordinary updates (by simp) (.swap _ _ _ _ _))
            ((Evaluation.execution rightEval (.cons :: code) (_ :: stack) updates).trans
              (.single (ordinary updates (by simp) (.cons _ _ _ _ _))))))
  | _, _, _, _, _, .first term forced cell, code, stack, updates => by
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append]
      exact (Evaluation.execution term (.unfreeze :: .first :: code) stack updates).trans
        ((Force.execution forced (.first :: code) stack updates).tail
          (ordinary updates (by simp) (.first _ _ _ cell)))
  | _, _, _, _, _, .second term forced cell, code, stack, updates => by
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append]
      exact (Evaluation.execution term (.unfreeze :: .second :: code) stack updates).trans
        ((Force.execution forced (.second :: code) stack updates).tail
          (ordinary updates (by simp) (.second _ _ _ cell)))
  | _, environment, _, _, _, .app (operator := operator) (argument := argument)
      operatorEval argumentEval forced invocation, code, stack, updates => by
      simp only [compile, forceOperator, List.append_assoc, List.cons_append, List.nil_append]
      have kept := lookup_prefix (Force.heap_prefix forced) (allocated (cell := .pair _ _))
      exact .head (ordinary updates (by simp) (.push _ _ _ _))
        ((Evaluation.execution operatorEval
          (.swap :: (compile argument ++ .cons :: .push :: .first :: .unfreeze :: .swap :: .second :: .cons :: .app :: code))
          (environment :: stack) updates).trans
          (.head (ordinary updates (by simp) (.swap _ _ _ _ _))
            ((Evaluation.execution argumentEval
              (.cons :: .push :: .first :: .unfreeze :: .swap :: .second :: .cons :: .app :: code)
              (_ :: stack) updates).trans
              (.head (ordinary updates (by simp) (.cons _ _ _ _ _))
              (.head (ordinary updates (by simp) (.push _ _ _ _))
              (.head (ordinary updates (by simp) (.first _ _ _ allocated))
                ((Force.execution forced (.swap :: .second :: .cons :: .app :: code) (_ :: stack) updates).trans
                  (.head (ordinary updates (by simp) (.swap _ _ _ _ _))
                  (.head (ordinary updates (by simp) (.second _ _ _ kept))
                    (Invocation.execution invocation code stack updates))))))))))
  | _, environment, _, _, _, .conditional (whenTrue := whenTrue) (whenFalse := whenFalse)
      (selected := selected) (second := second) condition forced selectedEval, code, stack, updates => by
      simp only [compile, List.append_assoc, List.cons_append, List.nil_append]
      have selectedRun := Evaluation.execution selectedEval code stack updates
      have conditionRun := Evaluation.execution condition
        (.unfreeze :: .branch (compile whenTrue) (compile whenFalse) :: code) (environment :: stack) updates
      have forceRun := Force.execution forced
        (.branch (compile whenTrue) (compile whenFalse) :: code) (environment :: stack) updates
      have branch := ordinary (world := second) updates (by simp)
        (Graph.Transition.branch selected environment (compile whenTrue) (compile whenFalse) code stack _)
      cases selected <;>
        exact .head (ordinary updates (by simp) (.push _ _ _ _))
          (conditionRun.trans (forceRun.trans (.head branch selectedRun)))
  | _, _, _, _, _, .primitive (operation := operation) argument forced cell left right, code, stack, updates => by
      simp only [compile, forceOperands, List.append_assoc, List.cons_append, List.nil_append]
      exact (Evaluation.execution argument
        (.unfreeze :: .push :: .first :: .unfreeze :: .swap :: .second :: .unfreeze :: .cons :: .operation operation :: code)
        stack updates).trans
        ((Force.execution forced
          (.push :: .first :: .unfreeze :: .swap :: .second :: .unfreeze :: .cons :: .operation operation :: code)
          stack updates).trans
          (.head (ordinary updates (by simp) (.push _ _ _ _))
          (.head (ordinary updates (by simp) (.first _ _ _ cell))
            ((Force.execution left (.swap :: .second :: .unfreeze :: .cons :: .operation operation :: code)
              (_ :: stack) updates).trans
              (.head (ordinary updates (by simp) (.swap _ _ _ _ _))
              (.head (ordinary updates (by simp) (.second _ _ _ (lookup_prefix (Force.heap_prefix left) cell)))
                ((Force.execution right (.cons :: .operation operation :: code) (_ :: stack) updates).trans
                  (.head (ordinary updates (by simp) (.cons _ _ _ _ _))
                    (.single (ordinary updates (by simp) (.operation _ _ _ _ allocated)))))))))))
/-- Invocation begins with the explicit argument-pair construction, then enters
its independently stored source body. -/
theorem Invocation.execution : {function argument value : Word} → {world final : World} →
    Invocation function argument world value final → (code : Code) → (stack : List Word) →
    (updates : List Update) →
    Steps (world.config argument (.cons :: .app :: code) (function :: stack) updates)
      (final.config value code stack updates)
  | _, argument, value, world, final, .closure (address := address) (body := source) (environment := environment)
      cell body, code, stack, updates => by
      have bodyRun : Steps
          (((world.append (.pair (.ref address) argument)).append (.pair environment argument)).config
            (.ref (world.append (.pair (.ref address) argument)).heap.length) (compile source ++ code) stack updates)
          (final.config value code stack updates) := by
        simpa only [World.append, List.length_append, List.length_singleton] using
          Evaluation.execution body code stack updates
      exact .head (ordinary updates (by simp) (.cons _ _ _ _ _))
        (.head (ordinary updates (by simp) (.app code stack _ allocated
          cell)) bodyRun)
/-- First force creates a real update delimiter. Evaluation and nested force
return inside it before the owned result is published and the caller restored. -/
theorem Force.execution : {word value : Word} → {world final : World} →
    Force word world value final → (code : Code) → (stack : List Word) →
    (updates : List Update) →
    Steps (world.config word (.unfreeze :: code) stack updates)
      (final.config value code stack updates)
  | _, _, _, _, .value word world notLaze, code, stack, updates =>
      .single (.skip word code stack world.heap world.store updates world.nextOwner notLaze)
  | _, _, _, _, .cached cell cached, code, stack, updates =>
      .single (.cached code stack _ _ updates _ cell cached)
  | _, _, _, _, .allocate cell fresh allocated again, code, stack, updates =>
      .head (.allocate code stack _ _ _ updates _ cell fresh allocated)
        (Force.execution again code stack updates)
  | _, _, world, _, .evaluate (address := address) (body := body) (environment := environment)
      cell suspended bodyEval again owned forced, code, stack, updates => by
      let frame : Update := ⟨cellId address, (compile body, environment), world.nextOwner, code, stack⟩
      exact .head (.begin code stack world.heap world.store updates world.nextOwner cell suspended)
        ((Evaluation.execution bodyEval [.unfreeze] [] (frame :: updates)).trans
          ((Force.execution again [] [] (frame :: updates)).tail
            (.update _ _ _ frame updates _ owned forced)))
end

/-! ### Recovering source return points from completed execution -/

/-- The count is the existing deterministic core iteration, not a second
runner or an alternative fuel interpretation. -/
private def Counted (count : Nat) (before after : State) : Prop :=
  (fun current : Option State => current.bind step)^[count] (some before) = some after

private theorem counted_of_steps {before after : State} (run : Steps before after) :
    ∃ count, Counted count before after := by
  obtain ⟨events, trace⟩ := ProductiveCoreAdapters.trace_of_reachable core
    ((core_steps_iff _ _).mpr run)
  exact ⟨events.length, trace.iteration core⟩

private theorem Counted.first_transition {count : Nat} {before after : State}
    (run : Counted count before after) (finished : completed after = some after)
    (pending : completed before = none) :
    ∃ next rest, count = rest + 1 ∧ Transition before next ∧ Counted rest next after := by
  cases count with
  | zero =>
      change some before = some after at run
      cases run
      rw [pending] at finished
      cases finished
  | succ count =>
      change (fun current : Option State => current.bind step)^[count + 1] (some before) = some after at run
      rw [Function.iterate_succ_apply] at run
      simp only [Option.bind_some] at run
      cases moved : step before with
      | none =>
          rw [moved, Function.iterate_fixed (by rfl)] at run
          cases run
      | some next =>
          rw [moved] at run
          exact ⟨next, count, rfl, step_sound moved, run⟩

private theorem Counted.consume {count : Nat} {before after next : State}
    (run : Counted count before after) (finished : completed after = some after)
    (transition : Transition before next) :
    ∃ rest, count = rest + 1 ∧ Counted rest next after := by
  have pending : completed before = none := by
    cases done : completed before with
    | none => rfl
    | some value =>
        have noStep := completed_final before value done
        rw [step_complete transition] at noStep
        cases noStep
  obtain ⟨next', rest, length, moved, following⟩ := run.first_transition finished pending
  have same : next' = next := Option.some.inj ((step_complete moved).symm.trans (step_complete transition))
  subst next'
  exact ⟨rest, length, following⟩

private theorem Counted.completed_eq {count : Nat} {before after : State}
    (run : Counted count before after) (finished : completed before = some before) : after = before := by
  have noStep := completed_final before before finished
  have fixed : (some before).bind step = none := by simp [noStep]
  cases count with
  | zero => exact (Option.some.inj run).symm
  | succ count =>
      change (fun current : Option State => current.bind step)^[count + 1] (some before) = some after at run
      rw [Function.iterate_succ_apply, fixed, Function.iterate_fixed (by rfl)] at run
      cases run

section ReturnInversion

variable {count : Nat} {word : Word} {code : Code} {stack : List Word} {world : World}
  {updates : List Update} {final : State}

private theorem Counted.push_inv
    (run : Counted count (world.config word (.push :: code) stack updates) final)
    (finished : completed final = some final) :
    ∃ rest, count = rest + 1 ∧ Counted rest (world.config word code (word :: stack) updates) final :=
  run.consume finished (ordinary updates (by simp) (.push _ _ _ _))

private theorem Counted.swap_inv {saved : Word}
    (run : Counted count (world.config word (.swap :: code) (saved :: stack) updates) final)
    (finished : completed final = some final) :
    ∃ rest, count = rest + 1 ∧ Counted rest (world.config saved code (word :: stack) updates) final :=
  run.consume finished (ordinary updates (by simp) (.swap _ _ _ _ _))

private theorem Counted.cons_inv {saved : Word}
    (run : Counted count (world.config word (.cons :: code) (saved :: stack) updates) final)
    (finished : completed final = some final) :
    ∃ rest, count = rest + 1 ∧ Counted rest
      ((world.append (.pair saved word)).config (.ref world.heap.length) code stack updates) final :=
  run.consume finished (ordinary updates (by simp) (.cons _ _ _ _ _))

private theorem Counted.quote_inv {value : Literal}
    (run : Counted count (world.config word (.quote value :: code) stack updates) final)
    (finished : completed final = some final) :
    ∃ rest, count = rest + 1 ∧ Counted rest (world.config (.literal value) code stack updates) final :=
  run.consume finished (ordinary updates (by simp) (.quote _ _ _ _ _))

private theorem Counted.cur_inv {body : Code}
    (run : Counted count (world.config word (.cur body :: code) stack updates) final)
    (finished : completed final = some final) :
    ∃ rest, count = rest + 1 ∧ Counted rest
      ((world.append (.closure body word)).config (.ref world.heap.length) code stack updates) final :=
  run.consume finished (ordinary updates (by simp) (.cur _ _ _ _ _))

private theorem Counted.freeze_inv {body : Code}
    (run : Counted count (world.config word (.freeze body :: code) stack updates) final)
    (finished : completed final = some final) :
    ∃ rest, count = rest + 1 ∧ Counted rest
      ((world.append (.laze body word)).config (.ref world.heap.length) code stack updates) final :=
  run.consume finished (ordinary updates (by simp) (.freeze _ _ _ _ _))

private theorem Counted.first_inv
    (run : Counted count (world.config word (.first :: code) stack updates) final)
    (finished : completed final = some final) :
    ∃ address left right rest, word = .ref address ∧ world.heap[address]? = some (.pair left right) ∧
      count = rest + 1 ∧ Counted rest (world.config left code stack updates) final := by
  obtain ⟨next, rest, length, moved, following⟩ := run.first_transition finished (by simp [World.config, completed])
  cases moved with
  | ordinary _ graph => cases graph; exact ⟨_, _, _, _, rfl, ‹_›, length, following⟩

private theorem Counted.second_inv
    (run : Counted count (world.config word (.second :: code) stack updates) final)
    (finished : completed final = some final) :
    ∃ address left right rest, word = .ref address ∧ world.heap[address]? = some (.pair left right) ∧
      count = rest + 1 ∧ Counted rest (world.config right code stack updates) final := by
  obtain ⟨next, rest, length, moved, following⟩ := run.first_transition finished (by simp [World.config, completed])
  cases moved with
  | ordinary _ graph => cases graph; exact ⟨_, _, _, _, rfl, ‹_›, length, following⟩

private theorem Counted.app_inv
    (run : Counted count (world.config word (.app :: code) stack updates) final)
    (finished : completed final = some final) :
    ∃ address closureAddress argument body environment rest,
      word = .ref address ∧ world.heap[address]? = some (.pair (.ref closureAddress) argument) ∧
      world.heap[closureAddress]? = some (.closure body environment) ∧ count = rest + 1 ∧
      Counted rest ((world.append (.pair environment argument)).config (.ref world.heap.length)
        (body ++ code) stack updates) final := by
  obtain ⟨next, rest, length, moved, following⟩ := run.first_transition finished (by simp [World.config, completed])
  cases moved with
  | ordinary _ graph => cases graph; exact ⟨_, _, _, _, _, _, rfl, ‹_›, ‹_›, length, following⟩

private theorem Counted.branch_inv {saved : Word} {whenTrue whenFalse : Code}
    (run : Counted count (world.config word (.branch whenTrue whenFalse :: code) (saved :: stack) updates) final)
    (finished : completed final = some final) :
    ∃ selected rest, word = .literal (.boolean selected) ∧ count = rest + 1 ∧
      Counted rest (world.config saved ((if selected then whenTrue else whenFalse) ++ code) stack updates) final := by
  obtain ⟨next, rest, length, moved, following⟩ := run.first_transition finished (by simp [World.config, completed])
  cases moved with
  | ordinary _ graph => cases graph; exact ⟨_, _, rfl, length, following⟩

private theorem Counted.operation_inv {operation : Primitive}
    (run : Counted count (world.config word (.operation operation :: code) stack updates) final)
    (finished : completed final = some final) :
    ∃ address left right rest,
      word = .ref address ∧ world.heap[address]? = some (.pair (.literal (.integer left)) (.literal (.integer right))) ∧
      count = rest + 1 ∧ Counted rest (world.config (.literal (operation.apply left right)) code stack updates) final := by
  obtain ⟨next, rest, length, moved, following⟩ := run.first_transition finished (by simp [World.config, completed])
  cases moved with
  | ordinary _ graph => cases graph; exact ⟨_, _, _, _, rfl, ‹_›, length, following⟩

private theorem Counted.wind_inv {address : Nat}
    (run : Counted count (world.config word (.wind :: code) (.ref address :: stack) updates) final)
    (finished : completed final = some final) :
    ∃ left right rest, world.heap[address]? = some (.pair left right) ∧ count = rest + 1 ∧
      Counted rest (({ world with heap := world.heap.set address (.pair left word) } : World).config
        word code stack updates) final := by
  obtain ⟨next, rest, length, moved, following⟩ := run.first_transition finished (by simp [World.config, completed])
  cases moved with
  | ordinary _ graph => cases graph; exact ⟨_, _, _, ‹_›, length, following⟩

private theorem Counted.update_inv {frame : Update}
    (run : Counted count (world.config word [] [] (frame :: updates)) final)
    (finished : completed final = some final) :
    ∃ rest, count = rest + 1 ∧
      world.store.lookup frame.cell = some ⟨frame.origin, .evaluating frame.owner⟩ ∧
      ¬ LazeAt world.heap word ∧
      Counted rest (({ world with store := (world.store.setKnownCache frame.cell
        ⟨frame.origin, .evaluating frame.owner⟩ (.value word)) } : World).config
          word frame.code frame.stack updates) final := by
  obtain ⟨next, rest, length, moved, following⟩ := run.first_transition finished (by simp [World.config, completed])
  cases moved with
  | ordinary _ graph => cases graph
  | update _ _ _ _ _ _ owned forced => exact ⟨_, length, owned, forced, following⟩

end ReturnInversion

private def EvaluationReturns (count : Nat) : Prop :=
  ∀ term environment world code stack updates final,
    SourceHeap world.heap →
    Counted count (world.config environment (compile term ++ code) stack updates) final →
    completed final = some final →
    ∃ value result rest, Evaluation term environment world value result ∧ rest < count ∧
      Counted rest (result.config value code stack updates) final

private def ForceReturns (count : Nat) : Prop :=
  ∀ word world code stack updates final,
    SourceHeap world.heap →
    Counted count (world.config word (.unfreeze :: code) stack updates) final →
    completed final = some final →
    ∃ value result rest, Force word world value result ∧ rest < count ∧
      Counted rest (result.config value code stack updates) final

private def InvocationReturns (count : Nat) : Prop :=
  ∀ function argument world code stack updates final,
    SourceHeap world.heap →
    Counted count (world.config argument (.cons :: .app :: code) (function :: stack) updates) final →
    completed final = some final →
    ∃ value result rest, Invocation function argument world value result ∧ rest < count ∧
      Counted rest (result.config value code stack updates) final

private theorem returns (count : Nat) :
    EvaluationReturns count ∧ ForceReturns count ∧ InvocationReturns count := by
  induction count using Nat.strong_induction_on with
  | _ count ih =>
  have forceReturns : ForceReturns count := by
    intro word world code stack updates final source run₀ finished
    obtain ⟨next, rest, length, moved, run₁⟩ :=
      run₀.first_transition finished (by simp [World.config, completed])
    cases moved with
    | ordinary ordinary graph => simp [World.config] at ordinary
    | skip word code stack heap store updates owner notLaze =>
        exact ⟨word, world, rest, .value word world notLaze, by omega, run₁⟩
    | cached code stack heap store updates owner cell cached =>
        exact ⟨_, world, rest, .cached cell cached, by omega, run₁⟩
    | allocate code stack heap store next updates owner cell fresh allocated =>
        obtain ⟨value, result, left, again, less, run₂⟩ :=
          (ih rest (by omega)).2.1 _ { world with store := next } code stack updates final source run₁ finished
        exact ⟨value, result, left, .allocate cell fresh allocated again, by omega, run₂⟩
    | @begin address body environment code stack heap store updates owner cell suspended =>
        obtain ⟨term, rfl⟩ := source.lookup cell
        let frame : Update := ⟨cellId address, (compile term, environment), world.nextOwner, code, stack⟩
        obtain ⟨before, first, left₁, evaluated, less₁, run₂⟩ :=
          (ih rest (by omega)).1 term environment (world.begin address (compile term, environment))
            [.unfreeze] [] (frame :: updates) final source run₁ finished
        obtain ⟨value, second, left₂, again, less₂, run₃⟩ :=
          (ih left₁ (by omega)).2.1 before first [] [] (frame :: updates) final
            (evaluated.source_heap source) run₂ finished
        obtain ⟨left₃, count₃, owned, forced, run₄⟩ := run₃.update_inv finished
        exact ⟨value, second.commit address (compile term, environment) world.nextOwner value,
          left₃, .evaluate cell suspended evaluated again owned forced, by omega, run₄⟩
  have invocationReturns : InvocationReturns count := by
    intro function argument world code stack updates final source run₀ finished
    obtain ⟨rest₁, count₁, run₁⟩ := run₀.cons_inv finished
    obtain ⟨address, closureAddress, argument', body, environment, rest₂,
      same, pair, closure, count₂, run₂⟩ := run₁.app_inv finished
    cases same
    simp only [World.append, allocated] at pair
    cases pair
    have admittedPair : SourceHeap (world.append (.pair (.ref closureAddress) argument)).heap :=
      source.append trivial
    obtain ⟨term, rfl⟩ := admittedPair.lookup closure
    have actualRun : Counted rest₂
        (((world.append (.pair (.ref closureAddress) argument)).append (.pair environment argument)).config
          (.ref (world.heap.length + 1)) (compile term ++ code) stack updates) final := by
      simpa only [World.append, List.length_append, List.length_singleton] using run₂
    obtain ⟨value, result, rest₃, evaluated, less₃, run₃⟩ :=
      (ih rest₂ (by omega)).1 term _ _ code stack updates final (admittedPair.append (cell := .pair environment argument) trivial) actualRun finished
    exact ⟨value, result, rest₃, .closure closure evaluated, by omega, run₃⟩
  have evaluationReturns : EvaluationReturns count := by
    intro term
    induction term with
    | var index =>
        intro environment world code stack updates final source run₀ finished
        cases index with
        | zero =>
            obtain ⟨address, left, right, rest, same, cell, count₁, run₁⟩ :=
              Counted.second_inv (code := code) run₀ finished
            subst environment
            exact ⟨right, world, rest, .varZero cell, by omega, run₁⟩
        | succ index =>
            rw [compile_var_succ, List.cons_append] at run₀
            obtain ⟨address, left, right, rest, same, cell, count₁, run₁⟩ := run₀.first_inv finished
            subst environment
            obtain ⟨value, result, left₁, evaluated, less₁, run₂⟩ :=
              (ih rest (by omega)).1 (.var index) left world code stack updates final source run₁ finished
            exact ⟨value, result, left₁, .varSucc cell evaluated, by omega, run₂⟩
    | literal value =>
        intro environment world code stack updates final source run₀ finished
        obtain ⟨rest, length, run₁⟩ := Counted.quote_inv (code := code) run₀ finished
        exact ⟨.literal value, world, rest, .literal value environment world, by omega, run₁⟩
    | lam body _ =>
        intro environment world code stack updates final source run₀ finished
        obtain ⟨rest, length, run₁⟩ := Counted.cur_inv (code := code) run₀ finished
        exact ⟨_, _, rest, .lam body environment world, by omega, run₁⟩
    | freeze body _ =>
        intro environment world code stack updates final source run₀ finished
        obtain ⟨rest, length, run₁⟩ := Counted.freeze_inv (code := code) run₀ finished
        exact ⟨_, _, rest, .freeze body environment world, by omega, run₁⟩
    | fix body _ =>
        intro environment world code stack updates final source run₀ finished
        simp only [compile, List.cons_append, List.nil_append] at run₀
        obtain ⟨rest₁, count₁, run₁⟩ := run₀.push_inv finished
        obtain ⟨rest₂, count₂, run₂⟩ := run₁.quote_inv finished
        obtain ⟨rest₃, count₃, run₃⟩ := run₂.cons_inv finished
        obtain ⟨rest₄, count₄, run₄⟩ := run₃.push_inv finished
        obtain ⟨rest₅, count₅, run₅⟩ := run₄.cur_inv finished
        obtain ⟨left, right, rest₆, cell, count₆, run₆⟩ := run₅.wind_inv finished
        have couple : (world.heap ++ [Cell.pair environment (.literal .unit)] ++
            [Cell.closure (compile body) (.ref world.heap.length)])[world.heap.length]? =
              some (.pair environment (.literal .unit)) := by simp
        change (world.heap ++ [Cell.pair environment (.literal .unit)] ++
          [Cell.closure (compile body) (.ref world.heap.length)])[world.heap.length]? = _ at cell
        rw [couple] at cell
        cases cell
        dsimp only [World.append] at run₆
        rw [windHeap_eq] at run₆
        simp only [List.length_append, List.length_singleton] at run₆
        exact ⟨_, _, rest₆, .fix body environment world, by omega, run₆⟩
    | pair left right _ _ =>
        intro environment world code stack updates final source run₀ finished
        simp only [compile, List.append_assoc, List.cons_append, List.nil_append] at run₀
        obtain ⟨rest₁, count₁, run₁⟩ := run₀.push_inv finished
        obtain ⟨leftWord, first, rest₂, leftEval, less₂, run₂⟩ :=
          (ih rest₁ (by omega)).1 left environment world _ _ updates final source run₁ finished
        obtain ⟨rest₃, count₃, run₃⟩ := run₂.swap_inv finished
        obtain ⟨rightWord, second, rest₄, rightEval, less₄, run₄⟩ :=
          (ih rest₃ (by omega)).1 right environment first _ _ updates final
            (leftEval.source_heap source) run₃ finished
        obtain ⟨rest₅, count₅, run₅⟩ := run₄.cons_inv finished
        exact ⟨_, _, rest₅, .pair leftEval rightEval, by omega, run₅⟩
    | first term termIH =>
        intro environment world code stack updates final source run₀ finished
        simp only [compile, List.append_assoc, List.cons_append, List.nil_append] at run₀
        obtain ⟨before, first, rest₁, evaluated, less₁, run₁⟩ :=
          termIH environment world _ stack updates final source run₀ finished
        obtain ⟨forced, second, rest₂, force, less₂, run₂⟩ :=
          (ih rest₁ less₁).2.1 before first _ stack updates final (evaluated.source_heap source) run₁ finished
        obtain ⟨address, left, right, rest₃, same, cell, count₃, run₃⟩ := run₂.first_inv finished
        subst forced
        exact ⟨_, _, rest₃, .first evaluated force cell, by omega, run₃⟩
    | second term termIH =>
        intro environment world code stack updates final source run₀ finished
        simp only [compile, List.append_assoc, List.cons_append, List.nil_append] at run₀
        obtain ⟨before, first, rest₁, evaluated, less₁, run₁⟩ :=
          termIH environment world _ stack updates final source run₀ finished
        obtain ⟨forced, second, rest₂, force, less₂, run₂⟩ :=
          (ih rest₁ less₁).2.1 before first _ stack updates final (evaluated.source_heap source) run₁ finished
        obtain ⟨address, left, right, rest₃, same, cell, count₃, run₃⟩ := run₂.second_inv finished
        subst forced
        exact ⟨_, _, rest₃, .second evaluated force cell, by omega, run₃⟩
    | app operator argument _ _ =>
        intro environment world code stack updates final source run₀ finished
        simp only [compile, forceOperator, List.append_assoc, List.cons_append, List.nil_append] at run₀
        obtain ⟨rest₁, count₁, run₁⟩ := run₀.push_inv finished
        obtain ⟨function, first, rest₂, operatorEval, less₂, run₂⟩ :=
          (ih rest₁ (by omega)).1 operator environment world _ _ updates final source run₁ finished
        obtain ⟨rest₃, count₃, run₃⟩ := run₂.swap_inv finished
        obtain ⟨operand, second, rest₄, argumentEval, less₄, run₄⟩ :=
          (ih rest₃ (by omega)).1 argument environment first _ _ updates final
            (operatorEval.source_heap source) run₃ finished
        obtain ⟨rest₅, count₅, run₅⟩ := run₄.cons_inv finished
        obtain ⟨rest₆, count₆, run₆⟩ := run₅.push_inv finished
        obtain ⟨address, left, right, rest₇, same, cell, count₇, run₇⟩ := run₆.first_inv finished
        cases same
        simp only [World.append, allocated] at cell
        cases cell
        obtain ⟨callee, third, rest₈, force, less₈, run₈⟩ :=
          (ih rest₇ (by omega)).2.1 function (second.append (.pair function operand)) _ _ updates final
            ((argumentEval.source_heap (operatorEval.source_heap source)).append trivial) run₇ finished
        obtain ⟨rest₉, count₉, run₉⟩ := run₈.swap_inv finished
        obtain ⟨address', left', right', rest₁₀, same', cell', count₁₀, run₁₀⟩ := run₉.second_inv finished
        cases same'
        rw [lookup_prefix (Force.heap_prefix force) allocated] at cell'
        cases cell'
        obtain ⟨value, result, rest₁₁, invocation, less₁₁, run₁₁⟩ :=
          (ih rest₁₀ (by omega)).2.2 callee operand third code stack updates final
            (force.source_heap ((argumentEval.source_heap (operatorEval.source_heap source)).append trivial))
              run₁₀ finished
        exact ⟨value, result, rest₁₁, .app operatorEval argumentEval force invocation, by omega, run₁₁⟩
    | conditional condition whenTrue whenFalse _ _ _ =>
        intro environment world code stack updates final source run₀ finished
        simp only [compile, List.append_assoc, List.cons_append, List.nil_append] at run₀
        obtain ⟨rest₁, count₁, run₁⟩ := run₀.push_inv finished
        obtain ⟨before, first, rest₂, evaluated, less₂, run₂⟩ :=
          (ih rest₁ (by omega)).1 condition environment world _ _ updates final source run₁ finished
        obtain ⟨test, second, rest₃, force, less₃, run₃⟩ :=
          (ih rest₂ (by omega)).2.1 before first _ _ updates final (evaluated.source_heap source) run₂ finished
        obtain ⟨selected, rest₄, same, count₄, run₄⟩ := run₃.branch_inv finished
        subst test
        have chosen : Counted rest₄
            (second.config environment (compile (if selected then whenTrue else whenFalse) ++ code) stack updates)
            final := by cases selected <;> exact run₄
        obtain ⟨value, result, rest₅, selectedEval, less₅, run₅⟩ :=
          (ih rest₄ (by omega)).1 _ environment second code stack updates final
            (force.source_heap (evaluated.source_heap source)) chosen finished
        exact ⟨value, result, rest₅, .conditional evaluated force selectedEval, by omega, run₅⟩
    | primitive operation argument argumentIH =>
        intro environment world code stack updates final source run₀ finished
        simp only [compile, forceOperands, List.append_assoc, List.cons_append, List.nil_append] at run₀
        obtain ⟨before, first, rest₁, evaluated, less₁, run₁⟩ :=
          argumentIH environment world _ stack updates final source run₀ finished
        obtain ⟨couple, second, rest₂, force, less₂, run₂⟩ :=
          (ih rest₁ less₁).2.1 before first _ stack updates final (evaluated.source_heap source) run₁ finished
        obtain ⟨rest₃, count₃, run₃⟩ := run₂.push_inv finished
        obtain ⟨address, left, right, rest₄, same, cell, count₄, run₄⟩ := run₃.first_inv finished
        subst couple
        obtain ⟨leftResult, third, rest₅, leftForce, less₅, run₅⟩ :=
          (ih rest₄ (by omega)).2.1 left second _ _ updates final
            (force.source_heap (evaluated.source_heap source)) run₄ finished
        obtain ⟨rest₆, count₆, run₆⟩ := run₅.swap_inv finished
        obtain ⟨address', left', right', rest₇, same', cell', count₇, run₇⟩ := run₆.second_inv finished
        cases same'
        rw [lookup_prefix (Force.heap_prefix leftForce) cell] at cell'
        cases cell'
        obtain ⟨rightResult, fourth, rest₈, rightForce, less₈, run₈⟩ :=
          (ih rest₇ (by omega)).2.1 right third _ _ updates final
            (leftForce.source_heap (force.source_heap (evaluated.source_heap source))) run₇ finished
        obtain ⟨rest₉, count₉, run₉⟩ := run₈.cons_inv finished
        obtain ⟨address'', leftValue, rightValue, rest₁₀, same'', cell'', count₁₀, run₁₀⟩ :=
          run₉.operation_inv finished
        cases same''
        simp only [World.append, allocated] at cell''
        cases cell''
        exact ⟨_, _, rest₁₀, .primitive evaluated force cell leftForce rightForce, by omega, run₁₀⟩
  exact ⟨evaluationReturns, forceReturns, invocationReturns⟩

/-- Every completed native execution from a source-admitted arena has an
independent source derivation. This includes cache hits and arbitrarily nested
update frames; the returned world retains the exact cache and owner history. -/
theorem execution_complete {term : Term} {environment : Word} {world : World} {final : State}
    (source : SourceHeap world.heap)
    (run : Steps (world.config environment (compile term) [] []) final)
    (finished : completed final = some final) :
    ∃ value result, Evaluation term environment world value result ∧
      final = result.config value [] [] [] := by
  obtain ⟨count, counted⟩ := counted_of_steps run
  obtain ⟨value, result, rest, evaluated, _, back⟩ :=
    (returns count).1 term environment world [] [] [] final source
      (by simpa only [List.append_nil] using counted) finished
  exact ⟨value, result, evaluated, back.completed_eq rfl⟩

/-- The memoizing realization and its source semantics agree on complete
values and the entire retained world. The shared arena and demand store are
part of the observation, so sharing cannot disappear in this theorem. -/
theorem evaluation_iff_execution {term : Term} {environment value : Word} {world result : World}
    (source : SourceHeap world.heap) :
    Evaluation term environment world value result ↔
      Steps (world.config environment (compile term) [] []) (result.config value [] [] []) := by
  constructor
  · intro evaluation
    simpa only [List.append_nil] using evaluation.execution [] [] []
  · intro run
    obtain ⟨value', result', evaluated, same⟩ := execution_complete source run rfl
    have equalValue : value = value' := congrArg (fun state => state.graph.register) same
    have equalHeap : result.heap = result'.heap := congrArg (fun state => state.graph.heap) same
    have equalStore : result.store = result'.store := congrArg State.store same
    have equalOwner : result.nextOwner = result'.nextOwner := congrArg State.nextOwner same
    cases result
    cases result'
    cases equalHeap
    cases equalStore
    cases equalOwner
    cases equalValue
    exact evaluated

private theorem completed_identity {state final : State} (observed : completed state = some final) :
    state = final := by
  rcases state with ⟨⟨word, code, stack, heap⟩, store, updates, owner⟩
  cases code <;> cases stack <;> cases updates <;> simp_all [completed]

/-- The executable budgeted client completes exactly on source evaluation.
The budget counts actual machine transitions and the final observation. -/
theorem evaluation_iff_finished {term : Term} {environment value : Word} {world result : World}
    (source : SourceHeap world.heap) :
    Evaluation term environment world value result ↔
      ∃ budget events, machine.run budget (world.config environment (compile term) [] []) =
        (events, .finished (result.config value [] [] [])) := by
  rw [evaluation_iff_execution source]
  constructor
  · intro run
    exact (ProductiveCoreAdapters.answer_reachable_iff_finished answerCore _ _).mp
      ⟨_, (core_steps_iff _ _).mpr run, rfl⟩
  · intro ran
    obtain ⟨final, reached, observed⟩ :=
      (ProductiveCoreAdapters.answer_reachable_iff_finished answerCore _ _).mpr ran
    have same := completed_identity observed
    subst final
    exact (core_steps_iff _ _).mp reached

/-- The public empty-world loader has no extra admission assumption. All
source constructs, recursive closures and retained memoized forces are covered. -/
theorem source_iff_run (term : Term) (value : Word) (world : World) :
    Evaluation term .unit World.empty value world ↔
      ∃ budget events, machine.run budget (load term) =
        (events, .finished (world.config value [] [] [])) :=
  evaluation_iff_finished SourceHeap.empty

/-- A finished budgeted answer has the independent source derivation of its
exact world, including the committed cache and producer counter. -/
theorem run_source_sound {term : Term} {budget : Nat} {events : List Occurrence} {final : State}
    (ran : machine.run budget (load term) = (events, .finished final)) :
    ∃ value world, Evaluation term .unit World.empty value world ∧
      final = world.config value [] [] [] := by
  obtain ⟨state, reached, observed⟩ :=
    (ProductiveCoreAdapters.answer_reachable_iff_finished answerCore _ _).mpr ⟨budget, events, ran⟩
  have same := completed_identity observed
  subst state
  exact execution_complete SourceHeap.empty ((core_steps_iff _ _).mp reached) observed

/-- Determinism follows from actual execution, including the resulting shared
world. It is not imposed as an extra source rule. -/
theorem Evaluation.unique {term : Term} {environment first second : Word}
    {world firstWorld secondWorld : World}
    (one : Evaluation term environment world first firstWorld)
    (two : Evaluation term environment world second secondWorld) :
    first = second ∧ firstWorld = secondWorld := by
  have same := core.steps_final_unique
    ((core_steps_iff _ _).mpr (one.execution [] [] []))
    ((core_steps_iff _ _).mpr (two.execution [] [] []))
    (completed_final (firstWorld.config first [] [] []) _ rfl)
    (completed_final (secondWorld.config second [] [] []) _ rfl)
  have equalValue : first = second := congrArg (fun state => state.graph.register) same
  have equalHeap : firstWorld.heap = secondWorld.heap := congrArg (fun state => state.graph.heap) same
  have equalStore : firstWorld.store = secondWorld.store := congrArg State.store same
  have equalOwner : firstWorld.nextOwner = secondWorld.nextOwner := congrArg State.nextOwner same
  refine ⟨equalValue, ?_⟩
  cases firstWorld
  cases secondWorld
  cases equalHeap
  cases equalStore
  cases equalOwner
  rfl

end Need

end Mettapedia.Machines.CategoricalAbstractMachine.Graph
