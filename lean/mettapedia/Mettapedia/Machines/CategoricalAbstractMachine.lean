import Mettapedia.CategoryTheory.RelativeClosedSyntaxClosed
import Mettapedia.Machines.ProductiveCoreAdapters
import Mathlib.Data.List.Basic
import Mettapedia.OSLF.Syntax.BindingSignature

/-!
# The historical categorical abstract machine

The core source and instruction tables follow Cousineau, Curien and Mauny,
*The Categorical Abstract Machine* (1987), pp. 186--190. Source closures
retain source bodies; executable closures retain instruction lists. The
compiler supplies their representation map. Quotation (p. 180, Table 1) and
Boolean branching (pp. 192--193, Table 6) also execute on raw configurations.
One indexed source grammar and independent evaluation judgment cover both
the historical constant-free fragment and the quotation/conditional extension.
The compiler, native closure readback and completed-execution correspondence
are shared. Non-Boolean conditions remain stuck; no termination is assumed.

The strict profile is the active instruction table of Section 2. The neutral
profile adds the inactive projection/application rules of Table 5. Completed
answers require empty code and empty stack. Arbitrary raw instructions are
not thereby certified as compiled source programs.

The instruction table also lists the primitives, `wind`, `freeze` and
`unfreeze` of Sections 4 and 5. They have no rule here; the value-graph machine
of `CategoricalAbstractMachineGraph` executes them.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.CategoricalAbstractMachine

/-- Quoted constants of the executable profile; integers are mathematical integers.
`unit` is the quotable `()` that the recursion code of Section 4 (p. 193) places
in a couple before `wind` (`nullvalue` in Section 5). It is a constant, distinct
from the empty environment `SourceValue.unit`. -/
inductive Literal where
  | boolean (value : Bool)
  | integer (value : Int)
  | unit
  deriving DecidableEq, Repr

/-- The strict primitives of Section 5 (p. 198): `plus`, `minus`, `times`, `eq`
and `leq` act on a couple of integers. -/
inductive Primitive where
  | plus
  | minus
  | times
  | equal
  | lessEqual
  deriving DecidableEq, Repr

/-- The constant a primitive returns on the couple `(left, right)` of integers. -/
def Primitive.apply : Primitive → Int → Int → Literal
  | .plus, left, right => .integer (left + right)
  | .minus, left, right => .integer (left - right)
  | .times, left, right => .integer (left * right)
  | .equal, left, right => .boolean (decide (left = right))
  | .lessEqual, left, right => .boolean (decide (left ≤ right))

/-- One source grammar, with operational extensions admitted explicitly. The
historical constant-free fragment is the specialization at `false`. -/
inductive Source (extended : Bool) where
  | var (index : Nat)
  | lam (body : Source extended)
  | app (operator argument : Source extended)
  | pair (left right : Source extended)
  | first (term : Source extended)
  | second (term : Source extended)
  | literal (enabled : extended = true) (value : Literal)
  | conditional (enabled : extended = true) (condition whenTrue whenFalse : Source extended)
  deriving DecidableEq, Repr

abbrev Expr := Source false

namespace Expr
abbrev var := Source.var (extended := false)
abbrev lam := Source.lam (extended := false)
abbrev app := Source.app (extended := false)
abbrev pair := Source.pair (extended := false)
abbrev first := Source.first (extended := false)
abbrev second := Source.second (extended := false)
end Expr

variable {extended : Bool}

/-- One instruction table for the tree-valued machine of this file and the
value-graph machine of `CategoricalAbstractMachineGraph`. The last four
instructions are Section 4/5 extensions: `operation` applies a strict
primitive to a couple of integers (p. 198), `wind` closes a recursive
environment by physically replacing the right part of a couple (Table 6),
`freeze` delays a body into a laze and `unfreeze` forces one (Table 7). The
tree-valued `Transition` below has no rule for these four; they execute on the
value graph, where `wind` updates a shared cell in place. -/
inductive Instruction where
  | first
  | second
  | cur (body : List Instruction)
  | push
  | swap
  | cons
  | app
  | quote (value : Literal)
  | branch (whenTrue whenFalse : List Instruction)
  | operation (primitive : Primitive)
  | wind
  | freeze (body : List Instruction)
  | unfreeze
  deriving Repr

/-- The constructor index of an instruction form. Equal instructions have equal
indices; it is used only to separate distinct forms in `Instruction.decEq`. -/
def Instruction.tag : Instruction → Nat
  | .first => 0
  | .second => 1
  | .cur _ => 2
  | .push => 3
  | .swap => 4
  | .cons => 5
  | .app => 6
  | .quote _ => 7
  | .branch _ _ => 8
  | .operation _ => 9
  | .wind => 10
  | .freeze _ => 11
  | .unfreeze => 12

theorem Instruction.ne_of_tag_ne {left right : Instruction} (different : left.tag ≠ right.tag) :
    left ≠ right :=
  fun same => different (congrArg Instruction.tag same)

mutual
/-- Equality of two instructions of the same form. The equal-index hypothesis
leaves only the diagonal cases; their fields are compared recursively. -/
def Instruction.decEqOfTag : (left right : Instruction) → left.tag = right.tag → Decidable (left = right)
  | .first, .first, _ | .second, .second, _ | .push, .push, _ | .swap, .swap, _
  | .cons, .cons, _ | .app, .app, _ | .wind, .wind, _ | .unfreeze, .unfreeze, _ => .isTrue rfl
  | .cur left, .cur right, _ =>
      match Instruction.codeDecEq left right with
      | .isTrue same => .isTrue (same ▸ rfl)
      | .isFalse different => .isFalse (fun same => different (Instruction.cur.inj same))
  | .freeze left, .freeze right, _ =>
      match Instruction.codeDecEq left right with
      | .isTrue same => .isTrue (same ▸ rfl)
      | .isFalse different => .isFalse (fun same => different (Instruction.freeze.inj same))
  | .quote left, .quote right, _ =>
      if same : left = right then .isTrue (same ▸ rfl)
      else .isFalse (fun equal => same (Instruction.quote.inj equal))
  | .operation left, .operation right, _ =>
      if same : left = right then .isTrue (same ▸ rfl)
      else .isFalse (fun equal => same (Instruction.operation.inj equal))
  | .branch leftTrue leftFalse, .branch rightTrue rightFalse, _ =>
      match Instruction.codeDecEq leftTrue rightTrue, Instruction.codeDecEq leftFalse rightFalse with
      | .isTrue sameTrue, .isTrue sameFalse => .isTrue (sameTrue ▸ sameFalse ▸ rfl)
      | .isFalse different, _ => .isFalse (fun same => different (Instruction.branch.inj same).1)
      | _, .isFalse different => .isFalse (fun same => different (Instruction.branch.inj same).2)
def Instruction.codeDecEq : (left right : List Instruction) → Decidable (left = right)
  | [], [] => .isTrue rfl
  | [], _ :: _ | _ :: _, [] => .isFalse (by intro same; cases same)
  | left :: lefts, right :: rights =>
      match (if tags : left.tag = right.tag then Instruction.decEqOfTag left right tags
          else .isFalse (Instruction.ne_of_tag_ne tags)), Instruction.codeDecEq lefts rights with
      | .isTrue sameHead, .isTrue sameTail => .isTrue (sameHead ▸ sameTail ▸ rfl)
      | .isFalse different, _ => .isFalse (fun same => different (List.cons.inj same).1)
      | _, .isFalse different => .isFalse (fun same => different (List.cons.inj same).2)
end

/-- Distinct forms differ by constructor index; equal forms compare their fields. -/
def Instruction.decEq (left right : Instruction) : Decidable (left = right) :=
  if tags : left.tag = right.tag then Instruction.decEqOfTag left right tags
  else .isFalse (Instruction.ne_of_tag_ne tags)

instance : DecidableEq Instruction := Instruction.decEq

abbrev Code := List Instruction

def compileSource : Source extended → Code
  | .var index => List.replicate index .first ++ [.second]
  | .lam body => [.cur (compileSource body)]
  | .app operator argument =>
      [.push] ++ compileSource operator ++ [.swap] ++ compileSource argument ++ [.cons, .app]
  | .pair left right => [.push] ++ compileSource left ++ [.swap] ++ compileSource right ++ [.cons]
  | .first term => compileSource term ++ [.first]
  | .second term => compileSource term ++ [.second]
  | .literal _ value => [.quote value]
  | .conditional _ condition whenTrue whenFalse =>
      .push :: compileSource condition ++ [.branch (compileSource whenTrue) (compileSource whenFalse)]

abbrev compile : Expr → Code := compileSource

@[simp] theorem compile_var_zero : compileSource (extended := extended) (.var 0) = [.second] := rfl

@[simp] theorem compile_var_succ (index : Nat) :
    compileSource (extended := extended) (.var (index + 1)) = .first :: compileSource (extended := extended) (.var index) := by
  simp [compileSource, List.replicate_succ]

theorem compile_nonempty (term : Source extended) : compileSource term ≠ [] := by
  cases term <;> simp [compileSource]

private inductive SymbolicValue (extended : Bool) where
  | environment (depth : Nat)
  | term (expression : Source extended)

private structure SymbolicState (extended : Bool) where
  register : SymbolicValue extended
  stack : List (SymbolicValue extended)

/-- Symbolically execute instructions to reconstruct their source expression.
The final canonical check distinguishes compiler output from extra raw work. -/
@[simp] private def decodeAux : Code → SymbolicState extended → Option (SymbolicState extended)
  | [], state => some state
  | .first :: rest, ⟨.environment depth, stack⟩ =>
      decodeAux rest ⟨.environment (depth + 1), stack⟩
  | .first :: rest, ⟨.term expression, stack⟩ =>
      decodeAux rest ⟨.term (.first expression), stack⟩
  | .second :: rest, ⟨.environment depth, stack⟩ =>
      decodeAux rest ⟨.term (.var depth), stack⟩
  | .second :: rest, ⟨.term expression, stack⟩ =>
      decodeAux rest ⟨.term (.second expression), stack⟩
  | .cur body :: rest, ⟨.environment 0, stack⟩ =>
      match decodeAux body ⟨.environment 0, []⟩ with
      | some ⟨.term expression, []⟩ => decodeAux rest ⟨.term (.lam expression), stack⟩
      | _ => none
  | .push :: rest, ⟨value, stack⟩ => decodeAux rest ⟨value, value :: stack⟩
  | .swap :: rest, ⟨value, saved :: stack⟩ => decodeAux rest ⟨saved, value :: stack⟩
  | .cons :: rest, ⟨.term right, .term left :: stack⟩ =>
      decodeAux rest ⟨.term (.pair left right), stack⟩
  | .app :: rest, ⟨.term (.pair operator argument), stack⟩ =>
      decodeAux rest ⟨.term (.app operator argument), stack⟩
  | .quote value :: rest, ⟨.environment 0, stack⟩ =>
      if enabled : extended = true then decodeAux rest ⟨.term (.literal enabled value), stack⟩
      else none
  | .branch whenTrue whenFalse :: rest, ⟨.term condition, .environment 0 :: stack⟩ =>
      if enabled : extended = true then
        match decodeAux whenTrue ⟨.environment 0, []⟩,
            decodeAux whenFalse ⟨.environment 0, []⟩ with
        | some ⟨.term left, []⟩, some ⟨.term right, []⟩ =>
            decodeAux rest ⟨.term (.conditional enabled condition left right), stack⟩
        | _, _ => none
      else none
  | _, _ => none

private theorem decodeAux_lookup (index depth : Nat) (rest : Code)
    (stack : List (SymbolicValue extended)) :
    decodeAux (List.replicate index .first ++ .second :: rest) ⟨.environment depth, stack⟩ =
      decodeAux rest ⟨.term (.var (depth + index)), stack⟩ := by
  induction index generalizing depth with
  | zero => simp [decodeAux]
  | succ index ih =>
      simp only [List.replicate_succ, List.cons_append, decodeAux]
      simpa only [Nat.add_assoc, Nat.add_comm 1 index] using ih (depth + 1)

private theorem decodeAux_compile (expression : Source extended) (rest : Code)
    (stack : List (SymbolicValue extended)) :
    decodeAux (compileSource expression ++ rest) ⟨.environment 0, stack⟩ =
      decodeAux rest ⟨.term expression, stack⟩ := by
  induction expression generalizing rest stack with
  | var index => simpa only [compileSource, List.append_assoc, List.singleton_append, Nat.zero_add]
      using decodeAux_lookup index 0 rest stack
  | lam body ih =>
      simp only [compileSource, List.singleton_append, decodeAux]
      have bodyDecoded := ih [] []
      simp only [List.append_nil, decodeAux] at bodyDecoded
      rw [bodyDecoded]
  | app operator argument operatorIH argumentIH =>
      simp only [compileSource, List.append_assoc, List.cons_append, List.nil_append, decodeAux]
      rw [operatorIH]
      simp only [decodeAux]
      rw [argumentIH]
      simp only [decodeAux]
  | pair left right leftIH rightIH =>
      simp only [compileSource, List.append_assoc, List.cons_append, List.nil_append, decodeAux]
      rw [leftIH]
      simp only [decodeAux]
      rw [rightIH]
      simp only [decodeAux]
  | first term ih =>
      simp only [compileSource, List.append_assoc]
      rw [ih]
      simp only [List.singleton_append, decodeAux]
  | second term ih =>
      simp only [compileSource, List.append_assoc]
      rw [ih]
      simp only [List.singleton_append, decodeAux]
  | literal enabled value => simp [compileSource, decodeAux, enabled]
  | conditional enabled condition whenTrue whenFalse conditionIH trueIH falseIH =>
      simp only [compileSource, List.cons_append, List.append_assoc, decodeAux]
      rw [conditionIH]
      have trueDecoded := trueIH [] []
      have falseDecoded := falseIH [] []
      simp only [List.append_nil, decodeAux] at trueDecoded falseDecoded
      simp [decodeAux, enabled, trueDecoded, falseDecoded]

def decodeSourceCode (code : Code) : Option (Source extended) :=
  match decodeAux code ⟨.environment 0, []⟩ with
  | some ⟨.term expression, []⟩ => if compileSource expression = code then some expression else none
  | _ => none

@[simp] theorem decode_compile (expression : Source extended) : decodeSourceCode (compileSource expression) = some expression := by
  have reconstructed := decodeAux_compile expression [] []
  simp only [List.append_nil, decodeAux] at reconstructed
  simp [decodeSourceCode, reconstructed]

theorem compile_decode {code : Code} {expression : Source extended}
    (decoded : decodeSourceCode code = some expression) : compileSource expression = code := by
  unfold decodeSourceCode at decoded
  split at decoded
  · split at decoded
    · cases decoded
      assumption
    · contradiction
  · contradiction

theorem compile_injective : Function.Injective (@compileSource extended) := by
  intro left right same
  have decoded := congrArg (@decodeSourceCode extended) same
  simpa only [decode_compile, Option.some.injEq] using decoded

inductive SourceValue (extended : Bool) where
  | unit
  | literal (enabled : extended = true) (value : Literal)
  | pair (left right : SourceValue extended)
  | closure (body : Source extended) (environment : SourceValue extended)
  | first (value : SourceValue extended)
  | second (value : SourceValue extended)
  | app (value : SourceValue extended)
  deriving DecidableEq, Repr

abbrev Value := SourceValue false

namespace Value
abbrev unit := SourceValue.unit (extended := false)
abbrev pair := SourceValue.pair (extended := false)
abbrev closure := SourceValue.closure (extended := false)
abbrev first := SourceValue.first (extended := false)
abbrev second := SourceValue.second (extended := false)
abbrev app := SourceValue.app (extended := false)
end Value

inductive NativeValue where
  | unit
  | literal (value : Literal)
  | pair (left right : NativeValue)
  | closure (body : Code) (environment : NativeValue)
  | first (value : NativeValue)
  | second (value : NativeValue)
  | app (value : NativeValue)
  deriving DecidableEq, Repr

def encodeSourceValue : SourceValue extended → NativeValue
  | .unit => .unit
  | .literal _ value => .literal value
  | .pair left right => .pair (encodeSourceValue left) (encodeSourceValue right)
  | .closure body environment => .closure (compileSource body) (encodeSourceValue environment)
  | .first value => .first (encodeSourceValue value)
  | .second value => .second (encodeSourceValue value)
  | .app value => .app (encodeSourceValue value)

abbrev encodeValue : Value → NativeValue := encodeSourceValue

def decodeSourceValue : NativeValue → Option (SourceValue extended)
  | .unit => some .unit
  | .literal value => if enabled : extended = true then some (.literal enabled value) else none
  | .pair left right =>
      match decodeSourceValue left, decodeSourceValue right with
      | some left, some right => some (.pair left right)
      | _, _ => none
  | .closure body environment =>
      match decodeSourceCode body, decodeSourceValue environment with
      | some body, some environment => some (.closure body environment)
      | _, _ => none
  | .first value => (decodeSourceValue value).map .first
  | .second value => (decodeSourceValue value).map .second
  | .app value => (decodeSourceValue value).map .app

@[simp] theorem decode_encodeValue (value : SourceValue extended) : decodeSourceValue (encodeSourceValue value) = some value := by
  induction value <;> simp_all [encodeSourceValue, decodeSourceValue]

theorem encodeValue_injective : Function.Injective (@encodeSourceValue extended) := by
  intro left right same
  have decoded := congrArg (@decodeSourceValue extended) same
  simpa only [decode_encodeValue, Option.some.injEq] using decoded

theorem encode_decodeValue {native : NativeValue} {value : SourceValue extended}
    (decoded : decodeSourceValue native = some value) : encodeSourceValue value = native := by
  induction native generalizing value with
  | literal literal =>
      simp only [decodeSourceValue] at decoded
      split at decoded
      · cases decoded; rfl
      · contradiction
  | unit => simp only [decodeSourceValue, Option.some.injEq] at decoded; subst value; rfl
  | pair left right leftIH rightIH =>
      cases leftDecoded : decodeSourceValue (extended := extended) left with
      | none => simp [decodeSourceValue, leftDecoded] at decoded
      | some leftValue =>
          cases rightDecoded : decodeSourceValue (extended := extended) right with
          | none => simp [decodeSourceValue, leftDecoded, rightDecoded] at decoded
          | some rightValue =>
              simp only [decodeSourceValue, leftDecoded, rightDecoded, Option.some.injEq] at decoded
              subst value
              simp only [encodeSourceValue, leftIH leftDecoded, rightIH rightDecoded]
  | closure body environment environmentIH =>
      cases bodyDecoded : decodeSourceCode (extended := extended) body with
      | none => simp [decodeSourceValue, bodyDecoded] at decoded
      | some bodyValue =>
          cases environmentDecoded : decodeSourceValue (extended := extended) environment with
          | none => simp [decodeSourceValue, bodyDecoded, environmentDecoded] at decoded
          | some environmentValue =>
              simp only [decodeSourceValue, bodyDecoded, environmentDecoded, Option.some.injEq] at decoded
              subst value
              simp only [encodeSourceValue, compile_decode bodyDecoded, environmentIH environmentDecoded]
  | first native ih =>
      cases nativeDecoded : decodeSourceValue (extended := extended) native <;>
        simp only [decodeSourceValue, nativeDecoded, Option.map_some, Option.map_none,
          Option.some.injEq, reduceCtorEq] at decoded
      subst value
      simp only [encodeSourceValue, ih nativeDecoded]
  | second native ih =>
      cases nativeDecoded : decodeSourceValue (extended := extended) native <;>
        simp only [decodeSourceValue, nativeDecoded, Option.map_some, Option.map_none,
          Option.some.injEq, reduceCtorEq] at decoded
      subst value
      simp only [encodeSourceValue, ih nativeDecoded]
  | app native ih =>
      cases nativeDecoded : decodeSourceValue (extended := extended) native <;>
        simp only [decodeSourceValue, nativeDecoded, Option.map_some, Option.map_none,
          Option.some.injEq, reduceCtorEq] at decoded
      subst value
      simp only [encodeSourceValue, ih nativeDecoded]

def firstValue : SourceValue extended → SourceValue extended
  | .pair left _ => left
  | value => .first value

def secondValue : SourceValue extended → SourceValue extended
  | .pair _ right => right
  | value => .second value

def NotPair : SourceValue extended → Prop
  | .pair _ _ => False
  | _ => True

def NotClosure : SourceValue extended → Prop
  | .closure _ _ => False
  | _ => True

inductive First : SourceValue extended → SourceValue extended → Prop where
  | pair (left right : SourceValue extended) : First (.pair left right) left
  | neutral (value : SourceValue extended) (inactive : NotPair value) : First value (.first value)

inductive Second : SourceValue extended → SourceValue extended → Prop where
  | pair (left right : SourceValue extended) : Second (.pair left right) right
  | neutral (value : SourceValue extended) (inactive : NotPair value) : Second value (.second value)

theorem firstValue_sound (value : SourceValue extended) : First value (firstValue value) := by
  cases value <;> first | exact .pair _ _ | exact .neutral _ trivial

theorem secondValue_sound (value : SourceValue extended) : Second value (secondValue value) := by
  cases value <;> first | exact .pair _ _ | exact .neutral _ trivial

theorem First.result {value result : SourceValue extended} (derivation : First value result) :
    firstValue value = result := by
  cases derivation with
  | pair => rfl
  | neutral value inactive => cases value <;> simp_all [NotPair, firstValue]

theorem Second.result {value result : SourceValue extended} (derivation : Second value result) :
    secondValue value = result := by
  cases derivation with
  | pair => rfl
  | neutral value inactive => cases value <;> simp_all [NotPair, secondValue]

mutual
/-- Independent completed combinatory evaluation, with active rules taking
precedence over neutral rules. Instruction lists do not occur in this judgment. -/
inductive Evaluation : Source extended → SourceValue extended → SourceValue extended → Prop where
  | varZero {environment value : SourceValue extended} (projection : Second environment value) :
      Evaluation (.var 0) environment value
  | varSucc {index : Nat} {environment before value : SourceValue extended}
      (projection : First environment before) (rest : Evaluation (.var index) before value) :
      Evaluation (.var (index + 1)) environment value
  | literal (enabled : extended = true) (value : Literal) (environment : SourceValue extended) :
      Evaluation (.literal enabled value) environment (.literal enabled value)
  | conditional {enabled : extended = true} {condition whenTrue whenFalse : Source extended}
      {environment value : SourceValue extended} {selected : Bool}
      (conditionEval : Evaluation condition environment (.literal enabled (.boolean selected)))
      (selectedEval : Evaluation (if selected then whenTrue else whenFalse) environment value) :
      Evaluation (.conditional enabled condition whenTrue whenFalse) environment value
  | lam (body : Source extended) (environment : SourceValue extended) :
      Evaluation (.lam body) environment (.closure body environment)
  | pair {left right : Source extended} {environment first second : SourceValue extended}
      (leftEval : Evaluation left environment first)
      (rightEval : Evaluation right environment second) :
      Evaluation (.pair left right) environment (.pair first second)
  | app {operator argument : Source extended} {environment function operand value : SourceValue extended}
      (operatorEval : Evaluation operator environment function)
      (argumentEval : Evaluation argument environment operand)
      (invocation : Invocation function operand value) :
      Evaluation (.app operator argument) environment value
  | first {term : Source extended} {environment before value : SourceValue extended}
      (termEval : Evaluation term environment before) (projection : First before value) :
      Evaluation (.first term) environment value
  | second {term : Source extended} {environment before value : SourceValue extended}
      (termEval : Evaluation term environment before) (projection : Second before value) :
      Evaluation (.second term) environment value
inductive Invocation : SourceValue extended → SourceValue extended → SourceValue extended → Prop where
  | closure {body : Source extended} {environment argument value : SourceValue extended}
      (bodyEval : Evaluation body (.pair environment argument) value) :
      Invocation (.closure body environment) argument value
  | neutral (function argument : SourceValue extended) (inactive : NotClosure function) :
      Invocation function argument (.app (.pair function argument))
end

/-- The historical code/value readers retain their original constant-free boundary. -/
abbrev decodeCode : Code → Option Expr := decodeSourceCode
abbrev decodeValue : NativeValue → Option Value := decodeSourceValue

inductive Profile where
  | strict
  | neutral
  deriving DecidableEq, Repr

structure State where
  register : NativeValue
  code : Code
  stack : List NativeValue
  deriving DecidableEq, Repr

def NativeNotPair : NativeValue → Prop
  | .pair _ _ => False
  | _ => True

def NativeNotApplicable : NativeValue → Prop
  | .pair (.closure _ _) _ => False
  | _ => True

/-- The instruction table as independent operational rules. There is no rule
for `operation`, `wind`, `freeze` or `unfreeze`: a tree configuration with one
of them at the head is stopped. They are interpreted by the value-graph machine
of `CategoricalAbstractMachineGraph`. -/
inductive Transition : Profile → State → State → Prop where
  | firstPair (profile : Profile) (left right : NativeValue) (code : Code)
      (stack : List NativeValue) :
      Transition profile ⟨.pair left right, .first :: code, stack⟩ ⟨left, code, stack⟩
  | firstNeutral (value : NativeValue) (code : Code) (stack : List NativeValue)
      (inactive : NativeNotPair value) :
      Transition .neutral ⟨value, .first :: code, stack⟩ ⟨.first value, code, stack⟩
  | secondPair (profile : Profile) (left right : NativeValue) (code : Code)
      (stack : List NativeValue) :
      Transition profile ⟨.pair left right, .second :: code, stack⟩ ⟨right, code, stack⟩
  | secondNeutral (value : NativeValue) (code : Code) (stack : List NativeValue)
      (inactive : NativeNotPair value) :
      Transition .neutral ⟨value, .second :: code, stack⟩ ⟨.second value, code, stack⟩
  | cur (profile : Profile) (value : NativeValue) (body code : Code)
      (stack : List NativeValue) :
      Transition profile ⟨value, .cur body :: code, stack⟩ ⟨.closure body value, code, stack⟩
  | push (profile : Profile) (value : NativeValue) (code : Code)
      (stack : List NativeValue) :
      Transition profile ⟨value, .push :: code, stack⟩ ⟨value, code, value :: stack⟩
  | swap (profile : Profile) (value saved : NativeValue) (code : Code)
      (stack : List NativeValue) :
      Transition profile ⟨value, .swap :: code, saved :: stack⟩ ⟨saved, code, value :: stack⟩
  | cons (profile : Profile) (value saved : NativeValue) (code : Code)
      (stack : List NativeValue) :
      Transition profile ⟨value, .cons :: code, saved :: stack⟩ ⟨.pair saved value, code, stack⟩
  | appClosure (profile : Profile) (environment argument : NativeValue) (body code : Code)
      (stack : List NativeValue) :
      Transition profile ⟨.pair (.closure body environment) argument, .app :: code, stack⟩
        ⟨.pair environment argument, body ++ code, stack⟩
  | appNeutral (value : NativeValue) (code : Code) (stack : List NativeValue)
      (inactive : NativeNotApplicable value) :
      Transition .neutral ⟨value, .app :: code, stack⟩ ⟨.app value, code, stack⟩
  | quote (profile : Profile) (value : NativeValue) (literal : Literal) (code : Code)
      (stack : List NativeValue) :
      Transition profile ⟨value, .quote literal :: code, stack⟩ ⟨.literal literal, code, stack⟩
  | branchTrue (profile : Profile) (saved : NativeValue) (whenTrue whenFalse code : Code)
      (stack : List NativeValue) :
      Transition profile ⟨.literal (.boolean true), .branch whenTrue whenFalse :: code, saved :: stack⟩
        ⟨saved, whenTrue ++ code, stack⟩
  | branchFalse (profile : Profile) (saved : NativeValue) (whenTrue whenFalse code : Code)
      (stack : List NativeValue) :
      Transition profile ⟨.literal (.boolean false), .branch whenTrue whenFalse :: code, saved :: stack⟩
        ⟨saved, whenFalse ++ code, stack⟩

/-- Executable instruction table. The four value-graph instructions (`operation`,
`wind`, `freeze`, `unfreeze`) fall to the final case: the tree machine stops there. -/
def step (profile : Profile) : State → Option State
  | ⟨_, [], _⟩ => none
  | ⟨value, .first :: code, stack⟩ =>
      match value with
      | .pair left _ => some ⟨left, code, stack⟩
      | _ => match profile with
          | .strict => none
          | .neutral => some ⟨.first value, code, stack⟩
  | ⟨value, .second :: code, stack⟩ =>
      match value with
      | .pair _ right => some ⟨right, code, stack⟩
      | _ => match profile with
          | .strict => none
          | .neutral => some ⟨.second value, code, stack⟩
  | ⟨_, .quote literal :: code, stack⟩ => some ⟨.literal literal, code, stack⟩
  | ⟨.literal (.boolean true), .branch whenTrue _ :: code, saved :: stack⟩ =>
      some ⟨saved, whenTrue ++ code, stack⟩
  | ⟨.literal (.boolean false), .branch _ whenFalse :: code, saved :: stack⟩ =>
      some ⟨saved, whenFalse ++ code, stack⟩
  | ⟨value, .cur body :: code, stack⟩ => some ⟨.closure body value, code, stack⟩
  | ⟨value, .push :: code, stack⟩ => some ⟨value, code, value :: stack⟩
  | ⟨value, .swap :: code, saved :: stack⟩ => some ⟨saved, code, value :: stack⟩
  | ⟨value, .cons :: code, saved :: stack⟩ => some ⟨.pair saved value, code, stack⟩
  | ⟨value, .app :: code, stack⟩ =>
      match value with
      | .pair (.closure body environment) argument =>
          some ⟨.pair environment argument, body ++ code, stack⟩
      | _ => match profile with
          | .strict => none
          | .neutral => some ⟨.app value, code, stack⟩
  | _ => none

theorem step_complete {profile : Profile} {before after : State}
    (transition : Transition profile before after) : step profile before = some after := by
  cases transition with
  | firstPair => rfl
  | firstNeutral value code stack inactive => cases value <;> simp_all [NativeNotPair, step]
  | secondPair => rfl
  | secondNeutral value code stack inactive => cases value <;> simp_all [NativeNotPair, step]
  | cur => rfl
  | push => rfl
  | swap => rfl
  | cons => rfl
  | appClosure => rfl
  | quote => rfl
  | branchTrue => rfl
  | branchFalse => rfl
  | appNeutral value code stack inactive =>
      cases value with
      | pair left right =>
          cases left with
          | closure _ _ => exact False.elim inactive
          | unit | literal _ | pair _ _ | first _ | second _ | app _ => rfl
      | unit | literal _ | closure _ _ | first _ | second _ | app _ => rfl

theorem step_sound {profile : Profile} {before after : State}
    (execution : step profile before = some after) : Transition profile before after := by
  rcases before with ⟨value, code, stack⟩
  cases code with
  | nil => simp [step] at execution
  | cons instruction code =>
      cases instruction with
      | first =>
          cases value <;> cases profile <;> simp only [step, Option.some.injEq, reduceCtorEq] at execution
          all_goals subst after
          all_goals first | exact .firstPair _ _ _ _ _ | exact .firstNeutral _ _ _ trivial
      | second =>
          cases value <;> cases profile <;> simp only [step, Option.some.injEq, reduceCtorEq] at execution
          all_goals subst after
          all_goals first | exact .secondPair _ _ _ _ _ | exact .secondNeutral _ _ _ trivial
      | quote literal =>
          simp only [step, Option.some.injEq] at execution
          subst after
          exact .quote _ _ _ _ _
      | branch whenTrue whenFalse =>
          cases value <;> cases stack <;> simp only [step, reduceCtorEq] at execution
          rename_i literal saved stack
          cases literal with
          | integer | unit => simp at execution
          | boolean selected =>
              cases selected <;> simp only [Option.some.injEq] at execution
              all_goals subst after
              · exact .branchFalse _ _ _ _ _ _
              · exact .branchTrue _ _ _ _ _ _
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
              have same := Option.some.inj execution
              subst after
              exact .swap _ _ _ _ _
      | cons =>
          cases stack with
          | nil => simp [step] at execution
          | cons saved stack =>
              have same := Option.some.inj execution
              subst after
              exact .cons _ _ _ _ _
      | app =>
          cases value with
          | pair left right =>
              cases left <;> cases profile <;>
                simp only [step, Option.some.injEq, reduceCtorEq] at execution
              all_goals subst after
              all_goals first | exact .appClosure _ _ _ _ _ _ | exact .appNeutral _ _ _ trivial
          | unit | literal _ | closure _ _ | first _ | second _ | app _ =>
              cases profile <;> simp only [step, Option.some.injEq, reduceCtorEq] at execution
              all_goals subst after
              all_goals exact .appNeutral _ _ _ trivial
      | operation _ | wind | freeze _ | unfreeze => simp [step] at execution

theorem step_iff (profile : Profile) (before after : State) :
    step profile before = some after ↔ Transition profile before after :=
  ⟨step_sound, step_complete⟩

abbrev Steps (profile : Profile) := Relation.ReflTransGen (Transition profile)

def extend (state : State) (code : Code) (stack : List NativeValue) : State :=
  ⟨state.register, state.code ++ code, state.stack ++ stack⟩

theorem Transition.extend {profile : Profile} {before after : State}
    (transition : Transition profile before after) (code : Code) (stack : List NativeValue) :
    Transition profile (extend before code stack) (extend after code stack) := by
  cases transition <;> dsimp only [CategoricalAbstractMachine.extend]
  all_goals try simp only [List.cons_append, List.append_assoc]
  all_goals first
    | exact .firstPair _ _ _ _ _
    | exact .firstNeutral _ _ _ ‹_›
    | exact .secondPair _ _ _ _ _
    | exact .secondNeutral _ _ _ ‹_›
    | exact .cur _ _ _ _ _
    | exact .push _ _ _ _
    | exact .swap _ _ _ _ _
    | exact .cons _ _ _ _ _
    | exact .appClosure _ _ _ _ _ _
    | exact .appNeutral _ _ _ ‹_›
    | exact .quote _ _ _ _ _
    | exact .branchTrue _ _ _ _ _ _
    | exact .branchFalse _ _ _ _ _ _

theorem Steps.extend {profile : Profile} {before after : State}
    (execution : Steps profile before after) (code : Code) (stack : List NativeValue) :
    Steps profile (extend before code stack) (extend after code stack) := by
  induction execution with
  | refl => exact .refl
  | tail _ transition ih => exact ih.tail (transition.extend code stack)

/-! ## The original constant-free compiled image

These predicates retain the original instruction and value profile inside
the extended raw instruction table. They certify syntax, not historical
source scope, memory ownership or publication authority.
-/

mutual
inductive ConstantFreeInstruction : Instruction → Prop where
  | first : ConstantFreeInstruction .first
  | second : ConstantFreeInstruction .second
  | cur {body : Code} (bodyFree : ConstantFreeCode body) : ConstantFreeInstruction (.cur body)
  | push : ConstantFreeInstruction .push
  | swap : ConstantFreeInstruction .swap
  | cons : ConstantFreeInstruction .cons
  | app : ConstantFreeInstruction .app
inductive ConstantFreeCode : Code → Prop where
  | nil : ConstantFreeCode []
  | cons {instruction : Instruction} {rest : Code}
      (headFree : ConstantFreeInstruction instruction) (tailFree : ConstantFreeCode rest) :
      ConstantFreeCode (instruction :: rest)
end

inductive ConstantFreeValue : NativeValue → Prop where
  | unit : ConstantFreeValue .unit
  | pair {left right : NativeValue} (leftFree : ConstantFreeValue left)
      (rightFree : ConstantFreeValue right) : ConstantFreeValue (.pair left right)
  | closure {body : Code} {environment : NativeValue}
      (bodyFree : ConstantFreeCode body) (environmentFree : ConstantFreeValue environment) :
      ConstantFreeValue (.closure body environment)
  | first {value : NativeValue} (valueFree : ConstantFreeValue value) : ConstantFreeValue (.first value)
  | second {value : NativeValue} (valueFree : ConstantFreeValue value) : ConstantFreeValue (.second value)
  | app {value : NativeValue} (valueFree : ConstantFreeValue value) : ConstantFreeValue (.app value)

def ConstantFreeState (state : State) : Prop :=
  ConstantFreeValue state.register ∧ ConstantFreeCode state.code ∧
    ∀ value ∈ state.stack, ConstantFreeValue value

theorem ConstantFreeCode.head {instruction : Instruction} {rest : Code}
    (free : ConstantFreeCode (instruction :: rest)) : ConstantFreeInstruction instruction := by
  cases free with
  | cons headFree _ => exact headFree

theorem ConstantFreeCode.tail {instruction : Instruction} {rest : Code}
    (free : ConstantFreeCode (instruction :: rest)) : ConstantFreeCode rest := by
  cases free with
  | cons _ tailFree => exact tailFree

theorem ConstantFreeCode.append {left right : Code} (leftFree : ConstantFreeCode left)
    (rightFree : ConstantFreeCode right) : ConstantFreeCode (left ++ right) := by
  induction left with
  | nil => exact rightFree
  | cons instruction rest ih => exact .cons leftFree.head (ih leftFree.tail)

theorem ConstantFreeCode.singleton {instruction : Instruction}
    (free : ConstantFreeInstruction instruction) : ConstantFreeCode [instruction] := .cons free .nil

theorem ConstantFreeCode.replicate {instruction : Instruction}
    (free : ConstantFreeInstruction instruction) (count : Nat) :
    ConstantFreeCode (List.replicate count instruction) := by
  induction count with
  | zero => exact .nil
  | succ count ih => simpa only [List.replicate_succ] using ConstantFreeCode.cons free ih

theorem compile_constantFree (term : Expr) : ConstantFreeCode (compileSource term) := by
  induction term with
  | var index => exact (ConstantFreeCode.replicate .first index).append (.singleton .second)
  | lam body ih => exact .singleton (.cur ih)
  | app operator argument operatorIH argumentIH =>
      exact ((((ConstantFreeCode.singleton .push).append operatorIH).append (.singleton .swap)).append
        argumentIH).append (.cons .cons (.singleton .app))
  | pair left right leftIH rightIH =>
      exact ((((ConstantFreeCode.singleton .push).append leftIH).append (.singleton .swap)).append
        rightIH).append (.singleton .cons)
  | first term ih => exact ih.append (.singleton .first)
  | second term ih => exact ih.append (.singleton .second)
  | literal enabled _ => cases enabled
  | conditional enabled _ _ _ _ _ _ => cases enabled

theorem encodeValue_constantFree (value : Value) : ConstantFreeValue (encodeSourceValue value) := by
  induction value with
  | unit => exact .unit
  | literal enabled _ => cases enabled
  | pair _ _ leftIH rightIH => exact .pair leftIH rightIH
  | closure body _ ih => exact .closure (compile_constantFree body) ih
  | first _ ih => exact .first ih
  | second _ ih => exact .second ih
  | app _ ih => exact .app ih

theorem ConstantFreeValue.pair_left {left right : NativeValue}
    (free : ConstantFreeValue (.pair left right)) : ConstantFreeValue left := by
  cases free with
  | pair leftFree _ => exact leftFree

theorem ConstantFreeValue.pair_right {left right : NativeValue}
    (free : ConstantFreeValue (.pair left right)) : ConstantFreeValue right := by
  cases free with
  | pair _ rightFree => exact rightFree

theorem ConstantFreeValue.closure_code {body : Code} {environment : NativeValue}
    (free : ConstantFreeValue (.closure body environment)) : ConstantFreeCode body := by
  cases free with
  | closure bodyFree _ => exact bodyFree

theorem ConstantFreeValue.closure_environment {body : Code} {environment : NativeValue}
    (free : ConstantFreeValue (.closure body environment)) : ConstantFreeValue environment := by
  cases free with
  | closure _ environmentFree => exact environmentFree

theorem ConstantFreeValue.not_literal {value : NativeValue} (free : ConstantFreeValue value)
    (literal : Literal) : value ≠ .literal literal := by
  intro same
  subst value
  cases free

theorem Transition.constantFree {profile : Profile} {before after : State}
    (transition : Transition profile before after) (free : ConstantFreeState before) :
    ConstantFreeState after := by
  cases transition with
  | firstPair profile left right code stack =>
      rcases free with ⟨valueFree, codeFree, stackFree⟩
      exact ⟨valueFree.pair_left, codeFree.tail, stackFree⟩
  | firstNeutral value code stack inactive =>
      rcases free with ⟨valueFree, codeFree, stackFree⟩
      exact ⟨.first valueFree, codeFree.tail, stackFree⟩
  | secondPair profile left right code stack =>
      rcases free with ⟨valueFree, codeFree, stackFree⟩
      exact ⟨valueFree.pair_right, codeFree.tail, stackFree⟩
  | secondNeutral value code stack inactive =>
      rcases free with ⟨valueFree, codeFree, stackFree⟩
      exact ⟨.second valueFree, codeFree.tail, stackFree⟩
  | cur profile value body code stack =>
      rcases free with ⟨valueFree, codeFree, stackFree⟩
      have bodyFree : ConstantFreeCode body := by
        cases codeFree.head with
        | cur bodyFree => exact bodyFree
      exact ⟨.closure bodyFree valueFree, codeFree.tail, stackFree⟩
  | push profile value code stack =>
      rcases free with ⟨valueFree, codeFree, stackFree⟩
      refine ⟨valueFree, codeFree.tail, ?_⟩
      intro next member
      rcases List.mem_cons.mp member with same | previous
      · exact same ▸ valueFree
      · exact stackFree next previous
  | swap profile value saved code stack =>
      rcases free with ⟨valueFree, codeFree, stackFree⟩
      refine ⟨stackFree saved (List.mem_cons_self), codeFree.tail, ?_⟩
      intro next member
      rcases List.mem_cons.mp member with same | previous
      · exact same ▸ valueFree
      · exact stackFree next (List.mem_cons_of_mem _ previous)
  | cons profile value saved code stack =>
      rcases free with ⟨valueFree, codeFree, stackFree⟩
      exact ⟨.pair (stackFree saved (List.mem_cons_self)) valueFree, codeFree.tail,
        fun next member => stackFree next (List.mem_cons_of_mem _ member)⟩
  | appClosure profile environment argument body code stack =>
      rcases free with ⟨valueFree, codeFree, stackFree⟩
      exact ⟨.pair valueFree.pair_left.closure_environment valueFree.pair_right,
        valueFree.pair_left.closure_code.append codeFree.tail, stackFree⟩
  | appNeutral value code stack inactive =>
      rcases free with ⟨valueFree, codeFree, stackFree⟩
      exact ⟨.app valueFree, codeFree.tail, stackFree⟩
  | quote profile value literal code stack => cases free.2.1.head
  | branchTrue profile saved whenTrue whenFalse code stack => cases free.2.1.head
  | branchFalse profile saved whenTrue whenFalse code stack => cases free.2.1.head

theorem Steps.constantFree {profile : Profile} {before after : State}
    (execution : Steps profile before after) (free : ConstantFreeState before) :
    ConstantFreeState after := by
  induction execution with
  | refl => exact free
  | tail _ transition ih => exact transition.constantFree ih

/-- The old compiler image and all of its reachable configurations remain
inside the old instruction/value profile, even in the extended machine.
The previously constructed source correspondences therefore retain their
original source boundary in both directions. -/
theorem compiled_constantFree {profile : Profile} {term : Expr} {environment : Value} {state : State}
    (execution : Steps profile ⟨encodeSourceValue environment, compileSource term, []⟩ state) :
    ConstantFreeState state :=
  execution.constantFree ⟨encodeValue_constantFree environment, compile_constantFree term,
    by intro value member; cases member⟩

theorem compiled_cannot_quote {profile : Profile} {term : Expr} {environment : Value} {state : State}
    (execution : Steps profile ⟨encodeSourceValue environment, compileSource term, []⟩ state)
    (literal : Literal) (rest : Code) : state.code ≠ .quote literal :: rest := by
  intro same
  have free := (compiled_constantFree execution).2.1
  rw [same] at free
  cases free.head

theorem compiled_cannot_branch {profile : Profile} {term : Expr} {environment : Value} {state : State}
    (execution : Steps profile ⟨encodeSourceValue environment, compileSource term, []⟩ state)
    (whenTrue whenFalse rest : Code) : state.code ≠ .branch whenTrue whenFalse :: rest := by
  intro same
  have free := (compiled_constantFree execution).2.1
  rw [same] at free
  cases free.head

theorem compiled_cannot_produce_literal {profile : Profile} {term : Expr} {environment : Value}
    {state : State} (execution : Steps profile ⟨encodeSourceValue environment, compileSource term, []⟩ state)
    (literal : Literal) : state.register ≠ .literal literal :=
  (compiled_constantFree execution).1.not_literal literal

@[simp] theorem decode_literal (literal : Literal) : decodeValue (.literal literal) = none := rfl

@[simp] theorem decode_quote (literal : Literal) (rest : Code) :
    decodeCode (.quote literal :: rest) = none := by simp [decodeCode, decodeSourceCode]

@[simp] theorem decode_branch (whenTrue whenFalse rest : Code) :
    decodeCode (.branch whenTrue whenFalse :: rest) = none := by simp [decodeCode, decodeSourceCode]

/-! ## Quotation and selected branch continuations -/

@[simp] theorem quote_step (profile : Profile) (value : NativeValue) (literal : Literal) (code : Code)
    (stack : List NativeValue) :
    step profile ⟨value, .quote literal :: code, stack⟩ = some ⟨.literal literal, code, stack⟩ := rfl

theorem quote_transition_iff (profile : Profile) (value : NativeValue) (literal : Literal) (code : Code)
    (stack : List NativeValue) (after : State) :
    Transition profile ⟨value, .quote literal :: code, stack⟩ after ↔
      after = ⟨.literal literal, code, stack⟩ := by
  rw [← step_iff, quote_step, Option.some.injEq, eq_comm]

@[simp] theorem branch_step (profile : Profile) (selected : Bool) (saved : NativeValue)
    (whenTrue whenFalse code : Code) (stack : List NativeValue) :
    step profile ⟨.literal (.boolean selected), .branch whenTrue whenFalse :: code, saved :: stack⟩ =
      some ⟨saved, (if selected then whenTrue else whenFalse) ++ code, stack⟩ := by
  cases selected <;> rfl

/-- Selection restores the exact saved environment, consumes its one stack
entry and appends exactly the selected arm before the retained code suffix.
No property or execution of the unselected arm is required. -/
theorem branch_transition_iff (profile : Profile) (selected : Bool) (saved : NativeValue)
    (whenTrue whenFalse code : Code) (stack : List NativeValue) (after : State) :
    Transition profile
      ⟨.literal (.boolean selected), .branch whenTrue whenFalse :: code, saved :: stack⟩ after ↔
      after = ⟨saved, (if selected then whenTrue else whenFalse) ++ code, stack⟩ := by
  rw [← step_iff, branch_step, Option.some.injEq, eq_comm]

/-- A completed selected arm retains arbitrary caller code and stack. This
law uses the independently judged arm execution and the generic suffix law;
it does not assert that an arbitrary raw arm is a compiled source term. -/
theorem branch_execution_tail (profile : Profile) (selected : Bool) (saved result : NativeValue)
    (whenTrue whenFalse code : Code) (stack : List NativeValue)
    (chosen : Steps profile ⟨saved, if selected then whenTrue else whenFalse, []⟩ ⟨result, [], []⟩) :
    Steps profile ⟨.literal (.boolean selected), .branch whenTrue whenFalse :: code, saved :: stack⟩
      ⟨result, code, stack⟩ := by
  have first := step_sound (branch_step profile selected saved whenTrue whenFalse code stack)
  simpa only [extend, List.nil_append] using Relation.ReflTransGen.head first (chosen.extend code stack)

theorem first_transition (value : SourceValue extended) (code : Code) (stack : List NativeValue) :
    Transition .neutral ⟨encodeSourceValue value, .first :: code, stack⟩
      ⟨encodeSourceValue (firstValue value), code, stack⟩ := by
  cases value <;> first | exact .firstPair _ _ _ _ _ | exact .firstNeutral _ _ _ trivial

theorem second_transition (value : SourceValue extended) (code : Code) (stack : List NativeValue) :
    Transition .neutral ⟨encodeSourceValue value, .second :: code, stack⟩
      ⟨encodeSourceValue (secondValue value), code, stack⟩ := by
  cases value <;> first | exact .secondPair _ _ _ _ _ | exact .secondNeutral _ _ _ trivial

theorem Evaluation.execution_tail {term : Source extended} {environment value : SourceValue extended}
    (evaluation : Evaluation term environment value) (code : Code) (stack : List NativeValue) :
    Steps .neutral ⟨encodeSourceValue environment, compileSource term ++ code, stack⟩
      ⟨encodeSourceValue value, code, stack⟩ := by
  induction evaluation using Evaluation.rec
      (motive_2 := fun function argument value _ => ∀ (code : Code) (stack : List NativeValue),
        Steps .neutral ⟨.pair (encodeSourceValue function) (encodeSourceValue argument), .app :: code, stack⟩
          ⟨encodeSourceValue value, code, stack⟩) generalizing code stack with
  | @varZero environment _ projection =>
      have transition := second_transition environment code stack
      rw [projection.result] at transition
      exact .single transition
  | @varSucc index environment _ _ projection _ restIH =>
      have transition := first_transition environment (compileSource (extended := extended) (.var index) ++ code) stack
      rw [projection.result] at transition
      simpa only [compile_var_succ, List.cons_append] using
        (Relation.ReflTransGen.head transition (restIH code stack))
  | literal => exact .single (.quote .neutral _ _ _ _)
  | @conditional enabled condition whenTrue whenFalse environment value selected _ _ conditionIH selectedIH =>
      simp only [compileSource, List.cons_append, List.append_assoc]
      have conditionRun := conditionIH (.branch (compileSource whenTrue) (compileSource whenFalse) :: code)
        (encodeSourceValue environment :: stack)
      have selectedRun := selectedIH code stack
      have chosen := step_sound (branch_step .neutral selected (encodeSourceValue environment)
        (compileSource whenTrue) (compileSource whenFalse) code stack)
      cases selected <;> simp only [Bool.false_eq_true, if_false, if_true] at selectedRun chosen
      · exact .head (.push .neutral _ _ _) (conditionRun.trans (.head chosen selectedRun))
      · exact .head (.push .neutral _ _ _) (conditionRun.trans (.head chosen selectedRun))
  | lam => exact .single (.cur .neutral _ _ _ _)
  | @pair _ right environment first _ _ _ leftIH rightIH =>
      simp only [compileSource, List.append_assoc, List.cons_append, List.nil_append]
      have leftRun := leftIH (.swap :: (compileSource right ++ .cons :: code))
        (encodeSourceValue environment :: stack)
      have rightRun := rightIH (.cons :: code) (encodeSourceValue first :: stack)
      exact .head (.push .neutral _ _ _) (leftRun.trans
        (.head (.swap .neutral _ _ _ _) (rightRun.tail (.cons .neutral _ _ _ _))))
  | @app _ argument environment function _ _ _ _ _ operatorIH argumentIH invocationIH =>
      simp only [compileSource, List.append_assoc, List.cons_append, List.nil_append]
      have operatorRun := operatorIH
        (.swap :: (compileSource argument ++ .cons :: .app :: code)) (encodeSourceValue environment :: stack)
      have argumentRun := argumentIH (.cons :: .app :: code)
        (encodeSourceValue function :: stack)
      exact .head (.push .neutral _ _ _) (operatorRun.trans
        (.head (.swap .neutral _ _ _ _) ((argumentRun.tail (.cons .neutral _ _ _ _)).trans
          (invocationIH code stack))))
  | @first _ _ before _ _ projection termIH =>
      have transition := first_transition before code stack
      rw [projection.result] at transition
      simpa only [compileSource, List.append_assoc, List.singleton_append] using
        (termIH (.first :: code) stack).tail transition
  | @second _ _ before _ _ projection termIH =>
      have transition := second_transition before code stack
      rw [projection.result] at transition
      simpa only [compileSource, List.append_assoc, List.singleton_append] using
        (termIH (.second :: code) stack).tail transition
  | closure _ bodyIH =>
      rename_i code stack
      exact .head (.appClosure .neutral _ _ _ _ _) (bodyIH code stack)
  | neutral function argument inactive =>
      rename_i code stack
      have notApplicable : NativeNotApplicable (.pair (encodeSourceValue function) (encodeSourceValue argument)) := by
        cases function <;> simp_all [encodeSourceValue, NotClosure, NativeNotApplicable]
      exact .single (.appNeutral _ _ _ notApplicable)
theorem Invocation.execution_tail {function argument value : SourceValue extended}
    (invocation : Invocation function argument value) (code : Code) (stack : List NativeValue) :
    Steps .neutral ⟨.pair (encodeSourceValue function) (encodeSourceValue argument), .app :: code, stack⟩
      ⟨encodeSourceValue value, code, stack⟩ := by
  cases invocation with
  | closure bodyEval =>
      exact .head (.appClosure .neutral _ _ _ _ _) (bodyEval.execution_tail code stack)
  | neutral function argument inactive =>
      have notApplicable : NativeNotApplicable (.pair (encodeSourceValue function) (encodeSourceValue argument)) := by
        cases function <;> simp_all [encodeSourceValue, NotClosure, NativeNotApplicable]
      exact .single (.appNeutral _ _ _ notApplicable)
theorem Evaluation.execution {term : Source extended} {environment value : SourceValue extended}
    (evaluation : Evaluation term environment value) :
    Steps .neutral ⟨encodeSourceValue environment, compileSource term, []⟩ ⟨encodeSourceValue value, [], []⟩ := by
  simpa only [List.append_nil] using evaluation.execution_tail [] []

/-! Evaluation-context witnesses reconstruct source evaluations from native
instruction traces. They are proof data, not an additional machine interface. -/

private inductive Frame (extended : Bool) where
  | condition (enabled : extended = true) (whenTrue whenFalse : Source extended) (environment : SourceValue extended)
  | pairLeft (right : Source extended) (environment : SourceValue extended)
  | pairRight (left : SourceValue extended)
  | appLeft (argument : Source extended) (environment : SourceValue extended)
  | appRight (function : SourceValue extended)
  | first
  | second

private def frameCode : Frame extended → Code
  | .pairLeft right _ => .swap :: (compileSource right ++ [.cons])
  | .pairRight _ => [.cons]
  | .appLeft argument _ => .swap :: (compileSource argument ++ [.cons, .app])
  | .appRight _ => [.cons, .app]
  | .first => [.first]
  | .second => [.second]
  | .condition _ whenTrue whenFalse _ => [.branch (compileSource whenTrue) (compileSource whenFalse)]

private def contextCode : List (Frame extended) → Code
  | [] => []
  | frame :: rest => frameCode frame ++ contextCode rest

private def contextStack : List (Frame extended) → List NativeValue
  | [] => []
  | .condition _ _ _ environment :: rest | .pairLeft _ environment :: rest | .appLeft _ environment :: rest =>
      encodeSourceValue environment :: contextStack rest
  | .pairRight left :: rest | .appRight left :: rest => encodeSourceValue left :: contextStack rest
  | .first :: rest | .second :: rest => contextStack rest

private theorem contextCode_nil_iff (frames : List (Frame extended)) : contextCode frames = [] ↔ frames = [] := by
  cases frames with
  | nil => simp [contextCode]
  | cons frame rest => cases frame <;> simp [contextCode, frameCode]

private inductive Focus (extended : Bool) where
  | evaluate (term : Source extended) (environment : SourceValue extended)
  | returned (value : SourceValue extended)
  | invoke (function argument : SourceValue extended)

private structure Packet (extended : Bool) where
  focus : Focus extended
  frames : List (Frame extended)

private def encodePacket (packet : Packet extended) : State :=
  match packet.focus with
  | .evaluate term environment =>
      ⟨encodeSourceValue environment, compileSource term ++ contextCode packet.frames, contextStack packet.frames⟩
  | .returned value => ⟨encodeSourceValue value, contextCode packet.frames, contextStack packet.frames⟩
  | .invoke function argument =>
      ⟨.pair (encodeSourceValue function) (encodeSourceValue argument), .app :: contextCode packet.frames,
        contextStack packet.frames⟩

private def exposeEvaluation : Source extended → SourceValue extended → List (Frame extended) → Packet extended
  | .first term, environment, frames => exposeEvaluation term environment (.first :: frames)
  | .second term, environment, frames => exposeEvaluation term environment (.second :: frames)
  | term, environment, frames => ⟨.evaluate term environment, frames⟩

private def exposePacket (packet : Packet extended) : Packet extended :=
  match packet.focus with
  | .evaluate term environment => exposeEvaluation term environment packet.frames
  | _ => packet

private def Ready : Focus extended → Prop
  | .evaluate (.first _) _ | .evaluate (.second _) _ => False
  | _ => True

private theorem exposeEvaluation_ready (term : Source extended) (environment : SourceValue extended) (frames : List (Frame extended)) :
    Ready (exposeEvaluation term environment frames).focus := by
  induction term generalizing frames <;> first
    | exact trivial
    | apply_assumption

private theorem exposePacket_ready (packet : Packet extended) : Ready (exposePacket packet).focus := by
  cases packet with
  | mk focus frames =>
      cases focus with
      | evaluate term environment => exact exposeEvaluation_ready term environment frames
      | returned _ | invoke _ _ => exact trivial

private theorem encode_exposeEvaluation (term : Source extended) (environment : SourceValue extended) (frames : List (Frame extended)) :
    encodePacket (exposeEvaluation term environment frames) =
      encodePacket ⟨.evaluate term environment, frames⟩ := by
  induction term generalizing frames with
  | first term ih =>
      simp only [exposeEvaluation]
      rw [ih]
      simp [encodePacket, compileSource, contextCode, frameCode, contextStack, List.append_assoc]
  | second term ih =>
      simp only [exposeEvaluation]
      rw [ih]
      simp [encodePacket, compileSource, contextCode, frameCode, contextStack, List.append_assoc]
  | var _ | lam _ _ | app _ _ _ _ | pair _ _ _ _ | literal _ _ | conditional _ _ _ _ _ _ _ => rfl

private theorem encode_exposePacket (packet : Packet extended) :
    encodePacket (exposePacket packet) = encodePacket packet := by
  cases packet with
  | mk focus frames =>
      cases focus with
      | evaluate term environment => exact encode_exposeEvaluation term environment frames
      | returned _ | invoke _ _ => rfl

private def advanceReady : Packet extended → Option (Packet extended)
  | ⟨.evaluate (.var 0) environment, frames⟩ => some ⟨.returned (secondValue environment), frames⟩
  | ⟨.evaluate (.var (index + 1)) environment, frames⟩ =>
      some ⟨.evaluate (.var index) (firstValue environment), frames⟩
  | ⟨.evaluate (.literal enabled value) _, frames⟩ => some ⟨.returned (.literal enabled value), frames⟩
  | ⟨.evaluate (.conditional enabled condition whenTrue whenFalse) environment, frames⟩ =>
      some ⟨.evaluate condition environment, .condition enabled whenTrue whenFalse environment :: frames⟩
  | ⟨.evaluate (.lam body) environment, frames⟩ => some ⟨.returned (.closure body environment), frames⟩
  | ⟨.evaluate (.pair left right) environment, frames⟩ =>
      some ⟨.evaluate left environment, .pairLeft right environment :: frames⟩
  | ⟨.evaluate (.app operator argument) environment, frames⟩ =>
      some ⟨.evaluate operator environment, .appLeft argument environment :: frames⟩
  | ⟨.returned value, .pairLeft right environment :: frames⟩ =>
      some ⟨.evaluate right environment, .pairRight value :: frames⟩
  | ⟨.returned value, .pairRight left :: frames⟩ => some ⟨.returned (.pair left value), frames⟩
  | ⟨.returned value, .appLeft argument environment :: frames⟩ =>
      some ⟨.evaluate argument environment, .appRight value :: frames⟩
  | ⟨.returned value, .appRight function :: frames⟩ => some ⟨.invoke function value, frames⟩
  | ⟨.returned value, .first :: frames⟩ => some ⟨.returned (firstValue value), frames⟩
  | ⟨.returned value, .second :: frames⟩ => some ⟨.returned (secondValue value), frames⟩
  | ⟨.returned (.literal _ (.boolean selected)), .condition _ whenTrue whenFalse environment :: frames⟩ =>
      some ⟨.evaluate (if selected then whenTrue else whenFalse) environment, frames⟩
  | ⟨.invoke (.closure body environment) argument, frames⟩ =>
      some ⟨.evaluate body (.pair environment argument), frames⟩
  | ⟨.invoke function argument, frames⟩ => some ⟨.returned (.app (.pair function argument)), frames⟩
  | _ => none

private def advance (packet : Packet extended) : Option (Packet extended) := advanceReady (exposePacket packet)

private inductive Resumes : List (Frame extended) → SourceValue extended → SourceValue extended → Prop where
  | nil (value : SourceValue extended) : Resumes [] value value
  | condition {enabled : extended = true} {whenTrue whenFalse : Source extended}
      {environment result answer : SourceValue extended} {selected : Bool} {frames : List (Frame extended)}
      (selectedEval : Evaluation (if selected then whenTrue else whenFalse) environment result)
      (following : Resumes frames result answer) :
      Resumes (.condition enabled whenTrue whenFalse environment :: frames)
        (.literal enabled (.boolean selected)) answer
  | pairLeft {right : Source extended} {environment left rightValue answer : SourceValue extended} {frames : List (Frame extended)}
      (rightEval : Evaluation right environment rightValue)
      (following : Resumes frames (.pair left rightValue) answer) :
      Resumes (.pairLeft right environment :: frames) left answer
  | pairRight {left right answer : SourceValue extended} {frames : List (Frame extended)}
      (following : Resumes frames (.pair left right) answer) :
      Resumes (.pairRight left :: frames) right answer
  | appLeft {argument : Source extended} {environment function operand result answer : SourceValue extended}
      {frames : List (Frame extended)} (argumentEval : Evaluation argument environment operand)
      (invocation : Invocation function operand result) (following : Resumes frames result answer) :
      Resumes (.appLeft argument environment :: frames) function answer
  | appRight {function operand result answer : SourceValue extended} {frames : List (Frame extended)}
      (invocation : Invocation function operand result) (following : Resumes frames result answer) :
      Resumes (.appRight function :: frames) operand answer
  | first {value result answer : SourceValue extended} {frames : List (Frame extended)}
      (projection : First value result) (following : Resumes frames result answer) :
      Resumes (.first :: frames) value answer
  | second {value result answer : SourceValue extended} {frames : List (Frame extended)}
      (projection : Second value result) (following : Resumes frames result answer) :
      Resumes (.second :: frames) value answer

private def Resolves (packet : Packet extended) (answer : SourceValue extended) : Prop :=
  match packet.focus with
  | .evaluate term environment =>
      ∃ value, Evaluation term environment value ∧ Resumes packet.frames value answer
  | .returned value => Resumes packet.frames value answer
  | .invoke function argument =>
      ∃ value, Invocation function argument value ∧ Resumes packet.frames value answer

private theorem exposeEvaluation_resolves (term : Source extended) (environment : SourceValue extended)
    (frames : List (Frame extended)) (answer : SourceValue extended) :
    Resolves (exposeEvaluation term environment frames) answer ↔
      Resolves ⟨.evaluate term environment, frames⟩ answer := by
  induction term generalizing frames with
  | first term ih =>
      simp only [exposeEvaluation]
      rw [ih]
      constructor
      · rintro ⟨before, termEval, following⟩
        cases following with
        | first projection following => exact ⟨_, .first termEval projection, following⟩
      · rintro ⟨result, evaluation, following⟩
        cases evaluation with
        | first termEval projection => exact ⟨_, termEval, .first projection following⟩
  | second term ih =>
      simp only [exposeEvaluation]
      rw [ih]
      constructor
      · rintro ⟨before, termEval, following⟩
        cases following with
        | second projection following => exact ⟨_, .second termEval projection, following⟩
      · rintro ⟨result, evaluation, following⟩
        cases evaluation with
        | second termEval projection => exact ⟨_, termEval, .second projection following⟩
  | var _ | lam _ _ | app _ _ _ _ | pair _ _ _ _ | literal _ _ | conditional _ _ _ _ _ _ _ => exact Iff.rfl

private theorem exposePacket_resolves (packet : Packet extended) (answer : SourceValue extended) :
    Resolves (exposePacket packet) answer ↔ Resolves packet answer := by
  cases packet with
  | mk focus frames =>
      cases focus with
      | evaluate term environment => exact exposeEvaluation_resolves term environment frames answer
      | returned _ | invoke _ _ => exact Iff.rfl

private theorem advanceReady_resolves {before after : Packet extended}
    (execution : advanceReady before = some after) (answer : SourceValue extended)
    (following : Resolves after answer) : Resolves before answer := by
  cases before with
  | mk focus frames =>
      cases focus with
      | evaluate term environment =>
          cases term with
          | var index =>
              cases index with
              | zero =>
                  simp only [advanceReady, Option.some.injEq] at execution
                  subst after
                  exact ⟨_, .varZero (secondValue_sound environment), following⟩
              | succ index =>
                  simp only [advanceReady, Option.some.injEq] at execution
                  subst after
                  rcases following with ⟨value, evaluation, resumed⟩
                  exact ⟨value, .varSucc (firstValue_sound environment) evaluation, resumed⟩
          | literal enabled value =>
              simp only [advanceReady, Option.some.injEq] at execution
              subst after
              exact ⟨_, .literal enabled value environment, following⟩
          | conditional enabled condition whenTrue whenFalse =>
              simp only [advanceReady, Option.some.injEq] at execution
              subst after
              rcases following with ⟨value, evaluation, resumed⟩
              cases resumed with
              | condition selectedEval following =>
                  exact ⟨_, .conditional evaluation selectedEval, following⟩
          | lam body =>
              simp only [advanceReady, Option.some.injEq] at execution
              subst after
              exact ⟨_, .lam body environment, following⟩
          | pair left right =>
              simp only [advanceReady, Option.some.injEq] at execution
              subst after
              rcases following with ⟨value, evaluation, resumed⟩
              cases resumed with
              | pairLeft rightEval following => exact ⟨_, .pair evaluation rightEval, following⟩
          | app operator argument =>
              simp only [advanceReady, Option.some.injEq] at execution
              subst after
              rcases following with ⟨value, evaluation, resumed⟩
              cases resumed with
              | appLeft argumentEval invocation following =>
                  exact ⟨_, .app evaluation argumentEval invocation, following⟩
          | first _ | second _ => simp [advanceReady] at execution
      | returned value =>
          cases frames with
          | nil => simp [advanceReady] at execution
          | cons frame frames =>
              cases frame with
              | condition enabled whenTrue whenFalse environment =>
                  cases value with
                  | literal enabled literal =>
                      cases literal with
                      | boolean selected =>
                          simp only [advanceReady, Option.some.injEq] at execution
                          subst after
                          rcases following with ⟨value, evaluation, resumed⟩
                          exact .condition evaluation resumed
                      | integer _ | unit => simp [advanceReady] at execution
                  | unit | pair _ _ | closure _ _ | first _ | second _ | app _ =>
                      simp [advanceReady] at execution
              | pairLeft right environment =>
                  simp only [advanceReady, Option.some.injEq] at execution
                  subst after
                  rcases following with ⟨result, evaluation, resumed⟩
                  cases resumed with
                  | pairRight following => exact .pairLeft evaluation following
              | pairRight left =>
                  simp only [advanceReady, Option.some.injEq] at execution
                  subst after
                  exact .pairRight following
              | appLeft argument environment =>
                  simp only [advanceReady, Option.some.injEq] at execution
                  subst after
                  rcases following with ⟨result, evaluation, resumed⟩
                  cases resumed with
                  | appRight invocation following => exact .appLeft evaluation invocation following
              | appRight function =>
                  simp only [advanceReady, Option.some.injEq] at execution
                  subst after
                  rcases following with ⟨result, invocation, resumed⟩
                  exact .appRight invocation resumed
              | first =>
                  simp only [advanceReady, Option.some.injEq] at execution
                  subst after
                  exact .first (firstValue_sound value) following
              | second =>
                  simp only [advanceReady, Option.some.injEq] at execution
                  subst after
                  exact .second (secondValue_sound value) following
      | invoke function argument =>
          cases function with
          | closure body environment =>
              simp only [advanceReady, Option.some.injEq] at execution
              subst after
              rcases following with ⟨value, evaluation, resumed⟩
              exact ⟨value, .closure evaluation, resumed⟩
          | unit | literal _ _ | pair _ _ | first _ | second _ | app _ =>
              simp only [advanceReady, Option.some.injEq] at execution
              subst after
              exact ⟨_, .neutral _ argument trivial, following⟩

private theorem advance_resolves {before after : Packet extended}
    (execution : advance before = some after) (answer : SourceValue extended)
    (following : Resolves after answer) : Resolves before answer :=
  (exposePacket_resolves before answer).mp (advanceReady_resolves execution answer following)

private theorem advanceReady_encoded (packet : Packet extended) (ready : Ready packet.focus) :
    step .neutral (encodePacket packet) = (advanceReady packet).map encodePacket := by
  cases packet with
  | mk focus frames =>
      cases focus with
      | evaluate term environment =>
          cases term with
          | var index => cases index <;> cases environment <;> rfl
          | lam _ | literal _ _ => rfl
          | conditional _ _ _ _ =>
              simp [encodePacket, advanceReady, step, compileSource, contextCode, frameCode,
                contextStack, List.append_assoc]
          | pair _ _ | app _ _ =>
              simp [encodePacket, advanceReady, step, compileSource, contextCode, frameCode,
                contextStack, List.append_assoc]
          | first _ | second _ => exact False.elim ready
      | returned value =>
          cases frames with
          | nil => rfl
          | cons frame frames =>
              cases frame with
              | pairLeft _ _ | appLeft _ _ =>
                  simp [encodePacket, advanceReady, step, contextCode, frameCode, contextStack,
                    List.append_assoc]
              | condition _ _ _ _ =>
                  cases value with
                  | literal _ literal => cases literal <;> first | rfl | rename_i selected; cases selected <;> rfl
                  | unit | pair _ _ | closure _ _ | first _ | second _ | app _ => rfl
              | pairRight _ | appRight _ => rfl
              | first | second => cases value <;> rfl
      | invoke function argument => cases function <;> rfl

private theorem advance_encoded (packet : Packet extended) :
    step .neutral (encodePacket packet) = (advance packet).map encodePacket := by
  rw [← encode_exposePacket packet]
  exact advanceReady_encoded (exposePacket packet) (exposePacket_ready packet)

private theorem execution_contexts {before after : State} (execution : Steps .neutral before after) :
    ∀ (packet : Packet extended), encodePacket packet = before →
      ∃ residual, encodePacket residual = after ∧
        ∀ answer, Resolves residual answer → Resolves packet answer := by
  induction execution using Relation.ReflTransGen.head_induction_on with
  | refl =>
      intro packet encoded
      exact ⟨packet, encoded, fun _ resolved => resolved⟩
  | head transition _ ih =>
      intro packet encoded
      have executed := step_complete transition
      rw [← encoded, advance_encoded] at executed
      cases chosen : advance packet with
      | none => simp only [chosen, Option.map_none, reduceCtorEq] at executed
      | some next =>
          simp only [chosen, Option.map_some, Option.some.injEq] at executed
          obtain ⟨residual, finalEncoded, reconstruct⟩ := ih next executed
          exact ⟨residual, finalEncoded, fun answer resolved =>
            advance_resolves chosen answer (reconstruct answer resolved)⟩

private theorem advanceReady_none (packet : Packet false) (ready : Ready packet.focus)
    (stopped : advanceReady packet = none) : ∃ value, packet = ⟨.returned value, []⟩ := by
  cases packet with
  | mk focus frames =>
      cases focus with
      | evaluate term environment =>
          cases term with
          | var index => cases index <;> simp [advanceReady] at stopped
          | lam _ | app _ _ | pair _ _ => simp [advanceReady] at stopped
          | literal enabled _ | conditional enabled _ _ _ => cases enabled
          | first _ | second _ => exact False.elim ready
      | returned value =>
          cases frames with
          | nil => exact ⟨value, rfl⟩
          | cons frame frames =>
              cases frame with
              | condition enabled _ _ _ => cases enabled
              | pairLeft _ _ | pairRight _ | appLeft _ _ | appRight _ | first | second =>
                  simp [advanceReady] at stopped
      | invoke function argument => cases function <;> simp [advanceReady] at stopped

private theorem stopped_context (packet : Packet false) (stopped : step .neutral (encodePacket packet) = none) :
    ∃ value, encodePacket packet = ⟨encodeSourceValue value, [], []⟩ ∧ Resolves packet value := by
  rw [advance_encoded] at stopped
  cases chosen : advance packet with
  | none =>
      obtain ⟨value, finalPacket⟩ := advanceReady_none (exposePacket packet)
        (exposePacket_ready packet) chosen
      refine ⟨value, ?_, ?_⟩
      · rw [← encode_exposePacket packet, finalPacket]
        rfl
      · apply (exposePacket_resolves packet value).mp
        rw [finalPacket]
        exact .nil value
  | some next => simp [chosen] at stopped

/-- A stopped compiled computation is a completed source evaluation, rather
than an arbitrary missing instruction transition. No termination is assumed. -/
theorem compiled_terminal_shape {term : Expr} {environment : Value} {final : State}
    (execution : Steps .neutral ⟨encodeSourceValue environment, compileSource term, []⟩ final)
    (stopped : step .neutral final = none) :
    ∃ value, final = ⟨encodeSourceValue value, [], []⟩ ∧ Evaluation term environment value := by
  obtain ⟨packet, encoded, reconstruct⟩ := execution_contexts execution
    ⟨.evaluate term environment, []⟩ (by simp [encodePacket, contextCode, contextStack])
  obtain ⟨value, completed, resolved⟩ := stopped_context packet (by rw [encoded]; exact stopped)
  have initial := reconstruct value resolved
  rcases initial with ⟨result, evaluation, resumed⟩
  cases resumed
  exact ⟨value, encoded.symm.trans completed, evaluation⟩

/-- Construct the semantic value at the actual native endpoint. -/
theorem execution_complete {term : Source extended} {environment : SourceValue extended} {native : NativeValue}
    (execution : Steps .neutral ⟨encodeSourceValue environment, compileSource term, []⟩ ⟨native, [], []⟩) :
    ∃ value, Evaluation term environment value ∧ encodeSourceValue value = native := by
  obtain ⟨⟨focus, frames⟩, encoded, reconstruct⟩ := execution_contexts execution
    ⟨.evaluate term environment, []⟩ (by simp [encodePacket, contextCode, contextStack])
  have emptyCode := congrArg State.code encoded
  cases focus with
  | evaluate term environment =>
      have empty : compileSource term = [] := (List.append_eq_nil_iff.mp emptyCode).1
      exact False.elim (compile_nonempty term empty)
  | invoke function argument => simp [encodePacket] at emptyCode
  | returned value =>
      have emptyFrames : frames = [] := (contextCode_nil_iff frames).mp emptyCode
      subst frames
      have initial := reconstruct value (Resumes.nil value)
      rcases initial with ⟨result, evaluation, resumed⟩
      cases resumed
      exact ⟨value, evaluation, congrArg State.register encoded⟩

theorem evaluation_iff_execution (term : Source extended) (environment value : SourceValue extended) :
    Evaluation term environment value ↔
      Steps .neutral ⟨encodeSourceValue environment, compileSource term, []⟩ ⟨encodeSourceValue value, [], []⟩ := by
  constructor
  · exact Evaluation.execution
  · intro execution
    obtain ⟨result, evaluation, represented⟩ := execution_complete execution
    have same := encodeValue_injective represented
    subst result
    exact evaluation

theorem compiled_progress {term : Expr} {environment : Value} {state : State}
    (execution : Steps .neutral ⟨encodeSourceValue environment, compileSource term, []⟩ state) :
    (∃ next, Transition .neutral state next) ∨
      (∃ value, state = ⟨encodeSourceValue value, [], []⟩ ∧ Evaluation term environment value) := by
  cases selected : step .neutral state with
  | none => exact Or.inr (compiled_terminal_shape execution selected)
  | some next => exact Or.inl ⟨next, step_sound selected⟩

inductive CombinatoryState (extended : Bool := false) where
  | question (term : Source extended) (environment : SourceValue extended)
  | answer (value : SourceValue extended)
  deriving DecidableEq, Repr

/-- The question/answer reductions of the paper, p. 187. The completed
premises are independently judged by `Evaluation`; the equivalence below
joins that completed form to these reductions and their transitive closure. -/
inductive CombinatoryReduction : (CombinatoryState extended) → (CombinatoryState extended) → Prop where
  | varZero {environment value : SourceValue extended} (projection : Second environment value) :
      CombinatoryReduction (.question (.var 0) environment) (.answer value)
  | varSucc {index : Nat} {environment before : SourceValue extended} (projection : First environment before) :
      CombinatoryReduction (.question (.var (index + 1)) environment) (.question (.var index) before)
  | lam (body : Source extended) (environment : SourceValue extended) :
      CombinatoryReduction (.question (.lam body) environment) (.answer (.closure body environment))
  | pair {left right : Source extended} {environment first second : SourceValue extended}
      (leftEval : Evaluation left environment first) (rightEval : Evaluation right environment second) :
      CombinatoryReduction (.question (.pair left right) environment) (.answer (.pair first second))
  | appClosure {operator argument body : Source extended} {environment captured operand : SourceValue extended}
      (operatorEval : Evaluation operator environment (.closure body captured))
      (argumentEval : Evaluation argument environment operand) :
      CombinatoryReduction (.question (.app operator argument) environment)
        (.question body (.pair captured operand))
  | appNeutral {operator argument : Source extended} {environment function operand : SourceValue extended}
      (operatorEval : Evaluation operator environment function)
      (argumentEval : Evaluation argument environment operand) (inactive : NotClosure function) :
      CombinatoryReduction (.question (.app operator argument) environment)
        (.answer (.app (.pair function operand)))
  | first {term : Source extended} {environment before value : SourceValue extended}
      (termEval : Evaluation term environment before) (projection : First before value) :
      CombinatoryReduction (.question (.first term) environment) (.answer value)
  | second {term : Source extended} {environment before value : SourceValue extended}
      (termEval : Evaluation term environment before) (projection : Second before value) :
      CombinatoryReduction (.question (.second term) environment) (.answer value)
  | literal (enabled : extended = true) (value : Literal) (environment : SourceValue extended) :
      CombinatoryReduction (.question (.literal enabled value) environment) (.answer (.literal enabled value))
  | conditional {enabled : extended = true} {condition whenTrue whenFalse : Source extended}
      {environment : SourceValue extended} {selected : Bool}
      (conditionEval : Evaluation condition environment (.literal enabled (.boolean selected))) :
      CombinatoryReduction (.question (.conditional enabled condition whenTrue whenFalse) environment)
        (.question (if selected then whenTrue else whenFalse) environment)

abbrev CombinatorySteps := Relation.ReflTransGen (CombinatoryReduction (extended := extended))

private def CombinatoryResult (state : (CombinatoryState extended)) (value : SourceValue extended) : Prop :=
  match state with
  | .question term environment => Evaluation term environment value
  | .answer before => before = value

private theorem combinatory_result_backward {before after : (CombinatoryState extended)}
    (reduction : CombinatoryReduction before after) (value : SourceValue extended)
    (following : CombinatoryResult after value) : CombinatoryResult before value := by
  cases reduction with
  | literal enabled value environment => cases following; exact .literal enabled value environment
  | conditional conditionEval => exact .conditional conditionEval following
  | varZero projection => cases following; exact .varZero projection
  | varSucc projection => exact .varSucc projection following
  | lam body environment => cases following; exact .lam body environment
  | pair leftEval rightEval => cases following; exact .pair leftEval rightEval
  | appClosure operatorEval argumentEval => exact .app operatorEval argumentEval (.closure following)
  | appNeutral operatorEval argumentEval inactive =>
      cases following
      exact .app operatorEval argumentEval (.neutral _ _ inactive)
  | first termEval projection => cases following; exact .first termEval projection
  | second termEval projection => cases following; exact .second termEval projection

private theorem combinatory_steps_backward {before after : (CombinatoryState extended)}
    (execution : CombinatorySteps before after) :
    ∀ value, CombinatoryResult after value → CombinatoryResult before value := by
  induction execution using Relation.ReflTransGen.head_induction_on with
  | refl => exact fun _ following => following
  | head reduction _ ih => exact fun value following =>
      combinatory_result_backward reduction value (ih value following)

theorem Evaluation.combinatory {term : Source extended} {environment value : SourceValue extended}
    (evaluation : Evaluation term environment value) :
    CombinatorySteps (.question term environment) (.answer value) := by
  induction evaluation using Evaluation.rec
      (motive_2 := fun function operand value _ => ∀ (operator argument : Source extended) (environment : SourceValue extended),
        Evaluation operator environment function → Evaluation argument environment operand →
          CombinatorySteps (.question (.app operator argument) environment) (.answer value)) with
  | varZero projection => exact .single (.varZero projection)
  | varSucc projection _ ih => exact .head (.varSucc projection) ih
  | lam body environment => exact .single (.lam body environment)
  | pair leftEval rightEval _ _ => exact .single (.pair leftEval rightEval)
  | app operatorEval argumentEval _ _ _ invocationIH =>
      exact invocationIH _ _ _ operatorEval argumentEval
  | first termEval projection _ => exact .single (.first termEval projection)
  | second termEval projection _ => exact .single (.second termEval projection)
  | closure _ bodyIH =>
      rename_i operator argument environment operatorEval argumentEval
      exact .head (.appClosure operatorEval argumentEval) bodyIH
  | neutral function operand inactive =>
      rename_i operator argument environment operatorEval argumentEval
      exact .single (.appNeutral operatorEval argumentEval inactive)

  | literal enabled value environment => exact .single (.literal enabled value environment)
  | conditional conditionEval _ _ selectedIH => exact .head (.conditional conditionEval) selectedIH

theorem combinatory_iff_evaluation (term : Source extended) (environment value : SourceValue extended) :
    CombinatorySteps (.question term environment) (.answer value) ↔ Evaluation term environment value :=
  ⟨fun execution => combinatory_steps_backward execution value rfl, Evaluation.combinatory⟩

/-- Proposition 3.1, with constructed source-body/code-body representation
and both terminal fields retained. This is the augmented Table 5 profile. -/
theorem combinatory_iff_execution (term : Source extended) (environment value : SourceValue extended) :
    CombinatorySteps (.question term environment) (.answer value) ↔
      Steps .neutral ⟨encodeSourceValue environment, compileSource term, []⟩ ⟨encodeSourceValue value, [], []⟩ :=
  (combinatory_iff_evaluation term environment value).trans (evaluation_iff_execution term environment value)

/-! ## The existing deterministic and finite-run interfaces -/

/-- A source question retains both the expression and its categorical
environment. The compiled loader does not erase captured environments. -/
def sourceCore (extended : Bool) (profile : Profile) : MachineCore (Source extended × SourceValue extended) where
  State := State
  load question := ⟨encodeSourceValue question.2, compileSource question.1, []⟩
  step := step profile

abbrev core (profile : Profile) := sourceCore false profile

/-- Raw code with an empty instruction stream but a nonempty stack is
stopped, not a completed source answer. This observer does not certify that
arbitrary code was compiled. -/
def answer : State → Option NativeValue
  | ⟨value, [], []⟩ => some value
  | _ => none

theorem answer_iff (state : State) (value : NativeValue) :
    answer state = some value ↔ state = ⟨value, [], []⟩ := by
  rcases state with ⟨register, code, stack⟩
  cases code <;> cases stack <;> simp [answer]

theorem answer_final (profile : Profile) (state : State) (value : NativeValue)
    (observed : answer state = some value) : step profile state = none := by
  rw [(answer_iff state value).mp observed]
  rfl

def sourceAnswerCore (extended : Bool) (profile : Profile) :
    AnswerMachineCore (Source extended × SourceValue extended) NativeValue where
  toMachineCore := sourceCore extended profile
  answer := answer
  answer_final := answer_final profile

abbrev answerCore (profile : Profile) := sourceAnswerCore false profile

theorem core_step_iff (profile : Profile) (state next : State) :
    (core profile).StepRel state next ↔ Transition profile state next :=
  step_iff profile state next

theorem core_steps_iff (profile : Profile) (state final : State) :
    (core profile).Steps state final ↔ Steps profile state final := by
  constructor
  · exact Relation.ReflTransGen.mono (fun left right edge =>
      (core_step_iff profile left right).mp edge) state final
  · exact Relation.ReflTransGen.mono (fun left right edge =>
      (core_step_iff profile left right).mpr edge) state final

theorem sourceCore_steps_iff (profile : Profile) (state final : State) :
    (sourceCore extended profile).Steps state final ↔ Steps profile state final := by
  constructor
  · exact Relation.ReflTransGen.mono (fun left right edge =>
      (step_iff profile left right).mp edge) state final
  · exact Relation.ReflTransGen.mono (fun left right edge =>
      (step_iff profile left right).mpr edge) state final

theorem sourceProduces_iff_evaluation (term : Source extended) (environment : SourceValue extended) (value : NativeValue) :
    (sourceAnswerCore extended .neutral).Produces (term, environment) value ↔
      ∃ source, Evaluation term environment source ∧ encodeSourceValue source = value := by
  constructor
  · rintro ⟨final, reached, observed⟩
    have ending := (answer_iff final value).mp observed
    rw [ending] at reached
    exact execution_complete ((sourceCore_steps_iff .neutral _ _).mp reached)
  · rintro ⟨source, evaluation, represented⟩
    subst value
    exact ⟨⟨encodeSourceValue source, [], []⟩,
      (sourceCore_steps_iff .neutral _ _).mpr evaluation.execution, rfl⟩

theorem produces_iff_evaluation (term : Expr) (environment : Value) (value : NativeValue) :
    (answerCore .neutral).Produces (term, environment) value ↔
      ∃ source, Evaluation term environment source ∧ encodeSourceValue source = value :=
  sourceProduces_iff_evaluation term environment value

/-- The completed source result is unique because the actual executable
machine is deterministic; the representation map is proved injective. -/
theorem Evaluation.unique {term : Source extended} {environment first second : SourceValue extended}
    (one : Evaluation term environment first) (two : Evaluation term environment second) : first = second := by
  apply encodeValue_injective
  exact (sourceAnswerCore extended .neutral).produces_unique
    ((sourceProduces_iff_evaluation term environment (encodeSourceValue first)).mpr ⟨first, one, rfl⟩)
    ((sourceProduces_iff_evaluation term environment (encodeSourceValue second)).mpr ⟨second, two, rfl⟩)

open Mettapedia.GSLT.Distinction.ProductiveBlocks

abbrev Occurrence := ProductiveCoreAdapters.Occurrence State

/-- Each computational occurrence records its actual source and destination
machine states. It is not an external effect or a source beta-step count. -/
def machine (profile : Profile) : Machine State Occurrence NativeValue Empty :=
  ProductiveCoreAdapters.answerMachine (answerCore profile)

theorem evaluation_iff_finished (term : Source extended) (environment value : SourceValue extended) :
    Evaluation term environment value ↔ ∃ budget events,
      (machine .neutral).run budget ⟨encodeSourceValue environment, compileSource term, []⟩ =
        (events, .finished (encodeSourceValue value)) := by
  change Evaluation term environment value ↔ ∃ budget events,
    (ProductiveCoreAdapters.answerMachine (sourceAnswerCore extended .neutral)).run budget
      ((sourceAnswerCore extended .neutral).load (term, environment)) = (events, .finished (encodeSourceValue value))
  rw [← ProductiveCoreAdapters.produces_iff_finished (sourceAnswerCore extended .neutral) (term, environment) (encodeSourceValue value),
    sourceProduces_iff_evaluation]
  constructor
  · intro evaluation; exact ⟨value, evaluation, rfl⟩
  · rintro ⟨source, evaluation, represented⟩
    exact encodeValue_injective represented ▸ evaluation

/-- CAM instructions do not acquire the common runner's silent label. A
divergent source program may keep executing computational instructions. -/
theorem machine_no_administration (profile : Profile) (state next : State) :
    (machine profile).step state ≠ some (.silent next) :=
  ProductiveCoreAdapters.answer_no_administration (answerCore profile) state next

/-- Exact resumption retains register, instruction suffix and full stack.
The trace uses actual Table 1/Table 5 transitions, through their checked
executable correspondence. -/
theorem trace_resume (profile : Profile) {state residual : State} {events : List Occurrence}
    (trace : ProductiveCoreAdapters.Trace (core profile) state events residual) (second : Nat) :
    (machine profile).run (events.length + second) state =
      (events ++ ((machine profile).run second residual).1, ((machine profile).run second residual).2) :=
  ProductiveCoreAdapters.trace_answer_resume (answerCore profile) trace second

theorem computational_account (profile : Profile) (price : State → Nat) (budget : Nat) (state : State) :
    (machine profile).spent (ProductiveCoreAdapters.computationalPrice (core profile) price) budget state =
      ProductiveCoreAdapters.charge price ((machine profile).run budget state).1 :=
  ProductiveCoreAdapters.answer_spent_is_charge (answerCore profile) price budget state

theorem computational_account_resume (profile : Profile) {state residual : State}
    {events : List Occurrence} (trace : ProductiveCoreAdapters.Trace (core profile) state events residual)
    (price : State → Nat) (second : Nat) :
    (machine profile).spent (ProductiveCoreAdapters.computationalPrice (core profile) price)
      (events.length + second) state = ProductiveCoreAdapters.charge price events +
      (machine profile).spent (ProductiveCoreAdapters.computationalPrice (core profile) price) second residual :=
  ProductiveCoreAdapters.trace_answer_account_resume (answerCore profile) trace price second

/-- The shared occurrence runner records this exact branch transition,
including the complete selected and unselected source code in its saved
configuration. Branch selection contributes one computational occurrence. -/
theorem branch_trace (profile : Profile) (selected : Bool) (saved : NativeValue)
    (whenTrue whenFalse code : Code) (stack : List NativeValue) :
    ProductiveCoreAdapters.Trace (core profile)
      ⟨.literal (.boolean selected), .branch whenTrue whenFalse :: code, saved :: stack⟩
      [(⟨.literal (.boolean selected), .branch whenTrue whenFalse :: code, saved :: stack⟩,
        ⟨saved, (if selected then whenTrue else whenFalse) ++ code, stack⟩)]
      ⟨saved, (if selected then whenTrue else whenFalse) ++ code, stack⟩ :=
  .cons (branch_step profile selected saved whenTrue whenFalse code stack) (.empty _)

theorem branch_resume (profile : Profile) (selected : Bool) (saved : NativeValue)
    (whenTrue whenFalse code : Code) (stack : List NativeValue) (second : Nat) :
    (machine profile).run (1 + second)
        ⟨.literal (.boolean selected), .branch whenTrue whenFalse :: code, saved :: stack⟩ =
      ([(⟨.literal (.boolean selected), .branch whenTrue whenFalse :: code, saved :: stack⟩,
          ⟨saved, (if selected then whenTrue else whenFalse) ++ code, stack⟩)] ++
        ((machine profile).run second
          ⟨saved, (if selected then whenTrue else whenFalse) ++ code, stack⟩).1,
        ((machine profile).run second
          ⟨saved, (if selected then whenTrue else whenFalse) ++ code, stack⟩).2) :=
  trace_resume profile (branch_trace profile selected saved whenTrue whenFalse code stack) second

theorem branch_account_resume (profile : Profile) (selected : Bool) (saved : NativeValue)
    (whenTrue whenFalse code : Code) (stack : List NativeValue) (price : State → Nat) (second : Nat) :
    (machine profile).spent (ProductiveCoreAdapters.computationalPrice (core profile) price)
        (1 + second)
        ⟨.literal (.boolean selected), .branch whenTrue whenFalse :: code, saved :: stack⟩ =
      price ⟨.literal (.boolean selected), .branch whenTrue whenFalse :: code, saved :: stack⟩ +
        (machine profile).spent (ProductiveCoreAdapters.computationalPrice (core profile) price)
          second ⟨saved, (if selected then whenTrue else whenFalse) ++ code, stack⟩ := by
  exact computational_account_resume profile
    (branch_trace profile selected saved whenTrue whenFalse code stack) price second

/-- Completed-answer observation takes one runner boundary after the last
computational instruction. These are semantic work accounts, not host CPU
costs or compiler guarantees. -/
theorem instruction_and_completion_account (profile : Profile) (budget : Nat) (state : State) :
    (machine profile).spent (fun _ => 1) budget state = ((machine profile).run budget state).1.length +
      (match ((machine profile).run budget state).2 with | .finished _ => 1 | _ => 0) := by
  have shared := ProductiveCoreAdapters.answer_instruction_count (answerCore profile) budget state
  simp only [machine, answerCore, sourceAnswerCore, sourceCore] at shared ⊢
  convert shared using 1
  congr 1
  cases ending : ((machine profile).run budget state).2 <;>
    simp only [machine, answerCore, sourceAnswerCore, sourceCore] at ending <;> simp only [ending]

theorem occurrences_le_budget (profile : Profile) (budget : Nat) (state : State) :
    ((machine profile).run budget state).1.length ≤ budget :=
  ProductiveCoreAdapters.answer_occurrences_le_budget (answerCore profile) budget state

/-! ## Scoped lambda readback and weak call-by-value

The syntax adapter below presents the existing source grammar to the shared
binding algebra. New binders are fixed by its lifted substitutions. Section 3
of Cousineau, Curien and Mauny (1987), pp. 189--191, uses closed readbacks and
weak left-to-right evaluation; closure bodies are not evaluated on creation.
The same signature is indexed by the existing source-extension flag. At
`true`, literal normals and selected Boolean branches extend the readback,
substitution and completed-execution theorems; at `false`, the historical
five-head binding signature is unchanged.
-/

namespace Lambda

open Mettapedia.OSLF.Binding

inductive Head (extended : Bool) where
  | lam | app | pair | first | second
  | literal (enabled : extended = true) (value : Literal)
  | conditional (enabled : extended = true)
  deriving DecidableEq

abbrev signature (extended : Bool) : Signature where
  Srt := Unit
  Op := fun _ => Head extended
  arity := fun head => match head with
    | .lam => [([()], ())]
    | .app | .pair => [([], ()), ([], ())]
    | .first | .second => [([], ())]
    | .literal _ _ => []
    | .conditional _ => [([], ()), ([], ()), ([], ())]

abbrev Scoped (context : List Unit) (extended : Bool := false) := Term (signature extended) context ()
abbrev Closed (extended : Bool := false) := Scoped [] extended

def lam {Γ : List Unit} (body : Scoped (extended := extended) (() :: Γ)) : Scoped (extended := extended) Γ :=
  .op .lam (.cons body .nil)
def app {Γ : List Unit} (operator argument : Scoped (extended := extended) Γ) : Scoped (extended := extended) Γ :=
  .op .app (.cons operator (.cons argument .nil))
def pair {Γ : List Unit} (left right : Scoped (extended := extended) Γ) : Scoped (extended := extended) Γ :=
  .op .pair (.cons left (.cons right .nil))
def first {Γ : List Unit} (term : Scoped (extended := extended) Γ) : Scoped (extended := extended) Γ :=
  .op .first (.cons term .nil)
def second {Γ : List Unit} (term : Scoped (extended := extended) Γ) : Scoped (extended := extended) Γ :=
  .op .second (.cons term .nil)

def literal {Γ : List Unit} (enabled : extended = true) (value : Literal) : Scoped Γ extended :=
  .op (.literal enabled value) .nil
def conditional {Γ : List Unit} (enabled : extended = true)
    (condition whenTrue whenFalse : Scoped Γ extended) : Scoped Γ extended :=
  .op (.conditional enabled) (.cons condition (.cons whenTrue (.cons whenFalse .nil)))

def position : {Γ : List Unit} → {sort : Unit} → Var Γ sort → Nat
  | _, _, .zero => 0
  | _, _, .succ variable_ => position variable_ + 1

def slot? : (Γ : List Unit) → Nat → Option (Var Γ ())
  | [], _ => none
  | () :: _, 0 => some .zero
  | () :: Γ, index + 1 => (slot? Γ index).map .succ

mutual
def erase : {Γ : List Unit} → {sort : Unit} → Term (signature extended) Γ sort → Source extended
  | _, _, .var variable_ => .var (position variable_)
  | _, _, .op head arguments => match head with
      | .lam => .lam (eraseAt arguments 0)
      | .app => .app (eraseAt arguments 0) (eraseAt arguments 1)
      | .pair => .pair (eraseAt arguments 0) (eraseAt arguments 1)
      | .first => .first (eraseAt arguments 0)
      | .second => .second (eraseAt arguments 0)
      | .literal enabled value => .literal enabled value
      | .conditional enabled => .conditional enabled (eraseAt arguments 0) (eraseAt arguments 1) (eraseAt arguments 2)
def eraseAt : {arity : List (List Unit × Unit)} → {Γ : List Unit} →
    (arguments : Args (signature extended) arity Γ) → Fin arity.length → Source extended
  | _, _, .cons head _, ⟨0, _⟩ => erase head
  | _, _, .cons _ tail, ⟨index + 1, bound⟩ => eraseAt tail ⟨index, Nat.lt_of_succ_lt_succ bound⟩
end

@[simp] theorem eraseAt_zero {Γ : List Unit} {binders : List Unit} {sort : Unit}
    {arity : List (List Unit × Unit)} (head : Term (signature extended) (binders ++ Γ) sort)
    (tail : Args (signature extended) arity Γ) : eraseAt (.cons head tail) 0 = erase head := rfl

@[simp] theorem eraseAt_succ {Γ : List Unit} {binders : List Unit} {sort : Unit}
    {arity : List (List Unit × Unit)} (head : Term (signature extended) (binders ++ Γ) sort)
    (tail : Args (signature extended) arity Γ) (index : Fin arity.length) :
    eraseAt (.cons head tail) index.succ = eraseAt tail index := rfl

@[simp] theorem erase_lam {Γ : List Unit} (body : Scoped (extended := extended) (() :: Γ)) : erase (lam body) = .lam (erase body) := rfl
@[simp] theorem erase_app {Γ : List Unit} (operator argument : Scoped (extended := extended) Γ) :
    erase (app operator argument) = .app (erase operator) (erase argument) := rfl
@[simp] theorem erase_pair {Γ : List Unit} (left right : Scoped (extended := extended) Γ) :
    erase (pair left right) = .pair (erase left) (erase right) := rfl
@[simp] theorem erase_first {Γ : List Unit} (term : Scoped (extended := extended) Γ) : erase (first term) = .first (erase term) := rfl
@[simp] theorem erase_second {Γ : List Unit} (term : Scoped (extended := extended) Γ) : erase (second term) = .second (erase term) := rfl

@[simp] theorem erase_literal {Γ : List Unit} (enabled : extended = true) (value : Literal) :
    erase (literal (Γ := Γ) enabled value) = .literal enabled value := rfl
@[simp] theorem erase_conditional {Γ : List Unit} (enabled : extended = true)
    (condition whenTrue whenFalse : Scoped Γ extended) :
    erase (conditional enabled condition whenTrue whenFalse) =
      .conditional enabled (erase condition) (erase whenTrue) (erase whenFalse) := rfl

def represent : (Γ : List Unit) → Source extended → Option (Scoped (extended := extended) Γ)
  | Γ, .var index => (slot? Γ index).map .var
  | Γ, .lam body => (represent (() :: Γ) body).map lam
  | Γ, .app operator argument => do
      let operator ← represent Γ operator
      let argument ← represent Γ argument
      pure (app operator argument)
  | Γ, .pair left right => do
      let left ← represent Γ left
      let right ← represent Γ right
      pure (pair left right)
  | Γ, .first term => (represent Γ term).map first
  | Γ, .second term => (represent Γ term).map second
  | _, .literal enabled value => some (literal enabled value)
  | Γ, .conditional enabled condition whenTrue whenFalse => do
      let condition ← represent Γ condition
      let whenTrue ← represent Γ whenTrue
      let whenFalse ← represent Γ whenFalse
      pure (conditional enabled condition whenTrue whenFalse)

@[simp] theorem slot?_position {Γ : List Unit} (variable_ : Var Γ ()) :
    slot? Γ (position variable_) = some variable_ := by
  induction Γ with
  | nil => cases variable_
  | cons sort Γ ih =>
      cases sort
      cases variable_ with
      | zero => rfl
      | succ variable_ => simp only [position, slot?, ih variable_, Option.map_some]

theorem position_slot? {Γ : List Unit} {index : Nat} {variable_ : Var Γ ()}
    (represented : slot? Γ index = some variable_) : position variable_ = index := by
  induction Γ generalizing index with
  | nil => simp [slot?] at represented
  | cons sort Γ ih =>
      cases sort
      cases index with
      | zero => simp only [slot?, Option.some.injEq] at represented; subst variable_; rfl
      | succ index =>
          cases previous : slot? Γ index <;> simp [slot?, previous] at represented
          subst variable_
          simpa only [position] using congrArg Nat.succ (ih previous)

@[simp] theorem represent_erase : ∀ {Γ : List Unit} (term : Scoped (extended := extended) Γ),
    represent Γ (erase term) = some term
  | Γ, .var variable_ => by
      change (slot? Γ (position variable_)).map (Term.var (S := (signature extended))) = some (.var variable_)
      rw [slot?_position]
      rfl
  | Γ, .op .lam (.cons body .nil) => by
      change (represent (() :: Γ) (erase body)).map lam = some (lam body)
      rw [show represent (() :: Γ) (erase body) = some body from represent_erase body]
      rfl
  | Γ, .op .app (.cons operator (.cons argument .nil)) => by
      change ((represent Γ (erase operator)).bind fun operator =>
        (represent Γ (erase argument)).bind fun argument => some (app operator argument)) = _
      rw [show represent Γ (erase operator) = some operator from represent_erase operator,
          show represent Γ (erase argument) = some argument from represent_erase argument]
      rfl
  | Γ, .op .pair (.cons left (.cons right .nil)) => by
      change ((represent Γ (erase left)).bind fun left =>
        (represent Γ (erase right)).bind fun right => some (pair left right)) = _
      rw [show represent Γ (erase left) = some left from represent_erase left,
          show represent Γ (erase right) = some right from represent_erase right]
      rfl
  | Γ, .op .first (.cons term .nil) => by
      change (represent Γ (erase term)).map first = some (first term)
      rw [show represent Γ (erase term) = some term from represent_erase term]
      rfl
  | Γ, .op .second (.cons term .nil) => by
      change (represent Γ (erase term)).map second = some (second term)
      rw [show represent Γ (erase term) = some term from represent_erase term]
      rfl
  | Γ, .op (.literal enabled value) .nil => rfl
  | Γ, .op (.conditional enabled) (.cons condition (.cons whenTrue (.cons whenFalse .nil))) => by
      change ((represent Γ (erase condition)).bind fun condition =>
        (represent Γ (erase whenTrue)).bind fun whenTrue =>
          (represent Γ (erase whenFalse)).bind fun whenFalse =>
            some (conditional enabled condition whenTrue whenFalse)) = _
      rw [show represent Γ (erase condition) = some condition from represent_erase condition,
        show represent Γ (erase whenTrue) = some whenTrue from represent_erase whenTrue,
        show represent Γ (erase whenFalse) = some whenFalse from represent_erase whenFalse]
      rfl
termination_by _ term => termSize term
decreasing_by all_goals simp only [termSize, argsSize]; omega

theorem erase_represent {Γ : List Unit} {expression : Source extended} {term : Scoped (extended := extended) Γ}
    (represented : represent Γ expression = some term) : erase term = expression := by
  induction expression generalizing Γ term with
  | var index =>
      obtain ⟨variable_, found, same⟩ := Option.map_eq_some_iff.mp (by simpa only [represent] using represented)
      subst term
      simpa only [erase, eraseAt] using congrArg Source.var (position_slot? found)
  | lam body ih =>
      obtain ⟨bodyTerm, found, same⟩ := Option.map_eq_some_iff.mp (by simpa only [represent] using represented)
      subst term
      simpa only [erase_lam] using congrArg Source.lam (ih found)
  | app operator argument ihO ihA =>
      cases operatorFound : represent Γ operator with
      | none => simp [represent, operatorFound] at represented
      | some operatorTerm =>
          cases argumentFound : represent Γ argument with
          | none => simp [represent, operatorFound, argumentFound] at represented
          | some argumentTerm =>
              simp [represent, operatorFound, argumentFound] at represented
              subst term
              simp only [erase_app, ihO operatorFound, ihA argumentFound]
  | pair left right ihL ihR =>
      cases leftFound : represent Γ left with
      | none => simp [represent, leftFound] at represented
      | some leftTerm =>
          cases rightFound : represent Γ right with
          | none => simp [represent, leftFound, rightFound] at represented
          | some rightTerm =>
              simp [represent, leftFound, rightFound] at represented
              subst term
              simp only [erase_pair, ihL leftFound, ihR rightFound]
  | first expression ih =>
      obtain ⟨child, found, same⟩ := Option.map_eq_some_iff.mp (by simpa only [represent] using represented)
      subst term
      simpa only [erase_first] using congrArg Source.first (ih found)
  | second expression ih =>
      obtain ⟨child, found, same⟩ := Option.map_eq_some_iff.mp (by simpa only [represent] using represented)
      subst term
      simpa only [erase_second] using congrArg Source.second (ih found)

  | literal enabled value =>
      simp only [represent, Option.some.injEq] at represented
      subst term
      rfl
  | conditional enabled condition whenTrue whenFalse ihC ihT ihF =>
      cases hc : represent Γ condition with
      | none => simp [represent, hc] at represented
      | some c =>
          cases ht : represent Γ whenTrue with
          | none => simp [represent, hc, ht] at represented
          | some t =>
              cases hf : represent Γ whenFalse with
              | none => simp [represent, hc, ht, hf] at represented
              | some f =>
                  simp [represent, hc, ht, hf] at represented
                  subst term
                  simp only [erase_conditional, ihC hc, ihT ht, ihF hf]

theorem erase_injective {Γ : List Unit} : Function.Injective (@erase extended Γ ()) := by
  intro left right same
  have represented := congrArg (represent Γ) same
  simpa only [represent_erase, Option.some.injEq] using represented

abbrev Context (values : List (Closed extended)) : List Unit := List.replicate values.length ()

private def scopedCases {Γ : List Unit} {P : Scoped (extended := extended) Γ → Sort _}
    (varCase : ∀ variable_, P (.var variable_))
    (lamCase : ∀ body, P (lam body))
    (appCase : ∀ operator argument, P (app operator argument))
    (pairCase : ∀ left right, P (pair left right))
    (firstCase : ∀ term, P (first term))
    (secondCase : ∀ term, P (second term))
    (literalCase : ∀ enabled value, P (literal enabled value))
    (conditionalCase : ∀ enabled condition whenTrue whenFalse,
      P (conditional enabled condition whenTrue whenFalse)) : (term : Scoped (extended := extended) Γ) → P term
  | .var variable_ => varCase variable_
  | .op .lam (.cons body .nil) => lamCase body
  | .op .app (.cons operator (.cons argument .nil)) => appCase operator argument
  | .op .pair (.cons left (.cons right .nil)) => pairCase left right
  | .op .first (.cons term .nil) => firstCase term
  | .op .second (.cons term .nil) => secondCase term
  | .op (.literal enabled value) .nil => literalCase enabled value
  | .op (.conditional enabled) (.cons condition (.cons whenTrue (.cons whenFalse .nil))) =>
      conditionalCase enabled condition whenTrue whenFalse

@[simp] theorem bind_lam {Γ Δ : List Unit} (sigma : Sub (signature extended) Γ Δ) (body : Scoped (extended := extended) (() :: Γ)) :
    bind sigma (lam body) = lam (bind (liftSub sigma [()]) body) := rfl
@[simp] theorem bind_app {Γ Δ : List Unit} (sigma : Sub (signature extended) Γ Δ) (operator argument : Scoped (extended := extended) Γ) :
    bind sigma (app operator argument) = app (bind sigma operator) (bind sigma argument) := rfl
@[simp] theorem bind_pair {Γ Δ : List Unit} (sigma : Sub (signature extended) Γ Δ) (left right : Scoped (extended := extended) Γ) :
    bind sigma (pair left right) = pair (bind sigma left) (bind sigma right) := rfl
@[simp] theorem bind_first {Γ Δ : List Unit} (sigma : Sub (signature extended) Γ Δ) (term : Scoped (extended := extended) Γ) :
    bind sigma (first term) = first (bind sigma term) := rfl
@[simp] theorem bind_second {Γ Δ : List Unit} (sigma : Sub (signature extended) Γ Δ) (term : Scoped (extended := extended) Γ) :
    bind sigma (second term) = second (bind sigma term) := rfl

@[simp] theorem bind_literal {Γ Δ : List Unit} (sigma : Sub (signature extended) Γ Δ)
    (enabled : extended = true) (value : Literal) :
    bind sigma (literal enabled value) = literal enabled value := rfl
@[simp] theorem bind_conditional {Γ Δ : List Unit} (sigma : Sub (signature extended) Γ Δ)
    (enabled : extended = true) (condition whenTrue whenFalse : Scoped Γ extended) :
    bind sigma (conditional enabled condition whenTrue whenFalse) =
      conditional enabled (bind sigma condition) (bind sigma whenTrue) (bind sigma whenFalse) := rfl

def substitution : (values : List (Closed extended)) → Sub (signature extended) (Context values) []
  | [], _, variable_ => nomatch variable_
  | value :: _, _, .zero => value
  | _ :: values, _, .succ variable_ => substitution values () variable_

def prepend {Γ : List Unit} (sigma : Sub (signature extended) Γ []) (value : (Closed extended)) :
    Sub (signature extended) (() :: Γ) []
  | _, .zero => value
  | _, .succ variable_ => sigma () variable_

@[simp] theorem substitution_cons (value : (Closed extended)) (values : List (Closed extended)) :
    substitution (value :: values) = prepend (substitution values) value := by
  funext sort variable_
  cases sort
  cases variable_ <;> rfl

/-- Closing an abstraction and then applying it is the same substitution as
extending the captured environment. This uses associativity and weakening of
the common binding algebra, at every binder depth. -/
theorem instantiate_closed {Γ : List Unit} (sigma : Sub (signature extended) Γ [])
    (body : Scoped (extended := extended) (() :: Γ)) (argument : (Closed extended)) :
    inst (bind (liftSub sigma [()]) body) argument = bind (prepend sigma argument) body := by
  change bind (Mettapedia.OSLF.Binding.extend argument) (bind (liftSub sigma [()]) body) = _
  rw [bind_comp]
  apply congrArg (fun (sigma : Sub (signature extended) (() :: Γ) []) => bind sigma body)
  funext sort variable_
  cases sort
  cases variable_ with
  | zero => rfl
  | succ variable_ =>
      change inst (weaken (sigma () variable_)) argument = sigma () variable_
      exact inst_weaken (sigma () variable_) argument

/-- Tag distinctions for the weak untyped source profile. Neutral projections
and applications are values only when the active rule is unavailable. -/
def NotLam (term : (Closed extended)) : Prop :=
  match erase term with
  | .lam _ => False
  | _ => True

def NotPair (term : (Closed extended)) : Prop :=
  match erase term with
  | .pair _ _ => False
  | _ => True

inductive Normal : (Closed extended) → Prop where
  | literal (enabled : extended = true) (value : Literal) : Normal (literal enabled value)

  | lam (body : Scoped (extended := extended) [()]) : Normal (lam body)
  | pair {left right : (Closed extended)} (leftNormal : Normal left) (rightNormal : Normal right) :
      Normal (pair left right)
  | first {term : (Closed extended)} (normal : Normal term) (inactive : NotPair term) : Normal (first term)
  | second {term : (Closed extended)} (normal : Normal term) (inactive : NotPair term) : Normal (second term)
  | app {operator argument : (Closed extended)} (operatorNormal : Normal operator)
      (argumentNormal : Normal argument) (inactive : NotLam operator) : Normal (app operator argument)

mutual
/-- Exact source readback of a source-bodied combinatory value. Environments
are separate from values: their unit sentinel is never a lambda source value. -/
inductive Readback : SourceValue extended → (Closed extended) → Prop where
  | literal (enabled : extended = true) (value : Literal) :
      Readback (.literal enabled value) (literal enabled value)

  | closure {environment : SourceValue extended} {values : List (Closed extended)} {body : Scoped (extended := extended) (() :: Context values)}
      (captured : EnvironmentReadback environment values) :
      Readback (.closure (erase body) environment) (lam (bind (liftSub (substitution values) [()]) body))
  | pair {left right : SourceValue extended} {leftTerm rightTerm : (Closed extended)}
      (leftReadback : Readback left leftTerm) (rightReadback : Readback right rightTerm) :
      Readback (.pair left right) (pair leftTerm rightTerm)
  | first {value : SourceValue extended} {term : (Closed extended)} (readback : Readback value term)
      (inactive : CategoricalAbstractMachine.NotPair value) : Readback (.first value) (first term)
  | second {value : SourceValue extended} {term : (Closed extended)} (readback : Readback value term)
      (inactive : CategoricalAbstractMachine.NotPair value) : Readback (.second value) (second term)
  | app {operator argument : SourceValue extended} {operatorTerm argumentTerm : (Closed extended)}
      (operatorReadback : Readback operator operatorTerm) (argumentReadback : Readback argument argumentTerm)
      (inactive : NotClosure operator) :
      Readback (.app (.pair operator argument)) (app operatorTerm argumentTerm)
inductive EnvironmentReadback : SourceValue extended → List (Closed extended) → Prop where
  | nil : EnvironmentReadback .unit []
  | cons {environment value : SourceValue extended} {values : List (Closed extended)} {term : (Closed extended)}
      (environmentReadback : EnvironmentReadback environment values) (valueReadback : Readback value term) :
      EnvironmentReadback (.pair environment value) (term :: values)
end

inductive ProjectionFirst : (Closed extended) → (Closed extended) → Prop where
  | pair (left right : (Closed extended)) : ProjectionFirst (pair left right) left
  | neutral (term : (Closed extended)) (inactive : NotPair term) : ProjectionFirst term (first term)
inductive ProjectionSecond : (Closed extended) → (Closed extended) → Prop where
  | pair (left right : (Closed extended)) : ProjectionSecond (pair left right) right
  | neutral (term : (Closed extended)) (inactive : NotPair term) : ProjectionSecond term (second term)

mutual
/-- Independent completed weak left-to-right source evaluation. Application
uses source substitution, rather than closure environments or instructions. -/
inductive CBV : (Closed extended) → (Closed extended) → Prop where
  | literal (enabled : extended = true) (value : Literal) : CBV (literal enabled value) (literal enabled value)
  | conditional {enabled : extended = true} {condition whenTrue whenFalse value : Closed extended}
      {selected : Bool} (conditionEval : CBV condition (literal enabled (.boolean selected)))
      (selectedEval : CBV (if selected then whenTrue else whenFalse) value) :
      CBV (conditional enabled condition whenTrue whenFalse) value

  | lam (body : Scoped (extended := extended) [()]) : CBV (lam body) (lam body)
  | pair {left right leftValue rightValue : (Closed extended)}
      (leftEval : CBV left leftValue) (rightEval : CBV right rightValue) :
      CBV (pair left right) (pair leftValue rightValue)
  | app {operator argument function operand result : (Closed extended)}
      (operatorEval : CBV operator function) (argumentEval : CBV argument operand)
      (invocation : Application function operand result) : CBV (app operator argument) result
  | first {term before result : (Closed extended)} (evaluation : CBV term before)
      (projection : ProjectionFirst before result) : CBV (first term) result
  | second {term before result : (Closed extended)} (evaluation : CBV term before)
      (projection : ProjectionSecond before result) : CBV (second term) result
inductive Application : (Closed extended) → (Closed extended) → (Closed extended) → Prop where
  | beta {body : Scoped (extended := extended) [()]} {argument result : (Closed extended)} (bodyEval : CBV (inst body argument) result) :
      Application (lam body) argument result
  | neutral (operator argument : (Closed extended)) (inactive : NotLam operator) :
      Application operator argument (app operator argument)
end

theorem Readback.notLam {value : SourceValue extended} {term : (Closed extended)}
    (readback : Readback value term) (inactive : NotClosure value) : NotLam term := by
  cases readback <;> simp_all [NotClosure, NotLam]

theorem Readback.notPair {value : SourceValue extended} {term : (Closed extended)}
    (readback : Readback value term) (inactive : CategoricalAbstractMachine.NotPair value) : NotPair term := by
  cases readback <;> simp_all [CategoricalAbstractMachine.NotPair, NotPair]

theorem Readback.normal {value : SourceValue extended} {term : (Closed extended)} (readback : Readback value term) : Normal term := by
  induction readback using Readback.rec
      (motive_2 := fun _ values _ => ∀ term ∈ values, Normal term) with
  | literal enabled value => exact .literal enabled value
  | closure => exact .lam _
  | pair _ _ ihLeft ihRight => exact .pair ihLeft ihRight
  | first readback inactive ih => exact .first ih (readback.notPair inactive)
  | second readback inactive ih => exact .second ih (readback.notPair inactive)
  | app operatorReadback _ inactive ihO ihA => exact .app ihO ihA (operatorReadback.notLam inactive)
  | nil => rename_i term member; cases member
  | cons _ _ ihValues ihValue =>
      rename_i term member
      cases member with
      | head => exact ihValue
      | tail _ member => exact ihValues _ member

theorem Normal.evaluation {term : (Closed extended)} (normal : Normal term) : CBV term term := by
  induction normal with
  | literal enabled value => exact .literal enabled value
  | lam body => exact .lam body
  | pair _ _ ihL ihR => exact .pair ihL ihR
  | first _ inactive ih => exact .first ih (.neutral _ inactive)
  | second _ inactive ih => exact .second ih (.neutral _ inactive)
  | app _ _ inactive ihO ihA => exact .app ihO ihA (.neutral _ _ inactive)

theorem ProjectionFirst.normal {term result : (Closed extended)} (projection : ProjectionFirst term result)
    (normal : Normal term) : Normal result := by
  cases projection with
  | pair => cases normal; assumption
  | neutral term inactive => exact .first normal inactive

theorem ProjectionSecond.normal {term result : (Closed extended)} (projection : ProjectionSecond term result)
    (normal : Normal term) : Normal result := by
  cases projection with
  | pair => cases normal; assumption
  | neutral term inactive => exact .second normal inactive

theorem CBV.normal {term result : (Closed extended)} (evaluation : CBV term result) : Normal result := by
  induction evaluation using CBV.rec
      (motive_2 := fun operator argument result _ => Normal operator → Normal argument → Normal result) with
  | literal enabled value => exact .literal enabled value
  | conditional _ _ _ ihSelected => exact ihSelected
  | lam body => exact .lam body
  | pair _ _ ihL ihR => exact .pair ihL ihR
  | app _ _ _ ihO ihA ihCall => exact ihCall ihO ihA
  | first _ projection ih => exact projection.normal ih
  | second _ projection ih => exact projection.normal ih
  | beta _ ih => exact ih
  | neutral operator argument inactive => exact .app ‹Normal operator› ‹Normal argument› inactive

theorem EnvironmentReadback.lookup {environment : SourceValue extended} {values : List (Closed extended)}
    (captured : EnvironmentReadback environment values) (variable_ : Var (Context values) ()) :
    ∃ value, CategoricalAbstractMachine.Evaluation (.var (position variable_)) environment value ∧
      Readback value (substitution values () variable_) := by
  induction values generalizing environment with
  | nil => cases variable_
  | cons term values ih =>
      cases captured with
      | cons captured readback =>
          cases variable_ with
          | zero => exact ⟨_, .varZero (.pair _ _), readback⟩
          | succ variable_ =>
              obtain ⟨value, evaluation, valueReadback⟩ := ih captured variable_
              exact ⟨value, .varSucc (.pair _ _) evaluation, valueReadback⟩

theorem Normal.result {term result : (Closed extended)} (normal : Normal term) (evaluation : CBV term result) : result = term := by
  induction normal generalizing result with
  | literal enabled value => cases evaluation; rfl
  | lam body => cases evaluation; rfl
  | pair leftNormal rightNormal ihL ihR =>
      cases evaluation with
      | pair leftEval rightEval => rw [ihL leftEval, ihR rightEval]
  | first normal inactive ih =>
      cases evaluation with
      | first evaluation projection =>
          have same := ih evaluation
          subst same
          cases projection with
          | pair left right => simp [NotPair, erase_pair] at inactive
          | neutral => rfl
  | second normal inactive ih =>
      cases evaluation with
      | second evaluation projection =>
          have same := ih evaluation
          subst same
          cases projection with
          | pair left right => simp [NotPair, erase_pair] at inactive
          | neutral => rfl
  | app operatorNormal argumentNormal inactive ihO ihA =>
      cases evaluation with
      | app operatorEval argumentEval invocation =>
          have operatorSame := ihO operatorEval
          have argumentSame := ihA argumentEval
          subst operatorSame
          subst argumentSame
          cases invocation with
          | beta => simp [NotLam, erase_lam] at inactive
          | neutral => rfl

theorem First.readback {value result : SourceValue extended} (projection : CategoricalAbstractMachine.First value result)
    {term : (Closed extended)} (readback : Readback value term) :
    ∃ resultTerm, Readback result resultTerm ∧ ProjectionFirst term resultTerm := by
  cases projection with
  | pair left right =>
      cases readback with
      | pair leftReadback rightReadback => exact ⟨_, leftReadback, .pair _ _⟩
  | neutral value inactive => exact ⟨first term, .first readback inactive, .neutral term (readback.notPair inactive)⟩

theorem Second.readback {value result : SourceValue extended} (projection : CategoricalAbstractMachine.Second value result)
    {term : (Closed extended)} (readback : Readback value term) :
    ∃ resultTerm, Readback result resultTerm ∧ ProjectionSecond term resultTerm := by
  cases projection with
  | pair left right =>
      cases readback with
      | pair leftReadback rightReadback => exact ⟨_, rightReadback, .pair _ _⟩
  | neutral value inactive => exact ⟨second term, .second readback inactive, .neutral term (readback.notPair inactive)⟩

theorem variable_readback {environment value : SourceValue extended} {values : List (Closed extended)}
    (captured : EnvironmentReadback environment values) (variable_ : Var (Context values) ())
    (evaluation : CategoricalAbstractMachine.Evaluation (.var (position variable_)) environment value) :
    ∃ result, Readback value result ∧ CBV (substitution values () variable_) result := by
  obtain ⟨actual, actualEval, readback⟩ := captured.lookup variable_
  have same := CategoricalAbstractMachine.Evaluation.unique actualEval evaluation
  subst value
  exact ⟨_, readback, readback.normal.evaluation⟩

/-- Every completed combinatory evaluation of a scoped expression in a
represented environment yields its exact weak source readback. -/
theorem evaluation_readback {term : Source extended} {environment value : SourceValue extended}
    (evaluation : CategoricalAbstractMachine.Evaluation term environment value) :
    ∀ {values : List (Closed extended)} (source : Scoped (extended := extended) (Context values))
      (_captured : EnvironmentReadback environment values), erase source = term →
      ∃ result, Readback value result ∧ CBV (bind (substitution values) source) result := by
  induction evaluation using CategoricalAbstractMachine.Evaluation.rec
      (motive_2 := fun function argument value _ => ∀ {operator operand : (Closed extended)},
        Readback function operator → Readback argument operand →
          ∃ result, Readback value result ∧ Application operator operand result) with
  | @varZero environment value projection =>
      intro values source captured represented
      induction source using scopedCases with
      | varCase variable_ =>
          apply variable_readback captured variable_
          rw [show position variable_ = 0 from Source.var.inj represented]
          exact .varZero projection
      | lamCase body => simp only [erase_lam, reduceCtorEq] at represented
      | appCase operator argument => simp only [erase_app, reduceCtorEq] at represented
      | pairCase left right => simp only [erase_pair, reduceCtorEq] at represented
      | firstCase term => simp only [erase_first, reduceCtorEq] at represented
      | secondCase term => simp only [erase_second, reduceCtorEq] at represented
      | literalCase enabled value => simp only [erase_literal, reduceCtorEq] at represented
      | conditionalCase enabled condition whenTrue whenFalse => simp only [erase_conditional, reduceCtorEq] at represented
  | @varSucc index environment before value projection rest restIH =>
      intro values source captured represented
      induction source using scopedCases with
      | varCase variable_ =>
          apply variable_readback captured variable_
          rw [show position variable_ = index + 1 from Source.var.inj represented]
          exact .varSucc projection rest
      | lamCase body => simp only [erase_lam, reduceCtorEq] at represented
      | appCase operator argument => simp only [erase_app, reduceCtorEq] at represented
      | pairCase left right => simp only [erase_pair, reduceCtorEq] at represented
      | firstCase term => simp only [erase_first, reduceCtorEq] at represented
      | secondCase term => simp only [erase_second, reduceCtorEq] at represented
      | literalCase enabled value => simp only [erase_literal, reduceCtorEq] at represented
      | conditionalCase enabled condition whenTrue whenFalse => simp only [erase_conditional, reduceCtorEq] at represented
  | @lam body environment =>
      intro values source captured represented
      induction source using scopedCases with
      | varCase variable_ => simp only [erase, reduceCtorEq] at represented
      | lamCase sourceBody =>
          have same : erase sourceBody = body := Source.lam.inj represented
          subst body
          exact ⟨_, .closure captured, .lam _⟩
      | appCase operator argument => simp only [erase_app, reduceCtorEq] at represented
      | pairCase left right => simp only [erase_pair, reduceCtorEq] at represented
      | firstCase term => simp only [erase_first, reduceCtorEq] at represented
      | secondCase term => simp only [erase_second, reduceCtorEq] at represented
      | literalCase enabled value => simp only [erase_literal, reduceCtorEq] at represented
      | conditionalCase enabled condition whenTrue whenFalse => simp only [erase_conditional, reduceCtorEq] at represented
  | @pair left right environment firstValue secondValue leftEval rightEval leftIH rightIH =>
      intro values source captured represented
      induction source using scopedCases with
      | varCase variable_ => simp only [erase, reduceCtorEq] at represented
      | lamCase body => simp only [erase_lam, reduceCtorEq] at represented
      | appCase operator argument => simp only [erase_app, reduceCtorEq] at represented
      | pairCase sourceLeft sourceRight =>
          obtain ⟨sameLeft, sameRight⟩ := Source.pair.inj represented
          obtain ⟨leftTerm, leftReadback, leftCBV⟩ := leftIH sourceLeft captured sameLeft
          obtain ⟨rightTerm, rightReadback, rightCBV⟩ := rightIH sourceRight captured sameRight
          exact ⟨_, .pair leftReadback rightReadback, .pair leftCBV rightCBV⟩
      | firstCase term => simp only [erase_first, reduceCtorEq] at represented
      | secondCase term => simp only [erase_second, reduceCtorEq] at represented
      | literalCase enabled value => simp only [erase_literal, reduceCtorEq] at represented
      | conditionalCase enabled condition whenTrue whenFalse => simp only [erase_conditional, reduceCtorEq] at represented
  | @app operator argument environment function operand result operatorEval argumentEval invocation operatorIH argumentIH invocationIH =>
      intro values source captured represented
      induction source using scopedCases with
      | varCase variable_ => simp only [erase, reduceCtorEq] at represented
      | lamCase body => simp only [erase_lam, reduceCtorEq] at represented
      | appCase sourceOperator sourceArgument =>
          obtain ⟨sameOperator, sameArgument⟩ := Source.app.inj represented
          obtain ⟨functionTerm, functionReadback, operatorCBV⟩ := operatorIH sourceOperator captured sameOperator
          obtain ⟨operandTerm, operandReadback, argumentCBV⟩ := argumentIH sourceArgument captured sameArgument
          obtain ⟨resultTerm, resultReadback, sourceInvocation⟩ := invocationIH functionReadback operandReadback
          exact ⟨resultTerm, resultReadback, .app operatorCBV argumentCBV sourceInvocation⟩
      | pairCase left right => simp only [erase_pair, reduceCtorEq] at represented
      | firstCase term => simp only [erase_first, reduceCtorEq] at represented
      | secondCase term => simp only [erase_second, reduceCtorEq] at represented
      | literalCase enabled value => simp only [erase_literal, reduceCtorEq] at represented
      | conditionalCase enabled condition whenTrue whenFalse => simp only [erase_conditional, reduceCtorEq] at represented
  | @first term environment before value termEval projection termIH =>
      intro values source captured represented
      induction source using scopedCases with
      | varCase variable_ => simp only [erase, reduceCtorEq] at represented
      | lamCase body => simp only [erase_lam, reduceCtorEq] at represented
      | appCase operator argument => simp only [erase_app, reduceCtorEq] at represented
      | pairCase left right => simp only [erase_pair, reduceCtorEq] at represented
      | firstCase sourceTerm =>
          have same := Source.first.inj represented
          obtain ⟨beforeTerm, beforeReadback, termCBV⟩ := termIH sourceTerm captured same
          obtain ⟨resultTerm, resultReadback, sourceProjection⟩ := First.readback projection beforeReadback
          exact ⟨_, resultReadback, .first termCBV sourceProjection⟩
      | secondCase term => simp only [erase_second, reduceCtorEq] at represented
      | literalCase enabled value => simp only [erase_literal, reduceCtorEq] at represented
      | conditionalCase enabled condition whenTrue whenFalse => simp only [erase_conditional, reduceCtorEq] at represented
  | @second term environment before value termEval projection termIH =>
      intro values source captured represented
      induction source using scopedCases with
      | varCase variable_ => simp only [erase, reduceCtorEq] at represented
      | lamCase body => simp only [erase_lam, reduceCtorEq] at represented
      | appCase operator argument => simp only [erase_app, reduceCtorEq] at represented
      | pairCase left right => simp only [erase_pair, reduceCtorEq] at represented
      | firstCase term => simp only [erase_first, reduceCtorEq] at represented
      | secondCase sourceTerm =>
          have same := Source.second.inj represented
          obtain ⟨beforeTerm, beforeReadback, termCBV⟩ := termIH sourceTerm captured same
          obtain ⟨resultTerm, resultReadback, sourceProjection⟩ := Second.readback projection beforeReadback
          exact ⟨_, resultReadback, .second termCBV sourceProjection⟩
      | literalCase enabled value => simp only [erase_literal, reduceCtorEq] at represented
      | conditionalCase enabled condition whenTrue whenFalse => simp only [erase_conditional, reduceCtorEq] at represented
  | @closure body environment argument value bodyEval bodyIH =>
      rename_i operator operand functionReadback argumentReadback
      cases functionReadback with
      | @closure environment values sourceBody captured =>
          obtain ⟨resultTerm, resultReadback, sourceEval⟩ := bodyIH (values := operand :: values)
            sourceBody (.cons captured argumentReadback) rfl
          refine ⟨resultTerm, resultReadback, .beta ?_⟩
          rw [instantiate_closed]
          simpa only [substitution_cons] using sourceEval
  | neutral function argument inactive =>
      rename_i operator operand functionReadback argumentReadback
      exact ⟨_, .app functionReadback argumentReadback inactive,
        .neutral _ _ (functionReadback.notLam inactive)⟩

  | @literal enabled value environment =>
      intro values source captured represented
      induction source using scopedCases with
      | literalCase sourceEnabled sourceValue =>
          have same := Source.literal.inj represented
          subst sourceValue
          exact ⟨_, .literal enabled value, .literal enabled value⟩
      | varCase | lamCase | appCase | pairCase | firstCase | secondCase | conditionalCase =>
          cases represented
  | @conditional enabled condition whenTrue whenFalse environment value selected conditionEval selectedEval conditionIH selectedIH =>
      intro values source captured represented
      induction source using scopedCases with
      | conditionalCase sourceEnabled sourceCondition sourceTrue sourceFalse =>
          obtain ⟨sameCondition, sameTrue, sameFalse⟩ := Source.conditional.inj represented
          obtain ⟨conditionTerm, conditionReadback, conditionCBV⟩ := conditionIH sourceCondition captured sameCondition
          cases conditionReadback
          obtain ⟨resultTerm, resultReadback, resultCBV⟩ := selectedIH
            (if selected then sourceTrue else sourceFalse) captured (by cases selected <;> assumption)
          refine ⟨resultTerm, resultReadback, .conditional conditionCBV ?_⟩
          cases selected <;> exact resultCBV
      | varCase | lamCase | appCase | pairCase | firstCase | secondCase | literalCase =>
          cases represented

theorem invocation_readback {function argument value : SourceValue extended}
    (invocation : Invocation function argument value) {operator operand : (Closed extended)}
    (functionReadback : Readback function operator) (argumentReadback : Readback argument operand) :
    ∃ result, Readback value result ∧ Application operator operand result := by
  cases invocation with
  | closure bodyEval =>
      cases functionReadback with
      | @closure environment values sourceBody captured =>
          obtain ⟨resultTerm, resultReadback, sourceEval⟩ := evaluation_readback bodyEval
            (values := operand :: values) sourceBody (.cons captured argumentReadback) rfl
          refine ⟨resultTerm, resultReadback, .beta ?_⟩
          rw [instantiate_closed]
          simpa only [substitution_cons] using sourceEval
  | neutral function argument inactive =>
      exact ⟨_, .app functionReadback argumentReadback inactive,
        .neutral _ _ (functionReadback.notLam inactive)⟩

theorem Readback.reflectNotLam {value : SourceValue extended} {term : (Closed extended)}
    (readback : Readback value term) (inactive : NotLam term) : NotClosure value := by
  cases readback <;> simp_all [NotLam, NotClosure]

theorem Readback.reflectNotPair {value : SourceValue extended} {term : (Closed extended)}
    (readback : Readback value term) (inactive : NotPair term) : CategoricalAbstractMachine.NotPair value := by
  cases readback <;> simp_all [NotPair, CategoricalAbstractMachine.NotPair]

theorem ProjectionFirst.realization {term result : (Closed extended)} (projection : ProjectionFirst term result)
    {value : SourceValue extended} (readback : Readback value term) :
    ∃ actual, CategoricalAbstractMachine.First value actual ∧ Readback actual result := by
  cases projection with
  | pair left right =>
      cases readback with
      | pair leftReadback rightReadback => exact ⟨_, .pair _ _, leftReadback⟩
  | neutral term inactive =>
      have actualInactive := readback.reflectNotPair inactive
      exact ⟨_, .neutral _ actualInactive, .first readback actualInactive⟩

theorem ProjectionSecond.realization {term result : (Closed extended)} (projection : ProjectionSecond term result)
    {value : SourceValue extended} (readback : Readback value term) :
    ∃ actual, CategoricalAbstractMachine.Second value actual ∧ Readback actual result := by
  cases projection with
  | pair left right =>
      cases readback with
      | pair leftReadback rightReadback => exact ⟨_, .pair _ _, rightReadback⟩
  | neutral term inactive =>
      have actualInactive := readback.reflectNotPair inactive
      exact ⟨_, .neutral _ actualInactive, .second readback actualInactive⟩

theorem lam_inj {Γ : List Unit} {left right : Scoped (extended := extended) (() :: Γ)} (same : lam left = lam right) : left = right := by
  apply erase_injective
  have erased := congrArg erase same
  exact Source.lam.inj erased

theorem app_inj {Γ : List Unit} {operator argument operator' argument' : Scoped (extended := extended) Γ}
    (same : app operator argument = app operator' argument') : operator = operator' ∧ argument = argument' := by
  have erased := Source.app.inj (congrArg erase same)
  exact ⟨erase_injective erased.1, erase_injective erased.2⟩

theorem pair_inj {Γ : List Unit} {left right left' right' : Scoped (extended := extended) Γ}
    (same : pair left right = pair left' right') : left = left' ∧ right = right' := by
  have erased := Source.pair.inj (congrArg erase same)
  exact ⟨erase_injective erased.1, erase_injective erased.2⟩

theorem first_inj {Γ : List Unit} {term term' : Scoped (extended := extended) Γ} (same : first term = first term') : term = term' := by
  apply erase_injective
  exact Source.first.inj (congrArg erase same)

theorem second_inj {Γ : List Unit} {term term' : Scoped (extended := extended) Γ} (same : second term = second term') : term = term' := by
  apply erase_injective
  exact Source.second.inj (congrArg erase same)

theorem literal_inj {Γ : List Unit} {enabled : extended = true} {left right : Literal}
    (same : literal (Γ := Γ) enabled left = literal enabled right) : left = right :=
  Source.literal.inj (congrArg erase same)

theorem conditional_inj {Γ : List Unit} {enabled : extended = true}
    {condition whenTrue whenFalse condition' whenTrue' whenFalse' : Scoped Γ extended}
    (same : conditional enabled condition whenTrue whenFalse = conditional enabled condition' whenTrue' whenFalse') :
    condition = condition' ∧ whenTrue = whenTrue' ∧ whenFalse = whenFalse' := by
  have erased := Source.conditional.inj (congrArg erase same)
  exact ⟨erase_injective erased.1, erase_injective erased.2.1, erase_injective erased.2.2⟩

theorem variable_realization {environment : SourceValue extended} {values : List (Closed extended)}
    (captured : EnvironmentReadback environment values) (variable_ : Var (Context values) ())
    {result : (Closed extended)} (evaluation : CBV (substitution values () variable_) result) :
    ∃ value, CategoricalAbstractMachine.Evaluation (.var (position variable_)) environment value ∧
      Readback value result := by
  obtain ⟨value, lookup, readback⟩ := captured.lookup variable_
  have same := readback.normal.result evaluation
  subst result
  exact ⟨value, lookup, readback⟩

/-- Reverse correspondence constructs the actual combinatory endpoint of a
source evaluation, preserving its represented captured environment. -/
theorem cbv_realization {term result : (Closed extended)} (evaluation : CBV term result) :
    ∀ {environment : SourceValue extended} {values : List (Closed extended)} (source : Scoped (extended := extended) (Context values))
      (_captured : EnvironmentReadback environment values), bind (substitution values) source = term →
      ∃ value, CategoricalAbstractMachine.Evaluation (erase source) environment value ∧ Readback value result := by
  induction evaluation using CBV.rec
      (motive_2 := fun operator operand result _ => ∀ {function argument : SourceValue extended},
        Readback function operator → Readback argument operand →
          ∃ value, Invocation function argument value ∧ Readback value result) with
  | literal enabled value =>
      intro environment values source captured represented
      induction source using scopedCases with
      | varCase variable_ =>
          apply variable_realization captured variable_
          rw [show substitution values () variable_ = _ from represented]
          exact .literal enabled value
      | literalCase sourceEnabled sourceValue =>
          have same := literal_inj represented
          subst sourceValue
          exact ⟨_, .literal enabled value environment, .literal enabled value⟩
      | lamCase | appCase | pairCase | firstCase | secondCase | conditionalCase => cases represented
  | @conditional enabled condition whenTrue whenFalse value selected conditionEval selectedEval conditionIH selectedIH =>
      intro environment values source captured represented
      induction source using scopedCases with
      | varCase variable_ =>
          apply variable_realization captured variable_
          rw [show substitution values () variable_ = _ from represented]
          exact .conditional conditionEval selectedEval
      | conditionalCase sourceEnabled sourceCondition sourceTrue sourceFalse =>
          obtain ⟨sameCondition, sameTrue, sameFalse⟩ := conditional_inj represented
          obtain ⟨conditionValue, actualCondition, conditionReadback⟩ := conditionIH sourceCondition captured sameCondition
          cases conditionReadback
          obtain ⟨resultValue, actualResult, resultReadback⟩ := selectedIH
            (if selected then sourceTrue else sourceFalse) captured (by cases selected <;> assumption)
          refine ⟨resultValue, .conditional actualCondition ?_, resultReadback⟩
          cases selected <;> exact actualResult
      | lamCase | appCase | pairCase | firstCase | secondCase | literalCase => cases represented

  | lam body =>
      intro environment values source captured represented
      induction source using scopedCases with
      | varCase variable_ =>
          apply variable_realization captured variable_
          rw [show substitution values () variable_ = lam body from represented]
          exact .lam body
      | lamCase sourceBody => exact ⟨_, .lam _ _, represented ▸ (Readback.closure captured)⟩
      | appCase operator argument => cases represented
      | pairCase left right => cases represented
      | firstCase term => cases represented
      | secondCase term => cases represented
      | literalCase enabled value => cases represented
      | conditionalCase enabled condition whenTrue whenFalse => cases represented
  | pair leftEval rightEval leftIH rightIH =>
      intro environment values source captured represented
      induction source using scopedCases with
      | varCase variable_ =>
          apply variable_realization captured variable_
          rw [show substitution values () variable_ = _ from represented]
          exact .pair leftEval rightEval
      | lamCase body => cases represented
      | appCase operator argument => cases represented
      | pairCase left right =>
          obtain ⟨sameLeft, sameRight⟩ := pair_inj represented
          obtain ⟨leftValue, actualLeft, leftReadback⟩ := leftIH left captured sameLeft
          obtain ⟨rightValue, actualRight, rightReadback⟩ := rightIH right captured sameRight
          exact ⟨_, .pair actualLeft actualRight, .pair leftReadback rightReadback⟩
      | firstCase term => cases represented
      | secondCase term => cases represented
      | literalCase enabled value => cases represented
      | conditionalCase enabled condition whenTrue whenFalse => cases represented
  | app operatorEval argumentEval invocation operatorIH argumentIH invocationIH =>
      intro environment values source captured represented
      induction source using scopedCases with
      | varCase variable_ =>
          apply variable_realization captured variable_
          rw [show substitution values () variable_ = _ from represented]
          exact .app operatorEval argumentEval invocation
      | lamCase body => cases represented
      | appCase operator argument =>
          obtain ⟨sameOperator, sameArgument⟩ := app_inj represented
          obtain ⟨function, actualOperator, operatorReadback⟩ := operatorIH operator captured sameOperator
          obtain ⟨operand, actualArgument, argumentReadback⟩ := argumentIH argument captured sameArgument
          obtain ⟨value, actualInvocation, valueReadback⟩ := invocationIH operatorReadback argumentReadback
          exact ⟨value, .app actualOperator actualArgument actualInvocation, valueReadback⟩
      | pairCase left right => cases represented
      | firstCase term => cases represented
      | secondCase term => cases represented
      | literalCase enabled value => cases represented
      | conditionalCase enabled condition whenTrue whenFalse => cases represented
  | first evaluation projection termIH =>
      intro environment values source captured represented
      induction source using scopedCases with
      | varCase variable_ =>
          apply variable_realization captured variable_
          rw [show substitution values () variable_ = _ from represented]
          exact .first evaluation projection
      | lamCase body => cases represented
      | appCase operator argument => cases represented
      | pairCase left right => cases represented
      | firstCase term =>
          have same := first_inj represented
          obtain ⟨before, actualTerm, beforeReadback⟩ := termIH term captured same
          obtain ⟨value, actualProjection, valueReadback⟩ := projection.realization beforeReadback
          exact ⟨value, .first actualTerm actualProjection, valueReadback⟩
      | secondCase term => cases represented
      | literalCase enabled value => cases represented
      | conditionalCase enabled condition whenTrue whenFalse => cases represented
  | second evaluation projection termIH =>
      intro environment values source captured represented
      induction source using scopedCases with
      | varCase variable_ =>
          apply variable_realization captured variable_
          rw [show substitution values () variable_ = _ from represented]
          exact .second evaluation projection
      | lamCase body => cases represented
      | appCase operator argument => cases represented
      | pairCase left right => cases represented
      | firstCase term => cases represented
      | secondCase term =>
          have same := second_inj represented
          obtain ⟨before, actualTerm, beforeReadback⟩ := termIH term captured same
          obtain ⟨value, actualProjection, valueReadback⟩ := projection.realization beforeReadback
          exact ⟨value, .second actualTerm actualProjection, valueReadback⟩
      | literalCase enabled value => cases represented
      | conditionalCase enabled condition whenTrue whenFalse => cases represented
  | beta bodyEval bodyIH =>
      rename_i body operand result function argument functionReadback argumentReadback
      cases functionReadback with
      | @closure environment values sourceBody captured =>
          obtain ⟨value, actualBody, valueReadback⟩ := bodyIH (values := operand :: values) sourceBody
            (.cons captured argumentReadback) (by simpa only [substitution_cons] using
              (instantiate_closed (substitution values) sourceBody operand).symm)
          exact ⟨value, .closure actualBody, valueReadback⟩
  | neutral operator operand inactive =>
      rename_i function argument functionReadback argumentReadback
      have actualInactive := functionReadback.reflectNotLam inactive
      exact ⟨_, .neutral _ _ actualInactive, .app functionReadback argumentReadback actualInactive⟩


/-- These tag tests inspect syntax only. Scope and captured-value validity are
checked by the executable readback below and its independent judgments. -/
def nonPair : SourceValue extended → Bool
  | .pair _ _ => false
  | _ => true

def nonClosure : SourceValue extended → Bool
  | .closure _ _ => false
  | _ => true

@[simp] theorem nonPair_iff (value : SourceValue extended) : nonPair value = true ↔ CategoricalAbstractMachine.NotPair value := by
  cases value <;> simp [nonPair, CategoricalAbstractMachine.NotPair]
@[simp] theorem nonClosure_iff (value : SourceValue extended) : nonClosure value = true ↔ NotClosure value := by
  cases value <;> simp [nonClosure, NotClosure]

mutual
/-- Executable closed readback. An unscoped closure, an environment sentinel
as value, or a payload using an active rule as a neutral value is refused. -/
def realize : SourceValue extended → Option (Closed extended)
  | .literal enabled value => some (literal enabled value)
  | .unit => none
  | .closure body environment => do
      let values ← realizeEnvironment environment
      let source ← represent (() :: Context values) body
      pure (lam (bind (liftSub (substitution values) [()]) source))
  | .pair left right => do
      let left ← realize left
      let right ← realize right
      pure (pair left right)
  | .first value => if nonPair value then (realize value).map first else none
  | .second value => if nonPair value then (realize value).map second else none
  | .app (.pair operator argument) => if nonClosure operator then do
      let operator ← realize operator
      let argument ← realize argument
      pure (app operator argument)
    else none
  | .app _ => none

def realizeEnvironment : SourceValue extended → Option (List (Closed extended))
  | .unit => some []
  | .pair environment value => do
      let values ← realizeEnvironment environment
      let value ← realize value
      pure (value :: values)
  | _ => none
end

theorem Readback.realized {value : SourceValue extended} {term : (Closed extended)} (readback : Readback value term) : realize value = some term := by
  induction readback using Readback.rec
      (motive_2 := fun environment values _ => realizeEnvironment environment = some values) with
  | literal => rfl
  | @closure environment values body captured capturedIH =>
      simp only [realize, capturedIH]
      change (represent (() :: Context values) (erase body)).bind _ = _
      rw [show represent (() :: Context values) (erase body) = some body from represent_erase body]
      rfl
  | pair _ _ leftIH rightIH => simp [realize, leftIH, rightIH]
  | first _ inactive ih => simp [realize, (nonPair_iff _).mpr inactive, ih]
  | second _ inactive ih => simp [realize, (nonPair_iff _).mpr inactive, ih]
  | app _ _ inactive operatorIH argumentIH => simp [realize, (nonClosure_iff _).mpr inactive, operatorIH, argumentIH]
  | nil => rfl
  | cons _ _ capturedIH valueIH => simp [realizeEnvironment, capturedIH, valueIH]

theorem EnvironmentReadback.realized {environment : SourceValue extended} {values : List (Closed extended)}
    (captured : EnvironmentReadback environment values) : realizeEnvironment environment = some values := by
  induction values generalizing environment with
  | nil => cases captured; rfl
  | cons value values ih =>
      cases captured with
      | cons captured readback => simp [realizeEnvironment, ih captured, readback.realized]

private theorem realize_sound_both (value : SourceValue extended) :
    (∀ term, realize value = some term → Readback value term) ∧
    (∀ values, realizeEnvironment value = some values → EnvironmentReadback value values) := by
  induction value with
  | unit =>
      constructor
      · intro term found; simp [realize] at found
      · intro values found; simp only [realizeEnvironment, Option.some.injEq] at found; subst values; exact .nil
  | pair left right ihL ihR =>
      constructor
      · intro term found
        cases leftFound : realize left with
        | none => simp [realize, leftFound] at found
        | some leftTerm =>
            cases rightFound : realize right with
            | none => simp [realize, leftFound, rightFound] at found
            | some rightTerm =>
                simp [realize, leftFound, rightFound] at found
                subst term
                exact .pair (ihL.1 _ leftFound) (ihR.1 _ rightFound)
      · intro values found
        cases leftFound : realizeEnvironment left with
        | none => simp [realizeEnvironment, leftFound] at found
        | some leftValues =>
            cases rightFound : realize right with
            | none => simp [realizeEnvironment, leftFound, rightFound] at found
            | some rightTerm =>
                simp [realizeEnvironment, leftFound, rightFound] at found
                subst values
                exact .cons (ihL.2 _ leftFound) (ihR.1 _ rightFound)
  | closure body environment ih =>
      constructor
      · intro term found
        cases environmentFound : realizeEnvironment environment with
        | none => simp [realize, environmentFound] at found
        | some values =>
            cases sourceFound : represent (() :: Context values) body with
            | none => simp [realize, environmentFound, sourceFound] at found
            | some source =>
                simp [realize, environmentFound, sourceFound] at found
                subst term
                have represented := erase_represent sourceFound
                subst body
                exact .closure (ih.2 _ environmentFound)
      · intro values found; simp [realizeEnvironment] at found
  | first value ih =>
      constructor
      · intro term found
        by_cases inactive : nonPair value = true
        · have mapped : (realize value).map first = some term := by simpa [realize, inactive] using found
          obtain ⟨before, beforeFound, same⟩ := Option.map_eq_some_iff.mp mapped
          subst term
          exact .first (ih.1 _ beforeFound) ((nonPair_iff _).mp inactive)
        · simp [realize, inactive] at found
      · intro values found; simp [realizeEnvironment] at found
  | second value ih =>
      constructor
      · intro term found
        by_cases inactive : nonPair value = true
        · have mapped : (realize value).map second = some term := by simpa [realize, inactive] using found
          obtain ⟨before, beforeFound, same⟩ := Option.map_eq_some_iff.mp mapped
          subst term
          exact .second (ih.1 _ beforeFound) ((nonPair_iff _).mp inactive)
        · simp [realize, inactive] at found
      · intro values found; simp [realizeEnvironment] at found
  | app value ih =>
      constructor
      · intro term found
        cases value with
        | pair operator argument =>
            by_cases inactive : nonClosure operator = true
            · cases operatorFound : realize operator with
              | none => simp [realize, inactive, operatorFound] at found
              | some operatorTerm =>
                  cases argumentFound : realize argument with
                  | none => simp [realize, inactive, operatorFound, argumentFound] at found
                  | some argumentTerm =>
                      simp [realize, inactive, operatorFound, argumentFound] at found
                      subst term
                      have representedPair := ih.1 (pair operatorTerm argumentTerm)
                        (by simp [realize, operatorFound, argumentFound])
                      cases representedPair with
                      | pair operatorReadback argumentReadback =>
                          exact .app operatorReadback argumentReadback ((nonClosure_iff _).mp inactive)
            · simp [realize, inactive] at found
        | literal _ _ => simp [realize] at found
        | unit | closure _ _ | first _ | second _ | app _ => simp [realize] at found
      · intro values found; simp [realizeEnvironment] at found

  | literal enabled value =>
      constructor
      · intro term found
        simp only [realize, Option.some.injEq] at found
        subst term
        exact .literal enabled value
      · intro values found
        simp [realizeEnvironment] at found

theorem realize_sound {value : SourceValue extended} {term : (Closed extended)} (represented : realize value = some term) : Readback value term :=
  (realize_sound_both value).1 term represented

theorem realizeEnvironment_sound {environment : SourceValue extended} {values : List (Closed extended)}
    (represented : realizeEnvironment environment = some values) : EnvironmentReadback environment values :=
  (realize_sound_both environment).2 values represented

theorem realize_iff (value : SourceValue extended) (term : (Closed extended)) : realize value = some term ↔ Readback value term :=
  ⟨realize_sound, Readback.realized⟩

theorem realizeEnvironment_iff (environment : SourceValue extended) (values : List (Closed extended)) :
    realizeEnvironment environment = some values ↔ EnvironmentReadback environment values :=
  ⟨realizeEnvironment_sound, EnvironmentReadback.realized⟩

theorem Readback.unique {value : SourceValue extended} {left right : (Closed extended)}
    (leftReadback : Readback value left) (rightReadback : Readback value right) : left = right :=
  Option.some.inj (leftReadback.realized.symm.trans rightReadback.realized)

theorem cbv_iff_evaluation {environment : SourceValue extended} {values : List (Closed extended)} (source : Scoped (extended := extended) (Context values))
    (captured : EnvironmentReadback environment values) (result : (Closed extended)) :
    CBV (bind (substitution values) source) result ↔
      ∃ value, CategoricalAbstractMachine.Evaluation (erase source) environment value ∧ Readback value result := by
  constructor
  · intro evaluation
    exact cbv_realization evaluation source captured rfl
  · rintro ⟨value, evaluation, readback⟩
    obtain ⟨actual, actualReadback, sourceEval⟩ := evaluation_readback evaluation source captured rfl
    have same := actualReadback.unique readback
    subst result
    exact sourceEval

/-- Native closure-code validation and scoped lambda readback are separate
checks. This operation performs both; success alone grants no historical or
publication authority to arbitrary supplied code. -/
def nativeReadback (value : NativeValue) : Option (Source extended) := do
  let source ← decodeSourceValue value
  let closed ← realize source
  pure (erase closed)


/-- The historical weak, left-to-right call-by-value strategy. Evaluation does
not enter a lambda. The right child is demanded only after the left child is
normal; projection and beta rules demand their value operands first. -/
inductive Step : (Closed extended) → (Closed extended) → Prop where
  | beta (body : Scoped (extended := extended) [()]) (argument : (Closed extended)) : Normal argument →
      Step (app (lam body) argument) (inst body argument)
  | appLeft {before after : (Closed extended)} (argument : (Closed extended)) : Step before after →
      Step (app before argument) (app after argument)
  | appRight (operator : (Closed extended)) {before after : (Closed extended)} : Normal operator → Step before after →
      Step (app operator before) (app operator after)
  | pairLeft {before after : (Closed extended)} (right : (Closed extended)) : Step before after →
      Step (pair before right) (pair after right)
  | pairRight (left : (Closed extended)) {before after : (Closed extended)} : Normal left → Step before after →
      Step (pair left before) (pair left after)
  | first {before after : (Closed extended)} : Step before after → Step (first before) (first after)
  | second {before after : (Closed extended)} : Step before after → Step (second before) (second after)
  | firstPair (left right : (Closed extended)) : Normal left → Normal right → Step (first (pair left right)) left
  | secondPair (left right : (Closed extended)) : Normal left → Normal right → Step (second (pair left right)) right
  | conditional {enabled : extended = true} {before after : Closed extended}
      (whenTrue whenFalse : Closed extended) : Step before after →
      Step (conditional enabled before whenTrue whenFalse) (conditional enabled after whenTrue whenFalse)
  | select (enabled : extended = true) (selected : Bool) (whenTrue whenFalse : Closed extended) :
      Step (conditional enabled (literal enabled (.boolean selected)) whenTrue whenFalse)
        (if selected then whenTrue else whenFalse)

abbrev Steps := Relation.ReflTransGen (Step (extended := extended))

theorem Normal.inert {term : (Closed extended)} (normal : Normal term) : ∀ {after : (Closed extended)}, ¬ Step term after := by
  induction normal with
  | literal => intro after transition; cases transition
  | lam body => intro after transition; cases transition
  | pair leftNormal rightNormal leftIH rightIH =>
      intro after transition
      cases transition with
      | pairLeft _ child => exact leftIH child
      | pairRight _ _ child => exact rightIH child
  | first normal inactive ih =>
      intro after transition
      cases transition with
      | first child => exact ih child
      | firstPair left right => simp [NotPair, erase_pair] at inactive
  | second normal inactive ih =>
      intro after transition
      cases transition with
      | second child => exact ih child
      | secondPair left right => simp [NotPair, erase_pair] at inactive
  | app operatorNormal argumentNormal inactive operatorIH argumentIH =>
      intro after transition
      cases transition with
      | beta body argument => simp [NotLam, erase_lam] at inactive
      | appLeft _ child => exact operatorIH child
      | appRight _ _ child => exact argumentIH child

theorem Steps.appLeft {before after : (Closed extended)} (trace : Steps before after) (argument : (Closed extended)) :
    Steps (app before argument) (app after argument) :=
  trace.lift (fun operator => app operator argument) (fun _ _ child => .appLeft argument child)

theorem Steps.appRight {before after : (Closed extended)} (trace : Steps before after) (operator : (Closed extended))
    (normal : Normal operator) : Steps (app operator before) (app operator after) :=
  trace.lift (app operator) (fun _ _ child => .appRight operator normal child)

theorem Steps.pairLeft {before after : (Closed extended)} (trace : Steps before after) (right : (Closed extended)) :
    Steps (pair before right) (pair after right) :=
  trace.lift (fun left => pair left right) (fun _ _ child => .pairLeft right child)

theorem Steps.pairRight {before after : (Closed extended)} (trace : Steps before after) (left : (Closed extended))
    (normal : Normal left) : Steps (pair left before) (pair left after) :=
  trace.lift (pair left) (fun _ _ child => .pairRight left normal child)

theorem Steps.first {before after : (Closed extended)} (trace : Steps before after) : Steps (first before) (first after) :=
  trace.lift Lambda.first (fun _ _ child => Step.first child)

theorem Steps.second {before after : (Closed extended)} (trace : Steps before after) : Steps (second before) (second after) :=
  trace.lift Lambda.second (fun _ _ child => Step.second child)

theorem Steps.conditional {enabled : extended = true} {before after : Closed extended}
    (trace : Steps before after) (whenTrue whenFalse : Closed extended) :
    Steps (conditional enabled before whenTrue whenFalse) (conditional enabled after whenTrue whenFalse) :=
  trace.lift (fun condition => Lambda.conditional enabled condition whenTrue whenFalse)
    (fun _ _ child => .conditional whenTrue whenFalse child)

theorem ProjectionFirst.steps {term result : (Closed extended)} (projection : ProjectionFirst term result)
    (normal : Normal term) : Steps (first term) result := by
  cases projection with
  | pair left right =>
      cases normal with
      | pair leftNormal rightNormal => exact .single (.firstPair _ _ leftNormal rightNormal)
  | neutral => exact .refl

theorem ProjectionSecond.steps {term result : (Closed extended)} (projection : ProjectionSecond term result)
    (normal : Normal term) : Steps (second term) result := by
  cases projection with
  | pair left right =>
      cases normal with
      | pair leftNormal rightNormal => exact .single (.secondPair _ _ leftNormal rightNormal)
  | neutral => exact .refl

theorem CBV.steps {term result : (Closed extended)} (evaluation : CBV term result) : Steps term result := by
  induction evaluation using CBV.rec
      (motive_2 := fun operator argument result _ => Normal operator → Normal argument →
        Steps (Lambda.app operator argument) result) with
  | literal => exact .refl
  | @conditional enabled _ whenTrue whenFalse _ selected _ _ conditionIH selectedIH =>
      exact (conditionIH.conditional whenTrue whenFalse).trans (.head (.select enabled selected _ _) selectedIH)
  | lam => exact .refl
  | pair leftEval _ leftIH rightIH =>
      exact (leftIH.pairLeft _).trans (rightIH.pairRight _ leftEval.normal)
  | app operatorEval argumentEval _ operatorIH argumentIH callIH =>
      exact ((operatorIH.appLeft _).trans (argumentIH.appRight _ operatorEval.normal)).trans
        (callIH operatorEval.normal argumentEval.normal)
  | first evaluation projection ih => exact ih.first.trans (projection.steps evaluation.normal)
  | second evaluation projection ih => exact ih.second.trans (projection.steps evaluation.normal)
  | beta _ ih => exact .head (.beta _ _ ‹Normal _›) ih
  | neutral => exact .refl

/-- One source step can be prepended to a completed source derivation. This
is a property of the independent strategy, not of the instruction executor. -/
theorem Step.rewind {before after : (Closed extended)} (transition : Step before after) :
    ∀ {result : (Closed extended)}, CBV after result → CBV before result := by
  induction transition with
  | conditional whenTrue whenFalse child ih =>
      intro result evaluation
      cases evaluation with
      | conditional conditionEval selectedEval => exact .conditional (ih conditionEval) selectedEval
  | select enabled selected whenTrue whenFalse =>
      intro result evaluation
      exact .conditional (.literal enabled (.boolean selected)) evaluation

  | beta body argument normal =>
      intro result evaluation
      exact .app (.lam body) normal.evaluation (.beta evaluation)
  | appLeft argument child ih =>
      intro result evaluation
      cases evaluation with
      | app operatorEval argumentEval invocation => exact .app (ih operatorEval) argumentEval invocation
  | appRight operator normal child ih =>
      intro result evaluation
      cases evaluation with
      | app operatorEval argumentEval invocation => exact .app operatorEval (ih argumentEval) invocation
  | pairLeft right child ih =>
      intro result evaluation
      cases evaluation with
      | pair leftEval rightEval => exact .pair (ih leftEval) rightEval
  | pairRight left normal child ih =>
      intro result evaluation
      cases evaluation with
      | pair leftEval rightEval => exact .pair leftEval (ih rightEval)
  | first child ih =>
      intro result evaluation
      cases evaluation with
      | first evaluation projection => exact .first (ih evaluation) projection
  | second child ih =>
      intro result evaluation
      cases evaluation with
      | second evaluation projection => exact .second (ih evaluation) projection
  | firstPair left right leftNormal rightNormal =>
      intro result evaluation
      exact .first (.pair evaluation rightNormal.evaluation) (.pair _ _)
  | secondPair left right leftNormal rightNormal =>
      intro result evaluation
      exact .second (.pair leftNormal.evaluation evaluation) (.pair _ _)

theorem Steps.rewind {before after : (Closed extended)} (trace : Steps before after) {result : (Closed extended)}
    (evaluation : CBV after result) : CBV before result := by
  induction trace using Relation.ReflTransGen.head_induction_on with
  | refl => exact evaluation
  | head transition _ ih => exact transition.rewind ih

theorem cbv_iff_steps_normal (term result : (Closed extended)) : CBV term result ↔ Steps term result ∧ Normal result :=
  ⟨fun evaluation => ⟨evaluation.steps, evaluation.normal⟩,
    fun ⟨trace, normal⟩ => trace.rewind normal.evaluation⟩


@[simp] theorem close_empty (source : (Closed extended)) : bind (substitution []) source = source := by
  have empty : (substitution [] : Sub (signature extended) [] []) =
      (fun (sort : Unit) (variable_ : Var [] sort) => @Term.var (signature extended) [] sort variable_) := by
    funext sort variable_
    cases variable_
  rw [empty]
  exact bind_id source

/-- Proposition 3.2 with arbitrary captured scope: source substitution and
weak evaluation agree with combinatory execution and exact closed readback.
The environment witness contains independently judged source values. -/
theorem source_iff_combinatory {environment : SourceValue extended} {values : List (Closed extended)}
    (source : Scoped (extended := extended) (Context values)) (captured : EnvironmentReadback environment values) (result : (Closed extended)) :
    Steps (bind (substitution values) source) result ∧ Normal result ↔
      ∃ value, CombinatorySteps (.question (erase source) environment) (.answer value) ∧ Readback value result := by
  rw [← cbv_iff_steps_normal, cbv_iff_evaluation source captured]
  constructor
  · rintro ⟨value, evaluation, readback⟩
    exact ⟨value, evaluation.combinatory, readback⟩
  · rintro ⟨value, execution, readback⟩
    exact ⟨value, (combinatory_iff_evaluation _ _ _).mp execution, readback⟩

/-- The closed-term statement of Proposition 3.2, for the augmented neutral
completion profile in Table 5. No reduction under a lambda is admitted. -/
theorem proposition_3_2 (source result : (Closed extended)) :
    Steps source result ∧ Normal result ↔
      ∃ value, CombinatorySteps (.question (erase source) .unit) (.answer value) ∧ Readback value result := by
  simpa only [close_empty] using source_iff_combinatory (values := []) source EnvironmentReadback.nil result

/-- Exact correspondence with the constructed instruction compiler. Both
terminal code and terminal stack are empty; captured environments remain
present in the native closure payload. -/
theorem source_iff_execution {environment : SourceValue extended} {values : List (Closed extended)}
    (source : Scoped (extended := extended) (Context values)) (captured : EnvironmentReadback environment values) (result : (Closed extended)) :
    Steps (bind (substitution values) source) result ∧ Normal result ↔
      ∃ value, CategoricalAbstractMachine.Steps .neutral
        ⟨encodeSourceValue environment, compileSource (erase source), []⟩ ⟨encodeSourceValue value, [], []⟩ ∧ Readback value result := by
  rw [source_iff_combinatory source captured]
  constructor
  · rintro ⟨value, execution, readback⟩
    exact ⟨value, (combinatory_iff_execution _ _ _).mp execution, readback⟩
  · rintro ⟨value, execution, readback⟩
    exact ⟨value, (combinatory_iff_execution _ _ _).mpr execution, readback⟩

theorem nativeReadback_iff (native : NativeValue) (expression : Source extended) :
    nativeReadback native = some expression ↔
      ∃ value closed, decodeSourceValue native = some value ∧ Readback value closed ∧ erase closed = expression := by
  constructor
  · intro found
    cases decoded : decodeSourceValue native with
    | none => simp [nativeReadback, decoded] at found
    | some value =>
        cases realized : realize value with
        | none => simp [nativeReadback, decoded, realized] at found
        | some closed =>
            have same : erase closed = expression := by simpa [nativeReadback, decoded, realized] using found
            exact ⟨value, closed, rfl, realize_sound realized, same⟩
  · rintro ⟨value, closed, decoded, readback, same⟩
    simp [nativeReadback, decoded, readback.realized, same]

@[simp] theorem nativeReadback_encode {value : SourceValue extended} {closed : (Closed extended)} (readback : Readback value closed) :
    nativeReadback (encodeSourceValue value) = some (erase closed) := by
  simp [nativeReadback, readback.realized]

/-- Executable source readback of any result produced by compiled scoped
code is precisely the independently evaluated source result. Raw code is not
assigned source validity merely because its instruction stream terminates. -/
theorem source_iff_nativeReadback {environment : SourceValue extended} {values : List (Closed extended)}
    (source : Scoped (extended := extended) (Context values)) (captured : EnvironmentReadback environment values) (result : (Closed extended)) :
    Steps (bind (substitution values) source) result ∧ Normal result ↔
      ∃ native, CategoricalAbstractMachine.Steps .neutral
        ⟨encodeSourceValue environment, compileSource (erase source), []⟩ ⟨native, [], []⟩ ∧
          nativeReadback native = some (erase result) := by
  constructor
  · intro reduction
    obtain ⟨value, execution, readback⟩ := (source_iff_execution source captured result).mp reduction
    exact ⟨encodeSourceValue value, execution, nativeReadback_encode readback⟩
  · rintro ⟨native, execution, found⟩
    obtain ⟨value, evaluation, same⟩ := execution_complete execution
    rw [← same] at found
    obtain ⟨decoded, closed, decodeFound, readback, erased⟩ := (nativeReadback_iff _ _).mp found
    have equalValue : value = decoded := Option.some.inj ((decode_encodeValue value).symm.trans decodeFound)
    subst decoded
    have equalTerm := erase_injective erased
    subst closed
    exact (cbv_iff_steps_normal _ _).mp ((cbv_iff_evaluation source captured result).mpr
      ⟨value, evaluation, readback⟩)

theorem closed_iff_nativeReadback (source result : (Closed extended)) :
    Steps source result ∧ Normal result ↔
      ∃ native, CategoricalAbstractMachine.Steps .neutral
        ⟨.unit, compileSource (erase source), []⟩ ⟨native, [], []⟩ ∧ nativeReadback native = some (erase result) := by
  simpa only [close_empty, encodeSourceValue] using source_iff_nativeReadback (values := []) source EnvironmentReadback.nil result

/-- Source correspondence also holds at the common runner's completed
answer boundary. The existing instruction occurrence and resumption accounts
remain separate from source reductions and from host instruction costs. -/
theorem source_iff_finished {environment : SourceValue extended} {values : List (Closed extended)}
    (source : Scoped (extended := extended) (Context values)) (captured : EnvironmentReadback environment values) (result : (Closed extended)) :
    Steps (bind (substitution values) source) result ∧ Normal result ↔
      ∃ budget events native,
        (machine .neutral).run budget ⟨encodeSourceValue environment, compileSource (erase source), []⟩ =
          (events, .finished native) ∧ nativeReadback native = some (erase result) := by
  rw [← cbv_iff_steps_normal, cbv_iff_evaluation source captured]
  constructor
  · rintro ⟨value, evaluation, readback⟩
    obtain ⟨budget, events, completed⟩ := (evaluation_iff_finished _ _ _).mp evaluation
    exact ⟨budget, events, encodeSourceValue value, completed, nativeReadback_encode readback⟩
  · rintro ⟨budget, events, native, completed, found⟩
    have produced : (sourceAnswerCore extended .neutral).Produces (erase source, environment) native :=
      (ProductiveCoreAdapters.produces_iff_finished _ _ _).mpr ⟨budget, events, completed⟩
    obtain ⟨value, evaluation, same⟩ := (sourceProduces_iff_evaluation _ _ _).mp produced
    rw [← same] at found
    obtain ⟨decoded, closed, decodeFound, readback, erased⟩ := (nativeReadback_iff _ _).mp found
    have equalValue : value = decoded := Option.some.inj ((decode_encodeValue value).symm.trans decodeFound)
    subst decoded
    have equalTerm := erase_injective erased
    subst closed
    exact ⟨value, evaluation, readback⟩

/-- Completed source evaluation has a unique result; this follows through
constructed readback and actual deterministic CAM execution. -/
theorem CBV.unique {term left right : (Closed extended)} (one : CBV term left) (two : CBV term right) : left = right := by
  obtain ⟨first, firstEval, firstReadback⟩ := (cbv_iff_evaluation (values := []) term EnvironmentReadback.nil left).mp
    (by simpa only [close_empty] using one)
  obtain ⟨second, secondEval, secondReadback⟩ := (cbv_iff_evaluation (values := []) term EnvironmentReadback.nil right).mp
    (by simpa only [close_empty] using two)
  have same := CategoricalAbstractMachine.Evaluation.unique firstEval secondEval
  subst second
  exact firstReadback.unique secondReadback


/-- A changed right child witnesses that the source strategy had already
completed its left operand. This order constraint is independent of the CAM
compiler or its instruction schedule. -/
theorem Step.right_demand {operator before after : (Closed extended)}
    (transition : Step (Lambda.app operator before) (Lambda.app operator after))
    (changed : before ≠ after) : Normal operator := by
  generalize beforeEq : Lambda.app operator before = source at transition
  generalize afterEq : Lambda.app operator after = target at transition
  cases transition with
  | beta body argument normal =>
      have same := (app_inj beforeEq).1
      rw [same]
      exact .lam body
  | appLeft argument child =>
      exact False.elim (changed ((app_inj beforeEq).2.trans (app_inj afterEq).2.symm))
  | appRight left normal child =>
      rw [(app_inj beforeEq).1]
      exact normal
  | pairLeft | pairRight | first | second | firstPair | secondPair | conditional | select =>
      have impossible := congrArg erase beforeEq
      simp only [erase_app, erase_pair, erase_first, erase_second, erase_conditional, reduceCtorEq] at impossible

theorem Step.pair_right_demand {left before after : (Closed extended)}
    (transition : Step (Lambda.pair left before) (Lambda.pair left after))
    (changed : before ≠ after) : Normal left := by
  generalize beforeEq : Lambda.pair left before = source at transition
  generalize afterEq : Lambda.pair left after = target at transition
  cases transition with
  | pairLeft right child =>
      exact False.elim (changed ((pair_inj beforeEq).2.trans (pair_inj afterEq).2.symm))
  | pairRight first normal child =>
      rw [(pair_inj beforeEq).1]
      exact normal
  | beta | appLeft | appRight | first | second | firstPair | secondPair | conditional | select =>
      have impossible := congrArg erase beforeEq
      simp only [erase_pair, erase_app, erase_first, erase_second, erase_conditional, reduceCtorEq] at impossible

end Lambda


/-! ## Typed categorical meaning of the existing CAM source grammar

The source annotations below use the existing generated cartesian-closed
category's objects and morphisms. They do not introduce a new term language,
category, compiler or executor. Types retain their formation evidence and
categorical values retain their actual closure body and captured environment.
-/

noncomputable section

namespace Typed

open _root_.CategoryTheory
open Mettapedia.CategoryTheory.RelativeClosedSyntax
open GeneratedCategory

universe u v a

variable {C : Type u} [Category.{v} C] {symbols : Symbols.{a}}
variable {signature : Signature (C := C) (symbols := symbols)}

abbrev TypeOf (signature : Signature (C := C) (symbols := symbols)) := Object signature

/-- Categorical environments retain the oldest context on the left and its
newest argument on the right, as in the actual CAM register representation. -/
@[reducible] def context : List (TypeOf signature) → TypeOf signature
  | [] => terminal signature
  | argument :: rest => product (context rest) argument

/-- Independent simple typing of the existing de Bruijn source grammar.
Annotations affect this judgment; the runtime expression stays unchanged. -/
inductive Typing : List (TypeOf signature) → Expr → TypeOf signature → Type (max u v a) where
  | varZero (rest : List (TypeOf signature)) (argument : TypeOf signature) :
      Typing (argument :: rest) (.var 0) argument
  | varSucc {rest : List (TypeOf signature)} {index : Nat} {result : TypeOf signature}
      (argument : TypeOf signature) (previous : Typing rest (.var index) result) :
      Typing (argument :: rest) (.var (index + 1)) result
  | lam {rest : List (TypeOf signature)} {body : Expr} {argument result : TypeOf signature}
      (typed : Typing (argument :: rest) body result) :
      Typing rest (.lam body) (exponentialObject argument result)
  | app {rest : List (TypeOf signature)} {operator argument : Expr} {domain result : TypeOf signature}
      (function : Typing rest operator (exponentialObject domain result))
      (operand : Typing rest argument domain) : Typing rest (.app operator argument) result
  | pair {rest : List (TypeOf signature)} {left right : Expr} {first second : TypeOf signature}
      (leftTyped : Typing rest left first) (rightTyped : Typing rest right second) :
      Typing rest (.pair left right) (product first second)
  | first {rest : List (TypeOf signature)} {term : Expr} {left right : TypeOf signature}
      (typed : Typing rest term (product left right)) : Typing rest (.first term) left
  | second {rest : List (TypeOf signature)} {term : Expr} {left right : TypeOf signature}
      (typed : Typing rest term (product left right)) : Typing rest (.second term) right

/-- The source morphism is constructed with actual projections, categorical
abstraction and evaluation. Its formation is supplied by the existing CCC. -/
def Typing.denote : {rest : List (TypeOf signature)} → {term : Expr} → {result : TypeOf signature} →
    Typing rest term result → (context rest ⟶ result)
  | _, _, _, .varZero rest argument => GeneratedCategory.second (context rest) argument
  | _, _, _, .varSucc argument previous => GeneratedCategory.first _ argument ≫ previous.denote
  | _, _, _, .lam typed => abstraction typed.denote
  | _, _, _, .app function operand => pairing function.denote operand.denote ≫ evaluation _ _
  | _, _, _, .pair left right => pairing left.denote right.denote
  | _, _, _, .first typed => typed.denote ≫ GeneratedCategory.first _ _
  | _, _, _, .second typed => typed.denote ≫ GeneratedCategory.second _ _

/-- A typing derivation constructs an exact representation in the existing
scoped binding syntax at every binder depth. This is syntax evidence only. -/
theorem Typing.represented {rest : List (TypeOf signature)} {term : Expr} {result : TypeOf signature}
    (typed : Typing rest term result) :
    ∃ source : Lambda.Scoped (List.replicate rest.length ()),
      Lambda.represent (List.replicate rest.length ()) term = some source := by
  induction typed with
  | varZero rest argument =>
      exact ⟨.var .zero, rfl⟩
  | @varSucc rest index result argument previous ih =>
      obtain ⟨source, represented⟩ := ih
      obtain ⟨variable_, found, same⟩ := Option.map_eq_some_iff.mp
        (by simpa only [Lambda.represent] using represented)
      refine ⟨.var (.succ variable_), ?_⟩
      simp only [List.length_cons, List.replicate_succ, Lambda.represent, Lambda.slot?, found,
        Option.map_some]
  | lam typed ih =>
      obtain ⟨body, represented⟩ := ih
      simp only [List.length_cons, List.replicate_succ] at body represented
      exact ⟨Lambda.lam body, by simp only [Lambda.represent, represented, Option.map_some]⟩
  | app function operand functionIH operandIH =>
      obtain ⟨operator, operatorRepresented⟩ := functionIH
      obtain ⟨argument, argumentRepresented⟩ := operandIH
      exact ⟨Lambda.app operator argument,
        by simp only [Lambda.represent, operatorRepresented, argumentRepresented]; rfl⟩
  | pair left right leftIH rightIH =>
      obtain ⟨leftSource, leftRepresented⟩ := leftIH
      obtain ⟨rightSource, rightRepresented⟩ := rightIH
      exact ⟨Lambda.pair leftSource rightSource,
        by simp only [Lambda.represent, leftRepresented, rightRepresented]; rfl⟩
  | first typed ih =>
      obtain ⟨source, represented⟩ := ih
      exact ⟨Lambda.first source, by simp only [Lambda.represent, represented, Option.map_some]⟩
  | second typed ih =>
      obtain ⟨source, represented⟩ := ih
      exact ⟨Lambda.second source, by simp only [Lambda.represent, represented, Option.map_some]⟩

theorem Typing.scoped {rest : List (TypeOf signature)} {term : Expr} {result : TypeOf signature}
    (typed : Typing rest term result) :
    ∃ source : Lambda.Scoped (List.replicate rest.length ()), Lambda.erase source = term := by
  obtain ⟨source, represented⟩ := typed.represented
  exact ⟨source, Lambda.erase_represent represented⟩

theorem Typing.lambda_type {rest : List (TypeOf signature)} {body : Expr} {result : TypeOf signature}
    (typed : Typing rest (.lam body) result) :
    ∃ argument codomain, result = exponentialObject argument codomain := by
  cases typed with
  | lam typed => exact ⟨_, _, rfl⟩

theorem Typing.variable_zero_type {rest : List (TypeOf signature)} {argument result : TypeOf signature}
    (typed : Typing (argument :: rest) (.var 0) result) : result = argument := by
  cases typed
  rfl

mutual
/-- A categorical meaning of an actual source-bodied value at an arbitrary
ambient object. The unit case is the actual terminal environment value; it
is not a claim of lambda readback or source publication authority. -/
inductive ValueMeaning (ambient : TypeOf signature) :
    (value : Value) → (result : TypeOf signature) → (ambient ⟶ result) → Prop where
  | unit : ValueMeaning ambient .unit (terminal signature) (toTerminal ambient)
  | pair {left right : Value} {first second : TypeOf signature}
      {leftArrow : ambient ⟶ first} {rightArrow : ambient ⟶ second}
      (leftMeaning : ValueMeaning ambient left first leftArrow)
      (rightMeaning : ValueMeaning ambient right second rightArrow) :
      ValueMeaning ambient (.pair left right) (product first second) (pairing leftArrow rightArrow)
  | closure {rest : List (TypeOf signature)} {body : Expr} {environment : Value}
      {argument result : TypeOf signature} {capturedArrow : ambient ⟶ context rest}
      (typed : Typing (argument :: rest) body result)
      (captured : EnvironmentMeaning ambient environment rest capturedArrow) :
      ValueMeaning ambient (.closure body environment) (exponentialObject argument result)
        (capturedArrow ≫ abstraction typed.denote)

inductive EnvironmentMeaning (ambient : TypeOf signature) :
    (environment : Value) → (rest : List (TypeOf signature)) → (ambient ⟶ context rest) → Prop where
  | nil : EnvironmentMeaning ambient .unit [] (toTerminal ambient)
  | cons {environment value : Value} {rest : List (TypeOf signature)} {argument : TypeOf signature}
      {environmentArrow : ambient ⟶ context rest} {valueArrow : ambient ⟶ argument}
      (captured : EnvironmentMeaning ambient environment rest environmentArrow)
      (argumentMeaning : ValueMeaning ambient value argument valueArrow) :
      EnvironmentMeaning ambient (.pair environment value) (argument :: rest) (pairing environmentArrow valueArrow)
end

private theorem product_injective {left right first second : TypeOf signature}
    (same : product left right = product first second) : left = first ∧ right = second := by
  have codes := congrArg Object.code same
  obtain ⟨leftCode, rightCode⟩ := ObjectCode.product.inj codes
  exact ⟨Object.ext leftCode, Object.ext rightCode⟩

private theorem exponential_injective {left right first second : TypeOf signature}
    (same : exponentialObject left right = exponentialObject first second) :
    left = first ∧ right = second := by
  have codes := congrArg Object.code same
  obtain ⟨leftCode, rightCode⟩ := ObjectCode.exponential.inj codes
  exact ⟨Object.ext leftCode, Object.ext rightCode⟩

theorem EnvironmentMeaning.second {ambient argument : TypeOf signature}
    {rest : List (TypeOf signature)} {environment value : Value}
    {environmentArrow : ambient ⟶ context (argument :: rest)}
    (captured : EnvironmentMeaning ambient environment (argument :: rest) environmentArrow)
    (projection : Second environment value) :
    ValueMeaning ambient value argument
      (environmentArrow ≫ GeneratedCategory.second (context rest) argument) := by
  cases captured with
  | @cons previousValue argumentValue previousRest previousArgument environmentArrow valueArrow previous argumentMeaning =>
      cases projection with
      | pair =>
          change ValueMeaning ambient value argument
            (pairing environmentArrow valueArrow ≫ GeneratedCategory.second (context rest) argument)
          rw [GeneratedCategory.pairing_second]
          exact argumentMeaning
      | neutral value inactive => exact False.elim inactive

theorem EnvironmentMeaning.first {ambient argument : TypeOf signature}
    {rest : List (TypeOf signature)} {environment value : Value}
    {environmentArrow : ambient ⟶ context (argument :: rest)}
    (captured : EnvironmentMeaning ambient environment (argument :: rest) environmentArrow)
    (projection : First environment value) :
    EnvironmentMeaning ambient value rest
      (environmentArrow ≫ GeneratedCategory.first (context rest) argument) := by
  cases captured with
  | @cons previousValue argumentValue previousRest previousArgument environmentArrow valueArrow previous argumentMeaning =>
      cases projection with
      | pair =>
          change EnvironmentMeaning ambient value rest
            (pairing environmentArrow valueArrow ≫ GeneratedCategory.first (context rest) argument)
          rw [GeneratedCategory.pairing_first]
          exact previous
      | neutral value inactive => exact False.elim inactive

private theorem ValueMeaning.pair_case {ambient actual : TypeOf signature}
    {before : Value} {arrow : ambient ⟶ actual}
    (meaning : ValueMeaning ambient before actual arrow) {left right : TypeOf signature}
    (same : actual = product left right) :
    ∃ (leftValue rightValue : Value) (leftArrow : ambient ⟶ left) (rightArrow : ambient ⟶ right),
      before = .pair leftValue rightValue ∧ HEq arrow (pairing leftArrow rightArrow) ∧
      ValueMeaning ambient leftValue left leftArrow ∧ ValueMeaning ambient rightValue right rightArrow := by
  cases meaning with
  | unit =>
      have codes := congrArg Object.code same
      cases codes
  | @pair beforeLeft beforeRight actualLeft actualRight leftArrow rightArrow leftMeaning rightMeaning =>
      obtain ⟨leftSame, rightSame⟩ := product_injective same
      subst actualLeft
      subst actualRight
      exact ⟨_, _, _, _, rfl, HEq.rfl, leftMeaning, rightMeaning⟩
  | closure =>
      have codes := congrArg Object.code same
      cases codes

theorem ValueMeaning.first {ambient left right : TypeOf signature}
    {before value : Value} {arrow : ambient ⟶ product left right}
    (meaning : ValueMeaning ambient before (product left right) arrow)
    (projection : First before value) :
    ValueMeaning ambient value left (arrow ≫ GeneratedCategory.first left right) := by
  obtain ⟨leftValue, rightValue, leftArrow, rightArrow, sameValue, sameArrow, leftMeaning, _⟩ :=
    meaning.pair_case rfl
  subst before
  have arrowSame : arrow = pairing leftArrow rightArrow := eq_of_heq sameArrow
  subst arrow
  cases projection with
  | pair => simpa only [GeneratedCategory.pairing_first] using leftMeaning
  | neutral _ inactive => exact False.elim inactive

theorem ValueMeaning.second {ambient left right : TypeOf signature}
    {before value : Value} {arrow : ambient ⟶ product left right}
    (meaning : ValueMeaning ambient before (product left right) arrow)
    (projection : Second before value) :
    ValueMeaning ambient value right (arrow ≫ GeneratedCategory.second left right) := by
  obtain ⟨leftValue, rightValue, leftArrow, rightArrow, sameValue, sameArrow, _, rightMeaning⟩ :=
    meaning.pair_case rfl
  subst before
  have arrowSame : arrow = pairing leftArrow rightArrow := eq_of_heq sameArrow
  subst arrow
  cases projection with
  | pair => simpa only [GeneratedCategory.pairing_second] using rightMeaning
  | neutral _ inactive => exact False.elim inactive

private theorem ValueMeaning.closure_case {ambient actual : TypeOf signature}
    {before : Value} {arrow : ambient ⟶ actual}
    (meaning : ValueMeaning ambient before actual arrow) {argument result : TypeOf signature}
    (same : actual = exponentialObject argument result) :
    ∃ (rest : List (TypeOf signature)) (body : Expr) (environment : Value)
      (typed : Typing (argument :: rest) body result) (capturedArrow : ambient ⟶ context rest),
      before = .closure body environment ∧ HEq arrow (capturedArrow ≫ abstraction typed.denote) ∧
      EnvironmentMeaning ambient environment rest capturedArrow := by
  cases meaning with
  | unit =>
      have codes := congrArg Object.code same
      cases codes
  | pair =>
      have codes := congrArg Object.code same
      cases codes
  | @closure rest body environment actualArgument actualResult capturedArrow typed captured =>
      obtain ⟨argumentSame, resultSame⟩ := exponential_injective same
      subst actualArgument
      subst actualResult
      exact ⟨rest, body, environment, typed, capturedArrow, rfl, HEq.rfl, captured⟩

/-- Evaluating a constructed closure at an argument is the existing CCC beta
equation at the complete captured environment, for any ambient object. -/
theorem closure_application {ambient environment argument result : TypeOf signature}
    (captured : ambient ⟶ environment) (operand : ambient ⟶ argument)
    (body : product environment argument ⟶ result) :
    pairing (captured ≫ abstraction body) operand ≫ evaluation argument result =
      pairing captured operand ≫ body := by
  have beta := congrArg (fun (arrow : product environment argument ⟶ result) =>
    pairing captured operand ≫ arrow) (unabstract_abstraction body)
  unfold unabstract at beta
  rw [← Category.assoc, pairing_precompose] at beta
  simpa only [← Category.assoc,
    GeneratedCategory.pairing_first, GeneratedCategory.pairing_second] using beta

/-- Completed source evaluation realizes its constructed categorical morphism.
The proof follows the independent source and invocation judgments, rather than
defining the result meaning to be the evaluator's result. -/
theorem evaluation_meaning {term : Expr} {environment value : Value}
    (evaluated : Evaluation term environment value) :
    ∀ {rest : List (TypeOf signature)} {result ambient : TypeOf signature}
      (typed : Typing rest term result) {capturedArrow : ambient ⟶ context rest},
      EnvironmentMeaning ambient environment rest capturedArrow →
      ValueMeaning ambient value result (capturedArrow ≫ typed.denote) := by
  induction evaluated using Evaluation.rec
    (motive_2 := fun function argument value _ =>
      ∀ {domain result ambient : TypeOf signature}
        {functionArrow : ambient ⟶ exponentialObject domain result}
        {argumentArrow : ambient ⟶ domain},
        ValueMeaning ambient function (exponentialObject domain result) functionArrow →
        ValueMeaning ambient argument domain argumentArrow →
        ValueMeaning ambient value result
          (pairing functionArrow argumentArrow ≫ evaluation domain result)) with
  | varZero projection =>
      intro rest result ambient typed capturedArrow captured
      cases typed with
      | varZero => exact captured.second projection
  | varSucc projection restEval restIH =>
      intro rest result ambient typed capturedArrow captured
      cases typed with
      | varSucc argument previous =>
          have meaning := restIH previous (captured.first projection)
          simpa only [Typing.denote, Category.assoc] using meaning
  | lam body environment =>
      intro rest result ambient typed capturedArrow captured
      cases typed with
      | lam bodyTyped => exact .closure bodyTyped captured
  | pair leftEval rightEval leftIH rightIH =>
      intro rest result ambient typed capturedArrow captured
      cases typed with
      | pair leftTyped rightTyped =>
          have meaning := ValueMeaning.pair (leftIH leftTyped captured) (rightIH rightTyped captured)
          simpa only [Typing.denote, pairing_precompose] using meaning
  | app operatorEval argumentEval invocation operatorIH argumentIH invocationIH =>
      intro rest result ambient typed capturedArrow captured
      cases typed with
      | app functionTyped argumentTyped =>
          have meaning := invocationIH (operatorIH functionTyped captured) (argumentIH argumentTyped captured)
          simpa only [Typing.denote, ← Category.assoc, pairing_precompose] using meaning
  | first termEval projection termIH =>
      intro rest result ambient typed capturedArrow captured
      cases typed with
      | first termTyped =>
          have meaning := (termIH termTyped captured).first projection
          simpa only [Typing.denote, Category.assoc] using meaning
  | second termEval projection termIH =>
      intro rest result ambient typed capturedArrow captured
      cases typed with
      | second termTyped =>
          have meaning := (termIH termTyped captured).second projection
          simpa only [Typing.denote, Category.assoc] using meaning
  | @closure body environment argument value bodyEval bodyIH =>
      rename_i domain result ambient functionArrow argumentArrow functionMeaning argumentMeaning
      obtain ⟨rest, body, environment, bodyTyped, capturedArrow, sameValue, sameArrow, captured⟩ :=
        functionMeaning.closure_case rfl
      have sameBody := SourceValue.closure.inj sameValue
      obtain ⟨rfl, rfl⟩ := sameBody
      have arrowSame : functionArrow = capturedArrow ≫ abstraction bodyTyped.denote := eq_of_heq sameArrow
      subst functionArrow
      have meaning := bodyIH bodyTyped (EnvironmentMeaning.cons captured argumentMeaning)
      simpa only [closure_application] using meaning
  | neutral function argument inactive =>
      rename_i domain result ambient functionArrow argumentArrow functionMeaning argumentMeaning
      obtain ⟨rest, body, environment, typed, capturedArrow, sameValue, sameArrow, captured⟩ :=
        functionMeaning.closure_case rfl
      subst function
      exact False.elim inactive

  | @literal enabled _ _ | @conditional enabled _ _ _ _ _ _ _ _ _ _ => cases enabled

theorem EnvironmentMeaning.value {ambient : TypeOf signature}
    {environment : Value} {rest : List (TypeOf signature)}
    {arrow : ambient ⟶ context rest}
    (captured : EnvironmentMeaning ambient environment rest arrow) :
    ValueMeaning ambient environment (context rest) arrow := by
  induction environment generalizing rest with
  | unit => cases captured; exact .unit
  | pair environment value previous _ =>
      cases captured with
      | cons environmentMeaning valueMeaning => exact .pair (previous environmentMeaning) valueMeaning
  | literal enabled _ => cases enabled
  | closure | first | second | app => cases captured

private theorem strict_first {ambient left right : TypeOf signature}
    {before value : Value} {arrow : ambient ⟶ product left right}
    (meaning : ValueMeaning ambient before (product left right) arrow)
    (projection : First before value) (code : Code) (stack : List NativeValue) :
    Transition .strict ⟨encodeSourceValue before, .first :: code, stack⟩
      ⟨encodeSourceValue value, code, stack⟩ := by
  obtain ⟨leftValue, rightValue, leftArrow, rightArrow, sameValue, sameArrow, leftMeaning, rightMeaning⟩ :=
    meaning.pair_case rfl
  subst before
  cases projection with
  | pair => exact .firstPair .strict _ _ _ _
  | neutral _ inactive => exact False.elim inactive

private theorem strict_second {ambient left right : TypeOf signature}
    {before value : Value} {arrow : ambient ⟶ product left right}
    (meaning : ValueMeaning ambient before (product left right) arrow)
    (projection : Second before value) (code : Code) (stack : List NativeValue) :
    Transition .strict ⟨encodeSourceValue before, .second :: code, stack⟩
      ⟨encodeSourceValue value, code, stack⟩ := by
  obtain ⟨leftValue, rightValue, leftArrow, rightArrow, sameValue, sameArrow, leftMeaning, rightMeaning⟩ :=
    meaning.pair_case rfl
  subst before
  cases projection with
  | pair => exact .secondPair .strict _ _ _ _
  | neutral _ inactive => exact False.elim inactive

/-- Every completed typed evaluation follows the original active Table 1
profile, with arbitrary instruction suffix and retained stack. Inactive
projection and application rules are excluded by constructed value shapes. -/
theorem strict_execution_tail {term : Expr} {environment value : Value}
    (evaluated : Evaluation term environment value) :
    ∀ {rest : List (TypeOf signature)} {result ambient : TypeOf signature}
      (_typed : Typing rest term result) {capturedArrow : ambient ⟶ context rest},
      EnvironmentMeaning ambient environment rest capturedArrow →
      ∀ (code : Code) (stack : List NativeValue),
        Steps .strict ⟨encodeSourceValue environment, compileSource term ++ code, stack⟩
          ⟨encodeSourceValue value, code, stack⟩ := by
  induction evaluated using Evaluation.rec
    (motive_2 := fun function argument value _ =>
      ∀ {domain result ambient : TypeOf signature}
        {functionArrow : ambient ⟶ exponentialObject domain result}
        {argumentArrow : ambient ⟶ domain},
        ValueMeaning ambient function (exponentialObject domain result) functionArrow →
        ValueMeaning ambient argument domain argumentArrow →
        ∀ (code : Code) (stack : List NativeValue),
          Steps .strict ⟨.pair (encodeSourceValue function) (encodeSourceValue argument), .app :: code, stack⟩
            ⟨encodeSourceValue value, code, stack⟩) with
  | varZero projection =>
      intro rest result ambient typed capturedArrow captured code stack
      cases typed with
      | varZero => exact .single (strict_second captured.value projection code stack)
  | @varSucc index environment before value projection restEval restIH =>
      intro rest result ambient typed capturedArrow captured code stack
      cases typed with
      | varSucc argument previous =>
          have transition := strict_first captured.value projection (compileSource (extended := false) (.var index) ++ code) stack
          have restRun := restIH previous (captured.first projection) code stack
          simpa only [compile_var_succ, List.cons_append] using restRun.head transition
  | lam =>
      intro rest result ambient typed capturedArrow captured code stack
      exact .single (.cur .strict _ _ _ _)
  | @pair left right environment first second leftEval rightEval leftIH rightIH =>
      intro rest result ambient typed capturedArrow captured code stack
      cases typed with
      | pair leftTyped rightTyped =>
          simp only [compileSource, List.append_assoc, List.cons_append, List.nil_append]
          have leftRun := leftIH leftTyped captured (.swap :: (compileSource right ++ .cons :: code))
            (encodeSourceValue environment :: stack)
          have rightRun := rightIH rightTyped captured (.cons :: code) (encodeSourceValue first :: stack)
          exact .head (.push .strict _ _ _) (leftRun.trans
            (.head (.swap .strict _ _ _ _) (rightRun.tail (.cons .strict _ _ _ _))))
  | @app operator argument environment function operand value operatorEval argumentEval invocation operatorIH argumentIH invocationIH =>
      intro rest result ambient typed capturedArrow captured code stack
      cases typed with
      | app functionTyped argumentTyped =>
          simp only [compileSource, List.append_assoc, List.cons_append, List.nil_append]
          have operatorRun := operatorIH functionTyped captured
            (.swap :: (compileSource argument ++ .cons :: .app :: code)) (encodeSourceValue environment :: stack)
          have argumentRun := argumentIH argumentTyped captured (.cons :: .app :: code)
            (encodeSourceValue function :: stack)
          have invocationRun := invocationIH
            (evaluation_meaning operatorEval functionTyped captured)
            (evaluation_meaning argumentEval argumentTyped captured) code stack
          exact .head (.push .strict _ _ _) (operatorRun.trans
            (.head (.swap .strict _ _ _ _) ((argumentRun.tail (.cons .strict _ _ _ _)).trans invocationRun)))
  | first termEval projection termIH =>
      intro rest result ambient typed capturedArrow captured code stack
      cases typed with
      | first termTyped =>
          have transition := strict_first (evaluation_meaning termEval termTyped captured) projection code stack
          simpa only [compileSource, List.append_assoc, List.singleton_append] using
            (termIH termTyped captured (.first :: code) stack).tail transition
  | second termEval projection termIH =>
      intro rest result ambient typed capturedArrow captured code stack
      cases typed with
      | second termTyped =>
          have transition := strict_second (evaluation_meaning termEval termTyped captured) projection code stack
          simpa only [compileSource, List.append_assoc, List.singleton_append] using
            (termIH termTyped captured (.second :: code) stack).tail transition
  | @closure body environment argument value bodyEval bodyIH =>
      rename_i domain result ambient functionArrow argumentArrow functionMeaning argumentMeaning code stack
      obtain ⟨rest, sourceBody, sourceEnvironment, bodyTyped, capturedArrow, sameValue, sameArrow, captured⟩ :=
        functionMeaning.closure_case rfl
      obtain ⟨rfl, rfl⟩ := SourceValue.closure.inj sameValue
      exact .head (.appClosure .strict _ _ _ _ _)
        (bodyIH bodyTyped (EnvironmentMeaning.cons captured argumentMeaning) code stack)
  | neutral function argument inactive =>
      rename_i domain result ambient functionArrow argumentArrow functionMeaning argumentMeaning code stack
      obtain ⟨rest, body, environment, typed, capturedArrow, sameValue, sameArrow, captured⟩ :=
        functionMeaning.closure_case rfl
      subst function
      exact False.elim inactive

  | @literal enabled _ _ | @conditional enabled _ _ _ _ _ _ _ _ _ _ => cases enabled

theorem strict_execution {term : Expr} {environment value : Value}
    (evaluated : Evaluation term environment value) {rest : List (TypeOf signature)}
    {result ambient : TypeOf signature} (typed : Typing rest term result)
    {capturedArrow : ambient ⟶ context rest}
    (captured : EnvironmentMeaning ambient environment rest capturedArrow) :
    Steps .strict ⟨encodeSourceValue environment, compileSource term, []⟩ ⟨encodeSourceValue value, [], []⟩ := by
  simpa only [List.append_nil] using strict_execution_tail evaluated typed captured [] []

private theorem strict_transition_neutral {before after : State}
    (transition : Transition .strict before after) : Transition .neutral before after := by
  cases transition <;> first
    | exact .firstPair _ _ _ _ _
    | exact .secondPair _ _ _ _ _
    | exact .cur _ _ _ _ _
    | exact .push _ _ _ _
    | exact .swap _ _ _ _ _
    | exact .cons _ _ _ _ _
    | exact .appClosure _ _ _ _ _ _
    | exact .quote _ _ _ _ _
    | exact .branchTrue _ _ _ _ _ _
    | exact .branchFalse _ _ _ _ _ _

theorem strict_steps_neutral {before after : State}
    (execution : Steps .strict before after) : Steps .neutral before after := by
  induction execution with
  | refl => exact .refl
  | tail _ transition ih => exact ih.tail (strict_transition_neutral transition)

/-- For the compiled typed source and independently meaningful environment,
completion in the active Table 1 profile is exactly source evaluation. -/
theorem evaluation_iff_strict_execution (term : Expr) (environment value : Value)
    {rest : List (TypeOf signature)} {result ambient : TypeOf signature}
    (typed : Typing rest term result) {capturedArrow : ambient ⟶ context rest}
    (captured : EnvironmentMeaning ambient environment rest capturedArrow) :
    Evaluation term environment value ↔
      Steps .strict ⟨encodeSourceValue environment, compileSource term, []⟩ ⟨encodeSourceValue value, [], []⟩ :=
  ⟨fun evaluated => strict_execution evaluated typed captured,
    fun execution => (evaluation_iff_execution term environment value).mpr (strict_steps_neutral execution)⟩

theorem compiled_execution_meaning {term : Expr} {environment : Value} {native : NativeValue}
    {rest : List (TypeOf signature)} {result ambient : TypeOf signature}
    (typed : Typing rest term result) {capturedArrow : ambient ⟶ context rest}
    (captured : EnvironmentMeaning ambient environment rest capturedArrow)
    (execution : Steps .neutral ⟨encodeSourceValue environment, compileSource term, []⟩ ⟨native, [], []⟩) :
    ∃ value, encodeSourceValue value = native ∧
      ValueMeaning ambient value result (capturedArrow ≫ typed.denote) := by
  obtain ⟨value, evaluated, represented⟩ := execution_complete execution
  exact ⟨value, represented, evaluation_meaning evaluated typed captured⟩

theorem finished_meaning {term : Expr} {environment : Value} {native : NativeValue}
    {rest : List (TypeOf signature)} {result ambient : TypeOf signature}
    (typed : Typing rest term result) {capturedArrow : ambient ⟶ context rest}
    (captured : EnvironmentMeaning ambient environment rest capturedArrow)
    {budget : Nat} {events : List Occurrence}
    (finished : (machine .neutral).run budget ⟨encodeSourceValue environment, compileSource term, []⟩ =
      (events, .finished native)) :
    ∃ value, encodeSourceValue value = native ∧
      ValueMeaning ambient value result (capturedArrow ≫ typed.denote) := by
  have produced := (ProductiveCoreAdapters.produces_iff_finished
    (answerCore .neutral) (term, environment) native).mpr ⟨budget, events, finished⟩
  obtain ⟨value, evaluated, represented⟩ := (produces_iff_evaluation term environment native).mp produced
  exact ⟨value, represented, evaluation_meaning evaluated typed captured⟩

/-- Source typing does not add runtime annotations: the same compiled code
and actual native closure payload meet the strict runner's completed answer. -/
theorem strict_produces_iff_evaluation (term : Expr) (environment : Value) (native : NativeValue)
    {rest : List (TypeOf signature)} {result ambient : TypeOf signature}
    (typed : Typing rest term result) {capturedArrow : ambient ⟶ context rest}
    (captured : EnvironmentMeaning ambient environment rest capturedArrow) :
    (answerCore .strict).Produces (term, environment) native ↔
      ∃ value, Evaluation term environment value ∧ encodeSourceValue value = native := by
  constructor
  · rintro ⟨final, reached, observed⟩
    have ending := (answer_iff final native).mp observed
    rw [ending] at reached
    exact execution_complete (strict_steps_neutral ((core_steps_iff .strict _ _).mp reached))
  · rintro ⟨value, evaluated, represented⟩
    subst native
    exact ⟨⟨encodeSourceValue value, [], []⟩,
      (core_steps_iff .strict _ _).mpr (strict_execution evaluated typed captured), rfl⟩

theorem evaluation_iff_strict_finished (term : Expr) (environment value : Value)
    {rest : List (TypeOf signature)} {result ambient : TypeOf signature}
    (typed : Typing rest term result) {capturedArrow : ambient ⟶ context rest}
    (captured : EnvironmentMeaning ambient environment rest capturedArrow) :
    Evaluation term environment value ↔ ∃ budget events,
      (machine .strict).run budget ⟨encodeSourceValue environment, compileSource term, []⟩ =
        (events, .finished (encodeSourceValue value)) := by
  change Evaluation term environment value ↔ ∃ budget events,
    (ProductiveCoreAdapters.answerMachine (answerCore .strict)).run budget
      ((answerCore .strict).load (term, environment)) = (events, .finished (encodeSourceValue value))
  rw [← ProductiveCoreAdapters.produces_iff_finished (answerCore .strict) (term, environment) (encodeSourceValue value),
    strict_produces_iff_evaluation term environment (encodeSourceValue value) typed captured]
  constructor
  · intro evaluated; exact ⟨value, evaluated, rfl⟩
  · rintro ⟨source, evaluated, represented⟩
    exact encodeValue_injective represented ▸ evaluated

theorem strict_finished_meaning {term : Expr} {environment : Value} {native : NativeValue}
    {rest : List (TypeOf signature)} {result ambient : TypeOf signature}
    (typed : Typing rest term result) {capturedArrow : ambient ⟶ context rest}
    (captured : EnvironmentMeaning ambient environment rest capturedArrow)
    {budget : Nat} {events : List Occurrence}
    (finished : (machine .strict).run budget ⟨encodeSourceValue environment, compileSource term, []⟩ =
      (events, .finished native)) :
    ∃ value, encodeSourceValue value = native ∧
      ValueMeaning ambient value result (capturedArrow ≫ typed.denote) := by
  have produced := (ProductiveCoreAdapters.produces_iff_finished
    (answerCore .strict) (term, environment) native).mpr ⟨budget, events, finished⟩
  obtain ⟨value, evaluated, represented⟩ :=
    (strict_produces_iff_evaluation term environment native typed captured).mp produced
  exact ⟨value, represented, evaluation_meaning evaluated typed captured⟩

/-- The CCC beta equation is distinct from the number of CAM instructions
needed to execute this source application. -/
theorem Typing.beta {rest : List (TypeOf signature)} {body operand : Expr}
    {argument result : TypeOf signature}
    (bodyTyped : Typing (argument :: rest) body result)
    (argumentTyped : Typing rest operand argument) :
    (Typing.app (Typing.lam bodyTyped) argumentTyped).denote =
      pairing (𝟙 (context rest)) argumentTyped.denote ≫ bodyTyped.denote := by
  simpa only [Typing.denote, Category.id_comp] using
    closure_application (𝟙 (context rest)) argumentTyped.denote bodyTyped.denote

end Typed

end

/-! ## Compiled code admission and dynamic instruction legality -/

/-- A code image retains its source environment; decoding only the instruction
stream cannot supply or replace that environment. -/
def decodeImage (image : Code × Value) : Option (Expr × Value) :=
  (decodeCode image.1).map fun expression => (expression, image.2)

def compileImage (question : Expr × Value) : Code × Value :=
  (compileSource question.1, question.2)

@[simp] theorem decodeImage_compileImage (question : Expr × Value) :
    decodeImage (compileImage question) = some question := by
  rcases question with ⟨expression, environment⟩
  simp [decodeImage, compileImage]

/-- The historical compiler image has a checked loader. Raw operational
extensions require their own source image and admission contract. -/
def loadImage (profile : Profile) (image : Code × Value) : Option State :=
  (core profile).loadCode decodeImage image

@[simp] theorem loadImage_compileImage (profile : Profile) (question : Expr × Value) :
    loadImage profile (compileImage question) = some ((core profile).load question) :=
  MachineCore.loadCode_encode (core profile) compileImage decodeImage
    decodeImage_compileImage question

@[simp] theorem loadImage_refused_iff (profile : Profile) (code : Code) (environment : Value) :
    loadImage profile (code, environment) = none ↔ decodeCode code = none := by
  cases decoded : decodeCode code with
  | none =>
      simp only [loadImage, MachineCore.loadCode, decodeImage, decoded, Option.map_none]
      exact iff_true_intro rfl
  | some expression => simp [loadImage, MachineCore.loadCode, decodeImage, decoded]

/-- Admission preserves exactly the supplied instruction image and environment.
It does not grant an empty stack a result before execution has occurred. -/
theorem loadImage_some_iff (profile : Profile) (code : Code) (environment : Value) (state : State) :
    loadImage profile (code, environment) = some state ↔
      ∃ expression, decodeCode code = some expression ∧
        state = ⟨encodeSourceValue environment, code, []⟩ := by
  cases decoded : decodeCode code with
  | none => simp [loadImage, MachineCore.loadCode, decodeImage, decoded]
  | some expression =>
      have canonical := compile_decode decoded
      simp [loadImage, MachineCore.loadCode, decodeImage, decoded, core, sourceCore, canonical,
        eq_comm]

/-- A legal instruction is an actual head of the retained code with an
independent instruction-table transition. It is distinct from code admission. -/
def InstructionLegal (profile : Profile) (state : State) (opcode : Instruction) : Prop :=
  ∃ rest next, state.code = opcode :: rest ∧ Transition profile state next

theorem Transition.has_instruction {profile : Profile} {before after : State}
    (transition : Transition profile before after) :
    ∃ opcode, before.code.head? = some opcode := by
  cases transition <;> simp

def instructionContract (profile : Profile) :
    MachineCore.InstructionContract (core profile) Instruction where
  fetch state := state.code.head?
  Legal := InstructionLegal profile
  enabled_iff state := by
    constructor
    · rintro ⟨next, advanced⟩
      have transition := step_sound advanced
      cases code : state.code with
      | nil =>
          obtain ⟨opcode, fetched⟩ := transition.has_instruction
          simp [code] at fetched
      | cons opcode rest =>
          exact ⟨opcode, rfl, rest, next, code, transition⟩
    · rintro ⟨opcode, _, rest, next, _, transition⟩
      exact ⟨next, step_complete transition⟩

/-- The admitted code uses the existing source/machine correspondence; neither
loading nor instruction validation introduces a second evaluation semantics. -/
theorem admitted_answer_iff_evaluation (code : Code) (environment : Value) (expression : Expr)
    (decoded : decodeCode code = some expression) (value : NativeValue) :
    (∃ initial final, loadImage .neutral (code, environment) = some initial ∧
      (core .neutral).Steps initial final ∧ answer final = some value) ↔
      ∃ result, Evaluation expression environment result ∧ encodeSourceValue result = value := by
  have canonical := compile_decode decoded
  have loaded : loadImage .neutral (code, environment) =
      some ((core .neutral).load (expression, environment)) := by
    rw [← canonical]
    exact loadImage_compileImage .neutral (expression, environment)
  rw [loaded]
  constructor
  · rintro ⟨initial, final, same, reached, observed⟩
    cases same
    exact (produces_iff_evaluation expression environment value).mp ⟨final, reached, observed⟩
  · intro evaluated
    obtain ⟨final, reached, observed⟩ :=
      (produces_iff_evaluation expression environment value).mpr evaluated
    exact ⟨_, final, rfl, reached, observed⟩

/-! ## Conservativity and executable admission of the extended source -/

/-- Enable quotation/conditionals without changing any existing source constructor. -/
def Source.enable : Source extended → Source true
  | .var index => .var index
  | .lam body => .lam body.enable
  | .app operator argument => .app operator.enable argument.enable
  | .pair left right => .pair left.enable right.enable
  | .first term => .first term.enable
  | .second term => .second term.enable
  | .literal _ value => .literal rfl value
  | .conditional _ condition whenTrue whenFalse =>
      .conditional rfl condition.enable whenTrue.enable whenFalse.enable

@[simp] theorem compile_enable (term : Source extended) : compileSource term.enable = compileSource term := by
  induction term <;> simp_all [Source.enable, compileSource]

/-- Captured environments and source closure bodies move together. -/
def SourceValue.enable : SourceValue extended → SourceValue true
  | .unit => .unit
  | .literal _ value => .literal rfl value
  | .pair left right => .pair left.enable right.enable
  | .closure body environment => .closure body.enable environment.enable
  | .first value => .first value.enable
  | .second value => .second value.enable
  | .app value => .app value.enable

@[simp] theorem encodeValue_enable (value : SourceValue extended) :
    encodeSourceValue value.enable = encodeSourceValue value := by
  induction value <;> simp_all [SourceValue.enable, encodeSourceValue]

/-- The old and extended source judgments agree exactly on the embedded
fragment, through their independently proved correspondence with the same CAM. -/
theorem evaluation_enable_iff (term : Source extended) (environment value : SourceValue extended) :
    Evaluation term.enable environment.enable value.enable ↔ Evaluation term environment value := by
  rw [evaluation_iff_execution, evaluation_iff_execution]
  simp only [encodeValue_enable, compile_enable]

/-- Completed native values reconstruct source closure bodies and their entire
captured environment; neither code nor the environment is supplied by a caller. -/
theorem evaluation_iff_nativeReadback (term : Source extended) (environment value : SourceValue extended) :
    Evaluation term environment value ↔
      ∃ native, Steps .neutral ⟨encodeSourceValue environment, compileSource term, []⟩ ⟨native, [], []⟩ ∧
        decodeSourceValue native = some value := by
  constructor
  · intro evaluated
    exact ⟨encodeSourceValue value, evaluated.execution, decode_encodeValue value⟩
  · rintro ⟨native, execution, decoded⟩
    have represented := encode_decodeValue decoded
    rw [← represented] at execution
    exact (evaluation_iff_execution term environment value).mpr execution

namespace Extended

abbrev Expr := Source true
abbrev Value := SourceValue true

def quote (value : Literal) : Expr := .literal rfl value

def conditional (condition whenTrue whenFalse : Expr) : Expr :=
  .conditional rfl condition whenTrue whenFalse

abbrev compile : Expr → Code := compileSource
abbrev encodeValue : Value → NativeValue := encodeSourceValue
abbrev decodeCode : Code → Option Expr := decodeSourceCode
abbrev decodeValue : NativeValue → Option Value := decodeSourceValue
abbrev core (profile : Profile) := sourceCore true profile
abbrev answerCore (profile : Profile) := sourceAnswerCore true profile

/-- Loading is checked against the extended compiler image, separately from
runtime instruction legality. The original source environment is retained. -/
def decodeImage (image : Code × Value) : Option (Expr × Value) :=
  (decodeCode image.1).map fun expression => (expression, image.2)

def compileImage (question : Expr × Value) : Code × Value :=
  (compileSource question.1, question.2)

@[simp] theorem decodeImage_compileImage (question : Expr × Value) :
    decodeImage (compileImage question) = some question := by
  rcases question with ⟨expression, environment⟩
  simp [decodeImage, compileImage]

def loadImage (profile : Profile) (image : Code × Value) : Option State :=
  (core profile).loadCode decodeImage image

@[simp] theorem loadImage_compileImage (profile : Profile) (question : Expr × Value) :
    loadImage profile (compileImage question) = some ((core profile).load question) :=
  MachineCore.loadCode_encode (core profile) compileImage decodeImage decodeImage_compileImage question

@[simp] theorem loadImage_refused_iff (profile : Profile) (code : Code) (environment : Value) :
    loadImage profile (code, environment) = none ↔ decodeCode code = none := by
  cases decoded : decodeCode code with
  | none =>
      simp only [loadImage, MachineCore.loadCode, decodeImage, decoded, Option.map_none]
      exact iff_true_intro rfl
  | some expression => simp [loadImage, MachineCore.loadCode, decodeImage, decoded]

/-- Every accepted image executes exactly its independently judged source.
Acceptance does not assert progress for a non-Boolean condition. -/
theorem admitted_answer_iff_evaluation (code : Code) (environment : Value) (expression : Expr)
    (decoded : decodeCode code = some expression) (value : NativeValue) :
    (∃ initial final, loadImage .neutral (code, environment) = some initial ∧
      (core .neutral).Steps initial final ∧ answer final = some value) ↔
      ∃ result, Evaluation expression environment result ∧ encodeSourceValue result = value := by
  have canonical := compile_decode decoded
  have loaded : loadImage .neutral (code, environment) =
      some ((core .neutral).load (expression, environment)) := by
    rw [← canonical]
    exact loadImage_compileImage .neutral (expression, environment)
  rw [loaded]
  constructor
  · rintro ⟨initial, final, same, reached, observed⟩
    cases same
    exact (sourceProduces_iff_evaluation expression environment value).mp ⟨final, reached, observed⟩
  · intro evaluated
    obtain ⟨final, reached, observed⟩ :=
      (sourceProduces_iff_evaluation expression environment value).mpr evaluated
    exact ⟨_, final, rfl, reached, observed⟩

end Extended

end Mettapedia.Machines.CategoricalAbstractMachine
