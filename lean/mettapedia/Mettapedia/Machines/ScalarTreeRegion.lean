import Mettapedia.Machines.RegisterCode
import Mettapedia.GSLT.Dynamics.PartialRegionPlan

/-!
# Bounded scalar expression regions

Already-ready locals and literals can feed a compact scalar interpreter
without publishing each intermediate value. Calls, forced arguments, binds,
and constructors are not scalar-tree nodes. Partial primitive operations keep
their left-to-right schedule; no associativity or commutativity law is used.

The compiler below emits a postorder stack program. Its interpreter is
independent of the recursive source interpretation and of the existing node
executor. The correspondence and read-footprint laws concern this algorithm,
not a native implementation or a concrete IEEE primitive implementation.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ScalarTreeRegion

variable {L O V P H : Type}

inductive Tree (L O : Type) where
  | literal (value : L)
  | slot (index : Nat)
  | binary (operation : O) (left right : Tree L O)
  deriving DecidableEq

def evaluate (literal : L → V) (operation : O → V → V → Option V)
    (locals : Nat → Option V) : Tree L O → Option V
  | .literal value => some (literal value)
  | .slot index => locals index
  | .binary op left right => do
      let l ← evaluate literal operation locals left
      let r ← evaluate literal operation locals right
      operation op l r

inductive Instruction (L O : Type) where
  | push (value : L)
  | read (index : Nat)
  | apply (operation : O)
  deriving DecidableEq

def step (literal : L → V) (operation : O → V → V → Option V)
    (locals : Nat → Option V) : Instruction L O → List V → Option (List V)
  | .push value, stack => some (literal value :: stack)
  | .read index, stack => (locals index).map (· :: stack)
  | .apply op, right :: left :: rest => (operation op left right).map (· :: rest)
  | .apply _, _ => none

def execute (literal : L → V) (operation : O → V → V → Option V)
    (locals : Nat → Option V) : List (Instruction L O) → List V → Option (List V)
  | [], stack => some stack
  | instruction :: rest, stack => do
      let next ← step literal operation locals instruction stack
      execute literal operation locals rest next

def compile : Tree L O → List (Instruction L O)
  | .literal value => [.push value]
  | .slot index => [.read index]
  | .binary op left right => compile left ++ compile right ++ [.apply op]

private theorem option_map_bind {A B C : Type} (value : Option A)
    (f : A → B) (g : B → Option C) :
    (value.map f).bind g = value.bind (fun a => g (f a)) := by
  cases value <;> rfl

/-- A compiled expression adds precisely one value before an arbitrary
continuation and leaves the incoming stack untouched underneath it. -/
theorem compile_execute_suffix (literal : L → V)
    (operation : O → V → V → Option V) (locals : Nat → Option V)
    (tree : Tree L O) (suffix : List (Instruction L O)) (stack : List V) :
    execute literal operation locals (compile tree ++ suffix) stack =
      (evaluate literal operation locals tree).bind
        (fun value => execute literal operation locals suffix (value :: stack)) := by
  induction tree generalizing suffix stack with
  | literal value => rfl
  | slot index => simp [compile, execute, step, evaluate, option_map_bind]
  | binary op left right ihLeft ihRight =>
      simp [compile, List.append_assoc, ihLeft, ihRight, evaluate,
        execute, step, Option.bind_assoc, option_map_bind]

theorem compile_execute (literal : L → V)
    (operation : O → V → V → Option V) (locals : Nat → Option V)
    (tree : Tree L O) (stack : List V) :
    execute literal operation locals (compile tree) stack =
      (evaluate literal operation locals tree).map (· :: stack) := by
  rw [← List.append_nil (compile tree), compile_execute_suffix]
  cases evaluate literal operation locals tree <;> rfl

def embed : Tree L O → RegisterCode.Node L O P H
  | .literal value => .lit value
  | .slot index => .slot index
  | .binary op left right => .op op [embed left, embed right]

/-- Scalar source trees are a genuine fragment of the existing node language.
Their operations do not write locals, so the original register state survives. -/
theorem embed_evaluate (semantics : RegisterCode.Sem V L O P H)
    (answer : H → List V → Option V) (locals : RegisterCode.Regs V)
    (tree : Tree L O) :
    RegisterCode.eval semantics answer locals (embed tree) =
      (evaluate semantics.lit (fun op l r => semantics.op op [l,r]) locals tree).map
        (fun value => (value,locals)) := by
  induction tree with
  | literal value => rfl
  | slot index => rfl
  | binary op left right ihLeft ihRight =>
      simp only [embed, RegisterCode.eval, RegisterCode.evalList, ihLeft,
        evaluate]
      cases hl : evaluate semantics.lit (fun op l r => semantics.op op [l,r]) locals left <;>
        cases hr : evaluate semantics.lit (fun op l r => semantics.op op [l,r]) locals right <;>
        simp_all [Option.map, Option.bind]

theorem compiled_node_observation (semantics : RegisterCode.Sem V L O P H)
    (answer : H → List V → Option V) (locals : RegisterCode.Regs V)
    (tree : Tree L O) :
    (execute semantics.lit (fun op l r => semantics.op op [l,r]) locals
      (compile tree) []).bind List.head? =
        (RegisterCode.eval semantics answer locals (embed tree)).map Prod.fst := by
  rw [compile_execute, embed_evaluate]
  cases evaluate semantics.lit (fun op l r => semantics.op op [l,r]) locals tree <;> rfl

def reads : Tree L O → List Nat
  | .literal _ => []
  | .slot index => [index]
  | .binary _ left right => reads left ++ reads right

theorem embed_scoped (patterns : RegisterCode.Patterns P) (m : Nat)
    (scope : Finset Nat) (tree : Tree L O)
    (covers : ∀ i ∈ reads tree, i ∈ scope) :
    RegisterCode.Scoped patterns m scope (embed (H := H) tree) := by
  induction tree with
  | literal value => trivial
  | slot index => exact covers index (by simp [reads])
  | binary op left right ihLeft ihRight =>
      change RegisterCode.Scoped patterns m scope (embed left) ∧
        RegisterCode.Scoped patterns m scope (embed right) ∧ True
      exact ⟨ihLeft (fun i hi => covers i (by simp [reads, hi])),
        ihRight (fun i hi => covers i (by simp [reads, hi])), trivial⟩

/-- The direct region agrees with the existing register-code lowering, not
only with an independently defined stack machine. -/
theorem scalar_region_eq_register_code (semantics : RegisterCode.Sem V L O P H)
    (answer : H → List V → Option V) (fuses : O → Nat → Bool)
    (locals : RegisterCode.Regs V) (m : Nat) (scope : Finset Nat)
    (tree : Tree L O) (covers : ∀ i ∈ reads tree, i ∈ scope)
    (bounded : ∀ i ∈ scope, i < m) :
    RegisterCode.answer (RegisterCode.exec semantics answer
      (RegisterCode.compile fuses (embed tree) true m m).1 locals) =
        evaluate semantics.lit (fun op l r => semantics.op op [l,r]) locals tree := by
  have lowering := RegisterCode.lower_answers semantics answer fuses
    (R := locals) (N := locals) (dst := m)
    (embed_scoped semantics.toPatterns m scope tree covers)
    bounded (fun _ _ => rfl) (Nat.le_refl m)
  rw [lowering.answer_eq, embed_evaluate]
  cases evaluate semantics.lit (fun op l r => semantics.op op [l,r]) locals tree <;> rfl

def instructionRead : Instruction L O → Option Nat
  | .read index => some index
  | _ => none

/-- Every source local remains a liveness input after fusion, including
repeated reads. Literals need no activation register. -/
theorem compile_reads (tree : Tree L O) :
    (compile tree).filterMap instructionRead = reads tree := by
  induction tree <;> simp_all [compile, reads, instructionRead, List.filterMap_append]

def nodes : Tree L O → Nat
  | .literal _ | .slot _ => 1
  | .binary _ left right => nodes left + nodes right + 1

theorem compile_length (tree : Tree L O) : (compile tree).length = nodes tree := by
  induction tree <;> simp_all [compile, nodes, Nat.add_assoc]

def observe (literal : L → V) (operation : O → V → V → Option V)
    (locals : Nat → Option V) (tree : Tree L O) : Option V :=
  (execute literal operation locals (compile tree) []).bind List.head?

theorem observe_eq_evaluate (literal : L → V)
    (operation : O → V → V → Option V) (locals : Nat → Option V) (tree : Tree L O) :
    observe literal operation locals tree = evaluate literal operation locals tree := by
  rw [observe, compile_execute]
  cases evaluate literal operation locals tree <;> rfl

/-- A bounded region either publishes its complete observation or returns the
unchanged input to the source evaluator. Work is not part of this observation. -/
theorem bounded_region_exact (literal : L → V)
    (operation : O → V → V → Option V) (locals : Nat → Option V) (limit : Nat) :
    GSLT.Dynamics.PartialRegionPlan.realize
      (GSLT.Dynamics.PartialRegionPlan.boundedAttempt nodes limit
        (observe literal operation locals))
      (evaluate literal operation locals) = evaluate literal operation locals := by
  apply GSLT.Dynamics.PartialRegionPlan.realize_boundedAttempt_exact
  funext tree
  exact observe_eq_evaluate literal operation locals tree

example : observe (id : Int → Int) (fun (_ : Unit) l r => some (l-r))
    (fun _ => some 2) (.binary () (.literal 5) (.slot 0)) = some 3 := by decide

example : observe (id : Int → Int) (fun (_ : Unit) l r => some (l-r))
    (fun _ => some 2) (.binary () (.slot 0) (.literal 5)) ≠ some 3 := by decide

example : execute (id : Int → Int) (fun (_ : Unit) l r => some (l-r))
    (fun _ => none) [.apply ()] [] = none := by decide

#print axioms compiled_node_observation
#print axioms scalar_region_eq_register_code
#print axioms compile_reads
#print axioms bounded_region_exact

end Mettapedia.Machines.ScalarTreeRegion
