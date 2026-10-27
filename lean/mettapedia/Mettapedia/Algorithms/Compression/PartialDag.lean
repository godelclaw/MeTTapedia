import Mettapedia.Algorithms.Compression.CompactDag

/-!
# Partial operators in the shared compact DAG

A numerical fault is an algebra result, not failure of the record traversal.
Only dependent nodes propagate that fault; an unused failed node cannot erase
an independent selected root. Malformed references still fail the traversal.
Argument order determines the first propagated fault. This model assumes
actual functions, not effectful or nondeterministic evaluator callbacks.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Compression.PartialDag

open KolmogorovComplexity CompactDag

variable {Error Value : Type}

def arguments : List (Except Error Value) → Except Error (List Value)
  | [] => .ok []
  | .error reason :: _ => .error reason
  | .ok value :: rest => (arguments rest).map (value :: ·)

def apply (operator : BinString → List Value → Except Error Value)
    (tag : BinString) (children : List (Except Error Value)) : Except Error Value :=
  (arguments children).bind (operator tag)

theorem arguments_append (first second : List (Except Error Value)) :
    arguments (first ++ second) =
      (arguments first).bind (fun left => (arguments second).map (left ++ ·)) := by
  induction first with
  | nil =>
      simp only [List.nil_append, arguments]
      cases arguments second <;> rfl
  | cons head tail ih =>
      cases head with
      | error reason => rfl
      | ok value =>
          simp only [List.cons_append, arguments, ih]
          cases left : arguments tail <;> cases right : arguments second <;> rfl

theorem first_fault (reason : Error) (rest : List (Except Error Value)) :
    arguments (.error reason :: rest) = .error reason := rfl

theorem argument_fault_prevents_operator
    (operator : BinString → List Value → Except Error Value) (tag : BinString)
    (children : List (Except Error Value)) (reason : Error)
    (failed : arguments children = .error reason) :
    apply operator tag children = .error reason := by
  simp only [apply, failed]
  rfl

/-- Memoized and unfolded partial execution agree without assuming any
associativity, commutativity, or totality of the supplied operators. -/
theorem evaluate_unfold (leaf : BinString → Except Error Value)
    (operator : BinString → List Value → Except Error Value) (forest : Forest) :
    CompactDag.evaluate leaf (apply operator) forest =
      (CompactDag.unfold forest).map (List.map (CompactDag.fold leaf (apply operator))) :=
  CompactDag.evaluate_unfold leaf (apply operator) forest

namespace Controls

def leaf (bytes : BinString) : Except String Nat :=
  if bytes = [] then .ok 2 else .error "input"

def ordered (_tag : BinString) : List Nat → Except String Nat
  | [first, second] => .ok (10 * first + second)
  | _ => .error "arity"

def independent : Forest :=
  ⟨[2, 0, 2], [.leaf [], .leaf [false], .node [true] [0, 0]]⟩

theorem unused_fault_preserves_roots_and_duplicates :
    CompactDag.evaluate leaf (apply ordered) independent =
      some [.ok 22, .ok 2, .ok 22] := by decide

theorem used_fault_reaches_only_its_dependents :
    CompactDag.evaluate leaf (apply ordered)
      ⟨[2, 0], [.leaf [], .leaf [false], .node [true] [0, 1]]⟩ =
      some [.error "input", .ok 2] := by decide

theorem argument_order_selects_the_first_fault :
    apply ordered [] [.error "left", .error "right"] = .error "left" ∧
      apply ordered [] [.error "right", .error "left"] = .error "right" := by decide

theorem malformed_reference_is_not_an_operator_fault :
    CompactDag.evaluate leaf (apply ordered) ⟨[0], [.node [] [0]]⟩ = none := by decide

end Controls
end Mettapedia.Algorithms.Compression.PartialDag
