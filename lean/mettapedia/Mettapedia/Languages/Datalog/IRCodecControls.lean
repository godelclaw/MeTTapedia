import Mettapedia.Languages.Datalog.IRCodec
import Mettapedia.Languages.Datalog.ProgramStaticControls

/-! Direct IR controls exercise the real static acceptance programs without
importing their source grammar. Payload-node counts exclude string byte length
and runtime allocator costs. The MeTTa execution correspondence is separate. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.Languages.Datalog.IRCodec.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern)

mutual
  def nodes : Pattern → Nat
    | .bvar _ | .fvar _ => 1
    | .apply _ children | .collection _ children _ => 1 + nodeList children
    | .lambda _ body | .multiLambda _ _ body => 1 + nodes body
    | .subst body replacement => 1 + nodes body + nodes replacement
  def nodeList : List Pattern → Nat
    | [] => 0
    | first :: rest => nodes first + nodeList rest
end

theorem scalar_is_one_atomic_payload (input : Value) : nodes (value input) = 2 := by
  cases input <;> rfl

theorem acceptance_programs_round_trip :
    program? (program ProgramStatic.Controls.cyclicGraph) = some ProgramStatic.Controls.cyclicGraph ∧
      program? (program ProgramStatic.Controls.pointsTo) = some ProgramStatic.Controls.pointsTo :=
  ⟨program_roundtrip _,program_roundtrip _⟩

def duplicateFacts : Program := ⟨[
  .fact ⟨["edge"],[.number 1,.number 2]⟩,
  .fact ⟨["edge"],[.number 1,.number 2]⟩,
  .rule ⟨⟨["same"],[.var "X",.var "X"]⟩,
    [.atom ⟨["edge"],[.var "X",.anonymous]⟩]⟩]⟩

theorem occurrences_and_variable_relationships_round_trip :
    program? (program duplicateFacts) = some duplicateFacts := program_roundtrip _

theorem malformed_and_noncanonical_payloads_refused :
    value? (.apply "IntegerValue" [atom "01"]) = none ∧
    value? (.apply "UnsignedValue" [atom "-1"]) = none ∧
    value? (.apply "FloatValue" [atom "18446744073709551616"]) = none ∧
    value? (.apply "IntegerValue" [atom "not-an-integer"]) = none ∧
    program? (.apply "Program" []) = none ∧
    qualifiedName? (.apply "QualifiedName" [.collection .vec [atom "edge"] (some "unfinished")]) = none := by
  decide_cbv

theorem scalar_sorts_do_not_collapse :
    value (.number 1) ≠ value (.unsigned 1) ∧
      value (.symbol "1") ≠ value (.number 1) ∧
      value (.floating 0) ≠ value (.floating 9223372036854775808) := by
  decide +kernel

theorem ieee_payloads_round_trip :
    value? (value (.floating 0)) = some (.floating 0) ∧
      value? (value (.floating 9223372036854775808)) = some (.floating 9223372036854775808) ∧
      value? (value (.floating 9221120237041090561)) = some (.floating 9221120237041090561) := by
  exact ⟨value_roundtrip _,value_roundtrip _,value_roundtrip _⟩

#print axioms scalar_is_one_atomic_payload
#print axioms acceptance_programs_round_trip
#print axioms malformed_and_noncanonical_payloads_refused

end Mettapedia.Languages.Datalog.IRCodec.Controls
