import Mettapedia.Languages.Datalog.ProgramStatic

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.ProgramStatic.Controls

private def declare (name : String) (fields : List (String × AttributeType)) : Statement :=
  .declaration ⟨[name], fields.map fun (identifier, type) => ⟨identifier, type⟩⟩

private def atom (name : String) (arguments : List Argument) : Atom := ⟨[name], arguments⟩
private def v (name : String) : Argument := .var name
private def call (name : String) (arguments : List Argument) : Premise := .atom (atom name arguments)
private def rule (name : String) (arguments : List Argument) (body : List Premise) : Statement :=
  .rule ⟨atom name arguments, body⟩

/-- Structured counterparts of the ordinary acceptance programs. These are
static controls, not a claim of packed-forest lowering correspondence. -/
def cyclicGraph : Program := ⟨[
  declare "Edge" [("source", .symbol), ("target", .symbol)], .input ["Edge"],
  declare "Task" [("name", .symbol), ("source", .symbol), ("target", .symbol), ("priority", .number)],
  .input ["Task"],
  declare "Reach" [("source", .symbol), ("target", .symbol)],
  rule "Reach" [v "X", v "Y"] [call "Edge" [v "X", v "Y"]],
  rule "Reach" [v "X", v "Z"] [call "Reach" [v "X", v "Y"], call "Edge" [v "Y", v "Z"]],
  .output ["Reach"],
  declare "PathStep" [("source", .symbol), ("via", .symbol), ("target", .symbol)],
  rule "PathStep" [v "X", v "Y", v "Z"]
    [call "Reach" [v "X", v "Y"], call "Edge" [v "Y", v "Z"],
      .comparison ⟨.different, v "X", v "Z"⟩],
  .output ["PathStep"],
  declare "Eligible" [("name", .symbol), ("priority", .number)],
  rule "Eligible" [v "Name", v "Priority"]
    [call "Task" [v "Name", v "Source", v "Target", v "Priority"],
      call "Reach" [v "Source", v "Target"],
      .comparison ⟨.greaterEqual, v "Priority", .literal (.number 1)⟩],
  .output ["Eligible"]]⟩

def pointsTo : Program := ⟨[
  declare "Address" [("variable", .symbol), ("object", .symbol)], .input ["Address"],
  declare "Copy" [("target", .symbol), ("source", .symbol)], .input ["Copy"],
  declare "Load" [("target", .symbol), ("pointer", .symbol)], .input ["Load"],
  declare "Store" [("pointer", .symbol), ("source", .symbol)], .input ["Store"],
  declare "PointsTo" [("variable", .symbol), ("object", .symbol)],
  declare "Heap" [("cell", .symbol), ("object", .symbol)],
  rule "PointsTo" [v "V", v "O"] [call "Address" [v "V", v "O"]],
  rule "PointsTo" [v "V", v "O"] [call "Copy" [v "V", v "W"], call "PointsTo" [v "W", v "O"]],
  rule "Heap" [v "Cell", v "O"]
    [call "Store" [v "P", v "V"], call "PointsTo" [v "P", v "Cell"], call "PointsTo" [v "V", v "O"]],
  rule "PointsTo" [v "V", v "O"]
    [call "Load" [v "V", v "P"], call "PointsTo" [v "P", v "Cell"], call "Heap" [v "Cell", v "O"]],
  .output ["PointsTo"], .output ["Heap"]]⟩

theorem acceptance_programs_static :
    checkProgram cyclicGraph = true ∧ checkProgram pointsTo = true ∧
      diagnose cyclicGraph = [] ∧ diagnose pointsTo = [] := by
  decide +kernel

theorem declared_interfaces_and_ground_facts :
    checkProgram ⟨cyclicGraph.statements ++ [.fact ⟨["Edge"], [.symbol "a", .symbol "b"]⟩]⟩ = true ∧
    diagnose ⟨cyclicGraph.statements ++ [.fact ⟨["Edge"], [.number 1, .symbol "b"]⟩]⟩ =
      [.illTypedFact 14] ∧
    diagnose ⟨cyclicGraph.statements ++ [.output ["Unknown"]]⟩ = [.undeclaredInterface 14] ∧
    diagnose ⟨cyclicGraph.statements ++ [declare "Edge" [("source", .symbol), ("target", .symbol)]]⟩ =
      [.duplicateRelations] := by
  decide +kernel

theorem inconsistent_or_unbound_variables_refused :
    diagnose ⟨cyclicGraph.statements ++ [rule "Reach" [v "X", v "Y"]
      [call "Edge" [v "X", .anonymous]]]⟩ = [.illTypedClause 14] ∧
    diagnose ⟨cyclicGraph.statements ++ [rule "Eligible" [v "Name", v "Priority"]
      [call "Task" [v "Name", v "Source", v "Target", v "Priority"],
        call "Reach" [v "Priority", v "Target"]]]⟩ = [.illTypedClause 14] ∧
    diagnose ⟨[declare "Bad" [("same", .symbol), ("same", .symbol)]]⟩ = [.invalidDeclaration 0] := by
  decide +kernel

theorem ground_empty_body_is_supported :
    checkProgram ⟨[declare "Ready" [], rule "Ready" [] [], .output ["Ready"]]⟩ = true ∧
      checkProgram ⟨[declare "Ready" [("value", .number)],
        rule "Ready" [.literal (.number 1)] [], .output ["Ready"]]⟩ = true ∧
      checkProgram ⟨[declare "Ready" [("value", .number)],
        rule "Ready" [v "X"] [], .output ["Ready"]]⟩ = false := by
  decide +kernel

#print axioms acceptance_programs_static
#print axioms declared_interfaces_and_ground_facts
#print axioms inconsistent_or_unbound_variables_refused
#print axioms ground_empty_body_is_supported

end Mettapedia.Languages.Datalog.ProgramStatic.Controls
