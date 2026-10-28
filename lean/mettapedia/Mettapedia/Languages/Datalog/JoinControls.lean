import Mettapedia.Languages.Datalog.Join

/-! Separating source-join controls: shared variables, kept premises, wildcard
independence and distinct validation positions for equal fact values. -/

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.Join.Controls

private def symbol (value : String) : Value := .symbol value
private def literal (value : String) : Argument := .literal (symbol value)
private def edge (left right : String) : GroundFact := ⟨["Edge"], [symbol left, symbol right]⟩
private def edgePattern (left right : Argument) : Atom := ⟨["Edge"], [left, right]⟩

def routeAtoms : List Atom :=
  [edgePattern (literal "A") (.var "X"), edgePattern (.var "X") (.var "Y")]

def routeFacts : List GroundFact := [edge "A" "B", edge "B" "D", edge "A" "C", edge "C" "D"]

theorem two_routes_same_endpoint :
    (join routeAtoms routeFacts []).map (fun row =>
      (row.environment.lookup "X", row.environment.lookup "Y", row.rowPositions)) =
      [(some (symbol "B"), some (symbol "D"), [0,1]),
       (some (symbol "C"), some (symbol "D"), [2,3])] := by decide +kernel

theorem repeated_variable_disagreement_refused :
    join [edgePattern (.var "X") (.var "X")] [edge "A" "B"] [] = [] := by decide +kernel

theorem repeated_variable_agreement_accepted :
    (join [edgePattern (.var "X") (.var "X")] [edge "A" "A"] []).length = 1 := by decide +kernel

theorem wildcard_positions_independent :
    (join [edgePattern .anonymous .anonymous] [edge "A" "B"] []).map (·.environment) = [[]] := by
  decide +kernel

theorem duplicate_validation_is_retained :
    (join [edgePattern (.var "X") (.var "Y")] [edge "A" "B", edge "A" "B"] []).map
      (fun row => (row.facts, row.rowPositions)) =
        [([edge "A" "B"], [0]), ([edge "A" "B"], [1])] := by decide +kernel

theorem repeated_premises_keep_one_fact :
    (join [edgePattern (.var "X") (.var "Y"), edgePattern (.var "X") (.var "Y")]
      [edge "A" "B"] []).map (fun row => (row.facts, row.rowPositions)) =
        [([edge "A" "B", edge "A" "B"], [0,0])] := by decide +kernel

theorem missing_second_premise_refused : join routeAtoms [edge "A" "B"] [] = [] := by decide +kernel

theorem wrong_relation_refused :
    join [edgePattern (.var "X") (.var "Y")] [⟨["Other"], [symbol "A", symbol "B"]⟩] [] = [] := by
  decide +kernel

theorem wrong_arity_refused :
    join [edgePattern (.var "X") (.var "Y")] [⟨["Edge"], [symbol "A"]⟩] [] = [] := by decide +kernel

theorem empty_body_has_one_grounding : join [] [] [] = [⟨[], [], []⟩] := by decide +kernel

#print axioms two_routes_same_endpoint
#print axioms repeated_variable_disagreement_refused
#print axioms duplicate_validation_is_retained
#print axioms repeated_premises_keep_one_fact
#print axioms empty_body_has_one_grounding

end Mettapedia.Languages.Datalog.Join.Controls
