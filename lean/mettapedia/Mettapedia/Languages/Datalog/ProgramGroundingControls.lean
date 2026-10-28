import Mettapedia.Languages.Datalog.ProgramGrounding
import Mettapedia.Languages.Datalog.ProgramStatic
import Mettapedia.Languages.Datalog.ComparisonControls

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.ProgramGrounding.Controls

private def tag (value : Int) : GroundFact := ⟨["Tag"], [.number value]⟩
private def result (value : Int) : GroundFact := ⟨["Result"], [.number value]⟩

def program : Program := ⟨[
  .declaration ⟨["Tag"], [⟨"value", .number⟩]⟩,
  .input ["Tag"],
  .fact (tag 1),
  .output ["Tag"],
  .rule ⟨⟨["Result"], [.var "X"]⟩,
    [.atom ⟨["Tag"], [.var "X"]⟩,
     .comparison ⟨.less, .var "X", .literal (.number 2)⟩]⟩,
  .declaration ⟨["Result"], [⟨"value", .number⟩]⟩]⟩

private def policy := Comparisons.Controls.integerPolicy

theorem complete_program_indices_and_results :
    ProgramStatic.checkProgram program = true ∧
      ((produce policy program [tag 1, tag 2]).map fun entry => entry.key.statementIndex) = [2, 4] ∧
      ((produce policy program [tag 1, tag 2]).map fun entry => entry.conclusion) = [tag 1, result 1] := by
  decide +kernel

theorem declarations_and_interfaces_are_not_clauses (clause : Clause) :
    ¬ ClauseAt program 0 clause ∧ ¬ ClauseAt program 1 clause ∧
      ¬ ClauseAt program 3 clause ∧ ¬ ClauseAt program 5 clause := by
  simp [ClauseAt, program]

theorem no_implicit_same_round_fact_publication :
    ((produce policy program [tag 2]).map fun entry => entry.conclusion) = [tag 1] ∧
      ((produce policy program []).map fun entry => entry.conclusion) = [tag 1] := by
  decide +kernel

#print axioms complete_program_indices_and_results
#print axioms declarations_and_interfaces_are_not_clauses
#print axioms no_implicit_same_round_fact_publication

end Mettapedia.Languages.Datalog.ProgramGrounding.Controls
