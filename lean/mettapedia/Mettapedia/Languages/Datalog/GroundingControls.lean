import Mettapedia.Languages.Datalog.Grounding
import Mettapedia.Languages.Datalog.JoinControls

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.Grounding.Controls

def route : Clause :=
  ⟨⟨["Goal"], [.var "Y"]⟩, Join.Controls.routeAtoms.map Premise.atom⟩

def unboundHead : Clause := {route with head := ⟨["Goal"], [.var "Z"]⟩}

theorem head_range_checks :
    route.checkRangeRestriction = true ∧ unboundHead.checkRangeRestriction = false := by decide +kernel

theorem two_joins_one_conclusion :
    (Join.join route.positiveAtoms Join.Controls.routeFacts []).filterMap
      (fun row => head? row.environment route.head) =
        [⟨["Goal"], [.symbol "D"]⟩, ⟨["Goal"], [.symbol "D"]⟩] := by decide +kernel

theorem no_default_for_unbound_head :
    (Join.join unboundHead.positiveAtoms Join.Controls.routeFacts []).filterMap
      (fun row => head? row.environment unboundHead.head) = [] := by decide +kernel

theorem wrong_conclusion_refused :
    head? [("Y", .symbol "D")] route.head ≠ some ⟨["Goal"], [.symbol "Other"]⟩ := by decide +kernel

theorem wrong_predicate_refused :
    head? [("Y", .symbol "D")] route.head ≠ some ⟨["Other"], [.symbol "D"]⟩ := by decide +kernel

#print axioms two_joins_one_conclusion
#print axioms no_default_for_unbound_head
#print axioms wrong_conclusion_refused

end Mettapedia.Languages.Datalog.Grounding.Controls
