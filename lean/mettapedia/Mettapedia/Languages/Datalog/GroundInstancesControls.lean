import Mettapedia.Languages.Datalog.GroundInstancesComplete
import Mettapedia.Languages.Datalog.ComparisonControls
import Mettapedia.Languages.Datalog.DerivationIdentityControls

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.GroundInstances.Controls

open Join

def policy := Comparisons.Controls.integerPolicy

def guarded : Clause :=
  ⟨⟨["Eligible"], [.var "X"]⟩,
    [.atom ⟨["Score"], [.var "X"]⟩,
     .comparison ⟨.less, .var "X", .literal (.number 3)⟩]⟩

def scores : List GroundFact :=
  [⟨["Score"], [.number 1]⟩, ⟨["Score"], [.number 2]⟩, ⟨["Score"], [.number 4]⟩]

theorem guard_filters_actual_groundings :
    (produce policy 9 guarded scores).map (fun item => (item.key.statementIndex, item.conclusion.values)) =
      [(9,[.number 1]), (9,[.number 2])] := by decide +kernel

theorem no_guard_default_for_unbound_variable :
    let invalid := {guarded with body :=
      [.atom ⟨["Score"], [.var "X"]⟩,
       .comparison ⟨.less, .var "Y", .literal (.number 3)⟩]}
    produce policy 9 invalid scores = [] := by decide +kernel

def routes := produce policy 7 Grounding.Controls.route Join.Controls.routeFacts

theorem one_fact_two_source_keys :
    (routes.map (·.conclusion)).eraseDups.length = 1 ∧
      (routes.map (·.key)).eraseDups.length = 2 := by decide +kernel

theorem duplicate_validation_does_not_add_logical_keys :
    let emitted := produce policy 3 DerivationIdentity.Controls.oneAtom DerivationIdentity.Controls.duplicates
    emitted.map (·.rowPositions) = [[0],[1]] ∧
      (emitted.map (·.key)).eraseDups.length = 1 := by decide +kernel

theorem forged_conclusion_absent :
    ¬ ∃ item ∈ produce policy 9 guarded scores, item.conclusion = ⟨["Eligible"], [.number 4]⟩ := by
  decide +kernel

theorem zero_body_constant_clause :
    (produce policy 2 ⟨⟨["Unit"], [.literal (.number 5)]⟩,[]⟩ []).map (·.conclusion) =
      [⟨["Unit"],[.number 5]⟩] := by decide +kernel

#print axioms guard_filters_actual_groundings
#print axioms one_fact_two_source_keys
#print axioms duplicate_validation_does_not_add_logical_keys
#print axioms zero_body_constant_clause

end Mettapedia.Languages.Datalog.GroundInstances.Controls
