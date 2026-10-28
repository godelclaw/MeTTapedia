import Mettapedia.Languages.Datalog.Observation
import Mettapedia.Languages.Datalog.ComparisonControls

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.Observation.Controls

private def edge (first second : Int) : GroundFact :=
  ⟨["Edge"], [.number first, .number second]⟩

private def answer (value : Int) : GroundFact := ⟨["Answer"], [.number value]⟩

private def clause : Clause :=
  ⟨⟨["Answer"], [.var "X"]⟩,
    [.atom ⟨["Edge"], [.var "X", .var "Y"]⟩,
     .atom ⟨["Edge"], [.var "Y", .literal (.number 9)]⟩,
     .comparison ⟨.less, .var "Y", .literal (.number 3)⟩]⟩

private def known : List GroundFact :=
  [edge 0 1, edge 0 2, edge 1 9, edge 2 9, edge 0 4, edge 4 9]

private def key (via : Int) : DerivationKey :=
  ⟨7, [("X", .number 0), ("Y", .number via)], [edge 0 via, edge via 9]⟩

private def policy := Comparisons.Controls.integerPolicy

theorem two_routes_one_fact :
    factSet policy 7 clause known = {answer 0} ∧
      (keyBag policy 7 clause known).card = 2 ∧
      (keyBag policy 7 clause known).count (key 1) = 1 ∧
      (keyBag policy 7 clause known).count (key 2) = 1 ∧
      (keyBag policy 7 clause known).count (key 4) = 0 := by
  decide +kernel

theorem duplicate_validation_is_not_a_new_key :
    (firings policy 7 clause (edge 0 1 :: known)).length = 3 ∧
      (keyBag policy 7 clause (edge 0 1 :: known)).card = 2 ∧
      factSet policy 7 clause (edge 0 1 :: known) = {answer 0} := by
  decide +kernel

theorem permutation_keeps_both_observations :
    factSet policy 7 clause known.reverse = factSet policy 7 clause known ∧
      keyBag policy 7 clause known.reverse = keyBag policy 7 clause known := by
  constructor
  · exact factSet_congr _ _ _ _ _ (by simp)
  · exact keyBag_congr _ _ _ _ _ (by simp)

theorem missing_guarded_and_wrong_conclusion_controls :
    factSet policy 7 clause [edge 0 1, edge 0 2] = ∅ ∧
      factSet policy 7 clause [edge 0 4, edge 4 9] = ∅ ∧
      (keyBag policy 7 clause [edge 0 1, edge 1 9]).card = 1 ∧
      answer 1 ∉ factSet policy 7 clause known := by
  decide +kernel

#print axioms two_routes_one_fact
#print axioms duplicate_validation_is_not_a_new_key
#print axioms permutation_keeps_both_observations
#print axioms missing_guarded_and_wrong_conclusion_controls

end Mettapedia.Languages.Datalog.Observation.Controls
