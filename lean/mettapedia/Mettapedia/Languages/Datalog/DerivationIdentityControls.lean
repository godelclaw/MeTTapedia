import Mettapedia.Languages.Datalog.DerivationIdentity
import Mettapedia.Languages.Datalog.GroundingControls

set_option autoImplicit false

namespace Mettapedia.Languages.Datalog.DerivationIdentity.Controls

open Join

def route := Grounding.Controls.route

def routeKeys : List DerivationKey :=
  (join route.positiveAtoms Join.Controls.routeFacts []).filterMap (key? 7 route)

theorem canonical_route_bindings : routeKeys.map (·.grounding) =
    [[("X", .symbol "B"), ("Y", .symbol "D")],
     [("X", .symbol "C"), ("Y", .symbol "D")]] := by decide +kernel

theorem source_statement_index_retained : routeKeys.map (·.statementIndex) = [7,7] := by decide +kernel

theorem routes_remain_distinct : routeKeys.length = 2 ∧ routeKeys.Nodup := by decide +kernel

def oneAtom : Clause :=
  ⟨⟨["Goal"], [.var "Y"]⟩, [.atom ⟨["Edge"], [.var "X", .var "Y"]⟩]⟩

def duplicates : List GroundFact :=
  [⟨["Edge"], [.symbol "A", .symbol "B"]⟩, ⟨["Edge"], [.symbol "A", .symbol "B"]⟩]

def duplicateRows := join oneAtom.positiveAtoms duplicates []

theorem duplicate_validations_have_one_logical_key :
    duplicateRows.map (·.rowPositions) = [[0],[1]] ∧
      (duplicateRows.filterMap (key? 3 oneAtom)).eraseDups.length = 1 := by decide +kernel

theorem absent_variable_refuses_key :
    key? 3 oneAtom ⟨[("Y", .symbol "B")], [], []⟩ = none := by decide +kernel

theorem positional_arity_controls :
    decodeGrounding? oneAtom [] = none ∧
      decodeGrounding? oneAtom [.symbol "A", .symbol "B", .symbol "C"] = none ∧
      decodeGrounding? oneAtom [.symbol "A", .symbol "B"] =
        some [("X", .symbol "A"), ("Y", .symbol "B")] := by decide +kernel

theorem context_is_more_than_arity :
    let other : Clause :=
      ⟨⟨["Goal"], [.var "Y"]⟩, [.atom ⟨["Edge"], [.var "Z", .var "Y"]⟩]⟩
    decodeGrounding? oneAtom [.symbol "A", .symbol "B"] ≠
      decodeGrounding? other [.symbol "A", .symbol "B"] := by decide +kernel

#print axioms canonical_route_bindings
#print axioms routes_remain_distinct
#print axioms duplicate_validations_have_one_logical_key
#print axioms context_is_more_than_arity

end Mettapedia.Languages.Datalog.DerivationIdentity.Controls
