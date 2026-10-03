import MettapediaFourColor.TwoPortCoreElimination

/-!
# Actual source boundaries requiring joint two-port information

The two boundary words arise in proper colourings of the punctured
spherical examples. Here their failure to extend through the exact decoded
catalogue cores is proved directly by forced colours. The spherical
realizations remain separately checked program evidence.
-/

namespace FourColor.TwoPortCoreObstruction

open Color FiveTriangleCollapseObstruction SimpleGraph.BinaryConstraints

def upperWord : Fin 11 → Color := ![c3,c0,c3,c0,c3,c0,c2,c0,c2,c1,c2]
def lowerWord : Fin 10 → Color := ![c3,c1,c0,c3,c1,c2,c1,c0,c2,c0]

def UpperAllowed (v : Fin 18) (c : Color) : Prop :=
  ∀ i : Fin 11, upper.graph.Adj v (i.castAdd 7) → c ≠ upperWord i

def LowerAllowed (v : Fin 17) (c : Color) : Prop :=
  ∀ i : Fin 10, lower.graph.Adj v (i.castAdd 7) → c ≠ lowerWord i

instance (v : Fin 18) (c : Color) : Decidable (UpperAllowed v c) := by
  unfold UpperAllowed; infer_instance
instance (v : Fin 17) (c : Color) : Decidable (LowerAllowed v c) := by
  unfold LowerAllowed; infer_instance

theorem upper_lists : ∀ c : Color,
    (UpperAllowed 17 c ↔ c = c1) ∧
    (UpperAllowed 15 c ↔ c = c1 ∨ c = c2) ∧
    (UpperAllowed 12 c ↔ c = c1 ∨ c = c2) ∧
    (UpperAllowed 14 c ↔ c = c1 ∨ c = c3) ∧
    (UpperAllowed 13 c ↔ c = c1 ∨ c = c3) := by decide +kernel

theorem lower_lists : ∀ c : Color,
    (LowerAllowed 15 c ↔ c = c2) ∧
    (LowerAllowed 11 c ↔ c = c0 ∨ c = c2) ∧
    (LowerAllowed 14 c ↔ c = c2 ∨ c = c3) ∧
    (LowerAllowed 12 c ↔ c = c0 ∨ c = c3) := by decide +kernel

/-- Explicit witnesses accepted after replacing the first ear's joint
relation by its two marginals. The omitted vertex's displayed value is unused. -/
def upperMarginal : Fin 18 → Color :=
  ![c3,c0,c3,c0,c3,c0,c2,c0,c2,c1,c2,c0,c1,c0,c3,c2,c3,c1]

def lowerMarginal : Fin 17 → Color :=
  ![c3,c1,c0,c3,c1,c2,c1,c0,c2,c0,c1,c0,c0,c0,c3,c2,c2]

theorem upper_marginal_passes :
    (∀ i : Fin 11, upperMarginal (i.castAdd 7) = upperWord i) ∧
    (∀ x y : Fin 18, x ≠ 13 → y ≠ 13 → upper.graph.Adj x y →
      upperMarginal x ≠ upperMarginal y) ∧
    (∃ c, UpperAllowed 13 c ∧ c ≠ upperMarginal 12) ∧
    (∃ c, UpperAllowed 13 c ∧ c ≠ upperMarginal 14) := by decide +kernel

theorem lower_marginal_passes :
    (∀ i : Fin 10, lowerMarginal (i.castAdd 7) = lowerWord i) ∧
    (∀ x y : Fin 17, x ≠ 12 → y ≠ 12 → lower.graph.Adj x y →
      lowerMarginal x ≠ lowerMarginal y) ∧
    (∃ c, LowerAllowed 12 c ∧ c ≠ lowerMarginal 11) ∧
    (∃ c, LowerAllowed 12 c ∧ c ≠ lowerMarginal 14) := by decide +kernel

/-- The source boundary cannot extend; the contradiction uses one shared
interior colour, not a search through all core assignments. -/
theorem upper_no_extension (C : upper.graph.Coloring Color)
    (boundary : ∀ i : Fin 11, C (i.castAdd 7) = upperWord i) : False := by
  have allowed (v : Fin 18) : UpperAllowed v (C v) := by
    intro i hi
    simpa only [boundary i] using C.valid hi
  have h17 : C 17 = c1 := (upper_lists _).1.mp (allowed 17)
  have h15 : C 15 = c2 := ((upper_lists _).2.1.mp (allowed 15)).resolve_left
    (h17 ▸ C.valid (show upper.graph.Adj 15 17 from by decide +kernel))
  have h12 : C 12 = c1 := ((upper_lists _).2.2.1.mp (allowed 12)).resolve_right
    (h15 ▸ C.valid (show upper.graph.Adj 12 15 from by decide +kernel))
  have h14 : C 14 = c3 := ((upper_lists _).2.2.2.1.mp (allowed 14)).resolve_left
    (h12 ▸ C.valid (show upper.graph.Adj 14 12 from by decide +kernel))
  exact (separate_ports_not_joint (show c1 ≠ c3 by decide)).2.2
    ⟨C 13, (upper_lists _).2.2.2.2.mp (allowed 13),
      h12 ▸ C.valid (show upper.graph.Adj 13 12 from by decide +kernel),
      h14 ▸ C.valid (show upper.graph.Adj 13 14 from by decide +kernel)⟩

theorem lower_no_extension (C : lower.graph.Coloring Color)
    (boundary : ∀ i : Fin 10, C (i.castAdd 7) = lowerWord i) : False := by
  have allowed (v : Fin 17) : LowerAllowed v (C v) := by
    intro i hi
    simpa only [boundary i] using C.valid hi
  have h15 : C 15 = c2 := (lower_lists _).1.mp (allowed 15)
  have h11 : C 11 = c0 := ((lower_lists _).2.1.mp (allowed 11)).resolve_right
    (h15 ▸ C.valid (show lower.graph.Adj 11 15 from by decide +kernel))
  have h14 : C 14 = c3 := ((lower_lists _).2.2.1.mp (allowed 14)).resolve_left
    (h15 ▸ C.valid (show lower.graph.Adj 14 15 from by decide +kernel))
  exact (separate_ports_not_joint (show c0 ≠ c3 by decide)).2.2
    ⟨C 12, (lower_lists _).2.2.2.mp (allowed 12),
      h11 ▸ C.valid (show lower.graph.Adj 12 11 from by decide +kernel),
      h14 ▸ C.valid (show lower.graph.Adj 12 14 from by decide +kernel)⟩

end FourColor.TwoPortCoreObstruction
