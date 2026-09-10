import Mettapedia.GraphTheory.FourColor.MarkedSquareBoundaryReduction

/-!
# Incidence semantics of the boundary-observation replacement

The digon-and-wire fibre is the actual nonzero proper edge-colouring
predicate on the displayed six-vertex graph with four degree-one ports.
This separates a physical incidence check from ambient seam admissibility.
-/

namespace Mettapedia.GraphTheory.FourColor.MarkedSquareBoundaryReduction

def Incident (v : Fin 6) (e : Fin 5) : Prop :=
  (endpoints e).1 = v ∨ (endpoints e).2 = v
  deriving Decidable

def degree (v : Fin 6) : Nat :=
  (Finset.univ.filter (Incident v)).card

def EdgeProper (c : DigonWireColoring) : Prop :=
  (∀ e, c e ≠ 0) ∧ ∀ v e f, e ≠ f → Incident v e → Incident v f → c e ≠ c f
  deriving Decidable

theorem proper_iff (c : DigonWireColoring) :
    EdgeProper c ↔
      ProperColorTriple (c 2) (c 0) (c 1) ∧
      ProperColorTriple (c 3) (c 0) (c 1) ∧ c 4 ≠ 0 := by
  simp only [EdgeProper, Incident, endpoints, Fin.forall_fin_succ,
    Fin.succ_zero_eq_one, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
    ProperColorTriple]
  aesop

theorem extension_iff_edgeProper (w : SquareBoundaryWord) (c : DigonWireColoring) :
    IsDigonWireExtension w c ↔ EdgeProper c ∧
      c 2 = w 0 ∧ c 3 = w 1 ∧ c 4 = w 2 ∧ c 4 = w 3 := by
  rw [proper_iff]
  simp only [IsDigonWireExtension]
  tauto

theorem degree_and_no_loops :
    (∀ v : Fin 6, degree v = if v.val < 2 then 3 else 1) ∧
    (∀ e : Fin 5, (endpoints e).1 ≠ (endpoints e).2) := by decide

/-- The retained marked edge and reference wire have no common endpoint. -/
theorem marked_reference_nonadjacent :
    ¬ ∃ v, Incident v 0 ∧ Incident v 4 := by decide

/-- The local physical carrier has two rather than four cubic vertices.
The four terminal vertices are present on both sides of the replacement. -/
theorem fewer_internal_vertices :
    (Finset.univ.filter fun v : Fin 6 => degree v = 3).card < 4 := by decide

/-- Exact equality-fibre transport to the incidence-level graph, not an
uninterpreted state variable. -/
def physicalEqualityEquiv (w : SquareBoundaryWord) :
    {x // IsSquareExtension w x ∧ x 0 = w 2} ≃
      {c // EdgeProper c ∧
        c 2 = w 0 ∧ c 3 = w 1 ∧ c 4 = w 2 ∧ c 4 = w 3 ∧ c 0 = c 4} :=
  (equalityEquiv w).trans
    (Equiv.subtypeEquivRight fun c => by
      rw [extension_iff_edgeProper]
      constructor
      · rintro ⟨⟨hp, h0, h1, h2, h3⟩, hm⟩
        exact ⟨hp, h0, h1, h2, h3, hm.trans h2.symm⟩
      · rintro ⟨hp, h0, h1, h2, h3, hm⟩
        exact ⟨⟨hp, h0, h1, h2, h3⟩, hm.trans h2⟩)

end Mettapedia.GraphTheory.FourColor.MarkedSquareBoundaryReduction
