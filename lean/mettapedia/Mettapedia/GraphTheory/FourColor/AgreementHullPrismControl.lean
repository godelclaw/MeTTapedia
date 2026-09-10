import Mettapedia.GraphTheory.FourColor.AgreementClosedCuts
import Mettapedia.GraphTheory.FourColor.ColorAlgebra

/-!+# Agreement closure can swallow a properly coloured cube

Two proper nonzero edge labellings differ on the upper square only.
Nevertheless their agreeing subgraph is connected: it contains the lower
square and every spoke. Thus closing a nonempty seed under agreeing edges
leaves no opposite shore. This refutes a generic construction rule, not a
claim restricted to absolute deletion minima or least counterexamples.
-/

namespace Mettapedia.GraphTheory.FourColor.AgreementHullPrismControl

open SimpleGraph AgreementClosedCuts

def edges : Finset (Sym2 (Fin 8)) :=
  {s(0, 1), s(1, 2), s(2, 3), s(3, 0),
   s(4, 5), s(5, 6), s(6, 7), s(7, 4),
   s(0, 4), s(1, 5), s(2, 6), s(3, 7)}

def cube : SimpleGraph (Fin 8) := SimpleGraph.fromEdgeSet (edges : Set (Sym2 (Fin 8)))

instance : DecidableRel cube.Adj := inferInstanceAs (DecidableRel (SimpleGraph.fromEdgeSet _).Adj)

def left (e : Sym2 (Fin 8)) : Color :=
  if e ∈ ({s(0, 1), s(2, 3), s(4, 5), s(6, 7)} : Finset _) then red
  else if e ∈ ({s(1, 2), s(3, 0), s(5, 6), s(7, 4)} : Finset _) then blue
  else purple

def right (e : Sym2 (Fin 8)) : Color :=
  if e ∈ ({s(0, 1), s(2, 3)} : Finset _) then blue
  else if e ∈ ({s(1, 2), s(3, 0)} : Finset _) then red
  else left e

/-- Properness at every actual vertex, including all retained spokes. -/
theorem proper_nonzero :
    (∀ u v, cube.Adj u v → left s(u, v) ≠ 0 ∧ right s(u, v) ≠ 0) ∧
    (∀ u v w, cube.Adj u v → cube.Adj u w → v ≠ w →
      left s(u, v) ≠ left s(u, w) ∧ right s(u, v) ≠ right s(u, w)) := by
  decide +kernel

theorem disagrees_exactly_on_top : ∀ e ∈ edges,
    left e ≠ right e ↔ e ∈ ({s(0, 1), s(1, 2), s(2, 3), s(3, 0)} : Finset _) := by
  decide +kernel

abbrev agreeing := agreementGraph cube left right

theorem reachable_from_zero (v : Fin 8) : agreeing.Reachable 0 v := by
  have h04 : agreeing.Adj 0 4 := by decide
  have h45 : agreeing.Adj 4 5 := by decide
  have h56 : agreeing.Adj 5 6 := by decide
  have h67 : agreeing.Adj 6 7 := by decide
  have h51 : agreeing.Adj 5 1 := by decide
  have h62 : agreeing.Adj 6 2 := by decide
  have h73 : agreeing.Adj 7 3 := by decide
  have h05 := h04.reachable.trans h45.reachable
  have h06 := h05.trans h56.reachable
  have h07 := h06.trans h67.reachable
  fin_cases v
  · exact .refl _
  · exact h05.trans h51.reachable
  · exact h06.trans h62.reachable
  · exact h07.trans h73.reachable
  · exact h04.reachable
  · exact h05
  · exact h06
  · exact h07

theorem agreeing_preconnected : agreeing.Preconnected :=
  fun u v => (reachable_from_zero u).symm.trans (reachable_from_zero v)

theorem every_nonempty_hull_is_univ {A : Set (Fin 8)} (hA : A.Nonempty) :
    hull agreeing A = Set.univ :=
  hull_eq_univ_of_preconnected agreeing agreeing_preconnected hA

/-- No cut separating these two upper vertices can avoid all agreeing edges. -/
theorem no_closed_separation : ¬ ∃ S : Set (Fin 8),
    ({0} : Set (Fin 8)) ⊆ S ∧ ({2} : Set (Fin 8)) ⊆ Sᶜ ∧ Closed agreeing S := by
  intro h
  exact (exists_closed_separator_iff agreeing {0} {2}).mp h 0 (by simp) 2 (by simp)
    (reachable_from_zero 2)

end Mettapedia.GraphTheory.FourColor.AgreementHullPrismControl
