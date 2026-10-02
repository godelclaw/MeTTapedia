import MettapediaFourColor.WheelBoundaryLayouts
import MettapediaFourColor.ExceptionalCoreInduced

/-!
# An actual two-five degree profile constructs its complete wheel

The position of the second five is selected from the actual neighbour orbit.
The same wheel core, shared outer seams and short-cycle completion apply at
every position. All twelve ports are distinct and lie within radius two.
No boundary colouring repair or global coverage is assumed here.
-/

namespace FourColor.TwoFiveWheelOccurrence

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality
open MinimalExceptionalEmbedding (graph rotation)
open WheelBoundaryCompletion (Occurrence)

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (original : Data G) (minimal : GraphBackedVertexMinimalTaitCounterexample original)

/-- A degree profile fixes the shared core reading, including its actual rotation. -/
def reading (p : Fin 6) (d : (graph original minimal).Dart)
    (seven : (graph original minimal).degree d.fst = 7)
    (profile : ∀ i : Fin 7,
      (graph original minimal).degree (WheelNeighborhood.neighbor (rotation original minimal) d i) =
        if i = 0 ∨ i = TwoFiveWheelData.selected p then 5 else 6) :
    WheelBoundaryCompletion.Reading (WheelBoundaryLayouts.twoFive p)
      (rotation original minimal) where
  map := D3009Wheel.hom _ d (MinimalExceptionalEmbedding.triangular original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal) seven
  degree_eq := by
    intro i
    change (graph original minimal).degree (D3009Wheel.vertex (rotation original minimal) d i) = _
    have cases : i = 0 ∨ ∃ j, i = D3009Wheel.rim j := by revert i; decide +kernel
    rcases cases with rfl | ⟨j,rfl⟩
    · rw [D3009Wheel.vertex_center, WheelBoundaryLayouts.center_degree]
      exact seven
    · rw [D3009Wheel.vertex_rim, WheelBoundaryLayouts.degrees]
      exact profile j
  face := D3009Wheel.face _ d (MinimalExceptionalEmbedding.cyclic original minimal) seven

/-- The degree profile and actual short-cycle laws discharge all collision
and embedding conditions. -/
def occurrence (p : Fin 6) (d : (graph original minimal).Dart)
    (seven : (graph original minimal).degree d.fst = 7)
    (profile : ∀ i : Fin 7,
      (graph original minimal).degree (WheelNeighborhood.neighbor (rotation original minimal) d i) =
        if i = 0 ∨ i = TwoFiveWheelData.selected p then 5 else 6) :
    Occurrence (WheelBoundaryLayouts.twoFive p) (rotation original minimal) := by
  let r := reading original minimal p d seven profile
  let tri := MinimalExceptionalEmbedding.triangular original minimal
  let cyc := MinimalExceptionalEmbedding.cyclic original minimal
  exact WheelBoundaryCompletion.complete r tri cyc
    (D3009Wheel.injective _ d cyc seven)
    (fun i j h => (D3009Wheel.edge_iff _ d tri cyc seven
      (fun _ _ _ => MinimalExceptionalEmbedding.triangle_facial original minimal) i j).mp h)
    (fun _ _ _ => MinimalExceptionalEmbedding.triangle_facial original minimal)
    (fun _ _ _ _ => ExceptionalCoreInduced.four_cycle_chord original minimal)

/-- Select the position from the second actual five, preserving both marked
vertices rather than choosing unrelated copies of the local profile. -/
theorem supplied (d : (graph original minimal).Dart)
    (seven : (graph original minimal).degree d.fst = 7)
    (five : (graph original minimal).degree d.snd = 5)
    (q : _) (adj : (graph original minimal).Adj d.fst q)
    (other_five : (graph original minimal).degree q = 5) (distinct : q ≠ d.snd)
    (six : ∀ w, (graph original minimal).Adj d.fst w → w ≠ d.snd → w ≠ q →
      (graph original minimal).degree w = 6) :
    ∃ p : Fin 6, ∃ o : Occurrence (WheelBoundaryLayouts.twoFive p) (rotation original minimal),
      o.hom 12 = d.fst ∧ o.hom 13 = d.snd ∧
      o.hom ((D3009Wheel.rim (TwoFiveWheelData.selected p)).natAdd 12) = q := by
  let cyc := MinimalExceptionalEmbedding.cyclic original minimal
  obtain ⟨i, hi⟩ := WheelNeighborhood.covers (rotation original minimal) d cyc seven adj
  have nz : i ≠ 0 := by
    intro eq; subst i; exact distinct hi.symm
  let p : Fin 6 := ⟨i.val - 1, by have := i.isLt; omega⟩
  have selected : TwoFiveWheelData.selected p = i := by
    apply Fin.ext
    have ip : 0 < i.val := Fin.pos_iff_ne_zero.mpr nz
    simp only [TwoFiveWheelData.selected, p]
    omega
  have profile (j : Fin 7) :
      (graph original minimal).degree (WheelNeighborhood.neighbor (rotation original minimal) d j) =
        if j = 0 ∨ j = TwoFiveWheelData.selected p then 5 else 6 := by
    by_cases zero : j = 0
    · subst j
      rw [ite_eq_left (Or.inl rfl)]
      exact five
    by_cases same : j = i
    · subst j
      rw [selected, ite_eq_left (Or.inr rfl), hi]
      exact other_five
    rw [ite_eq_right (by simpa [selected] using And.intro zero same)]
    apply six _ (WheelNeighborhood.adjacent _ d j)
    · intro eq
      exact zero (WheelNeighborhood.neighbor_injective _ d cyc seven (by decide)
        (show WheelNeighborhood.neighbor (rotation original minimal) d j =
          WheelNeighborhood.neighbor (rotation original minimal) d (0 : Fin 7) from eq))
    · intro eq
      exact same (WheelNeighborhood.neighbor_injective _ d cyc seven (by decide) (eq.trans hi.symm))
  refine ⟨p, occurrence original minimal p d seven profile, rfl, rfl, ?_⟩
  change WheelBoundaryCompletion.vertex (reading original minimal p d seven profile)
    ((D3009Wheel.rim (TwoFiveWheelData.selected p)).natAdd 12) = q
  rw [WheelBoundaryCompletion.vertex_core]
  change D3009Wheel.vertex (rotation original minimal) d
    (D3009Wheel.rim (TwoFiveWheelData.selected p)) = q
  rw [D3009Wheel.vertex_rim, selected]
  exact hi

end
end FourColor.TwoFiveWheelOccurrence
