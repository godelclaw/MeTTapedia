import Mettapedia.GraphTheory.FourColor.ZigzagTubeReplacement
import Mettapedia.GraphTheory.FourColor.ZigzagRingTwoColour
import Mettapedia.GraphTheory.FourColor.OpenTangleClosedWitness

/-!
# Two rows reconstruct a cyclically shifted wiring

Every nonzero input word has a genuine first ring colouring. Its complementary
ring returns the same input with a one-port shift. This includes words using
all three colours and words missing a colour.

Consequently a compatible exterior of arbitrary size reconstructs an actual
closed colouring around the two rows. This is the colouring component of a
proposed replacement by free wires. The geometry, bridge freedom and strict
reduction of that replacement are separate obligations.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing.ShiftedWiring

open GoertzelV24CorridorPumping GoertzelV24OpenTangleComposition
open GoertzelV24TwoEdgeCutMinimality OpenTangleClosedWitness

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable tubeVertexFintype tubeInteriorFintype

variable (k : ℕ) [NeZero k]

/-- No fullness condition is required: a missing colour supplies a constant
cursor, while a full word uses the existing local cursor construction. -/
theorem exists_first_ring (hk : 3 ≤ k) (x : Fin k → Color)
    (hx : ∀ i, x i ≠ 0) : ∃ y, Step k x y := by
  classical
  by_cases hall : ∀ c : Color, c ≠ 0 → ∃ i, x i = c
  · exact Full.exists_step k hk ⟨hx, hall⟩
  · push Not at hall
    obtain ⟨c, hc, hmissing⟩ := hall
    exact ⟨x, (step_iff_of_missing k x x hx hc hmissing).mpr (Or.inl rfl)⟩

/-- One shared intermediate word joins the first ring to its complement. -/
theorem two_rows (hk : 3 ≤ k) (x : Fin k → Color) (hx : ∀ i, x i ≠ 0) :
    (tube k 1).Accepts x (shift k x) := by
  obtain ⟨y, hy⟩ := exists_first_ring k hk x hx
  apply (tube_accepts_iff k 1 x (shift k x)).mpr
  exact .succ hy (.succ (hy.two_ring_shift k) (.zero _))

variable {V I B : Type*} [Fintype V] [DecidableEq V]
  [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
  (O : OpenTangleData V I B) (matching : B ≃ Fin k ⊕ Fin k)

/-- The exterior's two boundary words are joined by the proposed shifted
free wires. The colours on every exterior dart are retained in reconstruction. -/
theorem closed_reconstruction (hk : 3 ≤ k) (l : I ⊕ B → Color)
    (hl : IsColor O l)
    (hwire : ∀ i, l (.inr (matching.symm (.inr i))) =
      l (.inr (matching.symm (.inl (i + 1))))) :
    ∃ c : (sewn O (tube k 1).data matching).EdgeColoring Color,
      (sewn O (tube k 1).data matching).IsTaitEdgeColoring c ∧
      ∀ d, c ((sewn O (tube k 1).data matching).edgeOf
        (composeDartEquiv (.inl d))) = l d := by
  let x : Fin k → Color := fun i => l (.inr (matching.symm (.inl i)))
  have hx : ∀ i, x i ≠ 0 := fun i => hl.2.2 _
  obtain ⟨r, hr, hleft, hright⟩ := two_rows k hk x hx
  have hboundary (p : Fin k ⊕ Fin k) :
      l (.inr (matching.symm p)) = r (.inr p) := by
    cases p with
    | inl i => exact (congrFun hleft i).symm
    | inr i => exact (hwire i).trans (congrFun hright i).symm
  exact glue O (tube k 1).data matching l r hl hr
    (fun b => by simpa using hboundary (matching b))

end
end Mettapedia.GraphTheory.FourColor.ZigzagRing.ShiftedWiring
