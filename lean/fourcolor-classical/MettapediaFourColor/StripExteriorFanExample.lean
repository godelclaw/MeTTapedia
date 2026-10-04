import MettapediaFourColor.StripExteriorFan
import MettapediaFourColor.StripSixMixedExample

/-! # The forced fan on an existing spherical occurrence

The original difficult joint branch satisfies the exact interior-block and
exterior-completeness hypotheses. The geometric fan therefore prevents any
zero/three phase from reaching the complementary repair boundary. This does
not prevent the existing mixed-pair repair of the same colouring.
-/

namespace FourColor.StripExteriorFanExample

open SimpleGraph Color StripSixMixedExample

theorem interior_block : StripExteriorFan.InteriorBlock patch where
  first := by apply Dart.ext; decide +kernel
  second := by apply Dart.ext; decide +kernel
  only := by decide +kernel

/-- Every actual outside neighbour is represented in the exterior graph. -/
theorem complete : ∀ v, patch.Exterior v → ambient.Adj (patch.point 1) v →
    ∃ w, reading.embedding w = v := by
  unfold StripSixBarrierGeometry.Patch.Exterior
  decide +kernel

theorem forced_path : ∃ p : exterior.Walk (port 0) (port 2),
    ∀ v ∈ p.support, state 0 v = c0 ∨ state 0 v = c3 :=
  StripExteriorFan.bichromatic_path patch interior_block cyclic triangular reading complete
    (state 0) (initial_form 1) missing_colour

/-- A whole phase fails as a preparation, not merely one chosen switch. -/
theorem no_preparation (D : exterior.Coloring Color)
    (phase : Relation.ReflTransGen (KempePairHistory.Step c0 c3) (state 0) D) :
    ¬ ∀ i, D (port i) = StripComplementaryRepair.input i :=
  StripExteriorFan.no_preparation patch interior_block cyclic triangular reading complete
    (state 0) D initial_form missing_colour phase

end FourColor.StripExteriorFanExample
