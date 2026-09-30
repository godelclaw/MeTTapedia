import Mettapedia.GraphTheory.FourColor.PaddedCycleCapEven
import Mettapedia.GraphTheory.FourColor.RotationSystemExactTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideReassembly

/-! # Transport the cap reduction to an exactly represented ambient graph

Dart and vertex equivalences must preserve edge mates, incidence and cyclic
rotations. Such a representation transfers the strict family reduction and
excludes the represented cap from a vertex-minimal counterexample. Supplying
these equivalences from broader geometric recognition remains a separate task.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap

open GoertzelV24OpenTangleComposition OpenTangleClosedWitness
open GoertzelV24TwoEdgeCutMinimality GoertzelV24VertexSideReassembly

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (m : ℕ) [NeZero m] (hm : 2 ≤ m) (heven : Even m)
  {V I B W E : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B] [Fintype W] [DecidableEq W] [Fintype E] [DecidableEq E]
  (outside : OpenTangleData V I B) (seam : B ≃ Empty ⊕ Fin (m*2))
  (RS : RotationSystem W E)
  (d : RS.D ≃ (sewn outside (indexedCap m hm) seam).D)
  (v : W ≃ V ⊕ Vertex m)
  (ha : ∀ x, d (RS.alpha x) = (sewn outside (indexedCap m hm) seam).alpha (d x))
  (hv : ∀ x, v (RS.vertOf x) = (sewn outside (indexedCap m hm) seam).vertOf (d x))
  (hr : ∀ x, d (RS.rho x) = (sewn outside (indexedCap m hm) seam).rho (d x))

include heven d v ha hv hr in
/-- Exact graph representations transport the reduction, not merely its
existence-of-colouring observation. -/
theorem exact_reduction (h : BridgelessSphericalCubicMapData RS) :
    Fintype.card (V ⊕ Fin (m*2)) < Fintype.card W ∧
      BridgelessSphericalCubicMapData
        (sewn outside (CycleCap.cap (m*2) (by omega)) seam) ∧
      (RotationSystemTaitColorable (sewn outside (CycleCap.cap (m*2) (by omega)) seam) →
        RotationSystemTaitColorable RS) := by
  have hclass := RotationSystemExactTransport.mapClass RS
    (sewn outside (indexedCap m hm) seam) d v ha hv hr h
  obtain ⟨hcard,hsmall,hcolour⟩ := strict_even_reduction m hm heven outside seam hclass
  rw [← Fintype.card_congr v] at hcard
  exact ⟨hcard,hsmall,fun hc =>
    (rotationSystemTaitColorable_iff_of_dartEquiv RS
      (sewn outside (indexedCap m hm) seam) d v ha hv).mpr (hcolour hc)⟩

end

noncomputable section
universe u
variable (m : ℕ) [NeZero m] (hm : 2 ≤ m) (heven : Even m)
  {V I B W : Type u} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B] [Fintype W] [DecidableEq W]
  {G : SimpleGraph W} [DecidableRel G.Adj]
  (rotation : SimpleGraphDartRotation.Data G)
  (outside : OpenTangleData V I B) (seam : B ≃ Empty ⊕ Fin (m*2))

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

include heven in
/-- An exactly recognized even cap cannot occur in a least counterexample. -/
theorem no_even_cap
    (minimal : GraphBackedVertexMinimalTaitCounterexample rotation)
    (d : rotation.toRotationSystem.D ≃ (sewn outside (indexedCap m hm) seam).D)
    (v : W ≃ V ⊕ Vertex m)
    (ha : ∀ x, d (rotation.toRotationSystem.alpha x) =
      (sewn outside (indexedCap m hm) seam).alpha (d x))
    (hv : ∀ x, v (rotation.toRotationSystem.vertOf x) =
      (sewn outside (indexedCap m hm) seam).vertOf (d x))
    (hr : ∀ x, d (rotation.toRotationSystem.rho x) =
      (sewn outside (indexedCap m hm) seam).rho (d x)) : False := by
  obtain ⟨hcard,hclass,hcolour⟩ := exact_reduction m hm heven outside seam
    rotation.toRotationSystem d v ha hv hr minimal.toBridgelessSphericalCubicMapData
  exact minimal.notColorable (hcolour (minimal.smallerColorable _ hcard hclass))

end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap
