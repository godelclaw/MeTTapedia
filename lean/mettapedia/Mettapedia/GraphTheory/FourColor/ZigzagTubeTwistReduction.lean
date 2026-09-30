import Mettapedia.GraphTheory.FourColor.ZigzagTubeReplacement
import Mettapedia.GraphTheory.FourColor.TwoSidedBoundaryVertex
import Mettapedia.GraphTheory.FourColor.OpenTangleClosedWitness

/-!
# Two-row deletion with a cyclic change of seam matching

A ring colouring followed by its complementary colouring shifts the input
word once. Applying the shifted first colouring gives three rings from one.
The shortened tube moves its right ports by one cyclic position. That move
commutes with the actual boundary face return, so Euler characteristic,
cubicity, connectedness and bridge-freedom survive in any sewn exterior.

The colour statement is directed: every smaller colouring reconstructs.
Equality of the two boundary supports is neither required nor asserted.
No finite colouring table or complete Four Colour theorem is used.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing

open GoertzelV24CorridorPumping GoertzelV24OpenTangleComposition
open SerialTangleSmallCutTransfer TwoSidedBoundaryReindex
open GoertzelV24TwoEdgeCutMinimality GoertzelV24CompositeSeamCubic
open GoertzelV24CompositeSeamMultigraph OpenTangleVertexReflection
open OpenTanglePortReplacement OpenTangleReplacementEuler
open OpenTangleRewireFaces

set_option backward.isDefEq.respectTransparency false

variable (k : ℕ) [NeZero k]

/-- Repeat the final colouring, with its complementary middle ring. -/
theorem transfer_insert_two {n : ℕ} {x y : Fin k → Color}
    (h : ExactRelationalTransfer (Step k) (n + 1) x y) :
    ExactRelationalTransfer (Step k) (n + 3) x (shift k y) := by
  induction n generalizing x with
  | zero =>
    cases h with
    | succ hs ht =>
      cases ht
      have shifted : Step k (shift k x) (shift k y) := hs.rotate_step k 1
      exact .succ hs (.succ (hs.two_ring_shift k) (.succ shifted (.zero _)))
  | succ n ih =>
    cases h with
    | succ hs ht => exact .succ hs (ih ht)

/-- The theorem retains actual compatible colourings of every ring. -/
theorem tube_insert_two (n : ℕ) {x y : Fin k → Color}
    (h : (tube k n).Accepts x y) : (tube k (n + 2)).Accepts x (shift k y) := by
  apply (tube_accepts_iff k (n + 2) _ _).mpr
  exact transfer_insert_two k ((tube_accepts_iff k n _ _).mp h)

/-- New right port `i` denotes old right port `i+1`. -/
def twistPorts : Equiv.Perm (Fin k ⊕ Fin k) :=
  Equiv.sumCongr (Equiv.refl _) (Equiv.addRight 1)

noncomputable section
attribute [local instance] Classical.propDecidable tubeVertexFintype tubeInteriorFintype

def twistedTube (n : ℕ) :
    TwoSidedOpenTangleData (tube k n).V (tube k n).I (Fin k) (Fin k) :=
  reindex (tube k n).data (twistPorts k)

theorem twistedTube_accepts (n : ℕ) (x y : Fin k → Color) :
    (twistedTube k n).AcceptsBoundaryWords x (shift k y) ↔ (tube k n).Accepts x y := by
  have h := accepts_reindex (tube k n).data (twistPorts k) (Sum.elim x y)
  have he : Sum.elim x y ∘ twistPorts k = Sum.elim x (shift k y) := by
    funext b
    cases b <;> rfl
  rw [he, TwoSidedBoundaryReindex.accepts_iff,
    TwoSidedBoundaryReindex.accepts_iff] at h
  exact h

/-- A directed boundary replacement, with the shared port word unchanged. -/
theorem twistedTube_reconstruct (n : ℕ) (x y : Fin k → Color)
    (h : (twistedTube k n).AcceptsBoundaryWords x y) :
    (tube k (n + 2)).Accepts x y := by
  let z : Fin k → Color := fun i => y (i - 1)
  have hz : shift k z = y := by funext i; simp [shift, z]
  rw [← hz] at h ⊢
  exact tube_insert_two k n ((twistedTube_accepts k n x z).mp h)

/-- A cyclic port shift preserves both oriented boundary-face cycles. -/
theorem twistedTube_returnCode (n : ℕ) :
    returnCode (asOpen (twistedTube k n)) = boundaryPerm k := by
  rw [returnCode_asOpen, twistedTube, TwoSidedBoundaryJoint.face_reindex,
    tube_face_code]
  ext b
  rcases b with i | i <;>
    simp [twistPorts, boundaryPerm, boundaryNext, Equiv.addRight, sub_eq_add_neg]

theorem twistedTube_mass (n : ℕ) :
    eulerMass (asOpen (twistedTube k n)) = eulerMass (asOpen (tube k n).data) :=
  TwoSidedBoundaryJoint.mass_reindex _ _

section Context
variable {V I B : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B]
  (outside : OpenTangleData V I B) (m : B ≃ Fin k ⊕ Fin k)

/-- Arbitrary exteriors, including disconnected ones, retain the map class. -/
theorem twistedTube_class (hk : 2 ≤ k) (n : ℕ)
    (h : BridgelessSphericalCubicMapData
      (outside.composeRotationSystem (asOpen (tube k (n + 2)).data) m)) :
    BridgelessSphericalCubicMapData
      (outside.composeRotationSystem (asOpen (twistedTube k n)) m) := by
  have structural := OpenTangleInternalReplacement.replacement_structural outside
    (asOpen (tube k (n + 2)).data) (asOpen (twistedTube k n)) m m
    (tube_connected_bridgeless k hk (n + 2))
    (by simpa only [twistedTube, TwoSidedBoundaryJoint.side_reindex] using
      tube_connected_bridgeless k hk n)
  have heuler : compositeEuler outside (asOpen (tube k (n + 2)).data) m =
      compositeEuler outside (asOpen (twistedTube k n)) m := by
    apply (euler_eq_iff_mass _ _
      ((tube_returnCode k (n + 2)).trans (twistedTube_returnCode k n).symm)
      outside m).mpr
    rw [twistedTube_mass]
    exact (tube_eulerMass k (n + 2)).trans (tube_eulerMass k n).symm
  exact {
    spherical := {
      cubic := isCubic_composeRotationSystem outside (asOpen (twistedTube k n)) m
        (exterior_isCubic outside _ m h.spherical.cubic)
        (cubic_reindex _ _ (tube_isCubic k n))
      euler := by
        change compositeEuler outside (asOpen (twistedTube k n)) m = 2
        rw [← heuler]
        exact h.spherical.euler }
    primalConnected := (structural.mp ⟨h.primalConnected, h.edgeBridgeFree⟩).1
    vertexRotationCyclic := vertexRotationCyclic_composeRotationSystem outside
      (asOpen (twistedTube k n)) m
      (exterior_rotationCyclic outside _ m h.vertexRotationCyclic)
      (rotationCyclic_reindex _ _ (tube_rotationCyclic k n))
    edgeBridgeFree := (structural.mp ⟨h.primalConnected, h.edgeBridgeFree⟩).2 }

/-- Reconstruct genuine edge colours while fixing every exterior edge. -/
theorem twistedTube_closed_reconstruct (n : ℕ)
    (c : (outside.composeRotationSystem (asOpen (twistedTube k n)) m).EdgeColoring Color)
    (hc : (outside.composeRotationSystem (asOpen (twistedTube k n)) m).IsTaitEdgeColoring c) :
    ∃ old : (outside.composeRotationSystem (asOpen (tube k (n + 2)).data) m).EdgeColoring Color,
      (outside.composeRotationSystem (asOpen (tube k (n + 2)).data) m).IsTaitEdgeColoring old ∧
      ∀ d, old ((outside.composeRotationSystem (asOpen (tube k (n + 2)).data) m).edgeOf
          (composeDartEquiv (.inl d))) =
        c ((outside.composeRotationSystem (asOpen (twistedTube k n)) m).edgeOf
          (composeDartEquiv (.inl d))) :=
  OpenTangleClosedWitness.replace outside (twistedTube k n) m (tube k (n + 2)).data
    (twistedTube_reconstruct k n) c hc

omit [DecidableEq V] in
/-- Exactly two rows are removed, with no new vertices outside the tube. -/
theorem twistedTube_vertex_loss (n : ℕ) :
    Fintype.card (V ⊕ (tube k (n + 2)).V) =
      Fintype.card (V ⊕ (tube k n).V) + 4 * k := by
  rw [Fintype.card_sum, Fintype.card_sum]
  simp only [← Nat.card_eq_fintype_card, tube_vertex_card]
  ring

/-- A uniform strict reduction at every width at least two. -/
theorem strict_twistedTube_reduction (hk : 2 ≤ k) (n : ℕ)
    (h : BridgelessSphericalCubicMapData
      (outside.composeRotationSystem (asOpen (tube k (n + 2)).data) m)) :
    Fintype.card (V ⊕ (tube k n).V) < Fintype.card (V ⊕ (tube k (n + 2)).V) ∧
      BridgelessSphericalCubicMapData
        (outside.composeRotationSystem (asOpen (twistedTube k n)) m) ∧
      (RotationSystemTaitColorable (outside.composeRotationSystem (asOpen (twistedTube k n)) m) →
        RotationSystemTaitColorable (outside.composeRotationSystem (asOpen (tube k (n + 2)).data) m)) := by
  refine ⟨?_, twistedTube_class k outside m hk n h, ?_⟩
  · have hv := twistedTube_vertex_loss k (V := V) n
    omega
  · rintro ⟨c, hc⟩
    obtain ⟨old, hold, _⟩ := twistedTube_closed_reconstruct k outside m n c hc
    exact ⟨old, hold⟩

end Context
end
end Mettapedia.GraphTheory.FourColor.ZigzagRing
