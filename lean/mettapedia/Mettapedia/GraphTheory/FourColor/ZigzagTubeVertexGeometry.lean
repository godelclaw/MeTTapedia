import Mettapedia.GraphTheory.FourColor.ZigzagRingGeometry
import Mettapedia.GraphTheory.FourColor.SerialTangleVertexGeometry

/-!
# Cubic vertex fibres and rotations of literal tubes

Each ring vertex has its displayed three darts, in one rotation cycle.
The literal serial constructor retains these fibres and cycles, proving
the same conditions for every nonempty tube at every positive width.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing

open GoertzelV24OpenTangleComposition
open GoertzelV24CompositeSeamCubic SerialTangleSmallCutTransfer
open SerialTangleVertexGeometry

noncomputable section
attribute [local instance] Classical.propDecidable

variable (k : Nat) [NeZero k]

theorem ring_dartsAt_inl (i : Fin k) :
    openDartsAt (openRing k) (.inl i) =
      { .inr (.inl i), .inl (.inl (i, false)), .inl (.inr (i - 1, true)) } := by
  ext d
  rcases d with (⟨j, _ | _⟩ | ⟨j, _ | _⟩) | (j | j) <;>
    simp [openDartsAt, openRing, asOpen_vertOf, vertOf_apply,
      twoSidedOpenTangleVertOf, interiorVert, eq_sub_iff_add_eq]

theorem ring_dartsAt_inr (i : Fin k) :
    openDartsAt (openRing k) (.inr i) =
      { .inl (.inl (i, true)), .inl (.inr (i, false)), .inr (.inr i) } := by
  ext d
  rcases d with (⟨j, _ | _⟩ | ⟨j, _ | _⟩) | (j | j) <;>
    simp [openDartsAt, openRing, asOpen_vertOf, vertOf_apply,
      twoSidedOpenTangleVertOf, interiorVert]

theorem ring_isCubic : OpenIsCubic (openRing k) := by
  rintro (i | i)
  · rw [ring_dartsAt_inl]; simp
  · rw [ring_dartsAt_inr]; simp

private theorem ring_sameCycle_port (d : AllDart k) :
    (rho k).SameCycle (.inr ((ring k).vertOf d)) d := by
  rcases d with (⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i)
  · exact (Equiv.Perm.SameCycle.refl (rho k) (.inr (.inl i))).apply_right
  · exact (Equiv.Perm.SameCycle.refl (rho k) (.inr (.inr i))).apply_right
  · exact (Equiv.Perm.SameCycle.refl (rho k) (.inr (.inr i))).apply_right.apply_right
  · simpa [rho, rhoFun, vertOf_apply, twoSidedOpenTangleVertOf, interiorVert] using
      (Equiv.Perm.SameCycle.refl (rho k) (.inr (.inl (i + 1)))).apply_right.apply_right
  · exact .rfl
  · exact .rfl

theorem ring_rotationCyclic : OpenRotationCyclic (openRing k) := by
  intro d d' hv
  change (rho k).SameCycle d d'
  have h := ring_sameCycle_port k d
  simp only [openRing, asOpen_vertOf] at hv
  rw [hv] at h
  exact h.symm.trans (ring_sameCycle_port k d')

attribute [local instance] tubeVertexFintype tubeInteriorFintype
  appendRingVertexFintype appendRingInteriorFintype

omit [NeZero k] in
private theorem hidden_vertex_geometry_congr (T U : HiddenTangle (Fin k) (Fin k))
    [Fintype T.I] [DecidableEq T.I] [DecidableEq T.V]
    [Fintype U.I] [DecidableEq U.I] [DecidableEq U.V] (h : T = U) :
    (OpenIsCubic (asOpen T.data) ∧ OpenRotationCyclic (asOpen T.data)) ↔
      (OpenIsCubic (asOpen U.data) ∧ OpenRotationCyclic (asOpen U.data)) := by
  subst U
  congr!

theorem tube_vertex_geometry (n : Nat) :
    OpenIsCubic (asOpen (tube k n).data) ∧ OpenRotationCyclic (asOpen (tube k n).data) := by
  induction n with
  | zero =>
    exact (hidden_vertex_geometry_congr k (tube k 0) ⟨Vtx k, Dart k, ring k⟩ rfl).mpr
      ⟨ring_isCubic k, ring_rotationCyclic k⟩
  | succ n ih =>
    apply (hidden_vertex_geometry_congr k _ _ (tube_succ k n)).mpr
    constructor
    · convert serial_isCubic (tube k n).data (ring k) ih.1 (ring_isCubic k) using 1 <;>
        congr!
    · exact serial_rotationCyclic (tube k n).data (ring k) ih.2 (ring_rotationCyclic k)

theorem tube_isCubic (n : Nat) : OpenIsCubic (asOpen (tube k n).data) :=
  (tube_vertex_geometry k n).1

theorem tube_rotationCyclic (n : Nat) : OpenRotationCyclic (asOpen (tube k n).data) :=
  (tube_vertex_geometry k n).2

end
end Mettapedia.GraphTheory.FourColor.ZigzagRing
