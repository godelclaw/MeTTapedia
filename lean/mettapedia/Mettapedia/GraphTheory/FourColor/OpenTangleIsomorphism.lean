import Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement
import Mettapedia.GraphTheory.FourColor.RotationSystemExactTransport
import Mettapedia.GraphTheory.FourColor.GoertzelV24VertexSideReassembly

/-!
# Exact open-tangle representation changes

An isomorphism retains vertices, internal edge pairs, boundary half-edges
and rotations. Its boundary map transports the computed face return, and
sewing commutes with the change of representation in every fixed exterior.
No equality of outer marks is required.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism

open GoertzelV24OpenTangleComposition GoertzelV24TwoEdgeCutMinimality
open OpenTangleMarkedFace OpenTanglePortReplacement SerialTangleFaceTransfer
open SerialTangleFaceCode GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24VertexSideReassembly
open GoertzelV24CompositeSeamMultigraph GoertzelV24CanonicalHubCyclicity

variable {V I B W J C : Type*}

/-- Exact local incidence and rotation data; no colouring premise. -/
structure Iso (P : OpenTangleData V I B) (Q : OpenTangleData W J C) where
  vertex : V ≃ W
  interior : I ≃ J
  boundary : B ≃ C
  alpha : ∀ i, interior (P.interiorAlpha i) = Q.interiorAlpha (interior i)
  vert : ∀ d, vertex (P.vertOf d) =
    Q.vertOf (Equiv.sumCongr interior boundary d)
  rotation : ∀ d, Equiv.sumCongr interior boundary (P.rho d) =
    Q.rho (Equiv.sumCongr interior boundary d)

namespace Iso
variable {P : OpenTangleData V I B} {Q : OpenTangleData W J C} (e : Iso P Q)

def darts : I ⊕ B ≃ J ⊕ C := Equiv.sumCongr e.interior e.boundary

def symm : Iso Q P where
  vertex := e.vertex.symm
  interior := e.interior.symm
  boundary := e.boundary.symm
  alpha i := by
    apply e.interior.injective
    simp only [Equiv.apply_symm_apply, e.alpha]
  vert d := by
    apply e.vertex.injective
    rw [Equiv.apply_symm_apply, e.vert]
    exact congrArg Q.vertOf (e.darts.apply_symm_apply d).symm
  rotation d := by
    apply e.darts.injective
    change e.darts (e.darts.symm (Q.rho d)) = e.darts (P.rho (e.darts.symm d))
    rw [Equiv.apply_symm_apply]
    simpa only [darts, Equiv.apply_symm_apply] using (e.rotation (e.darts.symm d)).symm

theorem phi (d : I ⊕ B) : e.darts (openPhi P d) = openPhi Q (e.darts d) := by
  change e.darts (P.rho _) = Q.rho _
  change Equiv.sumCongr e.interior e.boundary (P.rho _) = Q.rho _
  rw [e.rotation]
  apply congrArg Q.rho
  cases d with
  | inl i => exact congrArg Sum.inl (e.alpha i)
  | inr b => rfl

theorem phi_permCongr : e.darts.permCongr (openPhi P) = openPhi Q := by
  apply Equiv.ext
  intro d
  obtain ⟨d, rfl⟩ := e.darts.surjective d
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using e.phi d

theorem boundary_iff (d : I ⊕ B) : Boundary d ↔ Boundary (e.darts d) := by
  cases d <;> rfl

variable [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B]
  [Fintype J] [DecidableEq J] [Fintype C] [DecidableEq C]

/-- The exact port observation commutes with first return through the interior. -/
theorem returnCode : e.boundary.permCongr (OpenTanglePortReplacement.returnCode P) =
    OpenTanglePortReplacement.returnCode Q := by
  classical
  have h := nextHitPerm_permCongr e.darts (openPhi P) Boundary Boundary e.boundary_iff
  rw [e.phi_permCongr] at h
  let b := e.darts.subtypeEquiv e.boundary_iff
  have hb : (boundaryCoordinate I B).trans e.boundary =
      b.trans (boundaryCoordinate J C) := by
    apply Equiv.ext
    rintro ⟨i | p, hp⟩
    · exact hp.elim
    · rfl
  unfold OpenTanglePortReplacement.returnCode
  rw [h]
  have hh := congrArg (fun f => f.permCongr
    (GoertzelV24OrderedCutFaceReturnProfile.nextHitPerm (openPhi P) Boundary)) hb
  exact hh

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]

omit [Fintype J] [Fintype C] [DecidableEq C] [Fintype W] [DecidableEq W] in
theorem sideStep {v w : V} (h : (sideMultigraph P).Step v w) :
    (sideMultigraph Q).Step (e.vertex v) (e.vertex w) := by
  obtain ⟨i, hv, hw⟩ := exists_interiorDart_of_sideStep P h
  have hv' : Q.interiorVert (e.interior i) = e.vertex v :=
    (e.vert (.inl i)).symm.trans (congrArg e.vertex hv)
  have hw' : Q.interiorVert (Q.interiorAlpha (e.interior i)) = e.vertex w := by
    rw [← e.alpha]
    exact (e.vert (.inl (P.interiorAlpha i))).symm.trans (congrArg e.vertex hw)
  refine ⟨sideEdgeOf Q (e.interior i), not_false, ?_⟩
  simpa only [hv', hw'] using sideMultigraph_ends Q (e.interior i)

include e in
omit [Fintype J] [Fintype C] [DecidableEq C] [Fintype W] [DecidableEq W] in
theorem connected (h : (sideMultigraph P).Connected) : (sideMultigraph Q).Connected := by
  intro v w
  obtain ⟨v, rfl⟩ := e.vertex.surjective v
  obtain ⟨w, rfl⟩ := e.vertex.surjective w
  have hp := h v w
  induction hp with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail (e.sideStep hs)

variable {X K L : Type*}
  [Fintype X] [DecidableEq X] [Fintype K] [DecidableEq K]
  [Fintype L] [DecidableEq L]
  (outside : OpenTangleData X K L) (m : L ≃ B)

noncomputable def sewnDarts : (outside.composeRotationSystem P m).D ≃
    (outside.composeRotationSystem Q (m.trans e.boundary)).D :=
  Equiv.sumCongr (Equiv.sumCongr (Equiv.refl K) e.interior)
    (Equiv.sumCongr (Equiv.refl L) e.boundary)

theorem sewnDarts_reassoc (d : (K ⊕ L) ⊕ (I ⊕ B)) :
    e.sewnDarts outside m (composeDartEquiv d) =
      composeDartEquiv (Equiv.sumCongr (Equiv.refl _) e.darts d) := by
  rcases d with (k | l) | (i | b) <;> rfl

theorem sewn_alpha (d : (outside.composeRotationSystem P m).D) :
    e.sewnDarts outside m ((outside.composeRotationSystem P m).alpha d) =
      (outside.composeRotationSystem Q (m.trans e.boundary)).alpha
        (e.sewnDarts outside m d) := by
  rcases d with (k | i) | (l | b)
  · rfl
  · exact congrArg (Sum.inl ∘ Sum.inr) (e.alpha i)
  · rfl
  · change Sum.inr (Sum.inl (m.symm b)) =
      Sum.inr (Sum.inl (m.symm (e.boundary.symm (e.boundary b))))
    rw [Equiv.symm_apply_apply]

theorem sewn_vert (d : (outside.composeRotationSystem P m).D) :
    Equiv.sumCongr (Equiv.refl X) e.vertex ((outside.composeRotationSystem P m).vertOf d) =
      (outside.composeRotationSystem Q (m.trans e.boundary)).vertOf
        (e.sewnDarts outside m d) := by
  rcases d with (k | i) | (l | b)
  · rfl
  · exact congrArg Sum.inr (e.vert (.inl i))
  · rfl
  · exact congrArg Sum.inr (e.vert (.inr b))

theorem sewn_rotation (d : (outside.composeRotationSystem P m).D) :
    e.sewnDarts outside m ((outside.composeRotationSystem P m).rho d) =
      (outside.composeRotationSystem Q (m.trans e.boundary)).rho
        (e.sewnDarts outside m d) := by
  obtain ⟨x, rfl⟩ := composeDartEquiv.surjective d
  change e.sewnDarts outside m (composeDartEquiv ((Equiv.sumCongr outside.rho P.rho)
    (composeDartEquiv.symm (composeDartEquiv x)))) = composeDartEquiv
    ((Equiv.sumCongr outside.rho Q.rho)
      (composeDartEquiv.symm (e.sewnDarts outside m (composeDartEquiv x))))
  rw [Equiv.symm_apply_apply, sewnDarts_reassoc, sewnDarts_reassoc, Equiv.symm_apply_apply]
  cases x with
  | inl d => rfl
  | inr d => exact congrArg (composeDartEquiv ∘ Sum.inr) (e.rotation d)

/-- The representation change preserves the actual geometric class after sewing. -/
theorem sewn_class
    (h : BridgelessSphericalCubicMapData (outside.composeRotationSystem P m)) :
    BridgelessSphericalCubicMapData (outside.composeRotationSystem Q (m.trans e.boundary)) :=
  RotationSystemExactTransport.mapClass _ _ (e.sewnDarts outside m)
    (Equiv.sumCongr (Equiv.refl X) e.vertex) (e.sewn_alpha outside m)
    (e.sewn_vert outside m) (e.sewn_rotation outside m) h

theorem sewn_colorable_iff :
    RotationSystemTaitColorable (outside.composeRotationSystem P m) ↔
      RotationSystemTaitColorable (outside.composeRotationSystem Q (m.trans e.boundary)) :=
  rotationSystemTaitColorable_iff_of_dartEquiv _ _ (e.sewnDarts outside m)
    (Equiv.sumCongr (Equiv.refl X) e.vertex) (e.sewn_alpha outside m) (e.sewn_vert outside m)

end Iso
end Mettapedia.GraphTheory.FourColor.OpenTangleIsomorphism
