import Mettapedia.GraphTheory.FourColor.StructuralCutRLink
import Mettapedia.GraphTheory.Hypermap.Patch

/-!
# The rewired disk for an open-tangle boundary ring

The ordinary capped shore pairs each boundary dart with a hub dart, so its
edge permutation is an involution. Gonthier's `snip_disk` uses a different
presentation: it retains the interior edge pairing and makes the boundary
ring itself one edge orbit. This module constructs that hypermap directly
from the route's `OpenTangleData` and a permutation of its boundary ports.

The construction supplies the *edge-orbit* field of `Hypermap.Patch`; it does
not by itself supply the disk's face-simplicity, the complementary snipped
remainder, or their embedding laws. Those are separate mathematical duties.
-/

namespace Mettapedia.GraphTheory.FourColor.StructuralCutSnipDisk

open Equiv Equiv.Perm Mettapedia.GraphTheory
open GoertzelV24OpenTangleComposition
open GoertzelV24OrbitCountCongr
open GoertzelV24SeamExchange

variable {V I B : Type*} [Fintype I] [DecidableEq I]
  [Fintype B] [DecidableEq B]

/-- Unlike the ordinary cap, the boundary ports are paired around the ring,
not with new hub darts. Interior edges are unchanged. -/
def snipEdge (T : OpenTangleData V I B) (σ : Perm B) : Perm (I ⊕ B) :=
  Equiv.sumCongr T.interiorAlpha σ

/-- The hypermap on the snipped disk. Its face permutation is forced by the
three-permutation law once the node and edge permutations are chosen. -/
def snipDisk (T : OpenTangleData V I B) (σ : Perm B) : Hypermap (I ⊕ B) where
  edge := snipEdge T σ
  node := T.rho⁻¹
  face := T.rho * (snipEdge T σ)⁻¹
  cancel3 := by
    intro d
    simp [snipEdge, Perm.mul_apply]

@[simp] theorem snipDisk_edge (T : OpenTangleData V I B) (σ : Perm B) :
    (snipDisk T σ).edge = snipEdge T σ := rfl

@[simp] theorem snipDisk_node (T : OpenTangleData V I B) (σ : Perm B) :
    (snipDisk T σ).node = T.rho⁻¹ := rfl

@[simp] theorem snipDisk_face (T : OpenTangleData V I B) (σ : Perm B) :
    (snipDisk T σ).face = T.rho * (snipEdge T σ)⁻¹ := rfl

/-- The border consists of the real boundary darts, not the hub copies of an
ordinary cap. -/
def border : Set (I ⊕ B) := Set.range Sum.inr

omit [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] in
@[simp] theorem inr_mem_border (b : B) : (Sum.inr b : I ⊕ B) ∈ border :=
  ⟨b, rfl⟩

omit [Fintype I] [DecidableEq I] [Fintype B] [DecidableEq B] in
@[simp] theorem inl_not_mem_border (i : I) : (Sum.inl i : I ⊕ B) ∉ border := by
  rintro ⟨b, h⟩
  cases h

/-- A fixed-point-free one-cycle boundary permutation makes the border one
edge orbit of the disk, exactly the `Patch.edgeCycle_d` obligation. -/
theorem edgeCycle_border (T : OpenTangleData V I B) (σ : Perm B)
    (hcycle : σ.IsCycle) (hfixfree : ∀ b : B, σ b ≠ b) :
    ∀ x y : I ⊕ B, x ∈ border →
      (((snipDisk T σ).edge).SameCycle x y ↔ y ∈ border) := by
  intro x y hx
  obtain ⟨b, rfl⟩ := hx
  rcases y with i | c
  · constructor
    · intro h
      exact (not_sameCycle_sumCongr_inl_inr T.interiorAlpha σ i b) h.symm |>.elim
    · intro h
      exact (inl_not_mem_border i h).elim
  · constructor
    · intro _
      exact inr_mem_border c
    · intro _
      change Equiv.Perm.SameCycle (Equiv.sumCongr T.interiorAlpha σ)
        (Sum.inr b) (Sum.inr c)
      exact (sameCycle_sumCongr_inr_iff T.interiorAlpha σ b c).2
        (hcycle.sameCycle (hfixfree b) (hfixfree c))

/-! ## Face walks compared with the ordinary capped shore -/

/-- On an interior dart, one snip-disk face step is one capped-shore face
step, viewed in the real-dart summand of the cap. -/
theorem face_interior (T : OpenTangleData V I B) (σ : Perm B) (i : I) :
    (Sum.inl ((snipDisk T σ).face (Sum.inl i)) : (I ⊕ B) ⊕ B) =
      hubPhi T σ⁻¹ (Sum.inl (Sum.inl i)) := by
  have hα : T.interiorAlpha.symm i = T.interiorAlpha i := by
    apply T.interiorAlpha.injective
    simpa using (T.interiorAlpha_involutive i).symm
  simpa [snipDisk, snipEdge, hubPhi, hubAlphaFun, Perm.mul_apply]
    using hα

/-- At a boundary dart the capped-shore face walk visits the hub once; the
snip-disk face step skips precisely that hub dart. -/
theorem face_boundary (T : OpenTangleData V I B) (σ : Perm B) (b : B) :
    (Sum.inl ((snipDisk T σ).face (Sum.inr b)) : (I ⊕ B) ⊕ B) =
      ((hubPhi T σ⁻¹) ^ 2) (Sum.inl (Sum.inr b)) := by
  simp [snipDisk, snipEdge, hubPhi, hubAlphaFun, Perm.mul_apply,
    pow_succ, pow_zero]

private theorem sameCycle_map_of_step {A C : Type*} [Fintype A]
    (π : Perm A) (τ : Perm C) (embed : A → C)
    (hstep : ∀ a, τ.SameCycle (embed a) (embed (π a)))
    {a b : A} (hab : π.SameCycle a b) :
    τ.SameCycle (embed a) (embed b) := by
  obtain ⟨n, rfl⟩ := hab.exists_nat_pow_eq
  clear hab
  induction n with
  | zero => simpa using SameCycle.refl τ (embed a)
  | succ n ih =>
      rw [pow_succ', Perm.mul_apply]
      exact ih.trans (hstep ((π ^ n) a))

/-- A snip-disk facial connection maps to a capped-shore facial connection.
The cap has an extra hub dart on each boundary step, but no new face orbit is
created by skipping it. -/
theorem face_sameCycle_to_hub (T : OpenTangleData V I B) (σ : Perm B)
    {x y : I ⊕ B}
    (hxy : ((snipDisk T σ).face).SameCycle x y) :
    (hubPhi T σ⁻¹).SameCycle (Sum.inl x) (Sum.inl y) := by
  apply sameCycle_map_of_step (snipDisk T σ).face (hubPhi T σ⁻¹)
    Sum.inl ?_ hxy
  intro d
  rcases d with i | b
  · rw [face_interior]
    exact ⟨1, by simp⟩
  · rw [face_boundary]
    let φ := hubPhi T σ⁻¹
    have h1 : φ.SameCycle (Sum.inl (Sum.inr b))
        (φ (Sum.inl (Sum.inr b))) := ⟨1, by simp⟩
    have h2 : φ.SameCycle (φ (Sum.inl (Sum.inr b)))
        (φ (φ (Sum.inl (Sum.inr b)))) := ⟨1, by simp⟩
    simpa [φ, pow_succ, Perm.mul_apply] using h1.trans h2

/-- The disk-border simplicity field of `Hypermap.Patch` follows from the
route's already-proved hub-face distinctness. This is a genuine orbit
transport: it is not asserted as a new hypothesis on the snipped disk. -/
theorem simple_border_of_hubFacesDistinct
    (T : OpenTangleData V I B) (σ : Perm B)
    (hfaces : HubFacesDistinct T σ⁻¹) :
    ∀ x ∈ border, ∀ y ∈ border,
      ((snipDisk T σ).face).SameCycle x y → x = y := by
  intro x hx y hy hxy
  obtain ⟨b, rfl⟩ := hx
  obtain ⟨c, rfl⟩ := hy
  have hreal := face_sameCycle_to_hub T σ hxy
  have hb : (hubPhi T σ⁻¹).SameCycle
      (Sum.inr (σ⁻¹ b)) (Sum.inl (Sum.inr b)) := by
    have hstep : hubPhi T σ⁻¹ (Sum.inl (Sum.inr b)) =
        Sum.inr (σ⁻¹ b) := by
      simp [hubPhi, hubAlphaFun, Perm.mul_apply]
    exact (show (hubPhi T σ⁻¹).SameCycle
      (Sum.inl (Sum.inr b)) (Sum.inr (σ⁻¹ b)) from
        ⟨1, by simpa using hstep⟩).symm
  have hc : (hubPhi T σ⁻¹).SameCycle
      (Sum.inl (Sum.inr c)) (Sum.inr (σ⁻¹ c)) := by
    have hstep : hubPhi T σ⁻¹ (Sum.inl (Sum.inr c)) =
        Sum.inr (σ⁻¹ c) := by
      simp [hubPhi, hubAlphaFun, Perm.mul_apply]
    exact ⟨1, by simpa using hstep⟩
  have heq : σ⁻¹ b = σ⁻¹ c := hfaces _ _ (hb.trans (hreal.trans hc))
  exact congrArg Sum.inr ((σ⁻¹).injective heq)

section OrderedBond

open SimpleGraphDartRotation
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24CanonicalHubClosure
open GoertzelV24ConnectedShoreLiteralNode
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24FaceOrbitIncidence
open GoertzelV24DeletedRegionRotationSplice
open SphericalContourSeparators
open StructuralCutRLink

variable {W : Type*} [Fintype W] [DecidableEq W]
  {G : SimpleGraph W} [DecidableRel G.Adj]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- An actual source-derived ordered bond supplies the one-edge-orbit border
of the snipped disk. This consumes both the generic rewiring and the physical
first-return ring; unlike a plain hub cap, it works for any number of ports.
The remaining fields of `Hypermap.Patch` are not claimed here. -/
theorem orderedContourBond_snipDisk_edgeCycle
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (root far : OrbitFace rotation.toRotationSystem)
    {lo hi width : ℕ}
    (bond : OrderedContourBond rotation root far lo hi width)
    (outer : RetainedDart rotation.toRotationSystem
      (deletedRegionKeep bond.deleted)) :
    ∀ x y : InternalDart rotation.toRotationSystem
          (deletedRegionKeep bond.deleted) ⊕
        BoundaryDart rotation.toRotationSystem
          (deletedRegionKeep bond.deleted),
      x ∈ border →
      (((snipDisk
        (OpenTangleData.ofVertexSide rotation.toRotationSystem
          (deletedRegionKeep bond.deleted) outer)
        (retainedRegionBoundarySuccessor rotation.toRotationSystem
          (deletedRegionKeep bond.deleted))).edge).SameCycle x y ↔
        y ∈ border) := by
  exact edgeCycle_border _ _
    (retainedSuccessor_isCycle_of_orderedContourBond rotation hclass htwo
      root far bond)
    (fun b => retainedSuccessor_ne_self rotation.toRotationSystem
      (deletedRegionKeep bond.deleted) htwo b)

/-- The same physical ordered bond also supplies the `Patch.simple_d` field.
The first-return cap theorem proves its hub faces distinct; skipping each hub
dart transports that fact to the snipped disk's actual face orbits. -/
theorem orderedContourBond_snipDisk_simple
    (rotation : Data G)
    (root far : OrbitFace rotation.toRotationSystem)
    {lo hi width : ℕ}
    (bond : OrderedContourBond rotation root far lo hi width)
    (outer : RetainedDart rotation.toRotationSystem
      (deletedRegionKeep bond.deleted)) :
    ∀ x ∈ border, ∀ y ∈ border,
      (((snipDisk
        (OpenTangleData.ofVertexSide rotation.toRotationSystem
          (deletedRegionKeep bond.deleted) outer)
        (retainedRegionBoundarySuccessor rotation.toRotationSystem
          (deletedRegionKeep bond.deleted))).face).SameCycle x y) → x = y := by
  apply simple_border_of_hubFacesDistinct
  simpa only [GoertzelV24VertexSideOpenTangle.canonicalHubRotation] using
    hubFacesDistinct_canonical rotation.toRotationSystem
      (deletedRegionKeep bond.deleted) outer

end OrderedBond

end Mettapedia.GraphTheory.FourColor.StructuralCutSnipDisk
