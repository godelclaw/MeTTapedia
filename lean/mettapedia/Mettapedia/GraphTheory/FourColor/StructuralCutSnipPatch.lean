import Mettapedia.GraphTheory.FourColor.StructuralCutSnipDisk
import Mettapedia.GraphTheory.FourColor.StructuralCutPatchObstruction
import Mettapedia.GraphTheory.FourColor.GoertzelV24ComplementaryShoreBoundaryOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24StellarDualStructure

/-!
# The physical embeddings for snipping an ordered vertex cut

The snipped disk consists of actual retained darts. Its complement is the
ordinary cap of the deleted shore: deleted real darts plus hub copies, where
each hub copy is embedded as the opposite retained boundary dart. This gives
the precise overlapping carriers required by `Hypermap.Patch`. We prove the
embedding and coverage laws directly on those physical carriers before using
any orbit-count identity.
-/

namespace Mettapedia.GraphTheory.FourColor.StructuralCutSnipPatch

open Equiv Equiv.Perm Mettapedia.GraphTheory
open GoertzelV24RotationCutDartDecomposition
open GoertzelV24DeletedRegionRotationSplice
open GoertzelV24ComplementaryShoreBoundaryOrder
open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24RetainedRegionBoundaryOrder
open GoertzelV24OrbitCountCongr
open GoertzelV24VertexSideOpenTangle
open StructuralCutSnipDisk
open StructuralCutPatchObstruction

variable {V E : Type*} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]

noncomputable section

/-- Actual retained darts, classified as intact or exposed. -/
abbrev DiskDarts (RS : RotationSystem V E) (deleted : Finset V) :=
  InternalDart RS (deletedRegionKeep deleted) ⊕
    BoundaryDart RS (deletedRegionKeep deleted)

/-- Deleted-side real darts plus hub copies of its exposed darts. The hub
copies map to the retained side of the original crossed edges. -/
abbrev RemDarts (RS : RotationSystem V E) (deleted : Finset V) :=
  (InternalDart RS (deletedSideKeep deleted) ⊕
    BoundaryDart RS (deletedSideKeep deleted)) ⊕
      BoundaryDart RS (deletedSideKeep deleted)

/-- The disk embedding is literal inclusion of retained darts. -/
def diskEmbed (RS : RotationSystem V E) (deleted : Finset V) :
    DiskDarts RS deleted → RS.D
  | .inl i => i.1.1
  | .inr b => b.1.1

/-- The remainder embedding is inclusion on deleted real darts and ambient
edge reversal on hub copies. -/
def remEmbed (RS : RotationSystem V E) (deleted : Finset V) :
    RemDarts RS deleted → RS.D
  | .inl (.inl i) => i.1.1
  | .inl (.inr b) => b.1.1
  | .inr b => RS.alpha b.1.1

theorem diskEmbed_eq_retained (RS : RotationSystem V E)
    (deleted : Finset V) (d : DiskDarts RS deleted) :
    diskEmbed RS deleted d =
      ((retainedDartEquivInternalSumBoundary RS
        (deletedRegionKeep deleted)).symm d).1 := by
  rcases d with i | b <;> rfl

theorem diskEmbed_injective (RS : RotationSystem V E)
    (deleted : Finset V) : Function.Injective (diskEmbed RS deleted) := by
  intro x y h
  rw [diskEmbed_eq_retained, diskEmbed_eq_retained] at h
  exact (retainedDartEquivInternalSumBoundary RS
    (deletedRegionKeep deleted)).symm.injective (Subtype.val_injective h)

theorem remEmbed_real_eq_deleted (RS : RotationSystem V E)
    (deleted : Finset V)
    (d : InternalDart RS (deletedSideKeep deleted) ⊕
      BoundaryDart RS (deletedSideKeep deleted)) :
    remEmbed RS deleted (Sum.inl d) =
      ((retainedDartEquivInternalSumBoundary RS
        (deletedSideKeep deleted)).symm d).1 := by
  rcases d with i | b <;> rfl

/-- Neither embedding identifies two different darts. In the remainder,
deleted real darts cannot collide with hub copies because their base vertices
lie on opposite sides of the cut. -/
theorem remEmbed_injective (RS : RotationSystem V E)
    (deleted : Finset V) : Function.Injective (remEmbed RS deleted) := by
  intro x y h
  rcases x with x | x
  · rcases y with y | y
    · apply congrArg Sum.inl
      rw [remEmbed_real_eq_deleted, remEmbed_real_eq_deleted] at h
      exact (retainedDartEquivInternalSumBoundary RS
        (deletedSideKeep deleted)).symm.injective (Subtype.val_injective h)
    · have hx : deletedSideKeep deleted
          (RS.vertOf (remEmbed RS deleted (Sum.inl x))) := by
        rw [remEmbed_real_eq_deleted]
        exact ((retainedDartEquivInternalSumBoundary RS
          (deletedSideKeep deleted)).symm x).2
      have hy : ¬ deletedSideKeep deleted
          (RS.vertOf (remEmbed RS deleted (Sum.inr y))) := y.2
      exact (hy (h ▸ hx)).elim
  · rcases y with y | y
    · have hx : ¬ deletedSideKeep deleted
          (RS.vertOf (remEmbed RS deleted (Sum.inr x))) := x.2
      have hy : deletedSideKeep deleted
          (RS.vertOf (remEmbed RS deleted (Sum.inl y))) := by
        rw [remEmbed_real_eq_deleted]
        exact ((retainedDartEquivInternalSumBoundary RS
          (deletedSideKeep deleted)).symm y).2
      exact (hx (h.symm ▸ hy)).elim
    · apply congrArg Sum.inr
      apply Subtype.ext
      apply Subtype.ext
      exact RS.alpha.injective h

/-! ## The actual overlap and coverage -/

def diskBorder (RS : RotationSystem V E) (deleted : Finset V) :
    Set (DiskDarts RS deleted) := Set.range Sum.inr

def remBorder (RS : RotationSystem V E) (deleted : Finset V) :
    Set (RemDarts RS deleted) := Set.range Sum.inr

theorem boundaryAlpha_symm_val (RS : RotationSystem V E)
    (deleted : Finset V)
    (b : BoundaryDart RS (deletedSideKeep deleted)) :
    ((complementBoundaryAlphaEquiv RS deleted).symm b).1.1 =
      RS.alpha b.1.1 := by
  let matching := complementBoundaryAlphaEquiv RS deleted
  have h := complementBoundaryAlphaEquiv_val RS deleted (matching.symm b)
  rw [matching.apply_symm_apply] at h
  calc
    (matching.symm b).1.1 = RS.alpha (RS.alpha (matching.symm b).1.1) :=
      (RS.alpha_involutive _).symm
    _ = RS.alpha b.1.1 := congrArg RS.alpha h.symm

theorem ring_images_equal (RS : RotationSystem V E)
    (deleted : Finset V) :
    remEmbed RS deleted '' remBorder RS deleted =
      diskEmbed RS deleted '' diskBorder RS deleted := by
  ext x
  constructor
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    let matching := complementBoundaryAlphaEquiv RS deleted
    refine ⟨Sum.inr (matching.symm b), ⟨matching.symm b, rfl⟩, ?_⟩
    exact boundaryAlpha_symm_val RS deleted b
  · rintro ⟨_, ⟨b, rfl⟩, rfl⟩
    let matching := complementBoundaryAlphaEquiv RS deleted
    refine ⟨Sum.inr (matching b), ⟨matching b, rfl⟩, ?_⟩
    change RS.alpha (matching b).1.1 = b.1.1
    rw [complementBoundaryAlphaEquiv_val]
    exact RS.alpha_involutive _

theorem mem_range_diskEmbed_iff (RS : RotationSystem V E)
    (deleted : Finset V) (x : RS.D) :
    x ∈ Set.range (diskEmbed RS deleted) ↔
      deletedRegionKeep deleted (RS.vertOf x) := by
  constructor
  · rintro ⟨d, rfl⟩
    rw [diskEmbed_eq_retained]
    exact ((retainedDartEquivInternalSumBoundary RS
      (deletedRegionKeep deleted)).symm d).2
  · intro hx
    let d : RetainedDart RS (deletedRegionKeep deleted) := ⟨x, hx⟩
    refine ⟨retainedDartEquivInternalSumBoundary RS
      (deletedRegionKeep deleted) d, ?_⟩
    rw [diskEmbed_eq_retained]
    simp [d]

/-- The two images cover every ambient dart and intersect exactly at the
actual cut ports. This is the `Patch.cover` law on the physical vertex cut. -/
theorem cover (RS : RotationSystem V E) (deleted : Finset V) (x : RS.D) :
    x ∈ Set.range (remEmbed RS deleted) ↔
      (x ∉ Set.range (diskEmbed RS deleted) ∨
        x ∈ diskEmbed RS deleted '' diskBorder RS deleted) := by
  constructor
  · rintro ⟨d, rfl⟩
    rcases d with d | b
    · left
      rw [mem_range_diskEmbed_iff, remEmbed_real_eq_deleted]
      exact ((retainedDartEquivInternalSumBoundary RS
        (deletedSideKeep deleted)).symm d).2
    · right
      rw [← ring_images_equal RS deleted]
      exact ⟨Sum.inr b, ⟨b, rfl⟩, rfl⟩
  · rintro (h | h)
    · have hx : deletedSideKeep deleted (RS.vertOf x) := by
        change ¬ deletedRegionKeep deleted (RS.vertOf x)
        exact mt ((mem_range_diskEmbed_iff RS deleted x).2) h
      let d : RetainedDart RS (deletedSideKeep deleted) := ⟨x, hx⟩
      refine ⟨Sum.inl
        (retainedDartEquivInternalSumBoundary RS
          (deletedSideKeep deleted) d), ?_⟩
      rw [remEmbed_real_eq_deleted]
      simp [d]
    · rw [← ring_images_equal RS deleted] at h
      obtain ⟨d, _, rfl⟩ := h
      exact ⟨d, rfl⟩

/-- Equality of the two physical embeddings forces both arguments onto their
respective border summands. -/
theorem common_images_border (RS : RotationSystem V E)
    (deleted : Finset V) {xd : DiskDarts RS deleted}
    {xr : RemDarts RS deleted}
    (h : diskEmbed RS deleted xd = remEmbed RS deleted xr) :
    xd ∈ diskBorder RS deleted ∧ xr ∈ remBorder RS deleted := by
  have hrange : diskEmbed RS deleted xd ∈
      Set.range (remEmbed RS deleted) := ⟨xr, h.symm⟩
  have hcov := (cover RS deleted (diskEmbed RS deleted xd)).1 hrange
  have hbd : xd ∈ diskBorder RS deleted := by
    rcases hcov with hnot | himage
    · exact (hnot ⟨xd, rfl⟩).elim
    · obtain ⟨yd, hyd, heq⟩ := himage
      have hsame : yd = xd := diskEmbed_injective RS deleted heq
      exact hsame ▸ hyd
  refine ⟨hbd, ?_⟩
  have himage : remEmbed RS deleted xr ∈
      remEmbed RS deleted '' remBorder RS deleted := by
    rw [ring_images_equal RS deleted]
    exact ⟨xd, hbd, h⟩
  obtain ⟨yr, hyr, heq⟩ := himage
  have hsame : yr = xr := remEmbed_injective RS deleted heq
  exact hsame ▸ hyr

/-- On the border, equality of embeddings means exactly that the deleted
port is the ambient-alpha partner of the retained port. -/
theorem boundary_embed_eq_iff (RS : RotationSystem V E)
    (deleted : Finset V)
    (b : BoundaryDart RS (deletedRegionKeep deleted))
    (c : BoundaryDart RS (deletedSideKeep deleted)) :
    diskEmbed RS deleted (Sum.inr b) =
        remEmbed RS deleted (Sum.inr c) ↔
      complementBoundaryAlphaEquiv RS deleted b = c := by
  constructor
  · intro h
    have hb : b = (complementBoundaryAlphaEquiv RS deleted).symm c := by
      apply Subtype.ext
      apply Subtype.ext
      exact h.trans (boundaryAlpha_symm_val RS deleted c).symm
    simp [hb]
  · intro h
    change b.1.1 = RS.alpha c.1.1
    rw [← h, complementBoundaryAlphaEquiv_val]
    exact (RS.alpha_involutive _).symm

/-! ## The three hypermaps on the physical cut -/

def diskTangle (RS : RotationSystem V E) (deleted : Finset V)
    (outer : RetainedDart RS (deletedRegionKeep deleted)) :=
  OpenTangleData.ofVertexSide RS (deletedRegionKeep deleted) outer

def remTangle (RS : RotationSystem V E) (deleted : Finset V)
    (outer : RetainedDart RS (deletedSideKeep deleted)) :=
  OpenTangleData.ofVertexSide RS (deletedSideKeep deleted) outer

def diskMap (RS : RotationSystem V E) (deleted : Finset V)
    (outer : RetainedDart RS (deletedRegionKeep deleted)) :
    Hypermap (DiskDarts RS deleted) :=
  snipDisk (diskTangle RS deleted outer)
    (retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted))

def remMap (RS : RotationSystem V E) (deleted : Finset V)
    (outer : RetainedDart RS (deletedSideKeep deleted)) :
    Hypermap (RemDarts RS deleted) :=
  hubHypermap (remTangle RS deleted outer)
    (canonicalHubRotation RS (deletedSideKeep deleted))

theorem diskEmbed_rho (RS : RotationSystem V E) (deleted : Finset V)
    (outer : RetainedDart RS (deletedRegionKeep deleted))
    (d : DiskDarts RS deleted) :
    diskEmbed RS deleted ((diskTangle RS deleted outer).rho d) =
      RS.rho (diskEmbed RS deleted d) := by
  have h := ofVertexSide_rho_underlying RS
    (deletedRegionKeep deleted) outer d
  rw [diskEmbed_eq_retained, diskEmbed_eq_retained]
  simpa only [diskTangle, retainedRho_val] using congrArg Subtype.val h

theorem diskEmbed_node (RS : RotationSystem V E) (deleted : Finset V)
    (outer : RetainedDart RS (deletedRegionKeep deleted))
    (d : DiskDarts RS deleted) :
    diskEmbed RS deleted ((diskMap RS deleted outer).node d) =
      (Hypermap.ofRotationSystem RS).node (diskEmbed RS deleted d) := by
  change diskEmbed RS deleted
      ((diskTangle RS deleted outer).rho.symm d) =
      RS.rho.symm (diskEmbed RS deleted d)
  apply RS.rho.injective
  simpa using diskEmbed_rho RS deleted outer
    ((diskTangle RS deleted outer).rho.symm d) |>.symm

theorem diskEmbed_edge_off_border
    (RS : RotationSystem V E) (deleted : Finset V)
    (outer : RetainedDart RS (deletedRegionKeep deleted))
    (d : DiskDarts RS deleted) (hd : d ∉ diskBorder RS deleted) :
    diskEmbed RS deleted ((diskMap RS deleted outer).edge d) =
      (Hypermap.ofRotationSystem RS).edge (diskEmbed RS deleted d) := by
  rcases d with i | b
  · change (internalAlpha RS (deletedRegionKeep deleted) i).1.1 =
      RS.alpha i.1.1
    rfl
  · exact (hd ⟨b, rfl⟩).elim

theorem remEmbed_rho_real (RS : RotationSystem V E) (deleted : Finset V)
    (outer : RetainedDart RS (deletedSideKeep deleted))
    (d : InternalDart RS (deletedSideKeep deleted) ⊕
      BoundaryDart RS (deletedSideKeep deleted)) :
    remEmbed RS deleted (Sum.inl ((remTangle RS deleted outer).rho d)) =
      RS.rho (remEmbed RS deleted (Sum.inl d)) := by
  have h := ofVertexSide_rho_underlying RS
    (deletedSideKeep deleted) outer d
  rw [remEmbed_real_eq_deleted, remEmbed_real_eq_deleted]
  simpa only [remTangle, retainedRho_val] using congrArg Subtype.val h

theorem remEmbed_node_off_border (RS : RotationSystem V E)
    (deleted : Finset V)
    (outer : RetainedDart RS (deletedSideKeep deleted))
    (d : RemDarts RS deleted) (hd : d ∉ remBorder RS deleted) :
    remEmbed RS deleted ((remMap RS deleted outer).node d) =
      (Hypermap.ofRotationSystem RS).node (remEmbed RS deleted d) := by
  rcases d with d | b
  · change remEmbed RS deleted
        (Sum.inl ((remTangle RS deleted outer).rho.symm d)) =
        RS.rho.symm (remEmbed RS deleted (Sum.inl d))
    apply RS.rho.injective
    simpa using remEmbed_rho_real RS deleted outer
      ((remTangle RS deleted outer).rho.symm d) |>.symm
  · exact (hd ⟨b, rfl⟩).elim

theorem remEmbed_edge (RS : RotationSystem V E) (deleted : Finset V)
    (outer : RetainedDart RS (deletedSideKeep deleted))
    (d : RemDarts RS deleted) :
    remEmbed RS deleted ((remMap RS deleted outer).edge d) =
      (Hypermap.ofRotationSystem RS).edge (remEmbed RS deleted d) := by
  rcases d with (i | b) | b
  · change (internalAlpha RS (deletedSideKeep deleted) i).1.1 =
      RS.alpha i.1.1
    rfl
  · rfl
  · change b.1.1 = RS.alpha (RS.alpha b.1.1)
    exact (RS.alpha_involutive _).symm

/-- If the deleted shore's canonical hub order is one nontrivial cycle, its
hub copies are exactly one node orbit of the remainder. This is the dual
border-orbit field required by `Hypermap.Patch`. -/
theorem remNodeCycle (RS : RotationSystem V E) (deleted : Finset V)
    (outer : RetainedDart RS (deletedSideKeep deleted))
    (hcycle : (canonicalHubRotation RS (deletedSideKeep deleted)).IsCycle)
    (hfixfree : ∀ b : BoundaryDart RS (deletedSideKeep deleted),
      canonicalHubRotation RS (deletedSideKeep deleted) b ≠ b) :
    ∀ x y : RemDarts RS deleted, x ∈ remBorder RS deleted →
      (((remMap RS deleted outer).node).SameCycle x y ↔
        y ∈ remBorder RS deleted) := by
  intro x y hx
  obtain ⟨b, rfl⟩ := hx
  rcases y with d | c
  · constructor
    · intro h
      have h' : Equiv.Perm.SameCycle
          (Equiv.sumCongr (remTangle RS deleted outer).rho
            (canonicalHubRotation RS (deletedSideKeep deleted)))
          (Sum.inr b) (Sum.inl d) := (sameCycle_inv).1 h
      exact (not_sameCycle_sumCongr_inl_inr _ _ d b) h'.symm |>.elim
    · intro h
      exact (show (Sum.inl d : RemDarts RS deleted) ∉ remBorder RS deleted from
        by rintro ⟨c, hc⟩; cases hc) h |>.elim
  · constructor
    · intro _
      exact ⟨c, rfl⟩
    · intro _
      have h' : Equiv.Perm.SameCycle
          (Equiv.sumCongr (remTangle RS deleted outer).rho
            (canonicalHubRotation RS (deletedSideKeep deleted)))
          (Sum.inr b) (Sum.inr c) :=
        (sameCycle_sumCongr_inr_iff _ _ b c).2
          (hcycle.sameCycle (hfixfree b) (hfixfree c))
      exact (sameCycle_inv).2 h'

theorem diskEdge_mem_border_iff (RS : RotationSystem V E)
    (deleted : Finset V)
    (outer : RetainedDart RS (deletedRegionKeep deleted))
    (d : DiskDarts RS deleted) :
    (diskMap RS deleted outer).edge d ∈ diskBorder RS deleted ↔
      d ∈ diskBorder RS deleted := by
  rcases d with i | b
  · simp [diskMap, snipDisk, snipEdge, diskBorder]
  · simp [diskMap, snipDisk, snipEdge, diskBorder]

theorem remNode_mem_border_iff (RS : RotationSystem V E)
    (deleted : Finset V)
    (outer : RetainedDart RS (deletedSideKeep deleted))
    (d : RemDarts RS deleted) :
    (remMap RS deleted outer).node d ∈ remBorder RS deleted ↔
      d ∈ remBorder RS deleted := by
  rcases d with d | b
  · simp [remMap, hubHypermap, remBorder]
  · simp [remMap, hubHypermap, remBorder]

/-- The disk edge order and remainder node order run in opposite directions
under the physical boundary matching. This is exactly `Patch.ring_rev` for
the two constructed maps. -/
theorem ring_reverse (RS : RotationSystem V E) (deleted : Finset V)
    (outerD : RetainedDart RS (deletedRegionKeep deleted))
    (outerR : RetainedDart RS (deletedSideKeep deleted))
    (horder : canonicalHubRotation RS (deletedSideKeep deleted) =
      (complementBoundaryAlphaEquiv RS deleted).permCongr
        (retainedRegionBoundarySuccessor RS
          (deletedRegionKeep deleted))) :
    ∀ xd : DiskDarts RS deleted, ∀ xr : RemDarts RS deleted,
      diskEmbed RS deleted ((diskMap RS deleted outerD).edge xd) =
        remEmbed RS deleted xr ↔
      diskEmbed RS deleted xd =
        remEmbed RS deleted ((remMap RS deleted outerR).node xr) := by
  let matching := complementBoundaryAlphaEquiv RS deleted
  let σ := retainedRegionBoundarySuccessor RS (deletedRegionKeep deleted)
  let ρ := canonicalHubRotation RS (deletedSideKeep deleted)
  have hρ (b : BoundaryDart RS (deletedRegionKeep deleted)) :
      ρ (matching b) = matching (σ b) := by
    change canonicalHubRotation RS (deletedSideKeep deleted)
      (matching b) = matching (σ b)
    rw [horder]
    simp [matching, σ, Equiv.permCongr_apply]
  intro xd xr
  constructor
  · intro h
    have hpair := common_images_border RS deleted h
    have hxd : xd ∈ diskBorder RS deleted :=
      (diskEdge_mem_border_iff RS deleted outerD xd).1 hpair.1
    obtain ⟨b, rfl⟩ := hxd
    obtain ⟨c, rfl⟩ := hpair.2
    have hbc : matching (σ b) = c := by
      apply (boundary_embed_eq_iff RS deleted (σ b) c).1
      exact h
    have hbc' : matching b = ρ.symm c := by
      apply ρ.injective
      simpa [hρ b] using hbc
    apply (boundary_embed_eq_iff RS deleted b (ρ.symm c)).2
    exact hbc'
  · intro h
    have hpair := common_images_border RS deleted h
    obtain ⟨b, rfl⟩ := hpair.1
    have hxr : xr ∈ remBorder RS deleted :=
      (remNode_mem_border_iff RS deleted outerR xr).1 hpair.2
    obtain ⟨c, rfl⟩ := hxr
    have hbc : matching b = ρ.symm c := by
      apply (boundary_embed_eq_iff RS deleted b (ρ.symm c)).1
      exact h
    have hbc' : matching (σ b) = c := by
      rw [← hρ]
      exact (congrArg ρ hbc).trans (ρ.apply_symm_apply c)
    apply (boundary_embed_eq_iff RS deleted (σ b) c).2
    exact hbc'

section OrderedBond

open SimpleGraphDartRotation
open SphericalContourSeparators
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24FaceOrbitIncidence
open GoertzelV24SimpleGraphFaceDualConnectedness
open GoertzelV24CanonicalHubCyclicity
open GoertzelV24OrbitFaceCurvatureBulk
open GoertzelV24FaceDualConnectedness
open GoertzelV24PermutationOrbitSurgery
open StructuralCutRLink
open GoertzelV24CyclicBondBoundary.CyclicBondBoundaryData

variable {G : SimpleGraph V} [DecidableRel G.Adj]

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

/-- The deleted shore's hub order is the retained first-return order,
transported across the ambient edge involution. This is the orientation
identity the existing planar-bond theorem proves, not a separately chosen
border order. -/
theorem deletedHub_eq_conjugate_retainedSuccessor
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (root far : OrbitFace rotation.toRotationSystem)
    {lo hi width : ℕ}
    (bond : OrderedContourBond rotation root far lo hi width) :
    canonicalHubRotation rotation.toRotationSystem
        (deletedSideKeep bond.deleted) =
      (complementBoundaryAlphaEquiv rotation.toRotationSystem bond.deleted).permCongr
        (retainedRegionBoundarySuccessor rotation.toRotationSystem
          (deletedRegionKeep bond.deleted)) := by
  let RS := rotation.toRotationSystem
  let matching := complementBoundaryAlphaEquiv RS bond.deleted
  have hG : G.Connected := by
    simpa only [RS, rotationPrimalGraph_toRotationSystem_eq]
      using hclass.primalConnected
  have hrev := orientationReversing_canonicalHubRotation_of_planarBond
    rotation bond.deleted hclass.spherical htwo hG
      hclass.vertexRotationCyclic bond.connected bond.complement_connected
  ext c
  let b := matching.symm c
  have hc : c = matching b := by simp [b]
  rw [hc]
  have h := hrev b
  change (canonicalHubRotation RS (deletedSideKeep bond.deleted))
      (matching b) =
        matching ((canonicalHubRotation RS
          (deletedRegionKeep bond.deleted)).symm b) at h
  have hroot : (canonicalHubRotation RS
      (deletedRegionKeep bond.deleted)).symm =
      retainedRegionBoundarySuccessor RS
        (deletedRegionKeep bond.deleted) := by
    simp only [canonicalHubRotation]
    exact inv_inv _
  rw [hroot] at h
  simpa [RS, matching, Equiv.permCongr_apply,
    canonicalHubRotation] using h

/-- For the actual connected planar bond, the complementary cap has exactly
one node-orbit border. No independent cycle hypothesis is added to Patch. -/
theorem orderedContourBond_remNodeCycle
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (root far : OrbitFace rotation.toRotationSystem)
    {lo hi width : ℕ}
    (bond : OrderedContourBond rotation root far lo hi width)
    (outer : RetainedDart rotation.toRotationSystem
      (deletedSideKeep bond.deleted)) :
    ∀ x y : RemDarts rotation.toRotationSystem bond.deleted,
      x ∈ remBorder rotation.toRotationSystem bond.deleted →
      (((remMap rotation.toRotationSystem bond.deleted outer).node).SameCycle
        x y ↔ y ∈ remBorder rotation.toRotationSystem bond.deleted) := by
  let RS := rotation.toRotationSystem
  let matching := complementBoundaryAlphaEquiv RS bond.deleted
  let σ := retainedRegionBoundarySuccessor RS
    (deletedRegionKeep bond.deleted)
  have hσ : σ.IsCycle :=
    retainedSuccessor_isCycle_of_orderedContourBond rotation hclass htwo
      root far bond
  have heq : canonicalHubRotation RS (deletedSideKeep bond.deleted) =
      matching.permCongr σ :=
    deletedHub_eq_conjugate_retainedSuccessor rotation hclass htwo
      root far bond
  have hcycle : (canonicalHubRotation RS
      (deletedSideKeep bond.deleted)).IsCycle := by
    rw [heq]
    exact isCycle_permCongr matching σ hσ
  have hfixfree : ∀ b : BoundaryDart RS (deletedSideKeep bond.deleted),
      canonicalHubRotation RS (deletedSideKeep bond.deleted) b ≠ b := by
    intro b hb
    have hnot := retainedSuccessor_ne_self RS
      (deletedSideKeep bond.deleted) htwo b
    apply hnot
    change (retainedRegionBoundarySuccessor RS
      (deletedSideKeep bond.deleted))⁻¹ b = b at hb
    have h := congrArg (retainedRegionBoundarySuccessor RS
      (deletedSideKeep bond.deleted)) hb
    simpa using h.symm
  exact remNodeCycle RS bond.deleted outer hcycle hfixfree

/-- The actual ordered bond, cut at its physical darts and closed by the two
first-return border orders, is a patch of the ambient hypermap. No orbit-count
or genus identity is assumed in constructing the patch. -/
theorem orderedContourBond_patch
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (root far : OrbitFace rotation.toRotationSystem)
    {lo hi width : ℕ}
    (bond : OrderedContourBond rotation root far lo hi width)
    (outerD : RetainedDart rotation.toRotationSystem
      (deletedRegionKeep bond.deleted))
    (outerR : RetainedDart rotation.toRotationSystem
      (deletedSideKeep bond.deleted)) :
    Hypermap.Patch
      (Hypermap.ofRotationSystem rotation.toRotationSystem)
      (diskMap rotation.toRotationSystem bond.deleted outerD)
      (remMap rotation.toRotationSystem bond.deleted outerR)
      (diskEmbed rotation.toRotationSystem bond.deleted)
      (remEmbed rotation.toRotationSystem bond.deleted)
      (diskBorder rotation.toRotationSystem bond.deleted)
      (remBorder rotation.toRotationSystem bond.deleted) := by
  let RS := rotation.toRotationSystem
  let deleted := bond.deleted
  refine {
    injd := diskEmbed_injective RS deleted
    injr := remEmbed_injective RS deleted
    edgeCycle_d := ?_
    nodeCycle_r := ?_
    simple_d := ?_
    cover := cover RS deleted
    ring_eq := ring_images_equal RS deleted
    ring_rev := ring_reverse RS deleted outerD outerR
      (deletedHub_eq_conjugate_retainedSuccessor rotation hclass htwo root far bond)
    edge_d := diskEmbed_edge_off_border RS deleted outerD
    node_d := diskEmbed_node RS deleted outerD
    edge_r := remEmbed_edge RS deleted outerR
    node_r := remEmbed_node_off_border RS deleted outerR
  }
  · exact orderedContourBond_snipDisk_edgeCycle rotation hclass htwo
      root far bond outerD
  · exact orderedContourBond_remNodeCycle rotation hclass htwo
      root far bond outerR
  · exact orderedContourBond_snipDisk_simple rotation root far bond outerD

/-- The Coq-derived patch genus law now applies to a cut supplied by the
route, rather than only to an abstract patch or a laboratory instance. -/
theorem orderedContourBond_genus_add
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (root far : OrbitFace rotation.toRotationSystem)
    {lo hi width : ℕ}
    (bond : OrderedContourBond rotation root far lo hi width)
    (outerD : RetainedDart rotation.toRotationSystem
      (deletedRegionKeep bond.deleted))
    (outerR : RetainedDart rotation.toRotationSystem
      (deletedSideKeep bond.deleted)) :
    Hypermap.genus (Hypermap.ofRotationSystem rotation.toRotationSystem) =
      Hypermap.genus (diskMap rotation.toRotationSystem bond.deleted outerD) +
        Hypermap.genus (remMap rotation.toRotationSystem bond.deleted outerR) := by
  exact (orderedContourBond_patch rotation hclass htwo root far bond outerD outerR).genus_patch

/-- Planarity of the ambient map is equivalent to planarity of both physical
pieces of an ordered contour bond. -/
theorem orderedContourBond_planar_iff
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (root far : OrbitFace rotation.toRotationSystem)
    {lo hi width : ℕ}
    (bond : OrderedContourBond rotation root far lo hi width)
    (outerD : RetainedDart rotation.toRotationSystem
      (deletedRegionKeep bond.deleted))
    (outerR : RetainedDart rotation.toRotationSystem
      (deletedSideKeep bond.deleted)) :
    Hypermap.Planar (Hypermap.ofRotationSystem rotation.toRotationSystem) ↔
      Hypermap.Planar (diskMap rotation.toRotationSystem bond.deleted outerD) ∧
        Hypermap.Planar (remMap rotation.toRotationSystem bond.deleted outerR) := by
  exact (orderedContourBond_patch rotation hclass htwo root far bond outerD outerR).planar_patch

/-- Euler's sphere equation on a connected rotation presentation is exactly
planarity of its associated hypermap. This makes the patch planarity law
applicable to the route's existing spherical-map hypothesis. -/
theorem hypermap_planar_of_spherical
    (RS : RotationSystem V E)
    (hsphere : OrbitSphericalCubicMapData RS)
    (hconnected : (rotationPrimalGraph RS).Connected)
    (hrotation : VertexRotationCyclic RS) :
    Hypermap.Planar (Hypermap.ofRotationSystem RS) := by
  have hsurj : Function.Surjective RS.vertOf := by
    intro vertex
    have hcard := hsphere.cubic vertex
    have hnonempty : (RS.dartsAt vertex).Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro hempty
      rw [hempty, Finset.card_empty] at hcard
      omega
    obtain ⟨located, hlocated⟩ := hnonempty
    exact ⟨located, (Finset.mem_filter.1 hlocated).2⟩
  have hv : orbitCount RS.rho = Fintype.card V :=
    GoertzelV24StellarDualStructure.orbitCount_rho_eq_card_vertex RS
      hrotation hsurj
  have he : orbitCount RS.alpha = Fintype.card E :=
    GoertzelV24StellarDualStructure.orbitCount_alpha_eq_card_edge RS
  have hf : orbitCount RS.phi = Fintype.card (OrbitFace RS) :=
    GoertzelV24StellarDualStructure.orbitCount_phi_eq_card_orbitFace RS
  have hc : Hypermap.compCount (Hypermap.ofRotationSystem RS) = 1 :=
    GoertzelV24ConnectedMapEulerBound.hypermap_compCount_eq_one_of_primalConnected
      RS hconnected hrotation
  have hdarts : Fintype.card RS.D = 2 * Fintype.card E :=
    RS.card_darts_eq_twice_card_edges
  have heuler : Fintype.card V + Fintype.card (OrbitFace RS) =
      Fintype.card E + 2 := by
    have h := hsphere.euler
    omega
  rw [Hypermap.planar_iff_eulerRhs_eq,
    Hypermap.eulerRhs_eq_card_add_two_mul_compCount,
    Hypermap.eulerLhs_eq_orbit_sum]
  simp only [Hypermap.ofRotationSystem_edge, Hypermap.ofRotationSystem_node,
    Hypermap.ofRotationSystem_face, Hypermap.orbitCount_inv]
  rw [hc, hv, he, hf, hdarts]
  omega

/-- The route's two-sided-face condition is the hypermap bridge condition:
the two darts of each edge lie on different facial cycles. -/
theorem hypermap_bridgeless_of_twoSided
    (RS : RotationSystem V E) (htwo : OrbitFacesTwoSided RS) :
    Hypermap.Patch.Bridgeless (Hypermap.ofRotationSystem RS) := by
  intro dart hface
  exact htwo dart (Quotient.sound hface)

/-- Each of the two actual snipped pieces is planar, with no extra planarity
assumption beyond the route's existing spherical class. -/
theorem orderedContourBond_planar_parts
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (root far : OrbitFace rotation.toRotationSystem)
    {lo hi width : ℕ}
    (bond : OrderedContourBond rotation root far lo hi width)
    (outerD : RetainedDart rotation.toRotationSystem
      (deletedRegionKeep bond.deleted))
    (outerR : RetainedDart rotation.toRotationSystem
      (deletedSideKeep bond.deleted)) :
    Hypermap.Planar (diskMap rotation.toRotationSystem bond.deleted outerD) ∧
      Hypermap.Planar (remMap rotation.toRotationSystem bond.deleted outerR) := by
  exact (orderedContourBond_planar_iff rotation hclass htwo root far bond
    outerD outerR).mp
      (hypermap_planar_of_spherical rotation.toRotationSystem hclass.spherical
        hclass.primalConnected hclass.vertexRotationCyclic)

/-- The same physical patch transfers the ambient no-bridge condition to
both snipped pieces. This is a class-preservation consequence of the cut,
not a separate bridge assumption on either piece. -/
theorem orderedContourBond_bridgeless_parts
    (rotation : Data G)
    (hclass : BridgelessSphericalCubicMapData rotation.toRotationSystem)
    (htwo : OrbitFacesTwoSided rotation.toRotationSystem)
    (root far : OrbitFace rotation.toRotationSystem)
    {lo hi width : ℕ}
    (bond : OrderedContourBond rotation root far lo hi width)
    (outerD : RetainedDart rotation.toRotationSystem
      (deletedRegionKeep bond.deleted))
    (outerR : RetainedDart rotation.toRotationSystem
      (deletedSideKeep bond.deleted)) :
    Hypermap.Patch.Bridgeless
        (diskMap rotation.toRotationSystem bond.deleted outerD) ∧
      Hypermap.Patch.Bridgeless
        (remMap rotation.toRotationSystem bond.deleted outerR) := by
  exact (orderedContourBond_patch rotation hclass htwo root far bond
    outerD outerR).bridgeless_parts
      (hypermap_bridgeless_of_twoSided rotation.toRotationSystem htwo)

end OrderedBond

end

end Mettapedia.GraphTheory.FourColor.StructuralCutSnipPatch
