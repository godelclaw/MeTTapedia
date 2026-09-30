import Mettapedia.GraphTheory.FourColor.ZigzagTwoRowWiringGeometry
import Mettapedia.GraphTheory.FourColor.OpenTanglePortFaceCount

/-!
# Face counts and strict two-row free-wire reduction

Opposite exterior and tube returns make the whole Euler calculation a
symbolic boundary calculation. Combined with the two-shore cut theorem,
this proves a strict reduction with actual colouring reconstruction.
Recognition of these exterior conditions in a general ambient map remains
a separate geometric obligation.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing.ShiftedWiring.Geometry

open Equiv Equiv.Perm GoertzelV24OpenTangleComposition
open GoertzelV24RotationSpliceConstructor GoertzelV24CompositeSeamMultigraph
open GoertzelV24OrderedCutFaceReturnProfile GoertzelV24RetainedSpliceFaceCount
open GoertzelV24FaceOrbitPartitionBridge GoertzelV24FaceOrbitIncidence
open GoertzelV24PermutationOrbitSurgery OpenTangleMarkedFace
open OpenTanglePortReplacement OpenTangleReplacementEuler OpenTangleRewireFaces
open SerialTangleFaceTransfer SerialTangleFaceCode
open SerialTangleSmallCutTransfer
open GoertzelV24CompositeSeamCubic OpenTangleVertexReflection
open GoertzelV24TwoEdgeCutMinimality
open GoertzelV24CompositeSphericity

noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable tubeVertexFintype tubeInteriorFintype

private theorem inverse_cycle_count {A : Type*} [Fintype A] [DecidableEq A]
    (p : Perm A) : p⁻¹.partition.parts.card = p.partition.parts.card := by
  rw [← card_permOrbit_eq_card_partition_parts, ← card_permOrbit_eq_card_partition_parts]
  apply Fintype.card_congr
  exact Quotient.congr (Equiv.refl _) (fun _ _ => sameCycle_inv)

private theorem swap_cycle_count {A : Type*} [Fintype A] [DecidableEq A] :
    (MatchedSeam.seamSwap (Equiv.refl A)).partition.parts.card = Fintype.card A := by
  let p := MatchedSeam.seamSwap (Equiv.refl A)
  let tag : A ⊕ A → A := Sum.elim id id
  have hstep (d) : tag (p d) = tag d := by cases d <;> rfl
  have hpow (n : ℕ) (d) : tag ((p ^ n) d) = tag d := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [pow_succ', Perm.mul_apply, hstep] using ih
  have hc (d e) : p.SameCycle d e ↔ tag d = tag e := by
    constructor
    · intro h
      obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
      simpa only [hn] using (hpow n d).symm
    · rcases d with d | d <;> rcases e with e | e
      all_goals intro he; change d = e at he; subst e
      · exact .refl _ _
      · exact (Perm.SameCycle.refl p (.inl d)).apply_right
      · exact (Perm.SameCycle.refl p (.inr d)).apply_right
      · exact .refl _ _
  rw [← card_permOrbit_eq_card_partition_parts]
  change orbitCount p = _
  have h := OrbitCountSplitting.orbitCount_eq_card_of_completeInvariant tag hc
    (fun a => ⟨.inl a, rfl⟩)
  simpa using h

variable (k : ℕ) [NeZero k]

private theorem opposite_sewing_count :
    (partition (Equiv.sumCongr (boundaryPerm k)⁻¹ (boundaryPerm k) *
      MatchedSeam.seamSwap (Equiv.refl _))).parts.card = 2 * k := by
  let e := Equiv.sumCongr (Equiv.refl (Fin k ⊕ Fin k)) (boundaryPerm k)⁻¹
  have he : e.permCongr (Equiv.sumCongr (boundaryPerm k)⁻¹ (boundaryPerm k) *
      MatchedSeam.seamSwap (Equiv.refl _)) = MatchedSeam.seamSwap (Equiv.refl _) := by
    ext d
    cases d <;> simp [e, Perm.mul_apply, MatchedSeam.seamSwap]
  have h := card_permCongr_partition_parts e
    (Equiv.sumCongr (boundaryPerm k)⁻¹ (boundaryPerm k) * MatchedSeam.seamSwap (Equiv.refl _))
  rw [he, swap_cycle_count] at h
  simpa [Fintype.card_sum, Fintype.card_fin, two_mul] using h.symm

private theorem shifted_return : (boundaryPerm k)⁻¹ *
    MatchedSeam.seamSwap (wireMatching k) = MatchedSeam.seamSwap (Equiv.refl _) := by
  ext d
  rcases d with i | i <;>
    simp [boundaryPerm, wireMatching, MatchedSeam.seamSwap, Perm.mul_apply]

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  (O : OpenTangleData V I (Fin k ⊕ Fin k))

theorem face_phi (hs : Separated k O) : (closed k O hs).phi = openPhi O *
    ofSubtype ((boundaryCoordinate I (Fin k ⊕ Fin k)).symm.permCongr
      (MatchedSeam.seamSwap (wireMatching k))) := by
  change O.rho * (raw k O).alpha = _
  ext d
  simp only [Perm.mul_apply]
  rcases d with i | (i | i)
  · rw [ofSubtype_apply_of_not_mem _ (by exact id : ¬ Boundary (.inl i))]
    rfl
  · rw [ofSubtype_apply_of_mem _ (by trivial : Boundary (Sum.inr (Sum.inl i) : I ⊕ (Fin k ⊕ Fin k)))]
    rfl
  · rw [ofSubtype_apply_of_mem _ (by trivial : Boundary (Sum.inr (Sum.inr i) : I ⊕ (Fin k ⊕ Fin k)))]
    rfl

/-- The whole face count of the actual free-wire closure, for any exterior
return permutation, including unmarked interior faces. -/
theorem face_count (hs : Separated k O) :
    Fintype.card (OrbitFace (closed k O hs)) + (returnCode O).partition.parts.card =
      (openPhi O).partition.parts.card +
        (partition (returnCode O * MatchedSeam.seamSwap (wireMatching k))).parts.card := by
  let e := boundaryCoordinate I (Fin k ⊕ Fin k)
  let r := nextHitPerm (openPhi O) Boundary
  let s := e.symm.permCongr (MatchedSeam.seamSwap (wireMatching k))
  have hr := card_permCongr_partition_parts e r
  have hs' : e.permCongr s = MatchedSeam.seamSwap (wireMatching k) :=
    e.permCongr.apply_symm_apply _
  have hrs := card_permCongr_partition_parts e (r * s)
  rw [Equiv.permCongr_mul, hs'] at hrs
  have h := BoundaryRewireCycles.cycle_count_rewire (openPhi O) Boundary s
  rw [← face_phi k O hs] at h
  change Fintype.card (Quotient (SameCycle.setoid (closed k O hs).phi)) + _ = _
  rw [card_permOrbit_eq_card_partition_parts]
  change (returnCode O).partition.parts.card = _ at hr
  change (partition (returnCode O * MatchedSeam.seamSwap (wireMatching k))).parts.card = _ at hrs
  dsimp [r, s] at hr hrs
  dsimp [s] at h
  omega

theorem face_count_opposite (hs : Separated k O)
    (hr : returnCode O = (boundaryPerm k)⁻¹) :
    Fintype.card (OrbitFace (closed k O hs)) + 2 = (openPhi O).partition.parts.card + k := by
  have h := face_count k O hs
  rw [hr, inverse_cycle_count, boundary_cycle_count, shifted_return, swap_cycle_count] at h
  simpa using h

theorem euler_preserved (hs : Separated k O)
    (hr : returnCode O = (boundaryPerm k)⁻¹) :
    (Fintype.card V : ℤ) - Fintype.card (data k O hs).Edge +
      Fintype.card (OrbitFace (closed k O hs)) = compositeEuler O (asOpen (tube k 1).data) (Equiv.refl _) := by
  have hf := OpenTanglePortFaceCount.face_count O (asOpen (tube k 1).data) (Equiv.refl _)
  rw [hr, tube_returnCode, cycle_count_sum, inverse_cycle_count,
    boundary_cycle_count, opposite_sewing_count] at hf
  change Fintype.card (OrbitFace (compositeRS O (asOpen (tube k 1).data) (Equiv.refl _))) + 4 =
    (openPhi O).partition.parts.card + (openPhi (asOpen (tube k 1).data)).partition.parts.card + 2 * k at hf
  have hn := face_count_opposite k O hs hr
  have hm := tube_eulerMass k 1
  unfold eulerMass at hm
  have heo := two_mul_card_edge (original k O)
  have hen := two_mul_card_edge (closed k O hs)
  change 2 * Fintype.card (compositeDarts O (asOpen (tube k 1).data) (Equiv.refl _)).Edge =
    Fintype.card ((I ⊕ (tube k 1).I) ⊕ ((Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k))) at heo
  change 2 * Fintype.card (data k O hs).Edge = Fintype.card (I ⊕ (Fin k ⊕ Fin k)) at hen
  simp only [Fintype.card_sum, Fintype.card_fin] at heo hen
  unfold compositeEuler
  simp only [Fintype.card_sum]
  omega

theorem replacement_class (hk : 2 ≤ k) (H : TwoShores k O)
    (hr : returnCode O = (boundaryPerm k)⁻¹)
    (h : BridgelessSphericalCubicMapData (original k O)) :
    BridgelessSphericalCubicMapData (closed k O H.separated) := by
  have hg := structural k O hk H h.primalConnected h.edgeBridgeFree
  exact {
    spherical := {
      cubic := cubic k O H.separated
        (exterior_isCubic O (asOpen (tube k 1).data) (Equiv.refl _) h.spherical.cubic)
      euler := (euler_preserved k O H.separated hr).trans h.spherical.euler }
    primalConnected := hg.1
    vertexRotationCyclic := rotationCyclic k O H.separated
      (exterior_rotationCyclic O (asOpen (tube k 1).data) (Equiv.refl _) h.vertexRotationCyclic)
    edgeBridgeFree := hg.2 }

omit [DecidableEq V] [Fintype I] [DecidableEq I] in
/-- No wire vertex is added: all four `k` ring vertices disappear. -/
theorem vertex_loss : Fintype.card (V ⊕ (tube k 1).V) = Fintype.card V + 4 * k := by
  have h := tube_vertex_card k 1
  rw [Nat.card_eq_fintype_card] at h
  rw [Fintype.card_sum, h]
  omega

/-- One structural law handles every width and compatible two-shore
exterior in the stated geometric domain. -/
theorem strict_reduction (hk : 3 ≤ k) (H : TwoShores k O)
    (hr : returnCode O = (boundaryPerm k)⁻¹)
    (h : BridgelessSphericalCubicMapData (original k O)) :
    Fintype.card V < Fintype.card (V ⊕ (tube k 1).V) ∧
      BridgelessSphericalCubicMapData (closed k O H.separated) ∧
      (RotationSystemTaitColorable (closed k O H.separated) →
        RotationSystemTaitColorable (original k O)) := by
  refine ⟨?_, replacement_class k O (by omega) H hr h, ?_⟩
  · rw [vertex_loss]
    omega
  · rintro ⟨c, hc⟩
    obtain ⟨old, hold, _⟩ := reconstruct_colour k O hk H.separated c hc
    exact ⟨old, hold⟩

end
end Mettapedia.GraphTheory.FourColor.ZigzagRing.ShiftedWiring.Geometry
