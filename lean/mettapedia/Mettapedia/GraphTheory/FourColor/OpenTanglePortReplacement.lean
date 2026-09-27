import Mettapedia.GraphTheory.FourColor.SerialTangleFaceCode
import Mettapedia.GraphTheory.FourColor.OpenTangleReplacementEuler

/-!
# Replacement using face returns in the actual port coordinates

Equal boundary-return permutations preserve the face correction in every
fixed sewing context. They also preserve cofaciality of all exterior darts.
Together with equal open Euler mass this gives equal Euler characteristics
of the literal closed composites, even with different interior carriers.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement

open Equiv Equiv.Perm
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24CompositeSphericity GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24RetainedSpliceFaceCount
open OpenTangleMarkedFace OpenTangleRewireFaces OpenTangleReplacementEuler FaceReturnSum
open SerialTangleFaceTransfer SerialTangleFaceCode SerialTangleSmallCutTransfer

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W W' I J J' L R : Type*}

/-- The same boundary coordinate used by the serial transfer semantics. -/
def portMatching (J J' R : Type*) : {d : J ⊕ R // Boundary d} ≃
    {d : J' ⊕ R // Boundary d} :=
  (boundaryCoordinate J R).trans (boundaryCoordinate J' R).symm

def observed : Carrier I J L R → Prop := Sum.elim (fun _ => True) Boundary

def contextMatching : {d : Carrier I J L R // observed d} ≃
    {d : Carrier I J' L R // observed d} :=
  sumMatching (fun _ => True) (portMatching J J' R)

theorem seam_observed (d : Carrier I J L R) (h : IsSeam d) : observed d := by
  rcases d with (i | l) | (j | r)
  · trivial
  · trivial
  · exact h
  · trivial

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype J'] [DecidableEq J'] [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

def returnCode (T : OpenTangleData W J R) : Perm R :=
  (boundaryCoordinate J R).permCongr (nextHitPerm (openPhi T) Boundary)

theorem returnCode_asOpen (T : TwoSidedOpenTangleData V I L R) :
    returnCode (asOpen T) = SerialTangleFaceCode.encode T := rfl

variable (old : OpenTangleData W J R) (new : OpenTangleData W' J' R)
  (heq : returnCode old = returnCode new)

include heq

theorem portMatching_return (a : {d : J ⊕ R // Boundary d}) :
    portMatching J J' R (nextHitPerm (openPhi old) Boundary a) =
      nextHitPerm (openPhi new) Boundary (portMatching J J' R a) := by
  apply (boundaryCoordinate J' R).injective
  have h := Equiv.congr_fun heq (boundaryCoordinate J R a)
  simpa only [returnCode, Equiv.permCongr_apply, Equiv.symm_apply_apply,
    portMatching, Equiv.trans_apply, Equiv.apply_symm_apply] using h

theorem contextMatching_return (left : Perm (I ⊕ L)) :
    (contextMatching (I := I) (L := L)).permCongr
      (nextHitPerm (Equiv.sumCongr left (openPhi old)) observed) =
      nextHitPerm (Equiv.sumCongr left (openPhi new)) observed :=
  sumMatching_permCongr left (openPhi old) (openPhi new) (fun _ => True) _ _ _
    (portMatching_return old new heq)

omit heq [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype J'] [DecidableEq J'] [Fintype L] [DecidableEq L]
  [Fintype R] [DecidableEq R] in
theorem contextMatching_swap (m : L ≃ R) :
    (contextMatching (I := I) (J := J) (J' := J') (L := L)).permCongr
      (observedSwap m observed seam_observed) = observedSwap m observed seam_observed := by
  apply Equiv.ext
  intro z
  obtain ⟨d, rfl⟩ := (contextMatching (I := I) (J := J) (J' := J') (L := L)).surjective z
  simp only [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  rcases d with ⟨(i | l) | (j | r), h⟩
  · rfl
  · rfl
  · exact h.elim
  · rfl

variable [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype W'] [DecidableEq W']

/-- The number of faces wholly inside the replaced piece may change.
The sewing correction is fixed by its return permutation alone. -/
theorem face_count_replacement (outside : OpenTangleData V I L) (m : L ≃ R) :
    Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace (compositeRS outside old m)) +
        (openPhi new).partition.parts.card =
      Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace (compositeRS outside new m)) +
        (openPhi old).partition.parts.card := by
  let e := contextMatching (I := I) (J := J) (J' := J') (L := L) (R := R)
  have hr := contextMatching_return old new heq (openPhi outside)
  have hs := contextMatching_swap (I := I) (J := J) (J' := J') m
  have hrc := card_permCongr_partition_parts e
    (nextHitPerm (Equiv.sumCongr (openPhi outside) (openPhi old)) observed)
  rw [hr] at hrc
  have hsc := card_permCongr_partition_parts e
    (nextHitPerm (Equiv.sumCongr (openPhi outside) (openPhi old)) observed *
      observedSwap m observed seam_observed)
  rw [Equiv.permCongr_mul, hr, hs] at hsc
  have ho := observed_face_count outside old m observed seam_observed
  have hn := observed_face_count outside new m observed seam_observed
  omega

theorem twice_euler_replacement (outside : OpenTangleData V I L) (m : L ≃ R) :
    2 * compositeEuler outside old m - 2 * compositeEuler outside new m =
      eulerMass old - eulerMass new := by
  have hf := face_count_replacement old new heq outside m
  have ho := two_mul_card_edge (compositeRS outside old m)
  have hn := two_mul_card_edge (compositeRS outside new m)
  change 2 * Fintype.card (compositeDarts outside old m).Edge =
    Fintype.card (GoertzelV24RotationSpliceConstructor.MatchedSeam.Dart (I ⊕ J) L R) at ho
  change 2 * Fintype.card (compositeDarts outside new m).Edge =
    Fintype.card (GoertzelV24RotationSpliceConstructor.MatchedSeam.Dart (I ⊕ J') L R) at hn
  simp only [GoertzelV24RotationSpliceConstructor.MatchedSeam.Dart, Fintype.card_sum] at ho hn
  simp only [compositeEuler, eulerMass, Fintype.card_sum]
  omega

theorem euler_eq_iff_mass (outside : OpenTangleData V I L) (m : L ≃ R) :
    compositeEuler outside old m = compositeEuler outside new m ↔
      eulerMass old = eulerMass new := by
  have := twice_euler_replacement old new heq outside m
  omega

/-- All exterior darts keep their pairwise cofaciality, including those
on faces that never touch the seam. -/
theorem exterior_sameCycle_iff (outside : OpenTangleData V I L) (m : L ≃ R)
    (a b : I ⊕ L) :
    (outside.composeRotationSystem old m).phi.SameCycle
        (composeDartEquiv (.inl a)) (composeDartEquiv (.inl b)) ↔
      (outside.composeRotationSystem new m).phi.SameCycle
        (composeDartEquiv (.inl a)) (composeDartEquiv (.inl b)) := by
  apply (OpenTangleMarkedFace.compose_sameCycle_iff outside old m observed seam_observed
    ⟨.inl a, trivial⟩ ⟨.inl b, trivial⟩).trans
  apply Iff.trans _ (OpenTangleMarkedFace.compose_sameCycle_iff outside new m observed seam_observed
    ⟨.inl a, trivial⟩ ⟨.inl b, trivial⟩).symm
  rw [← contextMatching_return old new heq (openPhi outside),
    ← contextMatching_swap (I := I) (J := J) (J' := J') m, ← Equiv.permCongr_mul]
  exact (permCongr_sameCycle_iff
    (contextMatching (I := I) (J := J) (J' := J') (L := L) (R := R)) _
    ⟨.inl a, trivial⟩ ⟨.inl b, trivial⟩).symm

end
end Mettapedia.GraphTheory.FourColor.OpenTanglePortReplacement
