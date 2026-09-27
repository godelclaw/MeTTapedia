import Mettapedia.GraphTheory.FourColor.OpenTangleRewireFaces
import Mettapedia.GraphTheory.FourColor.NamedOpenFace
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitCountCongr

/-!
# Euler change under replacement in an arbitrary fixed exterior

Equal named boundary-return records preserve the face-count correction
caused by sewing, even when the replacement has a different interior
carrier. The remaining Euler difference is a quantity computed from the
replaced piece alone. This is an actual-composite theorem, not a premise
asserting that replacement is topologically valid. Connectivity and
bridgelessness are not inferred from Euler equality.
-/

namespace Mettapedia.GraphTheory.FourColor.OpenTangleReplacementEuler

open Equiv Equiv.Perm
open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open GoertzelV24CompositeSphericity GoertzelV24OrderedCutFaceReturnProfile
open GoertzelV24FaceOrbitPartitionBridge GoertzelV24RetainedSpliceFaceCount
open BoundaryRewireCycles OpenTangleMarkedFace OpenTangleRewireFaces

noncomputable section
attribute [local instance] Classical.propDecidable

theorem cycle_count_sum {A B : Type*} [Fintype A] [DecidableEq A]
    [Fintype B] [DecidableEq B] (p : Perm A) (q : Perm B) :
    (Equiv.Perm.partition (Equiv.sumCongr p q)).parts.card =
      p.partition.parts.card + q.partition.parts.card := by
  rw [← card_permOrbit_eq_card_partition_parts, ← card_permOrbit_eq_card_partition_parts p,
    ← card_permOrbit_eq_card_partition_parts q]
  rw [Fintype.card_congr (GoertzelV24OrbitCountCongr.sumOrbitEquiv p q), Fintype.card_sum]

variable {V W I J L R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]

theorem observed_face_count (left : OpenTangleData V I L) (right : OpenTangleData W J R)
    (matching : L ≃ R) (hit : Carrier I J L R → Prop) (hhit : ∀ d, IsSeam d → hit d) :
    Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace (compositeRS left right matching)) +
        (nextHitPerm (Equiv.sumCongr (openPhi left) (openPhi right)) hit).partition.parts.card =
      (openPhi left).partition.parts.card + (openPhi right).partition.parts.card +
        (nextHitPerm (Equiv.sumCongr (openPhi left) (openPhi right)) hit *
          observedSwap matching hit hhit).partition.parts.card := by
  have hc := cycle_count_rewire (Equiv.sumCongr (openPhi left) (openPhi right)) hit
    (observedSwap matching hit hhit)
  rw [observedSwap_extend] at hc
  have hf : Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace
        (compositeRS left right matching)) =
      (Equiv.sumCongr (openPhi left) (openPhi right) *
        OpenTangleMarkedFace.seamSwap matching : Perm (Carrier I J L R)).partition.parts.card := by
    change Fintype.card (Quotient (SameCycle.setoid
      (left.composeRotationSystem right matching).phi)) = _
    rw [card_permOrbit_eq_card_partition_parts, OpenTangleMarkedFace.compose_phi]
    exact card_permCongr_partition_parts composeDartEquiv _
  rw [← hf, cycle_count_sum] at hc
  exact hc

variable {W' J' R' K M : Type*}
  [Fintype W'] [DecidableEq W'] [Fintype J'] [DecidableEq J']
  [Fintype R'] [DecidableEq R'] [Fintype K] [Fintype M]

/-- The number of internal face cycles may change; the sewing correction
does not. The exterior is arbitrary and is not an argument of the record. -/
theorem face_count_replacement (left : OpenTangleData V I L)
    (old : OpenTangleData W J R) (new : OpenTangleData W' J' R')
    (oc : R ≃ K) (nc : R' ≃ K) (oo : M → Option (J ⊕ R)) (no : M → Option (J' ⊕ R'))
    (heq : NamedOpenFace.record old oc oo = NamedOpenFace.record new nc no) (outside : L ≃ K) :
    Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace
        (compositeRS left old (outside.trans oc.symm))) + (openPhi new).partition.parts.card =
      Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace
        (compositeRS left new (outside.trans nc.symm))) + (openPhi old).partition.parts.card := by
  let lh : I ⊕ L → Prop := fun _ => True
  have hl : ∀ l, lh (.inr l) := fun _ => trivial
  let e := NamedOpenFace.totalMatching old new oc nc oo no heq lh
  have hr := NamedOpenFace.totalMatching_return old new oc nc oo no heq lh (openPhi left)
  have hs := NamedOpenFace.totalMatching_swap_permCongr old new oc nc oo no heq lh hl outside
  have hrc := card_permCongr_partition_parts e
    (nextHitPerm (Equiv.sumCongr (openPhi left) (openPhi old)) (NamedOpenFace.totalHit lh oc oo))
  rw [hr] at hrc
  have hsc := card_permCongr_partition_parts e
    (nextHitPerm (Equiv.sumCongr (openPhi left) (openPhi old)) (NamedOpenFace.totalHit lh oc oo) *
      observedSwap (outside.trans oc.symm) (NamedOpenFace.totalHit lh oc oo)
        (NamedOpenFace.seam_hit lh hl oc oo))
  rw [Equiv.permCongr_mul, hr, hs] at hsc
  have ho := observed_face_count left old (outside.trans oc.symm)
    (NamedOpenFace.totalHit lh oc oo) (NamedOpenFace.seam_hit lh hl oc oo)
  have hn := observed_face_count left new (outside.trans nc.symm)
    (NamedOpenFace.totalHit lh nc no) (NamedOpenFace.seam_hit lh hl nc no)
  omega

/-- Twice the open piece's Euler contribution, expressed without division
and computed from its own vertices, internal darts and open face cycles.
No finite range for this integer is asserted. -/
def eulerMass (data : OpenTangleData W J R) : ℤ :=
  2 * (Fintype.card W : ℤ) - Fintype.card J + 2 * (openPhi data).partition.parts.card

theorem twice_euler_replacement (left : OpenTangleData V I L)
    (old : OpenTangleData W J R) (new : OpenTangleData W' J' R')
    (oc : R ≃ K) (nc : R' ≃ K) (oo : M → Option (J ⊕ R)) (no : M → Option (J' ⊕ R'))
    (heq : NamedOpenFace.record old oc oo = NamedOpenFace.record new nc no) (outside : L ≃ K) :
    2 * compositeEuler left old (outside.trans oc.symm) -
        2 * compositeEuler left new (outside.trans nc.symm) = eulerMass old - eulerMass new := by
  have hf := face_count_replacement left old new oc nc oo no heq outside
  have ho := two_mul_card_edge (compositeRS left old (outside.trans oc.symm))
  have hn := two_mul_card_edge (compositeRS left new (outside.trans nc.symm))
  change 2 * Fintype.card (compositeDarts left old (outside.trans oc.symm)).Edge =
    Fintype.card (GoertzelV24RotationSpliceConstructor.MatchedSeam.Dart (I ⊕ J) L R) at ho
  change 2 * Fintype.card (compositeDarts left new (outside.trans nc.symm)).Edge =
    Fintype.card (GoertzelV24RotationSpliceConstructor.MatchedSeam.Dart (I ⊕ J') L R') at hn
  simp only [GoertzelV24RotationSpliceConstructor.MatchedSeam.Dart, Fintype.card_sum] at ho hn
  have hb := Fintype.card_congr (oc.trans nc.symm)
  simp only [compositeEuler, eulerMass, Fintype.card_sum]
  omega

/-- Exact context congruence for Euler equality. This neither assumes nor
concludes connectivity, bridgelessness, or a global size bound. -/
theorem euler_eq_iff_mass (left : OpenTangleData V I L)
    (old : OpenTangleData W J R) (new : OpenTangleData W' J' R')
    (oc : R ≃ K) (nc : R' ≃ K) (oo : M → Option (J ⊕ R)) (no : M → Option (J' ⊕ R'))
    (heq : NamedOpenFace.record old oc oo = NamedOpenFace.record new nc no) (outside : L ≃ K) :
    compositeEuler left old (outside.trans oc.symm) = compositeEuler left new (outside.trans nc.symm) ↔
      eulerMass old = eulerMass new := by
  have := twice_euler_replacement left old new oc nc oo no heq outside
  omega

end
end Mettapedia.GraphTheory.FourColor.OpenTangleReplacementEuler
