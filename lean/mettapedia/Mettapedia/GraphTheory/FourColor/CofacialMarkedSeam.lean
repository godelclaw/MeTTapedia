import Mettapedia.GraphTheory.FourColor.CofacialSeamState
import Mettapedia.GraphTheory.FourColor.VertexSideCofacial
import Mettapedia.GraphTheory.FourColor.FrozenMarkedSeam

/-! # The physical marked seam preserves named cofaciality

Equality of the per-shore return records preserves and reflects the actual
face relation of the surviving named darts. The candidate is the same one
whose structural class, strict decrease and frozen Count semantics have
already been proved. Complete facial words and lengths are not asserted
to survive.
-/

namespace Mettapedia.GraphTheory.FourColor.MarkedCotreeSeam.SeamPair

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24RotationCutDartDecomposition GoertzelV24OpenTangleComposition
open GoertzelV24ConnectedEdgeShoreStructuralData GoertzelV24MajorityShoreNormalizedState
open GoertzelV24MajorityShorePhysicalReplacement GoertzelV24VertexSideOpenTangle
open FrozenVertexSideCount NamedOpenFace VertexSideCofacial

noncomputable section
universe u v
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
  {M : Type v} [Fintype M]
local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq
variable {rotation : Data G} {marks : Finset V} {mark : M → G.Dart} {w : ℕ}

def FaceEq (pair : SeamPair rotation marks mark w) : Prop :=
  CofacialSeamState.faceOfShore rotation pair.outer.shore pair.outer.innerOuter mark
    pair.width pair.outerWidth =
  CofacialSeamState.faceOfShore rotation pair.inner.shore pair.inner.innerOuter mark
    pair.width pair.innerWidth

theorem physicalCofacial_candidate_iff (pair : SeamPair rotation marks mark w)
    (hmarks : ∀ m, (mark m).fst ∈ marks) (m n : M) :
    PhysicalCofacial (outsideTangle rotation pair.outer.shore pair.outer.outsideOuter)
        (innerTangle rotation pair.inner.shore pair.inner.innerOuter) pair.matching
        (sideObservation rotation.toRotationSystem (majorityDeletedKeep G pair.outer.shore) mark)
        (sideObservation rotation.toRotationSystem (majorityRetainedKeep G pair.inner.shore) mark) m n ↔
      pair.candidate.phi.SameCycle (pair.liftedMark hmarks m) (pair.liftedMark hmarks n) := by
  rw [VertexSideCofacial.physicalCofacial_iff_ambient]
  have hname : ∀ d, FrozenVertexSideCount.ambientDart pair.outer.outsideOuter
      pair.inner.innerOuter pair.matching d = pair.ambientDart d := by
    rintro ((d | d) | (d | d)) <;> rfl
  simp only [hname]
  constructor
  · rintro ⟨d, e, hd, he, hc⟩
    have hd' : d = pair.liftedMark hmarks m :=
      pair.ambientDart_injective (hd.trans (pair.liftedMark_name hmarks m).symm)
    have he' : e = pair.liftedMark hmarks n :=
      pair.ambientDart_injective (he.trans (pair.liftedMark_name hmarks n).symm)
    rw [hd', he'] at hc
    exact hc
  · intro h
    exact ⟨_, _, pair.liftedMark_name hmarks m, pair.liftedMark_name hmarks n, h⟩

/-- Cofaciality survives on the literal ambient names, including faces
which split or merge away from those names. No perimeter bound is assumed. -/
theorem cofacial_iff (pair : SeamPair rotation marks mark w) (hface : pair.FaceEq)
    (hmarks : ∀ m, (mark m).fst ∈ marks) (m n : M) :
    rotation.toRotationSystem.phi.SameCycle (mark m) (mark n) ↔
      pair.candidate.phi.SameCycle (pair.liftedMark hmarks m) (pair.liftedMark hmarks n) := by
  rw [← pair.physicalCofacial_candidate_iff hmarks m n]
  rw [← VertexSideCofacial.physicalCofacial_reassembly_iff (majorityDeletedVertices G pair.outer.shore)
    pair.outer.outsideOuter pair.outer.innerOuter mark m n]
  let oc := boundaryCoordinate rotation pair.outer.shore pair.width pair.outerWidth
  let nc := boundaryCoordinate rotation pair.inner.shore pair.width pair.innerWidth
  let outside := (oldExteriorMatching rotation pair.outer.shore).trans oc
  have ho : outside.trans oc.symm = oldExteriorMatching rotation pair.outer.shore := by
    ext p; simp [outside]
  have hn : outside.trans nc.symm = pair.matching := by rfl
  have h := NamedOpenFace.physicalCofacial_iff
    (innerTangle rotation pair.outer.shore pair.outer.innerOuter)
    (innerTangle rotation pair.inner.shore pair.inner.innerOuter) oc nc
    (sideObservation rotation.toRotationSystem (majorityRetainedKeep G pair.outer.shore) mark)
    (sideObservation rotation.toRotationSystem (majorityRetainedKeep G pair.inner.shore) mark) hface outside
    (outsideTangle rotation pair.outer.shore pair.outer.outsideOuter)
    (sideObservation rotation.toRotationSystem (majorityDeletedKeep G pair.outer.shore) mark) m n
  simpa only [ho, hn] using h

end
end Mettapedia.GraphTheory.FourColor.MarkedCotreeSeam.SeamPair
