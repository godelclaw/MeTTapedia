import Mettapedia.GraphTheory.FourColor.VertexCodeTrace
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamCubic

/-!
# Constructed runs carry one rotation cycle per vertex

The bare tangle record only says the rotation preserves each vertex fiber
setwise; it does not say the fiber is a single cycle. That stronger property
is what lets a dart-level presentation be read as a vertex-level map, and it
is the one genuinely new invariant needed to transport the edge-presentation
Euler theory onto constructed runs.

It holds for every run, because every vertex is born as a star with a
three-cycle rotation, and neither boundary reindexing nor serial composition
alters the rotation at an existing vertex.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeRotationCyclic

open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24CompositeSeamCubic SerialTangleSmallCutTransfer
open TwoSidedBoundaryReindex VertexAttachmentTransfer
open VertexCodeTrace VertexCodeRealization
open TubeSlab.VertexTransfer VertexCodePartition

variable {V W I J L R M S : Type*}

/-- One rotation cycle per vertex, on a two-sided tangle. -/
def RotationCyclic (T : TwoSidedOpenTangleData V I L R) : Prop :=
  ∀ d d' : I ⊕ (L ⊕ R), T.vertOf d = T.vertOf d' → T.rho.SameCycle d d'

theorem asOpen_vertOf (T : TwoSidedOpenTangleData V I L R) (d : I ⊕ (L ⊕ R)) :
    (asOpen T).vertOf d = T.vertOf d := by
  rcases d with _ | (_ | _) <;> rfl

theorem rotationCyclic_asOpen {T : TwoSidedOpenTangleData V I L R}
    (h : RotationCyclic T) : OpenRotationCyclic (asOpen T) := by
  intro d d' hv
  rw [asOpen_vertOf, asOpen_vertOf] at hv
  exact h d d' hv

/-! ## The star -/

set_option maxRecDepth 4000 in
theorem turn_sameCycle (a b : Fin 3) : turn.SameCycle a b := by
  refine ⟨((b - a).val : ℤ), ?_⟩
  rw [zpow_natCast]
  fin_cases a <;> fin_cases b <;> decide +kernel

/-- All three darts of a star lie on one rotation cycle. -/
theorem star_rotationCyclic (order : Fin 3 ≃ R ⊕ S) :
    RotationCyclic (star order) := by
  intro d d' _
  have h := sameCycle_conjEquiv (dartOrder order) turn
    (turn_sameCycle ((dartOrder order).symm d) ((dartOrder order).symm d'))
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  exact h

/-! ## Boundary reindexing -/

theorem reindex_rotationCyclic [Finite I] [Finite L] [Finite R] {L' R' : Type*}
    (T : TwoSidedOpenTangleData V I L R) (e : L' ⊕ R' ≃ L ⊕ R)
    (h : RotationCyclic T) : RotationCyclic (reindex T e) := by
  intro d d' hv
  rw [vert_reindex, vert_reindex] at hv
  have hs := h _ _ hv
  have hc := sameCycle_conjEquiv (darts e (I := I)).symm T.rho hs
  have hrho : (reindex T e).rho = ((darts e).trans T.rho).trans (darts e).symm := by
    ext x
    rcases x with _ | (_ | _) <;> rfl
  rw [hrho]
  simpa using hc

/-! ## Serial composition -/

theorem vertOf_serialCompose (A : TwoSidedOpenTangleData V I L R)
    (B : TwoSidedOpenTangleData W J M S) (m : R ≃ M)
    (d : ((I ⊕ J) ⊕ (R ⊕ M)) ⊕ (L ⊕ S)) :
    (A.serialCompose B m).vertOf d = serialOutputVertOf A B d := by
  rcases d with ((_ | _) | (_ | _)) | (_ | _) <;> rfl

theorem serialCompose_rotationCyclic [Finite I] [Finite L] [Finite R]
    [Finite J] [Finite M] [Finite S]
    (A : TwoSidedOpenTangleData V I L R) (B : TwoSidedOpenTangleData W J M S)
    (m : R ≃ M) (hA : RotationCyclic A) (hB : RotationCyclic B) :
    RotationCyclic (A.serialCompose B m) := by
  intro d d' hv
  obtain ⟨x, rfl⟩ := (serialDartEquiv (I := I) (L := L) (R := R)
    (J := J) (M := M) (S := S)).surjective d
  obtain ⟨x', rfl⟩ := (serialDartEquiv (I := I) (L := L) (R := R)
    (J := J) (M := M) (S := S)).surjective d'
  rw [vertOf_serialCompose, vertOf_serialCompose,
    serialOutputVertOf_serialDartEquiv, serialOutputVertOf_serialDartEquiv] at hv
  change Equiv.Perm.SameCycle
    ((serialDartEquiv.symm.trans (Equiv.sumCongr A.rho B.rho)).trans serialDartEquiv)
    (serialDartEquiv x) (serialDartEquiv x')
  rcases x with a | b <;> rcases x' with a' | b' <;>
    simp only [serialSourceVertOf] at hv
  · exact sameCycle_conjEquiv _ _
      (sameCycle_sumCongr_inl _ _ (hA a a' (Sum.inl.inj hv)))
  · exact absurd hv (by simp)
  · exact absurd hv (by simp)
  · exact sameCycle_conjEquiv _ _
      (sameCycle_sumCongr_inr _ _ (hB b b' (Sum.inr.inj hv)))

/-! ## Every constructed run -/

theorem initial_rotationCyclic {r : ℕ} (a : Code 0 r) (h : Valid a) :
    RotationCyclic (initial a h) :=
  reindex_rotationCyclic _ _ (star_rotationCyclic _)

theorem attach_rotationCyclic {l r : ℕ} (a : Code l r) (h : Valid a)
    [Finite V] [Finite I] {T : TwoSidedOpenTangleData V I (Fin 0) (Fin l)}
    (hT : RotationCyclic T) : RotationCyclic (attach a h T) :=
  reindex_rotationCyclic _ _
    (serialCompose_rotationCyclic _ _ _
      (reindex_rotationCyclic _ _ hT) (star_rotationCyclic _))

/-- **The invariant.** Every constructed run has one rotation cycle per
vertex, so its dart presentation may be read as a vertex-level map. -/
theorem realize_rotationCyclic : {r : ℕ} → (t : Trace r) → RotationCyclic t.realize
  | _, .first a h => initial_rotationCyclic a h
  | _, .step t a h => attach_rotationCyclic a h (realize_rotationCyclic t)

theorem realize_openRotationCyclic {r : ℕ} (t : Trace r) :
    OpenRotationCyclic (asOpen t.realize) :=
  rotationCyclic_asOpen (realize_rotationCyclic t)

end Mettapedia.GraphTheory.FourColor.VertexCodeRotationCyclic
