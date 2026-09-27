import Mettapedia.GraphTheory.FourColor.FacialCycleLayer
import Mettapedia.GraphTheory.FourColor.ZigzagRingGeometry

/-!
# The literal open tangle of a facial ring layer

Opening the original graph on the recognized row gives the same dart and
face dynamics as the literal ring. The coordinate map preserves the
internal/boundary partition, edge reversal and vertex rotation. Thus the
colouring recognition and the open-face recognition refer to the same
physical row.
-/

namespace Mettapedia.GraphTheory.FourColor.FacialCycleTangle

open InducedCycleLayer FacialCycleLayer SimpleGraphDartRotation ZigzagRing
open GoertzelV24RotationCutDartDecomposition GoertzelV24OpenTangleComposition
open OpenTangleMarkedFace PhysicalForkCodeFaces

noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]
variable {k : ℕ} [NeZero k] (C : Cycle G k) (hk : 2 ≤ k)
  (hG : G.IsRegularOfDegree 3) (data : Data G)

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

def Row (v : V) : Prop := ∃ w, v = C.vertex w

def retained (d : AllDart k) : RetainedDart (RS data) (Row C) :=
  ⟨C.embedding hk hG d, ⟨(ring k).vertOf d, C.embedding_fst hk hG d⟩⟩

theorem retained_bijective : Function.Bijective (retained C hk hG data) := by
  constructor
  · intro d e he
    exact C.embedding_injective hk hG (congrArg Subtype.val he)
  · intro d
    obtain ⟨x, hx⟩ := C.embedding_covers hk hG d.val d.property
    exact ⟨x, Subtype.ext hx⟩

def retainedEquiv : AllDart k ≃ RetainedDart (RS data) (Row C) :=
  Equiv.ofBijective (retained C hk hG data) (retained_bijective C hk hG data)

def coordinate : AllDart k ≃ InternalDart (RS data) (Row C) ⊕ BoundaryDart (RS data) (Row C) :=
  (retainedEquiv C hk hG data).trans (retainedDartEquivInternalSumBoundary (RS data) (Row C))

def tangle : OpenTangleData {v : V // Row C v}
    (InternalDart (RS data) (Row C)) (BoundaryDart (RS data) (Row C)) :=
  OpenTangleData.ofVertexSide (RS data) (Row C) (retained C hk hG data (.inr (.inl 0)))

theorem internal_mate (d : ZigzagRing.Dart k) :
    Row C ((RS data).vertOf ((RS data).alpha (C.embedding hk hG (.inl d)))) := by
  change ∃ w, (C.embedding hk hG (.inl d)).symm.fst = C.vertex w
  rw [C.embedding_flip hk hG]
  exact ⟨(ring k).vertOf (.inl (flip k d)), C.embedding_fst hk hG _⟩

theorem boundary_mate (v : Vtx k) :
    ¬ Row C ((RS data).vertOf ((RS data).alpha (C.embedding hk hG (.inr v)))) := by
  rintro ⟨w, hw⟩
  exact C.port_not_cycle hk hG v w hw

def internalDart (d : ZigzagRing.Dart k) : InternalDart (RS data) (Row C) :=
  ⟨retained C hk hG data (.inl d), internal_mate C hk hG data d⟩

def boundaryDart (v : Vtx k) : BoundaryDart (RS data) (Row C) :=
  ⟨retained C hk hG data (.inr v), boundary_mate C hk hG data v⟩

theorem coordinate_internal (d : ZigzagRing.Dart k) :
    coordinate C hk hG data (.inl d) = .inl (internalDart C hk hG data d) :=
  TubeSlab.equiv_internal (RS data) (Row C) (internalDart C hk hG data d)

theorem coordinate_boundary (v : Vtx k) :
    coordinate C hk hG data (.inr v) = .inr (boundaryDart C hk hG data v) :=
  TubeSlab.equiv_boundary (RS data) (Row C) (boundaryDart C hk hG data v)

theorem internalDart_flip (d : ZigzagRing.Dart k) :
    internalAlpha (RS data) (Row C) (internalDart C hk hG data d) =
      internalDart C hk hG data (flip k d) := by
  apply Subtype.ext
  apply Subtype.ext
  exact C.embedding_flip hk hG d

/-- The internal edges and the exposed half-edges are the original ones. -/
theorem coordinate_alpha (d : AllDart k) :
    coordinate C hk hG data
        (Equiv.sumCongr (ring k).interiorAlpha (Equiv.refl (Vtx k)) d) =
      Equiv.sumCongr (tangle C hk hG data).interiorAlpha
        (Equiv.refl (BoundaryDart (RS data) (Row C))) (coordinate C hk hG data d) := by
  rcases d with d | v
  · simp only [Equiv.sumCongr_apply, Sum.map_inl, coordinate_internal]
    exact congrArg Sum.inl (internalDart_flip C hk hG data d).symm
  · simp only [Equiv.sumCongr_apply, Sum.map_inr, Equiv.refl_apply, coordinate_boundary]

variable {C hk hG data}
variable {R : Finset (GoertzelV24FaceOrbitIncidence.OrbitFace (RS data))}
variable (h : BoundsFaces C.toFrame hk hG data R) (hC : Cubic3 (RS data))
  (ha : AlternatingDegrees C.toFrame data R)

include h hC ha

theorem coordinate_rho (d : AllDart k) :
    coordinate C hk hG data ((rho k) d) =
      (tangle C hk hG data).rho (coordinate C hk hG data d) := by
  apply (retainedDartEquivInternalSumBoundary (RS data) (Row C)).symm.injective
  unfold tangle
  rw [OpenTangleData.ofVertexSide_rho_underlying]
  simp only [coordinate, Equiv.trans_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  exact (h.embedding_rho hC ha d).symm

/-- Conjugacy of the literal open-face permutations, before any ports are
glued to a surrounding graph. Boundary darts use the fixed-half-edge convention. -/
theorem coordinate_face (d : AllDart k) :
    coordinate C hk hG data ((face k) d) =
      openPhi (tangle C hk hG data) (coordinate C hk hG data d) := by
  change coordinate C hk hG data
      ((rho k) (Equiv.sumCongr (ring k).interiorAlpha (Equiv.refl (Vtx k)) d)) = _
  rw [coordinate_rho h hC ha, coordinate_alpha]
  rfl

theorem face_conjugate :
    (coordinate C hk hG data).permCongr (face k) = openPhi (tangle C hk hG data) := by
  apply Equiv.ext
  intro d
  obtain ⟨x, rfl⟩ := (coordinate C hk hG data).surjective d
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using coordinate_face h hC ha x

/-- The recognized open row has exactly the same two oriented face classes
as the literal ring; no closed ambient face count is inferred. -/
theorem face_sameCycle_iff (d e : AllDart k) :
    (openPhi (tangle C hk hG data)).SameCycle
        (coordinate C hk hG data d) (coordinate C hk hG data e) ↔
      faceSide k d = faceSide k e := by
  rw [← face_conjugate h hC ha]
  rw [GoertzelV24OrderedCutFaceReturnProfile.permCongr_sameCycle_iff]
  exact ZigzagRing.face_sameCycle_iff k d e

end
end Mettapedia.GraphTheory.FourColor.FacialCycleTangle
