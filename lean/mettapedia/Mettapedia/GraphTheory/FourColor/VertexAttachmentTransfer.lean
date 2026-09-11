import Mettapedia.GraphTheory.FourColor.BoundaryComponentCount
import Mettapedia.GraphTheory.FourColor.SerialTangleJointTransfer

/-!
# The oriented cubic vertex as a physical compositional operation

Separate the old boundary into retained ports L and consumed ports P.
Sew P to a new cubic vertex, retaining its other ports R. Persistent
ports stay on the old piece: no fictitious zero-vertex wire tangle is
introduced. An explicit cyclic enumeration, rather than an arbitrary
three-dart equivalence, determines the new rotation.

The same literal constructor has joint colour/face/cut/Euler transfer
and the exact component change read from zero-cut records. These are
physical one-step semantics for D2b; they do not supply global coverage.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexAttachmentTransfer

open GoertzelV24BoundaryEssentialGluing BoundarySmallCutProfile
open BoundarySmallCutViability StarAttachmentComponents
open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24CompositeSeamMultigraph SerialTangleSmallCutTransfer
open OpenTangleMarkedFace OpenTangleReplacementEuler
open GoertzelV24RetainedSpliceFaceCount

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V I L P R : Type*}

def turn : Equiv.Perm (Fin 3) where
  toFun i := i + 1
  invFun i := i - 1
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def dartOrder (order : Fin 3 ≃ P ⊕ R) : Fin 3 ≃ Empty ⊕ (P ⊕ R) where
  toFun i := .inr (order i)
  invFun := Sum.elim Empty.elim order.symm
  left_inv i := order.symm_apply_apply i
  right_inv := by rintro (e | b); exact e.elim; simp

/-- The supplied enumeration is the cyclic order of the three real darts. -/
def star (order : Fin 3 ≃ P ⊕ R) : TwoSidedOpenTangleData Unit Empty P R where
  interiorVert := Empty.elim
  leftVert := fun _ => ()
  rightVert := fun _ => ()
  interiorAlpha := Equiv.refl Empty
  interiorAlpha_involutive := fun d => d.elim
  interiorAlpha_fixfree := fun d => d.elim
  rho := (dartOrder order).permCongr turn
  vert_rho := fun _ => Subsingleton.elim _ _
  interior_no_self_loops := fun d => d.elim
  outer := .inr (order 0)

theorem star_rotation (order : Fin 3 ≃ P ⊕ R) (i : Fin 3) :
    (star order).rho (.inr (order i)) = .inr (order (i + 1)) := by
  simp [star, Equiv.permCongr_apply, dartOrder, turn]

theorem star_phi (order : Fin 3 ≃ P ⊕ R) :
    openPhi (asOpen (star order)) = (dartOrder order).permCongr turn := by
  ext d
  rcases d with e | b
  · exact e.elim
  · rfl

theorem star_accepts (order : Fin 3 ≃ P ⊕ R) (x : P → Color) (y : R → Color) :
    (star order).AcceptsBoundaryWords x y ↔
      (∀ b, Sum.elim x y b ≠ 0) ∧ Function.Injective (Sum.elim x y) := by
  constructor
  · rintro ⟨c, hc, hx, hy⟩
    have hw (b : P ⊕ R) : c (.inr b) = Sum.elim x y b := by
      cases b with
      | inl p => exact congrFun hx p
      | inr r => exact congrFun hy r
    refine ⟨fun b => hw b ▸ hc.2.2 (.inr b), ?_⟩
    intro a b he
    by_contra hn
    exact hc.2.1 (Subsingleton.elim _ _) (fun hh => hn (Sum.inr.inj hh))
      ((hw a).trans (he.trans (hw b).symm))
  · rintro ⟨hn, hi⟩
    refine ⟨Sum.elim Empty.elim (Sum.elim x y), ⟨?_, ?_, ?_⟩, rfl, rfl⟩
    · exact fun e => e.elim
    · rintro (e | a) (e | b) _ hab <;> try exact e.elim
      exact fun he => hab (congrArg Sum.inr (hi he))
    · rintro (e | b)
      · exact e.elim
      · exact hn b

variable [Fintype P] [DecidableEq P] [Fintype R] [DecidableEq R]

theorem star_faces (order : Fin 3 ≃ P ⊕ R) :
    (openPhi (asOpen (star order))).partition.parts.card = 1 := by
  rw [star_phi, card_permCongr_partition_parts]
  decide +kernel

theorem star_mass (order : Fin 3 ≃ P ⊕ R) : eulerMass (asOpen (star order)) = 4 := by
  simp [eulerMass, star_faces]

omit [DecidableEq P] [DecidableEq R] in
theorem star_arity (order : Fin 3 ≃ P ⊕ R) : Fintype.card P + Fintype.card R = 3 := by
  have h := Fintype.card_congr order
  simpa using h.symm

theorem star_face_code (order : Fin 3 ≃ P ⊕ R) :
    SerialTangleFaceCode.encode (star order) = order.permCongr turn := by
  ext b
  have h := PermutationFirstReturnRestriction.nextHit_apply_of_step
    (openPhi (asOpen (star order))) SerialTangleFaceTransfer.Boundary
    ⟨.inr b, trivial⟩ (by trivial)
  change (SerialTangleFaceCode.boundaryCoordinate Empty (P ⊕ R))
    (GoertzelV24OrderedCutFaceReturnProfile.nextHitPerm (openPhi (asOpen (star order)))
      SerialTangleFaceTransfer.Boundary ⟨.inr b, trivial⟩) = _
  have hh := congrArg (Sum.elim (fun e : Empty => e.elim) id) h
  have hb (d : {d : Empty ⊕ (P ⊕ R) // SerialTangleFaceTransfer.Boundary d}) :
      SerialTangleFaceCode.boundaryCoordinate Empty (P ⊕ R) d =
        Sum.elim (fun e : Empty => e.elim) id d.1 := by
    rcases d with ⟨e | b, _⟩
    · exact e.elim
    · rfl
  rw [hb]
  exact hh

variable [Fintype I] [DecidableEq I]
  (A : TwoSidedOpenTangleData V I L P)

/-- Literal one-vertex growth. L remains untouched, P becomes internal,
and R consists of the newly exposed darts. -/
def append (order : Fin 3 ≃ P ⊕ R) := A.serialCompose (star order) (Equiv.refl P)

omit [Fintype R] [DecidableEq R] in
theorem cutSize_append (order : Fin 3 ≃ P ⊕ R) (s : V ⊕ Unit → Bool) :
    cutSize (sideMultigraph (asOpen (append A order))) s =
      cutSize (attach (sideMultigraph (asOpen A)) A.rightVert) s := by
  have hb := OpenTangleCutDartSum.twice_cutSize (asOpen (star order)) (s ∘ Sum.inr)
  simp only [Finset.univ_eq_empty, Finset.sum_empty] at hb
  have hb' : cutSize (sideMultigraph (asOpen (star order))) (s ∘ Sum.inr) = 0 := by omega
  have he : s = Sum.elim (s ∘ Sum.inl) (s ∘ Sum.inr) := by
    funext v; cases v <;> rfl
  rw [he, append, cutSize_serial, hb']
  rw [attach, cutSize_glue]
  simp [cutSize, vertex, star, OpenTangleCutDartSum.bit]

omit [Fintype R] [DecidableEq R] in
theorem reach_append (order : Fin 3 ≃ P ⊕ R) (u v : V ⊕ Unit) :
    (sideMultigraph (asOpen (append A order))).Reach u v ↔
      (attach (sideMultigraph (asOpen A)) A.rightVert).Reach u v := by
  rw [reach_iff_zero_cuts, reach_iff_zero_cuts]
  simp only [cutSize_append]

def componentEquiv (order : Fin 3 ≃ P ⊕ R) :
    Component (sideMultigraph (asOpen (append A order))) ≃
      Component (attach (sideMultigraph (asOpen A)) A.rightVert) :=
  Quotient.congrRight (reach_append A order)

variable [Fintype V]

omit [Fintype R] [DecidableEq R] in
theorem component_count_append (order : Fin 3 ≃ P ⊕ R) :
    Nat.card (Component (sideMultigraph (asOpen (append A order)))) +
        Nat.card (Quotient (portSetoid (profile (sideMultigraph (asOpen A)) A.rightVert))) =
      Nat.card (Component (sideMultigraph (asOpen A))) + 1 := by
  rw [Nat.card_congr (componentEquiv A order)]
  exact component_count_profile (sideMultigraph (asOpen A)) A.rightVert

variable [Fintype L] [DecidableEq L]

theorem joint_append (order : Fin 3 ≃ P ⊕ R) :
    SerialTangleJointTransfer.encode (append A order) =
      SerialTangleJointTransfer.transfer (SerialTangleJointTransfer.encode A)
        (SerialTangleJointTransfer.encode (star order)) :=
  SerialTangleJointTransfer.encode_serial A (star order)

/-- The boundary computation retains face cycles that close at this step. -/
def deltaFaces (order : Fin 3 ≃ P ⊕ R) : ℤ :=
  ((Equiv.Perm.partition (Equiv.sumCongr (SerialTangleFaceCode.encode A)
    (order.permCongr turn) * SerialTangleFaceCode.codeSwap)).parts.card : ℤ) -
    (Equiv.Perm.partition (SerialTangleFaceCode.encode A)).parts.card

omit [Fintype V] in
theorem face_change (order : Fin 3 ≃ P ⊕ R) :
    ((openPhi (asOpen (append A order))).partition.parts.card : ℤ) -
      (openPhi (asOpen A)).partition.parts.card = deltaFaces A order := by
  have hf := SerialTangleFaceTransfer.serial_face_count A (star order)
  have hin := card_permCongr_partition_parts
    (SerialTangleFaceCode.combinedCoordinate (I := I) (J := Empty))
    (SerialTangleFaceTransfer.combinedReturn A (star order))
  have hout := card_permCongr_partition_parts
    (SerialTangleFaceCode.combinedCoordinate (I := I) (J := Empty))
    (SerialTangleFaceTransfer.combinedReturn A (star order) *
      SerialTangleFaceTransfer.boundarySwap)
  rw [SerialTangleFaceCode.combined_code, star_face_code, cycle_count_sum,
    card_permCongr_partition_parts] at hin
  rw [SerialTangleFaceCode.rewired_code, star_face_code] at hout
  have ht : turn.partition.parts.card = 1 := by decide +kernel
  rw [star_faces] at hf
  unfold deltaFaces append
  omega

/-- Four times total genus when the vertex rotations present the actual
vertices. Kept as an integer Euler expression on unrestricted tangles. -/
def defect {B : Type*} [Fintype B] [DecidableEq B]
    (T : TwoSidedOpenTangleData V I L B) : ℤ :=
  4 * (Nat.card (Component (sideMultigraph (asOpen T))) : ℤ) - eulerMass (asOpen T)

/-- The tested vertex formula, derived on the literal constructor.
Its quotient counts consumed components, not consumed ports. -/
theorem defect_change (order : Fin 3 ≃ P ⊕ R) :
    defect (append A order) - defect A =
      2 * (1 + (Fintype.card P : ℤ) -
        2 * Nat.card (Quotient (portSetoid (profile (sideMultigraph (asOpen A)) A.rightVert))) -
        deltaFaces A order) := by
  have hc := component_count_append A order
  have hf := face_change A order
  dsimp only [append] at hc hf
  unfold defect eulerMass append
  simp only [Fintype.card_sum, Fintype.card_unit, Fintype.card_empty] at *
  omega

theorem defect_change_executable [DecidableEq V] (order : Fin 3 ≃ P ⊕ R) :
    defect (append A order) - defect A =
      2 * (1 + (Fintype.card P : ℤ) -
        2 * BoundaryComponentCount.count (BoundarySmallCutExecutable.extractTangle A)
          (Sum.inr : P → L ⊕ P) - deltaFaces A order) := by
  rw [BoundaryComponentCount.count_extractTangle]
  exact defect_change A order

end
end Mettapedia.GraphTheory.FourColor.VertexAttachmentTransfer
