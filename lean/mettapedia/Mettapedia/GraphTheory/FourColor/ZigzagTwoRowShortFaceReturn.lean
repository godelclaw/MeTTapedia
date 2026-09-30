import Mettapedia.GraphTheory.FourColor.ZigzagTwoRowWiringFaces
import Mettapedia.GraphTheory.FourColor.GoertzelV24HexFaceRungType

/-!
# Short end faces determine the two-row exterior return

Three steps of each end face lie in the literal rows. If the whole face
has five or six steps, the remaining two or three steps give the opposite
exterior boundary return. An earlier boundary hit would enter another row
arc and cannot fit in that face. The calculation uses actual closed darts.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing.ShiftedWiring.Geometry

open Equiv Equiv.Perm GoertzelV24OpenTangleComposition
open OpenTangleMarkedFace SerialTangleFaceTransfer SerialTangleFaceCode
open GoertzelV24OrderedCutFaceReturnProfile PermutationFirstReturnRestriction
open GoertzelV24CompositeSeamCubic
open OpenTanglePortReplacement GoertzelV24HexFaceRungType

noncomputable section
attribute [local instance] Classical.propDecidable tubeVertexFintype tubeInteriorFintype
set_option backward.isDefEq.respectTransparency false

variable (k : ℕ) [NeZero k]
variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]
  (O : OpenTangleData V I (Fin k ⊕ Fin k))

def oldExterior (d : I ⊕ (Fin k ⊕ Fin k)) : (original k O).D :=
  composeDartEquiv (.inl d)

def oldTube (d : (tube k 1).I ⊕ (Fin k ⊕ Fin k)) : (original k O).D :=
  composeDartEquiv (.inr d)

theorem oldExterior_ne_oldTube (d e) : oldExterior k O d ≠ oldTube k O e := by
  intro h
  cases composeDartEquiv.injective h

theorem phi_oldExterior_interior (i : I) :
    (original k O).phi (oldExterior k O (.inl i)) =
      oldExterior k O (openPhi O (.inl i)) := rfl

theorem phi_oldTube_boundary (b : Fin k ⊕ Fin k) :
    (original k O).phi (oldTube k O (.inr b)) =
      oldExterior k O (openPhi O (.inr b)) := rfl

theorem phi_oldExterior_boundary (b : Fin k ⊕ Fin k) :
    ∃ i : (tube k 1).I, (original k O).phi (oldExterior k O (.inr b)) =
      oldTube k O (.inl i) := by
  rcases b with i | i
  · exact ⟨.inl (.inl (.inl (i, false))), rfl⟩
  · exact ⟨.inl (.inr (.inl (i, true))), rfl⟩

theorem phi_sq_oldExterior_boundary (b : Fin k ⊕ Fin k) :
    ∃ i : (tube k 1).I, ((original k O).phi ^ 2) (oldExterior k O (.inr b)) =
      oldTube k O (.inl i) := by
  rcases b with i | i
  · exact ⟨.inl (.inl (.inr (i, false))), rfl⟩
  · exact ⟨.inl (.inr (.inr (i - 1, true))), rfl⟩

theorem phi_cube_oldExterior_boundary (b : Fin k ⊕ Fin k) :
    ((original k O).phi ^ 3) (oldExterior k O (.inr b)) =
      oldTube k O (.inr (boundaryPerm k b)) := by
  rcases b with i | i <;> rfl

private theorem exterior_two_arc (b c : Fin k ⊕ Fin k)
    (h : ((original k O).phi ^ 2) (oldTube k O (.inr b)) =
      oldExterior k O (.inr c)) :
    ReturnArc (openPhi O) Boundary (.inr b) (.inr c) 2 := by
  have h' : (original k O).phi (oldExterior k O (openPhi O (.inr b))) =
      oldExterior k O (.inr c) := by
    simpa only [pow_succ', pow_zero, Perm.mul_apply, Perm.one_apply,
      phi_oldTube_boundary] using h
  generalize hd : openPhi O (.inr b) = d at h'
  cases d with
  | inl i =>
    rw [phi_oldExterior_interior] at h'
    have he := Sum.inl.inj (composeDartEquiv.injective h')
    refine ⟨by omega, ?_, ?_⟩
    · simpa only [pow_succ', pow_zero, Perm.mul_apply, Perm.one_apply, hd] using he
    · intro n hn hlt
      obtain rfl : n = 1 := by omega
      simp only [pow_one, hd, Boundary]
      exact id
  | inr p =>
    obtain ⟨i, hi⟩ := phi_oldExterior_boundary k O p
    exact (oldExterior_ne_oldTube k O (.inr c) (.inl i) (h'.symm.trans hi)).elim

private theorem exterior_three_arc (b c : Fin k ⊕ Fin k)
    (h : ((original k O).phi ^ 3) (oldTube k O (.inr b)) =
      oldExterior k O (.inr c)) :
    ReturnArc (openPhi O) Boundary (.inr b) (.inr c) 3 := by
  have h' : ((original k O).phi ^ 2) (oldExterior k O (openPhi O (.inr b))) =
      oldExterior k O (.inr c) := by
    simpa only [pow_succ, pow_one, Perm.mul_apply, phi_oldTube_boundary] using h
  generalize hd : openPhi O (.inr b) = d at h'
  cases d with
  | inr p =>
    obtain ⟨i, hi⟩ := phi_sq_oldExterior_boundary k O p
    exact (oldExterior_ne_oldTube k O (.inr c) (.inl i) (h'.symm.trans hi)).elim
  | inl i =>
    have hh : (original k O).phi (oldExterior k O (openPhi O (.inl i))) =
        oldExterior k O (.inr c) := by
      simpa only [pow_succ', pow_zero, Perm.mul_apply, Perm.one_apply,
        phi_oldExterior_interior] using h'
    generalize he : openPhi O (.inl i) = e at hh
    cases e with
    | inr p =>
      obtain ⟨j, hj⟩ := phi_oldExterior_boundary k O p
      exact (oldExterior_ne_oldTube k O (.inr c) (.inl j) (hh.symm.trans hj)).elim
    | inl j =>
      rw [phi_oldExterior_interior] at hh
      have hend := Sum.inl.inj (composeDartEquiv.injective hh)
      refine ⟨by omega, ?_, ?_⟩
      · simpa only [pow_succ', pow_zero, Perm.mul_apply, Perm.one_apply, hd, he] using hend
      · intro n hn hlt
        have hn' : n = 1 ∨ n = 2 := by omega
        rcases hn' with rfl | rfl <;>
          simp only [pow_succ', pow_zero, Perm.mul_apply, Perm.one_apply, hd, he, Boundary] <;>
          exact id

/-- Only the actual end-face sizes are supplied. The opposite return is
derived, not an independently assumed exterior summary. -/
theorem returnCode_of_short_end_faces
    (short : ∀ b, ((original k O).faceOrbit (oldExterior k O (.inr b))).card = 5 ∨
      ((original k O).faceOrbit (oldExterior k O (.inr b))).card = 6) :
    returnCode O = (boundaryPerm k)⁻¹ := by
  ext b
  let c := (boundaryPerm k).symm b
  have ht : ((original k O).phi ^ 3) (oldExterior k O (.inr c)) =
      oldTube k O (.inr b) := by
    simpa only [c, Equiv.apply_symm_apply] using phi_cube_oldExterior_boundary k O c
  have hp := (faceOrbit_isCycleOn (original k O) (oldExterior k O (.inr c))).pow_card_apply
    ((original k O).mem_faceOrbit_self _)
  have harc : ∃ n, ReturnArc (openPhi O) Boundary (.inr b) (.inr c) n := by
    rcases short c with hs | hs
    · rw [hs] at hp
      have hr : ((original k O).phi ^ 2) (oldTube k O (.inr b)) =
          oldExterior k O (.inr c) := by
        rw [← ht, ← Perm.mul_apply, ← pow_add]
        exact hp
      exact ⟨2, exterior_two_arc k O b c hr⟩
    · rw [hs] at hp
      have hr : ((original k O).phi ^ 3) (oldTube k O (.inr b)) =
          oldExterior k O (.inr c) := by
        rw [← ht, ← Perm.mul_apply, ← pow_add]
        exact hp
      exact ⟨3, exterior_three_arc k O b c hr⟩
  obtain ⟨n, hn⟩ := harc
  have hr := nextHit_eq_of_returnArc (openPhi O) Boundary
    ⟨.inr b, trivial⟩ ⟨.inr c, trivial⟩ hn
  exact congrArg (boundaryCoordinate I (Fin k ⊕ Fin k)) hr

end
end Mettapedia.GraphTheory.FourColor.ZigzagRing.ShiftedWiring.Geometry
