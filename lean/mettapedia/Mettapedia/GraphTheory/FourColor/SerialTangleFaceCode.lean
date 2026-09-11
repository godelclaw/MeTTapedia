import Mettapedia.GraphTheory.FourColor.SerialTangleFaceTransfer

/-!
# Boundary-only face transfer

The serial face update lives on `(L + P) + (P + R)`, independently of
the interior dart carriers. This identifies the finite port operation
with the literal constructor, retaining the complete cyclic order.
-/

namespace Mettapedia.GraphTheory.FourColor.SerialTangleFaceCode

open Equiv Equiv.Perm
open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24OrderedCutFaceReturnProfile
open SerialTangleSmallCutTransfer OpenTangleMarkedFace SerialTangleFaceTransfer
open PermutationFirstReturnRestriction

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V W I J L P R : Type*}

def boundaryCoordinate (I B : Type*) : {d : I ⊕ B // Boundary d} ≃ B where
  toFun
    | ⟨.inl _, h⟩ => False.elim h
    | ⟨.inr b, _⟩ => b
  invFun b := ⟨.inr b, trivial⟩
  left_inv := by rintro ⟨i | b, h⟩; exact False.elim h; rfl
  right_inv _ := rfl

def combinedCoordinate : {d : Source I J L P R // AllBoundary d} ≃
    (L ⊕ P) ⊕ (P ⊕ R) :=
  Equiv.subtypeSum.trans (Equiv.sumCongr (boundaryCoordinate I _) (boundaryCoordinate J _))

def ExternalCode : (L ⊕ P) ⊕ (P ⊕ R) → Prop
  | .inl (.inl _) => True
  | .inr (.inr _) => True
  | _ => False

def externalCoordinate : {d : Source I J L P R // External d} ≃ L ⊕ R where
  toFun
    | ⟨.inl (.inr (.inl l)), _⟩ => .inl l
    | ⟨.inr (.inr (.inr r)), _⟩ => .inr r
    | ⟨.inl (.inl _), h⟩ => False.elim h
    | ⟨.inl (.inr (.inr _)), h⟩ => False.elim h
    | ⟨.inr (.inl _), h⟩ => False.elim h
    | ⟨.inr (.inr (.inl _)), h⟩ => False.elim h
  invFun
    | .inl l => ⟨.inl (.inr (.inl l)), trivial⟩
    | .inr r => ⟨.inr (.inr (.inr r)), trivial⟩
  left_inv := by
    rintro ⟨(i | (l | p)) | (j | (p | r)), h⟩ <;> try exact False.elim h
    all_goals rfl
  right_inv := by rintro (l | r) <;> rfl

def codeExternalCoordinate : {d : (L ⊕ P) ⊕ (P ⊕ R) // ExternalCode d} ≃ L ⊕ R where
  toFun
    | ⟨.inl (.inl l), _⟩ => .inl l
    | ⟨.inr (.inr r), _⟩ => .inr r
    | ⟨.inl (.inr _), h⟩ => False.elim h
    | ⟨.inr (.inl _), h⟩ => False.elim h
  invFun
    | .inl l => ⟨.inl (.inl l), trivial⟩
    | .inr r => ⟨.inr (.inr r), trivial⟩
  left_inv := by
    rintro ⟨(l | p) | (p | r), h⟩ <;> try exact False.elim h
    all_goals rfl
  right_inv := by rintro (l | r) <;> rfl

def codeSwap : Perm ((L ⊕ P) ⊕ (P ⊕ R)) where
  toFun
    | .inl (.inr p) => .inr (.inl p)
    | .inr (.inl p) => .inl (.inr p)
    | d => d
  invFun
    | .inl (.inr p) => .inr (.inl p)
    | .inr (.inl p) => .inl (.inr p)
    | d => d
  left_inv := by rintro ((l | p) | (p | r)) <;> rfl
  right_inv := by rintro ((l | p) | (p | r)) <;> rfl

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]
  [Fintype R] [DecidableEq R]

def encode (T : TwoSidedOpenTangleData V I L R) : Perm (L ⊕ R) :=
  (boundaryCoordinate I _).permCongr (nextHitPerm (openPhi (asOpen T)) Boundary)

def transfer (a : Perm (L ⊕ P)) (b : Perm (P ⊕ R)) : Perm (L ⊕ R) :=
  codeExternalCoordinate.permCongr
    (nextHitPerm (Equiv.sumCongr a b * codeSwap) ExternalCode)

variable (A : TwoSidedOpenTangleData V I L P) (B : TwoSidedOpenTangleData W J P R)

theorem combined_apply (d : {d : Source I J L P R // AllBoundary d}) :
    combinedCoordinate (combinedReturn A B d) =
      Equiv.sumCongr (encode A) (encode B) (combinedCoordinate d) := by
  rw [combinedReturn_eq]
  rcases d with ⟨(i | b) | (j | c), h⟩
  all_goals try exact False.elim h
  all_goals rfl

theorem combined_code : combinedCoordinate.permCongr (combinedReturn A B) =
    Equiv.sumCongr (encode A) (encode B) := by
  ext d
  obtain ⟨x, rfl⟩ := (combinedCoordinate (I := I) (J := J)).surjective d
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using combined_apply A B x

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]
  [Fintype R] [DecidableEq R] in
theorem swap_apply (d : {d : Source I J L P R // AllBoundary d}) :
    combinedCoordinate (boundarySwap d) = codeSwap (combinedCoordinate d) := by
  rcases d with ⟨(i | (l | p)) | (j | (p | r)), h⟩ <;> try exact False.elim h
  all_goals rfl

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]
  [Fintype R] [DecidableEq R] in
theorem external_iff (d : {d : Source I J L P R // AllBoundary d}) :
    ExternalCode (combinedCoordinate d) ↔ External d.1 := by
  rcases d with ⟨(i | (l | p)) | (j | (p | r)), h⟩ <;> try exact False.elim h
  all_goals rfl

theorem rewired_code : combinedCoordinate.permCongr (combinedReturn A B * boundarySwap) =
    Equiv.sumCongr (encode A) (encode B) * codeSwap := by
  rw [Equiv.permCongr_mul, combined_code]
  congr 1
  ext d
  obtain ⟨x, rfl⟩ := (combinedCoordinate (I := I) (J := J)).surjective d
  simpa only [Equiv.permCongr_apply, Equiv.symm_apply_apply] using swap_apply x

omit [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype P] [DecidableEq P]
  [Fintype R] [DecidableEq R] in
theorem external_to_code (d : {d : Source I J L P R // External d}) :
    (codeExternalCoordinate (P := P)).symm (externalCoordinate d) =
      ⟨combinedCoordinate ⟨d.1, external_boundary _ d.2⟩,
        (external_iff _).2 d.2⟩ := by
  rcases d with ⟨(i | (l | p)) | (j | (p | r)), he⟩ <;> try exact False.elim he
  all_goals rfl

theorem transfer_apply (d : {d : Source I J L P R // External d}) :
    transfer (encode A) (encode B) (externalCoordinate d) =
      externalCoordinate (outputReturn A B d) := by
  let x := nestedMarks External AllBoundary external_boundary d
  have h := PermutationFirstReturnRestriction.nextHit_map
    (combinedReturn A B * boundarySwap)
    (Equiv.sumCongr (encode A) (encode B) * codeSwap)
    combinedCoordinate
    (by intro y; simp only [Perm.mul_apply, combined_apply, swap_apply])
    (fun d => External d.1) ExternalCode external_iff x
  apply (codeExternalCoordinate (P := P)).symm.injective
  simp only [transfer, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  rw [external_to_code, external_to_code]
  apply Subtype.ext
  exact h

/-- Entire outgoing cyclic order of the actual serial composite. -/
theorem encode_serial : encode (A.serialCompose B (Equiv.refl P)) = transfer (encode A) (encode B) := by
  apply Equiv.ext
  intro z
  obtain ⟨d, rfl⟩ := (externalCoordinate (I := I) (J := J) (P := P)).surjective z
  rw [transfer_apply]
  have h := serial_return A B d
  let y := outputReturn A B d
  have hs :
      nextHitPerm (openPhi (asOpen (A.serialCompose B (Equiv.refl P)))) Boundary
        ((boundaryCoordinate _ _).symm (externalCoordinate d)) =
      (boundaryCoordinate _ _).symm (externalCoordinate y) := by
    apply Subtype.ext
    convert h using 1
    · rcases d with ⟨(i | (l | p)) | (j | (p | r)), he⟩ <;> try exact False.elim he
      all_goals rfl
    · change (Sum.inr (externalCoordinate y) : ((I ⊕ J) ⊕ (P ⊕ P)) ⊕ (L ⊕ R)) =
        serialDartEquiv y.1
      rcases y with ⟨(i | (l | p)) | (j | (p | r)), he⟩ <;> try exact False.elim he
      all_goals rfl
  exact congrArg (boundaryCoordinate _ _) hs

end
end Mettapedia.GraphTheory.FourColor.SerialTangleFaceCode
