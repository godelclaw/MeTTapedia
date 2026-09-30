import Mettapedia.GraphTheory.FourColor.PaddedCycleCapTangle
import Mettapedia.GraphTheory.FourColor.ZigzagRingGeometry

/-!
# Faces and ordered boundary return of padded cycle caps

The literal cap has one central face, three internal faces per sector,
and one outer face. Its boundary return retreats one port, exactly as for
the cycle that replaces it. Both facts refer to the original dart carrier.
-/

namespace Mettapedia.GraphTheory.FourColor.PaddedCycleCap

open GoertzelV24OpenTangleComposition OpenTangleMarkedFace
open SerialTangleSmallCutTransfer PermutationFirstReturnRestriction
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24OrderedCutFaceReturnProfile

noncomputable section
attribute [local instance] Classical.propDecidable

variable (m : ℕ) [NeZero m] (hm : 2 ≤ m)

noncomputable abbrev openCap := asOpen (tangle m hm)
noncomputable abbrev face := openPhi (openCap m hm)

def faceStep : Dart m → Dart m
  | .inl (i, (e, false)) =>
      ![.inl (i+1,(0,false)), .inl (i+1,(3,true)), .inl (i+1,(6,true)),
        .inl (i,(4,false)), .inl (i,(5,false)), .inl (i,(1,false)),
        .inl (i,(8,false)), .inl (i,(10,false)), .inl (i,(9,false)),
        .inl (i,(7,true)), .inl (i,(2,false))] e
  | .inl (i, (e, true)) =>
      ![.inl (i,(3,false)), .inl (i,(7,false)), .inr (.inr (i,true)),
        .inl (i-1,(0,true)), .inl (i-1,(1,true)), .inl (i,(6,false)),
        .inl (i,(4,true)), .inl (i,(5,true)), .inl (i-1,(2,true)),
        .inr (.inr (i,false)), .inl (i,(9,true))] e
  | .inr (.inl e) => nomatch e
  | .inr (.inr (i, false)) => .inl (i,(8,true))
  | .inr (.inr (i, true)) => .inl (i,(10,true))

theorem face_apply (d : Dart m) : face m hm d = faceStep m d := by
  rcases d with ⟨i,e,b⟩ | (e | ⟨i,b⟩)
  · fin_cases e <;> cases b <;>
      simp [face, openPhi, openCap, asOpen, tangle, rotation, coordinates,
        rotatePosition, position, star, alpha, flip, faceStep]
  · exact nomatch e
  · cases b <;>
      simp [face, openPhi, openCap, asOpen, tangle, rotation, coordinates,
        rotatePosition, position, star, alpha, faceStep]

abbrev FaceLabel := Bool ⊕ (Fin m × Fin 3)

def rootAt (i : Fin m) (s : Fin 5) : Dart m :=
  ![.inl (i,(0,false)), .inl (i,(2,true)), .inl (i,(0,true)),
    .inl (i,(1,true)), .inl (i,(5,true))] s

def rootLabel (i : Fin m) (s : Fin 5) : FaceLabel m :=
  ![.inl false, .inl true, .inr (i,0), .inr (i,1), .inr (i,2)] s

/-- A sector root and the bounded number of face steps from it. -/
def localRoot : Dart m → Fin m × (Fin 5 × ℕ)
  | .inl (i, (e, false)) =>
      (i, ![(0,0), (2,4), (3,3), (2,1), (2,2), (2,3),
        (4,1), (3,1), (4,2), (4,3), (3,2)] e)
  | .inl (i, (e, true)) =>
      (if e = 3 ∨ e = 4 ∨ e = 6 then i-1 else i,
        ![(2,0), (3,0), (1,0), (2,5), (3,5), (4,0),
          (3,4), (4,4), (1,5), (1,3), (1,2)] e)
  | .inr (.inl e) => nomatch e
  | .inr (.inr (i, false)) => (i,(1,4))
  | .inr (.inr (i, true)) => (i,(1,1))

def faceLabel (d : Dart m) : FaceLabel m :=
  rootLabel m (localRoot m d).1 (localRoot m d).2.1

theorem localRoot_spec (d : Dart m) :
    (face m hm ^ (localRoot m d).2.2)
      (rootAt m (localRoot m d).1 (localRoot m d).2.1) = d := by
  rcases d with ⟨i,e,b⟩ | (e | ⟨i,b⟩)
  · fin_cases e <;> cases b <;>
      simp [localRoot, rootAt, pow_succ', Equiv.Perm.mul_apply, face_apply, faceStep]
  · exact nomatch e
  · cases b <;>
      simp [localRoot, rootAt, pow_succ', Equiv.Perm.mul_apply, face_apply, faceStep]

theorem faceLabel_step (d : Dart m) :
    faceLabel m (face m hm d) = faceLabel m d := by
  rw [face_apply]
  rcases d with ⟨i,e,b⟩ | (e | ⟨i,b⟩)
  · fin_cases e <;> cases b <;> simp [faceStep, faceLabel, localRoot, rootLabel]
  · exact nomatch e
  · cases b <;> rfl

private theorem central_step (i : Fin m) :
    (face m hm).SameCycle (rootAt m i 0) (rootAt m (i+1) 0) := by
  refine ⟨(1 : ℕ), ?_⟩
  simp [face_apply, faceStep, rootAt]

private theorem outer_step (i : Fin m) :
    (face m hm).SameCycle (rootAt m i 1) (rootAt m (i+1) 1) := by
  apply Equiv.Perm.SameCycle.symm
  refine ⟨(6 : ℕ), ?_⟩
  simp [rootAt, pow_succ', Equiv.Perm.mul_apply, face_apply, faceStep]

private theorem global_root (s : Fin 5) (hs : s = 0 ∨ s = 1) (i : Fin m) :
    (face m hm).SameCycle (rootAt m 0 s) (rootAt m i s) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  induction i using Fin.induction with
  | zero => exact Equiv.Perm.SameCycle.refl _ _
  | succ i ih =>
    have he : i.castSucc + 1 = i.succ := by apply Fin.ext; simp [Fin.add_def]
    apply ih.trans
    rw [← he]
    rcases hs with rfl | rfl
    · exact central_step _ hm _
    · exact outer_step _ hm _

def faceRoot : FaceLabel m → Dart m
  | .inl false => rootAt m 0 0
  | .inl true => rootAt m 0 1
  | .inr (i,s) => ![rootAt m i 2, rootAt m i 3, rootAt m i 4] s

theorem faceRoot_label (l : FaceLabel m) : faceLabel m (faceRoot m l) = l := by
  rcases l with (_ | _) | ⟨i,s⟩
  · rfl
  · rfl
  · fin_cases s <;> simp [faceRoot, faceLabel, localRoot, rootAt, rootLabel]

private theorem faceRoot_sameCycle (d : Dart m) :
    (face m hm).SameCycle (faceRoot m (faceLabel m d)) d := by
  have h : (face m hm).SameCycle
      (rootAt m (localRoot m d).1 (localRoot m d).2.1) d :=
    ⟨((localRoot m d).2.2 : ℕ), by rw [zpow_natCast]; exact localRoot_spec m hm d⟩
  apply Equiv.Perm.SameCycle.trans _ h
  generalize hi : (localRoot m d).1 = i
  generalize hs : (localRoot m d).2.1 = s
  change (face m hm).SameCycle (faceRoot m (rootLabel m _ _)) _
  rw [hi, hs]
  fin_cases s
  · exact global_root m hm 0 (Or.inl rfl) i
  · exact global_root m hm 1 (Or.inr rfl) i
  · exact Equiv.Perm.SameCycle.refl _ _
  · exact Equiv.Perm.SameCycle.refl _ _
  · exact Equiv.Perm.SameCycle.refl _ _

theorem face_sameCycle_iff (d e : Dart m) :
    (face m hm).SameCycle d e ↔ faceLabel m d = faceLabel m e := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply, faceLabel_step] using ih
  · intro h
    have hd := faceRoot_sameCycle m hm d
    rw [h] at hd
    exact hd.symm.trans (faceRoot_sameCycle m hm e)

theorem face_count : (face m hm).partition.parts.card = 3*m+2 := by
  rw [← GoertzelV24FaceOrbitPartitionBridge.card_permOrbit_eq_card_partition_parts]
  change orbitCount (face m hm) = _
  have h := OrbitCountSplitting.orbitCount_eq_card_of_completeInvariant
    (faceLabel m) (face_sameCycle_iff m hm)
    (fun l => ⟨faceRoot m l, faceRoot_label m l⟩)
  simpa [FaceLabel, Fintype.card_sum, Fintype.card_prod, Nat.mul_comm, Nat.add_comm] using h

theorem eulerMass : OpenTangleReplacementEuler.eulerMass (openCap m hm) = 4 := by
  unfold OpenTangleReplacementEuler.eulerMass
  rw [show (openPhi (openCap m hm)).partition.parts.card = 3*m+2 from face_count m hm]
  simp [Vertex, Interior, Fintype.card_prod]
  ring

def boundaryNext : Empty ⊕ Boundary m → Empty ⊕ Boundary m
  | .inl e => nomatch e
  | .inr (i,false) => .inr (i-1,true)
  | .inr (i,true) => .inr (i,false)

def boundaryPerm : Equiv.Perm (Empty ⊕ Boundary m) where
  toFun := boundaryNext m
  invFun
    | .inl e => nomatch e
    | .inr (i,false) => .inr (i,true)
    | .inr (i,true) => .inr (i+1,false)
  left_inv := by rintro (e | ⟨i,_ | _⟩) <;> first | exact nomatch e | simp [boundaryNext]
  right_inv := by rintro (e | ⟨i,_ | _⟩) <;> first | exact nomatch e | simp [boundaryNext]

theorem boundary_first_return (b : Empty ⊕ Boundary m) :
    nextHitPerm (face m hm) SerialTangleFaceTransfer.Boundary ⟨.inr b, trivial⟩ =
      ⟨.inr (boundaryNext m b), trivial⟩ := by
  apply nextHit_eq_of_returnArc
  refine ⟨show 0 < 3 by decide, ?_, ?_⟩
  · rcases b with e | ⟨i,b⟩
    · exact nomatch e
    · cases b <;> simp [pow_succ', Equiv.Perm.mul_apply, face_apply, faceStep, boundaryNext]
  · intro n hn hlt
    have h : n = 1 ∨ n = 2 := by omega
    rcases h with rfl | rfl <;> rcases b with e | ⟨i,b⟩ <;>
      first | exact nomatch e | cases b <;>
        simp [pow_succ', Equiv.Perm.mul_apply, face_apply, faceStep,
          SerialTangleFaceTransfer.Boundary]

theorem encode_cap : SerialTangleFaceCode.encode (tangle m hm) = boundaryPerm m := by
  ext b
  change SerialTangleFaceCode.boundaryCoordinate (Interior m) _
    (nextHitPerm (face m hm) SerialTangleFaceTransfer.Boundary ⟨.inr b, trivial⟩) = _
  rw [boundary_first_return]
  rfl

end
end Mettapedia.GraphTheory.FourColor.PaddedCycleCap
