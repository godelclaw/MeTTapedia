import Mettapedia.GraphTheory.FourColor.CycleCapTangle
import Mettapedia.GraphTheory.FourColor.ZigzagTubeStructural
import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamCubic

/-! # Geometry of a cycle with outward ports

The literal cycle is connected and bridgeless, has cubic vertex fibres,
and has two open faces. The outer face returns to the preceding port.
-/

namespace Mettapedia.GraphTheory.FourColor.CycleCap

open GoertzelV24OpenTangleComposition OpenTangleMarkedFace
open SerialTangleSmallCutTransfer GoertzelV24CompositeSeamCubic
open GoertzelV24OrderedCutFaceReturnProfile PermutationFirstReturnRestriction
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24BoundaryEssentialGluing Multigraph BoundarySmallCutProfile
open SmallCutConnectedBridgeless SmallCutReplacementCore OpenTangleCutDartSum
open GoertzelV24CompositeSeamMultigraph

noncomputable section
attribute [local instance] Classical.propDecidable

variable (k : ℕ) [NeZero k] (hk : 2 ≤ k)

noncomputable abbrev openCap := asOpen (cap k hk)
noncomputable abbrev face := openPhi (openCap k hk)

def faceStep : AllDart k → AllDart k
  | .inl (i,false) => .inr (.inr (i-1))
  | .inl (i,true) => .inl (i+1,true)
  | .inr (.inl e) => nomatch e
  | .inr (.inr i) => .inl (i,false)

theorem face_apply (d : AllDart k) : face k hk d = faceStep k d := by
  rcases d with ⟨i,_ | _⟩ | (e | i) <;> first | exact nomatch e |
    simp [face, openPhi, openCap, asOpen, cap, rho, rhoFun, interiorAlpha, flip, faceStep]

def faceSide : AllDart k → Bool
  | .inl (_,b) => b
  | .inr _ => false

def faceRootAt (b : Bool) (i : Fin k) : AllDart k := .inl (i,b)

private theorem face_root_step (b : Bool) (i : Fin k) :
    (face k hk).SameCycle (faceRootAt k b i) (faceRootAt k b (i+1)) := by
  cases b
  · apply Equiv.Perm.SameCycle.symm
    refine ⟨(2 : ℕ), ?_⟩
    simp [faceRootAt, pow_succ', Equiv.Perm.mul_apply, face_apply, faceStep]
  · refine ⟨(1 : ℕ), ?_⟩
    simp [faceRootAt, face_apply, faceStep]

private theorem face_root (b : Bool) (i : Fin k) :
    (face k hk).SameCycle (faceRootAt k b 0) (faceRootAt k b i) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  induction i using Fin.induction with
  | zero => exact .rfl
  | succ i ih =>
    have he : i.castSucc + 1 = i.succ := by apply Fin.ext; simp [Fin.add_def]
    exact ih.trans (he ▸ face_root_step _ hk b i.castSucc)

private theorem face_root_dart (d : AllDart k) :
    (face k hk).SameCycle (faceRootAt k (faceSide k d) 0) d := by
  rcases d with ⟨i,b⟩ | (e | i)
  · exact face_root k hk b i
  · exact nomatch e
  · have h := face_root k hk false (i+1)
    simpa [faceRootAt, faceSide, face_apply, faceStep] using h.apply_right

theorem faceSide_step (d : AllDart k) : faceSide k (face k hk d) = faceSide k d := by
  rw [face_apply]
  rcases d with ⟨i,_ | _⟩ | (e | i) <;> first | exact nomatch e | rfl

theorem face_sameCycle_iff (d e : AllDart k) :
    (face k hk).SameCycle d e ↔ faceSide k d = faceSide k e := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply, faceSide_step] using ih
  · intro h
    have hd := face_root_dart k hk d
    rw [h] at hd
    exact hd.symm.trans (face_root_dart k hk e)

theorem face_count : (face k hk).partition.parts.card = 2 := by
  rw [← GoertzelV24FaceOrbitPartitionBridge.card_permOrbit_eq_card_partition_parts]
  change orbitCount (face k hk) = 2
  simpa using OrbitCountSplitting.orbitCount_eq_card_of_completeInvariant
    (faceSide k) (face_sameCycle_iff k hk) (fun b => ⟨faceRootAt k b 0, rfl⟩)

theorem eulerMass : OpenTangleReplacementEuler.eulerMass (openCap k hk) = 4 := by
  unfold OpenTangleReplacementEuler.eulerMass
  rw [show (openPhi (openCap k hk)).partition.parts.card = 2 from face_count k hk]
  simp [Dart, Fintype.card_prod]
  ring

def boundaryPerm : Equiv.Perm (Empty ⊕ Fin k) :=
  Equiv.sumCongr (Equiv.refl Empty) (Equiv.subRight 1)

theorem boundary_first_return (b : Empty ⊕ Fin k) :
    nextHitPerm (face k hk) SerialTangleFaceTransfer.Boundary ⟨.inr b,trivial⟩ =
      ⟨.inr (boundaryPerm k b),trivial⟩ := by
  apply nextHit_eq_of_returnArc
  refine ⟨show 0 < 2 by decide, ?_, ?_⟩
  · rcases b with e | i
    · exact nomatch e
    · simp [pow_succ', Equiv.Perm.mul_apply, face_apply, faceStep, boundaryPerm]
  · intro n hn hlt
    have : n = 1 := by omega
    subst n
    rcases b with e | i
    · exact nomatch e
    · simp [face_apply, faceStep, SerialTangleFaceTransfer.Boundary]

theorem encode_cap : SerialTangleFaceCode.encode (cap k hk) = boundaryPerm k := by
  ext b
  change SerialTangleFaceCode.boundaryCoordinate (Dart k) _
    (nextHitPerm (face k hk) SerialTangleFaceTransfer.Boundary ⟨.inr b,trivial⟩) = _
  rw [boundary_first_return]
  rfl

theorem cap_dartsAt (i : Fin k) : openDartsAt (openCap k hk) i =
    {.inr (.inr i), .inl (i,false), .inl (i+1,true)} := by
  ext d
  rcases d with ⟨j,_ | _⟩ | (e | j) <;> first | exact nomatch e |
    simp [openDartsAt, openCap, asOpen_vertOf, TwoSidedOpenTangleData.vertOf,
      cap, twoSidedOpenTangleVertOf, interiorVert, sub_eq_iff_eq_add]

theorem cap_isCubic : OpenIsCubic (openCap k hk) := by
  intro i
  rw [cap_dartsAt]
  simp

private theorem cap_sameCycle_port (d : AllDart k) :
    (rho k).SameCycle (.inr (.inr ((cap k hk).vertOf d))) d := by
  rcases d with ⟨i,_ | _⟩ | (e | i)
  · exact (Equiv.Perm.SameCycle.refl (rho k) (.inr (.inr i))).apply_right
  · simpa [rho, rhoFun, TwoSidedOpenTangleData.vertOf, cap,
      twoSidedOpenTangleVertOf, interiorVert] using
      (Equiv.Perm.SameCycle.refl (rho k) (.inr (.inr (i-1)))).apply_right.apply_right
  · exact nomatch e
  · exact .rfl

theorem cap_rotationCyclic : OpenRotationCyclic (openCap k hk) := by
  intro d e hv
  change (rho k).SameCycle d e
  have h := cap_sameCycle_port k hk d
  simp only [openCap, asOpen_vertOf] at hv
  rw [hv] at h
  exact h.symm.trans (cap_sameCycle_port k hk e)

theorem cap_cutSize (s : Fin k → Bool) :
    cutSize (sideMultigraph (openCap k hk)) s =
      cutSize (permutationGraph (Equiv.subRight 1)) s := by
  have h := twice_cutSize (openCap k hk) s
  conv at h =>
    rhs
    simp only [Dart, Fintype.sum_prod_type, Fintype.sum_bool,
      openCap, asOpen, cap, interiorAlpha, Equiv.coe_fn_mk, flip, interiorVert,
      Bool.not_true, Bool.not_false]
  have he (i : Fin k) : bit (s (i-1)) (s i) = bit (s i) (s (i-1)) := bit_symm _ _
  simp only [he, Finset.sum_add_distrib] at h
  have hp : cutSize (permutationGraph (Equiv.subRight (1 : Fin k))) s =
      ∑ i : Fin k, bit (s i) (s (i-1)) := by
    simp [cutSize, permutationGraph, bit]
  omega

theorem cap_connected_bridgeless :
    (sideMultigraph (openCap k hk)).Connected ∧
      (sideMultigraph (openCap k hk)).Bridgeless := by
  apply (no_small_cut_iff _).mp
  rintro ⟨s, ⟨u,hu⟩, ⟨v,hv⟩, hs⟩
  rw [cap_cutSize] at hs
  have hedge := permutation_small_cut (Equiv.subRight (1 : Fin k)) s hs
  have hroot (i : Fin k) : s i = s 0 := by
    obtain ⟨n,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih =>
      have he : i.castSucc + 1 = i.succ := by apply Fin.ext; simp [Fin.add_def]
      have h : s (i.castSucc+1) = s i.castSucc := by
        have hh := hedge (i.castSucc+1)
        change s (i.castSucc+1) = s ((i.castSucc+1)-1) at hh
        simpa only [add_sub_cancel_right] using hh
      rw [he] at h
      exact h.trans ih
  have h := (hroot u).trans (hroot v).symm
  simp only [hu, hv, Bool.true_eq_false] at h

end
end Mettapedia.GraphTheory.FourColor.CycleCap
