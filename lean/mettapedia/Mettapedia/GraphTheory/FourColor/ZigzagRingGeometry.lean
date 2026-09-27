import Mettapedia.GraphTheory.FourColor.ZigzagRingTangle
import Mettapedia.GraphTheory.FourColor.ZigzagTubeCompression
import Mettapedia.GraphTheory.FourColor.OpenTangleBoundaryView
import Mettapedia.GraphTheory.FourColor.SerialTangleJointTransfer
import Mettapedia.GraphTheory.FourColor.PermutationFirstReturnRestriction
import Mettapedia.GraphTheory.OrbitCountSplitting

/-!
# The two oriented faces of a literal zigzag ring

The open face permutation has exactly two cycles. First return to the
boundary advances input ports and retreats output ports. These statements
refer to the same dart and rotation data as the colouring semantics.
-/

namespace Mettapedia.GraphTheory.FourColor.ZigzagRing

open GoertzelV24OpenTangleComposition OpenTangleMarkedFace
open GoertzelV24OrderedCutFaceReturnProfile PermutationFirstReturnRestriction
open GoertzelV24PermutationOrbitSurgery SerialTangleSmallCutTransfer

noncomputable section
attribute [local instance] Classical.propDecidable

variable (k : Nat) [NeZero k]

noncomputable abbrev openRing := asOpen (ring k)

noncomputable abbrev face := openPhi (openRing k)

def port (b : Bool) (i : Fin k) : AllDart k :=
  if b then .inr (.inr i) else .inr (.inl i)

/-- The two boundary components have opposite induced directions. -/
def boundaryNext : Fin k ⊕ Fin k → Fin k ⊕ Fin k
  | .inl i => .inl (i + 1)
  | .inr i => .inr (i - 1)

def boundaryPerm : Equiv.Perm (Fin k ⊕ Fin k) where
  toFun := boundaryNext k
  invFun
    | .inl i => .inl (i - 1)
    | .inr i => .inr (i + 1)
  left_inv := by rintro (i | i) <;> simp [boundaryNext]
  right_inv := by rintro (i | i) <;> simp [boundaryNext]

theorem face_cubed_boundary (b : Fin k ⊕ Fin k) :
    (face k ^ 3) (.inr b) = .inr (boundaryNext k b) := by
  rcases b with i | i <;>
    simp [face, openPhi, openRing, asOpen, ring,
      rho, rhoFun, interiorAlpha, flip, boundaryNext, pow_succ, Equiv.Perm.mul_apply]

/-- The boundary return is exactly three face steps, with no intervening port. -/
theorem boundary_first_return (b : Fin k ⊕ Fin k) :
    nextHitPerm (face k) (SerialTangleFaceTransfer.Boundary) ⟨.inr b, trivial⟩ =
      ⟨.inr (boundaryNext k b), trivial⟩ := by
  apply nextHit_eq_of_returnArc
  refine ⟨by decide, face_cubed_boundary k b, ?_⟩
  intro n hn hlt
  have h : n = 1 ∨ n = 2 := by omega
  rcases h with rfl | rfl <;> rcases b with i | i <;>
    simp [face, openPhi, openRing, asOpen, ring,
      rho, rhoFun, interiorAlpha, flip, SerialTangleFaceTransfer.Boundary, pow_succ, Equiv.Perm.mul_apply]

/-- A label for the two face cycles, not a quotient of the dart carrier. -/
def faceSide : AllDart k → Bool
  | .inl (.inl (_, b)) => b
  | .inl (.inr (_, b)) => b
  | .inr (.inl _) => false
  | .inr (.inr _) => true

theorem faceSide_step (d : AllDart k) : faceSide k (face k d) = faceSide k d := by
  rcases d with (⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i) <;>
    simp [face, openPhi, openRing, asOpen, ring,
      rho, rhoFun, interiorAlpha, flip, faceSide]

private theorem face_ports_step (b : Bool) (i : Fin k) :
    (face k).SameCycle (port k b i) (port k b (i + 1)) := by
  cases b
  · exact ⟨(3 : Nat), by
      rw [zpow_natCast]
      exact face_cubed_boundary k (.inl i)⟩
  · apply Equiv.Perm.SameCycle.symm
    refine ⟨(3 : Nat), ?_⟩
    rw [zpow_natCast]
    simpa [port, boundaryNext] using face_cubed_boundary k (.inr (i + 1))

private theorem face_ports_root (b : Bool) (i : Fin k) :
    (face k).SameCycle (port k b 0) (port k b i) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  induction i using Fin.induction with
  | zero => exact Equiv.Perm.SameCycle.refl _ _
  | succ i ih =>
    have he : i.castSucc + 1 = i.succ := by
      apply Fin.ext
      simp [Fin.add_def]
    exact ih.trans (he ▸ face_ports_step (m + 1) b i.castSucc)

private theorem face_port_of_dart (d : AllDart k) :
    ∃ i, (face k).SameCycle (port k (faceSide k d) i) d := by
  rcases d with (⟨i, _ | _⟩ | ⟨i, _ | _⟩) | (i | i)
  · refine ⟨i, ⟨(1 : Nat), ?_⟩⟩
    simp [face, openPhi, openRing, asOpen, ring,
      rho, rhoFun, interiorAlpha, port, faceSide]
  · refine ⟨i, ⟨(1 : Nat), ?_⟩⟩
    simp [face, openPhi, openRing, asOpen, ring,
      rho, rhoFun, interiorAlpha, port, faceSide]
  · refine ⟨i, ⟨(2 : Nat), ?_⟩⟩
    simp [face, openPhi, openRing, asOpen, ring,
      rho, rhoFun, interiorAlpha, flip, port, faceSide, pow_succ, Equiv.Perm.mul_apply]
  · refine ⟨i + 1, ⟨(2 : Nat), ?_⟩⟩
    simp [face, openPhi, openRing, asOpen, ring,
      rho, rhoFun, interiorAlpha, flip, port, faceSide, pow_succ, Equiv.Perm.mul_apply]
  · exact ⟨i, Equiv.Perm.SameCycle.refl _ _⟩
  · exact ⟨i, Equiv.Perm.SameCycle.refl _ _⟩

/-- All darts on each side lie on one face; the two sides never share a face. -/
theorem face_sameCycle_iff (d e : AllDart k) :
    (face k).SameCycle d e ↔ faceSide k d = faceSide k e := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih => simpa only [pow_succ', Equiv.Perm.mul_apply, faceSide_step] using ih
  · intro h
    obtain ⟨i, hi⟩ := face_port_of_dart k d
    obtain ⟨j, hj⟩ := face_port_of_dart k e
    have hd := (face_ports_root k (faceSide k d) i).trans hi
    have he := (face_ports_root k (faceSide k e) j).trans hj
    rw [h] at hd
    exact hd.symm.trans he

theorem openRing_face_count : (face k).partition.parts.card = 2 := by
  rw [← GoertzelV24FaceOrbitPartitionBridge.card_permOrbit_eq_card_partition_parts]
  change orbitCount (face k) = 2
  have h := OrbitCountSplitting.orbitCount_eq_card_of_completeInvariant
    (faceSide k) (face_sameCycle_iff k) (by
      intro b
      exact ⟨port k b 0, by cases b <;> rfl⟩)
  simpa using h

/-- The open Euler contribution is independent of circumference. -/
theorem openRing_eulerMass : OpenTangleReplacementEuler.eulerMass (openRing k) = 4 := by
  unfold OpenTangleReplacementEuler.eulerMass
  rw [show (openPhi (openRing k)).partition.parts.card = 2 from openRing_face_count k]
  simp [Vtx, Dart, Fintype.card_sum, Fintype.card_prod]
  ring

/-- The geometric transfer library reads the explicitly computed port return. -/
theorem encode_ring : SerialTangleFaceCode.encode (ring k) = boundaryPerm k := by
  ext b
  change SerialTangleFaceCode.boundaryCoordinate (Dart k) _
    (nextHitPerm (face k) SerialTangleFaceTransfer.Boundary ⟨.inr b, trivial⟩) = _
  rw [boundary_first_return]
  rfl

private theorem boundary_sameCycle (a b : Fin k ⊕ Fin k) :
    (boundaryPerm k).SameCycle a b ↔ faceSide k (.inr a) = faceSide k (.inr b) := by
  have h := permCongr_sameCycle_iff
    (SerialTangleFaceCode.boundaryCoordinate (Dart k) (Fin k ⊕ Fin k))
    (nextHitPerm (face k) SerialTangleFaceTransfer.Boundary)
    ⟨.inr a, trivial⟩ ⟨.inr b, trivial⟩
  rw [nextHitPerm_sameCycle_iff] at h
  change (SerialTangleFaceCode.encode (ring k)).SameCycle a b ↔ _ at h
  rw [encode_ring] at h
  exact h.trans (face_sameCycle_iff k _ _)

theorem boundary_cycle_count : (boundaryPerm k).partition.parts.card = 2 := by
  rw [← GoertzelV24FaceOrbitPartitionBridge.card_permOrbit_eq_card_partition_parts]
  change orbitCount (boundaryPerm k) = 2
  have h := OrbitCountSplitting.orbitCount_eq_card_of_completeInvariant
    (fun b => faceSide k (.inr b)) (boundary_sameCycle k) (by
      intro b
      cases b
      · exact ⟨.inl 0, rfl⟩
      · exact ⟨.inr 0, rfl⟩)
  simpa using h

/-- Joining two annular return permutations retains both exterior cycles. -/
theorem boundary_transfer :
    SerialTangleFaceCode.transfer (boundaryPerm k) (boundaryPerm k) = boundaryPerm k := by
  ext b
  let q := Equiv.sumCongr (boundaryPerm k) (boundaryPerm k) * SerialTangleFaceCode.codeSwap
  let e := SerialTangleFaceCode.codeExternalCoordinate (L := Fin k) (P := Fin k) (R := Fin k)
  have h : nextHitPerm q SerialTangleFaceCode.ExternalCode (e.symm b) =
      e.symm (boundaryNext k b) := by
    apply nextHit_eq_of_returnArc
    refine ⟨show 0 < 1 by decide, ?_, by intro n hn hlt; omega⟩
    cases b <;> rfl
  change e (nextHitPerm q SerialTangleFaceCode.ExternalCode (e.symm b)) = boundaryNext k b
  rw [h, Equiv.apply_symm_apply]

private def seamCoordinate :
    ((Fin k ⊕ Fin k) ⊕ (Fin k ⊕ Fin k)) ≃
      ((Fin k ⊕ Fin k) ⊕ (Fin k × Bool)) where
  toFun
    | .inl (.inl i) => .inl (.inl i)
    | .inr (.inr i) => .inl (.inr i)
    | .inl (.inr i) => .inr (i, false)
    | .inr (.inl i) => .inr (i - 1, true)
  invFun
    | .inl (.inl i) => .inl (.inl i)
    | .inl (.inr i) => .inr (.inr i)
    | .inr (i, false) => .inl (.inr i)
    | .inr (i, true) => .inr (.inl (i + 1))
  left_inv := by rintro ((i | i) | (i | i)) <;> simp
  right_inv := by rintro ((i | i) | ⟨i, _ | _⟩) <;> simp

private def seamFlip : Equiv.Perm (Fin k × Bool) where
  toFun p := (p.1, !p.2)
  invFun p := (p.1, !p.2)
  left_inv := by rintro ⟨i, b⟩; simp
  right_inv := by rintro ⟨i, b⟩; simp

omit [NeZero k] in
private theorem seamFlip_count : (seamFlip k).partition.parts.card = k := by
  rw [← GoertzelV24FaceOrbitPartitionBridge.card_permOrbit_eq_card_partition_parts]
  change orbitCount (seamFlip k) = k
  have h := OrbitCountSplitting.orbitCount_eq_card_of_completeInvariant
    (σ := seamFlip k) Prod.fst (by
      rintro ⟨i, b⟩ ⟨j, c⟩
      constructor
      · intro h
        obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
        have hi : ∀ n, ((seamFlip k ^ n) (i, b)).1 = i := by
          intro n
          induction n with
          | zero => rfl
          | succ n ih => simpa [pow_succ', Equiv.Perm.mul_apply, seamFlip] using ih
        simpa [hn] using (hi n).symm
      · intro hij
        change i = j at hij
        subst j
        cases b <;> cases c
        · exact Equiv.Perm.SameCycle.refl _ _
        · exact (Equiv.Perm.SameCycle.refl _ _).apply_right
        · exact (Equiv.Perm.SameCycle.refl _ _).apply_right
        · exact Equiv.Perm.SameCycle.refl _ _)
    (fun i => ⟨(i, false), rfl⟩)
  simpa using h

/-- Sewing closes exactly one additional boundary orbit per seam position. -/
theorem rewired_boundary_cycle_count :
    (Equiv.Perm.partition (Equiv.sumCongr (boundaryPerm k) (boundaryPerm k) *
      SerialTangleFaceCode.codeSwap)).parts.card = k + 2 := by
  have he : (seamCoordinate k).permCongr
      (Equiv.sumCongr (boundaryPerm k) (boundaryPerm k) *
        SerialTangleFaceCode.codeSwap) =
      Equiv.sumCongr (boundaryPerm k) (seamFlip k) := by
    ext d
    rcases d with (i | i) | ⟨i, _ | _⟩ <;>
      simp [Equiv.permCongr_apply, seamCoordinate, boundaryPerm, boundaryNext,
        SerialTangleFaceCode.codeSwap, seamFlip, Equiv.Perm.mul_apply]
  have h := GoertzelV24RetainedSpliceFaceCount.card_permCongr_partition_parts
    (seamCoordinate k)
    (Equiv.sumCongr (boundaryPerm k) (boundaryPerm k) * SerialTangleFaceCode.codeSwap)
  rw [he, OpenTangleReplacementEuler.cycle_count_sum,
    boundary_cycle_count, seamFlip_count] at h
  omega

variable {V I : Type*} [Fintype V] [DecidableEq V] [Fintype I] [DecidableEq I]

omit [Fintype V] [DecidableEq V] in
/-- The serial constructor preserves the annular boundary return. -/
theorem appendRing_face_code (T : TwoSidedOpenTangleData V I (Fin k) (Fin k))
    (hT : SerialTangleFaceCode.encode T = boundaryPerm k) :
    SerialTangleFaceCode.encode (T.serialCompose (ring k) (Equiv.refl _)) = boundaryPerm k := by
  rw [SerialTangleFaceCode.encode_serial, hT, encode_ring, boundary_transfer]

omit [DecidableEq V] in
/-- Actual Euler mass is unchanged by adding a ring to an annular return.
No assertion of ambient connectedness or bridge-freedom is implicit here. -/
theorem appendRing_eulerMass (T : TwoSidedOpenTangleData V I (Fin k) (Fin k))
    (hT : SerialTangleFaceCode.encode T = boundaryPerm k) :
    OpenTangleReplacementEuler.eulerMass (asOpen (T.serialCompose (ring k) (Equiv.refl _))) =
      OpenTangleReplacementEuler.eulerMass (asOpen T) := by
  have h := SerialTangleFaceTransfer.serial_eulerMass T (ring k)
  have hb := GoertzelV24RetainedSpliceFaceCount.card_permCongr_partition_parts
    (SerialTangleFaceCode.combinedCoordinate (I := I) (J := Dart k))
    (SerialTangleFaceTransfer.combinedReturn T (ring k))
  have hr := GoertzelV24RetainedSpliceFaceCount.card_permCongr_partition_parts
    (SerialTangleFaceCode.combinedCoordinate (I := I) (J := Dart k))
    (SerialTangleFaceTransfer.combinedReturn T (ring k) * SerialTangleFaceTransfer.boundarySwap)
  rw [SerialTangleFaceCode.combined_code, hT, encode_ring,
    OpenTangleReplacementEuler.cycle_count_sum, boundary_cycle_count] at hb
  rw [SerialTangleFaceCode.rewired_code, hT, encode_ring, rewired_boundary_cycle_count] at hr
  have h' :
      OpenTangleReplacementEuler.eulerMass (asOpen (T.serialCompose (ring k) (Equiv.refl _))) +
          2 * ((SerialTangleFaceTransfer.combinedReturn T (ring k)).partition.parts.card : ℤ) +
          2 * k =
        OpenTangleReplacementEuler.eulerMass (asOpen T) +
          OpenTangleReplacementEuler.eulerMass (asOpen (ring k)) +
          2 * ((SerialTangleFaceTransfer.combinedReturn T (ring k) *
            SerialTangleFaceTransfer.boundarySwap).partition.parts.card : ℤ) := by
    convert h using 1 <;> congr!
    simp only [Fintype.card_fin]
  have hm : OpenTangleReplacementEuler.eulerMass (asOpen (ring k)) = 4 := by
    exact openRing_eulerMass k
  rw [← hb, ← hr, hm] at h'
  omega

theorem tube_succ (n : Nat) : tube k (n + 1) = HiddenTangle.appendRing k (tube k n) := by
  unfold tube HiddenTangle.appendRings
  exact Function.iterate_succ_apply' _ _ _

instance tube_vertices_finite (n : Nat) : Finite (tube k n).V :=
  HiddenTangle.appendRings_finite k ⟨Vtx k, Dart k, ring k⟩ n

instance tube_interiors_finite (n : Nat) : Finite (tube k n).I := by
  induction n with
  | zero => exact inferInstanceAs (Finite (Dart k))
  | succ n ih =>
    rw [tube_succ]
    change Finite (((tube k n).I ⊕ Dart k) ⊕ (Fin k ⊕ Fin k))
    let := ih
    infer_instance

local instance tubeVertexFintype (n : Nat) : Fintype (tube k n).V := Fintype.ofFinite _
local instance tubeInteriorFintype (n : Nat) : Fintype (tube k n).I := Fintype.ofFinite _

local instance appendRingVertexFintype (T : HiddenTangle (Fin k) (Fin k)) [Fintype T.V] :
    Fintype (HiddenTangle.appendRing k T).V := inferInstanceAs (Fintype (T.V ⊕ Vtx k))

local instance appendRingInteriorFintype (T : HiddenTangle (Fin k) (Fin k)) [Fintype T.I] :
    Fintype (HiddenTangle.appendRing k T).I :=
  inferInstanceAs (Fintype ((T.I ⊕ Dart k) ⊕ (Fin k ⊕ Fin k)))

omit [NeZero k] in
private theorem hidden_encode_congr (T U : HiddenTangle (Fin k) (Fin k))
    [Fintype T.I] [DecidableEq T.I] [Fintype U.I] [DecidableEq U.I] (h : T = U) :
    SerialTangleFaceCode.encode T.data = SerialTangleFaceCode.encode U.data := by
  subst U
  congr 1

omit [NeZero k] in
private theorem hidden_mass_congr (T U : HiddenTangle (Fin k) (Fin k))
    [Fintype T.V] [Fintype T.I] [DecidableEq T.I]
    [Fintype U.V] [Fintype U.I] [DecidableEq U.I] (h : T = U) :
    OpenTangleReplacementEuler.eulerMass (asOpen T.data) =
      OpenTangleReplacementEuler.eulerMass (asOpen U.data) := by
  subst U
  congr 1 <;> exact Subsingleton.elim _ _

/-- Every nonempty literal tube has the same two oriented boundary returns. -/
theorem tube_face_code (n : Nat) :
    SerialTangleFaceCode.encode (tube k n).data = boundaryPerm k := by
  induction n with
  | zero => exact encode_ring k
  | succ n ih =>
    have h := appendRing_face_code k (tube k n).data ih
    exact (hidden_encode_congr k _ _ (tube_succ k n)).trans h

/-- Every nonempty literal tube has open Euler mass four. Interior faces
created at successive seams are included by the exact sewing formula. -/
theorem tube_eulerMass (n : Nat) :
    OpenTangleReplacementEuler.eulerMass (asOpen (tube k n).data) = 4 := by
  induction n with
  | zero =>
    convert openRing_eulerMass k using 1
    congr 1 <;> exact Subsingleton.elim _ _
  | succ n ih =>
    have h := appendRing_eulerMass k (tube k n).data (tube_face_code k n)
    apply (hidden_mass_congr k _ _ (tube_succ k n)).trans
    convert h.trans ih using 1
    congr 1

end

end Mettapedia.GraphTheory.FourColor.ZigzagRing
