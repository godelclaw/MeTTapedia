import Mathlib.Data.Fin.Rev
import Mettapedia.GraphTheory.FourColor.GoertzelV24RotationSpliceConstructor
import Mettapedia.GraphTheory.FourColor.DualTruncateSpanningFace
import Mettapedia.GraphTheory.OrbitCountSplitting

/-!
# Literal capped ladders

The perimeter has twice as many vertices as the ladder has columns. Each
vertex has its predecessor, successor, and reflected rung. At either end
the rung and one perimeter edge are parallel, with distinct dart-pair edge
identities. The face permutation is computed from these actual rotations.
-/

namespace Mettapedia.GraphTheory.FourColor.CappedLadderRotation

open GoertzelV24RotationSpliceConstructor
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceTwoSided GoertzelV24OrbitFaceCurvatureBulk
open DualTruncateSpanningFace

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (m : ℕ) [NeZero m]

abbrev Vertex := Fin (2*m)
abbrev Dart := Vertex m × Fin 3

private theorem two_le : 2 ≤ 2*m := by
  have := NeZero.ne m
  omega

private theorem one_ne_zero : (1 : Vertex m) ≠ 0 := by
  intro h
  have hv := congrArg Fin.val h
  change 1 % (2*m) = 0 at hv
  rw [Nat.mod_eq_of_lt (two_le m)] at hv
  omega

private theorem rev_eq_neg_one_sub {n : ℕ} [NeZero n] (v : Fin n) :
    v.rev = -1-v := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne n)
  rw [← Fin.last_sub]
  congr 1
  apply Fin.ext
  simp

theorem rev_ne (v : Vertex m) : v.rev ≠ v := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_rev] at hv
  have := v.is_lt
  omega

def flip (d : Dart m) : Dart m :=
  ![(d.1-1, 1), (d.1+1, 0), (d.1.rev, 2)] d.2

theorem flip_involutive (d : Dart m) : flip m (flip m d) = d := by
  rcases d with ⟨v,i⟩
  fin_cases i <;> simp [flip]

def alpha : Equiv.Perm (Dart m) :=
  (Function.Involutive.toPerm (flip m) (flip_involutive m))

def rho : Equiv.Perm (Dart m) :=
  Equiv.prodCongr (Equiv.refl (Vertex m)) (Equiv.addRight (1 : Fin 3))

@[simp] theorem alpha_zero (v : Vertex m) : alpha m (v,0) = (v-1,1) := rfl
@[simp] theorem alpha_one (v : Vertex m) : alpha m (v,1) = (v+1,0) := rfl
@[simp] theorem alpha_two (v : Vertex m) : alpha m (v,2) = (v.rev,2) := rfl
@[simp] theorem rho_apply (v : Vertex m) (i : Fin 3) : rho m (v,i) = (v,i+1) := rfl

abbrev data : RewiredDartSystem (Vertex m) (Dart m) where
  vertOf := Prod.fst
  alpha := alpha m
  rho := rho m
  alpha_involutive := flip_involutive m
  alpha_fixfree := by
    rintro ⟨v,i⟩ h
    fin_cases i
    · have h10 : (1 : Fin 3) = 0 := congrArg Prod.snd h
      norm_num at h10
    · have h01 : (0 : Fin 3) = 1 := congrArg Prod.snd h
      norm_num at h01
    · exact rev_ne m v (congrArg Prod.fst h)
  vert_rho := fun _ => rfl
  outer := (0,1)
  no_self_loops := by
    rintro ⟨v,i⟩ h
    fin_cases i
    · change v = v-1 at h
      have hz : (1 : Vertex m) = 0 := by
        have he := (sub_eq_iff_eq_add).mp h.symm
        exact add_left_cancel (a := v) (by simpa only [add_zero] using he.symm)
      exact one_ne_zero m hz
    · change v = v+1 at h
      have hz : (1 : Vertex m) = 0 :=
        add_left_cancel (a := v) (by simpa only [add_zero] using h.symm)
      exact one_ne_zero m hz
    · exact rev_ne m v h.symm

abbrev source : RotationSystem (Vertex m) (data m).Edge where
  D := Dart m
  edgeOf := (data m).edgeOf
  vertOf := Prod.fst
  alpha := alpha m
  rho := rho m
  alpha_involutive := flip_involutive m
  alpha_fixfree := (data m).alpha_fixfree
  edge_alpha := (data m).edgeOf_alpha
  edge_fiber_two := (data m).edge_fiber_two
  vert_rho := fun _ => rfl
  outer := (0,1)
  no_self_loops := (data m).no_self_loops

theorem source_eq : source m = (data m).toRotationSystem := rfl

@[simp] theorem phi_zero (v : Vertex m) : (source m).phi (v,0) = (v-1,2) := rfl
@[simp] theorem phi_one (v : Vertex m) : (source m).phi (v,1) = (v+1,1) := rfl
@[simp] theorem phi_two (v : Vertex m) : (source m).phi (v,2) = (v.rev,0) := by
  change (v.rev,(2 : Fin 3)+1) = (v.rev,0)
  congr 1

theorem cubic : (source m).IsCubic := by
  intro v
  have hf : (source m).dartsAt v = {(v,0), (v,1), (v,2)} := by
    ext d
    rcases d with ⟨w,i⟩
    change (w,i) ∈ Finset.univ.filter (fun d : Dart m => d.1 = v) ↔ _
    fin_cases i <;> simp [Prod.mk.injEq]
  rw [hf]
  simp

theorem rotationCyclic : VertexRotationCyclic (source m) := by
  rintro ⟨v,i⟩ ⟨w,j⟩ h
  change v = w at h
  subst w
  have h01 : (source m).rho.SameCycle (v,0) (v,1) := ⟨1, rfl⟩
  have h12 : (source m).rho.SameCycle (v,1) (v,2) := ⟨1, rfl⟩
  have h02 := h01.trans h12
  fin_cases i <;> fin_cases j <;> first
    | exact Equiv.Perm.SameCycle.refl _ _
    | exact h01
    | exact h12
    | exact h02
    | exact h01.symm
    | exact h12.symm
    | exact h02.symm

theorem outer_sameCycle (v : Vertex m) :
    (source m).phi.SameCycle (0,1) (v,1) := by
  have all (k : ℕ) (hk : k < 2*m) :
      (source m).phi.SameCycle (0,1) (⟨k,hk⟩,1) := by
    induction k with
    | zero => exact Equiv.Perm.SameCycle.refl _ _
    | succ k ih =>
      apply (ih (by omega)).trans
      refine ⟨1, ?_⟩
      rw [zpow_one, phi_one]
      congr 1
      apply Fin.ext
      change (k+(1 % (2*m))) % (2*m) = k+1
      rw [Nat.mod_eq_of_lt (two_le m)]
      exact Nat.mod_eq_of_lt hk
  exact all v.val v.is_lt

def spanningFace : SpanningFace (source m) where
  seed := (0,1)
  covers := fun v => ⟨(v,1), rfl, outer_sameCycle m v⟩

theorem connected : (rotationPrimalGraph (source m)).Connected := by
  have reach (v : Vertex m) : (rotationPrimalGraph (source m)).Reachable 0 v := by
    have all (k : ℕ) (hk : k < 2*m) :
        (rotationPrimalGraph (source m)).Reachable 0 ⟨k,hk⟩ := by
      induction k with
      | zero => exact .refl _
      | succ k ih =>
        apply (ih (by omega)).trans
        apply SimpleGraph.Adj.reachable
        refine ⟨(⟨k,by omega⟩,1), rfl, ?_⟩
        change (⟨k,by omega⟩ : Vertex m)+1 = ⟨k+1,hk⟩
        apply Fin.ext
        change (k+(1 % (2*m))) % (2*m) = k+1
        rw [Nat.mod_eq_of_lt (two_le m)]
        exact Nat.mod_eq_of_lt hk
    exact all v.val v.is_lt
  exact { preconnected := fun u v => (reach u).symm.trans (reach v) }

/-- Distance from the left cap in the reflected perimeter coordinates. -/
def folded (v : Vertex m) : Fin (m+1) :=
  ⟨min v.val (2*m-v.val), by have := v.is_lt; simp only [min_def]; split_ifs <;> omega⟩

private theorem neg_val (v : Vertex m) (hv : v ≠ 0) :
    (-v).val = 2*m-v.val := by
  rw [Fin.val_neg']
  apply Nat.mod_eq_of_lt
  have hpos : 0 < v.val := by
    have : v.val ≠ 0 := fun h => hv (Fin.ext h)
    omega
  omega

theorem folded_neg (v : Vertex m) : folded m (-v) = folded m v := by
  by_cases hv : v = 0
  · subst v; simp
  apply Fin.ext
  change min (-v).val (2*m-(-v).val) = min v.val (2*m-v.val)
  rw [neg_val m v hv]
  have he : 2*m-(2*m-v.val) = v.val := by have := v.is_lt; omega
  rw [he, min_comm]

def innerRoot (i : Fin (m+1)) : Vertex m := ⟨i.val, by have := i.is_lt; have := two_le m; omega⟩

theorem folded_innerRoot (i : Fin (m+1)) : folded m (innerRoot m i) = i := by
  apply Fin.ext
  change min i.val (2*m-i.val) = i.val
  apply min_eq_left
  have := i.is_lt
  omega

theorem innerRoot_folded (v : Vertex m) :
    innerRoot m (folded m v) = v ∨ innerRoot m (folded m v) = -v := by
  by_cases h : v.val ≤ 2*m-v.val
  · left
    apply Fin.ext
    exact min_eq_left h
  · right
    have hv : v ≠ 0 := by intro he; subst v; simp at h
    apply Fin.ext
    change min v.val (2*m-v.val) = (-v).val
    rw [neg_val m v hv, min_eq_right (by omega)]

abbrev FaceLabel := Unit ⊕ Fin (m+1)

def faceLabel (d : Dart m) : FaceLabel m :=
  ![.inr (folded m d.1), .inl (), .inr (folded m (d.1+1))] d.2

theorem faceLabel_phi (d : Dart m) : faceLabel m ((source m).phi d) = faceLabel m d := by
  rcases d with ⟨v,i⟩
  fin_cases i
  · change Sum.inr (folded m (v-1+1)) = Sum.inr (folded m v)
    simp
  · rfl
  · change faceLabel m (v.rev,(2 : Fin 3)+1) = faceLabel m (v,2)
    rw [show (2 : Fin 3)+1 = 0 from by decide +kernel]
    change Sum.inr (folded m v.rev) = Sum.inr (folded m (v+1))
    have he : v.rev = -(v+1) := by rw [rev_eq_neg_one_sub]; abel
    rw [he, folded_neg]

def faceRoot : FaceLabel m → Dart m
  | .inl _ => (0,1)
  | .inr i => (innerRoot m i,0)

theorem faceRoot_label (label : FaceLabel m) : faceLabel m (faceRoot m label) = label := by
  rcases label with u | i
  · cases u; rfl
  · simp [faceRoot, faceLabel, folded_innerRoot]

theorem phi_sq_zero (v : Vertex m) : ((source m).phi ^ 2) (v,0) = (-v,0) := by
  rw [pow_two, Equiv.Perm.mul_apply, phi_zero, phi_two]
  rw [rev_eq_neg_one_sub]
  congr 1
  abel

private theorem inner_sameCycle (v : Vertex m) :
    (source m).phi.SameCycle (innerRoot m (folded m v),0) (v,0) := by
  rcases innerRoot_folded m v with h | h
  · simpa only [h] using Equiv.Perm.SameCycle.refl (source m).phi (v,0)
  · rw [h]
    exact (show (source m).phi.SameCycle (v,0) (-v,0) from
      ⟨(2 : ℕ), by rw [zpow_natCast]; exact phi_sq_zero m v⟩).symm

theorem faceRoot_sameCycle (d : Dart m) :
    (source m).phi.SameCycle (faceRoot m (faceLabel m d)) d := by
  rcases d with ⟨v,i⟩
  fin_cases i
  · exact inner_sameCycle m v
  · exact outer_sameCycle m v
  · have he : folded m (v+1) = folded m v.rev := by
      rw [show v.rev = -(v+1) from by rw [rev_eq_neg_one_sub]; abel, folded_neg]
    change (source m).phi.SameCycle (innerRoot m (folded m (v+1)),0) (v,2)
    rw [he]
    exact (inner_sameCycle m v.rev).trans
      (show (source m).phi.SameCycle (v,2) (v.rev,0) from
        ⟨1, by rw [zpow_one, phi_two]⟩).symm

theorem face_sameCycle_iff (d e : Dart m) :
    (source m).phi.SameCycle d e ↔ faceLabel m d = faceLabel m e := by
  constructor
  · intro h
    obtain ⟨n, rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [pow_succ', Equiv.Perm.mul_apply, faceLabel_phi]
      exact ih
  · intro h
    have hd := faceRoot_sameCycle m d
    rw [h] at hd
    exact hd.symm.trans (faceRoot_sameCycle m e)

theorem face_count : Fintype.card (OrbitFace (source m)) = m+2 := by
  have h := OrbitCountSplitting.orbitCount_eq_card_of_completeInvariant
    (faceLabel m) (face_sameCycle_iff m)
    (fun l => ⟨faceRoot m l, faceRoot_label m l⟩)
  simpa [GoertzelV24PermutationOrbitSurgery.orbitCount, FaceLabel,
    OrbitFace, Nat.card_eq_fintype_card,
    Fintype.card_sum, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using h

theorem edge_count : Fintype.card (data m).Edge = 3*m := by
  have h := (source m).card_darts_eq_twice_card_edges
  change Fintype.card (Dart m) = _ at h
  simp only [Dart, Vertex, Fintype.card_prod, Fintype.card_fin] at h
  omega

theorem spherical : OrbitSphericalCubicMapData (source m) where
  cubic := cubic m
  euler := by
    rw [face_count, edge_count]
    simp only [Vertex, Fintype.card_fin]
    push_cast
    ring

theorem folded_succ_ne (v : Vertex m) : folded m (v+1) ≠ folded m v := by
  intro h
  have he := congrArg Fin.val h
  change min (v+1).val (2*m-(v+1).val) = min v.val (2*m-v.val) at he
  have hs : (v+1).val = (v.val+1) % (2*m) := by
    change (v.val+(1 % (2*m))) % (2*m) = _
    rw [Nat.mod_eq_of_lt (two_le m)]
  rw [hs] at he
  by_cases hv : v.val+1 < 2*m
  · rw [Nat.mod_eq_of_lt hv] at he
    simp only [min_def] at he
    split_ifs at he <;> omega
  · have hx : v.val+1 = 2*m := by have := v.is_lt; omega
    rw [hx, Nat.mod_self] at he
    simp only [min_def] at he
    split_ifs at he <;> omega

theorem twoSided : OrbitFacesTwoSided (source m) := by
  rintro ⟨v,i⟩ h
  have he : faceLabel m (v,i) = faceLabel m ((source m).alpha (v,i)) :=
    (face_sameCycle_iff m _ _).mp (Quotient.exact h)
  fin_cases i
  · simp [source, data, faceLabel] at he
  · simp [source, data, faceLabel] at he
  · change Sum.inr (folded m (v+1)) = Sum.inr (folded m (v.rev+1)) at he
    have hr : v.rev+1 = -v := by rw [rev_eq_neg_one_sub]; abel
    rw [hr, folded_neg] at he
    exact folded_succ_ne m v (Sum.inr.inj he)

end
end Mettapedia.GraphTheory.FourColor.CappedLadderRotation
