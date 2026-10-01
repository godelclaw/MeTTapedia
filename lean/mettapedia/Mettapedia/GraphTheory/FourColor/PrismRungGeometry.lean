import Mettapedia.GraphTheory.FourColor.PrismRungSplice

/-!
# Geometry of the original prism family

The actual face permutation has two rim orbits and one quadrilateral orbit
per rim position. The invariant below is complete at every width, giving
the sphere equation and two-sided edge incidence without a face table.
-/

namespace Mettapedia.GraphTheory.FourColor.PrismRungGeometry

open PrismRungCoordinates
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24TwoEdgeCutMinimality

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (m : ℕ) [NeZero m]

@[simp] theorem phi_zero (v : Vertex m) : (source m).phi (v,0) = (prev m v,2) := rfl
@[simp] theorem phi_one (v : Vertex m) : (source m).phi (v,1) = (next m v,1) := rfl
@[simp] theorem phi_two (v : Vertex m) : (source m).phi (v,2) = (v.rev,0) := by
  change (v.rev,(2 : Fin 3)+1) = (v.rev,0)
  congr 1

def rim (v : Vertex m) : Bool := decide (m+1 ≤ v.val)
def quad (v : Vertex m) : Fin (m+1) :=
  ⟨if v.val ≤ m then v.val else if v.val = m+1 then 0 else 2*m+2-v.val,
    by have := v.is_lt; split_ifs <;> omega⟩

theorem quad_val (v : Vertex m) : (quad m v).val =
    if v.val ≤ m then v.val else if v.val = m+1 then 0 else 2*m+2-v.val := by
  unfold quad
  split_ifs <;> rfl

theorem quad_partner (v : Vertex m) : quad m (prev m v).rev = quad m v := by
  apply Fin.ext
  have hv := v.is_lt
  simp only [quad_val,Fin.val_rev,prev_val]
  split_ifs <;> first | contradiction | omega

theorem rim_next (v : Vertex m) : rim m (next m v) = rim m v := by
  have hv := v.is_lt
  by_cases h : m+1 ≤ v.val
  · have hn : m+1 ≤ (next m v).val := by rw [next_val]; split_ifs <;> omega
    simp [rim,h,hn]
  · have hn : ¬m+1 ≤ (next m v).val := by rw [next_val]; split_ifs <;> omega
    simp [rim,h,hn]

def quadRoot (i : Fin (m+1)) : Vertex m := ⟨i.val,by have := i.is_lt; omega⟩
def rimRoot (b : Bool) : Vertex m := if b then ⟨m+1,by omega⟩ else 0

theorem quad_root (i : Fin (m+1)) : quad m (quadRoot m i) = i := by
  apply Fin.ext
  have hi := i.is_lt
  simp only [quad_val,quadRoot,Fin.val_mk]
  rw [ite_eq_left (by omega)]

theorem quad_root_or_partner (v : Vertex m) :
    quadRoot m (quad m v) = v ∨ quadRoot m (quad m v) = (prev m v).rev := by
  have hv := v.is_lt
  by_cases htop : v.val ≤ m
  · left
    apply Fin.ext
    simp only [quadRoot,Fin.val_mk,quad_val,ite_eq_left htop]
  · right
    apply Fin.ext
    simp only [quadRoot,Fin.val_mk,quad_val,prev_val,Fin.val_rev,ite_eq_right htop]
    split_ifs <;> first | contradiction | omega

abbrev FaceLabel := Bool ⊕ Fin (m+1)
def faceLabel (d : Dart m) : FaceLabel m :=
  ![.inr (quad m d.1),.inl (rim m d.1),.inr (quad m d.1.rev)] d.2
def faceRoot : FaceLabel m → Dart m
  | .inl b => (rimRoot m b,1)
  | .inr i => (quadRoot m i,0)

theorem faceLabel_phi (d : Dart m) : faceLabel m ((source m).phi d) = faceLabel m d := by
  rcases d with ⟨v,i⟩
  fin_cases i
  · change Sum.inr (quad m (prev m v).rev) = Sum.inr (quad m v)
    rw [quad_partner]
  · change Sum.inl (rim m (next m v)) = Sum.inl (rim m v)
    rw [rim_next]
  · rfl

theorem faceRoot_label (l : FaceLabel m) : faceLabel m (faceRoot m l) = l := by
  rcases l with b | i
  · cases b <;> simp [faceLabel,faceRoot,rim,rimRoot]
  · change Sum.inr (quad m (quadRoot m i)) = Sum.inr i
    rw [quad_root]

theorem rim_sameCycle (v : Vertex m) :
    (source m).phi.SameCycle (rimRoot m (rim m v),1) (v,1) := by
  have top (k : ℕ) (hk : k ≤ m) :
      (source m).phi.SameCycle (0,1) (⟨k,by omega⟩,1) := by
    induction k with
    | zero => exact Equiv.Perm.SameCycle.refl _ _
    | succ k ih =>
      apply (ih (by omega)).trans
      refine ⟨1,?_⟩
      rw [zpow_one,phi_one]
      apply Prod.ext
      · apply Fin.ext
        rw [next_val]
        simp only [Fin.val_mk]
        rw [ite_eq_right (by omega),ite_eq_right (by omega)]
      · rfl
  have bottom (k : ℕ) (hk : k ≤ m) :
      (source m).phi.SameCycle (⟨m+1,by omega⟩,1) (⟨m+1+k,by omega⟩,1) := by
    induction k with
    | zero => exact Equiv.Perm.SameCycle.refl _ _
    | succ k ih =>
      apply (ih (by omega)).trans
      refine ⟨1,?_⟩
      rw [zpow_one,phi_one]
      apply Prod.ext
      · apply Fin.ext
        rw [next_val]
        simp only [Fin.val_mk]
        rw [ite_eq_right (by omega),ite_eq_right (by omega)]
        omega
      · rfl
  have hv := v.is_lt
  by_cases h : v.val ≤ m
  · have he : rimRoot m (rim m v) = 0 := by simp [rimRoot,rim,show ¬m+1 ≤ v.val by omega]
    rw [he]
    exact top v.val h
  · have he : rimRoot m (rim m v) = ⟨m+1,by omega⟩ := by simp [rimRoot,rim,show m+1 ≤ v.val by omega]
    rw [he]
    have hb := bottom (v.val-(m+1)) (by omega)
    have hv' : (⟨m+1+(v.val-(m+1)),by omega⟩ : Vertex m) = v := by apply Fin.ext; change m+1+(v.val-(m+1)) = v.val; omega
    simpa only [hv'] using hb

theorem phi_sq_zero (v : Vertex m) : ((source m).phi ^ 2) (v,0) = ((prev m v).rev,0) := by
  rw [pow_two,Equiv.Perm.mul_apply,phi_zero,phi_two]

theorem quad_sameCycle (v : Vertex m) :
    (source m).phi.SameCycle (quadRoot m (quad m v),0) (v,0) := by
  rcases quad_root_or_partner m v with h | h
  · simpa only [h] using Equiv.Perm.SameCycle.refl (source m).phi (v,0)
  · rw [h]
    exact (show (source m).phi.SameCycle (v,0) ((prev m v).rev,0) from
      ⟨(2 : ℕ),by rw [zpow_natCast]; exact phi_sq_zero m v⟩).symm

theorem faceRoot_sameCycle (d : Dart m) :
    (source m).phi.SameCycle (faceRoot m (faceLabel m d)) d := by
  rcases d with ⟨v,i⟩
  fin_cases i
  · exact quad_sameCycle m v
  · exact rim_sameCycle m v
  · exact (quad_sameCycle m v.rev).trans
      (show (source m).phi.SameCycle (v,2) (v.rev,0) from ⟨1,by rw [zpow_one,phi_two]⟩).symm

theorem face_sameCycle_iff (d e : Dart m) :
    (source m).phi.SameCycle d e ↔ faceLabel m d = faceLabel m e := by
  constructor
  · intro h
    obtain ⟨n,rfl⟩ := h.exists_nat_pow_eq
    clear h
    induction n with
    | zero => rfl
    | succ n ih => rw [pow_succ',Equiv.Perm.mul_apply,faceLabel_phi]; exact ih
  · intro h
    have hd := faceRoot_sameCycle m d
    rw [h] at hd
    exact hd.symm.trans (faceRoot_sameCycle m e)

theorem face_count : Fintype.card (OrbitFace (source m)) = m+3 := by
  have h := OrbitCountSplitting.orbitCount_eq_card_of_completeInvariant
    (faceLabel m) (face_sameCycle_iff m) (fun l => ⟨faceRoot m l,faceRoot_label m l⟩)
  simpa [GoertzelV24PermutationOrbitSurgery.orbitCount,FaceLabel,OrbitFace,
    Nat.card_eq_fintype_card,Fintype.card_sum,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using h

theorem edge_count : Fintype.card (data m).Edge = 3*(m+1) := by
  have h := (source m).card_darts_eq_twice_card_edges
  change Fintype.card (Dart m) = _ at h
  simp only [Dart,Vertex,CappedLadderRotation.Vertex,Fintype.card_prod,Fintype.card_fin] at h
  omega

theorem spherical : OrbitSphericalCubicMapData (source m) where
  cubic := cubic m
  euler := by
    rw [face_count,edge_count]
    simp only [Vertex,CappedLadderRotation.Vertex,Fintype.card_fin]
    push_cast
    ring

theorem quad_rev_ne (v : Vertex m) : quad m v ≠ quad m v.rev := by
  intro h
  have he := congrArg Fin.val h
  have hv := v.is_lt
  have hm := NeZero.ne m
  simp only [quad_val,Fin.val_rev] at he
  split_ifs at he <;> first | contradiction | omega

theorem twoSided : OrbitFacesTwoSided (source m) := by
  rintro ⟨v,i⟩ h
  have he := (face_sameCycle_iff m _ _).mp (Quotient.exact h)
  fin_cases i
  · change Sum.inr (quad m v) = Sum.inl (rim m (prev m v)) at he
    cases he
  · change Sum.inl (rim m v) = Sum.inr (quad m (next m v)) at he
    cases he
  · change Sum.inr (quad m v.rev) = Sum.inr (quad m v.rev.rev) at he
    rw [Fin.rev_rev] at he
    exact quad_rev_ne m v (Sum.inr.inj he).symm

theorem connected : (graph m).Connected := by
  have top (k : ℕ) (hk : k ≤ m) : (graph m).Reachable 0 (⟨k,by omega⟩ : Vertex m) := by
    induction k with
    | zero => exact .refl _
    | succ k ih =>
      apply (ih (by omega)).trans
      apply _root_.SimpleGraph.Adj.reachable
      refine ⟨(⟨k,by omega⟩,1),rfl,?_⟩
      change next m ⟨k,by omega⟩ = (⟨k+1,by omega⟩ : Vertex m)
      apply Fin.ext
      rw [next_val]
      simp only [Fin.val_mk]
      rw [ite_eq_right (by omega),ite_eq_right (by omega)]
  have reach (v : Vertex m) : (graph m).Reachable 0 v := by
    by_cases h : v.val ≤ m
    · exact top v.val h
    · have hv := v.is_lt
      have hr : v.rev.val ≤ m := by rw [Fin.val_rev]; omega
      exact (top v.rev.val hr).trans
        (_root_.SimpleGraph.Adj.reachable (show (graph m).Adj v.rev v from
          ⟨(v.rev,2),rfl,Fin.rev_rev v⟩))
  letI : Nonempty (Vertex m) := ⟨0⟩
  exact ⟨fun v w => (reach v).symm.trans (reach w)⟩

variable (hm : 2 ≤ m)

/-- The original graph-backed prism has the same proved sphere geometry. -/
theorem graph_spherical : OrbitSphericalCubicMapData (graphData m hm).toRotationSystem :=
  RotationSystemExactTransport.spherical (source m) (graphData m hm).toRotationSystem
    (dartEquiv m hm) (Equiv.refl _) (dartEquiv_alpha m hm) (fun _ => rfl)
    (fun d => (graph_rho m hm d).symm) (spherical m)

theorem graph_twoSided : OrbitFacesTwoSided (graphData m hm).toRotationSystem :=
  RotationSystemExactTransport.twoSided (source m) (graphData m hm).toRotationSystem
    (dartEquiv m hm) (dartEquiv_alpha m hm) (fun d => (graph_rho m hm d).symm) (twoSided m)

end
end Mettapedia.GraphTheory.FourColor.PrismRungGeometry
