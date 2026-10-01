import Mettapedia.GraphTheory.FourColor.CappedLadderEndReduction
import Mettapedia.GraphTheory.FourColor.AdjacentSourceFacePhaseReduction
import Mettapedia.GraphTheory.FourColor.RotationSystemExactTransport

/-!
# Literal coordinates for a prism rung splice

The two rim cycles use opposite perimeter orders, with reflected rungs.
Deleting the rung at the two extreme perimeter vertices exposes four rail
darts. The intended sewing retains each dart and each parallel end edge.
This file constructs the original simple source from its actual rotations.
-/

namespace Mettapedia.GraphTheory.FourColor.PrismRungCoordinates

open GoertzelV24RotationSpliceConstructor GoertzelV24FaceDualConnectedness
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open DualTruncateColoring

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (m : ℕ) [NeZero m]

abbrev Vertex := CappedLadderRotation.Vertex (m+1)
abbrev Dart := Vertex m × Fin 3

def prev (v : Vertex m) : Vertex m :=
  if v.val = 0 then ⟨m,by omega⟩
  else if v.val = m+1 then ⟨2*m+1,by omega⟩
  else ⟨v.val-1,by have := v.is_lt; omega⟩

def next (v : Vertex m) : Vertex m :=
  if v.val = m then ⟨0,by omega⟩
  else if h : v.val = 2*m+1 then ⟨m+1,by omega⟩
  else ⟨v.val+1,by have := v.is_lt; omega⟩

theorem prev_val (v : Vertex m) : (prev m v).val =
    if v.val = 0 then m else if v.val = m+1 then 2*m+1 else v.val-1 := by
  unfold prev
  split_ifs <;> rfl

theorem next_val (v : Vertex m) : (next m v).val =
    if v.val = m then 0 else if v.val = 2*m+1 then m+1 else v.val+1 := by
  unfold next
  split_ifs <;> rfl

theorem prev_next (v : Vertex m) : prev m (next m v) = v := by
  apply Fin.ext
  have := v.is_lt
  have : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  simp only [prev_val, next_val]
  split_ifs <;> first | contradiction | omega

theorem next_prev (v : Vertex m) : next m (prev m v) = v := by
  apply Fin.ext
  have := v.is_lt
  have : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  simp only [prev_val, next_val]
  split_ifs <;> omega

def flip (d : Dart m) : Dart m :=
  ![(prev m d.1,1),(next m d.1,0),(d.1.rev,2)] d.2

theorem flip_involutive (d : Dart m) : flip m (flip m d) = d := by
  rcases d with ⟨v,i⟩
  fin_cases i <;> simp [flip, prev_next, next_prev]

def alpha : Equiv.Perm (Dart m) :=
  Function.Involutive.toPerm (flip m) (flip_involutive m)

def rho : Equiv.Perm (Dart m) :=
  Equiv.prodCongr (Equiv.refl (Vertex m)) (Equiv.addRight (1 : Fin 3))

@[simp] theorem alpha_zero (v : Vertex m) : alpha m (v,0) = (prev m v,1) := rfl
@[simp] theorem alpha_one (v : Vertex m) : alpha m (v,1) = (next m v,0) := rfl
@[simp] theorem alpha_two (v : Vertex m) : alpha m (v,2) = (v.rev,2) := rfl
@[simp] theorem rho_apply (v : Vertex m) (i : Fin 3) : rho m (v,i) = (v,i+1) := rfl

theorem neighbor_injective (hm : 2 ≤ m) (v : Vertex m) :
    Function.Injective (fun i : Fin 3 => (alpha m (v,i)).1) := by
  have hv := v.is_lt
  have hpn : prev m v ≠ next m v := by
    intro h
    have he := congrArg Fin.val h
    simp only [prev_val, next_val] at he
    split_ifs at he <;> omega
  have hpr : prev m v ≠ v.rev := by
    intro h
    have he := congrArg Fin.val h
    simp only [prev_val, Fin.val_rev] at he
    split_ifs at he <;> omega
  have hnr : next m v ≠ v.rev := by
    intro h
    have he := congrArg Fin.val h
    simp only [next_val, Fin.val_rev] at he
    split_ifs at he <;> omega
  intro i j h
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | exact False.elim (hpn h)
    | exact False.elim (hpn h.symm)
    | exact False.elim (hpr h)
    | exact False.elim (hpr h.symm)
    | exact False.elim (hnr h)
    | exact False.elim (hnr h.symm)

abbrev data : RewiredDartSystem (Vertex m) (Dart m) where
  vertOf := Prod.fst
  alpha := alpha m
  rho := rho m
  alpha_involutive := flip_involutive m
  alpha_fixfree := by
    rintro ⟨v,i⟩ h
    fin_cases i
    · have : (1 : Fin 3) = 0 := congrArg Prod.snd h
      norm_num at this
    · have : (0 : Fin 3) = 1 := congrArg Prod.snd h
      norm_num at this
    · exact CappedLadderRotation.rev_ne (m+1) v (congrArg Prod.fst h)
  vert_rho := fun _ => rfl
  outer := (0,2)
  no_self_loops := by
    rintro ⟨v,i⟩ h
    have hpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
    have hv := v.is_lt
    have he := congrArg Fin.val h
    fin_cases i
    · change v.val = (prev m v).val at he
      simp only [prev_val] at he
      split_ifs at he <;> omega
    · change v.val = (next m v).val at he
      simp only [next_val] at he
      split_ifs at he <;> omega
    · exact CappedLadderRotation.rev_ne (m+1) v h.symm

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
  outer := (0,2)
  no_self_loops := (data m).no_self_loops

abbrev graph := rotationPrimalGraph (source m)

def graphDart (d : Dart m) : (graph m).Dart :=
  ⟨(d.1,((source m).alpha d).1),⟨d,rfl,rfl⟩⟩

def ports : Fin 4 → Vertex m :=
  ![⟨m,by omega⟩,⟨1,by omega⟩,⟨2*m,by omega⟩,⟨m+1,by omega⟩]

theorem ports_val (i : Fin 4) : (ports m i).val = ![m,1,2*m,m+1] i := by
  fin_cases i <;> rfl

variable (hm : 2 ≤ m)

include hm in
theorem graphDart_injective : Function.Injective (graphDart m) := by
  rintro ⟨v,i⟩ ⟨w,j⟩ h
  have hv : v = w := congrArg (fun d : (graph m).Dart => d.fst) h
  subst w
  have hi := neighbor_injective m hm v (congrArg (fun d : (graph m).Dart => d.snd) h)
  subst j
  rfl

theorem graphDart_surjective : Function.Surjective (graphDart m) := by
  intro d
  obtain ⟨a,ha,hb⟩ := d.adj
  refine ⟨a, ?_⟩
  apply SimpleGraph.Dart.ext
  exact Prod.ext ha hb

def dartEquiv : Dart m ≃ (graph m).Dart :=
  Equiv.ofBijective (graphDart m) ⟨graphDart_injective m hm,graphDart_surjective m⟩

@[simp] theorem dartEquiv_fst (d : Dart m) : (dartEquiv m hm d).fst = d.1 := rfl
@[simp] theorem dartEquiv_snd (d : Dart m) :
    (dartEquiv m hm d).snd = ((source m).alpha d).1 := rfl

theorem dartEquiv_alpha (d : Dart m) :
    dartEquiv m hm ((source m).alpha d) = (dartEquiv m hm d).symm := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · change ((source m).alpha ((source m).alpha d)).1 = d.1
    rw [(source m).alpha_involutive]

def graphData : SimpleGraphDartRotation.Data (graph m) where
  vertexRotation := (dartEquiv m hm).permCongr (rho m)
  vertexRotation_fst := by
    intro d
    obtain ⟨a,rfl⟩ := (dartEquiv m hm).surjective d
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    rfl
  outer := dartEquiv m hm (0,2)

theorem graph_rho (d : Dart m) :
    (graphData m hm).vertexRotation (dartEquiv m hm d) =
      dartEquiv m hm ((source m).rho d) := by
  change (dartEquiv m hm).permCongr (rho m) (dartEquiv m hm d) = _
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]

instance graphAdjDecidable : DecidableRel (graph m).Adj := fun v w =>
  inferInstanceAs (Decidable (∃ d : Dart m, d.1 = v ∧ (alpha m d).1 = w))

theorem cubic : (source m).IsCubic := by
  intro v
  have hf : (source m).dartsAt v = {(v,0),(v,1),(v,2)} := by
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
  have h01 : (source m).rho.SameCycle (v,0) (v,1) := ⟨1,rfl⟩
  have h12 : (source m).rho.SameCycle (v,1) (v,2) := ⟨1,rfl⟩
  have h02 := h01.trans h12
  fin_cases i <;> fin_cases j <;> first
    | exact Equiv.Perm.SameCycle.refl _ _
    | exact h01
    | exact h12
    | exact h02
    | exact h01.symm
    | exact h12.symm
    | exact h02.symm

theorem graph_cubic : (graphData m hm).toRotationSystem.IsCubic :=
  RotationSystemExactTransport.cubic (source m) (graphData m hm).toRotationSystem
    (dartEquiv m hm) (Equiv.refl _) (fun _ => rfl) (cubic m)

theorem graph_rotation : VertexRotationCyclic (graphData m hm).toRotationSystem :=
  RotationSystemExactTransport.rotationCyclic (source m) (graphData m hm).toRotationSystem
    (dartEquiv m hm) (Equiv.refl _) (fun _ => rfl) (fun d => (graph_rho m hm d).symm)
    (rotationCyclic m)

def lastVertex : Vertex m := ⟨2*m+1,by omega⟩

theorem rev_zero : (0 : Vertex m).rev = lastVertex m := by
  apply Fin.ext
  simp only [Fin.val_rev, Fin.val_zero, lastVertex, Fin.val_mk]
  omega

theorem rev_last : (lastVertex m).rev = 0 := by rw [← rev_zero, Fin.rev_rev]

include hm in
theorem ports_injective : Function.Injective (ports m) := by
  intro i j h
  have he := congrArg Fin.val h
  simp only [ports_val] at he
  fin_cases i <;> fin_cases j <;> first
    | rfl
    | (exfalso; simp at he <;> omega)

include hm in
theorem ports_ne_zero (i : Fin 4) : ports m i ≠ 0 := by
  intro h
  have he := congrArg Fin.val h
  simp only [ports_val,Fin.val_zero] at he
  fin_cases i <;> simp at he <;> omega

include hm in
theorem ports_ne_last (i : Fin 4) : ports m i ≠ lastVertex m := by
  intro h
  have he := congrArg Fin.val h
  simp only [ports_val,lastVertex,Fin.val_mk] at he
  fin_cases i <;> simp at he <;> omega

theorem neighbors (v : Vertex m) : (graph m).neighborSet v =
    ({prev m v,next m v,v.rev} : Set (Vertex m)) := by
  ext w
  change (∃ d : Dart m, d.1 = v ∧ ((source m).alpha d).1 = w) ↔ _
  constructor
  · rintro ⟨⟨x,i⟩,hx,hα⟩
    change x = v at hx
    subst x
    fin_cases i
    · exact Or.inl hα.symm
    · exact Or.inr (Or.inl hα.symm)
    · exact Or.inr (Or.inr hα.symm)
  · intro h
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
    rcases h with rfl | rfl | rfl
    · exact ⟨(v,0),rfl,rfl⟩
    · exact ⟨(v,1),rfl,rfl⟩
    · exact ⟨(v,2),rfl,rfl⟩

theorem prev_zero : prev m 0 = ports m 0 := by simp [prev,ports]

theorem next_zero : next m 0 = ports m 1 := by
  have hzero : (0 : ℕ) ≠ m := (NeZero.ne m).symm
  simp [next,ports,hzero]

theorem prev_last : prev m (lastVertex m) = ports m 2 := by
  have hpos : 0 < m := Nat.pos_of_ne_zero (NeZero.ne m)
  apply Fin.ext
  rw [prev_val]
  change (if 2*m+1 = 0 then m else if 2*m+1 = m+1 then 2*m+1 else 2*m+1-1) = 2*m
  rw [if_neg (by omega),if_neg (by omega)]
  omega

theorem next_last : next m (lastVertex m) = ports m 3 := by
  apply Fin.ext
  rw [next_val]
  change (if 2*m+1 = m then 0 else if 2*m+1 = 2*m+1 then m+1 else 2*m+1+1) = m+1
  rw [if_neg (by omega),if_pos rfl]

def pair : GoertzelV24AdjacentPairBoundary.AdjacentPairData (graph m) where
  firstVertex := 0
  secondVertex := lastVertex m
  portVertex := ports m
  centralAdjacent := ⟨(0,2),rfl,rev_zero m⟩
  portInjective := ports_injective m hm
  portNeFirst := ports_ne_zero m hm
  portNeSecond := ports_ne_last m hm
  firstNeighbors := by
    rw [neighbors,prev_zero,next_zero,rev_zero]
    ext w
    simp [or_comm,or_left_comm,or_assoc]
  secondNeighbors := by
    rw [neighbors,prev_last,next_last,rev_last]
    ext w
    simp [or_comm,or_left_comm,or_assoc]

/-- The named rung is the actual central dart of the graph representation. -/
theorem central_dart : (pair m hm).rotationCentralDart = dartEquiv m hm (0,2) := by
  apply SimpleGraph.Dart.ext
  exact Prod.ext rfl (rev_zero m).symm

/-- The four interface positions are determined by the original rotations. -/
theorem rotation_ports (i : Fin 4) :
    (pair m hm).rotationPortVertex (graphData m hm) i = ports m i := by
  have hcentral := central_dart m hm
  have hrung : (graphData m hm).toRotationSystem.alpha (dartEquiv m hm (0,2)) =
      dartEquiv m hm (lastVertex m,2) := by
    change (dartEquiv m hm (0,2)).symm = _
    rw [← dartEquiv_alpha, alpha_two, rev_zero]
  fin_cases i
  · change ((graphData m hm).vertexRotation (pair m hm).rotationCentralDart).snd = _
    rw [hcentral,graph_rho]
    exact prev_zero m
  · change ((graphData m hm).vertexRotation
        ((graphData m hm).vertexRotation (pair m hm).rotationCentralDart)).snd = _
    rw [hcentral,graph_rho,graph_rho]
    exact next_zero m
  · change ((graphData m hm).vertexRotation
        ((graphData m hm).toRotationSystem.alpha (pair m hm).rotationCentralDart)).snd = _
    rw [hcentral,hrung,graph_rho]
    exact prev_last m
  · change ((graphData m hm).vertexRotation
        ((graphData m hm).vertexRotation
          ((graphData m hm).toRotationSystem.alpha (pair m hm).rotationCentralDart))).snd = _
    rw [hcentral,hrung,graph_rho,graph_rho]
    exact next_last m

/-- Canonical cyclic ordering agrees with the literal four exposed ports. -/
theorem ordered_pair :
    AdjacentSourceSplice.ordered (graphData m hm) (pair m hm)
      (graph_cubic m hm) (graph_rotation m hm) = pair m hm := by
  have hp : (pair m hm).rotationPortVertex (graphData m hm) = ports m :=
    funext (rotation_ports m hm)
  unfold AdjacentSourceSplice.ordered
    GoertzelV24AdjacentPairBoundary.AdjacentPairData.rotationOrderedData
  simp only [hp]
  rfl

end
end Mettapedia.GraphTheory.FourColor.PrismRungCoordinates
