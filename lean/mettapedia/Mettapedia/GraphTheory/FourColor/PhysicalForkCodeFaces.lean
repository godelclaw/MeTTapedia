import Mettapedia.GraphTheory.FourColor.PhysicalForkCode
import Mettapedia.GraphTheory.FourColor.EdgeShoreFaceForkFold
import Mettapedia.GraphTheory.FourColor.GoertzelV24ForkLocality
import Mettapedia.GraphTheory.FourColor.GoertzelV24InducedHexCorridorTypes

/-!
# The face coordinate of the fork fold, on positions

`EdgeShoreFaceForkFold` carries the face return of a node on its interface
darts `{d // Iface S d}`, a subtype of the ambient dart set.  On a cubic map
whose vertex rotations are single three-cycles, every middle vertex of an edge
shore carries exactly one interface dart: the partner of the last shore dart
before the rotation leaves the shore.  So the interface darts are the middle
vertices, and the face return becomes a permutation of the positions that name
the middle vertices.

At a fork the parent return is the first return of the merged child returns,
corrected by `forkRewire`.  This file proves that the correction is the
exchange of the two interface darts at every shared vertex and the identity
elsewhere.  The proof is one local fact about a three-cycle: from the left
child's interface turn at a shared vertex, the first return to the parent shore
is the right child's own first return, and symmetrically.

Consequently the fork step reads only the positions that are shared, and which
marks the parent keeps; no other ambient data enters.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFaces

open Equiv Equiv.Perm
open GoertzelV24OrderedCutFaceReturnProfile
open PermutationFirstReturnRestriction
open GoertzelV24ForkInterfaceSupport
open EdgeShoreFaceForkFold
open GoertzelV24FaceDualConnectedness

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-! ## Cubic three-cycle rotations -/

/-- The local shape of a cubic map with cyclic vertex rotations: the rotation
has period three, and the darts at a vertex are `d`, `ρ d`, `ρ² d`. -/
structure Cubic3 : Prop where
  cube : ∀ d, RS.rho (RS.rho (RS.rho d)) = d
  fiber : ∀ d d', RS.vertOf d' = RS.vertOf d →
    d' = d ∨ d' = RS.rho d ∨ d' = RS.rho (RS.rho d)

theorem cubic3_of (hcubic : RS.IsCubic) (hrot : VertexRotationCyclic RS) : Cubic3 RS := by
  have hcube := GoertzelV24InducedHexCorridorTypes.rho_cube_apply_of_isCubic RS hcubic hrot
  have h3 : RS.rho ^ 3 = 1 := by
    ext d
    simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply, Perm.one_apply]
    exact hcube d
  refine ⟨hcube, ?_⟩
  intro d d' hv
  obtain ⟨k, hk⟩ := (hrot d d' hv.symm).exists_nat_pow_eq
  have hpow : RS.rho ^ k = RS.rho ^ (k % 3) := by
    conv_lhs => rw [← Nat.div_add_mod k 3, pow_add, pow_mul, h3, one_pow, one_mul]
  rw [hpow] at hk
  have hlt : k % 3 < 3 := Nat.mod_lt _ (by norm_num)
  interval_cases h : k % 3
  · left; simpa using hk.symm
  · right; left; simpa using hk.symm
  · right; right; simpa [pow_succ, Perm.mul_apply] using hk.symm

/-! ## Middle vertices and interface darts -/

theorem mem_mid_iff (S : Finset E) (v : V) :
    v ∈ mid RS.endpoints S ↔
      (∃ d, RS.vertOf d = v ∧ RS.edgeOf d ∈ S) ∧
        (∃ d, RS.vertOf d = v ∧ RS.edgeOf d ∉ S) := by
  simp only [mid, Finset.mem_filter, Finset.mem_univ, true_and, Finset.Nonempty,
    RotationSystem.mem_endpoints_iff, RotationSystem.dartsOn, Finset.mem_compl]
  constructor
  · rintro ⟨⟨e, he, d, hd, hv⟩, ⟨f, hf, d', hd', hv'⟩⟩
    have hd : RS.edgeOf d = e := by simpa using hd
    have hd' : RS.edgeOf d' = f := by simpa using hd'
    exact ⟨⟨d, hv, hd ▸ he⟩, ⟨d', hv', hd' ▸ hf⟩⟩
  · rintro ⟨⟨d, hv, hd⟩, ⟨d', hv', hd'⟩⟩
    exact ⟨⟨RS.edgeOf d, hd, d, by simp, hv⟩, ⟨RS.edgeOf d', hd', d', by simp, hv'⟩⟩

theorem vertOf_rho_pow (n : ℕ) (d : RS.D) : RS.vertOf ((RS.rho ^ n) d) = RS.vertOf d := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pow_succ', Perm.mul_apply, RS.vert_rho, ih]

theorem vertOf_nextHit (hit : RS.D → Prop) (x : {d // hit d}) :
    RS.vertOf (nextHitPerm RS.rho hit x).1 = RS.vertOf x.1 := by
  obtain ⟨n, hn⟩ := (GoertzelV24SeamFaceArc.nextHit_sameCycle RS.rho hit x).exists_nat_pow_eq
  rw [nextHitPerm_apply, ← hn, vertOf_rho_pow]

/-- The interface darts of an edge shore. -/
abbrev IfaceDart (S : Finset E) := {d : RS.D // Iface RS.rho RS.alpha RS.edgeOf S d}

/-- The middle vertices of an edge shore. -/
abbrev MidVertex (S : Finset E) := {v : V // v ∈ mid RS.endpoints S}

theorem inShore_alpha_iff (S : Finset E) (d : RS.D) :
    InShore RS.edgeOf S (RS.alpha d) ↔ InShore RS.edgeOf S d := by
  simp only [InShore, RS.edge_alpha]

theorem iface_vertex_mem (S : Finset E) (d : IfaceDart RS S) :
    RS.vertOf (RS.alpha d.1) ∈ mid RS.endpoints S := by
  rw [mem_mid_iff]
  exact ⟨⟨RS.alpha d.1, rfl, (inShore_alpha_iff RS S d.1).mpr d.2.1⟩,
    ⟨RS.rho (RS.alpha d.1), RS.vert_rho _, d.2.2⟩⟩

/-- An interface dart sits at the far end of its edge: the vertex where the
rotation leaves the shore. -/
def ifaceVertex (S : Finset E) (d : IfaceDart RS S) : MidVertex RS S :=
  ⟨RS.vertOf (RS.alpha d.1), iface_vertex_mem RS S d⟩

variable {RS}

theorem ifaceVertex_injective (hC : Cubic3 RS) (S : Finset E) :
    Function.Injective (ifaceVertex RS S) := by
  intro a b hab
  have hv : RS.vertOf (RS.alpha b.1) = RS.vertOf (RS.alpha a.1) :=
    (congrArg Subtype.val hab).symm
  have hxS : RS.edgeOf (RS.alpha a.1) ∈ S := (inShore_alpha_iff RS S a.1).mpr a.2.1
  have hyS : RS.edgeOf (RS.alpha b.1) ∈ S := (inShore_alpha_iff RS S b.1).mpr b.2.1
  have hx' : RS.edgeOf (RS.rho (RS.alpha a.1)) ∉ S := a.2.2
  have hy' : RS.edgeOf (RS.rho (RS.alpha b.1)) ∉ S := b.2.2
  rcases hC.fiber _ _ hv with h | h | h
  · apply Subtype.ext
    have := congrArg RS.alpha h
    rw [RS.alpha_involutive, RS.alpha_involutive] at this
    exact this.symm
  · exact absurd (h ▸ hyS) hx'
  · exact absurd (by rw [h, hC.cube]; exact hxS) hy'

theorem exists_last_shore_dart (hC : Cubic3 RS) {S : Finset E} {v : V}
    (hv : v ∈ mid RS.endpoints S) :
    ∃ x, RS.vertOf x = v ∧ RS.edgeOf x ∈ S ∧ RS.edgeOf (RS.rho x) ∉ S := by
  obtain ⟨⟨a, ha, haS⟩, ⟨b, hb, hbS⟩⟩ := (mem_mid_iff RS S v).mp hv
  by_cases h1 : RS.edgeOf (RS.rho a) ∈ S
  · refine ⟨RS.rho a, by rw [RS.vert_rho, ha], h1, ?_⟩
    rcases hC.fiber a b (hb.trans ha.symm) with h | h | h
    · exact absurd (h ▸ haS) hbS
    · exact absurd (h ▸ h1) hbS
    · rw [← h]; exact hbS
  · exact ⟨a, ha, haS, h1⟩

theorem ifaceVertex_surjective (hC : Cubic3 RS) (S : Finset E) :
    Function.Surjective (ifaceVertex RS S) := by
  rintro ⟨v, hv⟩
  obtain ⟨x, hxv, hxS, hx'⟩ := exists_last_shore_dart hC hv
  refine ⟨⟨RS.alpha x, (inShore_alpha_iff RS S x).mpr hxS, ?_⟩, ?_⟩
  · show RS.edgeOf (RS.rho (RS.alpha (RS.alpha x))) ∉ S
    rw [RS.alpha_involutive]; exact hx'
  · apply Subtype.ext
    show RS.vertOf (RS.alpha (RS.alpha x)) = v
    rw [RS.alpha_involutive, hxv]

/-- **One interface dart per middle vertex.** -/
def ifaceEquiv (hC : Cubic3 RS) (S : Finset E) : IfaceDart RS S ≃ MidVertex RS S :=
  Equiv.ofBijective (ifaceVertex RS S) ⟨ifaceVertex_injective hC S, ifaceVertex_surjective hC S⟩

@[simp] theorem ifaceEquiv_apply_val (hC : Cubic3 RS) (S : Finset E) (d : IfaceDart RS S) :
    (ifaceEquiv hC S d).1 = RS.vertOf (RS.alpha d.1) := rfl

theorem vertOf_alpha_ifaceEquiv_symm (hC : Cubic3 RS) (S : Finset E) (v : MidVertex RS S) :
    RS.vertOf (RS.alpha ((ifaceEquiv hC S).symm v).1) = v.1 := by
  exact congrArg Subtype.val ((ifaceEquiv hC S).apply_symm_apply v)

/-! ## First returns around one vertex -/

section Returns

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem nextHit_two (p : Perm D) (hit : D → Prop) (x : {d // hit d})
    (h1 : ¬ hit (p x.1)) (h2 : hit (p (p x.1))) :
    (nextHitPerm p hit x).1 = p (p x.1) := by
  have := nextHit_eq_of_returnArc p hit x ⟨p (p x.1), h2⟩ (n := 2)
    ⟨by norm_num, by simp [pow_two, Perm.mul_apply], by
      intro i hi hil
      interval_cases i
      simpa using h1⟩
  exact congrArg Subtype.val this

theorem nextHit_three (p : Perm D) (hit : D → Prop) (x : {d // hit d})
    (h1 : ¬ hit (p x.1)) (h2 : ¬ hit (p (p x.1))) (h3 : hit (p (p (p x.1)))) :
    (nextHitPerm p hit x).1 = p (p (p x.1)) := by
  have := nextHit_eq_of_returnArc p hit x ⟨p (p (p x.1)), h3⟩ (n := 3)
    ⟨by norm_num, by simp [pow_succ, Perm.mul_apply], by
      intro i hi hil
      interval_cases i
      · simpa using h1
      · simpa [pow_two, Perm.mul_apply] using h2⟩
  exact congrArg Subtype.val this

end Returns

/-- **The local identity at a shared vertex.**  Let the left shore `S` and the
right shore `T` be disjoint and meet at one vertex; `xS` is the last left dart
there before the rotation leaves `S`, and `xT` the last right dart before it
leaves `T`.  Then the first return from `xS` to the parent shore is the right
child's own first return from `xT`.  The proof is a case split over the three
darts of the vertex. -/
theorem shared_return (hC : Cubic3 RS) {S T : Finset E} (hdisj : Disjoint S T)
    {xS xT : RS.D} (hv : RS.vertOf xT = RS.vertOf xS)
    (hS : InShore RS.edgeOf S xS) (hS' : ¬ InShore RS.edgeOf S (RS.rho xS))
    (hT : InShore RS.edgeOf T xT) (hT' : ¬ InShore RS.edgeOf T (RS.rho xT)) :
    (nextHitPerm RS.rho (InShore RS.edgeOf (S ∪ T))
        ⟨xS, inShore_left RS.edgeOf S T hS⟩).1 =
      (nextHitPerm RS.rho (InShore RS.edgeOf T) ⟨xT, hT⟩).1 := by
  have hST : ¬ InShore RS.edgeOf T xS := not_inShore_right RS.edgeOf S T hdisj hS
  have hU : ∀ {d}, InShore RS.edgeOf T d → InShore RS.edgeOf (S ∪ T) d :=
    fun h => inShore_right RS.edgeOf S T h
  rcases hC.fiber xS xT hv with h | h | h
  · exact absurd (h ▸ hT) hST
  · subst h
    rw [nextHit_apply_of_step RS.rho (InShore RS.edgeOf (S ∪ T)) _ (hU hT)]
    rw [nextHit_three RS.rho (InShore RS.edgeOf T) ⟨RS.rho xS, hT⟩ hT'
      (by show ¬ InShore RS.edgeOf T (RS.rho (RS.rho (RS.rho xS))); rw [hC.cube]; exact hST)
      (by show InShore RS.edgeOf T (RS.rho (RS.rho (RS.rho (RS.rho xS)))); rw [hC.cube]; exact hT)]
    show RS.rho xS = RS.rho (RS.rho (RS.rho (RS.rho xS)))
    rw [hC.cube]
  · subst h
    have hback : RS.rho (RS.rho (RS.rho xS)) = xS := hC.cube xS
    by_cases hmid : InShore RS.edgeOf T (RS.rho xS)
    · rw [nextHit_apply_of_step RS.rho (InShore RS.edgeOf (S ∪ T)) _ (hU hmid)]
      rw [nextHit_two RS.rho (InShore RS.edgeOf T) ⟨RS.rho (RS.rho xS), hT⟩
        (by show ¬ InShore RS.edgeOf T (RS.rho (RS.rho (RS.rho xS))); rw [hback]; exact hST)
        (by show InShore RS.edgeOf T (RS.rho (RS.rho (RS.rho (RS.rho xS)))); rw [hback]; exact hmid)]
      show RS.rho xS = RS.rho (RS.rho (RS.rho (RS.rho xS)))
      rw [hback]
    · rw [nextHit_two RS.rho (InShore RS.edgeOf (S ∪ T)) _
        (by
          intro h
          rcases Finset.mem_union.mp h with h | h
          · exact hS' h
          · exact hmid h)
        (hU hT)]
      rw [nextHit_three RS.rho (InShore RS.edgeOf T) ⟨RS.rho (RS.rho xS), hT⟩
        (by show ¬ InShore RS.edgeOf T (RS.rho (RS.rho (RS.rho xS))); rw [hback]; exact hST)
        (by show ¬ InShore RS.edgeOf T (RS.rho (RS.rho (RS.rho (RS.rho xS)))); rw [hback]; exact hmid)
        (by
          show InShore RS.edgeOf T (RS.rho (RS.rho (RS.rho (RS.rho (RS.rho xS)))))
          rw [hback]; exact hT)]
      show RS.rho (RS.rho xS) = RS.rho (RS.rho (RS.rho (RS.rho (RS.rho xS))))
      rw [hback]

/-- The same identity with the roles of the two children exchanged. -/
theorem shared_return' (hC : Cubic3 RS) {S T : Finset E} (hdisj : Disjoint S T)
    {xS xT : RS.D} (hv : RS.vertOf xT = RS.vertOf xS)
    (hS : InShore RS.edgeOf S xS) (hS' : ¬ InShore RS.edgeOf S (RS.rho xS))
    (hT : InShore RS.edgeOf T xT) (hT' : ¬ InShore RS.edgeOf T (RS.rho xT)) :
    (nextHitPerm RS.rho (InShore RS.edgeOf (S ∪ T))
        ⟨xT, inShore_right RS.edgeOf S T hT⟩).1 =
      (nextHitPerm RS.rho (InShore RS.edgeOf S) ⟨xS, hS⟩).1 := by
  have h := shared_return hC hdisj.symm hv.symm hT hT' hS hS'
  rw [← h]
  exact nextHit_val_congr_pred RS.rho (InShore RS.edgeOf (T ∪ S))
    (InShore RS.edgeOf (S ∪ T)) (fun d => by simp only [InShore, Finset.union_comm])
    ⟨xT, inShore_left RS.edgeOf T S hT⟩

/-! ## First return through a nested marked set -/

section Nested

variable {D : Type*} [Fintype D] [DecidableEq D]

theorem nested_value (p : Perm D) (big small : D → Prop) (hsub : ∀ d, small d → big d)
    (side : {d // big d} → Prop) (hside : ∀ c, side c ↔ small c.1)
    (c : {d // big d}) (hc : side c) :
    ((nextHitPerm (nextHitPerm p big) side ⟨c, hc⟩).1).1 =
      (nextHitPerm p small ⟨c.1, (hside c).mp hc⟩).1 := by
  have h1 := nextHit_val_congr_pred (nextHitPerm p big) side (fun c => small c.1) hside
    ⟨c, hc⟩
  rw [← h1, nextHit_nested p small big hsub]
  rfl

/-- A permutation identity fixing the pre-image of a rewire. -/
theorem rewire_eq_of (rho alpha : Perm D) (side : D → Prop) (x y : D)
    (h : rho (alpha x) = EdgeShoreFaceFork.splitRotation rho side (alpha y)) :
    EdgeShoreFaceFork.rewire rho alpha side x = y := by
  simp only [EdgeShoreFaceFork.rewire, Perm.mul_apply, h, Perm.inv_def, Equiv.symm_apply_apply]

/-- First return commutes with conjugation by an equivalence of carriers. -/
theorem nextHitPerm_permCongr {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (e : A ≃ B) (p : Perm A) (small : A → Prop) (hit : B → Prop)
    (h : ∀ a, hit (e a) ↔ small a) :
    nextHitPerm (e.permCongr p) hit =
      (e.subtypeEquiv (fun a => (h a).symm)).permCongr (nextHitPerm p small) := by
  apply Equiv.ext
  intro y
  obtain ⟨x, rfl⟩ := (e.subtypeEquiv (fun a => (h a).symm)).surjective y
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
  apply Subtype.ext
  exact nextHit_map p (e.permCongr p) e (fun a => by simp [Equiv.permCongr_apply])
    small hit h x

end Nested

/-! ## Positions of the face coordinate -/

/-- Name the interface darts of a shore by the positions of its middle
vertices. -/
def faceLabel (hC : Cubic3 RS) (S : Finset E) {n : ℕ} (ℓ : Fin n ≃ MidVertex RS S) :
    Fin n ≃ IfaceDart RS S :=
  ℓ.trans (ifaceEquiv hC S).symm

/-- The face coordinate of the code: the literal interface return, read on
positions. -/
def codeRet (hC : Cubic3 RS) (S : Finset E) {n : ℕ} (ℓ : Fin n ≃ MidVertex RS S) :
    Perm (Fin n) :=
  (faceLabel hC S ℓ).symm.permCongr (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha S)

theorem vertOf_alpha_faceLabel (hC : Cubic3 RS) (S : Finset E) {n : ℕ}
    (ℓ : Fin n ≃ MidVertex RS S) (i : Fin n) :
    RS.vertOf (RS.alpha (faceLabel hC S ℓ i).1) = (ℓ i).1 :=
  vertOf_alpha_ifaceEquiv_symm hC S (ℓ i)

section Fork

variable (hC : Cubic3 RS) {S T : Finset E} (hdisj : Disjoint S T)
variable {nL nR nP : ℕ} (ℓS : Fin nL ≃ MidVertex RS S) (ℓT : Fin nR ≃ MidVertex RS T)
  (ℓP : Fin nP ≃ MidVertex RS (S ∪ T))

/-- The interface marks of a fork. -/
abbrev Marked (S T : Finset E) :=
  {x : {d // InShore RS.edgeOf (S ∪ T) d} // forkHit RS.rho RS.alpha RS.edgeOf S T x}

/-- Child positions name the fork's interface marks. -/
def toMarked : Fin nL ⊕ Fin nR ≃ Marked (RS := RS) S T :=
  (Equiv.sumCongr ((faceLabel hC S ℓS).trans (forkLeftPart RS.rho RS.alpha RS.edgeOf S T).symm)
      ((faceLabel hC T ℓT).trans
        (forkRightPart RS.rho RS.alpha RS.edgeOf S T hdisj).symm)).trans
    (Equiv.sumCompl (fun y : Marked (RS := RS) S T => Iface RS.rho RS.alpha RS.edgeOf S y.1.1))

@[simp] theorem toMarked_inl (i : Fin nL) :
    (toMarked hC hdisj ℓS ℓT (.inl i)).1.1 = (faceLabel hC S ℓS i).1 := rfl

@[simp] theorem toMarked_inr (j : Fin nR) :
    (toMarked hC hdisj ℓS ℓT (.inr j)).1.1 = (faceLabel hC T ℓT j).1 := rfl

/-- The merged child returns, transported to the marks, are `mergeRet`. -/
theorem toMarked_merged :
    (toMarked hC hdisj ℓS ℓT).permCongr (Equiv.sumCongr (codeRet hC S ℓS) (codeRet hC T ℓT)) =
      mergeRet RS.rho RS.alpha RS.edgeOf S T hdisj
        (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha S)
        (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha T) := by
  apply Equiv.ext
  intro x
  obtain ⟨a, rfl⟩ := (toMarked hC hdisj ℓS ℓT).surjective x
  rcases a with i | j
  · apply Subtype.ext; apply Subtype.ext
    rw [mergeRet_apply_left RS.rho RS.alpha RS.edgeOf S T hdisj _ _ _
      (faceLabel hC S ℓS i).2]
    simp [toMarked, codeRet, Equiv.permCongr_apply, faceLabel]
    rfl
  · apply Subtype.ext; apply Subtype.ext
    have hnot : ¬ Iface RS.rho RS.alpha RS.edgeOf S (faceLabel hC T ℓT j).1 := fun h =>
      not_inShore_right RS.edgeOf S T hdisj h.1 (faceLabel hC T ℓT j).2.1
    rw [mergeRet_apply_right RS.rho RS.alpha RS.edgeOf S T hdisj _ _ _ hnot]
    simp [toMarked, codeRet, Equiv.permCongr_apply, faceLabel]
    rfl

/-- The positions of the two children that name one shared vertex. -/
def pairFun : Fin nL ⊕ Fin nR → Fin nL ⊕ Fin nR
  | .inl i =>
      if h : (ℓS i).1 ∈ mid RS.endpoints T then .inr (ℓT.symm ⟨(ℓS i).1, h⟩) else .inl i
  | .inr j =>
      if h : (ℓT j).1 ∈ mid RS.endpoints S then .inl (ℓS.symm ⟨(ℓT j).1, h⟩) else .inr j

theorem pairFun_involutive : Function.Involutive (pairFun ℓS ℓT) := by
  rintro (i | j)
  · by_cases h : (ℓS i).1 ∈ mid RS.endpoints T
    · have h' : (ℓT (ℓT.symm ⟨(ℓS i).1, h⟩)).1 ∈ mid RS.endpoints S := by
        simpa using (ℓS i).2
      simp only [pairFun, dif_pos h, dif_pos h']
      simp
    · simp [pairFun, h]
  · by_cases h : (ℓT j).1 ∈ mid RS.endpoints S
    · have h' : (ℓS (ℓS.symm ⟨(ℓT j).1, h⟩)).1 ∈ mid RS.endpoints T := by
        simpa using (ℓT j).2
      simp only [pairFun, dif_pos h, dif_pos h']
      simp
    · simp [pairFun, h]

/-- The physical pairing, as a permutation of the child positions. -/
def physPair : Perm (Fin nL ⊕ Fin nR) := (pairFun_involutive ℓS ℓT).toPerm _

@[simp] theorem physPair_apply (a : Fin nL ⊕ Fin nR) : physPair ℓS ℓT a = pairFun ℓS ℓT a := rfl

/-- A shore dart at a middle vertex which is not a middle vertex of the other
shore has no other-shore dart there. -/
theorem not_other_of_not_mid {A B : Finset E} {v : V} (hv : v ∉ mid RS.endpoints B)
    {x : RS.D} (hx : RS.vertOf x = v) (hxA : RS.edgeOf x ∈ A) (hAB : Disjoint A B)
    {r : RS.D} (hr : RS.vertOf r = v) : RS.edgeOf r ∉ B := by
  intro hrB
  apply hv
  rw [mem_mid_iff]
  exact ⟨⟨r, hr, hrB⟩, ⟨x, hx, Finset.disjoint_left.mp hAB hxA⟩⟩

/-- **The fork's face correction is the pairing of shared positions.**  At a
shared vertex it exchanges the two interface darts; elsewhere it is the
identity.  Nothing but the pairing is read. -/
theorem forkRewire_toMarked (a : Fin nL ⊕ Fin nR) :
    forkRewire RS.rho RS.alpha RS.edgeOf RS.edge_alpha S T hdisj (toMarked hC hdisj ℓS ℓT a) =
      toMarked hC hdisj ℓS ℓT (physPair ℓS ℓT a) := by
  apply Subtype.ext
  change EdgeShoreFaceFork.rewire (shoreRot RS.rho RS.edgeOf (S ∪ T))
      (shoreEdge RS.alpha RS.edgeOf RS.edge_alpha (S ∪ T)) (forkSide RS.edgeOf S T)
      (toMarked hC hdisj ℓS ℓT a).1 = (toMarked hC hdisj ℓS ℓT (physPair ℓS ℓT a)).1
  have hsideT : ∀ c : {d // InShore RS.edgeOf (S ∪ T) d},
      ¬ forkSide RS.edgeOf S T c ↔ InShore RS.edgeOf T c.1 := by
    intro c
    constructor
    · intro h; exact inShore_right_of_parent RS.edgeOf S T c.2 h
    · intro h hS; exact not_inShore_right RS.edgeOf S T hdisj hS h
  rcases a with i | j
  · -- a left mark
    set dS := (faceLabel hC S ℓS i).1 with hdS
    have hxS : InShore RS.edgeOf S (RS.alpha dS) :=
      (inShore_alpha_iff RS S dS).mpr (faceLabel hC S ℓS i).2.1
    have hxS' : ¬ InShore RS.edgeOf S (RS.rho (RS.alpha dS)) := (faceLabel hC S ℓS i).2.2
    have hvS : RS.vertOf (RS.alpha dS) = (ℓS i).1 := vertOf_alpha_faceLabel hC S ℓS i
    by_cases h : (ℓS i).1 ∈ mid RS.endpoints T
    · -- shared: exchange with the right mark at the same vertex
      set j := ℓT.symm ⟨(ℓS i).1, h⟩ with hj
      have hpair : physPair ℓS ℓT (.inl i) = .inr j := by simp [pairFun, h, hj]
      rw [hpair]
      set dT := (faceLabel hC T ℓT j).1 with hdT
      have hxT : InShore RS.edgeOf T (RS.alpha dT) :=
        (inShore_alpha_iff RS T dT).mpr (faceLabel hC T ℓT j).2.1
      have hxT' : ¬ InShore RS.edgeOf T (RS.rho (RS.alpha dT)) := (faceLabel hC T ℓT j).2.2
      have hvT : RS.vertOf (RS.alpha dT) = (ℓS i).1 := by
        rw [vertOf_alpha_faceLabel hC T ℓT j, hj]; simp
      apply rewire_eq_of
      have hneg : ¬ forkSide RS.edgeOf S T
          (shoreEdge RS.alpha RS.edgeOf RS.edge_alpha (S ∪ T)
            (toMarked hC hdisj ℓS ℓT (.inr j)).1) :=
        (hsideT _).mpr hxT
      rw [EdgeShoreFaceFork.splitRotation_apply_neg _ _ _ hneg]
      apply Subtype.ext
      have hn := nested_value RS.rho (InShore RS.edgeOf (S ∪ T)) (InShore RS.edgeOf T)
        (fun d hd => inShore_right RS.edgeOf S T hd) _ hsideT _ hneg
      exact (shared_return hC hdisj (hvT.trans hvS.symm) hxS hxS' hxT hxT').trans hn.symm
    · -- unshared: no crossing turn, so the rewire fixes the mark
      have hpair : physPair ℓS ℓT (.inl i) = .inl i := by simp [pairFun, h]
      rw [hpair]
      apply EdgeShoreFaceFork.rewire_fixed_of_not_mark
      intro hmark
      apply hmark
      show forkSide RS.edgeOf S T (shoreRot RS.rho RS.edgeOf (S ∪ T)
          (shoreEdge RS.alpha RS.edgeOf RS.edge_alpha (S ∪ T) (toMarked hC hdisj ℓS ℓT (.inl i)).1))
        ↔ InShore RS.edgeOf S (RS.alpha dS)
      refine ⟨fun _ => hxS, fun _ => ?_⟩
      set r := shoreRot RS.rho RS.edgeOf (S ∪ T)
          (shoreEdge RS.alpha RS.edgeOf RS.edge_alpha (S ∪ T) (toMarked hC hdisj ℓS ℓT (.inl i)).1)
      have hr : RS.vertOf r.1 = (ℓS i).1 := by
        rw [← hvS]
        exact vertOf_nextHit RS (InShore RS.edgeOf (S ∪ T)) _
      by_contra hrS
      exact not_other_of_not_mid h hvS hxS hdisj hr
        (inShore_right_of_parent RS.edgeOf S T r.2 hrS)
  · -- a right mark
    set dT := (faceLabel hC T ℓT j).1 with hdT
    have hxT : InShore RS.edgeOf T (RS.alpha dT) :=
      (inShore_alpha_iff RS T dT).mpr (faceLabel hC T ℓT j).2.1
    have hxT' : ¬ InShore RS.edgeOf T (RS.rho (RS.alpha dT)) := (faceLabel hC T ℓT j).2.2
    have hvT : RS.vertOf (RS.alpha dT) = (ℓT j).1 := vertOf_alpha_faceLabel hC T ℓT j
    have hxTS : ¬ InShore RS.edgeOf S (RS.alpha dT) :=
      fun hS => not_inShore_right RS.edgeOf S T hdisj hS hxT
    by_cases h : (ℓT j).1 ∈ mid RS.endpoints S
    · set i := ℓS.symm ⟨(ℓT j).1, h⟩ with hi
      have hpair : physPair ℓS ℓT (.inr j) = .inl i := by simp [pairFun, h, hi]
      rw [hpair]
      set dS := (faceLabel hC S ℓS i).1 with hdS
      have hxS : InShore RS.edgeOf S (RS.alpha dS) :=
        (inShore_alpha_iff RS S dS).mpr (faceLabel hC S ℓS i).2.1
      have hxS' : ¬ InShore RS.edgeOf S (RS.rho (RS.alpha dS)) := (faceLabel hC S ℓS i).2.2
      have hvS : RS.vertOf (RS.alpha dS) = (ℓT j).1 := by
        rw [vertOf_alpha_faceLabel hC S ℓS i, hi]; simp
      apply rewire_eq_of
      have hpos : forkSide RS.edgeOf S T
          (shoreEdge RS.alpha RS.edgeOf RS.edge_alpha (S ∪ T)
            (toMarked hC hdisj ℓS ℓT (.inl i)).1) := hxS
      rw [EdgeShoreFaceFork.splitRotation_apply_pos _ _ _ hpos]
      apply Subtype.ext
      have hn := nested_value RS.rho (InShore RS.edgeOf (S ∪ T)) (InShore RS.edgeOf S)
        (fun d hd => inShore_left RS.edgeOf S T hd) _ (fun c => Iff.rfl) _ hpos
      exact (shared_return' hC hdisj (hvT.trans hvS.symm) hxS hxS' hxT hxT').trans hn.symm
    · have hpair : physPair ℓS ℓT (.inr j) = .inr j := by simp [pairFun, h]
      rw [hpair]
      apply EdgeShoreFaceFork.rewire_fixed_of_not_mark
      intro hmark
      apply hmark
      show forkSide RS.edgeOf S T (shoreRot RS.rho RS.edgeOf (S ∪ T)
          (shoreEdge RS.alpha RS.edgeOf RS.edge_alpha (S ∪ T) (toMarked hC hdisj ℓS ℓT (.inr j)).1))
        ↔ InShore RS.edgeOf S (RS.alpha dT)
      refine ⟨fun hrS => ?_, fun hS => absurd hS hxTS⟩
      set r := shoreRot RS.rho RS.edgeOf (S ∪ T)
          (shoreEdge RS.alpha RS.edgeOf RS.edge_alpha (S ∪ T) (toMarked hC hdisj ℓS ℓT (.inr j)).1)
      have hr : RS.vertOf r.1 = (ℓT j).1 := by
        rw [← hvT]
        exact vertOf_nextHit RS (InShore RS.edgeOf (S ∪ T)) _
      exact absurd hrS (not_other_of_not_mid h hvT hxT hdisj.symm hr)

theorem toMarked_permCongr_pair :
    (toMarked hC hdisj ℓS ℓT).permCongr (physPair ℓS ℓT) =
      forkRewire RS.rho RS.alpha RS.edgeOf RS.edge_alpha S T hdisj := by
  apply Equiv.ext
  intro x
  obtain ⟨a, rfl⟩ := (toMarked hC hdisj ℓS ℓT).surjective x
  rw [Equiv.permCongr_apply, Equiv.symm_apply_apply, forkRewire_toMarked]

/-! ### The marks kept on the parent interface -/

/-- The parent's interface darts, named as marks of the fork. -/
def keepFun (k : Fin nP) : Fin nL ⊕ Fin nR :=
  (toMarked hC hdisj ℓS ℓT).symm
    (deepMarks RS.rho RS.alpha RS.edgeOf S T (faceLabel hC (S ∪ T) ℓP k)).1

theorem keepFun_injective : Function.Injective (keepFun hC hdisj ℓS ℓT ℓP) :=
  (toMarked hC hdisj ℓS ℓT).symm.injective.comp
    (Subtype.val_injective.comp ((deepMarks RS.rho RS.alpha RS.edgeOf S T).injective.comp
      (faceLabel hC (S ∪ T) ℓP).injective))

def physKeep : Fin nP ↪ Fin nL ⊕ Fin nR := ⟨keepFun hC hdisj ℓS ℓT ℓP, keepFun_injective hC hdisj ℓS ℓT ℓP⟩

theorem toMarked_keepFun (k : Fin nP) :
    toMarked hC hdisj ℓS ℓT (keepFun hC hdisj ℓS ℓT ℓP k) =
      (deepMarks RS.rho RS.alpha RS.edgeOf S T (faceLabel hC (S ∪ T) ℓP k)).1 := by
  simp [keepFun]

/-- A mark is kept exactly when its dart is an interface dart of the parent. -/
theorem mem_range_physKeep (a : Fin nL ⊕ Fin nR) :
    a ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP) ↔
      forkKeep RS.rho RS.alpha RS.edgeOf S T (toMarked hC hdisj ℓS ℓT a).1 := by
  constructor
  · rintro ⟨k, rfl⟩
    change forkKeep RS.rho RS.alpha RS.edgeOf S T
      (toMarked hC hdisj ℓS ℓT (keepFun hC hdisj ℓS ℓT ℓP k)).1
    rw [toMarked_keepFun]
    exact (deepMarks RS.rho RS.alpha RS.edgeOf S T (faceLabel hC (S ∪ T) ℓP k)).2
  · intro h
    let d : IfaceDart RS (S ∪ T) := ⟨(toMarked hC hdisj ℓS ℓT a).1.1, h⟩
    refine ⟨(faceLabel hC (S ∪ T) ℓP).symm d, ?_⟩
    change keepFun hC hdisj ℓS ℓT ℓP ((faceLabel hC (S ∪ T) ℓP).symm d) = a
    apply (toMarked hC hdisj ℓS ℓT).injective
    rw [toMarked_keepFun, Equiv.apply_symm_apply]
    rfl

/-- The physical descriptor of a fork: the pairing of shared positions, and
the parent's interface marks in parent order. -/
def physGlue : PhysicalForkCode.Glue nL nR nP := ⟨physPair ℓS ℓT, physKeep hC hdisj ℓS ℓT ℓP⟩

/-- **Fork correctness for the face coordinate.**  The abstract fork, fed the
positional returns of the two children and the physical descriptor, returns
the positional return of the parent. -/
theorem fork_ret (L : PhysicalForkCode.Code nL) (R : PhysicalForkCode.Code nR)
    (hL : L.ret = codeRet hC S ℓS) (hR : R.ret = codeRet hC T ℓT) :
    (PhysicalForkCode.fork L R (physGlue hC hdisj ℓS ℓT ℓP)).ret = codeRet hC (S ∪ T) ℓP := by
  let τ := toMarked hC hdisj ℓS ℓT
  let p := PhysicalForkCode.merged L R * physPair ℓS ℓT
  have hQ : τ.permCongr p =
      mergeRet RS.rho RS.alpha RS.edgeOf S T hdisj
          (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha S)
          (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha T) *
        forkRewire RS.rho RS.alpha RS.edgeOf RS.edge_alpha S T hdisj := by
    rw [Equiv.permCongr_mul, toMarked_permCongr_pair]
    congr 1
    rw [← toMarked_merged hC hdisj ℓS ℓT]
    simp only [PhysicalForkCode.merged, hL, hR]
    rfl
  have hhit : ∀ a, forkKeep RS.rho RS.alpha RS.edgeOf S T (τ a).1 ↔
      a ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP) :=
    fun a => (mem_range_physKeep hC hdisj ℓS ℓT ℓP a).symm
  have hN := nextHitPerm_permCongr τ p (fun a => a ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP))
    (fun y => forkKeep RS.rho RS.alpha RS.edgeOf S T y.1) hhit
  rw [hQ] at hN
  let σ := τ.subtypeEquiv (p := fun a => a ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP))
    (q := fun y : Marked (RS := RS) S T => forkKeep RS.rho RS.alpha RS.edgeOf S T y.1)
    (fun a => (hhit a).symm)
  change _ = σ.permCongr _ at hN
  -- the parent return, from the exact fork step
  have hP := forkStep_ret RS.rho RS.alpha RS.edgeOf RS.edge_alpha S T hdisj
  apply Equiv.ext
  intro k
  simp only [codeRet, PhysicalForkCode.fork, Equiv.permCongr_apply, Equiv.symm_symm]
  rw [← hP]
  change _ = (faceLabel hC (S ∪ T) ℓP).symm
    ((deepMarks RS.rho RS.alpha RS.edgeOf S T).symm
      ((nextHitPerm (mergeRet RS.rho RS.alpha RS.edgeOf S T hdisj
          (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha S)
          (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha T) *
        forkRewire RS.rho RS.alpha RS.edgeOf RS.edge_alpha S T hdisj)
        (fun y => forkKeep RS.rho RS.alpha RS.edgeOf S T y.1))
        (deepMarks RS.rho RS.alpha RS.edgeOf S T (faceLabel hC (S ∪ T) ℓP k))))
  rw [hN]
  set m := nextHitPerm p (fun a => a ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP))
    ((PhysicalForkCode.keepEquiv (physGlue hC hdisj ℓS ℓT ℓP)) k) with hm
  set k' := (PhysicalForkCode.keepEquiv (physGlue hC hdisj ℓS ℓT ℓP)).symm m with hk'
  have hmk : m.1 = keepFun hC hdisj ℓS ℓT ℓP k' := by
    have := congrArg Subtype.val
      ((PhysicalForkCode.keepEquiv (physGlue hC hdisj ℓS ℓT ℓP)).apply_symm_apply m)
    rw [← this]
    rfl
  have hsub : σ.symm
      (deepMarks RS.rho RS.alpha RS.edgeOf S T (faceLabel hC (S ∪ T) ℓP k)) =
      (PhysicalForkCode.keepEquiv (physGlue hC hdisj ℓS ℓT ℓP)) k := by
    apply σ.injective
    rw [Equiv.apply_symm_apply]
    apply Subtype.ext
    change _ = τ (keepFun hC hdisj ℓS ℓT ℓP k)
    rw [toMarked_keepFun]
  rw [Equiv.permCongr_apply, hsub, ← hm]
  have hout : σ m =
      deepMarks RS.rho RS.alpha RS.edgeOf S T (faceLabel hC (S ∪ T) ℓP k') := by
    apply Subtype.ext
    change τ m.1 = _
    rw [hmk, toMarked_keepFun]
  rw [hout, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  rfl

/-! ### The anatomy of a shared vertex -/

include hdisj in
/-- At a shared vertex the last right dart follows the last left dart either
immediately or after one step. -/
theorem shared_anatomy (hC : Cubic3 RS) {xS xT : RS.D} (hv : RS.vertOf xT = RS.vertOf xS)
    (hS : InShore RS.edgeOf S xS) (hT : InShore RS.edgeOf T xT) :
    xT = RS.rho xS ∨ xT = RS.rho (RS.rho xS) := by
  rcases hC.fiber xS xT hv with h | h | h
  · exact absurd (h ▸ hT) (not_inShore_right RS.edgeOf S T hdisj hS)
  · exact Or.inl h
  · exact Or.inr h

end Fork

/-- The `two` field: the vertex carries a second shore dart, the one before the
last shore dart in rotation order. -/
def codeTwo (hC : Cubic3 RS) (S : Finset E) {n : ℕ} (ℓ : Fin n ≃ MidVertex RS S) :
    Fin n → Bool :=
  fun i => decide (InShore RS.edgeOf S
    (RS.rho (RS.rho (RS.alpha (faceLabel hC S ℓ i).1))))

section Fork2

variable (hC : Cubic3 RS) {S T : Finset E} (hdisj : Disjoint S T)
variable {nL nR nP : ℕ} (ℓS : Fin nL ≃ MidVertex RS S) (ℓT : Fin nR ≃ MidVertex RS T)
  (ℓP : Fin nP ≃ MidVertex RS (S ∪ T))

theorem physPair_inl_of_mem {i : Fin nL} (h : (ℓS i).1 ∈ mid RS.endpoints T) :
    physPair ℓS ℓT (.inl i) = .inr (ℓT.symm ⟨(ℓS i).1, h⟩) := by
  simp [pairFun, h]

theorem physPair_inl_of_not_mem {i : Fin nL} (h : (ℓS i).1 ∉ mid RS.endpoints T) :
    physPair ℓS ℓT (.inl i) = .inl i := by
  simp [pairFun, h]

theorem physPair_inr_of_mem {j : Fin nR} (h : (ℓT j).1 ∈ mid RS.endpoints S) :
    physPair ℓS ℓT (.inr j) = .inl (ℓS.symm ⟨(ℓT j).1, h⟩) := by
  simp [pairFun, h]

theorem physPair_inr_of_not_mem {j : Fin nR} (h : (ℓT j).1 ∉ mid RS.endpoints S) :
    physPair ℓS ℓT (.inr j) = .inr j := by
  simp [pairFun, h]

/-- The dart of a left mark, its vertex, and the facts the case analyses use. -/
theorem leftMark_facts (i : Fin nL) :
    let x := RS.alpha (faceLabel hC S ℓS i).1
    InShore RS.edgeOf S x ∧ ¬ InShore RS.edgeOf S (RS.rho x) ∧ RS.vertOf x = (ℓS i).1 :=
  ⟨(inShore_alpha_iff RS S _).mpr (faceLabel hC S ℓS i).2.1, (faceLabel hC S ℓS i).2.2,
    vertOf_alpha_faceLabel hC S ℓS i⟩

theorem rightMark_facts (j : Fin nR) :
    let x := RS.alpha (faceLabel hC T ℓT j).1
    InShore RS.edgeOf T x ∧ ¬ InShore RS.edgeOf T (RS.rho x) ∧ RS.vertOf x = (ℓT j).1 :=
  ⟨(inShore_alpha_iff RS T _).mpr (faceLabel hC T ℓT j).2.1, (faceLabel hC T ℓT j).2.2,
    vertOf_alpha_faceLabel hC T ℓT j⟩

/-- Membership of a mark's dart in the parent interface. -/
theorem forkKeep_toMarked_iff (a : Fin nL ⊕ Fin nR) :
    forkKeep RS.rho RS.alpha RS.edgeOf S T (toMarked hC hdisj ℓS ℓT a).1 ↔
      ¬ InShore RS.edgeOf (S ∪ T) (RS.rho (RS.alpha (toMarked hC hdisj ℓS ℓT a).1.1)) := by
  constructor
  · intro h; exact h.2
  · intro h; exact ⟨(toMarked hC hdisj ℓS ℓT a).1.2, h⟩

theorem inl_mem_range_keep_iff (i : Fin nL) :
    Sum.inl i ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP) ↔
      ¬ InShore RS.edgeOf T (RS.rho (RS.alpha (faceLabel hC S ℓS i).1)) := by
  rw [mem_range_physKeep, forkKeep_toMarked_iff, toMarked_inl]
  obtain ⟨_, hS', _⟩ := leftMark_facts hC ℓS i
  constructor
  · intro h hT; exact h (inShore_right RS.edgeOf S T hT)
  · intro h hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact hS' hP
    · exact h hP

theorem inr_mem_range_keep_iff (j : Fin nR) :
    Sum.inr j ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP) ↔
      ¬ InShore RS.edgeOf S (RS.rho (RS.alpha (faceLabel hC T ℓT j).1)) := by
  rw [mem_range_physKeep, forkKeep_toMarked_iff, toMarked_inr]
  obtain ⟨_, hT', _⟩ := rightMark_facts hC ℓT j
  constructor
  · intro h hS; exact h (inShore_left RS.edgeOf S T hS)
  · intro h hP
    rcases Finset.mem_union.mp hP with hP | hP
    · exact h hP
    · exact hT' hP

/-- The two cases at a shared vertex, with everything the code reads. -/
theorem shared_cases (i : Fin nL) (j : Fin nR) (hij : (ℓT j).1 = (ℓS i).1) :
    (codeTwo hC T ℓT j = false ∧ Sum.inl i ∉ Set.range (physKeep hC hdisj ℓS ℓT ℓP) ∧
      (Sum.inr j ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP) ↔ codeTwo hC S ℓS i = false)) ∨
    (codeTwo hC S ℓS i = false ∧ Sum.inr j ∉ Set.range (physKeep hC hdisj ℓS ℓT ℓP) ∧
      (Sum.inl i ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP) ↔ codeTwo hC T ℓT j = false)) := by
  obtain ⟨hS, hS', hvS⟩ := leftMark_facts hC ℓS i
  obtain ⟨hT, hT', hvT⟩ := rightMark_facts hC ℓT j
  set xS := RS.alpha (faceLabel hC S ℓS i).1 with hxS
  set xT := RS.alpha (faceLabel hC T ℓT j).1 with hxT
  have hST : ∀ {d}, InShore RS.edgeOf S d → ¬ InShore RS.edgeOf T d :=
    fun h => not_inShore_right RS.edgeOf S T hdisj h
  rw [inl_mem_range_keep_iff, inr_mem_range_keep_iff]
  rcases shared_anatomy hdisj hC (hvT.trans (hij.trans hvS.symm)) hS hT with h | h
  · left
    refine ⟨?_, ?_, ?_⟩
    · simp only [codeTwo, decide_eq_false_iff_not]
      change ¬ InShore RS.edgeOf T (RS.rho (RS.rho xT))
      rw [h, hC.cube]; exact hST hS
    · rw [← h]; exact fun hn => hn hT
    · simp only [codeTwo, decide_eq_false_iff_not]
      change ¬ InShore RS.edgeOf S (RS.rho xT) ↔ ¬ InShore RS.edgeOf S (RS.rho (RS.rho xS))
      rw [h]
  · right
    refine ⟨?_, ?_, ?_⟩
    · simp only [codeTwo, decide_eq_false_iff_not]
      change ¬ InShore RS.edgeOf S (RS.rho (RS.rho xS))
      rw [← h]; exact fun hn => hST hn hT
    · change ¬ ¬ InShore RS.edgeOf S (RS.rho xT)
      rw [h, hC.cube]; exact fun hn => hn hS
    · simp only [codeTwo, decide_eq_false_iff_not]
      change ¬ InShore RS.edgeOf T (RS.rho xS) ↔ ¬ InShore RS.edgeOf T (RS.rho (RS.rho xT))
      rw [h, hC.cube]

theorem inl_mem_range_keep_of_not_mid (i : Fin nL) (h : (ℓS i).1 ∉ mid RS.endpoints T) :
    Sum.inl i ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP) := by
  rw [inl_mem_range_keep_iff]
  obtain ⟨hS, _, hvS⟩ := leftMark_facts hC ℓS i
  exact not_other_of_not_mid h hvS hS hdisj (by rw [RS.vert_rho]; exact hvS)

theorem inr_mem_range_keep_of_not_mid (j : Fin nR) (h : (ℓT j).1 ∉ mid RS.endpoints S) :
    Sum.inr j ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP) := by
  rw [inr_mem_range_keep_iff]
  obtain ⟨hT, _, hvT⟩ := rightMark_facts hC ℓT j
  exact not_other_of_not_mid h hvT hT hdisj.symm (by rw [RS.vert_rho]; exact hvT)

/-- **The physical descriptor is legal.**  The only hypothesis beyond the
map's own structure is that the two shores share a vertex. -/
theorem physGlue_legal (L : PhysicalForkCode.Code nL) (R : PhysicalForkCode.Code nR)
    (hL : L.two = codeTwo hC S ℓS) (hR : R.two = codeTwo hC T ℓT)
    (hshare : ∃ v, v ∈ mid RS.endpoints S ∧ v ∈ mid RS.endpoints T) :
    PhysicalForkCode.Legal L R (physGlue hC hdisj ℓS ℓT ℓP) := by
  have hpairL : ∀ i, (ℓS i).1 ∈ mid RS.endpoints T →
      ∃ j, physPair ℓS ℓT (.inl i) = .inr j ∧ (ℓT j).1 = (ℓS i).1 := fun i h =>
    ⟨_, physPair_inl_of_mem ℓS ℓT h, by simp⟩
  have hpairR : ∀ j, (ℓT j).1 ∈ mid RS.endpoints S →
      ∃ i, physPair ℓS ℓT (.inr j) = .inl i ∧ (ℓT j).1 = (ℓS i).1 := fun j h =>
    ⟨_, physPair_inr_of_mem ℓS ℓT h, by simp⟩
  refine ⟨pairFun_involutive ℓS ℓT, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    by_cases h : (ℓS i).1 ∈ mid RS.endpoints T
    · exact Or.inr ⟨_, physPair_inl_of_mem ℓS ℓT h⟩
    · exact Or.inl (physPair_inl_of_not_mem ℓS ℓT h)
  · intro j
    by_cases h : (ℓT j).1 ∈ mid RS.endpoints S
    · exact Or.inr ⟨_, physPair_inr_of_mem ℓS ℓT h⟩
    · exact Or.inl (physPair_inr_of_not_mem ℓS ℓT h)
  · obtain ⟨v, hvS, hvT⟩ := hshare
    refine ⟨.inl (ℓS.symm ⟨v, hvS⟩), ?_⟩
    have h : (ℓS (ℓS.symm ⟨v, hvS⟩)).1 ∈ mid RS.endpoints T := by simpa using hvT
    change physPair ℓS ℓT _ ≠ _
    rw [physPair_inl_of_mem ℓS ℓT h]
    exact Sum.inr_ne_inl
  · rintro (i | j) hx
    · by_cases h : (ℓS i).1 ∈ mid RS.endpoints T
      · obtain ⟨j, hj, hij⟩ := hpairL i h
        change PhysicalForkCode.twoOf _ _ _ = false ∨
          PhysicalForkCode.twoOf _ _ (physPair ℓS ℓT _) = false
        rw [hj]
        simp only [PhysicalForkCode.twoOf, hL, hR]
        rcases shared_cases hC hdisj ℓS ℓT ℓP i j hij with h | h
        · exact Or.inr h.1
        · exact Or.inl h.1
      · exact absurd (physPair_inl_of_not_mem ℓS ℓT h) hx
    · by_cases h : (ℓT j).1 ∈ mid RS.endpoints S
      · obtain ⟨i, hi, hij⟩ := hpairR j h
        change PhysicalForkCode.twoOf _ _ _ = false ∨
          PhysicalForkCode.twoOf _ _ (physPair ℓS ℓT _) = false
        rw [hi]
        simp only [PhysicalForkCode.twoOf, hL, hR]
        rcases shared_cases hC hdisj ℓS ℓT ℓP i j hij with h | h
        · exact Or.inl h.1
        · exact Or.inr h.1
      · exact absurd (physPair_inr_of_not_mem ℓS ℓT h) hx
  · rintro (i | j) hx
    · by_cases h : (ℓS i).1 ∈ mid RS.endpoints T
      · obtain ⟨j, hj, _⟩ := hpairL i h
        exact absurd (show physPair ℓS ℓT (.inl i) = .inl i from hx) (by rw [hj]; exact Sum.inr_ne_inl)
      · exact inl_mem_range_keep_of_not_mid hC hdisj ℓS ℓT ℓP i h
    · by_cases h : (ℓT j).1 ∈ mid RS.endpoints S
      · obtain ⟨i, hi, _⟩ := hpairR j h
        exact absurd (show physPair ℓS ℓT (.inr j) = .inr j from hx) (by rw [hi]; exact Sum.inl_ne_inr)
      · exact inr_mem_range_keep_of_not_mid hC hdisj ℓS ℓT ℓP j h
  · rintro (i | j) hx hopen
    · by_cases h : (ℓS i).1 ∈ mid RS.endpoints T
      · obtain ⟨j, hj, hij⟩ := hpairL i h
        simp only [PhysicalForkCode.OpenAt, physGlue, hj, PhysicalForkCode.twoOf, hL, hR,
          not_and_or, Bool.not_eq_false] at hopen
        change Sum.inl i ∉ Set.range (physKeep hC hdisj ℓS ℓT ℓP)
        rcases shared_cases hC hdisj ℓS ℓT ℓP i j hij with h' | h'
        · exact h'.2.1
        · rcases hopen with hopen | hopen
          · rw [h'.1] at hopen; exact absurd hopen (by decide)
          · rw [h'.2.2]; rw [hopen]; decide
      · exact absurd (physPair_inl_of_not_mem ℓS ℓT h) hx
    · by_cases h : (ℓT j).1 ∈ mid RS.endpoints S
      · obtain ⟨i, hi, hij⟩ := hpairR j h
        simp only [PhysicalForkCode.OpenAt, physGlue, hi, PhysicalForkCode.twoOf, hL, hR,
          not_and_or, Bool.not_eq_false] at hopen
        change Sum.inr j ∉ Set.range (physKeep hC hdisj ℓS ℓT ℓP)
        rcases shared_cases hC hdisj ℓS ℓT ℓP i j hij with h' | h'
        · rcases hopen with hopen | hopen
          · rw [h'.1] at hopen; exact absurd hopen (by decide)
          · rw [h'.2.2]; rw [hopen]; decide
        · exact h'.2.1
      · exact absurd (physPair_inr_of_not_mem ℓS ℓT h) hx
  · rintro (i | j) hx hopen
    · by_cases h : (ℓS i).1 ∈ mid RS.endpoints T
      · obtain ⟨j, hj, hij⟩ := hpairL i h
        simp only [PhysicalForkCode.OpenAt, physGlue, hj, PhysicalForkCode.twoOf, hL, hR] at hopen
        change Sum.inl i ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP) ↔
          physPair ℓS ℓT (.inl i) ∉ Set.range (physKeep hC hdisj ℓS ℓT ℓP)
        rw [hj]
        rcases shared_cases hC hdisj ℓS ℓT ℓP i j hij with h' | h'
        · simp only [h'.2.2, hopen.1, not_true_eq_false, iff_false]; exact h'.2.1
        · simp only [h'.2.2, hopen.2, true_iff]; exact h'.2.1
      · exact absurd (physPair_inl_of_not_mem ℓS ℓT h) hx
    · by_cases h : (ℓT j).1 ∈ mid RS.endpoints S
      · obtain ⟨i, hi, hij⟩ := hpairR j h
        simp only [PhysicalForkCode.OpenAt, physGlue, hi, PhysicalForkCode.twoOf, hL, hR] at hopen
        change Sum.inr j ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP) ↔
          physPair ℓS ℓT (.inr j) ∉ Set.range (physKeep hC hdisj ℓS ℓT ℓP)
        rw [hi]
        rcases shared_cases hC hdisj ℓS ℓT ℓP i j hij with h' | h'
        · simp only [h'.2.2, hopen.2, true_iff]; exact h'.2.1
        · simp only [h'.2.2, hopen.1, not_true_eq_false, iff_false]; exact h'.2.1
      · exact absurd (physPair_inr_of_not_mem ℓS ℓT h) hx

/-- The dart of a kept mark is the parent's interface dart at that position. -/
theorem toMarked_keep_dart (k : Fin nP) :
    (toMarked hC hdisj ℓS ℓT (keepFun hC hdisj ℓS ℓT ℓP k)).1.1 =
      (faceLabel hC (S ∪ T) ℓP k).1 := by
  rw [toMarked_keepFun]; rfl

/-- **Fork correctness for the degree flags.** -/
theorem fork_two (L : PhysicalForkCode.Code nL) (R : PhysicalForkCode.Code nR)
    (hL : L.two = codeTwo hC S ℓS) (hR : R.two = codeTwo hC T ℓT) :
    (PhysicalForkCode.fork L R (physGlue hC hdisj ℓS ℓT ℓP)).two = codeTwo hC (S ∪ T) ℓP := by
  funext k
  have hdart := toMarked_keep_dart hC hdisj ℓS ℓT ℓP k
  have hmem : keepFun hC hdisj ℓS ℓT ℓP k ∈ Set.range (physKeep hC hdisj ℓS ℓT ℓP) := ⟨k, rfl⟩
  simp only [PhysicalForkCode.fork, physGlue]
  change (if physPair ℓS ℓT (keepFun hC hdisj ℓS ℓT ℓP k) = keepFun hC hdisj ℓS ℓT ℓP k
      then PhysicalForkCode.twoOf L R (keepFun hC hdisj ℓS ℓT ℓP k) else true) = _
  have hST : ∀ {d}, InShore RS.edgeOf S d → ¬ InShore RS.edgeOf T d :=
    fun h => not_inShore_right RS.edgeOf S T hdisj h
  generalize hkk : keepFun hC hdisj ℓS ℓT ℓP k = a at hdart hmem
  rcases a with i | j
  · rw [toMarked_inl] at hdart
    obtain ⟨hS, hS', hvS⟩ := leftMark_facts hC ℓS i
    have hx : RS.alpha (faceLabel hC (S ∪ T) ℓP k).1 = RS.alpha (faceLabel hC S ℓS i).1 := by
      rw [hdart]
    simp only [codeTwo, hx]
    by_cases h : (ℓS i).1 ∈ mid RS.endpoints T
    · rw [physPair_inl_of_mem ℓS ℓT h, if_neg Sum.inr_ne_inl]
      set j := ℓT.symm ⟨(ℓS i).1, h⟩
      obtain ⟨hT, _, hvT⟩ := rightMark_facts hC ℓT j
      have hvT' : RS.vertOf (RS.alpha (faceLabel hC T ℓT j).1) =
          RS.vertOf (RS.alpha (faceLabel hC S ℓS i).1) := by
        rw [hvT, hvS]; simp [j]
      have hkeep := (inl_mem_range_keep_iff hC hdisj ℓS ℓT ℓP i).mp hmem
      rcases shared_anatomy hdisj hC hvT' hS hT with ha | ha
      · exact absurd (ha ▸ hT) hkeep
      · symm
        apply decide_eq_true
        rw [← ha]
        exact inShore_right RS.edgeOf S T hT
    · rw [physPair_inl_of_not_mem ℓS ℓT h, if_pos rfl]
      simp only [PhysicalForkCode.twoOf, hL, codeTwo]
      apply Bool.decide_congr
      constructor
      · exact fun hh => inShore_left RS.edgeOf S T hh
      · intro hP
        rcases Finset.mem_union.mp hP with hP | hP
        · exact hP
        · exact absurd hP (not_other_of_not_mid h hvS hS hdisj
            (by rw [RS.vert_rho, RS.vert_rho]; exact hvS))
  · rw [toMarked_inr] at hdart
    obtain ⟨hT, hT', hvT⟩ := rightMark_facts hC ℓT j
    have hx : RS.alpha (faceLabel hC (S ∪ T) ℓP k).1 = RS.alpha (faceLabel hC T ℓT j).1 := by
      rw [hdart]
    simp only [codeTwo, hx]
    by_cases h : (ℓT j).1 ∈ mid RS.endpoints S
    · rw [physPair_inr_of_mem ℓS ℓT h, if_neg Sum.inl_ne_inr]
      set i := ℓS.symm ⟨(ℓT j).1, h⟩
      obtain ⟨hS, _, hvS⟩ := leftMark_facts hC ℓS i
      have hvT' : RS.vertOf (RS.alpha (faceLabel hC T ℓT j).1) =
          RS.vertOf (RS.alpha (faceLabel hC S ℓS i).1) := by
        rw [hvT, hvS]; simp [i]
      have hkeep := (inr_mem_range_keep_iff hC hdisj ℓS ℓT ℓP j).mp hmem
      rcases shared_anatomy hdisj hC hvT' hS hT with ha | ha
      · symm
        apply decide_eq_true
        rw [ha, hC.cube]
        exact inShore_left RS.edgeOf S T hS
      · exact absurd (by rw [ha, hC.cube]; exact hS) hkeep
    · rw [physPair_inr_of_not_mem ℓS ℓT h, if_pos rfl]
      simp only [PhysicalForkCode.twoOf, hR, codeTwo]
      apply Bool.decide_congr
      constructor
      · exact fun hh => inShore_right RS.edgeOf S T hh
      · intro hP
        rcases Finset.mem_union.mp hP with hP | hP
        · exact absurd hP (not_other_of_not_mid h hvT hT hdisj.symm
            (by rw [RS.vert_rho, RS.vert_rho]; exact hvT))
        · exact hP

end Fork2

end

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFaces







