import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeCut
import Mettapedia.GraphTheory.FourColor.InvolutionEulerDefect
import Mettapedia.GraphTheory.FourColor.GoertzelV24StellarDualStructure

/-!
# The Euler guard at physical forks

The fold's structural state carries `closed`, the number of shore faces that
never reach the interface, as an unrestricted natural number.  The finite code
drops it.  What the code keeps instead is the guard `PhysicalForkCode.Euler`: at
a fork of connected pieces the genus changes by the shared count minus two plus
the children's return cycles minus the cycles of the corrected merged return,
and a planar fork is one where that change vanishes.

This file proves that every fork of a connected edge-leaf tree of a spherical
map satisfies the guard.  The input is Euler's formula for each connected edge
shore of a spherical map, `V_S + F_S = 2 + |S|`.  It is obtained without any
disc or corridor hypothesis: the shore's capped edge presentation has
nonnegative Euler defect, deleting edges cannot increase that defect, and the
whole spherical map has defect zero.  The components of the capped
presentation are one component for the connected shore and one for each
untouched vertex; its faces are the shore faces and one face for each untouched
vertex.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeEuler

open Equiv Equiv.Perm
open GoertzelV24ForkInterfaceSupport GoertzelV24OrderedCutFaceReturnProfile
open EdgeShoreFaceForkFold PhysicalForkCodeFaces PhysicalForkCodeCut
open GoertzelV24FaceDualConnectedness GoertzelV24WordReachability
open GoertzelV24RetainedSpliceFaceCount GoertzelV24FaceOrbitPartitionBridge
open InvolutionRestrictionEdgeList

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

theorem alpha_involutive' : Function.Involutive RS.alpha := RS.alpha_involutive

/-- The edge involution of a shore: the edge flip on shore darts, the identity
on every other dart. -/
def shoreAlpha (S : Finset E) : Perm RS.D :=
  restrict RS.alpha (alpha_involutive' RS) (InShore RS.edgeOf S)
    (fun d => inShore_alpha_iff RS S d)

theorem shoreAlpha_apply (S : Finset E) (d : RS.D) :
    shoreAlpha RS S d = if InShore RS.edgeOf S d then RS.alpha d else d := by
  unfold shoreAlpha
  simp only [restrict_apply]
  by_cases h : InShore RS.edgeOf S d <;> simp [h]

/-- Adjacency along shore edges. -/
def shoreGraph (S : Finset E) : SimpleGraph V where
  Adj u v := ∃ d, RS.edgeOf d ∈ S ∧ RS.vertOf d = u ∧ RS.vertOf (RS.alpha d) = v
  symm := ⟨by
    rintro u v ⟨d, hd, hu, hv⟩
    refine ⟨RS.alpha d, by rw [RS.edge_alpha]; exact hd, hv, ?_⟩
    rw [RS.alpha_involutive, hu]⟩
  loopless := ⟨by
    rintro v ⟨d, _, hu, hv⟩
    exact RS.no_self_loops d (hu.trans hv.symm)⟩

/-- Any two vertices touched by the shore are joined along shore edges. -/
def ShoreConnected (S : Finset E) : Prop :=
  ∀ u v, u ∈ touched RS S → v ∈ touched RS S → (shoreGraph RS S).Reachable u v

variable {RS}

/-! ## Components of the capped presentation -/

/-- One label for all touched vertices, and one for each untouched vertex. -/
def label (S : Finset E) (d : RS.D) : Option {v // v ∉ touched RS S} :=
  if h : RS.vertOf d ∈ touched RS S then none else some ⟨RS.vertOf d, h⟩

theorem label_rho (S : Finset E) (d : RS.D) : label S (RS.rho d) = label S d := by
  simp only [label, RS.vert_rho]

theorem label_shoreAlpha (S : Finset E) (d : RS.D) :
    label S (shoreAlpha RS S d) = label S d := by
  rw [shoreAlpha_apply]
  split_ifs with h
  · have h1 : RS.vertOf (RS.alpha d) ∈ touched RS S := alpha_touched h
    have h2 : RS.vertOf d ∈ touched RS S := mem_touched.mpr ⟨d, rfl, h⟩
    simp only [label, dif_pos h1, dif_pos h2]
  · rfl

theorem label_eq_of_word {S : Finset E} {x y : RS.D}
    (h : WordReachable [RS.rho, shoreAlpha RS S] x y) : label S x = label S y := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
      obtain ⟨g, hg, rfl⟩ := hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl
      · rw [label_rho]; exact ih
      · rw [label_shoreAlpha]; exact ih

theorem word_of_same_vertex (hC : Cubic3 RS) (S : Finset E) {x y : RS.D}
    (h : RS.vertOf y = RS.vertOf x) : WordReachable [RS.rho, shoreAlpha RS S] x y := by
  rcases hC.fiber x y h with rfl | rfl | rfl
  · exact WordReachable.refl _ _
  · exact wordReachable_step (by simp) x
  · exact (wordReachable_step (by simp) x).trans (wordReachable_step (by simp) _)

theorem word_of_walk (hC : Cubic3 RS) (S : Finset E) {u v : V}
    (p : (shoreGraph RS S).Walk u v) :
    ∀ x y : RS.D, RS.vertOf x = u → RS.vertOf y = v →
      WordReachable [RS.rho, shoreAlpha RS S] x y := by
  induction p with
  | nil =>
      intro x y hx hy
      exact word_of_same_vertex hC S (hy.trans hx.symm)
  | cons hadj p ih =>
      intro x y hx hy
      obtain ⟨d, hd, hdu, hdv⟩ := hadj
      have h1 := word_of_same_vertex hC S (x := x) (y := d) (hdu.trans hx.symm)
      have h2 : WordReachable [RS.rho, shoreAlpha RS S] d (RS.alpha d) := by
        have := wordReachable_step (L := [RS.rho, shoreAlpha RS S]) (g := shoreAlpha RS S)
          (by simp) d
        rwa [shoreAlpha_apply, if_pos (show InShore RS.edgeOf S d from hd)] at this
      exact h1.trans (h2.trans (ih _ _ hdv hy))

/-- **Components of a connected shore's capped presentation.** -/
theorem wordOrbitCount_shore (hC : Cubic3 RS) (hsurj : Function.Surjective RS.vertOf)
    (S : Finset E) (hconn : ShoreConnected RS S) (hne : (touched RS S).Nonempty) :
    wordOrbitCount [RS.rho, shoreAlpha RS S] = Fintype.card {v // v ∉ touched RS S} + 1 := by
  let f : Quotient (wordSetoid [RS.rho, shoreAlpha RS S]) → Option {v // v ∉ touched RS S} :=
    Quotient.lift (label S) (fun _ _ h => label_eq_of_word h)
  have hf : Function.Bijective f := by
    constructor
    · intro a b
      induction a using Quotient.inductionOn with
      | h x =>
        induction b using Quotient.inductionOn with
        | h y =>
          intro hxy
          change label S x = label S y at hxy
          apply Quotient.sound
          change WordReachable _ x y
          by_cases hx : RS.vertOf x ∈ touched RS S <;> by_cases hy : RS.vertOf y ∈ touched RS S
          · obtain ⟨p⟩ := hconn _ _ hx hy
            exact word_of_walk hC S p x y rfl rfl
          · simp [label, hx, hy] at hxy
          · simp [label, hx, hy] at hxy
          · simp only [label, dif_neg hx, dif_neg hy, Option.some.injEq, Subtype.mk.injEq] at hxy
            exact word_of_same_vertex hC S hxy.symm
    · rintro (_ | v)
      · obtain ⟨v, hv⟩ := hne
        obtain ⟨d, hd⟩ := hsurj v
        exact ⟨Quotient.mk _ d, by simp [f, label, hd, hv]⟩
      · obtain ⟨d, hd⟩ := hsurj v.1
        exact ⟨Quotient.mk _ d, by simp [f, label, hd, v.2]⟩
  rw [wordOrbitCount, Fintype.card_congr (Equiv.ofBijective f hf), Fintype.card_option]

/-! ## Faces of the capped presentation -/

/-- The capped face permutation of a shore, on the whole dart set. -/
def cappedPhi (S : Finset E) : Perm RS.D := RS.rho * shoreAlpha RS S

theorem cappedPhi_of_not (S : Finset E) {x : RS.D} (hx : ¬ InShore RS.edgeOf S x) :
    cappedPhi (RS := RS) S x = RS.rho x := by
  simp only [cappedPhi, Perm.mul_apply, shoreAlpha_apply, if_neg hx]

theorem shoreAlpha_eq_ofSubtype (S : Finset E) :
    shoreAlpha RS S = ofSubtype (shoreEdge RS.alpha RS.edgeOf RS.edge_alpha S) := by
  ext d
  by_cases h : InShore RS.edgeOf S d
  · rw [shoreAlpha_apply, if_pos h, ofSubtype_apply_of_mem _ h]; rfl
  · rw [shoreAlpha_apply, if_neg h, ofSubtype_apply_of_not_mem _ h]

theorem nextHit_cappedPhi (S : Finset E) :
    nextHitPerm (cappedPhi (RS := RS) S) (InShore RS.edgeOf S) =
      shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha S := by
  rw [shoreFace_eq_raw_return, cappedPhi, shoreAlpha_eq_ofSubtype]

theorem not_inShore_of_untouched {S : Finset E} {x : RS.D}
    (hx : RS.vertOf x ∉ touched RS S) : ¬ InShore RS.edgeOf S x :=
  fun h => hx (mem_touched.mpr ⟨x, rfl, h⟩)

theorem cappedPhi_pow_untouched (S : Finset E) {x : RS.D} (hx : RS.vertOf x ∉ touched RS S)
    (n : ℕ) : (cappedPhi (RS := RS) S ^ n) x = (RS.rho ^ n) x := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hnot : ¬ InShore RS.edgeOf S ((RS.rho ^ n) x) :=
        not_inShore_of_untouched (by rw [vertOf_rho_pow]; exact hx)
      rw [pow_succ', Perm.mul_apply, ih, cappedPhi_of_not S hnot, pow_succ', Perm.mul_apply]

theorem exists_hit_of_touched (hC : Cubic3 RS) (S : Finset E) {x : RS.D}
    (hx : RS.vertOf x ∈ touched RS S) :
    ∃ n, InShore RS.edgeOf S ((cappedPhi (RS := RS) S ^ n) x) := by
  by_cases h0 : InShore RS.edgeOf S x
  · exact ⟨0, h0⟩
  obtain ⟨d, hd, hdS⟩ := mem_touched.mp hx
  rcases hC.fiber x d hd with rfl | rfl | rfl
  · exact absurd hdS h0
  · exact ⟨1, by rw [pow_one, cappedPhi_of_not S h0]; exact hdS⟩
  · by_cases h1 : InShore RS.edgeOf S (RS.rho x)
    · exact ⟨1, by rw [pow_one, cappedPhi_of_not S h0]; exact h1⟩
    · refine ⟨2, ?_⟩
      rw [pow_two, Perm.mul_apply, cappedPhi_of_not S h0, cappedPhi_of_not S h1]
      exact hdS

theorem sameCycle_of_untouched (hC : Cubic3 RS) (S : Finset E) {x y : RS.D}
    (hx : RS.vertOf x ∉ touched RS S) (hy : RS.vertOf y = RS.vertOf x) :
    (cappedPhi (RS := RS) S).SameCycle x y := by
  rcases hC.fiber x y hy with rfl | rfl | rfl
  · exact SameCycle.refl _ _
  · exact ⟨1, by simp only [zpow_one]; rw [cappedPhi_of_not S (not_inShore_of_untouched hx)]⟩
  · refine ⟨2, ?_⟩
    have h2 := cappedPhi_pow_untouched S hx 2
    simp only [zpow_ofNat]
    rw [h2, pow_two, Perm.mul_apply]

/-- Faces of the capped presentation that miss the shore are the untouched
vertices. -/
def nonHitEquiv (hC : Cubic3 RS) (hsurj : Function.Surjective RS.vertOf) (S : Finset E) :
    NonHitOrbit (cappedPhi (RS := RS) S) (InShore RS.edgeOf S) ≃ {v // v ∉ touched RS S} where
  toFun o := ⟨RS.vertOf o.1.out, by
    intro hv
    obtain ⟨n, hn⟩ := exists_hit_of_touched hC S hv
    apply o.2
    refine ⟨_, hn, ?_⟩
    conv_rhs => rw [← Quotient.out_eq o.1]
    apply Quotient.sound
    exact (sameCycle_pow_left.mpr (SameCycle.refl _ _))⟩
  invFun v := ⟨Quotient.mk _ (hsurj v.1).choose, by
    rintro ⟨pt, hpt, hmk⟩
    have hv : RS.vertOf (hsurj v.1).choose ∉ touched RS S := by
      rw [(hsurj v.1).choose_spec]; exact v.2
    have hsc : (cappedPhi (RS := RS) S).SameCycle (hsurj v.1).choose pt :=
      (Quotient.exact hmk).symm
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    rw [← hn, cappedPhi_pow_untouched S hv] at hpt
    exact not_inShore_of_untouched (by rw [vertOf_rho_pow]; exact hv) hpt⟩
  left_inv o := by
    apply Subtype.ext
    change Quotient.mk _ (hsurj (RS.vertOf o.1.out)).choose = o.1
    conv_rhs => rw [← Quotient.out_eq o.1]
    apply Quotient.sound
    have hd := (hsurj (RS.vertOf o.1.out)).choose_spec
    have hout : RS.vertOf o.1.out ∉ touched RS S := by
      intro hv
      obtain ⟨n, hn⟩ := exists_hit_of_touched hC S hv
      apply o.2
      refine ⟨_, hn, ?_⟩
      conv_rhs => rw [← Quotient.out_eq o.1]
      apply Quotient.sound
      exact (sameCycle_pow_left.mpr (SameCycle.refl _ _))
    exact sameCycle_of_untouched hC S (by rw [hd]; exact hout) hd.symm
  right_inv v := by
    apply Subtype.ext
    change RS.vertOf (Quotient.mk (SameCycle.setoid _) (hsurj v.1).choose).out = v.1
    have hv : RS.vertOf (hsurj v.1).choose ∉ touched RS S := by
      rw [(hsurj v.1).choose_spec]; exact v.2
    have hsc : (cappedPhi (RS := RS) S).SameCycle (hsurj v.1).choose
        (Quotient.mk (SameCycle.setoid _) (hsurj v.1).choose).out :=
      (Quotient.exact (Quotient.out_eq (Quotient.mk (SameCycle.setoid _)
        (hsurj v.1).choose))).symm
    obtain ⟨n, hn⟩ := hsc.exists_nat_pow_eq
    rw [← hn, cappedPhi_pow_untouched S hv, vertOf_rho_pow, (hsurj v.1).choose_spec]

/-- **Faces of a shore's capped presentation.** -/
theorem orbitCount_cappedPhi (hC : Cubic3 RS) (hsurj : Function.Surjective RS.vertOf)
    (S : Finset E) :
    GoertzelV24PermutationOrbitSurgery.orbitCount (cappedPhi (RS := RS) S) =
      (shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha S).partition.parts.card +
        Fintype.card {v // v ∉ touched RS S} := by
  unfold GoertzelV24PermutationOrbitSurgery.orbitCount
  rw [card_permOrbit_eq_card_partition_parts, partition_split _ (InShore RS.edgeOf S),
    nextHit_cappedPhi, Fintype.card_congr (nonHitEquiv hC hsurj S)]

/-! ## Euler's formula for connected shores -/

theorem shoreAlpha_univ : shoreAlpha RS Finset.univ = RS.alpha := by
  ext d
  rw [shoreAlpha_apply, if_pos (show InShore RS.edgeOf Finset.univ d from Finset.mem_univ _)]

theorem touched_univ (hsurj : Function.Surjective RS.vertOf) :
    touched RS (Finset.univ : Finset E) = Finset.univ := by
  ext v
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨d, hd⟩ := hsurj v
  exact mem_touched.mpr ⟨d, hd, Finset.mem_univ _⟩

theorem shoreConnected_univ (hconn : (rotationPrimalGraph RS).Connected) :
    ShoreConnected RS (Finset.univ : Finset E) := by
  intro u v _ _
  have hle : rotationPrimalGraph RS ≤ shoreGraph RS Finset.univ := by
    rintro a b ⟨d, ha, hb⟩
    exact ⟨d, Finset.mem_univ _, ha, hb⟩
  exact (hconn.preconnected u v).mono hle

theorem card_moved_shoreAlpha (S : Finset E) :
    (GoertzelV24InvolutionEdgeList.movedFinset (shoreAlpha RS S)).card = 2 * S.card := by
  have hm : GoertzelV24InvolutionEdgeList.movedFinset (shoreAlpha RS S) =
      Finset.univ.filter fun d => RS.edgeOf d ∈ S := by
    ext d
    simp only [GoertzelV24InvolutionEdgeList.mem_movedFinset, Finset.mem_filter,
      Finset.mem_univ, true_and, shoreAlpha_apply]
    by_cases h : InShore RS.edgeOf S d
    · simp only [if_pos h]
      exact ⟨fun _ => h, fun _ => RS.alpha_fixfree d⟩
    · simp only [if_neg h, ne_eq, not_true_eq_false, false_iff]
      exact h
  have hb : (Finset.univ.filter fun d => RS.edgeOf d ∈ S) =
      S.biUnion (fun e => RS.dartsOn e) := by
    ext d
    simp [RotationSystem.dartsOn]
  rw [hm, hb, Finset.card_biUnion]
  · have h2 : ∀ e ∈ S, (RS.dartsOn e).card = 2 := fun e _ => RS.edge_fiber_two e
    rw [Finset.sum_congr rfl h2]
    simp [mul_comm]
  · intro e _ f _ hef
    rw [Function.onFun, Finset.disjoint_left]
    intro d hd hd'
    simp only [RotationSystem.dartsOn, Finset.mem_filter, Finset.mem_univ, true_and] at hd hd'
    exact hef (hd.symm.trans hd')

theorem card_untouched (S : Finset E) :
    Fintype.card {v // v ∉ touched RS S} + (touched RS S).card = Fintype.card V := by
  rw [Fintype.card_subtype_compl, Fintype.card_coe]
  have := Finset.card_le_univ (touched RS S)
  omega

/-- **The whole spherical map has Euler defect zero.** -/
theorem defect_alpha_eq_zero (hsph : GoertzelV24OrbitFaceCurvatureBulk.OrbitSphericalCubicMapData RS)
    (hconn : (rotationPrimalGraph RS).Connected) (hrot : VertexRotationCyclic RS) :
    InvolutionEulerDefect.defect RS.rho RS.alpha = 0 := by
  have hC := cubic3_of RS hsph.cubic hrot
  have hsurj : Function.Surjective RS.vertOf := by
    intro v
    obtain ⟨d, hd⟩ := Finset.card_pos.mp
      (show 0 < (RS.dartsAt v).card by rw [hsph.cubic]; omega)
    exact ⟨d, (Finset.mem_filter.mp hd).2⟩
  have hW := wordOrbitCount_shore hC hsurj Finset.univ (shoreConnected_univ hconn)
    (by rw [touched_univ hsurj]; exact Finset.univ_nonempty_iff.mpr ⟨RS.vertOf RS.outer⟩)
  rw [shoreAlpha_univ] at hW
  have hout : Fintype.card {v // v ∉ touched RS (Finset.univ : Finset E)} = 0 := by
    rw [touched_univ hsurj]; simp
  rw [hout] at hW
  have hmoved := card_moved_shoreAlpha (RS := RS) Finset.univ
  rw [shoreAlpha_univ, Finset.card_univ] at hmoved
  have hrho := GoertzelV24StellarDualStructure.orbitCount_rho_eq_card_vertex RS hrot hsurj
  have hphi : GoertzelV24PermutationOrbitSurgery.orbitCount (RS.rho * RS.alpha) =
      Fintype.card (GoertzelV24FaceOrbitIncidence.OrbitFace RS) := rfl
  have heuler := hsph.euler
  simp only [InvolutionEulerDefect.defect, hmoved, hW, hrho, hphi]
  push_cast
  omega

/-- **Euler's formula for a connected edge shore of a spherical map.** -/
theorem shore_euler (hsph : GoertzelV24OrbitFaceCurvatureBulk.OrbitSphericalCubicMapData RS)
    (hconn : (rotationPrimalGraph RS).Connected) (hrot : VertexRotationCyclic RS)
    (S : Finset E) (hS : ShoreConnected RS S) (hne : S.Nonempty) :
    (touched RS S).card + (shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha S).partition.parts.card =
      2 + S.card := by
  have hC := cubic3_of RS hsph.cubic hrot
  have hsurj : Function.Surjective RS.vertOf := by
    intro v
    obtain ⟨d, hd⟩ := Finset.card_pos.mp
      (show 0 < (RS.dartsAt v).card by rw [hsph.cubic]; omega)
    exact ⟨d, (Finset.mem_filter.mp hd).2⟩
  have hle := InvolutionEulerDefect.defect_restrict_le RS.rho RS.alpha (alpha_involutive' RS)
    (InShore RS.edgeOf S) (fun d => inShore_alpha_iff RS S d)
  have hnn := InvolutionEulerDefect.defect_nonneg RS.rho (shoreAlpha RS S)
    (restrict_involutive _ _ _ _)
  change InvolutionEulerDefect.defect RS.rho (shoreAlpha RS S) ≤ _ at hle
  rw [defect_alpha_eq_zero hsph hconn hrot] at hle
  have htouch : (touched RS S).Nonempty := by
    obtain ⟨e, he⟩ := hne
    obtain ⟨d, hd⟩ := Finset.card_pos.mp (show 0 < (RS.dartsOn e).card by
      have := RS.edge_fiber_two e
      unfold RotationSystem.dartsOn
      omega)
    exact ⟨RS.vertOf d, mem_touched.mpr ⟨d, rfl, (RotationSystem.mem_dartsOn RS).mp hd ▸ he⟩⟩
  have hW := wordOrbitCount_shore hC hsurj S hS htouch
  have hF := orbitCount_cappedPhi hC hsurj S
  have hmoved := card_moved_shoreAlpha (RS := RS) S
  have hrho := GoertzelV24StellarDualStructure.orbitCount_rho_eq_card_vertex RS hrot hsurj
  have hcard := card_untouched (RS := RS) S
  have hzero : InvolutionEulerDefect.defect RS.rho (shoreAlpha RS S) = 0 := le_antisymm hle hnn
  simp only [InvolutionEulerDefect.defect, hmoved, hW, hrho] at hzero
  change _ - 2 * (GoertzelV24PermutationOrbitSurgery.orbitCount (cappedPhi (RS := RS) S) : ℤ) = 0
    at hzero
  rw [hF] at hzero
  push_cast at hzero
  omega

/-! ## The guard at a physical fork -/

section Fork

variable (hC : Cubic3 RS) {S T : Finset E} (hdisj : Disjoint S T)
variable {nL nR nP : ℕ} (ℓS : Fin nL ≃ MidVertex RS S) (ℓT : Fin nR ≃ MidVertex RS T)
  (ℓP : Fin nP ≃ MidVertex RS (S ∪ T))

theorem toMarked_step (L : PhysicalForkCode.Code nL) (R : PhysicalForkCode.Code nR)
    (hL : L.ret = codeRet hC S ℓS) (hR : R.ret = codeRet hC T ℓT) :
    (toMarked hC hdisj ℓS ℓT).permCongr (PhysicalForkCode.merged L R * physPair ℓS ℓT) =
      mergeRet RS.rho RS.alpha RS.edgeOf S T hdisj
          (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha S)
          (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha T) *
        forkRewire RS.rho RS.alpha RS.edgeOf RS.edge_alpha S T hdisj := by
  rw [Equiv.permCongr_mul, toMarked_permCongr_pair]
  congr 1
  rw [← toMarked_merged hC hdisj ℓS ℓT]
  simp only [PhysicalForkCode.merged, hL, hR]

theorem sharedCount_physGlue :
    PhysicalForkCode.sharedCount (physGlue hC hdisj ℓS ℓT ℓP) =
      (touched RS S ∩ touched RS T).card := by
  unfold PhysicalForkCode.sharedCount
  have h1 : (Finset.univ.filter fun i : Fin nL =>
        (physGlue hC hdisj ℓS ℓT ℓP).pair (.inl i) ≠ .inl i) =
      Finset.univ.filter fun i : Fin nL => (ℓS i).1 ∈ mid RS.endpoints T := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change physPair ℓS ℓT (.inl i) ≠ .inl i ↔ _
    by_cases h : (ℓS i).1 ∈ mid RS.endpoints T
    · rw [physPair_inl_of_mem ℓS ℓT h]
      exact ⟨fun _ => h, fun _ => Sum.inr_ne_inl⟩
    · rw [physPair_inl_of_not_mem ℓS ℓT h]
      exact ⟨fun hn => absurd rfl hn, fun hm => absurd hm h⟩
  rw [h1]
  have hinj : Function.Injective (fun i : Fin nL => (ℓS i).1) :=
    Subtype.val_injective.comp ℓS.injective
  rw [← Finset.card_image_of_injective _ hinj]
  congr 1
  ext v
  simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨i, hi, rfl⟩
    exact ⟨mid_subset_touched (ℓS i).2, mid_subset_touched hi⟩
  · rintro ⟨hvS, hvT⟩
    obtain ⟨hmS, hmT⟩ := mid_of_touched_both hdisj hvS hvT
    exact ⟨ℓS.symm ⟨v, hmS⟩, by simpa using hmT, by simp⟩

/-- **Every fork of connected shores in a spherical map is planar.**  The
three shores' Euler formulas and the exact face law of the fork give the
guard of the finite code. -/
theorem physGlue_euler (L : PhysicalForkCode.Code nL) (R : PhysicalForkCode.Code nR)
    (hL : L.ret = codeRet hC S ℓS) (hR : R.ret = codeRet hC T ℓT)
    (hES : (touched RS S).card +
        (shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha S).partition.parts.card = 2 + S.card)
    (hET : (touched RS T).card +
        (shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha T).partition.parts.card = 2 + T.card)
    (hEP : (touched RS (S ∪ T)).card +
        (shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha (S ∪ T)).partition.parts.card =
          2 + (S ∪ T).card) :
    PhysicalForkCode.Euler L R (physGlue hC hdisj ℓS ℓT ℓP) := by
  unfold PhysicalForkCode.Euler PhysicalForkCode.cyc
  rw [sharedCount_physGlue]
  have hLc : L.ret.partition.parts.card =
      (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha S).partition.parts.card := by
    rw [hL, codeRet, card_permCongr_partition_parts]
  have hRc : R.ret.partition.parts.card =
      (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha T).partition.parts.card := by
    rw [hR, codeRet, card_permCongr_partition_parts]
  have hstep : (PhysicalForkCode.merged L R * (physGlue hC hdisj ℓS ℓT ℓP).pair).partition.parts.card =
      (mergeRet RS.rho RS.alpha RS.edgeOf S T hdisj
          (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha S)
          (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha T) *
        forkRewire RS.rho RS.alpha RS.edgeOf RS.edge_alpha S T hdisj).partition.parts.card := by
    rw [← toMarked_step hC hdisj ℓS ℓT L R hL hR, card_permCongr_partition_parts]
    rfl
  have hfaces := forkStep_faces RS.rho RS.alpha RS.edgeOf RS.edge_alpha S T hdisj
  rw [forkStep_eq, nodeState_faces, nodeState_faces, nodeState_faces, mergeRet_card] at hfaces
  have hunion := Finset.card_union_add_card_inter (touched RS S) (touched RS T)
  rw [← touched_union] at hunion
  have hST := Finset.card_union_of_disjoint hdisj
  rw [hLc, hRc, hstep]
  omega

end Fork

end

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeEuler



