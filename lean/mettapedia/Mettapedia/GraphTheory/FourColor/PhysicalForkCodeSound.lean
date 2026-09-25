import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeGlue

/-!
# Soundness of the fork-code closure

A piece in which every slot is occupied is a cubic map on its own: its darts are
the ends of its edges and the rotation steps through the slots.  The piece
realizing a root code of the closure is of this kind.  So every root code of
the closure `Reach bound` is the root code of an actual cubic map which is
connected and satisfies Euler's formula for the sphere, and which was built by
the forks of the closure itself.

Consequently the audit is exact: a rejecting root code of the closure would be
a connected spherical cubic map with no Tait colouring in which every
nontrivial vertex set is crossed by at least two edges.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodePiece

open Equiv Equiv.Perm
open GoertzelV24ForkInterfaceSupport GoertzelV24OrderedCutFaceReturnProfile
open EdgeShoreFaceForkFold PhysicalForkCodeFaces PhysicalForkCodeCut PhysicalForkCodeEuler
open PhysicalForkCodeFold PhysicalForkCode

noncomputable section
attribute [local instance] Classical.propDecidable

namespace Piece

variable (P : Piece)

/-- Every slot is occupied. -/
def Closed : Prop := ∀ s, P.Filled s

variable {P}

theorem closed_of_openV_empty (h : IsEmpty P.OpenV) : P.Closed := by
  intro s
  by_contra hs
  exact h.false ⟨s.1, ⟨s.2, hs⟩⟩

variable (hP : P.Closed)

/-- The ends of a closed piece fill its slots bijectively. -/
def placeEquiv : P.E × Bool ≃ P.V × ZMod 3 :=
  Equiv.ofBijective P.place ⟨P.place_injective, hP⟩

theorem place_placeEquiv_symm (s : P.V × ZMod 3) : P.place ((placeEquiv hP).symm s) = s :=
  (placeEquiv hP).apply_symm_apply s

theorem placeEquiv_symm_place (x : P.E × Bool) : (placeEquiv hP).symm (P.place x) = x :=
  (placeEquiv hP).symm_apply_apply x

/-- The rotation of a closed piece: the next slot. -/
def rotate : Perm (P.E × Bool) where
  toFun x := (placeEquiv hP).symm ((P.place x).1, (P.place x).2 + 1)
  invFun x := (placeEquiv hP).symm ((P.place x).1, (P.place x).2 - 1)
  left_inv x := by
    simp only [place_placeEquiv_symm, add_sub_cancel_right]
    exact placeEquiv_symm_place hP x
  right_inv x := by
    simp only [place_placeEquiv_symm, sub_add_cancel]
    exact placeEquiv_symm_place hP x

/-- The edge flip of a piece. -/
def flip : Perm (P.E × Bool) where
  toFun x := (x.1, !x.2)
  invFun x := (x.1, !x.2)
  left_inv x := by simp
  right_inv x := by simp

/-- **A closed piece is a map.** -/
abbrev toMap (hne : Nonempty P.E) : RotationSystem.{0, 0, 0} P.V P.E where
  D := P.E × Bool
  edgeOf := Prod.fst
  vertOf x := (P.place x).1
  alpha := flip
  rho := rotate hP
  alpha_involutive x := by simp [flip]
  alpha_fixfree := by
    rintro ⟨e, b⟩
    cases b <;> simp [flip]
  edge_alpha x := rfl
  edge_fiber_two e := by
    have : (Finset.univ.filter fun d : P.E × Bool => d.1 = e) = {(e, false), (e, true)} := by
      ext ⟨e', b⟩
      cases b <;> simp [eq_comm]
    rw [this, Finset.card_pair (by simp)]
  vert_rho x := by
    change (P.place ((placeEquiv hP).symm _)).1 = _
    rw [place_placeEquiv_symm]
  outer := (hne.some, false)
  no_self_loops := by
    rintro ⟨e, b⟩
    cases b
    · exact P.loopless e
    · exact (P.loopless e).symm

variable (hne : Nonempty P.E)

theorem toMap_rho (x : P.E × Bool) :
    (toMap hP hne).rho x = (placeEquiv hP).symm ((P.place x).1, (P.place x).2 + 1) := rfl

/-- The piece embedded in its own map. -/
def selfEmb : Emb P (toMap hP hne) where
  vmap := id
  vmap_injective := Function.injective_id
  emap := id
  emap_injective := Function.injective_id
  smap := (placeEquiv hP).symm
  vertOf_smap s := by
    change (P.place ((placeEquiv hP).symm s)).1 = s.1
    rw [place_placeEquiv_symm]
  rho_smap v k := by
    rw [toMap_rho, place_placeEquiv_symm]
  edgeOf_place x := by
    change ((placeEquiv hP).symm (P.place x)).1 = x.1
    rw [placeEquiv_symm_place]
  alpha_place e b := by
    change flip ((placeEquiv hP).symm (P.place (e, b))) = _
    rw [placeEquiv_symm_place, placeEquiv_symm_place]
    rfl
  open_not_shore s hs := absurd (hP s) hs

theorem toMap_cubic3 : Cubic3 (toMap hP hne) := by
  have hstep : ∀ (x : P.E × Bool) (j : ℕ), ((toMap hP hne).rho ^ j) x =
      (placeEquiv hP).symm ((P.place x).1, (P.place x).2 + j) := by
    intro x j
    induction j with
    | zero =>
      rw [pow_zero, Perm.one_apply, Nat.cast_zero, add_zero, Prod.mk.eta,
        placeEquiv_symm_place]
    | succ j ih =>
        rw [pow_succ', Perm.mul_apply, ih, toMap_rho, place_placeEquiv_symm]
        push_cast
        ring_nf
  refine ⟨fun d => ?_, fun d d' hv => ?_, fun d hd => ?_⟩
  · have := hstep d 3
    simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply] at this
    rw [this]
    rw [show (P.place d).2 + ((3 : ℕ) : ZMod 3) = (P.place d).2 by
      rw [show ((3 : ℕ) : ZMod 3) = 0 by decide, add_zero]]
    exact placeEquiv_symm_place hP d
  · change (P.place d').1 = (P.place d).1 at hv
    have hd' : d' = (placeEquiv hP).symm ((P.place d).1, (P.place d').2) := by
      rw [← hv, Prod.mk.eta, placeEquiv_symm_place]
    rcases zmod3_cases ((P.place d').2 - (P.place d).2) with h0 | h1 | h2
    · left
      rw [hd', sub_eq_zero.mp h0, Prod.mk.eta, placeEquiv_symm_place]
    · right; left
      rw [hd', toMap_rho]
      congr 2
      rw [sub_eq_iff_eq_add] at h1; rw [h1]; ring
    · right; right
      have := hstep d 2
      simp only [pow_succ, pow_zero, one_mul, Perm.mul_apply] at this
      rw [this, hd']
      congr 2
      rw [sub_eq_iff_eq_add] at h2; rw [h2]; push_cast; ring
  · rw [toMap_rho] at hd
    have := congrArg P.place hd
    rw [place_placeEquiv_symm] at this
    have h2 := congrArg Prod.snd this
    exact (zmod3_add_ne _).1 h2

theorem toMap_isCubic : (toMap hP hne).IsCubic := by
  intro v
  have : (toMap hP hne).dartsAt v = Finset.univ.image fun k : ZMod 3 => (placeEquiv hP).symm (v, k) := by
    ext x
    simp only [RotationSystem.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_image]
    constructor
    · intro hx
      exact ⟨(P.place x).2, by rw [← hx]; exact placeEquiv_symm_place hP x⟩
    · rintro ⟨k, rfl⟩
      rw [place_placeEquiv_symm]
  rw [this, Finset.card_image_of_injective _ (fun a b hab => by
    have := congrArg (fun y => (P.place y).2) hab
    simpa [place_placeEquiv_symm] using this)]
  rfl

theorem selfEmb_shore : (selfEmb hP hne).shore = Finset.univ := by
  ext e
  simp [Emb.shore, selfEmb]

end Piece

/-! ## Root codes of the closure are maps -/

/-- **Soundness of the closure at the root.**  Every root code of the closure is
the root code of a cubic map that is connected, satisfies Euler's formula for
the sphere, and is glued from single edges by the forks of the closure. -/
theorem reach_root_realized {bound : ℕ} {c : Code 0} (hc : Reach bound 0 c) :
    ∃ (V E : Type) (_ : Fintype V) (_ : DecidableEq V) (_ : Fintype E) (_ : DecidableEq E)
      (RS : RotationSystem.{0, 0, 0} V E) (hC : Cubic3 RS),
      RS.IsCubic ∧ ShoreConnected RS Finset.univ ∧
      (touched RS Finset.univ).card +
          (shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha Finset.univ).partition.parts.card =
        2 + (Finset.univ : Finset E).card ∧
      encode hC Finset.univ PhysicalForkCodeBase.rootLabel = c := by
  obtain ⟨P, ℓ, hR, hne⟩ := reach_realized hc
  have hP : P.Closed := Piece.closed_of_openV_empty ℓ.symm.isEmpty
  set RS := Piece.toMap hP hne
  have hC := Piece.toMap_cubic3 hP hne
  have hcub := Piece.toMap_isCubic hP hne
  obtain ⟨hcode, hconn, heul⟩ := hR.shore RS hC
    (PhysicalForkCodeBase.endpoints_cubic hcub) (Piece.selfEmb hP hne)
  have hS := Piece.selfEmb_shore hP hne
  refine ⟨P.V, P.E, inferInstance, inferInstance, inferInstance, inferInstance, RS, hC, hcub,
    ?_, ?_, ?_⟩
  · rw [← hS]; exact hconn
  · rw [← hS]; exact heul
  · rw [← hcode]
    exact encode_congr hC hS.symm _ _ (fun k => k.elim0)

/-- The root code has no small cut exactly when every nontrivial vertex set of
the map is crossed by at least two edges. -/
theorem not_hasSmallCut_iff {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E]
    [DecidableEq E] {RS : RotationSystem V E} (hC : Cubic3 RS)
    (ℓ : Fin 0 ≃ MidVertex RS (Finset.univ : Finset E)) :
    ¬ HasSmallCut (encode hC Finset.univ ℓ) ↔
      ∀ U : Finset V, U ⊆ touched RS Finset.univ → U.Nonempty →
        (touched RS Finset.univ \ U).Nonempty → 1 < cross RS Finset.univ U := by
  constructor
  · intro h U hU hin hout
    by_contra hle
    apply h
    refine ⟨cutRecord RS Finset.univ ℓ U, Finset.mem_image.mpr ⟨U,
      Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr hU, by omega⟩, rfl⟩, ?_, ?_⟩
    · simp [cutRecord, hin]
    · simp [cutRecord, hout]
  · rintro h ⟨r, hr, hin, hout⟩
    obtain ⟨U, hUmem, rfl⟩ := Finset.mem_image.mp hr
    obtain ⟨hU, hcross⟩ := Finset.mem_filter.mp hUmem
    simp only [cutRecord, decide_eq_true_eq] at hin hout
    have := h U (Finset.mem_powerset.mp hU) hin hout
    omega

/-- **The audit is exact.**  A rejecting root code of the closure is the root
code of a connected cubic map satisfying Euler's formula for the sphere, with no
Tait colouring, in which every nontrivial vertex set is crossed by at least two
edges. -/
theorem rejecting_root_realized {bound : ℕ} {c : Code 0} (hc : Reach bound 0 c)
    (hrej : Rejecting c) :
    ∃ (V E : Type) (_ : Fintype V) (_ : DecidableEq V) (_ : Fintype E) (_ : DecidableEq E)
      (RS : RotationSystem.{0, 0, 0} V E) (_ : Cubic3 RS),
      RS.IsCubic ∧ ShoreConnected RS Finset.univ ∧
      (touched RS Finset.univ).card +
          (shoreFace RS.rho RS.alpha RS.edgeOf RS.edge_alpha Finset.univ).partition.parts.card =
        2 + (Finset.univ : Finset E).card ∧
      ¬ GoertzelV24TwoEdgeCutMinimality.RotationSystemTaitColorable RS ∧
      ∀ U : Finset V, U ⊆ touched RS Finset.univ → U.Nonempty →
        (touched RS Finset.univ \ U).Nonempty → 1 < cross RS Finset.univ U := by
  obtain ⟨V, E, i1, i2, i3, i4, RS, hC, hcub, hconn, heul, hcode⟩ := reach_root_realized hc
  refine ⟨V, E, i1, i2, i3, i4, RS, hC, hcub, hconn, heul, ?_, ?_⟩
  · rw [← PhysicalForkCodeBase.root_colour_eq_empty_iff hC PhysicalForkCodeBase.rootLabel, hcode]
    exact hrej.1
  · rw [← not_hasSmallCut_iff hC PhysicalForkCodeBase.rootLabel, hcode]
    exact hrej.2

end

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodePiece
