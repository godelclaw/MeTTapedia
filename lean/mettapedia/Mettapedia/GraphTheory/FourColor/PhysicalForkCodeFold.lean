import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeEuler

/-!
# The finite code of every node of a physical edge-leaf tree

A node with edge shore `S` and a labelling of its middle vertices is encoded by
its degree flags, colour support, face return and cut records.  The fork
theorem assembles the five coordinate theorems: the code of a parent is the
abstract fork of its children's codes under the physical descriptor.  A single
edge is encoded by the fixed `leafCode`, whichever way its two ends are
labelled.  Induction over the tree then places the code of every node of a
connected tree of a spherical map in the closure `Reach`, provided every node
has at most `bound` middle vertices.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFold

open Equiv Equiv.Perm
open GoertzelV24ForkInterfaceSupport GoertzelV24ForkProjection GoertzelV24OrderedCutFaceReturnProfile
open EdgeShoreFaceForkFold PhysicalForkCodeFaces PhysicalForkCodeColour PhysicalForkCodeCut
open PhysicalForkCodeEuler PhysicalForkCode

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable {RS : RotationSystem V E}

/-- The code of an edge shore under a labelling of its middle vertices. -/
def encode (hC : Cubic3 RS) (S : Finset E) {n : ℕ} (ℓ : Fin n ≃ MidVertex RS S) : Code n where
  two := codeTwo hC S ℓ
  colour := codeColour RS S ℓ
  ret := codeRet hC S ℓ
  cut := codeCut RS S ℓ

/-- **The fork theorem.**  The code of a parent shore is the abstract fork of
its children's codes under the physical descriptor. -/
theorem encode_fork (hC : Cubic3 RS)
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ RS.endpoints e).card = 3)
    {S T : Finset E} (hdisj : Disjoint S T)
    {nL nR nP : ℕ} (ℓS : Fin nL ≃ MidVertex RS S) (ℓT : Fin nR ≃ MidVertex RS T)
    (ℓP : Fin nP ≃ MidVertex RS (S ∪ T)) :
    encode hC (S ∪ T) ℓP =
      fork (encode hC S ℓS) (encode hC T ℓT) (physGlue hC hdisj ℓS ℓT ℓP) := by
  ext1
  · exact (fork_two hC hdisj ℓS ℓT ℓP _ _ rfl rfl).symm
  · exact (fork_colour hC hdisj ℓS ℓT ℓP hcubic _ _ rfl rfl).symm
  · exact (fork_ret hC hdisj ℓS ℓT ℓP _ _ rfl rfl).symm
  · exact (fork_cut hC hdisj ℓS ℓT ℓP _ _ rfl rfl).symm

/-! ## A single edge -/

theorem edge_darts (x d : RS.D) : RS.edgeOf d = RS.edgeOf x ↔ d = x ∨ d = RS.alpha x := by
  have h := RS.dartsOn_eq_pair_of_mem (RS.mem_dartsOn.mpr rfl : x ∈ RS.dartsOn (RS.edgeOf x))
  rw [← RS.mem_dartsOn, h]
  simp

theorem rho_rho_ne (hC : Cubic3 RS) (x : RS.D) : RS.rho (RS.rho x) ≠ x := by
  intro h
  apply hC.moves x
  have := congrArg RS.rho h
  rw [hC.cube] at this
  exact this.symm

theorem edge_rho_ne (hC : Cubic3 RS) (x : RS.D) : RS.edgeOf (RS.rho x) ≠ RS.edgeOf x := by
  intro h
  rcases (edge_darts x _).mp h with h | h
  · exact hC.moves x h
  · exact RS.no_self_loops x (by rw [← h, RS.vert_rho])

theorem edge_rho_rho_ne (hC : Cubic3 RS) (x : RS.D) :
    RS.edgeOf (RS.rho (RS.rho x)) ≠ RS.edgeOf x := by
  intro h
  rcases (edge_darts x _).mp h with h | h
  · exact rho_rho_ne hC x h
  · exact RS.no_self_loops x (by rw [← h, RS.vert_rho, RS.vert_rho])

section Leaf

variable (hC : Cubic3 RS) (e : E) (ℓ : Fin 2 ≃ MidVertex RS {e})

theorem inShore_single {d : RS.D} : InShore RS.edgeOf {e} d ↔ RS.edgeOf d = e := by
  simp [InShore]

/-- The last shore dart at the vertex of position `i`. -/
theorem leaf_dart (i : Fin 2) :
    RS.edgeOf (RS.alpha (faceLabel hC {e} ℓ i).1) = e ∧
      RS.vertOf (RS.alpha (faceLabel hC {e} ℓ i).1) = (ℓ i).1 := by
  obtain ⟨hS, _, hv⟩ := leftMark_facts hC ℓ i
  exact ⟨(inShore_single e).mp hS, hv⟩

theorem leaf_two : codeTwo hC {e} ℓ = fun _ => false := by
  funext i
  simp only [codeTwo, decide_eq_false_iff_not]
  obtain ⟨he, _⟩ := leaf_dart hC e ℓ i
  rw [inShore_single]
  exact fun h => edge_rho_rho_ne hC _ (h.trans he.symm)

theorem leaf_ret_apply_ne (i : Fin 2) : codeRet hC {e} ℓ i ≠ i := by
  intro hfix
  set d := faceLabel hC {e} ℓ i with hd
  have hdS : RS.edgeOf d.1 = e := by
    have := d.2.1; exact (inShore_single e).mp this
  have hret : (nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha {e} d).1 = RS.alpha d.1 := by
    rw [nodeRet_eq_raw]
    have hp : ∀ x, ¬ InShore RS.edgeOf {e} x →
        (RS.rho * ofSubtype (shoreEdge RS.alpha RS.edgeOf RS.edge_alpha {e})) x = RS.rho x := by
      intro x hx
      rw [Perm.mul_apply, ofSubtype_apply_of_not_mem _ hx]
    have hq : (RS.rho * ofSubtype (shoreEdge RS.alpha RS.edgeOf RS.edge_alpha {e})) d.1 =
        RS.rho (RS.alpha d.1) := by
      rw [Perm.mul_apply, ofSubtype_apply_of_mem _ d.2.1]; rfl
    have hae : RS.edgeOf (RS.alpha d.1) = e := by rw [RS.edge_alpha]; exact hdS
    have hn1 : ¬ InShore RS.edgeOf {e} (RS.rho (RS.alpha d.1)) := by
      rw [inShore_single]; exact fun h => edge_rho_ne hC _ (h.trans hae.symm)
    have hn2 : ¬ InShore RS.edgeOf {e} (RS.rho (RS.rho (RS.alpha d.1))) := by
      rw [inShore_single]; exact fun h => edge_rho_rho_ne hC _ (h.trans hae.symm)
    rw [nextHit_three _ _ d
      (by rw [hq]; exact fun h => hn1 h.1)
      (by rw [hq, hp _ hn1]; exact fun h => hn2 h.1)
      (by
        rw [hq, hp _ hn1, hp _ hn2, hC.cube]
        refine ⟨(inShore_single e).mpr hae, ?_⟩
        rw [RS.alpha_involutive, inShore_single]
        exact fun h => edge_rho_ne hC _ (h.trans hdS.symm))]
    rw [hq, hp _ hn1, hp _ hn2, hC.cube]
  have hfix' : nodeRet RS.rho RS.alpha RS.edgeOf RS.edge_alpha {e} d = d := by
    have := congrArg (faceLabel hC {e} ℓ) hfix
    simpa [codeRet, Equiv.permCongr_apply, hd] using this
  have := congrArg Subtype.val hfix'
  rw [hret] at this
  exact RS.alpha_fixfree _ this

theorem perm_fin_two_eq_swap (σ : Perm (Fin 2)) (h : ∀ i, σ i ≠ i) : σ = swap 0 1 := by
  ext i
  fin_cases i
  · have := h 0
    have hv : σ 0 = 1 := by omega
    simp [hv]
  · have := h 1
    have hv : σ 1 = 0 := by omega
    simp [hv]

theorem leaf_ret : codeRet hC {e} ℓ = swap 0 1 :=
  perm_fin_two_eq_swap _ (leaf_ret_apply_ne hC e ℓ)

include hC in
theorem leaf_colour : codeColour RS {e} ℓ = leafCode.colour := by
  simp only [codeColour, labelledSupport, leafCode]
  rw [← leafSupport_eq_boundarySupport, leafSupport, Finset.image_image]
  congr 1
  funext c
  funext i
  simp only [Function.comp_apply, labelState, GoertzelV24ForkProjection.restrict, profile]
  obtain ⟨he, hv⟩ := leaf_dart hC e ℓ i
  have hmem : (ℓ i).1 ∈ RS.endpoints e :=
    RS.mem_endpoints_iff.mpr ⟨_, RS.mem_dartsOn.mpr he, hv⟩
  have hfilt : ({e} : Finset E).filter (fun f => (ℓ i).1 ∈ RS.endpoints f) = {e} := by
    ext f; simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · exact fun h => h.1
    · rintro rfl; exact ⟨rfl, hmem⟩
  rw [hfilt]
  simp

/-- The four records of a single edge, indexed by the membership bits of its
two ends. -/
def leafRecord (b : Bool × Bool) : CutRecord 2 :=
  ⟨![b.1, b.2], b.1 || b.2, !(b.1 && b.2), xor b.1 b.2⟩

theorem leafCode_cut_eq : leafCode.cut = Finset.univ.image leafRecord := by
  decide

/-- The ends of the edge, with the two darts over it. -/
theorem leaf_ends :
    let x := RS.alpha (faceLabel hC {e} ℓ 0).1
    RS.edgeOf x = e ∧ RS.vertOf x = (ℓ 0).1 ∧ RS.vertOf (RS.alpha x) = (ℓ 1).1 ∧
      (ℓ 0).1 ≠ (ℓ 1).1 := by
  intro x
  obtain ⟨he0, hv0⟩ := leaf_dart hC e ℓ 0
  obtain ⟨he1, hv1⟩ := leaf_dart hC e ℓ 1
  have hne : (ℓ 0).1 ≠ (ℓ 1).1 := by
    intro h
    have := ℓ.injective (Subtype.ext h)
    exact absurd this (by decide)
  refine ⟨he0, hv0, ?_, hne⟩
  rcases (edge_darts x (RS.alpha (faceLabel hC {e} ℓ 1).1)).mp (he1.trans he0.symm) with h | h
  · exact absurd (hv0.symm.trans ((congrArg RS.vertOf h).symm.trans hv1)) hne
  · rw [← h, hv1]

include hC in
theorem leaf_touched :
    touched RS {e} = {(ℓ 0).1, (ℓ 1).1} := by
  obtain ⟨he, hv0, hv1, _⟩ := leaf_ends hC e ℓ
  generalize RS.alpha (faceLabel hC {e} ℓ 0).1 = x at he hv0 hv1
  ext v
  simp only [mem_touched, Finset.mem_singleton, Finset.mem_insert]
  constructor
  · rintro ⟨d, hdv, hd⟩
    rcases (edge_darts x d).mp (hd.trans he.symm) with rfl | rfl
    · exact Or.inl (hdv.symm.trans hv0)
    · exact Or.inr (hdv.symm.trans hv1)
  · rintro (rfl | rfl)
    · exact ⟨x, hv0, he⟩
    · exact ⟨RS.alpha x, hv1, by rw [RS.edge_alpha]; exact he⟩

include hC in
theorem leaf_cross (U : Finset V) :
    cross RS {e} U =
      (if (ℓ 0).1 ∈ U ∧ (ℓ 1).1 ∉ U then 1 else 0) +
        (if (ℓ 1).1 ∈ U ∧ (ℓ 0).1 ∉ U then 1 else 0) := by
  obtain ⟨he, hv0, hv1, hne⟩ := leaf_ends hC e ℓ
  generalize RS.alpha (faceLabel hC {e} ℓ 0).1 = x at he hv0 hv1
  have hx : x ≠ RS.alpha x := fun h => RS.no_self_loops x (congrArg RS.vertOf h)
  have hset : (Finset.univ.filter fun d =>
      RS.edgeOf d ∈ ({e} : Finset E) ∧ RS.vertOf d ∈ U ∧ RS.vertOf (RS.alpha d) ∉ U) =
      ({x, RS.alpha x} : Finset RS.D).filter
        (fun d => RS.vertOf d ∈ U ∧ RS.vertOf (RS.alpha d) ∉ U) := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
      Finset.mem_insert]
    constructor
    · rintro ⟨hd, hrest⟩
      exact ⟨(edge_darts x d).mp (hd.trans he.symm), hrest⟩
    · rintro ⟨hd, hrest⟩
      refine ⟨?_, hrest⟩
      rcases hd with rfl | rfl
      · exact he
      · rw [RS.edge_alpha]; exact he
  unfold cross
  rw [hset, Finset.filter_insert, Finset.filter_singleton]
  simp only [hv0, hv1, RS.alpha_involutive]
  by_cases h0 : (ℓ 0).1 ∈ U <;> by_cases h1 : (ℓ 1).1 ∈ U <;>
    simp [h0, h1, hx]

include hC in
theorem leaf_record (U : Finset V) (hU : U ⊆ touched RS {e}) :
    cutRecord RS {e} ℓ U = leafRecord (decide ((ℓ 0).1 ∈ U), decide ((ℓ 1).1 ∈ U)) := by
  have ht := leaf_touched hC e ℓ
  rw [ht] at hU
  have hcross := leaf_cross hC e ℓ U
  obtain ⟨_, _, _, hne⟩ := leaf_ends hC e ℓ
  have hsub : ∀ v ∈ U, v = (ℓ 0).1 ∨ v = (ℓ 1).1 := fun v hv => by simpa using hU hv
  have hU' : U = ({(ℓ 0).1, (ℓ 1).1} : Finset V).filter (· ∈ U) := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · intro hv; exact ⟨hsub v hv, hv⟩
    · exact fun h => h.2
  simp only [cutRecord, leafRecord, ht, hcross]
  by_cases h0 : (ℓ 0).1 ∈ U <;> by_cases h1 : (ℓ 1).1 ∈ U
  · have hout : ({(ℓ 0).1, (ℓ 1).1} : Finset V) \ U = ∅ := by
      ext v; simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and, not_not]
      rintro (rfl | rfl) <;> assumption
    ext1
    · funext i; fin_cases i <;> simp [h0, h1]
    · simp [h0, h1]; exact ⟨_, h0⟩
    · simp [hout, h0, h1]
    · simp [h0, h1]
  · have hout : (({(ℓ 0).1, (ℓ 1).1} : Finset V) \ U).Nonempty :=
      ⟨(ℓ 1).1, by simp [h1]⟩
    ext1
    · funext i; fin_cases i <;> simp [h0, h1]
    · simp [h0, h1]; exact ⟨_, h0⟩
    · simp [hout, h0, h1]
    · simp [h0, h1]
  · have hout : (({(ℓ 0).1, (ℓ 1).1} : Finset V) \ U).Nonempty :=
      ⟨(ℓ 0).1, by simp [h0]⟩
    ext1
    · funext i; fin_cases i <;> simp [h0, h1]
    · simp [h0, h1]; exact ⟨_, h1⟩
    · simp [hout, h0, h1]
    · simp [h0, h1]
  · have hempty : U = ∅ := by
      rw [hU']; ext v
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton,
        Finset.notMem_empty, iff_false, not_and]
      rintro (rfl | rfl) <;> assumption
    have hout : (({(ℓ 0).1, (ℓ 1).1} : Finset V) \ U).Nonempty :=
      ⟨(ℓ 0).1, by simp [h0]⟩
    ext1
    · funext i; fin_cases i <;> simp [h0, h1]
    · simp [hempty]
    · simp [hout, h0, h1]
    · simp [h0, h1]

include hC in
theorem leaf_cut : codeCut RS {e} ℓ = leafCode.cut := by
  rw [leafCode_cut_eq]
  have ht := leaf_touched hC e ℓ
  obtain ⟨_, _, _, hne⟩ := leaf_ends hC e ℓ
  ext r
  simp only [codeCut, Finset.mem_image, Finset.mem_filter, Finset.mem_powerset, Finset.mem_univ,
    true_and]
  constructor
  · rintro ⟨U, ⟨hU, _⟩, rfl⟩
    exact ⟨_, (leaf_record hC e ℓ U hU).symm⟩
  · rintro ⟨⟨b0, b1⟩, rfl⟩
    let U : Finset V := ({(ℓ 0).1, (ℓ 1).1} : Finset V).filter
      (fun v => (v = (ℓ 0).1 ∧ b0 = true) ∨ (v = (ℓ 1).1 ∧ b1 = true))
    have hU : U ⊆ touched RS {e} := by rw [ht]; exact Finset.filter_subset _ _
    have h0 : ((ℓ 0).1 ∈ U) ↔ b0 = true := by
      simp [U, hne]
    have h1 : ((ℓ 1).1 ∈ U) ↔ b1 = true := by
      simp [U, hne, Ne.symm hne]
    refine ⟨U, ⟨hU, ?_⟩, ?_⟩
    · rw [leaf_cross hC e ℓ U]
      split_ifs <;> simp_all
    · rw [leaf_record hC e ℓ U hU]
      congr 1
      simp only [Prod.mk.injEq]
      exact ⟨by cases b0 <;> simp_all, by cases b1 <;> simp_all⟩

/-- **A single edge is coded by `leafCode`**, whichever way its ends are
labelled. -/
theorem encode_leaf : encode hC {e} ℓ = leafCode := by
  ext1
  · exact leaf_two hC e ℓ
  · exact leaf_colour hC e ℓ
  · exact leaf_ret hC e ℓ
  · exact leaf_cut hC e ℓ

end Leaf

/-! ## Middle vertices of a single edge, and connected single edges -/

theorem mid_single (hC : Cubic3 RS) (a : RS.D) :
    mid RS.endpoints {RS.edgeOf a} = {RS.vertOf a, RS.vertOf (RS.alpha a)} := by
  ext v
  rw [mem_mid_iff]
  simp only [Finset.mem_singleton, Finset.mem_insert]
  constructor
  · rintro ⟨⟨d, hdv, hd⟩, _⟩
    rcases (edge_darts a d).mp hd with rfl | rfl
    · exact Or.inl hdv.symm
    · exact Or.inr hdv.symm
  · rintro (rfl | rfl)
    · exact ⟨⟨a, rfl, rfl⟩, ⟨RS.rho a, RS.vert_rho a, edge_rho_ne hC a⟩⟩
    · refine ⟨⟨RS.alpha a, rfl, RS.edge_alpha a⟩, ⟨RS.rho (RS.alpha a), RS.vert_rho _, ?_⟩⟩
      intro h
      exact edge_rho_ne hC (RS.alpha a) (h.trans (RS.edge_alpha a).symm)

theorem card_mid_single (hC : Cubic3 RS) (e : E) : (mid RS.endpoints {e}).card = 2 := by
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (RS.dartsOn e).card by
    have := RS.edge_fiber_two e
    unfold RotationSystem.dartsOn
    omega)
  have hae : RS.edgeOf a = e := RS.mem_dartsOn.mp ha
  subst hae
  rw [mid_single hC a, Finset.card_pair (RS.no_self_loops a)]

theorem shoreConnected_single (e : E) : ShoreConnected RS {e} := by
  intro u v hu hv
  obtain ⟨a, hau, hae⟩ := mem_touched.mp hu
  obtain ⟨b, hbv, hbe⟩ := mem_touched.mp hv
  rw [Finset.mem_singleton] at hae hbe
  rcases (edge_darts a b).mp (hbe.trans hae.symm) with rfl | rfl
  · rw [← hau, ← hbv]
  · rw [← hau, ← hbv]
    exact SimpleGraph.Adj.reachable ⟨a, by rw [hae]; exact Finset.mem_singleton_self e, rfl, rfl⟩

/-- Two shores whose union is connected along its own edges share a vertex. -/
theorem exists_shared_of_connected {S T : Finset E} (hdisj : Disjoint S T)
    (hconn : ShoreConnected RS (S ∪ T)) (hS : S.Nonempty) (hT : T.Nonempty) :
    ∃ v, v ∈ mid RS.endpoints S ∧ v ∈ mid RS.endpoints T := by
  obtain ⟨e, he⟩ := hS
  obtain ⟨f, hf⟩ := hT
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (show 0 < (RS.dartsOn e).card by
    have := RS.edge_fiber_two e; unfold RotationSystem.dartsOn; omega)
  obtain ⟨b, hb⟩ := Finset.card_pos.mp (show 0 < (RS.dartsOn f).card by
    have := RS.edge_fiber_two f; unfold RotationSystem.dartsOn; omega)
  have haS : RS.vertOf a ∈ touched RS S := mem_touched.mpr ⟨a, rfl, RS.mem_dartsOn.mp ha ▸ he⟩
  have hbT : RS.vertOf b ∈ touched RS T := mem_touched.mpr ⟨b, rfl, RS.mem_dartsOn.mp hb ▸ hf⟩
  have hu : RS.vertOf a ∈ touched RS (S ∪ T) := by rw [touched_union]; exact Finset.mem_union_left _ haS
  have hw : RS.vertOf b ∈ touched RS (S ∪ T) := by rw [touched_union]; exact Finset.mem_union_right _ hbT
  obtain ⟨p⟩ := hconn _ _ hu hw
  suffices h : ∃ v, v ∈ touched RS S ∧ v ∈ touched RS T by
    obtain ⟨v, hvS, hvT⟩ := h
    exact ⟨v, mid_of_touched_both hdisj hvS hvT⟩
  by_cases hbS : RS.vertOf b ∈ touched RS S
  · exact ⟨_, hbS, hbT⟩
  obtain ⟨dd, _, hx, hy⟩ := p.exists_boundary_dart {v | v ∈ touched RS S} haS hbS
  obtain ⟨d, hd, hdx, hdy⟩ := dd.adj
  rcases Finset.mem_union.mp hd with hdS | hdT
  · exact absurd (by rw [← hdy]; exact alpha_touched hdS) hy
  · exact ⟨dd.fst, hx, mem_touched.mpr ⟨d, hdx, hdT⟩⟩

/-! ## Every node of a good tree is in the closure -/

/-- A tree of connected shores with at most `bound` middle vertices at every
fork. -/
def GoodTree (bound : ℕ) : GoertzelV24ConnectedBranchDecompositionForest.EdgeLeafTree E → Prop
  | .leaf _ => True
  | .fork l r =>
      ShoreConnected RS (GoertzelV24ForkFold.computedShore (.fork l r)) ∧
        (mid RS.endpoints (GoertzelV24ForkFold.computedShore (.fork l r))).card ≤ bound ∧
        GoodTree bound l ∧ GoodTree bound r

theorem shoreConnected_of_goodTree {bound : ℕ} :
    ∀ t : GoertzelV24ConnectedBranchDecompositionForest.EdgeLeafTree E,
      GoodTree (RS := RS) bound t → ShoreConnected RS (GoertzelV24ForkFold.computedShore t)
  | .leaf e, _ => shoreConnected_single e
  | .fork _ _, h => h.1

theorem computedShore_nonempty (t : GoertzelV24ConnectedBranchDecompositionForest.EdgeLeafTree E) :
    (GoertzelV24ForkFold.computedShore t).Nonempty := by
  rw [GoertzelV24ForkFold.computedShore_eq_shore]
  exact t.shore_nonempty

/-- **Physical coverage.**  In a connected spherical map, the code of every
node of a duplicate-free good tree, under any labelling of its middle
vertices, is reachable in the finite closure. -/
theorem reach_encode
    (hsph : GoertzelV24OrbitFaceCurvatureBulk.OrbitSphericalCubicMapData RS)
    (hconn : (GoertzelV24FaceDualConnectedness.rotationPrimalGraph RS).Connected)
    (hrot : GoertzelV24FaceDualConnectedness.VertexRotationCyclic RS)
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ RS.endpoints e).card = 3)
    {bound : ℕ} (hbound : 2 ≤ bound) :
    ∀ (t : GoertzelV24ConnectedBranchDecompositionForest.EdgeLeafTree E)
      (hnodup : t.leafList.Nodup), GoodTree (RS := RS) bound t →
      ∀ {n : ℕ} (ℓ : Fin n ≃ MidVertex RS (GoertzelV24ForkFold.computedShore t)),
        Reach bound n (encode (cubic3_of RS hsph.cubic hrot)
          (GoertzelV24ForkFold.computedShore t) ℓ)
  | .leaf e, _, _, n, ℓ => by
      have hn : n = 2 := by
        have := Fintype.card_congr ℓ
        rw [Fintype.card_fin] at this
        rw [this]
        change Fintype.card {v // v ∈ mid RS.endpoints {e}} = 2
        rw [Fintype.card_coe]
        exact card_mid_single (cubic3_of RS hsph.cubic hrot) e
      subst hn
      exact (congrArg (Reach bound 2)
        (encode_leaf (cubic3_of RS hsph.cubic hrot) e ℓ)).mpr Reach.leaf
  | .fork l r, hnodup, hgood, n, ℓ => by
      have hC := cubic3_of RS hsph.cubic hrot
      have hdisj := shore_disjoint l r hnodup
      have hl := List.Nodup.of_append_left hnodup
      have hr := List.Nodup.of_append_right hnodup
      obtain ⟨hcP, hwP, hgl, hgr⟩ := hgood
      let ℓL := (mid RS.endpoints (GoertzelV24ForkFold.computedShore l)).equivFin.symm
      let ℓR := (mid RS.endpoints (GoertzelV24ForkFold.computedShore r)).equivFin.symm
      have hRL := reach_encode hsph hconn hrot hcubic hbound l hl hgl ℓL
      have hRR := reach_encode hsph hconn hrot hcubic hbound r hr hgr ℓR
      have hn : n ≤ bound := by
        have := Fintype.card_congr ℓ
        rw [Fintype.card_fin, Fintype.card_coe] at this
        rw [this]; exact hwP
      change Reach bound n (encode hC (GoertzelV24ForkFold.computedShore l ∪
        GoertzelV24ForkFold.computedShore r) ℓ)
      rw [encode_fork hC hcubic hdisj ℓL ℓR ℓ]
      have hcl := shoreConnected_of_goodTree l hgl
      have hcr := shoreConnected_of_goodTree r hgr
      refine Reach.fork _ hRL hRR ?_ ?_ hn
      · exact physGlue_legal hC hdisj ℓL ℓR ℓ _ _ rfl rfl
          (exists_shared_of_connected hdisj hcP (computedShore_nonempty l)
            (computedShore_nonempty r))
      · exact physGlue_euler hC hdisj ℓL ℓR ℓ _ _ rfl rfl
          (shore_euler hsph hconn hrot _ hcl (computedShore_nonempty l))
          (shore_euler hsph hconn hrot _ hcr (computedShore_nonempty r))
          (shore_euler hsph hconn hrot _ hcP (computedShore_nonempty (.fork l r)))

/-- Coverage for a tree whose shore is identified with a given edge set. -/
theorem reach_encode_of_eq
    (hsph : GoertzelV24OrbitFaceCurvatureBulk.OrbitSphericalCubicMapData RS)
    (hconn : (GoertzelV24FaceDualConnectedness.rotationPrimalGraph RS).Connected)
    (hrot : GoertzelV24FaceDualConnectedness.VertexRotationCyclic RS)
    (hcubic : ∀ v : V, (Finset.univ.filter fun e => v ∈ RS.endpoints e).card = 3)
    {bound : ℕ} (hbound : 2 ≤ bound)
    (t : GoertzelV24ConnectedBranchDecompositionForest.EdgeLeafTree E)
    (hnodup : t.leafList.Nodup) (hgood : GoodTree (RS := RS) bound t)
    {S : Finset E} (hS : GoertzelV24ForkFold.computedShore t = S)
    {n : ℕ} (ℓ : Fin n ≃ MidVertex RS S) :
    Reach bound n (encode (cubic3_of RS hsph.cubic hrot) S ℓ) := by
  subst hS
  exact reach_encode hsph hconn hrot hcubic hbound t hnodup hgood ℓ

end

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFold


