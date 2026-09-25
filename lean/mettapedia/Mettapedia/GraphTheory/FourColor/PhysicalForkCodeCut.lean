import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeColour
import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality

/-!
# The cut coordinate of the fork fold

Colourability ignores bridges, and a cubic map with a bridge has no Tait
colouring.  A finite closure that forgot bridges would therefore contain
rejecting roots realized by bridged maps, which are not counterexamples.  The
cut coordinate retains exactly what is needed to see them.

For an edge shore `S`, a vertex set `U` of the vertices touched by `S` is
crossed by the shore darts based in `U` whose partner lies outside.  Record,
for every `U` crossed at most once, its bits at the middle positions, whether
`U` and its complement are nonempty, and whether one edge (rather than none)
crosses.  Crossing counts add over disjoint shores, and a vertex touched by
both children is a shared middle vertex, so the records of a parent are
exactly the compatible pairs of child records.  At the root there are no
positions; a record with both flags set is a cut of size at most one, which a
connected bridgeless map does not have.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeCut

open Equiv Equiv.Perm
open GoertzelV24ForkInterfaceSupport
open EdgeShoreFaceForkFold PhysicalForkCodeFaces
open GoertzelV24FaceDualConnectedness GoertzelV24RotationEdgeBridge

noncomputable section
attribute [local instance] Classical.propDecidable

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E)

/-- Vertices touched by a shore. -/
def touched (S : Finset E) : Finset V :=
  Finset.univ.filter fun v => ∃ d, RS.vertOf d = v ∧ RS.edgeOf d ∈ S

/-- Shore darts leaving `U`: one for each shore edge crossing `U`. -/
def cross (S : Finset E) (U : Finset V) : ℕ :=
  (Finset.univ.filter fun d =>
    RS.edgeOf d ∈ S ∧ RS.vertOf d ∈ U ∧ RS.vertOf (RS.alpha d) ∉ U).card

/-- The record of a vertex set, read at the positions of the middle vertices. -/
def cutRecord (S : Finset E) {n : ℕ} (ℓ : Fin n ≃ MidVertex RS S) (U : Finset V) :
    PhysicalForkCode.CutRecord n where
  bits i := decide ((ℓ i).1 ∈ U)
  inside := decide U.Nonempty
  outside := decide (touched RS S \ U).Nonempty
  cost := decide (cross RS S U = 1)

/-- The cut coordinate: records of all touched vertex sets crossed at most once. -/
def codeCut (S : Finset E) {n : ℕ} (ℓ : Fin n ≃ MidVertex RS S) :
    Finset (PhysicalForkCode.CutRecord n) :=
  (((touched RS S).powerset).filter fun U => cross RS S U ≤ 1).image (cutRecord RS S ℓ)

variable {RS}

theorem mem_touched {S : Finset E} {v : V} :
    v ∈ touched RS S ↔ ∃ d, RS.vertOf d = v ∧ RS.edgeOf d ∈ S := by
  simp [touched]

theorem touched_union (S T : Finset E) :
    touched RS (S ∪ T) = touched RS S ∪ touched RS T := by
  ext v
  simp only [mem_touched, Finset.mem_union]
  constructor
  · rintro ⟨d, hv, hd | hd⟩
    · exact Or.inl ⟨d, hv, hd⟩
    · exact Or.inr ⟨d, hv, hd⟩
  · rintro (⟨d, hv, hd⟩ | ⟨d, hv, hd⟩)
    · exact ⟨d, hv, Or.inl hd⟩
    · exact ⟨d, hv, Or.inr hd⟩

theorem alpha_touched {S : Finset E} {d : RS.D} (hd : RS.edgeOf d ∈ S) :
    RS.vertOf (RS.alpha d) ∈ touched RS S :=
  mem_touched.mpr ⟨RS.alpha d, rfl, by rw [RS.edge_alpha]; exact hd⟩

theorem cross_union {S T : Finset E} (hdisj : Disjoint S T) (U : Finset V) :
    cross RS (S ∪ T) U = cross RS S U + cross RS T U := by
  unfold cross
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext d
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    tauto
  · rw [Finset.disjoint_left]
    intro d hdS hdT
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hdS hdT
    exact Finset.disjoint_left.mp hdisj hdS.1 hdT.1

/-- Only the touched part of `U` matters to a shore. -/
theorem cross_inter_touched (S : Finset E) (U : Finset V) :
    cross RS S (U ∩ touched RS S) = cross RS S U := by
  unfold cross
  congr 1
  ext d
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨hd, ⟨hu, _⟩, hout⟩
    exact ⟨hd, hu, fun h => hout ⟨h, alpha_touched hd⟩⟩
  · rintro ⟨hd, hu, hout⟩
    exact ⟨hd, ⟨hu, mem_touched.mpr ⟨d, rfl, hd⟩⟩, fun h => hout h.1⟩

/-- A vertex touched by both of two disjoint shores is a middle vertex of each. -/
theorem mid_of_touched_both {S T : Finset E} (hdisj : Disjoint S T) {v : V}
    (hS : v ∈ touched RS S) (hT : v ∈ touched RS T) :
    v ∈ mid RS.endpoints S ∧ v ∈ mid RS.endpoints T := by
  obtain ⟨a, ha, haS⟩ := mem_touched.mp hS
  obtain ⟨b, hb, hbT⟩ := mem_touched.mp hT
  refine ⟨(mem_mid_iff RS S v).mpr ⟨⟨a, ha, haS⟩, ⟨b, hb, ?_⟩⟩,
    (mem_mid_iff RS T v).mpr ⟨⟨b, hb, hbT⟩, ⟨a, ha, ?_⟩⟩⟩
  · exact fun h => Finset.disjoint_left.mp hdisj h hbT
  · exact fun h => Finset.disjoint_left.mp hdisj haS h

theorem mid_subset_touched {S : Finset E} {v : V} (hv : v ∈ mid RS.endpoints S) :
    v ∈ touched RS S := by
  obtain ⟨⟨d, hd, hdS⟩, _⟩ := (mem_mid_iff RS S v).mp hv
  exact mem_touched.mpr ⟨d, hd, hdS⟩

section Fork

variable (hC : Cubic3 RS) {S T : Finset E} (hdisj : Disjoint S T)
variable {nL nR nP : ℕ} (ℓS : Fin nL ≃ MidVertex RS S) (ℓT : Fin nR ≃ MidVertex RS T)
  (ℓP : Fin nP ≃ MidVertex RS (S ∪ T))

/-- The vertex of a paired pair of positions is the same on both sides. -/
theorem paired_vertex {i : Fin nL} {j : Fin nR}
    (h : physPair ℓS ℓT (.inl i) = .inr j) : (ℓT j).1 = (ℓS i).1 := by
  by_cases hm : (ℓS i).1 ∈ mid RS.endpoints T
  · rw [physPair_inl_of_mem ℓS ℓT hm] at h
    cases h
    simp
  · rw [physPair_inl_of_not_mem ℓS ℓT hm] at h
    cases h

/-- Records of two restrictions of one vertex set agree at every shared vertex. -/
theorem bits_compatible (UA UB : Finset V)
    (hagree : ∀ v, v ∈ touched RS S → v ∈ touched RS T → (v ∈ UA ↔ v ∈ UB)) (x : Fin nL ⊕ Fin nR) :
    PhysicalForkCode.valOf (cutRecord RS S ℓS UA).bits (cutRecord RS T ℓT UB).bits
        ((physGlue hC hdisj ℓS ℓT ℓP).pair x) =
      PhysicalForkCode.valOf (cutRecord RS S ℓS UA).bits (cutRecord RS T ℓT UB).bits x := by
  change PhysicalForkCode.valOf _ _ (physPair ℓS ℓT x) = _
  rcases x with i | j
  · by_cases hm : (ℓS i).1 ∈ mid RS.endpoints T
    · rw [physPair_inl_of_mem ℓS ℓT hm]
      simp only [PhysicalForkCode.valOf, cutRecord]
      have hv : (ℓT (ℓT.symm ⟨(ℓS i).1, hm⟩)).1 = (ℓS i).1 := by simp
      rw [hv]
      exact Bool.decide_congr (hagree _ (mid_subset_touched (ℓS i).2) (mid_subset_touched hm)).symm
    · rw [physPair_inl_of_not_mem ℓS ℓT hm]
  · by_cases hm : (ℓT j).1 ∈ mid RS.endpoints S
    · rw [physPair_inr_of_mem ℓS ℓT hm]
      simp only [PhysicalForkCode.valOf, cutRecord]
      have hv : (ℓS (ℓS.symm ⟨(ℓT j).1, hm⟩)).1 = (ℓT j).1 := by simp
      rw [hv]
      exact Bool.decide_congr (hagree _ (mid_subset_touched hm) (mid_subset_touched (ℓT j).2))
    · rw [physPair_inr_of_not_mem ℓS ℓT hm]

/-- Compatible records glue: their union restricts back to each of them. -/
theorem glue_restrict (UA UB : Finset V) (hA : UA ⊆ touched RS S) (hB : UB ⊆ touched RS T)
    (hbits : ∀ x, PhysicalForkCode.valOf (cutRecord RS S ℓS UA).bits
        (cutRecord RS T ℓT UB).bits ((physGlue hC hdisj ℓS ℓT ℓP).pair x) =
      PhysicalForkCode.valOf (cutRecord RS S ℓS UA).bits (cutRecord RS T ℓT UB).bits x) :
    (UA ∪ UB) ∩ touched RS S = UA ∧ (UA ∪ UB) ∩ touched RS T = UB := by
  have hshared : ∀ v, v ∈ touched RS S → v ∈ touched RS T → (v ∈ UA ↔ v ∈ UB) := by
    intro v hvS hvT
    obtain ⟨hmS, hmT⟩ := mid_of_touched_both hdisj hvS hvT
    set i := ℓS.symm ⟨v, hmS⟩
    have hmi : (ℓS i).1 ∈ mid RS.endpoints T := by simpa [i] using hmT
    have h := hbits (.inl i)
    change PhysicalForkCode.valOf _ _ (physPair ℓS ℓT _) = _ at h
    rw [physPair_inl_of_mem ℓS ℓT hmi] at h
    simp only [PhysicalForkCode.valOf, cutRecord] at h
    have hv : (ℓT (ℓT.symm ⟨(ℓS i).1, hmi⟩)).1 = v := by simp [i]
    have hv' : (ℓS i).1 = v := by simp [i]
    rw [hv, hv'] at h
    exact (decide_eq_decide.mp h).symm
  constructor
  · ext v
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hv | hv, hvS⟩
      · exact hv
      · exact (hshared v hvS (hB hv)).mpr hv
    · intro hv; exact ⟨Or.inl hv, hA hv⟩
  · ext v
    simp only [Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨hv | hv, hvT⟩
      · exact (hshared v (hA hv) hvT).mp hv
      · exact hv
    · intro hv; exact ⟨Or.inr hv, hB hv⟩

/-- The output record of two restrictions is the record of the whole set. -/
theorem cutOut_restrict (U : Finset V) (hU : U ⊆ touched RS (S ∪ T))
    (hcross : cross RS (S ∪ T) U ≤ 1) :
    PhysicalForkCode.cutOut (physGlue hC hdisj ℓS ℓT ℓP)
        (cutRecord RS S ℓS (U ∩ touched RS S)) (cutRecord RS T ℓT (U ∩ touched RS T)) =
      cutRecord RS (S ∪ T) ℓP U := by
  rw [touched_union] at hU
  have hsum := cross_union hdisj (RS := RS) U
  rw [← cross_inter_touched S U, ← cross_inter_touched T U] at hsum
  simp only [PhysicalForkCode.cutOut, cutRecord]
  congr 1
  · funext k
    change PhysicalForkCode.valOf _ _ (keepFun hC hdisj ℓS ℓT ℓP k) = _
    generalize hkk : keepFun hC hdisj ℓS ℓT ℓP k = a
    rcases a with i | j
    · have hv := PhysicalForkCodeColour.keep_vertex_inl hC hdisj ℓS ℓT ℓP hkk
      simp only [PhysicalForkCode.valOf, hv, Finset.mem_inter]
      exact Bool.decide_congr ⟨fun h => h.1, fun h => ⟨h, hv ▸ mid_subset_touched (ℓS i).2⟩⟩
    · have hv := PhysicalForkCodeColour.keep_vertex_inr hC hdisj ℓS ℓT ℓP hkk
      simp only [PhysicalForkCode.valOf, hv, Finset.mem_inter]
      exact Bool.decide_congr ⟨fun h => h.1, fun h => ⟨h, hv ▸ mid_subset_touched (ℓT j).2⟩⟩
  · rw [← Bool.decide_or]
    apply Bool.decide_congr
    constructor
    · rintro (⟨v, hv⟩ | ⟨v, hv⟩)
      · exact ⟨v, (Finset.mem_inter.mp hv).1⟩
      · exact ⟨v, (Finset.mem_inter.mp hv).1⟩
    · rintro ⟨v, hv⟩
      rcases Finset.mem_union.mp (hU hv) with h | h
      · exact Or.inl ⟨v, Finset.mem_inter.mpr ⟨hv, h⟩⟩
      · exact Or.inr ⟨v, Finset.mem_inter.mpr ⟨hv, h⟩⟩
  · rw [← Bool.decide_or, touched_union]
    apply Bool.decide_congr
    constructor
    · rintro (⟨v, hv⟩ | ⟨v, hv⟩)
      · simp only [Finset.mem_sdiff, Finset.mem_inter, not_and] at hv
        exact ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hv.1, fun h => hv.2 h hv.1⟩⟩
      · simp only [Finset.mem_sdiff, Finset.mem_inter, not_and] at hv
        exact ⟨v, Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hv.1, fun h => hv.2 h hv.1⟩⟩
    · rintro ⟨v, hv⟩
      obtain ⟨hv1, hv2⟩ := Finset.mem_sdiff.mp hv
      rcases Finset.mem_union.mp hv1 with h | h
      · exact Or.inl ⟨v, Finset.mem_sdiff.mpr ⟨h, fun h' => hv2 (Finset.mem_inter.mp h').1⟩⟩
      · exact Or.inr ⟨v, Finset.mem_sdiff.mpr ⟨h, fun h' => hv2 (Finset.mem_inter.mp h').1⟩⟩
  · rw [← Bool.decide_or]
    apply Bool.decide_congr
    omega

/-- **Fork correctness for the cut coordinate.** -/
theorem fork_cut (L : PhysicalForkCode.Code nL) (R : PhysicalForkCode.Code nR)
    (hL : L.cut = codeCut RS S ℓS) (hR : R.cut = codeCut RS T ℓT) :
    (PhysicalForkCode.fork L R (physGlue hC hdisj ℓS ℓT ℓP)).cut = codeCut RS (S ∪ T) ℓP := by
  simp only [PhysicalForkCode.fork, hL, hR]
  ext r
  simp only [codeCut, Finset.mem_image, Finset.mem_filter, Finset.mem_product,
    Finset.mem_powerset]
  constructor
  · rintro ⟨⟨rA, rB⟩, ⟨⟨⟨UA, ⟨hA, hcA⟩, rfl⟩, ⟨UB, ⟨hB, hcB⟩, rfl⟩⟩, hbits, hcost⟩, rfl⟩
    obtain ⟨hrA, hrB⟩ := glue_restrict hC hdisj ℓS ℓT ℓP UA UB hA hB hbits
    have hU : UA ∪ UB ⊆ touched RS (S ∪ T) := by
      rw [touched_union]; exact Finset.union_subset_union hA hB
    have hsum := cross_union hdisj (RS := RS) (UA ∪ UB)
    rw [← cross_inter_touched S (UA ∪ UB), ← cross_inter_touched T (UA ∪ UB), hrA, hrB] at hsum
    have hcross : cross RS (S ∪ T) (UA ∪ UB) ≤ 1 := by
      simp only [cutRecord, decide_eq_true_eq, not_and] at hcost
      by_cases h1 : cross RS S UA = 1
      · have := hcost h1; omega
      · omega
    refine ⟨UA ∪ UB, ⟨hU, hcross⟩, ?_⟩
    rw [← cutOut_restrict hC hdisj ℓS ℓT ℓP (UA ∪ UB) hU hcross, hrA, hrB]
  · rintro ⟨U, ⟨hU, hcross⟩, rfl⟩
    have hsum := cross_union hdisj (RS := RS) U
    rw [← cross_inter_touched S U, ← cross_inter_touched T U] at hsum
    refine ⟨(cutRecord RS S ℓS (U ∩ touched RS S), cutRecord RS T ℓT (U ∩ touched RS T)),
      ⟨⟨⟨U ∩ touched RS S, ⟨Finset.inter_subset_right, by omega⟩, rfl⟩,
        ⟨U ∩ touched RS T, ⟨Finset.inter_subset_right, by omega⟩, rfl⟩⟩, ?_, ?_⟩, ?_⟩
    · exact bits_compatible hC hdisj ℓS ℓT ℓP _ _ (fun v hvS hvT => by
        simp only [Finset.mem_inter]; exact ⟨fun h => ⟨h.1, hvT⟩, fun h => ⟨h.1, hvS⟩⟩)
    · simp only [cutRecord, decide_eq_true_eq, not_and]
      intro h1 h2; omega
    · exact cutOut_restrict hC hdisj ℓS ℓT ℓP U hU hcross

end Fork

end

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeCut

