import Mettapedia.GraphTheory.FourColor.FourPortCountRewire

/-!
# Every wire endpoint of a two-vertex deletion is colourable

If a colourable cubic four-port exterior rejects the original two-vertex
connection, it admits a colouring with all four port colours equal.
Consequently every perfect matching of its ports gives a colourable
closed cubic tangle, with the two original vertices removed.

This is an endpoint theorem. Intermediate expansions and reconnections do
not change it if the final graph keeps this exterior and only pairs its
four ports. Larger-footprint moves and changes to the exterior are not
excluded. No planar counterexample is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.FourPortCompositeEndpoint

open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24ClosedCountReplacement GoertzelV24PortTangleCutParity
open GoertzelV24PortTangleCommonKempeWeb GoertzelV24PortTanglePhysicalKempeClosure
open GoertzelV24HexagonPairingTargetAwareBoundary FourPortCountRewire

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

private theorem paired_of_no_extension : ∀ w : SquareBoundaryWord,
    w.Nonzero → (∑ p, w p) = 0 → (¬ ∃ z, IsExtension false w z) →
      w 0 = w 1 ∧ w 2 = w 3 := by
  intro w hn hs hz
  have h01 : w 0 = w 1 := by
    by_contra h
    exact hz ((extension_iff_ne false w hn hs).2 h)
  refine ⟨h01, ?_⟩
  have h23 : ∀ w : SquareBoundaryWord, (∑ p, w p) = 0 →
      w 0 = w 1 → w 2 = w 3 := by decide +kernel
  exact h23 w hs h01

/-- The missing original edge forces two monochromatic port pairs. -/
theorem forced_pairs (T : PortTangle V I (PEmpty.{1} ⊕ Fin 4)) (hT : IsCubic T)
    (hzero : ¬ ClosedColorable T (cap false)) (c : Coloring T) (hc : IsProper c) :
    exteriorWord c 0 = exteriorWord c 1 ∧ exteriorWord c 2 = exteriorWord c 3 := by
  apply paired_of_no_extension _
    ⟨hc.1 (.inr (.inr 0)), hc.1 (.inr (.inr 1)),
     hc.1 (.inr (.inr 2)), hc.1 (.inr (.inr 3))⟩
  · simpa [exteriorWord, Fintype.sum_sum_type] using sum_boundaryWord_eq_zero T hT c hc
  · intro hz
    exact hzero ((closedColorable_cap_iff T false).2 ⟨c, hc, hz⟩)

private theorem exists_pair_swapping : ∀ a b : Color, a ≠ 0 → b ≠ 0 → a ≠ b →
    ∃ pair : TaitColorPair, pairActiveColor pair a ∧ pairActiveColor pair b ∧
      Color.swap pair.colors.1 pair.colors.2 a = b := by
  unfold pairActiveColor Color.twoColor
  decide +kernel

/-- A physical component switch makes both forced pairs have the same colour. -/
theorem exists_monochromatic_coloring
    (T : PortTangle V I (PEmpty.{1} ⊕ Fin 4)) (hT : IsCubic T)
    (hne : ∃ c : Coloring T, IsProper c)
    (hzero : ¬ ClosedColorable T (cap false)) :
    ∃ c : Coloring T, IsProper c ∧ ∃ a : Color, ∀ p, exteriorWord c p = a := by
  classical
  obtain ⟨c, hc⟩ := hne
  have hpairs := forced_pairs T hT hzero c hc
  by_cases hab : exteriorWord c 0 = exteriorWord c 2
  · refine ⟨c, hc, exteriorWord c 0, ?_⟩
    intro p
    fin_cases p
    · rfl
    · exact hpairs.1.symm
    · exact hab.symm
    · exact hpairs.2.symm.trans hab.symm
  obtain ⟨pair, ha, hb, hswap⟩ := exists_pair_swapping
    (exteriorWord c 0) (exteriorWord c 2)
    (hc.1 (.inr (.inr 0))) (hc.1 (.inr (.inr 2))) hab
  have hp : pairActiveDart c pair (.inr (.inr 0)) := ha
  have hq : pairActiveDart c pair (.inr (.inr 1)) := by
    change pairActiveColor pair (exteriorWord c 1)
    rw [← hpairs.1]
    exact ha
  have hr : pairActiveDart c pair (.inr (.inr 2)) := hb
  let selected := fun d => KempeConnected T c pair (.inr (.inr 0)) d
  let region := component_kempeRegion T c pair (.inr (.inr 0)) hp
  let next := switchRegion T c pair selected region
  have hn := switchRegion_isProper T c hc pair selected region
  have hnPairs := forced_pairs T hT hzero next hn
  have hroot : selected (.inr (.inr 0)) := Relation.EqvGen.refl _
  have hn0 : exteriorWord next 0 = exteriorWord c 2 :=
    (switchRegion_color_of_mem T c pair selected region hroot).trans hswap
  have hconn1 : selected (.inr (.inr 1)) := by
    by_contra hnot
    have hn1 : exteriorWord next 1 = exteriorWord c 1 :=
      switchRegion_color_of_not_mem T c pair selected region hnot
    exact hab (hpairs.1.trans (hn1.symm.trans (hnPairs.1.symm.trans hn0)))
  have hnot2 : ¬ selected (.inr (.inr 2)) := by
    intro hconn2
    have hm1 := (physicalMate_eq_iff_of_active T hT c hc pair
      (.inr 0) (.inr 1) hp).2 ⟨by decide, hq, hconn1⟩
    have hm2 := (physicalMate_eq_iff_of_active T hT c hc pair
      (.inr 0) (.inr 2) hp).2 ⟨by decide, hr, hconn2⟩
    exact (by decide : (Sum.inr 1 : PEmpty.{1} ⊕ Fin 4) ≠ .inr 2)
      (hm1.symm.trans hm2)
  have hn2 : exteriorWord next 2 = exteriorWord c 2 :=
    switchRegion_color_of_not_mem T c pair selected region hnot2
  refine ⟨next, hn, exteriorWord c 2, ?_⟩
  intro p
  fin_cases p
  · exact hn0
  · exact hnPairs.1.symm.trans hn0
  · exact hn2
  · exact hnPairs.2.symm.trans hn2

/-- A monochromatic seam has four distinct endpoint vertices by properness. -/
theorem ports_injective_of_zero (T : PortTangle V I (PEmpty.{1} ⊕ Fin 4))
    (hT : IsCubic T) (hne : ∃ c : Coloring T, IsProper c)
    (hzero : ¬ ClosedColorable T (cap false)) :
    Function.Injective (fun p : Fin 4 => T.vert (.inr (.inr p))) := by
  obtain ⟨c, hc, a, hm⟩ := exists_monochromatic_coloring T hT hne hzero
  intro p q he
  by_contra hnepq
  have hd : (Sum.inr (Sum.inr p) : I ⊕ (PEmpty.{1} ⊕ Fin 4)) ≠ .inr (.inr q) := by
    simpa using hnepq
  exact hc.2 _ _ he hd ((hm p).trans (hm q).symm)

/-- Every matching is allowed; cyclic order is not used in the colour theorem. -/
structure Pairing where
  mate : Fin 4 → Fin 4
  involutive : Function.Involutive mate
  fixfree : ∀ p, mate p ≠ p

/-- Move the four boundary darts into the interior carrier; the vertices stay. -/
def wireDartEquiv : ((I ⊕ Fin 4) ⊕ PEmpty.{1}) ≃ (I ⊕ (PEmpty.{1} ⊕ Fin 4)) where
  toFun
    | .inl (.inl i) => .inl i
    | .inl (.inr p) => .inr (.inr p)
    | .inr e => e.elim
  invFun
    | .inl i => .inl (.inl i)
    | .inr (.inl e) => e.elim
    | .inr (.inr p) => .inl (.inr p)
  left_inv := by rintro ((i | p) | e) <;> first | rfl | exact e.elim
  right_inv := by rintro (i | (e | p)) <;> first | rfl | exact e.elim

def wireClosure (T : PortTangle V I (PEmpty.{1} ⊕ Fin 4)) (m : Pairing)
    (hports : Function.Injective (fun p : Fin 4 => T.vert (.inr (.inr p)))) :
    PortTangle V (I ⊕ Fin 4) PEmpty.{1} where
  vert := T.vert ∘ wireDartEquiv
  alpha := Sum.map T.alpha m.mate
  alpha_involutive := by
    rintro (i | p)
    · exact congrArg Sum.inl (T.alpha_involutive i)
    · exact congrArg Sum.inr (m.involutive p)
  alpha_fixfree := by
    rintro (i | p) he
    · exact T.alpha_fixfree i (Sum.inl.inj he)
    · exact m.fixfree p (Sum.inr.inj he)
  no_self_loops := by
    rintro (i | p) he
    · exact T.no_self_loops i he
    · exact m.fixfree p (hports he).symm

omit [Fintype V] [DecidableEq I] in
theorem wireClosure_cubic (T : PortTangle V I (PEmpty.{1} ⊕ Fin 4)) (m : Pairing)
    (hports : Function.Injective (fun p : Fin 4 => T.vert (.inr (.inr p))))
    (hT : IsCubic T) : IsCubic (wireClosure T m hports) := by
  intro v
  have he : {d // (wireClosure T m hports).vert d = v} ≃ {d // T.vert d = v} :=
    Equiv.subtypeEquiv wireDartEquiv (fun _ => Iff.rfl)
  have hh := Fintype.card_congr he
  have hc := hT v
  simp only [Fintype.card_subtype] at hh
  exact hh.trans hc

/-- Any matching endpoint is an actually colourable, closed cubic incidence
structure. No length bound or invariant for the intermediate rewrite path is needed. -/
theorem every_wire_endpoint_colorable
    (T : PortTangle V I (PEmpty.{1} ⊕ Fin 4)) (hT : IsCubic T)
    (hne : ∃ c : Coloring T, IsProper c)
    (hzero : ¬ ClosedColorable T (cap false)) (m : Pairing) :
    Nonempty (Col (wireClosure T m (ports_injective_of_zero T hT hne hzero)) PEmpty.elim) := by
  obtain ⟨c, hc, a, hm⟩ := exists_monochromatic_coloring T hT hne hzero
  let hports := ports_injective_of_zero T hT hne hzero
  let out : Coloring (wireClosure T m hports) :=
    ⟨c.color ∘ wireDartEquiv, by
      rintro (i | p)
      · exact c.invariant i
      · exact (hm (m.mate p)).trans (hm p).symm⟩
  refine ⟨⟨out, ⟨fun d => hc.1 (wireDartEquiv d), ?_⟩, ?_⟩⟩
  · intro d e hv hne'
    exact hc.2 _ _ hv (fun he => hne' (wireDartEquiv.injective he))
  · funext p
    exact p.elim

omit [DecidableEq V] in
/-- The wire endpoint has exactly two fewer vertices than the I closure. -/
theorem endpoint_vertex_count : Fintype.card (V ⊕ Bool) = Fintype.card V + 2 := by simp

end Mettapedia.GraphTheory.FourColor.FourPortCompositeEndpoint
