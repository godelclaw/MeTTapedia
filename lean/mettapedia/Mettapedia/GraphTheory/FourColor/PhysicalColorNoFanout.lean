import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTanglePhysicalKempeClosure

/-!
# A cubic tangle cannot force three distinct boundary ports equal

A proposed physical implementation of shared boundary variables must not
silently introduce a colour-copy tensor. In a nonempty proper-colouring
family, no three distinct boundary ports are always equal: a bichromatic
component reaches just two ports, and switching it breaks the equality.

The result allows any finite interior and additional free ports. It needs
neither planarity nor connectedness. It does not address encoded signals,
frozen auxiliary boundaries, or exterior-dependent operations that do not
implement a universal colour copier.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalColorNoFanout

open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24PortTangleCutParity GoertzelV24PortTangleCommonKempeWeb
open GoertzelV24PortTanglePhysicalKempeClosure GoertzelV24HexagonPairingTargetAwareBoundary

universe u
variable {V I P : Type u} [Fintype V] [Fintype I] [Fintype P]
  [DecidableEq V] [DecidableEq I] [DecidableEq P]

private theorem exists_moving_pair : ∀ a : Color, a ≠ 0 →
    ∃ pair : TaitColorPair, pairActiveColor pair a ∧
      Color.swap pair.colors.1 pair.colors.2 a ≠ a := by
  unfold pairActiveColor Color.twoColor
  decide

/-- One actual Kempe component breaks an equality between three ports.
Other boundary ports are free and may change at the component's second end. -/
theorem exists_split_coloring (T : PortTangle V I P) (hcubic : IsCubic T)
    (c : Coloring T) (hc : IsProper c) (p q r : P)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r)
    (heq : word c p = word c q) (her : word c p = word c r) :
    ∃ c' : Coloring T, IsProper c' ∧
      ¬ (word c' p = word c' q ∧ word c' p = word c' r) := by
  classical
  obtain ⟨pair, ha, hmoving⟩ := exists_moving_pair _ (hc.1 (.inr p))
  have hp : pairActiveDart c pair (.inr p) := ha
  have hq : pairActiveDart c pair (.inr q) := by
    change pairActiveColor pair (word c q)
    rw [← heq]
    exact ha
  have hr : pairActiveDart c pair (.inr r) := by
    change pairActiveColor pair (word c r)
    rw [← her]
    exact ha
  let selected := fun d => KempeConnected T c pair (.inr p) d
  have hfar : ∃ s : P, (s = q ∨ s = r) ∧ ¬ selected (.inr s) := by
    by_cases hconn : selected (.inr q)
    · refine ⟨r, Or.inr rfl, ?_⟩
      intro hconnr
      have hmateq := (physicalMate_eq_iff_of_active T hcubic c hc pair p q hp).2
        ⟨hpq.symm, hq, hconn⟩
      have hmater := (physicalMate_eq_iff_of_active T hcubic c hc pair p r hp).2
        ⟨hpr.symm, hr, hconnr⟩
      exact hqr (hmateq.symm.trans hmater)
    · exact ⟨q, Or.inl rfl, hconn⟩
  obtain ⟨s, hs, hnot⟩ := hfar
  let region := component_kempeRegion T c pair (.inr p) hp
  let next := switchRegion T c pair selected region
  have hnext := switchRegion_isProper T c hc pair selected region
  have hroot : selected (.inr p) := Relation.EqvGen.refl _
  have hnewp : word next p =
      Color.swap pair.colors.1 pair.colors.2 (word c p) :=
    switchRegion_color_of_mem T c pair selected region hroot
  have hnews : word next s = word c s :=
    switchRegion_color_of_not_mem T c pair selected region hnot
  have hold : word c s = word c p := by
    rcases hs with rfl | rfl
    · exact heq.symm
    · exact her.symm
  refine ⟨next, hnext, ?_⟩
  intro he
  have hps : word next p = word next s := by
    rcases hs with rfl | rfl
    · exact he.1
    · exact he.2
  rw [hnewp, hnews, hold] at hps
  exact hmoving hps

/-- No nonvacuous, unrestricted proper-colouring family forces a colour
at one boundary port to be copied to two distinct other boundary ports. -/
theorem not_three_forced_equal (T : PortTangle V I P) (hcubic : IsCubic T)
    (hne : ∃ c : Coloring T, IsProper c) (p q r : P)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬ ∀ c : Coloring T, IsProper c → word c p = word c q ∧ word c p = word c r := by
  intro hall
  obtain ⟨c, hc⟩ := hne
  obtain ⟨c', hc', hsplit⟩ := exists_split_coloring T hcubic c hc p q r hpq hpr hqr
    (hall c hc).1 (hall c hc).2
  exact hsplit (hall c' hc')

/-- The same obstruction is stated on the exact physical support, so it
applies to a proposed tensor realizing a diagonal relation. -/
theorem support_not_subset_diagonal (T : PortTangle V I P) (hcubic : IsCubic T)
    (hne : (taitSupport T).Nonempty) (p q r : P)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ¬ taitSupport T ⊆ {w | w p = w q ∧ w p = w r} := by
  intro hsub
  obtain ⟨w, c, hc, _hw⟩ := hne
  apply not_three_forced_equal T hcubic ⟨c, hc⟩ p q r hpq hpr hqr
  intro d hd
  let boundary : P → {color : Color // color ≠ 0} :=
    fun s => ⟨word d s, hd.1 (.inr s)⟩
  have hmem : boundary ∈ taitSupport T := ⟨d, hd, rfl⟩
  have h := hsub hmem
  exact ⟨congrArg Subtype.val h.1, congrArg Subtype.val h.2⟩

/-- Equality of two literal port colours in every unrestricted proper colouring. -/
def ForcedEqual (T : PortTangle V I P) (p q : P) : Prop :=
  ∀ c : Coloring T, IsProper c → word c p = word c q

/-- Literal forced-equality classes are pairs or singletons, never forks.
Nonemptiness excludes the vacuous relation of an uncolourable tangle. -/
theorem forcedEqual_class_card_le_two (T : PortTangle V I P) (hcubic : IsCubic T)
    (hne : ∃ c : Coloring T, IsProper c) (root : P) :
    Nat.card {p : P // ForcedEqual T root p} ≤ 2 := by
  classical
  let S : Finset P := Finset.univ.filter (ForcedEqual T root)
  have hcard : S.card ≤ 2 := by
    by_contra h
    obtain ⟨p, q, r, hp, hq, hr, hpq, hpr, hqr⟩ :=
      Finset.two_lt_card_iff.mp (Nat.lt_of_not_ge h)
    have hp' : ForcedEqual T root p := (Finset.mem_filter.mp hp).2
    have hq' : ForcedEqual T root q := (Finset.mem_filter.mp hq).2
    have hr' : ForcedEqual T root r := (Finset.mem_filter.mp hr).2
    apply not_three_forced_equal T hcubic hne p q r hpq hpr hqr
    intro c hc
    exact ⟨(hp' c hc).symm.trans (hq' c hc), (hp' c hc).symm.trans (hr' c hc)⟩
  simpa [S, Nat.card_eq_fintype_card, Fintype.card_subtype] using hcard

end Mettapedia.GraphTheory.FourColor.PhysicalColorNoFanout
