import Mettapedia.GraphTheory.FourColor.RotationPatchKempe
import Mettapedia.GraphTheory.FourColor.DualTruncateColoring

/-!
# Source choices after a partial Kempe repair

A source colouring is required only on the exterior. A locally saturated
bichromatic vertex region preserves those exterior inequalities. Interior
choices can then be supplied jointly; the theorem does not assume an initial
colouring of the complete source or an extension of its original exterior.
-/

namespace Mettapedia.GraphTheory.FourColor.SourcePatchKempe

open GoertzelV24HexagonPairingTargetAwareBoundary GoertzelV24PortTangleCommonKempeWeb

noncomputable section

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u,u,u} V E) (outside : V → Prop)

def ExteriorProper (c : V → Color) : Prop :=
  (∀ v, outside v → c v ≠ 0) ∧
    ∀ d, outside (RS.vertOf d) → outside (RS.vertOf (RS.alpha d)) →
      c (RS.vertOf d) ≠ c (RS.vertOf (RS.alpha d))

structure Region (c : V → Color) (pair : TaitColorPair) (mask : V → Prop) : Prop where
  active : ∀ v, outside v → mask v → pairActiveColor pair (c v)
  closed : ∀ d, outside (RS.vertOf d) → outside (RS.vertOf (RS.alpha d)) →
    pairActiveColor pair (c (RS.vertOf d)) →
    pairActiveColor pair (c (RS.vertOf (RS.alpha d))) →
    (mask (RS.vertOf d) ↔ mask (RS.vertOf (RS.alpha d)))

def switched (c : V → Color) (pair : TaitColorPair) (mask : V → Prop)
    [DecidablePred mask] (v : V) : Color :=
  if mask v then Color.swap pair.colors.1 pair.colors.2 (c v) else c v

/-- A partial source switch preserves precisely the required exterior
constraints; no assertion about the omitted endpoints is smuggled in. -/
theorem switched_exterior (c : V → Color) (hc : ExteriorProper RS outside c)
    (pair : TaitColorPair) (mask : V → Prop) [DecidablePred mask]
    (region : Region RS outside c pair mask) :
    ExteriorProper RS outside (switched c pair mask) := by
  constructor
  · intro v hv
    by_cases hm : mask v
    · simp only [switched, if_pos hm]
      exact pairSwap_ne_zero pair (hc.1 v hv)
    · simpa only [switched, if_neg hm] using hc.1 v hv
  · intro d hd ha
    let v := RS.vertOf d
    let w := RS.vertOf (RS.alpha d)
    have hne : c v ≠ c w := hc.2 d hd ha
    change (if mask v then Color.swap pair.colors.1 pair.colors.2 (c v) else c v) ≠
      (if mask w then Color.swap pair.colors.1 pair.colors.2 (c w) else c w)
    by_cases hv : mask v <;> by_cases hw : mask w
    · simp only [switched, if_pos hv, if_pos hw]
      exact (pairSwap_injective pair).ne hne
    · simp only [switched, if_pos hv, if_neg hw]
      intro he
      have hwactive : pairActiveColor pair (c w) := by
        rw [← he]
        exact (pairActiveColor_swap_iff pair (c v)).2 (region.active v hd hv)
      exact hw ((region.closed d hd ha (region.active v hd hv) hwactive).1 hv)
    · simp only [switched, if_neg hv, if_pos hw]
      intro he
      have hvactive : pairActiveColor pair (c v) := by
        rw [he]
        exact (pairActiveColor_swap_iff pair (c w)).2 (region.active w ha hw)
      exact hv ((region.closed d hd ha hvactive (region.active w ha hw)).2 hw)
    · simpa only [switched, if_neg hv, if_neg hw] using hne

end
end Mettapedia.GraphTheory.FourColor.SourcePatchKempe
