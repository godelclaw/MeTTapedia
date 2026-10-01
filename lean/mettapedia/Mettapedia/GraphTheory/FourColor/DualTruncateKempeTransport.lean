import Mettapedia.GraphTheory.FourColor.SourcePatchKempe
import Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatch

/-!
# Exact physical transport of partial source Kempe switches

An exterior source vertex switch determines a saturated region of original
dual-and-truncate edges. Polygon edges follow their source observation; a
cross edge switches only when it has an active colour and meets the selected
source region. Visibility excludes edges wholly inside the omitted patch.
This proves the physical effect uniformly, without a map-specific edge mask
or a complete source colouring.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateKempeTransport

open DualTruncateColoring DualTruncateOpenPatch
open GoertzelV24HexagonPairingTargetAwareBoundary GoertzelV24PortTangleCommonKempeWeb

noncomputable section
set_option backward.isDefEq.respectTransparency false

instance activeColor_decidable (pair : TaitColorPair) : DecidablePred (pairActiveColor pair) := by
  unfold pairActiveColor Color.twoColor
  infer_instance

def star (a b : Color) (i : Fin 3) : Color :=
  if i = 0 then a+b else if i = 1 then b else a

def slotMask (pair : TaitColorPair) (a b : Color) (ma mb : Bool) (i : Fin 3) : Bool :=
  if i = 0 then (ma || mb) && decide (pairActiveColor pair (a+b))
  else if i = 1 then mb else ma

def Admissible (pair : TaitColorPair) (a b : Color) (ma mb : Bool) : Prop :=
  a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
    (ma = true → pairActiveColor pair a) ∧
    (mb = true → pairActiveColor pair b) ∧
    (pairActiveColor pair a → pairActiveColor pair b → ma = mb)

/-- One colour-alphabet law determines the complete local physical update. -/
theorem star_switch (pair : TaitColorPair) (a b : Color) (ma mb : Bool)
    (h : Admissible pair a b ma mb) (i : Fin 3) :
    star (if ma then Color.swap pair.colors.1 pair.colors.2 a else a)
        (if mb then Color.swap pair.colors.1 pair.colors.2 b else b) i =
      if slotMask pair a b ma mb i then
        Color.swap pair.colors.1 pair.colors.2 (star a b i) else star a b i := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a h.1 with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b h.2.1 with rfl | rfl | rfl
  all_goals
    cases pair <;> cases ma <;> cases mb <;> fin_cases i <;>
      revert h <;> unfold Admissible star slotMask pairActiveColor Color.twoColor <;>
      simp only [Set.mem_ofPred_eq] <;> decide +kernel

theorem slotMask_active (pair : TaitColorPair) (a b : Color) (ma mb : Bool)
    (h : Admissible pair a b ma mb) (i : Fin 3) (hm : slotMask pair a b ma mb i = true) :
    pairActiveColor pair (star a b i) := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a h.1 with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b h.2.1 with rfl | rfl | rfl
  all_goals
    cases pair <;> cases ma <;> cases mb <;> fin_cases i <;>
      revert h hm <;> unfold Admissible star slotMask pairActiveColor Color.twoColor <;>
      simp only [Set.mem_ofPred_eq] <;> decide +kernel

set_option maxHeartbeats 2000000 in
theorem slotMask_closed (pair : TaitColorPair) (a b : Color) (ma mb : Bool)
    (h : Admissible pair a b ma mb) (i j : Fin 3)
    (hi : pairActiveColor pair (star a b i))
    (hj : pairActiveColor pair (star a b j)) :
    (slotMask pair a b ma mb i = true ↔ slotMask pair a b ma mb j = true) := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a h.1 with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b h.2.1 with rfl | rfl | rfl
  all_goals
    cases pair <;> cases ma <;> cases mb <;> revert h i j <;>
      unfold Admissible star slotMask pairActiveColor Color.twoColor <;>
      simp only [Set.mem_ofPred_eq] <;> decide +kernel

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u,u,u} V E)

theorem star_colour (c : V → Color) (d : RS.D) (i : Fin 3) :
    edgeColour RS c ((rotation RS).edgeOf (d,i)) =
      star (c (RS.vertOf d)) (c (RS.vertOf (RS.alpha d))) i := by
  fin_cases i
  · exact star_colour_zero RS c d
  · exact star_colour_one RS c d
  · exact star_colour_two RS c d

def touchSource (mask : V → Prop) (e : E) : Prop :=
  ∃ d, RS.edgeOf d = e ∧ (mask (RS.vertOf d) ∨ mask (RS.vertOf (RS.alpha d)))

theorem touchSource_edge (mask : V → Prop) (d : RS.D) :
    touchSource RS mask (RS.edgeOf d) ↔
      mask (RS.vertOf d) ∨ mask (RS.vertOf (RS.alpha d)) := by
  constructor
  · rintro ⟨y,hy,hm⟩
    rcases RS.edge_fiber_two_cases (d := d) rfl hy with rfl | rfl
    · exact hm
    · simpa only [RS.alpha_involutive, or_comm] using hm
  · intro hm
    exact ⟨d,rfl,hm⟩

/-- The edge mask is derived from the original field and source region,
and retains only genuine exterior/cut edges. It does not read new choices. -/
def edgeMask (selected : V → Prop) (c : V → Color) (pair : TaitColorPair)
    (mask : V → Prop) (e : Edge RS) : Prop :=
  VisibleEdge RS (vertexRegion RS selected) e ∧
    match e with
    | .inl e => pairActiveColor pair (edgeColour RS c (.inl e)) ∧ touchSource RS mask e
    | .inr d => mask (RS.vertOf (RS.alpha d))

instance edgeMask_decidable (selected : V → Prop) (c : V → Color) (pair : TaitColorPair)
    (mask : V → Prop) : DecidablePred (edgeMask RS selected c pair mask) := Classical.decPred _

variable (selected : V → Prop) (c : V → Color) (pair : TaitColorPair)
  (mask : V → Prop) [DecidablePred mask]

theorem edgeMask_at_star (d : RS.D) (hd : ¬vertexRegion RS selected d) (i : Fin 3) :
    edgeMask RS selected c pair mask ((rotation RS).edgeOf (d,i)) ↔
      slotMask pair (c (RS.vertOf d)) (c (RS.vertOf (RS.alpha d)))
        (decide (mask (RS.vertOf d))) (decide (mask (RS.vertOf (RS.alpha d)))) i = true := by
  have hv : VisibleEdge RS (vertexRegion RS selected) ((rotation RS).edgeOf (d,i)) :=
    ⟨(d,i),rfl,hd⟩
  unfold edgeMask
  rw [and_iff_right hv]
  fin_cases i
  · simp [DualTruncateColoring.edgeOf, edgeColour, crossColour_edge,
      touchSource_edge, slotMask, and_comm]
  · simp [DualTruncateColoring.edgeOf, slotMask]
  · simp [DualTruncateColoring.edgeOf, slotMask, vert_alpha_phi_symm]

variable (hc : SourcePatchKempe.ExteriorProper RS (fun v => ¬selected v) c)
  (hregion : SourcePatchKempe.Region RS (fun v => ¬selected v) c pair mask)

include hc hregion in
theorem admissible_at (d : RS.D) (hd : ¬vertexRegion RS selected d) :
    Admissible pair (c (RS.vertOf d)) (c (RS.vertOf (RS.alpha d)))
      (decide (mask (RS.vertOf d))) (decide (mask (RS.vertOf (RS.alpha d)))) := by
  have hv : ¬selected (RS.vertOf d) := fun h => hd (Or.inl h)
  have hw : ¬selected (RS.vertOf (RS.alpha d)) := fun h => hd (Or.inr h)
  refine ⟨hc.1 _ hv,hc.1 _ hw,hc.2 d hv hw,?_,?_,?_⟩
  · intro hm
    exact hregion.active _ hv (of_decide_eq_true hm)
  · intro hm
    exact hregion.active _ hw (of_decide_eq_true hm)
  · intro ha hb
    have he := hregion.closed d hv hw ha hb
    by_cases hm : mask (RS.vertOf d)
    · simp [hm,he.1 hm]
    · have hn : ¬mask (RS.vertOf (RS.alpha d)) := fun h => hm (he.2 h)
      simp [hm,hn]

include hc hregion in
/-- A source component becomes a genuine saturated physical edge region
on the original exterior. -/
theorem physical_region :
    RotationPatchKempe.Region (rotation RS) (fun d => ¬vertexRegion RS selected d)
      (edgeColour RS c) pair (edgeMask RS selected c pair mask) := by
  constructor
  · rintro ⟨d,i⟩ hd hm
    have hm' := (edgeMask_at_star RS selected c pair mask d hd i).1 hm
    rw [star_colour RS c d i]
    exact slotMask_active pair _ _ _ _ (admissible_at RS selected c pair mask hc hregion d hd) i hm'
  · rintro ⟨d,i⟩ ⟨e,j⟩ hd hv hi hj
    change d = e at hv
    subst e
    rw [star_colour RS c d i] at hi
    rw [star_colour RS c d j] at hj
    rw [edgeMask_at_star RS selected c pair mask d hd i,
      edgeMask_at_star RS selected c pair mask d hd j]
    exact slotMask_closed pair _ _ _ _ (admissible_at RS selected c pair mask hc hregion d hd)
      i j hi hj

include hc hregion in
/-- The physical switch is exactly the exterior effect of the source switch.
All original incidences and cut observations are retained. -/
theorem exact_effect :
    Extends RS (vertexRegion RS selected)
      (RotationPatchKempe.switched (edgeColour RS c) pair (edgeMask RS selected c pair mask))
      (edgeColour RS (SourcePatchKempe.switched c pair mask)) := by
  intro d hd i
  unfold RotationPatchKempe.switched
  rw [star_colour RS (SourcePatchKempe.switched c pair mask) d i, star_colour RS c d i]
  simp only [edgeMask_at_star RS selected c pair mask d hd i]
  by_cases hv : mask (RS.vertOf d) <;> by_cases hw : mask (RS.vertOf (RS.alpha d)) <;>
    simpa [SourcePatchKempe.switched, hv, hw] using
    star_switch pair _ _ _ _ (admissible_at RS selected c pair mask hc hregion d hd) i

include hc hregion in
/-- Saturation transfers to any actual field with the same exterior
observations. This permits later physical steps in a reconstructed history. -/
theorem physical_region_after (initial : Edge RS → Color)
    (h : Extends RS (vertexRegion RS selected) initial (edgeColour RS c)) :
    RotationPatchKempe.Region (rotation RS) (fun d => ¬vertexRegion RS selected d)
      initial pair (edgeMask RS selected c pair mask) := by
  have hp := physical_region RS selected c pair mask hc hregion
  constructor
  · rintro ⟨d,i⟩ hd hm
    rw [←h d hd i]
    exact hp.active (d,i) hd hm
  · rintro ⟨d,i⟩ ⟨e,j⟩ hd hv hi hj
    change d = e at hv
    subst e
    rw [←h d hd i] at hi
    rw [←h d hd j] at hj
    exact hp.vertex_closed (d,i) (d,j) hd rfl hi hj

include hc hregion in
/-- A later step acts on the genuine preceding physical field. Agreement
at the exterior is enough; no equality at omitted interior edges is needed. -/
theorem exact_effect_after (initial : Edge RS → Color)
    (h : Extends RS (vertexRegion RS selected) initial (edgeColour RS c)) :
    Extends RS (vertexRegion RS selected)
      (RotationPatchKempe.switched initial pair (edgeMask RS selected c pair mask))
      (edgeColour RS (SourcePatchKempe.switched c pair mask)) := by
  intro d hd i
  rw [exact_effect RS selected c pair mask hc hregion d hd i]
  unfold RotationPatchKempe.switched
  split <;> rw [h d hd i]

end
end Mettapedia.GraphTheory.FourColor.DualTruncateKempeTransport
