import Mettapedia.GraphTheory.FourColor.SourcePatchKempe
import Mettapedia.GraphTheory.FourColor.TwoCellBoundaryChoiceRepair
import Mettapedia.GraphTheory.FourColor.DualTruncateOpenPatch

/-!
# Uniform reconstruction of two coupled source insertions

The frame names two distinct source vertices and their four exterior pins.
Every incidence at either omitted vertex goes to its partner or one of its
two pins. A proper partial exterior and the joint colour contract reconstruct
an actual source colouring, then a genuine dual-and-truncate Tait colouring.
The exterior may be obtained by any justified Kempe history. No full source
colouring or availability of a successful history is assumed.
-/

namespace Mettapedia.GraphTheory.FourColor.TwoCellSourceRepair

open DualTruncateColoring DualTruncateOpenPatch

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u,u,u} V E)

/-- An actual incidence contract; this does not assert any planar order or
occurrence theorem. The pins may coincide if the stated joint contract works. -/
structure Frame where
  left : V
  right : V
  distinct : left ≠ right
  pins : Fin 4 → V
  pins_outside : ∀ i, pins i ≠ left ∧ pins i ≠ right
  left_neighbours : ∀ d, RS.vertOf d = left →
    RS.vertOf (RS.alpha d) = right ∨
      RS.vertOf (RS.alpha d) = pins 0 ∨ RS.vertOf (RS.alpha d) = pins 1
  right_neighbours : ∀ d, RS.vertOf d = right →
    RS.vertOf (RS.alpha d) = left ∨
      RS.vertOf (RS.alpha d) = pins 2 ∨ RS.vertOf (RS.alpha d) = pins 3

namespace Frame

variable {RS}

def outside (frame : Frame RS) (v : V) : Prop := v ≠ frame.left ∧ v ≠ frame.right
def selected (frame : Frame RS) (v : V) : Prop := v = frame.left ∨ v = frame.right

theorem outside_iff_not_selected (frame : Frame RS) (v : V) :
    frame.outside v ↔ ¬frame.selected v := by simp [outside, selected]

theorem outside_eq_not_selected (frame : Frame RS) :
    frame.outside = (fun v => ¬frame.selected v) :=
  funext fun v => propext (frame.outside_iff_not_selected v)

def insert (frame : Frame RS) (c : V → Color) (x y : Color) (v : V) : Color :=
  if v = frame.left then x else if v = frame.right then y else c v

@[simp] theorem insert_left (frame : Frame RS) (c : V → Color) (x y : Color) :
    frame.insert c x y frame.left = x := by simp [insert]

@[simp] theorem insert_right (frame : Frame RS) (c : V → Color) (x y : Color) :
    frame.insert c x y frame.right = y := by simp [insert, frame.distinct.symm]

theorem insert_outside (frame : Frame RS) (c : V → Color) (x y : Color)
    (v : V) (hv : frame.outside v) : frame.insert c x y v = c v := by
  simp only [insert, ite_eq_right hv.1, ite_eq_right hv.2]

theorem insert_pin (frame : Frame RS) (c : V → Color) (x y : Color) (i : Fin 4) :
    frame.insert c x y (frame.pins i) = c (frame.pins i) :=
  frame.insert_outside c x y _ (frame.pins_outside i)

variable (frame : Frame RS) (c : V → Color)
  (hc : SourcePatchKempe.ExteriorProper RS frame.outside c)
  (x y : Color)
  (hxy : TwoCellBoundaryChoice.Compatible (c (frame.pins 0)) (c (frame.pins 1))
    (c (frame.pins 2)) (c (frame.pins 3)) x y)

include hc hxy in
theorem insert_nonzero (v : V) : frame.insert c x y v ≠ 0 := by
  by_cases hl : v = frame.left
  · subst v
    simpa only [insert_left] using hxy.1
  · by_cases hr : v = frame.right
    · subst v
      simpa only [insert_right] using hxy.2.1
    · rw [frame.insert_outside c x y v ⟨hl,hr⟩]
      exact hc.1 v ⟨hl,hr⟩

include hxy in
theorem insert_left_proper (d : RS.D) (hd : RS.vertOf d = frame.left) :
    frame.insert c x y (RS.vertOf d) ≠ frame.insert c x y (RS.vertOf (RS.alpha d)) := by
  rw [hd, insert_left]
  rcases frame.left_neighbours d hd with hr | ha | hb
  · rw [hr, insert_right]
    exact hxy.2.2.2.2.2.2
  · rw [ha, insert_pin]
    exact hxy.2.2.1
  · rw [hb, insert_pin]
    exact hxy.2.2.2.1

include hxy in
theorem insert_right_proper (d : RS.D) (hd : RS.vertOf d = frame.right) :
    frame.insert c x y (RS.vertOf d) ≠ frame.insert c x y (RS.vertOf (RS.alpha d)) := by
  rw [hd, insert_right]
  rcases frame.right_neighbours d hd with hl | ha | hb
  · rw [hl, insert_left]
    exact hxy.2.2.2.2.2.2.symm
  · rw [ha, insert_pin]
    exact hxy.2.2.2.2.1
  · rw [hb, insert_pin]
    exact hxy.2.2.2.2.2.1

include hc hxy in
theorem insert_proper (d : RS.D) :
    frame.insert c x y (RS.vertOf d) ≠ frame.insert c x y (RS.vertOf (RS.alpha d)) := by
  by_cases hl : RS.vertOf d = frame.left
  · exact frame.insert_left_proper c x y hxy d hl
  · by_cases hr : RS.vertOf d = frame.right
    · exact frame.insert_right_proper c x y hxy d hr
    · by_cases hal : RS.vertOf (RS.alpha d) = frame.left
      · have h := frame.insert_left_proper c x y hxy (RS.alpha d) hal
        simpa only [RS.alpha_involutive] using h.symm
      · by_cases har : RS.vertOf (RS.alpha d) = frame.right
        · have h := frame.insert_right_proper c x y hxy (RS.alpha d) har
          simpa only [RS.alpha_involutive] using h.symm
        · rw [frame.insert_outside c x y _ ⟨hl,hr⟩,
            frame.insert_outside c x y _ ⟨hal,har⟩]
          exact hc.2 d ⟨hl,hr⟩ ⟨hal,har⟩

/-- The uniform witness constructor retains both insertions and their seam. -/
def complete : ThreeVertexColoring RS where
  colour := frame.insert c x y
  nonzero := frame.insert_nonzero c hc x y hxy
  proper := frame.insert_proper c hc x y hxy

/-- Actual reconstruction fixes every exterior edge at the supplied
post-history value, including every cut edge. -/
theorem reconstructed_extends :
    Extends RS (vertexRegion RS frame.selected) (edgeColour RS c)
      (DualTruncateColoring.colouring RS (frame.complete c hc x y hxy)) := by
  intro d hd i
  have hl : frame.outside (RS.vertOf d) := by
    constructor <;> intro h
    · exact hd (Or.inl (Or.inl h))
    · exact hd (Or.inl (Or.inr h))
  have hr : frame.outside (RS.vertOf (RS.alpha d)) := by
    constructor <;> intro h
    · exact hd (Or.inr (Or.inl h))
    · exact hd (Or.inr (Or.inr h))
  change edgeColour RS (frame.insert c x y) ((rotation RS).edgeOf (d,i)) =
    edgeColour RS c ((rotation RS).edgeOf (d,i))
  fin_cases i
  · exact (star_colour_zero RS (frame.insert c x y) d).trans
      ((congrArg₂ (· + ·) (frame.insert_outside c x y _ hl)
        (frame.insert_outside c x y _ hr)).trans (star_colour_zero RS c d).symm)
  · exact (star_colour_one RS (frame.insert c x y) d).trans
      ((frame.insert_outside c x y _ hr).trans (star_colour_one RS c d).symm)
  · exact (star_colour_two RS (frame.insert c x y) d).trans
      ((frame.insert_outside c x y _ hl).trans (star_colour_two RS c d).symm)

end Frame

open GoertzelV24HexagonPairingTargetAwareBoundary GoertzelV24PortTangleCommonKempeWeb

/-- A separation condition on an actual source region. The unchanged colour
is inactive, and just one of the two equal active pins belongs to the region.
Availability of this condition is a separate geometric question. -/
structure OnePin (frame : Frame RS) (c : V → Color) (pair : TaitColorPair)
    (mask : V → Prop) (a b : Color) : Prop where
  pins : c (frame.pins 0) = a ∧ c (frame.pins 1) = b ∧
    c (frame.pins 2) = a ∧ c (frame.pins 3) = b
  distinct : a ≠ b
  inactive : ¬pairActiveColor pair a
  swaps : Color.swap pair.colors.1 pair.colors.2 b = a+b
  left_selected : mask (frame.pins 1)
  right_unselected : ¬mask (frame.pins 3)

variable {RS} (frame : Frame RS) (c : V → Color)
  (hc : SourcePatchKempe.ExteriorProper RS frame.outside c)
  (pair : TaitColorPair) (mask : V → Prop) [DecidablePred mask]
  (region : SourcePatchKempe.Region RS frame.outside c pair mask)
  (a b : Color) (contract : OnePin RS frame c pair mask a b)

include region contract in
theorem repaired_pin_values :
    SourcePatchKempe.switched c pair mask (frame.pins 0) = a ∧
    SourcePatchKempe.switched c pair mask (frame.pins 1) = a+b ∧
    SourcePatchKempe.switched c pair mask (frame.pins 2) = a ∧
    SourcePatchKempe.switched c pair mask (frame.pins 3) = b := by
  have hn0 : ¬mask (frame.pins 0) := by
    intro hm
    exact contract.inactive (contract.pins.1 ▸
      region.active _ (frame.pins_outside 0) hm)
  have hn2 : ¬mask (frame.pins 2) := by
    intro hm
    exact contract.inactive (contract.pins.2.2.1 ▸
      region.active _ (frame.pins_outside 2) hm)
  simp only [SourcePatchKempe.switched, ite_eq_right hn0, ite_eq_left contract.left_selected,
    ite_eq_right hn2, ite_eq_right contract.right_unselected, contract.pins.1, contract.pins.2.1,
    contract.pins.2.2.1, contract.pins.2.2.2, contract.swaps, and_self]

include hc region contract in
/-- One shared colour law supplies both interior choices after the physical
separation condition, at any source size. -/
theorem repaired_joint_choices :
    TwoCellBoundaryChoice.Compatible
      (SourcePatchKempe.switched c pair mask (frame.pins 0))
      (SourcePatchKempe.switched c pair mask (frame.pins 1))
      (SourcePatchKempe.switched c pair mask (frame.pins 2))
      (SourcePatchKempe.switched c pair mask (frame.pins 3)) b (a+b) := by
  rcases repaired_pin_values frame c pair mask region a b contract with ⟨h0,h1,h2,h3⟩
  rw [h0,h1,h2,h3]
  have ha : a ≠ 0 := contract.pins.1 ▸ hc.1 _ (frame.pins_outside 0)
  have hb : b ≠ 0 := contract.pins.2.1 ▸ hc.1 _ (frame.pins_outside 1)
  exact TwoCellBoundaryChoice.repair_one_pin a b ha hb contract.distinct

/-- Genuine witness reconstruction from a partial exterior and a separated
region, without supplying a completed colouring or a desired extension. -/
def repairedSource : ThreeVertexColoring RS :=
  frame.complete (SourcePatchKempe.switched c pair mask)
    (SourcePatchKempe.switched_exterior RS frame.outside c hc pair mask region)
    b (a+b) (repaired_joint_choices frame c hc pair mask region a b contract)

end
end Mettapedia.GraphTheory.FourColor.TwoCellSourceRepair
