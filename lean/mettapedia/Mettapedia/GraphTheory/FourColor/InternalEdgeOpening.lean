import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic

/-!
# Opening internal edges does not preserve their forced equality

The triangular prism has two cofacial internal edges equal in every
proper three-edge-colouring. Cutting those edges into four free ports
introduces proper colourings that cannot be reclosed. This is an endpoint
model of the actual surgery, not an abstract boundary language.

It invalidates applying free-port no-fanout to a reclosure-conditioned
colouring family. It does not give a counterexample to spherical 4CT.
Planarity and the port order of the explicit drawing are checked separately
by the constructor gate; the statements below concern literal incidence.
-/

namespace Mettapedia.GraphTheory.FourColor.InternalEdgeOpening

def Touch {V E : Type*} (ends : E → V × V) (e f : E) : Prop :=
  (ends e).1 = (ends f).1 ∨ (ends e).1 = (ends f).2 ∨
  (ends e).2 = (ends f).1 ∨ (ends e).2 = (ends f).2

instance {V E : Type*} [DecidableEq V] (ends : E → V × V) (e f : E) :
    Decidable (Touch ends e f) :=
  inferInstanceAs (Decidable ((ends e).1 = (ends f).1 ∨ (ends e).1 = (ends f).2 ∨
    (ends e).2 = (ends f).1 ∨ (ends e).2 = (ends f).2))

/-- Proper edge colouring on an explicit endpoint carrier. -/
def Proper {V E : Type*} (ends : E → V × V) (c : E → Fin 3) : Prop :=
  ∀ e f, e ≠ f → Touch ends e f → c e ≠ c f

instance {V E : Type*} [DecidableEq V] [Fintype E] [DecidableEq E]
    (ends : E → V × V) (c : E → Fin 3) : Decidable (Proper ends c) :=
  inferInstanceAs (Decidable (∀ e f, e ≠ f → Touch ends e f → c e ≠ c f))

def closedEnds : Fin 9 → Fin 6 × Fin 6 :=
  ![(0,1), (1,2), (2,0), (3,4), (4,5), (5,3), (0,3), (1,4), (2,5)]

/-- The first seven edges survive unchanged. The last four lead to
degree-one terminals; their incident prism vertices remain cubic. -/
def openEnds : Fin 11 → Fin 10 × Fin 10 :=
  ![(1,2), (2,0), (4,5), (5,3), (0,3), (1,4), (2,5),
    (0,6), (1,7), (3,8), (4,9)]

def cut (c : Fin 9 → Fin 3) : Fin 11 → Fin 3 :=
  ![c 1, c 2, c 4, c 5, c 6, c 7, c 8, c 0, c 0, c 3, c 3]

def Reclosable (c : Fin 11 → Fin 3) : Prop := c 7 = c 8 ∧ c 9 = c 10
  deriving Decidable

def glue (c : Fin 11 → Fin 3) : Fin 9 → Fin 3 :=
  ![c 7, c 0, c 1, c 9, c 2, c 3, c 4, c 5, c 6]

theorem glue_cut (c : Fin 9 → Fin 3) : glue (cut c) = c := by
  ext i; fin_cases i <;> rfl

theorem cut_glue (c : Fin 11 → Fin 3) (h : Reclosable c) : cut (glue c) = c := by
  ext i
  fin_cases i <;> simp [cut, glue, Reclosable] at * <;> aesop

def closedWitness : Fin 9 → Fin 3 := ![0,1,2,0,1,2,1,2,0]

theorem closedWitness_proper : Proper closedEnds closedWitness := by decide +kernel

private theorem third_unique : ∀ a b x y : Fin 3,
    a ≠ b → x ≠ a → x ≠ b → y ≠ a → y ≠ b → x = y := by decide

theorem closed_forces_equal (c : Fin 9 → Fin 3)
    (h : Proper closedEnds c) : c 0 = c 3 := by
  have h61 : c 6 = c 1 := third_unique _ _ _ _
    (h 0 2 (by decide) (by decide))
    (h 6 0 (by decide) (by decide)) (h 6 2 (by decide) (by decide))
    (h 1 0 (by decide) (by decide)) (h 1 2 (by decide) (by decide))
  have h72 : c 7 = c 2 := third_unique _ _ _ _
    (h 0 1 (by decide) (by decide))
    (h 7 0 (by decide) (by decide)) (h 7 1 (by decide) (by decide))
    (h 2 0 (by decide) (by decide)) (h 2 1 (by decide) (by decide))
  have h67 : c 6 ≠ c 7 := by
    rw [h61, h72]
    exact h 1 2 (by decide) (by decide)
  exact third_unique _ _ _ _ h67
    (h 0 6 (by decide) (by decide)) (h 0 7 (by decide) (by decide))
    (h 3 6 (by decide) (by decide)) (h 3 7 (by decide) (by decide))

def escape : Fin 11 → Fin 3 := ![0,1,1,0,2,2,2,0,1,1,0]

theorem escape_proper : Proper openEnds escape := by decide +kernel

theorem escape_not_reclosable : ¬ Reclosable escape := by decide

theorem escape_separates_signals : escape 7 ≠ escape 9 := by decide

theorem escape_not_in_cut_image : ¬ ∃ c, cut c = escape := by
  rintro ⟨c, hc⟩
  apply escape_not_reclosable
  rw [← hc]
  exact ⟨rfl, rfl⟩

theorem cut_proper (c : Fin 9 → Fin 3) (h : Proper closedEnds c) :
    Proper openEnds (cut c) := by
  simp [Proper, Touch, closedEnds, openEnds, cut, Fin.forall_fin_succ] at *
  tauto

theorem glue_proper (c : Fin 11 → Fin 3) (h : Proper openEnds c)
    (hr : Reclosable c) : Proper closedEnds (glue c) := by
  simp [Proper, Touch, closedEnds, openEnds, glue, Reclosable, Fin.forall_fin_succ] at *
  grind

/-- Reclosure constraints, not free boundary colourings, give the exact
colouring space of the original graph. -/
def colouringEquiv : {c : Fin 9 → Fin 3 // Proper closedEnds c} ≃
    {c : Fin 11 → Fin 3 // Proper openEnds c ∧ Reclosable c} where
  toFun c := ⟨cut c, cut_proper c c.property, rfl, rfl⟩
  invFun c := ⟨glue c, glue_proper c c.property.1 c.property.2⟩
  left_inv c := Subtype.ext (glue_cut c)
  right_inv c := Subtype.ext (cut_glue c c.property.2)

theorem reclosable_forces_equal (c : Fin 11 → Fin 3)
    (h : Proper openEnds c) (hr : Reclosable c) : c 7 = c 9 :=
  closed_forces_equal (glue c) (glue_proper c h hr)

/-- The attempted unconditional transfer to the two chosen half-edges is
false, even though the corresponding internal edges are always equal. -/
theorem free_opening_does_not_preserve_rigidity :
    (∀ c, Proper closedEnds c → c 0 = c 3) ∧
    ¬ (∀ c, Proper openEnds c → c 7 = c 9) :=
  ⟨closed_forces_equal, fun h => escape_separates_signals (h escape escape_proper)⟩

end Mettapedia.GraphTheory.FourColor.InternalEdgeOpening
