import MettapediaFourColor.StripDiamondRepair
import MettapediaFourColor.StripTriangleConsistency

/-!
# Protecting one end triangle while repairing the other

A palette is safe for an end triangle when shifting any suffix of its five
boundary observations leaves it colourable. Every colourable proper end
admits such a nonzero palette. An alternating right boundary can be repaired
at edge 9 with any permitted palette; if that palette is safe on the left,
both triangles are restored for every possible distinct partner.

The safe-palette intersection is an explicit hypothesis. Its existence for
every whole boundary is not asserted.
-/

namespace FourColor.StripProtectedEnds

open Color TriangleStripAnchors StripResponseSummary StripSourceExtension
open StripEndPhase (End)

def left (b : Boundary) : Fin 5 → Color := ![b 4,b 5,b 6,b 7,b 8]
def LeftOK (t : Fin 5 → Color) : Prop := End (t 0) (t 1) (t 2) (t 3) (t 4)
instance (t : Fin 5 → Color) : Decidable (LeftOK t) := by unfold LeftOK; infer_instance

def suffix (f : Color) (t : Fin 5 → Color) (cut : Fin 6) (i : Fin 5) : Color :=
  if cut.val ≤ i.val then f + t i else t i

def Safe (f : Color) (t : Fin 5 → Color) : Prop := ∀ cut, LeftOK (suffix f t cut)
instance (f : Color) (t : Fin 5 → Color) : Decidable (Safe f t) := by
  unfold Safe
  infer_instance

/-- Protection is locally available for every proper colourable end.
The palette need not be one which also repairs the other end. -/
theorem safe_exists : ∀ t : Fin 5 → Color,
    (∀ i : Fin 4, t i.castSucc ≠ t i.succ) → LeftOK t →
    ∃ f : Color, f ≠ 0 ∧ Safe f t := by
  simp only [← and_imp]
  decide +kernel

theorem safe_original (f : Color) (t : Fin 5 → Color) (h : Safe f t) : LeftOK t := by
  have eq : suffix f t 5 = t := by
    funext i
    have hi := i.isLt
    simp [suffix,show ¬ (5 : ℕ) ≤ i.val by omega]
  simpa only [eq] using h 5

def Right (x y z u v w : Color) : Prop :=
  ∃ a d, (a ≠ u ∧ a ≠ v ∧ a ≠ w) ∧ (d ≠ x ∧ d ≠ y) ∧ a ≠ d ∧
    ∃ e, (e ≠ z ∧ e ≠ u ∧ e ≠ y) ∧ a ≠ e ∧ e ≠ d
instance (x y z u v w : Color) : Decidable (Right x y z u v w) := by
  unfold Right
  infer_instance

def RightOK (b : Boundary) : Prop := ∃ a c, StripTriangleConsistency.right0 b a c
instance (b : Boundary) : Decidable (RightOK b) := by unfold RightOK; infer_instance

theorem right_iff (b : Boundary) : RightOK b ↔ Right (b 9) (b 10) (b 0) (b 1) (b 2) (b 3) := by
  simp [RightOK,StripTriangleConsistency.right0,join,unary,attachments,Right]

def Params (x y z f : Color) : Prop :=
  x ≠ y ∧ x ≠ z ∧ f ≠ 0 ∧ f ≠ x + y ∧ (z = y ∨ f = x + z)
instance (x y z f : Color) : Decidable (Params x y z f) := by unfold Params; infer_instance

def Family (b : Boundary) (f : Color) : Prop :=
  b 0 = b 9 ∧ b 1 = b 10 ∧ b 2 = b 9 ∧ Params (b 9) (b 10) (b 3) f

def update (b : Boundary) (f : Color) (j : Fin 11) (i : Fin 11) : Color :=
  if StripDiamondPhase.inside 9 j i then f + b i else b i

private def localBoundary (t : Fin 4 → Color) : Boundary :=
  ![t 0,t 1,t 0,t 2,c0,c0,c0,c0,c0,t 0,t 1]

/-- The right repair uses three boundary colours and the exchange palette.
Every partner location is checked, including the entire opposite arc. -/
private theorem local_release : ∀ t : Fin 4 → Color,
    Params (t 0) (t 1) (t 2) (t 3) → ∀ j : Fin 11, j ≠ 9 →
    let d := update (localBoundary t) (t 3) j
    Right (d 9) (d 10) (d 0) (d 1) (d 2) (d 3) := by
  decide +kernel

theorem right_release (b : Boundary) (f : Color) (h : Family b f)
    (j : Fin 11) (hj : j ≠ 9) : RightOK (update b f j) := by
  rw [right_iff]
  have result := local_release ![b 9,b 10,b 3,f] h.2.2.2 j hj
  simpa [localBoundary,update,h.1,h.2.1,h.2.2.1] using result

/-- Edge 9 lies outside the left observations. Its exchange changes only
a suffix there; the protection hypothesis retains the whole triangle. -/
theorem left_release (b : Boundary) (f : Color) (h : Safe f (left b))
    (j : Fin 11) (hj : j ≠ 9) : LeftOK (left (update b f j)) := by
  fin_cases j
  · simpa [left,LeftOK,update,StripDiamondPhase.inside,suffix] using h 0
  · simpa [left,LeftOK,update,StripDiamondPhase.inside,suffix] using h 0
  · simpa [left,LeftOK,update,StripDiamondPhase.inside,suffix] using h 0
  · simpa [left,LeftOK,update,StripDiamondPhase.inside,suffix] using h 0
  · simpa [left,LeftOK,update,StripDiamondPhase.inside,suffix] using h 1
  · simpa [left,LeftOK,update,StripDiamondPhase.inside,suffix] using h 2
  · simpa [left,LeftOK,update,StripDiamondPhase.inside,suffix] using h 3
  · simpa [left,LeftOK,update,StripDiamondPhase.inside,suffix] using h 4
  · simpa [left,LeftOK,update,StripDiamondPhase.inside,suffix] using h 5
  · exact (hj rfl).elim
  · simpa [left,LeftOK,update,StripDiamondPhase.inside,suffix] using h 5

theorem both_release (b : Boundary) (f : Color) (family : Family b f)
    (safe : Safe f (left b)) (j : Fin 11) (hj : j ≠ 9) :
    StripEndPhase.Good (update b f j) ∧ RightOK (update b f j) :=
  ⟨(StripEndPhase.good_iff _).mpr (left_release b f safe j hj),right_release b f family j hj⟩

private theorem end_map (g : EdgePerm) (x y z u v : Color) (h : End x y z u v) :
    End (g x) (g y) (g z) (g u) (g v) := by
  rcases h with ⟨a,d,⟨az,au,av⟩,⟨dx,dy,dz⟩,ad⟩
  have ne {a b : Color} (h : a ≠ b) : g a ≠ g b := fun e => h (EdgePerm.apply_injective g e)
  exact ⟨g a,g d,⟨ne az,ne au,ne av⟩,⟨ne dx,ne dy,ne dz⟩,ne ad⟩

theorem safe_map (b : Boundary) (f : Color) (g : EdgePerm) (h : Safe f (left b)) :
    Safe (g f) (left (fun i => g (b i))) := by
  intro cut
  have hs := h cut
  have mapped := end_map g _ _ _ _ _ hs
  fin_cases cut <;> simpa [LeftOK,left,suffix,EdgePerm.apply_add] using mapped

private theorem params_map : ∀ (g : EdgePerm) (x y z f : Color),
    Params x y z f → Params (g x) (g y) (g z) (g f) := by decide +kernel

theorem family_map (b : Boundary) (f : Color) (g : EdgePerm) (h : Family b f) :
    Family (fun i => g (b i)) (g f) :=
  ⟨congrArg g h.1,congrArg g h.2.1,congrArg g h.2.2.1,
    params_map g _ _ _ _ h.2.2.2⟩

end FourColor.StripProtectedEnds
