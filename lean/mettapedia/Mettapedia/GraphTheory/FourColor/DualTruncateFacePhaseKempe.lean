import Mettapedia.GraphTheory.FourColor.DualTruncateCornerSemantics
import Mettapedia.GraphTheory.FourColor.RotationPatchKempe

/-!
# Physical normalization of compatible face phases

An actual target Tait colouring and a proper source witness with the same
cross-edge field differ by a constant phase on each source face. A nonzero
phase selects an entire polygon of the corresponding two colours. Switching
all polygons with one phase is therefore a saturated physical Kempe switch,
with every cross edge fixed. Three such region stages recover the exact
source image. A stage may contain many connected Kempe components.

The source witness is an explicit compatible input. Its geometric supply is
a separate obligation, discharged on the spanning-face domain by calibration.
-/

namespace Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseKempe

open DualTruncateColoring
open GoertzelV24HexagonPairingTargetAwareBoundary GoertzelV24PortTangleCommonKempeWeb

noncomputable section
set_option backward.isDefEq.respectTransparency false

def pairSum (pair : TaitColorPair) : Color := pair.colors.1 + pair.colors.2

private theorem pairSum_nonzero (pair : TaitColorPair) : pairSum pair ≠ 0 := by
  cases pair <;> decide +kernel

/-- This check concerns only the fixed colour alphabet, not graph instances. -/
theorem phase_swap (pair : TaitColorPair) (q a : Color)
    (hq : q ≠ 0) (ha : a ≠ 0) (h : q+a = pairSum pair) :
    pairActiveColor pair q ∧ Color.swap pair.colors.1 pair.colors.2 q = a := by
  cases pair <;> revert q a <;>
    unfold pairSum pairActiveColor Color.twoColor <;> decide +kernel

private theorem nonzero_phase_is_cross (q r a b : Color)
    (hq : q ≠ 0) (hr : r ≠ 0) (ha : a ≠ 0) (hb : b ≠ 0)
    (hqr : q ≠ r) (hab : a ≠ b) (hcross : q+r = a+b) (hphase : q+a ≠ 0) :
    q+a = a+b := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero q hq with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero r hr with rfl | rfl | rfl
  all_goals revert a b; decide +kernel

private theorem pairSum_inactive (pair : TaitColorPair) :
    ¬pairActiveColor pair (pairSum pair) := by
  cases pair <;> unfold pairSum pairActiveColor Color.twoColor <;> decide +kernel

universe u
variable {V E : Type u} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem.{u,u,u} V E)

/-- Joint compatibility retains every literal source-edge observation. -/
def CrossCompatible (c : Edge RS → Color) (w : ThreeVertexColoring RS) : Prop :=
  ∀ d, c (.inl (RS.edgeOf d)) = w.colour (RS.vertOf d) + w.colour (RS.vertOf (RS.alpha d))

/-- The source choice is shared by every subsequent repair stage. -/
structure State (w : ThreeVertexColoring RS) where
  colouring : (rotation RS).EdgeColoring Color
  tait : (rotation RS).IsTaitEdgeColoring colouring
  compatible : CrossCompatible RS colouring w

variable (w : ThreeVertexColoring RS) (s : State RS w)

def error (d : RS.D) : Color :=
  DualTruncateCornerSemantics.corner RS s.colouring d + w.colour (RS.vertOf d)

theorem error_phi (d : RS.D) : error RS w s (RS.phi d) = error RS w s d := by
  apply (add_eq_zero_iff_eq _ _).1
  unfold error
  rw [RS.vert_phi_eq_vert_alpha]
  calc
    (DualTruncateCornerSemantics.corner RS s.colouring (RS.phi d) +
        w.colour (RS.vertOf (RS.alpha d))) +
      (DualTruncateCornerSemantics.corner RS s.colouring d + w.colour (RS.vertOf d)) =
        (DualTruncateCornerSemantics.corner RS s.colouring d +
          DualTruncateCornerSemantics.corner RS s.colouring (RS.phi d)) +
        (w.colour (RS.vertOf d) + w.colour (RS.vertOf (RS.alpha d))) := by abel
    _ = 0 := by
      rw [←DualTruncateCornerSemantics.cross_of_star RS
        (DualTruncateCornerSemantics.star_of_tait RS s.colouring s.tait d),
        s.compatible d, color_add_self]

theorem error_phi_symm (d : RS.D) : error RS w s (RS.phi.symm d) = error RS w s d := by
  simpa only [Equiv.apply_symm_apply] using (error_phi RS w s (RS.phi.symm d)).symm

def mask (pair : TaitColorPair) : Edge RS → Prop
  | .inl _ => False
  | .inr d => error RS w s d = pairSum pair

instance mask_decidable (pair : TaitColorPair) : DecidablePred (mask RS w s pair) :=
  fun e => match e with
    | .inl _ => inferInstanceAs (Decidable False)
    | .inr d => inferInstanceAs (Decidable (error RS w s d = pairSum pair))

theorem mask_at_star (pair : TaitColorPair) (d : RS.D) (i : Fin 3) :
    mask RS w s pair ((rotation RS).edgeOf (d,i)) ↔
      i ≠ 0 ∧ error RS w s d = pairSum pair := by
  fin_cases i <;> simp [mask, DualTruncateColoring.edgeOf, error_phi_symm]

theorem selected_cross (pair : TaitColorPair) (d : RS.D)
    (h : error RS w s d = pairSum pair) :
    s.colouring (.inl (RS.edgeOf d)) = pairSum pair := by
  have hv := DualTruncateCornerSemantics.corners_valid RS s.colouring s.tait
  have hc := DualTruncateCornerSemantics.cross_of_star RS
    (DualTruncateCornerSemantics.star_of_tait RS s.colouring s.tait d)
  have he := nonzero_phase_is_cross _ _ _ _ (hv.1 d) (hv.1 (RS.phi d))
    (w.nonzero _) (w.nonzero _) (hv.2.1 d) (w.proper d)
    (hc.symm.trans (s.compatible d)) (by change error RS w s d ≠ 0; rw [h]; exact pairSum_nonzero pair)
  exact (s.compatible d).trans (he.symm.trans h)

/-- Selected polygons contain precisely both active incidences at each
of their vertices. Cross edges are inactive and remain outside the mask. -/
theorem physical_region (pair : TaitColorPair) :
    RotationPatchKempe.Region (rotation RS) (fun _ => True) s.colouring pair (mask RS w s pair) := by
  constructor
  · rintro ⟨d,i⟩ _ hm
    have hm' := (mask_at_star RS w s pair d i).1 hm
    fin_cases i
    · exact (hm'.1 rfl).elim
    · change pairActiveColor pair (s.colouring (.inr d))
      rw [←DualTruncateCornerSemantics.corner_phi RS s.colouring d]
      exact (phase_swap pair _ _
        ((DualTruncateCornerSemantics.corners_valid RS s.colouring s.tait).1 (RS.phi d))
        (w.nonzero _) ((error_phi RS w s d).trans hm'.2)).1
    · exact (phase_swap pair _ _
        ((DualTruncateCornerSemantics.corners_valid RS s.colouring s.tait).1 d)
        (w.nonzero _) hm'.2).1
  · rintro ⟨d,i⟩ ⟨e,j⟩ _ hv hi hj
    change d = e at hv
    subst e
    rw [mask_at_star RS w s pair d i, mask_at_star RS w s pair d j]
    by_cases hm : error RS w s d = pairSum pair
    · have hzero : ¬pairActiveColor pair (s.colouring ((rotation RS).edgeOf (d,0))) := by
        change ¬pairActiveColor pair (s.colouring (.inl (RS.edgeOf d)))
        rw [selected_cross RS w s pair d hm]
        exact pairSum_inactive pair
      have hin : i ≠ 0 := fun he => hzero (he ▸ hi)
      have hjn : j ≠ 0 := fun he => hzero (he ▸ hj)
      exact iff_of_true ⟨hin,hm⟩ ⟨hjn,hm⟩
    · simp only [hm, and_false]

def nextCorners (pair : TaitColorPair) (d : RS.D) : Color :=
  if error RS w s d = pairSum pair then w.colour (RS.vertOf d)
  else DualTruncateCornerSemantics.corner RS s.colouring d

theorem nextCorners_cross (pair : TaitColorPair) (d : RS.D) :
    nextCorners RS w s pair d + nextCorners RS w s pair (RS.phi d) =
      s.colouring (.inl (RS.edgeOf d)) := by
  unfold nextCorners
  rw [error_phi]
  split
  · rw [RS.vert_phi_eq_vert_alpha]
    exact (s.compatible d).symm
  · exact (DualTruncateCornerSemantics.cross_of_star RS
      (DualTruncateCornerSemantics.star_of_tait RS s.colouring s.tait d)).symm

theorem nextCorners_valid (pair : TaitColorPair) :
    DualTruncateCornerSemantics.Valid RS (nextCorners RS w s pair) := by
  have hv := DualTruncateCornerSemantics.corners_valid RS s.colouring s.tait
  refine ⟨?_,?_,?_⟩
  · intro d
    unfold nextCorners
    split
    · exact w.nonzero _
    · exact hv.1 d
  · intro d
    unfold nextCorners
    rw [error_phi]
    split
    · rw [RS.vert_phi_eq_vert_alpha]
      exact w.proper d
    · exact hv.2.1 d
  · intro d
    unfold DualTruncateCornerSemantics.Balanced
    rw [nextCorners_cross, nextCorners_cross, RS.edge_alpha]

def step (pair : TaitColorPair) : State RS w where
  colouring := DualTruncateCornerSemantics.colouring RS (nextCorners RS w s pair)
    (nextCorners_valid RS w s pair)
  tait := DualTruncateCornerSemantics.colouring_tait RS (nextCorners RS w s pair)
    (nextCorners_valid RS w s pair)
  compatible := by
    intro d
    change DualTruncateCornerSemantics.cross RS (nextCorners RS w s pair) (RS.edgeOf d) = _
    rw [DualTruncateCornerSemantics.cross_edge RS _ d ((nextCorners_valid RS w s pair).2.2 d),
      nextCorners_cross, s.compatible d]

/-- The certified next witness is exactly the physical edge switch. -/
theorem exact_effect (pair : TaitColorPair) :
    (step RS w s pair).colouring =
      RotationPatchKempe.switched s.colouring pair (mask RS w s pair) := by
  funext e
  cases e with
  | inl e =>
    obtain ⟨d,hd⟩ := RS.dartsOn_nonempty e
    have he := RS.mem_dartsOn.mp hd
    rw [←he]
    change DualTruncateCornerSemantics.cross RS (nextCorners RS w s pair) (RS.edgeOf d) = _
    rw [DualTruncateCornerSemantics.cross_edge RS _ d ((nextCorners_valid RS w s pair).2.2 d),
      nextCorners_cross]
    simp [RotationPatchKempe.switched, mask]
  | inr d =>
    change nextCorners RS w s pair (RS.phi d) = _
    unfold nextCorners RotationPatchKempe.switched mask
    rw [error_phi]
    by_cases hm : error RS w s d = pairSum pair
    · simp only [hm, ite_true]
      rw [←DualTruncateCornerSemantics.corner_phi RS s.colouring d]
      exact (phase_swap pair _ _
        ((DualTruncateCornerSemantics.corners_valid RS s.colouring s.tait).1 (RS.phi d))
        (w.nonzero _) ((error_phi RS w s d).trans hm)).2.symm
    · simp only [hm, ite_false, DualTruncateCornerSemantics.corner_phi]

theorem step_cross_preserved (pair : TaitColorPair) (e : E) :
    (step RS w s pair).colouring (.inl e) = s.colouring (.inl e) := by
  rw [exact_effect]
  simp [RotationPatchKempe.switched, mask]

def clear (pair : TaitColorPair) (x : Color) : Color :=
  if x = pairSum pair then 0 else x

theorem step_error (pair : TaitColorPair) (d : RS.D) :
    error RS w (step RS w s pair) d = clear pair (error RS w s d) := by
  change DualTruncateCornerSemantics.corner RS
    (DualTruncateCornerSemantics.edgeColours RS (nextCorners RS w s pair)) d +
      w.colour (RS.vertOf d) = clear pair (error RS w s d)
  rw [DualTruncateCornerSemantics.corner_edgeColours]
  by_cases hm : error RS w s d = pairSum pair
  · simp only [nextCorners, clear, hm, ite_true, color_add_self]
  · simp only [nextCorners, clear, hm, ite_false]
    rfl

private theorem clear_all (x : Color) :
    clear .bluePurple (clear .redPurple (clear .redBlue x)) = 0 := by
  revert x
  decide +kernel

/-- There are three saturated region stages, not necessarily three
connected-component switches. The exact source image is the terminal field. -/
def normalize : State RS w :=
  step RS w (step RS w (step RS w s .redBlue) .redPurple) .bluePurple

theorem normalize_error (d : RS.D) : error RS w (normalize RS w s) d = 0 := by
  unfold normalize
  rw [step_error, step_error, step_error]
  exact clear_all _

theorem normalize_exact : (normalize RS w s).colouring = DualTruncateColoring.colouring RS w := by
  apply DFunLike.ext
  intro e
  cases e with
  | inl e =>
    obtain ⟨d,hd⟩ := RS.dartsOn_nonempty e
    have he := RS.mem_dartsOn.mp hd
    rw [←he]
    exact ((normalize RS w s).compatible d).trans (star_colour_zero RS w.colour d).symm
  | inr d =>
    rw [←DualTruncateCornerSemantics.corner_phi RS (normalize RS w s).colouring d]
    have h := (add_eq_zero_iff_eq _ _).1 (normalize_error RS w s (RS.phi d))
    change DualTruncateCornerSemantics.corner RS (normalize RS w s).colouring (RS.phi d) = _
    rw [h, RS.vert_phi_eq_vert_alpha]
    rfl

theorem normalize_cross_preserved (e : E) :
    (normalize RS w s).colouring (.inl e) = s.colouring (.inl e) := by
  unfold normalize
  rw [step_cross_preserved, step_cross_preserved, step_cross_preserved]

end
end Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseKempe
