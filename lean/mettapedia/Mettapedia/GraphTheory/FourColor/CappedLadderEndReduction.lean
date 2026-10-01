import Mettapedia.GraphTheory.FourColor.CappedLadderRotation
import Mettapedia.GraphTheory.FourColor.DualTruncateFacePhaseGSLT
import Mettapedia.GraphTheory.FourColor.DualTruncateMapGeometry
import Mettapedia.GraphTheory.FourColor.DualTruncateCornerCoherence
import Mettapedia.GraphTheory.FourColor.DualTruncateConstructionGSLT

/-!
# Recursive end reduction of literal capped ladders

Delete the two vertices of an end digon and sew its two exposed rails. The
result is the preceding ladder, including its two distinct parallel cap
edges. Every smaller source witness reconstructs while fixing all retained
vertices. An arbitrary smaller target Tait witness first supplies a joint
source witness through spanning-face calibration and physical phase repair.
-/

namespace Mettapedia.GraphTheory.FourColor.CappedLadderEndReduction

open CappedLadderRotation DualTruncateColoring DualTruncateFacePhaseKempe
open GoertzelV24TwoEdgeCutMinimality

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (m : ℕ) [NeZero m]

private theorem size_pos : 0 < 2*m := by have := NeZero.ne m; omega
private theorem size_two : 2 ≤ 2*m := by have := NeZero.ne m; omega

/-- Interior vertices keep their order. The two deleted cap vertices use
the opposite exposed endpoint's colour when reconstructed. -/
def project (v : Vertex (m+1)) : Vertex m :=
  ⟨if v.val = 0 then 2*m-1 else if v.val = 2*m+1 then 0 else v.val-1,
    by have := v.is_lt; have := size_pos m; split_ifs <;> omega⟩

/-- The actual retained vertex embedding. -/
def embed (v : Vertex m) : Vertex (m+1) := ⟨v.val+1, by have := v.is_lt; omega⟩

theorem project_embed (v : Vertex m) : project m (embed m v) = v := by
  apply Fin.ext
  simp only [project, embed, Fin.val_mk]
  have hzero : v.val+1 ≠ 0 := by omega
  have hlast : v.val+1 ≠ 2*m+1 := by have := v.is_lt; omega
  simp only [hzero, hlast, ite_false, Nat.add_sub_cancel]

theorem embed_injective : Function.Injective (embed m) :=
  Function.LeftInverse.injective (project_embed m)

theorem project_rev (v : Vertex (m+1)) : project m v.rev = (project m v).rev := by
  apply Fin.ext
  simp only [project, Fin.val_rev, Fin.val_mk]
  have := v.is_lt
  have := size_pos m
  split_ifs <;> omega

private theorem succ_val (n : ℕ) [NeZero n] (hn : 2 ≤ n) (v : Fin n) :
    (v+1).val = (v.val+1) % n := by
  change (v.val+(1 % n)) % n = _
  rw [Nat.mod_eq_of_lt hn]

theorem project_succ (v : Vertex (m+1)) (hv : v.val ≠ 2*m+1) :
    project m (v+1) = project m v + 1 := by
  apply Fin.ext
  have hs := succ_val (2*(m+1)) (by omega) v
  rw [Nat.mod_eq_of_lt (by have := v.is_lt; omega)] at hs
  rw [succ_val (2*m) (size_two m)]
  simp only [project, Fin.val_mk, hs]
  have hlt := v.is_lt
  have hp := size_pos m
  have hnextzero : v.val+1 ≠ 0 := by omega
  rw [if_neg hnextzero, if_neg hv]
  by_cases hzero : v.val = 0
  · rw [if_pos hzero, if_neg (by omega : v.val+1 ≠ 2*m+1), hzero]
    simp only [Nat.zero_add, Nat.sub_self]
    rw [show 2*m-1+1 = 2*m from by omega, Nat.mod_self]
  rw [if_neg hzero]
  by_cases hlast : v.val = 2*m
  · rw [if_pos (by omega : v.val+1 = 2*m+1), hlast]
    rw [show 2*m-1+1 = 2*m from by omega, Nat.mod_self]
  rw [if_neg (by omega : v.val+1 ≠ 2*m+1)]
  have he : (v.val-1+1) % (2*m) = v.val := by
    rw [Nat.sub_add_cancel (by omega), Nat.mod_eq_of_lt (by omega)]
  rw [Nat.add_sub_cancel]
  exact he.symm

theorem project_next_vertex (v : Vertex (m+1)) :
    ∃ i : Fin 3, (source m).vertOf ((source m).alpha (project m v,i)) = project m (v+1) := by
  by_cases hv : v.val = 2*m+1
  · have he : project m (v+1) = (project m v).rev := by
      apply Fin.ext
      have hs := succ_val (2*(m+1)) (by omega) v
      rw [hv, show 2*m+1+1 = 2*(m+1) from by omega, Nat.mod_self] at hs
      simp only [project, Fin.val_mk, Fin.val_rev, hs, hv]
      simp only [ite_true]
      rw [if_neg (by omega : 2*m+1 ≠ 0)]
    exact ⟨2,he.symm⟩
  · exact ⟨1,(project_succ m v hv).symm⟩

theorem embed_rev (v : Vertex m) : embed m v.rev = (embed m v).rev := by
  apply Fin.ext
  simp only [embed, Fin.val_rev, Fin.val_mk]
  have := v.is_lt
  omega

theorem embed_pred (v : Vertex m) (hv : v ≠ 0) : embed m (v-1) = embed m v-1 := by
  apply Fin.ext
  have hb : embed m v ≠ 0 := by intro h; have := congrArg Fin.val h; simp [embed] at this
  rw [Fin.val_sub_one_of_ne_zero hb]
  change (v-1).val+1 = v.val+1-1
  rw [Fin.val_sub_one_of_ne_zero hv]
  have hpos : 0 < v.val := by
    have : v.val ≠ 0 := fun h => hv (Fin.ext h)
    omega
  omega

theorem embed_succ (v : Vertex m) (hv : v.val+1 < 2*m) :
    embed m (v+1) = embed m v+1 := by
  apply Fin.ext
  rw [succ_val (2*(m+1)) (by omega)]
  change (v+1).val+1 = (v.val+1+1) % (2*(m+1))
  rw [succ_val (2*m) (size_two m), Nat.mod_eq_of_lt hv,
    Nat.mod_eq_of_lt (by omega)]

def embedDart (d : CappedLadderRotation.Dart m) : CappedLadderRotation.Dart (m+1) :=
  (embed m d.1,d.2)

/-- Rewire exactly the two exposed rail darts. All other old flips are
retained; the new rail seam and the existing end rung remain distinct. -/
def sewnFlip (d : CappedLadderRotation.Dart (m+1)) : CappedLadderRotation.Dart (m+1) :=
  if d.1.val = 1 ∧ d.2 = 0 then (⟨2*m,by omega⟩,1)
  else if d.1.val = 2*m ∧ d.2 = 1 then (⟨1,by have := size_pos m; omega⟩,0)
  else CappedLadderRotation.alpha (m+1) d

/-- The actual old-dart sewing is exactly the preceding literal ladder's
flip, through the retained-dart embedding. -/
theorem sewnFlip_embed (d : CappedLadderRotation.Dart m) :
    sewnFlip m (embedDart m d) = embedDart m ((source m).alpha d) := by
  rcases d with ⟨v,i⟩
  fin_cases i
  · by_cases hv : v = 0
    · subst v
      have hm : (-1 : Vertex m).val = 2*m-1 := by
        rw [Fin.val_neg']
        change (2*m-(1 % (2*m))) % (2*m) = _
        rw [Nat.mod_eq_of_lt (size_two m), Nat.mod_eq_of_lt (by have := size_pos m; omega)]
      change sewnFlip m (embed m 0,0) = (embed m (0-1),1)
      simp only [sewnFlip, embed, Fin.val_zero, Fin.val_mk, zero_sub, hm]
      simp only [and_self, ite_true]
      congr 1
      apply Fin.ext
      change 2*m = 2*m-1+1
      have := size_pos m
      omega
    · have hval : v.val ≠ 0 := fun h => hv (Fin.ext h)
      change sewnFlip m (embed m v,0) = (embed m (v-1),1)
      simp only [sewnFlip, embed, Fin.val_mk]
      rw [if_neg (by omega), if_neg (by simp)]
      change (embed m v-1,1) = (embed m (v-1),1)
      rw [embed_pred m v hv]
  · by_cases hv : v.val+1 = 2*m
    · have hs : v+1 = (0 : Vertex m) := by
        apply Fin.ext
        rw [succ_val (2*m) (size_two m), hv, Nat.mod_self]
        rfl
      change sewnFlip m (embed m v,1) = (embed m (v+1),0)
      simp only [sewnFlip, embed, Fin.val_mk]
      rw [if_neg (by simp), if_pos (by simp only [hv, and_self])]
      rw [hs]
      rfl
    · have hlt : v.val+1 < 2*m := by have := v.is_lt; omega
      change sewnFlip m (embed m v,1) = (embed m (v+1),0)
      simp only [sewnFlip, embed, Fin.val_mk]
      rw [if_neg (by simp), if_neg (by omega)]
      change (embed m v+1,0) = (embed m (v+1),0)
      rw [embed_succ m v hlt]
  · change sewnFlip m (embed m v,2) = (embed m v.rev,2)
    simp only [sewnFlip]
    rw [if_neg (by simp), if_neg (by simp)]
    change ((embed m v).rev,2) = (embed m v.rev,2)
    rw [embed_rev]

/-- Exactly the vertices between the two deleted end vertices remain. -/
def Retained (v : Vertex (m+1)) : Prop := 0 < v.val ∧ v.val < 2*m+1

theorem embed_retained (v : Vertex m) : Retained m (embed m v) := by
  have := v.is_lt
  constructor <;> change _ < _ <;> simp only [embed, Fin.val_mk] <;> omega

theorem embed_project (v : Vertex (m+1)) (hv : Retained m v) :
    embed m (project m v) = v := by
  unfold Retained at hv
  apply Fin.ext
  simp only [embed, project, Fin.val_mk]
  have hzero : v.val ≠ 0 := by exact Nat.ne_of_gt hv.1
  have hlast : v.val ≠ 2*m+1 := by omega
  rw [if_neg hzero, if_neg hlast]
  omega

theorem sewnFlip_retains_intact (d : CappedLadderRotation.Dart (m+1))
    (hd : Retained m d.1)
    (ha : Retained m ((source (m+1)).alpha d).1) :
    sewnFlip m d = (source (m+1)).alpha d := by
  have hright : ¬(d.1.val = 2*m ∧ d.2 = 1) := by
    rintro ⟨hv,hi⟩
    rcases d with ⟨v,i⟩
    change v.val = 2*m at hv
    change i = 1 at hi
    subst i
    change Retained m (v+1) at ha
    have hs := succ_val (2*(m+1)) (by omega) v
    rw [hv, Nat.mod_eq_of_lt (by omega)] at hs
    unfold Retained at ha
    omega
  have hleft : ¬(d.1.val = 1 ∧ d.2 = 0) := by
    rintro ⟨hv,hi⟩
    rcases d with ⟨v,i⟩
    change v.val = 1 at hv
    change i = 0 at hi
    subst i
    change Retained m (v-1) at ha
    have hzero : v ≠ 0 := by
      intro h
      have he := congrArg Fin.val h
      change v.val = 0 at he
      omega
    have hs := Fin.val_sub_one_of_ne_zero hzero
    unfold Retained at ha
    omega
  simp only [sewnFlip, hleft, hright, ite_false]

abbrev RetainedDart := {d : CappedLadderRotation.Dart (m+1) // Retained m d.1}

/-- Every retained old dart occurs once; this is not a projection that
forgets the distinction between parallel edges. -/
def retainedDartEquiv : CappedLadderRotation.Dart m ≃ RetainedDart m where
  toFun d := ⟨embedDart m d,embed_retained m d.1⟩
  invFun d := (project m d.val.1,d.val.2)
  left_inv d := by rcases d with ⟨v,i⟩; exact Prod.ext (project_embed m v) rfl
  right_inv d := by
    apply Subtype.ext
    exact Prod.ext (embed_project m d.val.1 d.property) rfl

/-- The sewn flip as a permutation of the actual retained old darts. -/
def sewnAlpha : Equiv.Perm (RetainedDart m) :=
  (retainedDartEquiv m).permCongr (CappedLadderRotation.alpha m)

theorem sewnAlpha_val (d : RetainedDart m) :
    (sewnAlpha m d).val = sewnFlip m d.val := by
  obtain ⟨x,rfl⟩ := (retainedDartEquiv m).surjective d
  rw [sewnAlpha, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  change embedDart m ((source m).alpha x) = sewnFlip m (embedDart m x)
  exact (sewnFlip_embed m x).symm

theorem sewnAlpha_involutive (d : RetainedDart m) : sewnAlpha m (sewnAlpha m d) = d := by
  obtain ⟨x,rfl⟩ := (retainedDartEquiv m).surjective d
  simp only [sewnAlpha, Equiv.permCongr_apply, Equiv.symm_apply_apply]
  change retainedDartEquiv m ((source m).alpha ((source m).alpha x)) = retainedDartEquiv m x
  rw [(source m).alpha_involutive]

theorem sewnAlpha_fixfree (d : RetainedDart m) : sewnAlpha m d ≠ d := by
  obtain ⟨x,rfl⟩ := (retainedDartEquiv m).surjective d
  intro h
  rw [sewnAlpha, Equiv.permCongr_apply, Equiv.symm_apply_apply] at h
  have hx : (source m).alpha x = x := (retainedDartEquiv m).injective h
  exact (source m).alpha_fixfree x hx

theorem retained_rho (d : CappedLadderRotation.Dart m) :
    embedDart m ((source m).rho d) = (source (m+1)).rho (embedDart m d) := rfl

theorem project_alpha_embed (d : CappedLadderRotation.Dart m) :
    project m ((source (m+1)).alpha (embedDart m d)).1 = ((source m).alpha d).1 := by
  rcases d with ⟨v,i⟩
  fin_cases i
  · change project m (embed m v-1) = v-1
    have he : (embed m v-1).val = v.val := by
      have hn : embed m v ≠ 0 := by intro h; have := congrArg Fin.val h; simp [embed] at this
      rw [Fin.val_sub_one_of_ne_zero hn]
      change v.val+1-1 = v.val
      omega
    have h := project_succ m (embed m v-1) (by rw [he]; have := v.is_lt; omega)
    rw [sub_add_cancel, project_embed] at h
    exact (eq_sub_iff_add_eq).mpr h.symm
  · change project m (embed m v+1) = v+1
    rw [project_succ m (embed m v) (by change v.val+1 ≠ 2*m+1; have := v.is_lt; omega),
      project_embed]
  · change project m (embed m v).rev = v.rev
    rw [project_rev, project_embed]

/-- A proper smaller source colouring extends across both deleted vertices.
The shared endpoint choices are exchanged, rather than chosen separately. -/
def restored (w : ThreeVertexColoring (source m)) : ThreeVertexColoring (source (m+1)) where
  colour := fun v => w.colour (project m v)
  nonzero := fun v => w.nonzero _
  proper := by
    rintro ⟨v,i⟩
    fin_cases i
    · change w.colour (project m v) ≠ w.colour (project m (v-1))
      obtain ⟨j,hj⟩ := project_next_vertex m (v-1)
      have h := w.proper (project m (v-1),j)
      rw [hj, sub_add_cancel] at h
      exact h.symm
    · change w.colour (project m v) ≠ w.colour (project m (v+1))
      obtain ⟨j,hj⟩ := project_next_vertex m v
      have h := w.proper (project m v,j)
      rw [hj] at h
      exact h
    · change w.colour (project m v) ≠ w.colour (project m v.rev)
      rw [project_rev]
      exact w.proper (project m v,2)

theorem restored_retained (w : ThreeVertexColoring (source m)) (v : Vertex m) :
    (restored m w).colour (embed m v) = w.colour v := by
  change w.colour (project m (embed m v)) = w.colour v
  rw [project_embed]

/-- Every labelled star observation of the retained expanded vertices is
preserved, including the observations at the two sewn half-darts. -/
theorem restored_stars (w : ThreeVertexColoring (source m))
    (d : CappedLadderRotation.Dart m) (j : Fin 3) :
    colouring (source (m+1)) (restored m w)
        ((rotation (source (m+1))).edgeOf (embedDart m d,j)) =
      colouring (source m) w ((rotation (source m)).edgeOf (d,j)) := by
  change edgeColour (source (m+1)) (restored m w).colour _ = edgeColour (source m) w.colour _
  have hbase : (restored m w).colour ((source (m+1)).vertOf (embedDart m d)) =
      w.colour ((source m).vertOf d) := restored_retained m w d.1
  have hopp : (restored m w).colour
        ((source (m+1)).vertOf ((source (m+1)).alpha (embedDart m d))) =
      w.colour ((source m).vertOf ((source m).alpha d)) :=
    congrArg w.colour (project_alpha_embed m d)
  fin_cases j
  · exact (star_colour_zero (source (m+1)) (restored m w).colour (embedDart m d)).trans
      ((congrArg₂ (fun a b : Color => a+b) hbase hopp).trans
        (star_colour_zero (source m) w.colour d).symm)
  · exact (star_colour_one (source (m+1)) (restored m w).colour (embedDart m d)).trans
      (hopp.trans (star_colour_one (source m) w.colour d).symm)
  · exact (star_colour_two (source (m+1)) (restored m w).colour (embedDart m d)).trans
      (hbase.trans (star_colour_two (source m) w.colour d).symm)

theorem target_vertices_removed : Fintype.card (source m).D + 6 =
    Fintype.card (source (m+1)).D := by
  change Fintype.card (CappedLadderRotation.Dart m) + 6 =
    Fintype.card (CappedLadderRotation.Dart (m+1))
  simp only [CappedLadderRotation.Dart, Vertex, Fintype.card_prod, Fintype.card_fin]
  omega

theorem target_strict_decrease : Fintype.card (source m).D <
    Fintype.card (source (m+1)).D := by
  have := target_vertices_removed m
  omega

theorem target_geometry : BridgelessSphericalCubicMapData (rotation (source m)) :=
  DualTruncateMapGeometry.mapClass_of _ (spherical m) (connected m) (rotationCyclic m)

/-- The whole structural operation uses every retained dart, computes the
two new seam orientations, preserves intact flips, and loses six expanded
vertices while staying in the same map class. -/
theorem strict_operation :
    (∀ d : RetainedDart m, (sewnAlpha m d).val = sewnFlip m d.val) ∧
      (∀ d : CappedLadderRotation.Dart (m+1), Retained m d.1 →
        Retained m ((source (m+1)).alpha d).1 → sewnFlip m d = (source (m+1)).alpha d) ∧
      BridgelessSphericalCubicMapData (rotation (source m)) ∧
      Fintype.card (source m).D + 6 = Fintype.card (source (m+1)).D :=
  ⟨sewnAlpha_val m, sewnFlip_retains_intact m, target_geometry m, target_vertices_removed m⟩

variable (input : (rotation (source m)).EdgeColoring Color)
  (hinput : (rotation (source m)).IsTaitEdgeColoring input)

def calibrated : ThreeVertexColoring (source m) :=
  DualTruncateSpanningFace.sourceColouring _ (spherical m) (twoSided m)
    (connected m) (rotationCyclic m) input hinput (spanningFace m)

def initial : State (source m) (calibrated m input hinput) where
  colouring := input
  tait := hinput
  compatible := by
    intro d
    exact (DualTruncateSpanningFace.sourceValues_difference _ (spherical m) (twoSided m)
      (connected m) (rotationCyclic m) input hinput (spanningFace m) d).symm

def history := DualTruncateFacePhaseGSLT.repair _ (calibrated m input hinput)
  (initial m input hinput)

theorem history_physical : DualTruncateFacePhaseGSLT.PhysicalHistory _
    (calibrated m input hinput) (history m input hinput) :=
  DualTruncateFacePhaseGSLT.physical_history _ _ _

theorem history_length : (history m input hinput).length = 3 := rfl

theorem terminal_exact : (normalize _ (calibrated m input hinput)
    (initial m input hinput)).colouring = colouring _ (calibrated m input hinput) :=
  normalize_exact _ _ _

theorem cross_preserved (edge : (data m).Edge) :
    (normalize _ (calibrated m input hinput)
      (initial m input hinput)).colouring (.inl edge) = input (.inl edge) :=
  normalize_cross_preserved _ _ _ edge

theorem terminal_coherent : DualTruncateCornerCoherence.Coherent (source m)
    (DualTruncateCornerSemantics.corner _
      (normalize _ (calibrated m input hinput) (initial m input hinput)).colouring) := by
  have hcorner (d : CappedLadderRotation.Dart m) :
      DualTruncateCornerSemantics.corner _
        (normalize _ (calibrated m input hinput) (initial m input hinput)).colouring d =
          (calibrated m input hinput).colour d.1 :=
    (add_eq_zero_iff_eq _ _).mp
      (normalize_error (source m) (calibrated m input hinput) (initial m input hinput) d)
  intro d e hv
  rw [hcorner, hcorner]
  exact congrArg (calibrated m input hinput).colour hv

/-- The reconstruction consumes the actual terminal physical field. -/
def terminalSource : ThreeVertexColoring (source m) :=
  DualTruncateCornerCoherence.sourceColouring _
    (DualTruncateCornerSemantics.corner _
      (normalize _ (calibrated m input hinput) (initial m input hinput)).colouring)
    (DualTruncateCornerSemantics.corners_valid (source m) _
      (normalize (source m) (calibrated m input hinput) (initial m input hinput)).tait)
    (terminal_coherent m input hinput)

theorem terminal_values (v : Vertex m) :
    (terminalSource m input hinput).colour v = (calibrated m input hinput).colour v := by
  change DualTruncateCornerCoherence.vertexColour (source m)
    (DualTruncateCornerSemantics.corner _
      (normalize _ (calibrated m input hinput) (initial m input hinput)).colouring)
    ((source m).vertOf (v,0)) = _
  rw [DualTruncateCornerCoherence.vertexColour_dart _ (terminal_coherent m input hinput)]
  exact (add_eq_zero_iff_eq _ _).mp
    (normalize_error (source m) (calibrated m input hinput) (initial m input hinput) (v,0))

theorem terminal_is_source_image : colouring (source m) (terminalSource m input hinput) =
    (normalize _ (calibrated m input hinput) (initial m input hinput)).colouring := by
  apply Eq.trans _ (terminal_exact m input hinput).symm
  have he : (terminalSource m input hinput).colour = (calibrated m input hinput).colour :=
    funext (terminal_values m input hinput)
  apply DFunLike.ext
  intro e
  change edgeColour (source m) (terminalSource m input hinput).colour e =
    edgeColour (source m) (calibrated m input hinput).colour e
  rw [he]

def restoredSource := restored m (terminalSource m input hinput)

/-- Reconstruction preserves the entire joint retained-star view of the
actual terminal physical field. Initial polygon colours may have changed
during repair; every initial cross colour was preserved separately. -/
theorem restored_terminal_stars (d : CappedLadderRotation.Dart m) (j : Fin 3) :
    colouring (source (m+1)) (restoredSource m input hinput)
        ((rotation (source (m+1))).edgeOf (embedDart m d,j)) =
      (normalize _ (calibrated m input hinput) (initial m input hinput)).colouring
        ((rotation (source m)).edgeOf (d,j)) :=
  (restored_stars m (terminalSource m input hinput) d j).trans
    (congrArg (fun c : (rotation (source m)).EdgeColoring Color =>
      c ((rotation (source m)).edgeOf (d,j))) (terminal_is_source_image m input hinput))

/-- Every arbitrary smaller target witness repairs and reconstructs an
actual colouring of the larger target. Size and geometry are proved for
all widths, including the parallel-edge terminal source. -/
theorem operational_reconstruction :
    (∀ d : RetainedDart m, (sewnAlpha m d).val = sewnFlip m d.val) ∧
      DualTruncateFacePhaseGSLT.PhysicalHistory _ (calibrated m input hinput)
        (history m input hinput) ∧
      (history m input hinput).length = 3 ∧
      BridgelessSphericalCubicMapData (rotation (source m)) ∧
      Fintype.card (source m).D + 6 = Fintype.card (source (m+1)).D ∧
      (rotation (source (m+1))).IsTaitEdgeColoring
        (colouring _ (restoredSource m input hinput)) :=
  ⟨(strict_operation m).1, history_physical m input hinput, history_length m input hinput,
    target_geometry m, target_vertices_removed m, colouring_nonzero _ _⟩

open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace VertexConstructionGSLT

include input hinput in
/-- The actual reconstructed colouring supplies compatible intermediate
witnesses on every complete faithful construction sweep. -/
theorem every_complete_sweep (order : List (source (m+1)).D)
    (hn : order.Nodup) (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (VertexConstructionGSLT.route (SourceVertexCodeTrace.encodeClosed
        (DualTruncateColoring.cubic (source (m+1)))
        (DualTruncateConstructionGSLT.rotationCyclic (source (m+1)))
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  DualTruncateConstructionGSLT.supported_encoded_route _
    (restoredSource m input hinput) order hn he hcover

end
end Mettapedia.GraphTheory.FourColor.CappedLadderEndReduction
