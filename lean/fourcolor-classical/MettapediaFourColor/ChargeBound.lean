import FourColor.Present

/-!
# Semantic charge certificates

A checker result supplies a bound on the actual charge crossing an edge.
These bounds compose around a hub and transport through reflection, even
when the Boolean checker is not known to commute with that reflection.
The transport uses the reference's mirror-map and discharge-rule theorems.
-/

namespace FourColor

open scoped BigOperators

/-- A bound on the actual transfer at the edge read by a fitting checker part. -/
def ChargeBound (p : Part) (b : ℤ) : Prop :=
  ∀ {D : Type} [Finite D] (G : Hypermap D) (x : D),
    ValidHub G x → G.ExactFitp x p → G.dscore2 (G.face (G.face x)) ≤ b

namespace ChargeBound

/-- Convert a checked bound into its semantic statement. -/
theorem of_check {redp : Part → Bool} (hred : RedpartSound redp)
    {n : ℕ} (rf : DruleFork Part.conversePart n) {p : Part} {b : ℤ}
    (hsize : p.size = n) (hcheck : checkDbound2 redp rf p b = true) :
    ChargeBound p b := by
  intro D _ G x hx hfit
  have hb := Hypermap.checkDbound2_le
    (fun y q hq => hred G hx.mce y q hq) hfit hcheck
  rw [rf.target_eq, rf.source_eq] at hb
  exact (G.dbound2_le hx.mce.plain
    (converseSpec_conversePart hx.mce.plain hx.mce.cubic hx.pentagonal)
    (hfit.1.trans hsize)).trans hb

/-- Reflection preserves the semantic bound, with the reference's five-face
shift aligning both the part and the transferred charge. -/
theorem reflect {p : Part} {b : ℤ} (hsize : 0 < p.size)
    (h : ChargeBound p b) : ChargeBound (reflectDrule p) b := by
  intro D _ G x hx hfit
  have hmfit := (Hypermap.exactFitp_mirror_reflectDrule
    hx.mce.plain hx.mce.cubic hsize x).mp hfit
  have hb := h G.mirror (G.face^[5] x) ((hx.iterate_face 5).mirror) hmfit
  have hshift : G.mirror.face (G.mirror.face (G.face^[5] x)) =
      G.face (G.face (G.face x)) := by
    change G.face.symm (G.face.symm (G.face (G.face (G.face (G.face (G.face x)))))) = _
    simp only [Equiv.symm_apply_apply]
  rw [hshift, G.dscore2_mirror_face hx.mce.plain hx.mce.cubic] at hb
  exact hb

/-- Bounds on all incident edges whose sum cancels the initial charge rule
out a positively charged hub fitting this part. -/
theorem successful_of_bounds {p : Part} {n : ℕ} (hsize : p.size = n)
    (h2 : 2 ≤ n) (bound : ℕ → ℤ)
    (bounds : ∀ j < n, ChargeBound (hubcapRot n j p) (bound j))
    (budget : dboundK n + ∑ j ∈ Finset.range n, bound j ≤ 0) : Successful p := by
  intro D _ G x hx hfit
  have harity : G.arity x = n := hfit.1.trans hsize
  have hy : ValidHub G (G.invFace2 x) := by
    rw [Hypermap.invFace2_eq_iterate G x (by omega)]
    exact hx.iterate_face _
  have hyr : G.arity (G.invFace2 x) = n := by
    rw [Hypermap.invFace2_eq_iterate G x (by omega), G.arity_iterate_face, harity]
  have hsum : (∑ j ∈ Finset.range n,
      G.dscore2 (G.face (G.face (G.face^[j] (G.invFace2 x))))) ≤
      ∑ j ∈ Finset.range n, bound j := by
    apply Finset.sum_le_sum
    intro j hj
    exact bounds j (Finset.mem_range.mp hj) G _ (hy.iterate_face j)
      (G.exactFitp_hubcapRot harity h2 (Finset.mem_range.mp hj) hfit)
  have hpos := hy.pos
  rw [Hypermap.dscore, ← G.sum_map_face_face _ G.dscore2,
    G.sum_orbitList_face, hyr] at hpos
  unfold dboundK at budget
  omega

end ChargeBound

end FourColor
