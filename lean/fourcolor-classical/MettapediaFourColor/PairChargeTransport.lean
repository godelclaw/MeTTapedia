import MettapediaFourColor.HubcapCharges

/-!
# Symmetries of paired charge bounds

A two-edge bound can be read from its other endpoint or in the mirror map.
The part and the offset both move: reflection reverses the offset, and
exchanging endpoints rotates the part. These are statements about actual
charges, independent of equivariance of the Boolean checker.
-/

namespace FourColor.PairChargeBound

/-- Read the same pair from its second endpoint. -/
theorem swap {p : Part} {n j : ℕ} {b : ℤ} (hsize : p.size = n) (hj : j ≤ n)
    (h : PairChargeBound p j b) : PairChargeBound (p.rot j) (n - j) b := by
  intro D _ G x hx hfit
  have harity : G.arity x = n := by simpa only [Part.size_rot, hsize] using hfit.1
  have hback : G.face^[j] (G.face^[n - j] x) = x := by
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hj,
      ← harity, G.iterate_face_arity]
  have hfit' : G.ExactFitp (G.face^[n - j] x) p :=
    (G.exact_fitp_rot (by omega : j ≤ p.size) _).mpr (by rw [hback]; exact hfit)
  have hb := h G _ (hx.iterate_face (n - j)) hfit'
  rw [hback] at hb
  simpa only [add_comm] using hb

/-- Read the paired charge in the reflected map, reversing the offset. -/
theorem reflect {p : Part} {n j : ℕ} {b : ℤ} (hsize : p.size = n)
    (hn : 0 < n) (hj : j ≤ n) (h : PairChargeBound p j b) :
    PairChargeBound (reflectDrule p) (n - j) b := by
  intro D _ G x hx hfit
  have harity : G.arity x = n := by simpa only [size_reflectDrule, hsize] using hfit.1
  have hmfit := (Hypermap.exactFitp_mirror_reflectDrule
    hx.mce.plain hx.mce.cubic (by omega : 0 < p.size) x).mp hfit
  have hb := h G.mirror (G.face^[5] x) ((hx.iterate_face 5).mirror) hmfit
  have hcycle : G.face^[j] (G.face^[n - j] x) = x := by
    rw [← Function.iterate_add_apply, Nat.add_sub_cancel' hj,
      ← harity, G.iterate_face_arity]
  have hcycle5 : G.face^[j] (G.face^[5] (G.face^[n - j] x)) = G.face^[5] x := by
    rw [← Function.iterate_add_apply, Nat.add_comm j 5,
      Function.iterate_add_apply, hcycle]
  have hback : G.mirror.face^[j] (G.face^[5] x) = G.face^[5] (G.face^[n - j] x) := by
    rw [Hypermap.mirror_face, ← hcycle5, G.iterate_faceInv_iterate_face]
  have charge (y : D) :
      G.mirror.dscore2 (G.mirror.face (G.mirror.face (G.face^[5] y))) =
        G.dscore2 (G.face (G.face y)) := by
    have hshift : G.mirror.face (G.mirror.face (G.face^[5] y)) =
        G.face (G.face (G.face y)) := by
      change G.face.symm (G.face.symm (G.face (G.face (G.face (G.face (G.face y)))))) = _
      simp only [Equiv.symm_apply_apply]
    rw [hshift, G.dscore2_mirror_face hx.mce.plain hx.mce.cubic]
  rw [hback, charge, charge] at hb
  exact hb

/-- Reflection followed by exchanging endpoints keeps the original offset. -/
theorem reflect_swap {p : Part} {n j : ℕ} {b : ℤ} (hsize : p.size = n)
    (hn : 0 < n) (hj : j ≤ n) (h : PairChargeBound p j b) :
    PairChargeBound ((reflectDrule p).rot (n - j)) j b := by
  intro D _ G x hx hfit
  have hs : (reflectDrule p).size = n := by simpa using hsize
  have result := swap hs (Nat.sub_le n j) (reflect hsize hn hj h) G x hx hfit
  simpa only [Nat.sub_sub_self hj] using result

#print axioms reflect_swap

end FourColor.PairChargeBound
