import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCyclicOrder

/-!
# Short faces exclude edges joining ports of one cyclic patch

Three-step boundary arcs and separation from their two-step predecessors
force an alleged internal port connection to reflect around the cyclic
indices. Pentagon closure contradicts separation; hexagon closure propagates
the connection. Reflection ends at a fixed edge or a three-step facial loop.
The law is independent of the boundary width.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ShortFacePortExclusion

open Equiv Equiv.Perm GoertzelV24OrbitFaceCyclicOrder Fin.NatCast

variable {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
  (RS : RotationSystem V E) {n : ℕ} [NeZero n] (port : Fin n → RS.D)
  (arc : ∀ i, (RS.phi ^ 2) (RS.rho (port i)) = port (i-1))
  (apart : ∀ i j, (RS.phi ^ 2) (port i) ≠ port j)
  (short : ∀ i, (RS.faceOrbit (port i)).card = 5 ∨ (RS.faceOrbit (port i)).card = 6)

private theorem period {d : RS.D} {k : ℕ} (h : (RS.faceOrbit d).card = k) :
    (RS.phi ^ k) d = d := by
  have he := (phi_isCycleOn_faceOrbit RS d).pow_card_apply (RS.mem_faceOrbit_self d)
  simpa only [h] using he

include short in
omit [NeZero n] in
private theorem not_three (i : Fin n) : (RS.phi ^ 3) (port i) ≠ port i := by
  intro he
  have hc := phi_isCycleOn_faceOrbit RS (port i)
  have hmod := (hc.pow_apply_eq_pow_apply (RS.mem_faceOrbit_self (port i))).1
    (show (RS.phi ^ 3) (port i) = (RS.phi ^ 0) (port i) by simpa using he)
  rcases short i with h | h <;> simp [Nat.ModEq, h] at hmod

include arc in
private theorem arc_three (i : Fin n) :
    (RS.phi ^ 3) (RS.alpha (port i)) = port (i-1) := by
  change ((RS.phi ^ 2) * RS.phi) (RS.alpha (port i)) = _
  simpa only [Perm.mul_apply, RotationSystem.phi, RS.alpha_involutive] using arc i

include arc in
private theorem mate_three {i j : Fin n} (h : RS.alpha (port i) = port j) :
    (RS.phi ^ 3) (port i) = port (j-1) := by
  change ((RS.phi ^ 2) * RS.phi) (port i) = _
  simpa only [Perm.mul_apply, RotationSystem.phi, h] using arc j

include arc apart short in
/-- A surviving internal connection must lie on a hexagon and propagates
in opposite directions along the two boundary endpoints. -/
theorem reflection {i j : Fin n} (h : RS.alpha (port i) = port j) :
    RS.alpha (port (i+1)) = port (j-1) := by
  have he := mate_three RS port arc h
  have hp : (RS.phi ^ 6) (port i) = port i := by
    rcases short i with h5 | h6
    · have hh : (RS.phi ^ 2) (port (j-1)) = port i := by
        rw [← he, ← Perm.mul_apply, ← pow_add]
        exact period RS h5
      exact (apart (j-1) i hh).elim
    · exact period RS h6
  have hh : (RS.phi ^ 3) (port (j-1)) = port i := by
    rw [← he, ← Perm.mul_apply, ← pow_add]
    exact hp
  apply (RS.phi ^ 3).injective
  rw [arc_three RS port arc, add_sub_cancel_right, hh]

include arc apart short in
/-- No boundary port has its actual edge mate at another port of this
patch. The proof uses no enumeration of matchings or boundary widths. -/
theorem no_port_edge (i j : Fin n) : RS.alpha (port i) ≠ port j := by
  have hn : ∀ k : ℕ, ∀ a : Fin n,
      RS.alpha (port a) ≠ port (a + (↑k : Fin n)) := by
    intro k
    induction k using Nat.twoStepInduction with
    | zero =>
      intro a h
      simp only [Nat.cast_zero, add_zero] at h
      exact RS.alpha_fixfree (port a) h
    | one =>
      intro a h
      simp only [Nat.cast_one] at h
      have hh := mate_three RS port arc h
      rw [add_sub_cancel_right] at hh
      exact not_three RS port short a hh
    | more k ih _ =>
      intro a h
      have hh := reflection RS port arc apart short h
      apply ih (a+1)
      have htwo : (2 : Fin n) - 1 = 1 := by
        rw [← one_add_one_eq_two, add_sub_cancel_right]
      convert hh using 1
      simp [Nat.cast_add, add_sub_assoc, add_comm, add_left_comm, htwo]
  simpa only [Fin.cast_val_eq_self, add_sub_cancel] using hn (j-i).val i

end Mettapedia.GraphTheory.FourColor.Compositional.ShortFacePortExclusion
