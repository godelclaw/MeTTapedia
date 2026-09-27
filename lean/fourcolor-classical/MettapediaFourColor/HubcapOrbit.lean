import FourColor.HubCap

/-!
# Sharing discharging checks along boundary-rotation orbits

A hubcap may visit several positions that present the same part to its
checker. If their bounds also agree, one certificate per representative
suffices. The equality concerns the entire part, including fan ranges.
-/

namespace FourColor.HubcapOrbit

/-- A hubcap with one single-edge constraint at each listed position. -/
def oneEntries (bound : ℕ → ℤ) : List ℕ → Hubcap
  | [] => .nil
  | j :: js => .one j (bound j) (oneEntries bound js)

/-- Assemble the individual constraints of a single-edge hubcap. -/
theorem oneEntries_fit {conv : Part → PRange × Part} {nhub : ℕ}
    (redp : Part → Bool) (rf : DruleFork conv nhub) (p : Part)
    (bound : ℕ → ℤ) (indices : List ℕ)
    (checks : ∀ j ∈ indices, checkDbound2 redp rf (hubcapRot nhub j p) (bound j) = true) :
    hubcapFit redp rf p (oneEntries bound indices) = true := by
  revert checks
  induction indices with
  | nil => intro _; rfl
  | cons j js ih =>
    intro checks
    simp only [oneEntries, hubcapFit, Bool.and_eq_true]
    exact ⟨checks j (by simp), ih (fun k hk => checks k (by simp [hk]))⟩

/-- Reuse certificates at representatives of equal rotated parts and bounds. -/
theorem oneEntries_fit_of_representatives {conv : Part → PRange × Part} {nhub : ℕ}
    (redp : Part → Bool) (rf : DruleFork conv nhub) (p : Part)
    (bound : ℕ → ℤ) (indices : List ℕ) (representative : ℕ → ℕ)
    (parts : ∀ j ∈ indices,
      hubcapRot nhub j p = hubcapRot nhub (representative j) p)
    (bounds : ∀ j ∈ indices, bound j = bound (representative j))
    (checks : ∀ j ∈ indices,
      checkDbound2 redp rf (hubcapRot nhub (representative j) p)
        (bound (representative j)) = true) :
    hubcapFit redp rf p (oneEntries bound indices) = true := by
  apply oneEntries_fit
  intro j hj
  rw [parts j hj, bounds j hj]
  exact checks j hj

/-- A period of the observed boundary data reduces all checks to one period. -/
theorem oneEntries_fit_periodic {conv : Part → PRange × Part} {nhub : ℕ}
    (redp : Part → Bool) (rf : DruleFork conv nhub) (p : Part)
    (bound : ℕ → ℤ) (indices : List ℕ) (period : ℕ) (positive : 0 < period)
    (parts : ∀ j ∈ indices, hubcapRot nhub j p = hubcapRot nhub (j % period) p)
    (bounds : ∀ j ∈ indices, bound j = bound (j % period))
    (checks : ∀ j < period,
      checkDbound2 redp rf (hubcapRot nhub j p) (bound j) = true) :
    hubcapFit redp rf p (oneEntries bound indices) = true :=
  oneEntries_fit_of_representatives redp rf p bound indices (· % period)
    parts bounds (fun j _ => checks (j % period) (Nat.mod_lt j positive))

end FourColor.HubcapOrbit
