import Mettapedia.GraphTheory.FourColor.CycleCapTangle

/-!
# A cyclic choice avoiding one forbidden colour

Nonconstant two-element lists on a cycle admit compatible choices. Cutting
at two different lists permits a greedy path whose final edge also closes.
The padded-cap reconstruction uses this law for its shared radial colours.
-/

namespace Mettapedia.GraphTheory.FourColor.CyclicColourAvoidance

private theorem exists_other (a b : Color) :
    ∃ c : Color, c ≠ 0 ∧ c ≠ a ∧ c ≠ b := by
  revert a b
  decide

noncomputable def other (a b : Color) : Color := Classical.choose (exists_other a b)

theorem other_spec (a b : Color) :
    other a b ≠ 0 ∧ other a b ≠ a ∧ other a b ≠ b :=
  Classical.choose_spec (exists_other a b)

private noncomputable def path (f : ℕ → Color) (seed : Color) : ℕ → Color
  | 0 => seed
  | n + 1 => other (path f seed n) (f (n + 1))

private theorem path_spec (f : ℕ → Color) (seed : Color) (hs : seed ≠ 0)
    (hf : seed ≠ f 0) (i : ℕ) :
    path f seed i ≠ 0 ∧ path f seed i ≠ f i := by
  cases i with
  | zero => exact ⟨hs, hf⟩
  | succ i => exact ⟨(other_spec _ _).1, (other_spec _ _).2.2⟩

private theorem cut_cycle (n : ℕ) (f : Fin (n + 1) → Color)
    (hf : ∀ i, f i ≠ 0) (hcut : f 0 ≠ f (Fin.last n)) :
    ∃ q : Fin (n + 1) → Color,
      CycleCap.Valid (n + 1) q ∧ ∀ i, q i ≠ f i := by
  have hn : 0 < n := by
    by_contra h
    have he : n = 0 := by omega
    subst n
    exact hcut rfl
  let F : ℕ → Color := fun j => f ⟨j % (n+1), Nat.mod_lt _ (by omega)⟩
  let q : Fin (n + 1) → Color := fun i => path F (f (Fin.last n)) i.val
  have hq (i : Fin (n + 1)) : q i ≠ 0 ∧ q i ≠ f i := by
    simpa [q, F, Nat.mod_eq_of_lt i.isLt] using path_spec F (f (Fin.last n)) (hf _) (by simpa [F] using hcut.symm) i.val
  refine ⟨q, ⟨fun i => (hq i).1, ?_⟩, fun i => (hq i).2⟩
  intro i
  by_cases hi : i.val = n
  · have he : i = Fin.last n := Fin.ext hi
    have hz : i + 1 = 0 := by
      apply Fin.ext
      simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < n + 1 by omega), hi]
    rw [hz]
    change q i ≠ f (Fin.last n)
    simpa [he] using (hq i).2
  · have hlt : i.val + 1 < n + 1 := by have := i.isLt; omega
    have hv : (i + 1).val = i.val + 1 := by
      simp [Fin.val_add, Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
        Nat.mod_eq_of_lt hlt]
    change path F (f (Fin.last n)) i.val ≠ path F (f (Fin.last n)) (i + 1).val
    rw [hv, path]
    exact (other_spec _ _).2.1.symm

theorem constant_of_next {α : Type*} {k : ℕ} [NeZero k] (f : Fin k → α)
    (h : ∀ i, f (i + 1) = f i) : ∀ i, f i = f 0 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ i ih =>
    have he : i.castSucc + 1 = i.succ := by
      apply Fin.ext
      simp [Fin.add_def]
    exact (he ▸ h i.castSucc).trans ih

/-- The same three colours work at every cycle length; no word table is used. -/
theorem exists_cycle {k : ℕ} [NeZero k] (f : Fin k → Color)
    (hf : ∀ i, f i ≠ 0) (hne : ∃ i j, f i ≠ f j) :
    ∃ q : Fin k → Color, CycleCap.Valid k q ∧ ∀ i, q i ≠ f i := by
  have hcut : ∃ r, f r ≠ f (r - 1) := by
    by_contra h
    push Not at h
    have hc := constant_of_next f (fun i => by simpa using h (i + 1))
    obtain ⟨i, j, hij⟩ := hne
    exact hij ((hc i).trans (hc j).symm)
  obtain ⟨r, hr⟩ := hcut
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne k)
  let F : Fin (n + 1) → Color := fun i => f (i + r)
  have hlast : (Fin.last n : Fin (n + 1)) + 1 = 0 := by
    apply Fin.ext
    simp
  have he : (Fin.last n : Fin (n + 1)) + r = r - 1 := by
    calc
      Fin.last n + r = (Fin.last n + 1) + (r - 1) := by abel
      _ = r - 1 := by rw [hlast, zero_add]
  obtain ⟨q, hq, havoid⟩ := cut_cycle n F (fun i => hf _) (by simpa [F, he] using hr)
  refine ⟨fun i => q (i - r), ⟨fun i => hq.1 _, ?_⟩, ?_⟩
  · intro i
    simpa [sub_add_eq_add_sub, add_sub_assoc] using hq.2 (i - r)
  · intro i
    simpa [F] using havoid (i - r)

/-- On an even cycle, the constant-list case also closes by alternating
the two permitted colours. This removes the nonconstancy hypothesis. -/
theorem exists_cycle_of_even {k : ℕ} [NeZero k] (he : Even k)
    (f : Fin k → Color) (hf : ∀ i, f i ≠ 0) :
    ∃ q : Fin k → Color, CycleCap.Valid k q ∧ ∀ i, q i ≠ f i := by
  classical
  by_cases hn : ∃ i j, f i ≠ f j
  · exact exists_cycle f hf hn
  push Not at hn
  let c := f 0
  let a := other c 0
  let b := other c a
  have ha : a ≠ 0 ∧ a ≠ c := ⟨(other_spec _ _).1,(other_spec _ _).2.1⟩
  have hb : b ≠ 0 ∧ b ≠ c ∧ b ≠ a := other_spec _ _
  have hk : 2 ≤ k := by
    obtain ⟨r,hr⟩ := he
    have := NeZero.pos k
    omega
  have hp (i : Fin k) : i.val % 2 ≠ (i+1).val % 2 := by
    have hv : (i+1).val % 2 = (i.val+1) % 2 := by
      rw [Fin.val_add, Fin.val_one', Nat.mod_eq_of_lt (show 1 < k by omega)]
      exact Nat.mod_mod_of_dvd _ he.two_dvd
    rw [hv]
    omega
  let q : Fin k → Color := fun i => if i.val % 2 = 0 then a else b
  refine ⟨q, ⟨?_, ?_⟩, ?_⟩
  · intro i
    dsimp [q]
    split_ifs <;> first | exact ha.1 | exact hb.1
  · intro i
    have h := hp i
    dsimp [q]
    split_ifs <;> first | omega | exact hb.2.2 | exact hb.2.2.symm
  · intro i
    rw [hn i 0]
    dsimp [q]
    split_ifs <;> first | exact ha.2 | exact hb.2.1

end Mettapedia.GraphTheory.FourColor.CyclicColourAvoidance
