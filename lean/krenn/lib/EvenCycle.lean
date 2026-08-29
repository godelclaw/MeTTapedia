import Mathlib

/-!
# Matchings along a cycle alternate

A matching all of whose edges join consecutive vertices of a cycle alternates:
once one vertex's choice is made, every other is forced around the cycle.  The
argument is about the set of vertices matched *forwards* — a vertex is matched
forwards exactly when its successor is not — so membership of that set alternates,
and on a cycle of even length it is fixed by whether the first vertex belongs.

The vertices are taken to be `ZMod m`, which is what a cycle is.
-/

namespace EvenCycle

variable {m : ℕ} [NeZero m]

omit [NeZero m] in
/-- On a cycle of at least three vertices, a step forward and a step back differ. -/
theorem one_ne_neg_one (hm : 3 ≤ m) : (1 : ZMod m) ≠ -1 := by
  intro h
  have h2 : ((2 : ℕ) : ZMod m) = 0 := by
    push_cast
    linear_combination h
  rw [ZMod.natCast_eq_zero_iff] at h2
  have := Nat.le_of_dvd (by norm_num) h2
  omega

/-- A permutation whose every edge joins consecutive vertices of the cycle. -/
def IsCyclic (σ : Equiv.Perm (ZMod m)) : Prop := ∀ i, σ i = i + 1 ∨ σ i = i - 1

/-- The vertices a cyclic matching sends forwards. -/
def fwd (σ : Equiv.Perm (ZMod m)) : Set (ZMod m) := {i | σ i = i + 1}

omit [NeZero m] in
/-- **Forwardness alternates.**  A vertex is matched forwards exactly when its
successor is not. -/
theorem mem_fwd_iff_succ_notMem (hm : 3 ≤ m) {σ : Equiv.Perm (ZMod m)}
    (hinv : ∀ x, σ (σ x) = x) (hc : IsCyclic σ) (i : ZMod m) :
    i ∈ fwd σ ↔ (i + 1) ∉ fwd σ := by
  have hne := one_ne_neg_one (m := m) hm
  constructor
  · intro hi hsucc
    have h1 : σ i = i + 1 := hi
    have h2 : σ (i + 1) = i + 1 + 1 := hsucc
    have h3 : σ (i + 1) = i := by rw [← h1, hinv]
    rw [h3] at h2
    exact hne (by linear_combination -h2)
  · intro hsucc
    rcases hc i with h | h
    · exact h
    · exfalso
      rcases hc (i + 1) with h4 | h4
      · exact hsucc h4
      · have h5 : σ (i + 1) = i := by rw [h4]; ring
        have h6 : σ i = i + 1 := by
          have hh := congrArg σ h5
          rw [hinv] at hh
          exact hh.symm
        rw [h] at h6
        exact hne (by linear_combination -h6)

omit [NeZero m] in
/-- **A cyclic matching is determined by its first vertex.**  Forwardness at any
vertex is decided by forwardness at zero together with the vertex's parity. -/
theorem mem_fwd_iff (hm : 3 ≤ m) {σ : Equiv.Perm (ZMod m)}
    (hinv : ∀ x, σ (σ x) = x) (hc : IsCyclic σ) :
    ∀ k : ℕ, ((k : ZMod m) ∈ fwd σ ↔ ((0 : ZMod m) ∈ fwd σ ↔ k % 2 = 0)) := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hstep := mem_fwd_iff_succ_notMem hm hinv hc (k : ZMod m)
    have hcast : ((k + 1 : ℕ) : ZMod m) = (k : ZMod m) + 1 := by push_cast; ring
    have hnot : ((k : ZMod m) + 1 ∈ fwd σ) ↔ ¬ ((k : ZMod m) ∈ fwd σ) := by tauto
    have hpar : (k + 1) % 2 = 0 ↔ ¬ (k % 2 = 0) := by omega
    rw [hcast, hnot, ih, hpar]
    tauto

/-! ### The two alternating matchings

On a cycle of even length the vertices carry a parity, given by the ring
homomorphism onto `ZMod 2`.  Parity of a successor is parity plus one, which is all
the arithmetic the two alternating matchings need — no reasoning about
representatives.
-/

section Even

variable {n : ℕ}

/-- The parity of a vertex on an even cycle. -/
def par (n : ℕ) : ZMod (2 * n) →+* ZMod 2 :=
  ZMod.castHom ⟨n, by ring⟩ (ZMod 2)

theorem par_add_one (i : ZMod (2 * n)) : par n (i + 1) = par n i + 1 := by
  simp [par]

theorem par_sub_one (i : ZMod (2 * n)) : par n (i - 1) = par n i - 1 := by
  simp [par]

theorem add_one_ne : ∀ p : ZMod 2, p + 1 ≠ p := by decide

theorem ne_imp_eq_add_one : ∀ p b : ZMod 2, p ≠ b → p = b + 1 := by decide

/-- The two alternating matchings: from a vertex of parity `b` go forwards, from
the other parity go back. -/
def altPerm (n : ℕ) (b : ZMod 2) (i : ZMod (2 * n)) : ZMod (2 * n) :=
  if par n i = b then i + 1 else i - 1

theorem altPerm_involutive (b : ZMod 2) : Function.Involutive (altPerm n b) := by
  intro i
  unfold altPerm
  by_cases h : par n i = b
  · have h1 : par n (i + 1) ≠ b := by
      rw [par_add_one, h]
      exact add_one_ne b
    rw [if_pos h, if_neg h1]
    ring
  · have h2 : par n i = b + 1 := ne_imp_eq_add_one _ _ h
    have h1 : par n (i - 1) = b := by
      rw [par_sub_one, h2]
      ring
    rw [if_neg h, if_pos h1]
    ring

/-- Neither alternating matching fixes a vertex. -/
theorem altPerm_ne (hn : 1 ≤ n) (b : ZMod 2) (i : ZMod (2 * n)) : altPerm n b i ≠ i := by
  have hone : (1 : ZMod (2 * n)) ≠ 0 := by
    have : Fact (1 < 2 * n) := ⟨by omega⟩
    exact one_ne_zero
  unfold altPerm
  by_cases h : par n i = b
  · rw [if_pos h]
    intro hh
    exact hone (by linear_combination hh)
  · rw [if_neg h]
    intro hh
    exact hone (by linear_combination -hh)

/-- Forwardness read through parity rather than through representatives. -/
theorem mem_fwd_iff_par (hm : 3 ≤ 2 * n) {σ : Equiv.Perm (ZMod (2 * n))}
    (hinv : ∀ x, σ (σ x) = x) (hc : IsCyclic σ) (i : ZMod (2 * n)) :
    i ∈ fwd σ ↔ ((0 : ZMod (2 * n)) ∈ fwd σ ↔ par n i = 0) := by
  have : NeZero (2 * n) := ⟨by omega⟩
  obtain ⟨k, rfl⟩ := ZMod.natCast_rightInverse.surjective i
  have hpar : par n ((k : ℕ) : ZMod (2 * n)) = ((k : ℕ) : ZMod 2) := map_natCast _ k
  have hzero : (((k : ℕ) : ZMod 2) = 0) ↔ k % 2 = 0 := by
    rw [ZMod.natCast_eq_zero_iff]
    omega
  rw [hpar, hzero]
  exact mem_fwd_iff hm hinv hc k

/-- **A cyclic matching is one of the two alternating ones.** -/
theorem eq_altPerm (hm : 3 ≤ 2 * n) {σ : Equiv.Perm (ZMod (2 * n))}
    (hinv : ∀ x, σ (σ x) = x) (hc : IsCyclic σ) :
    ∃ b : ZMod 2, ∀ i, σ i = altPerm n b i := by
  have hcases : ∀ p : ZMod 2, p = 0 ∨ p = 1 := by decide
  by_cases h0 : (0 : ZMod (2 * n)) ∈ fwd σ
  · refine ⟨0, fun i => ?_⟩
    have hfwd : i ∈ fwd σ ↔ par n i = 0 := by
      rw [mem_fwd_iff_par hm hinv hc i]
      exact ⟨fun hh => hh.mp h0, fun hh => ⟨fun _ => hh, fun _ => h0⟩⟩
    unfold altPerm
    by_cases hp : par n i = 0
    · rw [if_pos hp]
      exact hfwd.mpr hp
    · rw [if_neg hp]
      rcases hc i with h | h
      · exact absurd (hfwd.mp h) hp
      · exact h
  · refine ⟨1, fun i => ?_⟩
    have hfwd : i ∈ fwd σ ↔ ¬ (par n i = 0) := by
      rw [mem_fwd_iff_par hm hinv hc i]
      exact ⟨fun hh hp => h0 (hh.mpr hp),
        fun hh => ⟨fun hcon => absurd hcon h0, fun hp => absurd hp hh⟩⟩
    unfold altPerm
    by_cases hp : par n i = 1
    · rw [if_pos hp]
      refine hfwd.mpr ?_
      rw [hp]
      decide
    · rw [if_neg hp]
      rcases hc i with h | h
      · exfalso
        rcases hcases (par n i) with h1 | h1
        · exact hfwd.mp h h1
        · exact hp h1
      · exact h

end Even

end EvenCycle
