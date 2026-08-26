import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# The pumping engine: corridor padding from alive self-loops

This module isolates the arithmetic core shared by the route's two descent
arguments (the Seed Lemma and `A ≠ ∅`).  It is deliberately free of graph,
embedding, and colouring data: the only content is that a nonnegative
transfer with self-loops at every *alive* interface state accepts one more
rung than it already accepts.

## The shape of the argument

A corridor is a composite of identical rungs `S : c → c` between two
complementary pieces.  Counting Tait colourings refined by the interface
profile is a strong monoidal functor into matrices over `ℕ`, so a corridor of
`n` rungs has count `vᵀ Mⁿ u` with `M` the rung's transfer matrix.  Only
*positivity* of this count matters to the route, and positivity is a
reachability statement about the digraph of nonzero entries.  That digraph is
`Transfer` below.

Call an interface state **alive** when it lies on some accepted run — it is
reachable from the entry piece and reaches the exit piece.  The corridor
self-loop hypothesis (flag L2, in the form the source states it: *every
profile realized by an alive cross-section admits a one-ring extension to
itself*) says every alive state carries a self-loop.  Then a run of `n` rungs
pads to a run of `n+1` rungs by repeating the self-loop at its first state:
`accepted_succ_of_accepted`.

Read contrapositively — `not_accepted_of_not_accepted_succ` — this is the
descent the route uses.  A minimal instance that rejects at `n+1` rungs still
rejects after one rung is deleted, and rung deletion strictly decreases size,
so minimality is contradicted as soon as the corridor has two rungs.

## Why this replaces a pigeonhole

The source runs the same step as *profile repetition*: take a corridor longer
than the number of profiles, find a repeated profile, splice between the two
occurrences.  That route needs the corridor to exceed the profile count, and
so carries the profile count into the effective size threshold.  Padding at a
self-loop needs no repeat and no splice checklist: the shortened instance is
obtained by deleting one copy of a periodic rung, so it is valid by
construction, and two rungs already suffice.  The profile count is then only
needed for finiteness, and leaves the threshold entirely.

The hypotheses this module does *not* discharge, and which remain the route's
own work, are the existence of the clean corridor (flag L1) and the bound on
non-hexagonal faces that makes such a corridor available at large size.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24PumpingEngine

universe u

variable {Q : Type u}

/-- The positivity skeleton of a corridor: which rung transitions, entry
weights, and exit weights are nonzero.  `step q q'` reads "one rung carries
interface state `q` to interface state `q'`". -/
structure Transfer (Q : Type u) where
  /-- A rung admits a colouring restricting to `q` on one side and `q'` on the other. -/
  step : Q → Q → Prop
  /-- The piece on the entry side admits a colouring with interface state `q`. -/
  entry : Q → Prop
  /-- The piece on the exit side admits a colouring with interface state `q`. -/
  exit : Q → Prop

namespace Transfer

/-- `T.Chain n q q'`: a run of exactly `n` rungs from `q` to `q'`. -/
def Chain (T : Transfer Q) : ℕ → Q → Q → Prop
  | 0, q, q' => q = q'
  | (n + 1), q, q' => ∃ m, T.step q m ∧ Chain T n m q'

variable (T : Transfer Q)

@[simp] theorem chain_zero (q q' : Q) : T.Chain 0 q q' ↔ q = q' := Iff.rfl

@[simp] theorem chain_succ (n : ℕ) (q q' : Q) :
    T.Chain (n + 1) q q' ↔ ∃ m, T.step q m ∧ T.Chain n m q' := Iff.rfl

theorem chain_refl (q : Q) : T.Chain 0 q q := rfl

/-- The corridor of `n` rungs joins the two complementary pieces: some run of
exactly `n` rungs starts at an entry state and ends at an exit state.  This is
positivity of `vᵀ Mⁿ u`. -/
def Accepted (n : ℕ) : Prop :=
  ∃ q q', T.entry q ∧ T.Chain n q q' ∧ T.exit q'

/-- An interface state is **alive** when it lies on some accepted run: it is
reachable from the entry piece, and it reaches the exit piece. -/
def Alive (q : Q) : Prop :=
  (∃ n q₀, T.entry q₀ ∧ T.Chain n q₀ q) ∧ (∃ n q₁, T.Chain n q q₁ ∧ T.exit q₁)

/-- **Corridor Self-Loop Lemma** (flag L2), in the source's alive/relevant
form: every interface state realized by an alive cross-section admits the
translation-invariant one-ring extension to itself.

Stated on alive states only.  On the full realized state set the same
statement is false — measured on the `(5,0)` tube family, where only a third
of the realized classes carry a self-loop — and the route does not need it
there. -/
def SelfLooping : Prop := ∀ q, T.Alive q → T.step q q

variable {T}

/-- An entry state that begins an accepted run is alive. -/
theorem alive_of_accepted {n : ℕ} {q q' : Q}
    (hentry : T.entry q) (hchain : T.Chain n q q') (hexit : T.exit q') :
    T.Alive q :=
  ⟨⟨0, q, hentry, T.chain_refl q⟩, ⟨n, q', hchain, hexit⟩⟩

/-- **Padding.**  With self-loops at alive states, a corridor that accepts `n`
rungs accepts `n + 1`: repeat the self-loop at the run's first state.

This is the Shrinking Lemma's engine, run in the direction that needs no
profile repetition. -/
theorem accepted_succ_of_accepted (hloop : T.SelfLooping) {n : ℕ}
    (h : T.Accepted n) : T.Accepted (n + 1) := by
  obtain ⟨q, q', hentry, hchain, hexit⟩ := h
  exact ⟨q, q', hentry, ⟨q, hloop q (alive_of_accepted hentry hchain hexit), hchain⟩, hexit⟩

/-- Acceptance is monotone in corridor length. -/
theorem accepted_mono (hloop : T.SelfLooping) {m n : ℕ} (hmn : m ≤ n)
    (h : T.Accepted m) : T.Accepted n := by
  induction hmn with
  | refl => exact h
  | step _ ih => exact accepted_succ_of_accepted hloop ih

/-- **The descent step.**  Rejection at `n + 1` rungs forces rejection at `n`
rungs: deleting one rung of a clean corridor keeps a counterexample a
counterexample, while strictly decreasing size. -/
theorem not_accepted_of_not_accepted_succ (hloop : T.SelfLooping) {n : ℕ}
    (h : ¬ T.Accepted (n + 1)) : ¬ T.Accepted n :=
  fun ha => h (accepted_succ_of_accepted hloop ha)

/-- The descent step at any shorter length. -/
theorem not_accepted_of_not_accepted_of_le (hloop : T.SelfLooping) {m n : ℕ}
    (hmn : m ≤ n) (h : ¬ T.Accepted n) : ¬ T.Accepted m :=
  fun ha => h (accepted_mono hloop hmn ha)

end Transfer

/-! ## The counting layer

The route's transfer is not a relation but the functor `Count` into matrices
over `ℕ`.  This section carries the padding lemma across, so the engine may be
consumed either way. -/

section Counting

variable [Fintype Q]

/-- One rung's transfer matrix together with the two complementary pieces'
profile-refined colouring counts. -/
structure CountData (Q : Type u) [Fintype Q] where
  /-- `rung q q'` counts the rung's colourings restricting to `q` and `q'`. -/
  rung : Q → Q → ℕ
  /-- `entry q` counts the entry piece's colourings with interface state `q`. -/
  entry : Q → ℕ
  /-- `exit q` counts the exit piece's colourings with interface state `q`. -/
  exit : Q → ℕ

namespace CountData

variable (C : CountData Q)

/-- One application of the rung's transfer matrix. -/
def stepVec (w : Q → ℕ) : Q → ℕ := fun q => ∑ q', C.rung q q' * w q'

/-- `C.count n` is the number of Tait colourings of the whole instance whose
corridor has `n` rungs: the matrix product `vᵀ Mⁿ u`. -/
def count (n : ℕ) : ℕ := ∑ q, C.entry q * (C.stepVec^[n] C.exit) q

/-- The positivity skeleton of a counting datum. -/
def toTransfer : Transfer Q where
  step q q' := 0 < C.rung q q'
  entry q := 0 < C.entry q
  exit q := 0 < C.exit q

omit [Fintype Q] in
private theorem sum_pos_iff' {s : Finset Q} {f : Q → ℕ} :
    0 < ∑ q ∈ s, f q ↔ ∃ q ∈ s, 0 < f q := by
  simp [Nat.pos_iff_ne_zero, Finset.sum_eq_zero_iff]

/-- Positivity of the iterated transfer applied to the exit vector is exactly
reachability of an exit state in `n` rungs. -/
theorem stepVec_iterate_pos_iff (n : ℕ) (q : Q) :
    0 < (C.stepVec^[n] C.exit) q ↔ ∃ q', C.toTransfer.Chain n q q' ∧ 0 < C.exit q' := by
  induction n generalizing q with
  | zero =>
    simp only [Function.iterate_zero_apply]
    constructor
    · intro h
      exact ⟨q, rfl, h⟩
    · rintro ⟨q', hq', h⟩
      have hqq : q = q' := hq'
      subst hqq
      exact h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    simp only [stepVec, Transfer.chain_succ, toTransfer]
    rw [sum_pos_iff']
    constructor
    · rintro ⟨m, -, hm⟩
      have hrung : 0 < C.rung q m := by
        rcases Nat.eq_zero_or_pos (C.rung q m) with h0 | h
        · simp [h0] at hm
        · exact h
      have hrest : 0 < (C.stepVec^[n] C.exit) m := by
        rcases Nat.eq_zero_or_pos ((C.stepVec^[n] C.exit) m) with h0 | h
        · simp [h0] at hm
        · exact h
      obtain ⟨q', hchain, hexit⟩ := (ih m).mp hrest
      exact ⟨q', ⟨m, hrung, hchain⟩, hexit⟩
    · rintro ⟨q', ⟨m, hrung, hchain⟩, hexit⟩
      exact ⟨m, Finset.mem_univ m, Nat.mul_pos hrung ((ih m).mpr ⟨q', hchain, hexit⟩)⟩

/-- **The counting count is positive exactly when the corridor is accepted.** -/
theorem count_pos_iff (n : ℕ) : 0 < C.count n ↔ C.toTransfer.Accepted n := by
  simp only [count]
  rw [sum_pos_iff']
  constructor
  · rintro ⟨q, -, hq⟩
    have hentry : 0 < C.entry q := by
      rcases Nat.eq_zero_or_pos (C.entry q) with h0 | h
      · simp [h0] at hq
      · exact h
    have hrest : 0 < (C.stepVec^[n] C.exit) q := by
      rcases Nat.eq_zero_or_pos ((C.stepVec^[n] C.exit) q) with h0 | h
      · simp [h0] at hq
      · exact h
    obtain ⟨q', hchain, hexit⟩ := (C.stepVec_iterate_pos_iff n q).mp hrest
    exact ⟨q, q', hentry, hchain, hexit⟩
  · rintro ⟨q, q', hentry, hchain, hexit⟩
    exact ⟨q, Finset.mem_univ q,
      Nat.mul_pos hentry ((C.stepVec_iterate_pos_iff n q).mpr ⟨q', hchain, hexit⟩)⟩

/-- **Padding, in counting form.**  With self-loops at alive interface states,
a positive count at `n` rungs forces a positive count at `n + 1` rungs. -/
theorem count_succ_pos_of_count_pos (hloop : C.toTransfer.SelfLooping) {n : ℕ}
    (h : 0 < C.count n) : 0 < C.count (n + 1) :=
  (C.count_pos_iff (n + 1)).mpr
    (Transfer.accepted_succ_of_accepted hloop ((C.count_pos_iff n).mp h))

/-- **The descent step, in counting form.**  A vanishing count at `n + 1`
rungs forces a vanishing count after one rung is deleted. -/
theorem count_eq_zero_of_count_succ_eq_zero (hloop : C.toTransfer.SelfLooping)
    {n : ℕ} (h : C.count (n + 1) = 0) : C.count n = 0 := by
  by_contra hne
  have hpos := count_succ_pos_of_count_pos C hloop (Nat.pos_of_ne_zero hne)
  omega

end CountData

end Counting

end GoertzelV24PumpingEngine

end Mettapedia.GraphTheory.FourColor
