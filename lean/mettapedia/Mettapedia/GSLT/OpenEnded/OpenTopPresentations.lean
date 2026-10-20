import Mettapedia.GSLT.OpenEnded.CarrierBubbles
import Mathlib.Order.FixedPoints
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Set.Finite.Lattice

/-!
# Finite presentations of infinite least computation bubbles

A least computation bubble can be infinite (`CarrierBubbles.succ_cone_infinite`).
Its canonical description is still finite, in more than one way:

* **Inductively.** The reachable cone is the least fixed point of one step
  "seeds, and successors of the carrier" (`cone_eq_lfp`). The step relation of
  the calculus is a finite presentation of the bubble, whatever its size.
* **Coinductively.** The complement of the cone, the terms that can never be
  reached, is the greatest fixed point of the dual step "not a seed, and every
  predecessor outside" (`compl_cone_eq_gfp`). So unreachability is certified by
  an invariant, a set `X` with `X ⊆ coStep X` (coinduction); the complement of
  any step-closed set containing the seeds is one
  (`compl_le_gfp_of_stepClosed`).
* **By finite automata, sometimes.** Over unary numerals, a finite automaton
  accepts an eventually periodic set (`UnaryDFA.eventually_periodic`). Steps of
  `+ 2` from `0` reach exactly the even numbers, an infinite cone with a
  two-state presentation (`evens_cone`, `evens_cone_regular`). Doubling from
  `1` reaches exactly the powers of two (`powers_cone`), an infinite cone that
  no finite automaton presents (`powers_cone_not_regular`).

So whether an infinite least bubble has a finite-state presentation is a
property of the calculus, while its inductive and coinductive presentations
always exist.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OpenEnded.OpenTopPresentations

open Set
open Mettapedia.GSLT
open Mettapedia.GSLT.OpenEnded.CarrierBubbles

/-! ## Inductive and coinductive presentations of the cone -/

section Cone

variable (S : GSLT)

/-- The seeds and the successors of a carrier. -/
def coneStep (seeds : Set S.Term) : Set S.Term →o Set S.Term where
  toFun B := seeds ∪ {t' | ∃ t ∈ B, S.Step t t'}
  monotone' _ _ le := union_subset_union_right _ fun _ ⟨t, member, step⟩ => ⟨t, le member, step⟩

theorem multiStep_closed {B : Set S.Term} (closed : ∀ t ∈ B, ∀ t', S.Step t t' → t' ∈ B)
    {u t : S.Term} (path : S.MultiStep u t) (member : u ∈ B) : t ∈ B := by
  induction path with
  | refl => exact member
  | step step _ ih => exact ih (closed _ member _ step)

/-- **The reachable cone is the least fixed point of one step.** -/
theorem cone_eq_lfp (seeds : Set S.Term) : cone S seeds = OrderHom.lfp (coneStep S seeds) := by
  have least : IsLeast {B | coneStep S seeds B ≤ B} (cone S seeds) := by
    refine ⟨?_, fun B closed => ?_⟩
    · rintro t (member | ⟨u, inCone, step⟩)
      · exact ⟨t, member, .refl t⟩
      · exact cone_stepClosed seeds inCone step
    · rintro t ⟨s, member, path⟩
      exact multiStep_closed S (fun u inB t' step => closed (Or.inr ⟨u, inB, step⟩)) path
        (closed (Or.inl member))
  exact least.unique (OrderHom.isLeast_lfp_le (coneStep S seeds))

/-- Not a seed, and every predecessor outside. -/
def coStep (seeds : Set S.Term) : Set S.Term →o Set S.Term where
  toFun X := seedsᶜ ∩ {t | ∀ u, S.Step u t → u ∈ X}
  monotone' _ _ le _ member := ⟨member.1, fun u step => le (member.2 u step)⟩

/-- **The unreachable terms are the greatest fixed point of the dual step.** -/
theorem compl_cone_eq_gfp (seeds : Set S.Term) :
    (cone S seeds)ᶜ = OrderHom.gfp (coStep S seeds) := by
  apply le_antisymm
  · apply OrderHom.le_gfp
    intro t outside
    refine ⟨fun seed => outside ⟨t, seed, .refl t⟩, fun u step inCone => outside ?_⟩
    exact cone_stepClosed seeds inCone step
  · have fixed : coStep S seeds (OrderHom.gfp (coStep S seeds)) = OrderHom.gfp (coStep S seeds) :=
      OrderHom.map_gfp _
    have backward : ∀ {u t : S.Term}, S.MultiStep u t → t ∈ OrderHom.gfp (coStep S seeds) →
        u ∈ OrderHom.gfp (coStep S seeds) := by
      intro u t path
      induction path with
      | refl => exact id
      | step step _ ih =>
          intro member
          have next := ih member
          rw [← fixed] at next
          exact next.2 _ step
    rintro t member ⟨s, seed, path⟩
    have atSeed := backward path member
    rw [← fixed] at atSeed
    exact atSeed.1 seed

/-- **The complement of a step-closed set containing the seeds certifies
unreachability.** -/
theorem compl_le_gfp_of_stepClosed {seeds B : Set S.Term} (contains : seeds ⊆ B)
    (closed : ∀ t ∈ B, ∀ t', S.Step t t' → t' ∈ B) :
    Bᶜ ⊆ OrderHom.gfp (coStep S seeds) := by
  apply OrderHom.le_gfp
  intro t outside
  exact ⟨fun seed => outside (contains seed), fun u step inB => outside (closed u inB t step)⟩

end Cone

/-! ## Finite automata over unary numerals -/

/-- A deterministic finite automaton reading a unary numeral. -/
structure UnaryDFA where
  State : Type
  [finite : Finite State]
  start : State
  next : State → State
  accept : State → Prop

namespace UnaryDFA

/-- The automaton accepts `n` when `n` steps from the start reach an accepting
state. -/
def Accepts (M : UnaryDFA) (n : ℕ) : Prop :=
  M.accept (M.next^[n] M.start)

def language (M : UnaryDFA) : Set ℕ :=
  {n | M.Accepts n}

/-- **A finite automaton over unary numerals accepts an eventually periodic
set.** -/
theorem eventually_periodic (M : UnaryDFA) :
    ∃ N p, 0 < p ∧ ∀ n, N ≤ n → (M.Accepts (n + p) ↔ M.Accepts n) := by
  have := M.finite
  obtain ⟨i, j, different, same⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun n : ℕ => M.next^[n] M.start)
  have periodic : ∀ {i j : ℕ}, i < j → M.next^[i] M.start = M.next^[j] M.start →
      ∃ N p, 0 < p ∧ ∀ n, N ≤ n → (M.Accepts (n + p) ↔ M.Accepts n) := by
    intro i j lt eq
    refine ⟨i, j - i, Nat.sub_pos_of_lt lt, fun n le => ?_⟩
    have shifted : M.next^[n + (j - i)] M.start = M.next^[n] M.start := by
      have left : n + (j - i) = (n - i) + j := by omega
      have right : n = (n - i) + i := by omega
      rw [left, Function.iterate_add_apply, ← eq, ← Function.iterate_add_apply, ← right]
    unfold Accepts
    rw [shifted]
  rcases Nat.lt_or_gt_of_ne different with lt | gt
  · exact periodic lt same
  · exact periodic gt same.symm

end UnaryDFA

/-! ## Even numbers: an infinite cone with a two-state presentation -/

/-- A calculus on unary numerals with syntactic equality and the given steps. -/
abbrev natGSLT (rewrites : ℕ → ℕ → Prop) : GSLT where
  Term := ℕ
  equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
  rewrites := rewrites
  rewrites_resp_left := by
    rintro source _ target rfl step
    exact ⟨target, step, rfl⟩
  rewrites_resp_right := by
    rintro source target _ step rfl
    exact step

/-- Steps of `+ 2`. -/
abbrev plusTwo : GSLT :=
  natGSLT (fun n m => m = n + 2)

theorem multiStep_snoc {S : GSLT} {t u v : S.Term} (path : S.MultiStep t u) (step : S.Step u v) :
    S.MultiStep t v := by
  induction path with
  | refl => exact .step step (.refl _)
  | step first _ ih => exact .step first (ih step)

/-- An invariant of the steps holds along every path. -/
theorem natGSLT_invariant {rewrites : ℕ → ℕ → Prop} (P : ℕ → Prop)
    (preserved : ∀ a b, rewrites a b → P a → P b) :
    ∀ {u t : (natGSLT rewrites).Term}, (natGSLT rewrites).MultiStep u t → P u → P t := by
  intro u t path
  induction path with
  | refl => exact id
  | step step _ ih => exact fun holds => ih (preserved _ _ step holds)

theorem plusTwo_parity {u t : ℕ} (path : plusTwo.MultiStep u t) (even : u % 2 = 0) :
    t % 2 = 0 :=
  natGSLT_invariant (fun n : ℕ => n % 2 = 0)
    (fun a b (next : b = a + 2) (evenA : a % 2 = 0) => by omega) path even

theorem plusTwo_reaches (k : ℕ) : plusTwo.MultiStep (0 : ℕ) (2 * k) := by
  induction k with
  | zero => exact .refl _
  | succ k ih => exact multiStep_snoc (S := plusTwo) ih (show 2 * (k + 1) = 2 * k + 2 by omega)

/-- **The cone of `0` under `+ 2` is the even numbers.** -/
theorem evens_cone : (cone plusTwo ({0} : Set ℕ) : Set ℕ) = {n : ℕ | n % 2 = 0} := by
  refine Set.ext fun (n : ℕ) => ?_
  change n ∈ cone plusTwo ({0} : Set ℕ) ↔ n % 2 = 0
  constructor
  · rintro ⟨(s : ℕ), seed, path⟩
    have isZero : s = 0 := seed
    subst isZero
    exact plusTwo_parity path rfl
  · intro even
    have half : n = 2 * (n / 2) := by omega
    refine ⟨(0 : ℕ), rfl, ?_⟩
    rw [half]
    exact plusTwo_reaches (n / 2)

theorem evens_infinite : ({n : ℕ | n % 2 = 0} : Set ℕ).Infinite := by
  apply Set.infinite_of_not_bddAbove
  rintro ⟨bound, isBound⟩
  have member : 2 * (bound + 1) ∈ ({n : ℕ | n % 2 = 0} : Set ℕ) := by
    change 2 * (bound + 1) % 2 = 0
    omega
  have := isBound member
  omega

/-- The parity automaton. -/
def parity : UnaryDFA where
  State := Bool
  start := true
  next := not
  accept := fun state => state = true

theorem parity_iterate (n : ℕ) : Nat.iterate not n true = true ↔ n % 2 = 0 := by
  induction n with
  | zero => exact ⟨fun _ => rfl, fun _ => rfl⟩
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      cases state : Nat.iterate not n true
      · rw [state] at ih
        have odd : n % 2 ≠ 0 := fun even => by cases ih.mpr even
        exact ⟨fun _ => (by omega), fun _ => rfl⟩
      · rw [state] at ih
        have even : n % 2 = 0 := ih.mp rfl
        exact ⟨fun absurd => (by cases absurd), fun _ => (by omega)⟩

theorem parity_accepts (n : ℕ) : parity.Accepts n ↔ n % 2 = 0 :=
  parity_iterate n

/-- **An infinite least bubble with a finite-state presentation.** -/
theorem evens_cone_regular :
    parity.language = (cone plusTwo ({0} : Set ℕ) : Set ℕ) ∧
      (cone plusTwo ({0} : Set ℕ) : Set ℕ).Infinite := by
  rw [evens_cone]
  exact ⟨Set.ext parity_accepts, evens_infinite⟩

/-! ## Powers of two: an infinite cone with no finite-state presentation -/

/-- Doubling steps. -/
abbrev doubling : GSLT :=
  natGSLT (fun n m => m = 2 * n)

theorem doubling_powers {u t : ℕ} (path : doubling.MultiStep u t) (power : ∃ k, u = 2 ^ k) :
    ∃ k, t = 2 ^ k :=
  natGSLT_invariant (fun n : ℕ => ∃ k, n = 2 ^ k)
    (fun a b (next : b = 2 * a) ⟨k, isPower⟩ =>
      ⟨k + 1, by rw [next, isPower, pow_succ, Nat.mul_comm]⟩) path power

theorem doubling_reaches (k : ℕ) : doubling.MultiStep (1 : ℕ) (2 ^ k) := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
      exact multiStep_snoc (S := doubling) ih (show 2 ^ (k + 1) = 2 * 2 ^ k by
        rw [pow_succ, Nat.mul_comm])

/-- **The cone of `1` under doubling is the powers of two.** -/
theorem powers_cone : (cone doubling ({1} : Set ℕ) : Set ℕ) = {n : ℕ | ∃ k, n = 2 ^ k} := by
  refine Set.ext fun (n : ℕ) => ?_
  change n ∈ cone doubling ({1} : Set ℕ) ↔ ∃ k, n = 2 ^ k
  constructor
  · rintro ⟨(s : ℕ), seed, path⟩
    have isOne : s = 1 := seed
    subst isOne
    exact doubling_powers path ⟨0, rfl⟩
  · rintro ⟨k, rfl⟩
    exact ⟨(1 : ℕ), rfl, doubling_reaches k⟩

theorem powers_not_eventually_periodic :
    ¬ ∃ N p, 0 < p ∧ ∀ n, N ≤ n → ((∃ k, n + p = 2 ^ k) ↔ ∃ k, n = 2 ^ k) := by
  rintro ⟨N, p, positive, periodic⟩
  have large : N + p < 2 ^ (N + p) := Nat.lt_two_pow_self
  obtain ⟨m, eq⟩ := (periodic (2 ^ (N + p)) (by omega)).mpr ⟨N + p, rfl⟩
  have lower : 2 ^ (N + p) < 2 ^ m := by omega
  have upper : 2 ^ m < 2 ^ (N + p + 1) := by rw [pow_succ]; omega
  have one := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp lower
  have two := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp upper
  omega

/-- **An infinite least bubble with no finite-state presentation.** -/
theorem powers_cone_not_regular :
    ¬ ∃ M : UnaryDFA, M.language = (cone doubling ({1} : Set ℕ) : Set ℕ) := by
  rintro ⟨M, same⟩
  rw [powers_cone] at same
  obtain ⟨N, p, positive, periodic⟩ := M.eventually_periodic
  apply powers_not_eventually_periodic
  refine ⟨N, p, positive, fun n le => ?_⟩
  have shifted : (n + p ∈ M.language) ↔ (n ∈ M.language) := periodic n le
  rw [same] at shifted
  exact shifted

theorem powers_cone_infinite : (cone doubling ({1} : Set ℕ) : Set ℕ).Infinite := by
  rw [powers_cone]
  apply Set.infinite_of_not_bddAbove
  rintro ⟨(bound : ℕ), isBound⟩
  have below : 2 ^ bound ≤ bound := isBound ⟨bound, rfl⟩
  have large : bound < 2 ^ bound := Nat.lt_two_pow_self
  omega

#print axioms cone_eq_lfp
#print axioms compl_cone_eq_gfp
#print axioms compl_le_gfp_of_stepClosed
#print axioms UnaryDFA.eventually_periodic
#print axioms evens_cone
#print axioms evens_cone_regular
#print axioms powers_cone
#print axioms powers_cone_not_regular
#print axioms powers_cone_infinite

end Mettapedia.GSLT.OpenEnded.OpenTopPresentations
