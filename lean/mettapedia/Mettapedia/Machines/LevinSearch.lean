import Mathlib.Data.Nat.Log
import Mathlib.Tactic

/-!
# Levin search over a weighted portfolio

A portfolio (`Family`) holds searchers, each with a description length `ℓ`. A searcher reports
what it has found after a given amount of work, and keeps what it found (`Searcher.persistent`).
The lengths satisfy Kraft's inequality (`Family.kraft`): in every round `i`, the members of length
at most `i` together receive at most `2^i` work when member `k` receives `2^(i - ℓ_k)`.

Levin search runs rounds `0, 1, 2, …`; round `i` gives each member of length at most `i` the work
`2^(i - ℓ_k)` (`phase`). It returns the first answer found (`search`).

- `search_sound`: every answer is an answer of some member;
- `cost_lt`: the first `n` rounds cost less than `2^n` in total;
- `search_finds`: if member `k` finds an answer with work `t`, Levin search finds an answer by
  round `ℓ_k + ⌈log₂ t⌉`, after total work at most `4 · 2^ℓ_k · max t 1`.

So no member is ever more than a factor `4 · 2^ℓ_k` faster than the portfolio: Levin's optimality,
for the portfolio given. `Family.ofList` builds a finite portfolio from lengths whose Kraft sum is
at most one (`kraft_of_total`).
-/

set_option autoImplicit false

namespace Mettapedia.Machines.LevinSearch

universe u v

variable {α : Type u}

/-- **A searcher**: what it has found after a given amount of work. Found answers stay found. -/
structure Searcher (α : Type u) where
  result : Nat → Option α
  persistent : ∀ work answer, result work = some answer → result (work + 1) = some answer

namespace Searcher

theorem persists (searcher : Searcher α) {work more : Nat} (le : work ≤ more) {answer : α}
    (found : searcher.result work = some answer) : searcher.result more = some answer := by
  induction le with
  | refl => exact found
  | step _ ih => exact searcher.persistent _ _ ih

/-- A searcher from a probe: the first answer the probe gives at any work up to the given one. -/
def ofProbe (probe : Nat → Option α) : Searcher α where
  result work := (List.range (work + 1)).findSome? probe
  persistent work answer found := by
    rw [List.range_succ, List.findSome?_append, found]
    rfl

theorem ofProbe_found {probe : Nat → Option α} {work : Nat} {answer : α} (found : probe work = some answer) :
    ((ofProbe probe).result work).isSome := by
  simp only [ofProbe, List.findSome?_isSome_iff, List.mem_range]
  exact ⟨work, Nat.lt_succ_self work, by rw [found]; rfl⟩

theorem ofProbe_sound {probe : Nat → Option α} {work : Nat} {answer : α}
    (found : (ofProbe probe).result work = some answer) : ∃ step, probe step = some answer := by
  obtain ⟨step, _, read⟩ := List.exists_of_findSome?_eq_some found
  exact ⟨step, read⟩

end Searcher

/-- **A portfolio of searchers** with description lengths satisfying Kraft's inequality. -/
structure Family (ι : Type v) (α : Type u) where
  length : ι → Nat
  searcher : ι → Searcher α
  /-- The members of length at most a bound, each once. -/
  upTo : Nat → List ι
  upTo_exact : ∀ bound member, member ∈ upTo bound ↔ length member ≤ bound
  kraft : ∀ bound, ((upTo bound).map fun member => 2 ^ (bound - length member)).sum ≤ 2 ^ bound

namespace Family

variable {ι : Type v} (family : Family ι α)

/-- One round: each member of length at most the round works `2^(round - length)`. -/
def phase (round : Nat) : Option α :=
  (family.upTo round).findSome? fun member =>
    (family.searcher member).result (2 ^ (round - family.length member))

/-- The work of one round. -/
def phaseCost (round : Nat) : Nat :=
  ((family.upTo round).map fun member => 2 ^ (round - family.length member)).sum

/-- **Levin search**: the first answer found in the first `rounds` rounds. -/
def search : Nat → Option α
  | 0 => none
  | rounds + 1 => (search rounds).or (family.phase rounds)

/-- The total work of the first `rounds` rounds. -/
def cost : Nat → Nat
  | 0 => 0
  | rounds + 1 => cost rounds + family.phaseCost rounds

/-- **The first `n` rounds cost less than `2^n`.** -/
theorem cost_lt : ∀ rounds, family.cost rounds < 2 ^ rounds
  | 0 => by simp [cost]
  | rounds + 1 => by
    have earlier := cost_lt rounds
    have round := family.kraft rounds
    simp only [cost, phaseCost, pow_succ]
    omega

/-- **Every answer is an answer of some member.** -/
theorem search_sound : ∀ (rounds : Nat) (answer : α), family.search rounds = some answer →
    ∃ member work, (family.searcher member).result work = some answer
  | 0, _, found => by simp [search] at found
  | rounds + 1, answer, found => by
    simp only [search] at found
    cases earlier : family.search rounds with
    | some previous =>
      rw [earlier] at found
      cases found
      exact search_sound rounds _ earlier
    | none =>
      rw [earlier] at found
      obtain ⟨member, _, read⟩ := List.exists_of_findSome?_eq_some (show family.phase rounds = some answer from found)
      exact ⟨member, _, read⟩

/-- A member with enough work makes its round succeed. -/
theorem phase_finds {member : ι} {work : Nat} {answer : α}
    (found : (family.searcher member).result work = some answer) {round : Nat}
    (enough : family.length member ≤ round) (fuel : work ≤ 2 ^ (round - family.length member)) :
    (family.phase round).isSome := by
  rw [phase, List.findSome?_isSome_iff]
  refine ⟨member, (family.upTo_exact round member).mpr enough, ?_⟩
  rw [(family.searcher member).persists fuel found]
  rfl

theorem pow_clog_le (work : Nat) : 2 ^ Nat.clog 2 work ≤ 2 * max work 1 := by
  rcases Nat.lt_or_ge work 2 with small | large
  · interval_cases work <;> simp [Nat.clog]
  · have below := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) (show 1 < work by omega)
    rw [Nat.pred_eq_sub_one] at below
    have positive : 0 < Nat.clog 2 work := Nat.clog_pos (by norm_num) large
    have split : 2 ^ Nat.clog 2 work = 2 * 2 ^ (Nat.clog 2 work - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [split]
    have : max work 1 = work := by omega
    rw [this]
    omega

/-- **Levin's bound.** If a member finds an answer with work `t`, Levin search finds an answer by
round `ℓ + ⌈log₂ t⌉`, after total work at most `4 · 2^ℓ · max t 1`. -/
theorem search_finds {member : ι} {work : Nat} {answer : α}
    (found : (family.searcher member).result work = some answer) :
    (family.search (family.length member + Nat.clog 2 work + 1)).isSome ∧
      family.cost (family.length member + Nat.clog 2 work + 1) ≤ 4 * 2 ^ family.length member * max work 1 := by
  constructor
  · have finds := family.phase_finds found (round := family.length member + Nat.clog 2 work)
      (Nat.le_add_right _ _)
      (by rw [Nat.add_sub_cancel_left]; exact Nat.le_pow_clog (by norm_num) work)
    rw [search]
    cases family.search (family.length member + Nat.clog 2 work) with
    | none => simpa using finds
    | some _ => rfl
  · have total := family.cost_lt (family.length member + Nat.clog 2 work + 1)
    have bound := pow_clog_le work
    calc family.cost (family.length member + Nat.clog 2 work + 1)
        ≤ 2 ^ (family.length member + Nat.clog 2 work + 1) := total.le
      _ = 2 * 2 ^ family.length member * 2 ^ Nat.clog 2 work := by ring
      _ ≤ 2 * 2 ^ family.length member * (2 * max work 1) := Nat.mul_le_mul_left _ bound
      _ = 4 * 2 ^ family.length member * max work 1 := by ring

/-! ## Finite portfolios -/

/-- The members of a list of length at most a bound. -/
def listUpTo (lengths : List Nat) (bound : Nat) : List (Fin lengths.length) :=
  (List.finRange lengths.length).filter fun member => lengths.get member ≤ bound

theorem mem_listUpTo (lengths : List Nat) (bound : Nat) (member : Fin lengths.length) :
    member ∈ listUpTo lengths bound ↔ lengths.get member ≤ bound := by
  simp [listUpTo]

/-- **Kraft for every round from one total**: if the lengths are at most `top` and
`∑ 2^(top - ℓ) ≤ 2^top`, every round satisfies Kraft's inequality. -/
theorem kraft_of_total (lengths : List Nat) (top : Nat) (bounded : ∀ length ∈ lengths, length ≤ top)
    (total : (lengths.map fun length => 2 ^ (top - length)).sum ≤ 2 ^ top) (bound : Nat) :
    ((listUpTo lengths bound).map fun member => 2 ^ (bound - lengths.get member)).sum ≤ 2 ^ bound := by
  have scaled : ((listUpTo lengths bound).map fun member => 2 ^ (bound - lengths.get member)).sum * 2 ^ top ≤
      2 ^ bound * 2 ^ top := by
    rw [← List.sum_map_mul_right]
    calc ((listUpTo lengths bound).map fun member => 2 ^ (bound - lengths.get member) * 2 ^ top).sum
        = ((listUpTo lengths bound).map fun member => 2 ^ bound * 2 ^ (top - lengths.get member)).sum := by
          apply congrArg List.sum
          apply List.map_congr_left
          intro member memberIn
          have small : lengths.get member ≤ bound := (mem_listUpTo lengths bound member).mp memberIn
          have below : lengths.get member ≤ top := bounded _ (List.get_mem lengths member)
          rw [← pow_add, ← pow_add]
          congr 1
          omega
      _ = 2 ^ bound * ((listUpTo lengths bound).map fun member => 2 ^ (top - lengths.get member)).sum := by
          rw [List.sum_map_mul_left]
      _ ≤ 2 ^ bound * ((List.finRange lengths.length).map fun member => 2 ^ (top - lengths.get member)).sum := by
          apply Nat.mul_le_mul_left
          exact (List.filter_sublist.map _).sum_le_sum fun _ _ => Nat.zero_le _
      _ = 2 ^ bound * (lengths.map fun length => 2 ^ (top - length)).sum := by
          congr 2
          rw [← List.ofFn_eq_map]
          exact List.ofFn_getElem_eq_map lengths (fun length => 2 ^ (top - length))
      _ ≤ 2 ^ bound * 2 ^ top := Nat.mul_le_mul_left _ total
  exact Nat.le_of_mul_le_mul_right scaled (Nat.two_pow_pos top)

/-- **A finite portfolio** from searchers and lengths with Kraft sum at most one. -/
def ofList (members : List (Nat × Searcher α)) (top : Nat)
    (bounded : ∀ length ∈ members.map Prod.fst, length ≤ top)
    (total : ((members.map Prod.fst).map fun length => 2 ^ (top - length)).sum ≤ 2 ^ top) :
    Family (Fin (members.map Prod.fst).length) α where
  length member := (members.map Prod.fst).get member
  searcher member := (members.get (member.cast (List.length_map _))).2
  upTo := listUpTo (members.map Prod.fst)
  upTo_exact := mem_listUpTo (members.map Prod.fst)
  kraft := kraft_of_total (members.map Prod.fst) top bounded total

end Family

end Mettapedia.Machines.LevinSearch
