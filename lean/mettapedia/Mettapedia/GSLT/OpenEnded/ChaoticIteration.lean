import Mettapedia.GSLT.OpenEnded.ClosureSystems
import Mathlib.Order.OrderIsoNat
import Mathlib.Data.Set.Card

/-!
# Schedules for the least closure: chaotic iteration and depth-first search

A request given by monotone rules has a least solution: the least element above
the seed closed under every rule (`target`, `isLeast_target`). This file shows
that every fair schedule of rule applications computes it, and compares
depth-first search, with and without a depth bound, on propositional programs.

* **Every schedule is sound.** Applying the rules one at a time in any order,
  accumulating results, never leaves the least solution (`run_le_target`).
* **Every fair schedule is complete.** When the lattice has no infinite strictly
  ascending chains (finitely many generators, for instance), any schedule that
  applies every rule infinitely often reaches the least solution and stays
  there (`run_eventually_eq_target`). Two fair schedules agree from some point
  on (`schedule_independent`). Round-robin schedules are fair
  (`roundRobin_fair`). This is chaotic iteration (Cousot and Cousot).
* **Forward chaining computes the Horn closure under any fair order.** Firing
  Horn clauses one at a time from the seeds computes the Horn closure of
  `SufficientBubbles` (`target_fire_eq_hornClosure`,
  `fair_firing_computes_hornClosure`).
* **At most one effective step per generator.** Along any schedule, fair or
  not, the number of applications that change the current bubble is at most
  the number of generators (`effectiveSteps_le_card`). This bounds the
  productive work of every schedule; the linear-time forward chaining of
  Dowling and Gallier (1984) combines such a bound with one premise counter per
  Horn clause, which uses the shape of the clauses.
* **Depth-first search in clause order is order-dependent and incomplete.**
  Two ordered programs with the same clauses in a different order present the
  same Horn theory (`dfs_programs_same_rules`). Depth-first search with
  leftmost selection in the program's clause order (untabled SLD resolution)
  succeeds on one of them (`dfs_factFirst_succeeds`) and runs forever on the
  other without succeeding (`dfs_leftRecursive_never_succeeds`), although the
  goal is in the Horn closure (`goal_in_closure`). On a goal outside the
  closure it neither succeeds nor fails (`dfs_selfLoop_never_ends`), while the
  closure, computed by any fair schedule, settles the question
  (`selfLoop_closure_empty`).
* **Depth-first search with a depth bound is complete and order-independent.**
  A goal is provable by depth-first search within `n` resolution steps
  (`provableWithin`) for some `n` exactly when it is in the Horn closure
  (`exists_provableWithin_iff`). At each bound the answer depends only on the
  set of clauses, not on their order (`provableWithin_congr`). Iterative
  deepening, which tries the bounds `1, 2, 3, …`, finds the goal of both orders
  above at bound `1` (`bounded_dfs_both_orders`). On the looping goal outside
  the closure the bounded search fails at every bound
  (`bounded_dfs_selfLoop`), so iterative deepening never stops there; the empty
  Horn closure is the certificate of failure.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OpenEnded.ChaoticIteration

open Set
open Mettapedia.GSLT.OpenEnded.SufficientBubbles

universe u v

/-! ## Chaotic iteration in a complete lattice -/

section Lattice

variable {L : Type u} [CompleteLattice L] {ι : Type v}

/-- Every rule at once, above the seed. -/
def allRules (rules : ι → L →o L) (seed : L) : L →o L where
  toFun x := seed ⊔ ⨆ i, rules i x
  monotone' _ _ le := sup_le_sup_left (iSup_mono fun i => (rules i).monotone le) seed

/-- The least solution: the least element above the seed closed under every
rule. -/
def target (rules : ι → L →o L) (seed : L) : L :=
  OrderHom.lfp (allRules rules seed)

theorem allRules_le_iff (rules : ι → L →o L) (seed x : L) :
    allRules rules seed x ≤ x ↔ seed ≤ x ∧ ∀ i, rules i x ≤ x := by
  change seed ⊔ ⨆ i, rules i x ≤ x ↔ _
  rw [sup_le_iff, iSup_le_iff]

theorem isLeast_target (rules : ι → L →o L) (seed : L) :
    IsLeast {x | seed ≤ x ∧ ∀ i, rules i x ≤ x} (target rules seed) := by
  have least := OrderHom.isLeast_lfp_le (allRules rules seed)
  exact ⟨(allRules_le_iff rules seed _).mp least.1,
    fun x member => least.2 ((allRules_le_iff rules seed x).mpr member)⟩

/-- Applying the scheduled rules one at a time and accumulating. -/
def run (rules : ι → L →o L) (seed : L) (schedule : ℕ → ι) : ℕ → L
  | 0 => seed
  | n + 1 => run rules seed schedule n ⊔ rules (schedule n) (run rules seed schedule n)

theorem run_zero (rules : ι → L →o L) (seed : L) (schedule : ℕ → ι) :
    run rules seed schedule 0 = seed :=
  rfl

theorem run_succ (rules : ι → L →o L) (seed : L) (schedule : ℕ → ι) (n : ℕ) :
    run rules seed schedule (n + 1) =
      run rules seed schedule n ⊔ rules (schedule n) (run rules seed schedule n) :=
  rfl

theorem run_monotone (rules : ι → L →o L) (seed : L) (schedule : ℕ → ι) :
    Monotone (run rules seed schedule) :=
  monotone_nat_of_le_succ fun _ => le_sup_left

/-- **Every schedule is sound.** -/
theorem run_le_target (rules : ι → L →o L) (seed : L) (schedule : ℕ → ι) (n : ℕ) :
    run rules seed schedule n ≤ target rules seed := by
  obtain ⟨⟨above, closed⟩, _⟩ := isLeast_target rules seed
  induction n with
  | zero => exact above
  | succ n ih => exact sup_le ih (((rules (schedule n)).monotone ih).trans (closed _))

/-- A schedule applies every rule infinitely often. -/
def Fair (schedule : ℕ → ι) : Prop :=
  ∀ i N, ∃ n, N ≤ n ∧ schedule n = i

/-- **Every fair schedule reaches the least solution** when ascending chains
stabilize. -/
theorem run_eventually_eq_target [WellFoundedGT L] (rules : ι → L →o L) (seed : L)
    {schedule : ℕ → ι} (fair : Fair schedule) :
    ∃ N, ∀ n, N ≤ n → run rules seed schedule n = target rules seed := by
  obtain ⟨N, stable⟩ := WellFoundedGT.monotone_chain_condition
    (⟨run rules seed schedule, run_monotone rules seed schedule⟩ : ℕ →o L)
  have stable' : ∀ m, N ≤ m → run rules seed schedule N = run rules seed schedule m := stable
  have closed : ∀ i, rules i (run rules seed schedule N) ≤ run rules seed schedule N := by
    intro i
    obtain ⟨m, le, scheduled⟩ := fair i N
    have fired : rules i (run rules seed schedule m) ≤ run rules seed schedule (m + 1) := by
      rw [run_succ, scheduled]
      exact le_sup_right
    rw [← stable' m le, ← stable' (m + 1) (le.trans (Nat.le_succ m))] at fired
    exact fired
  have above : seed ≤ run rules seed schedule N :=
    run_monotone rules seed schedule (Nat.zero_le N)
  have reached : target rules seed ≤ run rules seed schedule N :=
    (isLeast_target rules seed).2 ⟨above, closed⟩
  refine ⟨N, fun n le => ?_⟩
  rw [← stable' n le]
  exact le_antisymm (run_le_target rules seed schedule N) reached

/-- **Fair schedules agree.** -/
theorem schedule_independent [WellFoundedGT L] (rules : ι → L →o L) (seed : L)
    {first second : ℕ → ι} (fairFirst : Fair first) (fairSecond : Fair second) :
    ∃ N, ∀ n, N ≤ n → run rules seed first n = run rules seed second n := by
  obtain ⟨N₁, reach₁⟩ := run_eventually_eq_target rules seed fairFirst
  obtain ⟨N₂, reach₂⟩ := run_eventually_eq_target rules seed fairSecond
  exact ⟨max N₁ N₂, fun n le =>
    (reach₁ n (le_of_max_le_left le)).trans (reach₂ n (le_of_max_le_right le)).symm⟩

end Lattice

/-- Round-robin over `k + 1` rules. -/
def roundRobin (k : ℕ) (n : ℕ) : Fin (k + 1) :=
  ⟨n % (k + 1), Nat.mod_lt _ (Nat.succ_pos k)⟩

theorem roundRobin_fair (k : ℕ) : Fair (roundRobin k) := by
  intro i N
  refine ⟨(k + 1) * N + i, ?_, ?_⟩
  · exact Nat.le_add_right_of_le (Nat.le_mul_of_pos_left N (Nat.succ_pos k))
  · apply Fin.ext
    change ((k + 1) * N + i) % (k + 1) = i
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt i.isLt]

/-! ## Firing Horn clauses -/

section Firing

variable {G : Type u}

/-- Firing one clause: its conclusion, when its premises are present. -/
def fire (clause : HornClause G) : Set G →o Set G where
  toFun S := {g | clause.premises ⊆ S ∧ g = clause.conclusion}
  monotone' _ _ le _ member := ⟨member.1.trans le, member.2⟩

theorem fire_le_iff (clause : HornClause G) (S : Set G) :
    fire clause S ≤ S ↔ clause.Holds S := by
  constructor
  · intro le premisesIn
    exact le ⟨premisesIn, rfl⟩
  · rintro holds g ⟨premisesIn, rfl⟩
    exact holds premisesIn

/-- **The least solution of firing a Horn theory is its Horn closure.** -/
theorem target_fire_eq_hornClosure (theory : Set (HornClause G)) (seeds : Set G) :
    target (fun clause : theory => fire clause.1) seeds =
      hornClosure theory seeds := by
  have same : {x | seeds ≤ x ∧ ∀ i : theory, fire i.1 x ≤ x} =
      {S | S ∈ hornModels theory ∧ seeds ⊆ S} := by
    ext S
    constructor
    · rintro ⟨seedsIn, closed⟩
      exact ⟨fun clause member => (fire_le_iff clause S).mp (closed ⟨clause, member⟩),
        seedsIn⟩
    · rintro ⟨closed, seedsIn⟩
      exact ⟨seedsIn, fun i => (fire_le_iff i.1 S).mpr (closed i.1 i.2)⟩
  have least := isLeast_target (fun clause : theory => fire clause.1) seeds
  rw [same] at least
  exact least.unique (isLeast_hornClosure theory seeds)

/-- **Any fair order of firing computes the Horn closure** over finitely
many generators. -/
theorem fair_firing_computes_hornClosure [Finite G] (theory : Set (HornClause G))
    (seeds : Set G) {schedule : ℕ → theory} (fair : Fair schedule) :
    ∃ N, ∀ n, N ≤ n →
      run (fun clause : theory => fire clause.1) seeds schedule n =
        hornClosure theory seeds := by
  obtain ⟨N, reached⟩ := run_eventually_eq_target (fun clause : theory => fire clause.1)
    seeds fair
  exact ⟨N, fun n le => (reached n le).trans (target_fire_eq_hornClosure theory seeds)⟩

end Firing

/-! ## At most one effective step per generator -/

section Effective

variable {G : Type u} {ι : Type v}

open Classical in
/-- The number of applications among the first `n` that changed the bubble. -/
noncomputable def effectiveSteps (rules : ι → Set G →o Set G) (seed : Set G)
    (schedule : ℕ → ι) : ℕ → ℕ
  | 0 => 0
  | n + 1 => effectiveSteps rules seed schedule n +
      if run rules seed schedule n = run rules seed schedule (n + 1) then 0 else 1

theorem effectiveSteps_le_ncard [Finite G] (rules : ι → Set G →o Set G) (seed : Set G)
    (schedule : ℕ → ι) (n : ℕ) :
    effectiveSteps rules seed schedule n ≤ (run rules seed schedule n).ncard := by
  induction n with
  | zero => exact Nat.zero_le _
  | succ n ih =>
      classical
      have grows : run rules seed schedule n ⊆ run rules seed schedule (n + 1) :=
        run_monotone rules seed schedule (Nat.le_succ n)
      by_cases same : run rules seed schedule n = run rules seed schedule (n + 1)
      · simp only [effectiveSteps, same, if_true, Nat.add_zero]
        exact same ▸ ih
      · simp only [effectiveSteps, same, if_false]
        have strict : run rules seed schedule n ⊂ run rules seed schedule (n + 1) :=
          ssubset_of_subset_of_ne grows same
        have larger := Set.ncard_lt_ncard strict (Set.toFinite _)
        omega

/-- **Along any schedule, at most one effective step per generator.** -/
theorem effectiveSteps_le_card [Finite G] (rules : ι → Set G →o Set G) (seed : Set G)
    (schedule : ℕ → ι) (n : ℕ) :
    effectiveSteps rules seed schedule n ≤ Nat.card G :=
  (effectiveSteps_le_ncard rules seed schedule n).trans
    ((Set.ncard_le_ncard (subset_univ _) (Set.toFinite _)).trans_eq (Set.ncard_univ G))

end Effective

/-! ## Depth-first search in clause order -/

section DepthFirst

variable {A : Type u} [DecidableEq A]

/-- A program as an ordered list of rules `(head, body)`. -/
abbrev OrderedProgram (A : Type u) :=
  List (A × List A)

/-- The pending goal lists of a depth-first search, the first one being
explored. -/
abbrev SearchState (A : Type u) :=
  List (List A)

/-- One step of depth-first search with leftmost selection: the first atom of the
first goal list is replaced by the body of each rule for it, in the program's
order, ahead of the remaining alternatives. An empty first goal list is a
success and stays. -/
def dfsStep (program : OrderedProgram A) : SearchState A → SearchState A
  | [] => []
  | [] :: rest => [] :: rest
  | (g :: goals) :: rest =>
      (program.filter (fun rule => rule.1 = g)).map (fun rule => rule.2 ++ goals) ++ rest

/-- The search after `n` steps. -/
def dfsRun (program : OrderedProgram A) (start : SearchState A) (n : ℕ) : SearchState A :=
  (dfsStep program)^[n] start

/-- The search has found a proof. -/
def Succeeded (state : SearchState A) : Prop :=
  state.head? = some []

/-- The search has run out of alternatives. -/
def Failed (state : SearchState A) : Prop :=
  state = []

/-- The Horn clauses presented by a program; the order of its clauses is
forgotten. -/
def programClauses (program : OrderedProgram A) : Set (HornClause A) :=
  {clause | ∃ rule ∈ program, clause = ⟨{a | a ∈ rule.2}, rule.1⟩}

/-! ### Depth-first search with a depth bound -/

/-- Depth-first search with leftmost selection and at most `n` resolution
steps: the empty goal list is proved; otherwise the first goal is resolved with
some clause for it, and the rest of the search has one step less. -/
def provableWithin (program : OrderedProgram A) : ℕ → List A → Bool
  | _, [] => true
  | 0, _ :: _ => false
  | n + 1, g :: goals =>
      program.any fun rule => decide (rule.1 = g) && provableWithin program n (rule.2 ++ goals)

theorem provableWithin_succ_cons (program : OrderedProgram A) (n : ℕ) (g : A) (goals : List A) :
    provableWithin program (n + 1) (g :: goals) = true ↔
      ∃ rule ∈ program, rule.1 = g ∧ provableWithin program n (rule.2 ++ goals) = true := by
  simp only [provableWithin, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]

theorem provableWithin_zero_cons (program : OrderedProgram A) (g : A) (goals : List A) :
    provableWithin program 0 (g :: goals) = false :=
  rfl

/-- One more step of budget never hurts. -/
theorem provableWithin_succ (program : OrderedProgram A) :
    ∀ (n : ℕ) (goals : List A), provableWithin program n goals = true →
      provableWithin program (n + 1) goals = true
  | _, [], _ => rfl
  | 0, g :: goals, proved => by rw [provableWithin_zero_cons] at proved; cases proved
  | n + 1, g :: goals, proved => by
      obtain ⟨rule, member, head, rest⟩ := (provableWithin_succ_cons program n g goals).mp proved
      exact (provableWithin_succ_cons program (n + 1) g goals).mpr
        ⟨rule, member, head, provableWithin_succ program n _ rest⟩

theorem provableWithin_mono (program : OrderedProgram A) {n m : ℕ} (le : n ≤ m) {goals : List A}
    (proved : provableWithin program n goals = true) : provableWithin program m goals = true := by
  induction m, le using Nat.le_induction with
  | base => exact proved
  | succ m _ ih => exact provableWithin_succ program m goals ih

/-- Proving two goal lists one after the other adds the budgets. -/
theorem provableWithin_append (program : OrderedProgram A) :
    ∀ (n m : ℕ) (xs ys : List A), provableWithin program n xs = true →
      provableWithin program m ys = true → provableWithin program (n + m) (xs ++ ys) = true
  | n, m, [], ys, _, provedYs => provableWithin_mono program (Nat.le_add_left m n) provedYs
  | 0, _, g :: xs, ys, provedXs, _ => by rw [provableWithin_zero_cons] at provedXs; cases provedXs
  | n + 1, m, g :: xs, ys, provedXs, provedYs => by
      obtain ⟨rule, member, head, rest⟩ := (provableWithin_succ_cons program n g xs).mp provedXs
      have combined := provableWithin_append program n m (rule.2 ++ xs) ys rest provedYs
      rw [List.append_assoc] at combined
      rw [show n + 1 + m = (n + m) + 1 by omega, List.cons_append]
      exact (provableWithin_succ_cons program (n + m) g (xs ++ ys)).mpr
        ⟨rule, member, head, combined⟩

/-- **Soundness of bounded search.** Every goal of a list proved within some
bound is in the Horn closure of the program. -/
theorem provableWithin_sound (program : OrderedProgram A) :
    ∀ (n : ℕ) (goals : List A), provableWithin program n goals = true →
      ∀ g ∈ goals, g ∈ hornClosure (programClauses program) ∅
  | _, [], _, _, absurd => (List.not_mem_nil absurd).elim
  | 0, g :: goals, proved, _, _ => by rw [provableWithin_zero_cons] at proved; cases proved
  | n + 1, g :: goals, proved, x, member => by
      obtain ⟨rule, inProgram, head, rest⟩ := (provableWithin_succ_cons program n g goals).mp proved
      have later := provableWithin_sound program n _ rest
      rcases List.mem_cons.mp member with rfl | inGoals
      · rw [← head]
        exact HornDerivable.rule ⟨{a | a ∈ rule.2}, rule.1⟩ ⟨rule, inProgram, rfl⟩
          fun a inBody => later a (List.mem_append_left goals inBody)
      · exact later x (List.mem_append_right rule.2 inGoals)

/-- Goals proved one at a time are proved together. -/
theorem exists_provableWithin_of_forall (program : OrderedProgram A) :
    ∀ goals : List A, (∀ g ∈ goals, ∃ n, provableWithin program n [g] = true) →
      ∃ n, provableWithin program n goals = true
  | [], _ => ⟨0, rfl⟩
  | g :: goals, each => by
      obtain ⟨n, head⟩ := each g List.mem_cons_self
      obtain ⟨m, rest⟩ := exists_provableWithin_of_forall program goals
        fun x member => each x (List.mem_cons_of_mem g member)
      exact ⟨n + m, provableWithin_append program n m [g] goals head rest⟩

/-- **Completeness of bounded search.** Every goal in the Horn closure is
proved within some bound. -/
theorem exists_provableWithin_of_mem (program : OrderedProgram A) {g : A}
    (derivable : g ∈ hornClosure (programClauses program) ∅) :
    ∃ n, provableWithin program n [g] = true := by
  induction derivable with
  | seed absurd => exact absurd.elim
  | rule clause member _ ih =>
      obtain ⟨rule, inProgram, rfl⟩ := member
      obtain ⟨n, body⟩ := exists_provableWithin_of_forall program rule.2 fun a inBody => ih a inBody
      refine ⟨n + 1, (provableWithin_succ_cons program n rule.1 []).mpr ⟨rule, inProgram, rfl, ?_⟩⟩
      rw [List.append_nil]
      exact body

/-- **Bounded search is sound and complete for the Horn closure.** -/
theorem exists_provableWithin_iff (program : OrderedProgram A) (g : A) :
    (∃ n, provableWithin program n [g] = true) ↔ g ∈ hornClosure (programClauses program) ∅ :=
  ⟨fun ⟨n, proved⟩ => provableWithin_sound program n [g] proved g List.mem_cons_self,
    exists_provableWithin_of_mem program⟩

/-- **The bounded search answers alike at every bound for programs with the
same clauses**, whatever their order. -/
theorem provableWithin_congr {program program' : OrderedProgram A}
    (same : ∀ rule, rule ∈ program ↔ rule ∈ program') :
    ∀ (n : ℕ) (goals : List A), provableWithin program n goals = provableWithin program' n goals
  | 0, [] => rfl
  | _ + 1, [] => rfl
  | 0, _ :: _ => rfl
  | n + 1, g :: goals => by
      rw [Bool.eq_iff_iff, provableWithin_succ_cons, provableWithin_succ_cons]
      constructor
      · rintro ⟨rule, member, head, rest⟩
        exact ⟨rule, (same rule).mp member, head, (provableWithin_congr same n _).symm ▸ rest⟩
      · rintro ⟨rule, member, head, rest⟩
        exact ⟨rule, (same rule).mpr member, head, (provableWithin_congr same n _) ▸ rest⟩

end DepthFirst

/-- Two atoms. -/
inductive Atom
  | p
  | q
  deriving DecidableEq

open Atom

instance : Finite Atom :=
  Finite.of_surjective (fun b : Bool => if b then p else q) (by
    intro atom
    cases atom
    · exact ⟨true, rfl⟩
    · exact ⟨false, rfl⟩)

/-- `p` from itself first, then `p` as a fact. -/
def leftRecursive : OrderedProgram Atom :=
  [(p, [p]), (p, [])]

/-- The same rules, the fact first. -/
def factFirst : OrderedProgram Atom :=
  [(p, []), (p, [p])]

/-- **The two programs present the same rules.** -/
theorem dfs_programs_same_rules :
    programClauses leftRecursive = programClauses factFirst := by
  ext clause
  simp only [programClauses, leftRecursive, factFirst, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left, mem_ofPred_eq]
  exact or_comm

/-- **The goal is in the Horn closure.** -/
theorem goal_in_closure : p ∈ hornClosure (programClauses leftRecursive) ∅ := by
  have fact : (⟨{a | a ∈ ([] : List Atom)}, p⟩ : HornClause Atom) ∈
      programClauses leftRecursive := ⟨(p, []), by simp [leftRecursive], rfl⟩
  exact HornDerivable.rule _ fact fun a member => absurd member List.not_mem_nil

theorem dfsRun_leftRecursive (n : ℕ) :
    dfsRun leftRecursive [[p]] n = [p] :: List.replicate n [] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [dfsRun, Function.iterate_succ_apply', ← dfsRun, ih]
      rfl

/-- **Depth-first search never succeeds on the left-recursive order.** -/
theorem dfs_leftRecursive_never_succeeds (n : ℕ) :
    ¬ Succeeded (dfsRun leftRecursive [[p]] n) := by
  rw [dfsRun_leftRecursive]
  intro succeeded
  cases succeeded

/-- **The same search succeeds at once on the other order.** -/
theorem dfs_factFirst_succeeds : Succeeded (dfsRun factFirst [[p]] 1) :=
  rfl

/-- `q` from itself only. -/
def selfLoop : OrderedProgram Atom :=
  [(q, [q])]

theorem dfsRun_selfLoop (n : ℕ) : dfsRun selfLoop [[q]] n = [[q]] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [dfsRun, Function.iterate_succ_apply', ← dfsRun, ih]
      rfl

/-- **On a goal outside the closure, depth-first search neither succeeds nor
fails.** -/
theorem dfs_selfLoop_never_ends (n : ℕ) :
    ¬ Succeeded (dfsRun selfLoop [[q]] n) ∧ ¬ Failed (dfsRun selfLoop [[q]] n) := by
  rw [dfsRun_selfLoop]
  exact ⟨fun succeeded => (by cases succeeded), fun failed => (by cases failed)⟩

/-- **The Horn closure settles the question: nothing is derivable.** -/
theorem selfLoop_closure_empty : hornClosure (programClauses selfLoop) ∅ = ∅ := by
  apply eq_empty_of_forall_notMem
  intro g generated
  induction generated with
  | seed member => exact member
  | rule clause member _ ih =>
      obtain ⟨rule, inProgram, rfl⟩ := member
      simp only [selfLoop, List.mem_singleton] at inProgram
      subst inProgram
      exact ih q (List.mem_singleton_self q)

/-- **Iterative deepening finds the goal of both clause orders at bound one.** -/
theorem bounded_dfs_both_orders :
    provableWithin leftRecursive 1 [p] = true ∧ provableWithin factFirst 1 [p] = true :=
  ⟨rfl, rfl⟩

/-- **On the looping goal outside the closure, bounded search fails at every
bound**, so iterative deepening never stops on it; the empty Horn closure is the
certificate of failure (`selfLoop_closure_empty`). -/
theorem bounded_dfs_selfLoop (n : ℕ) : provableWithin selfLoop n [q] = false := by
  cases proved : provableWithin selfLoop n [q] with
  | false => rfl
  | true =>
      have member := provableWithin_sound selfLoop n [q] proved q List.mem_cons_self
      rw [selfLoop_closure_empty] at member
      exact member.elim

/-- Round-robin over the single rule of `selfLoop` is fair; it settles on the
empty closure. -/
theorem selfLoop_fair_run_settles :
    ∃ N, ∀ n, N ≤ n →
      run (fun clause : programClauses selfLoop => fire clause.1) ∅
          (fun _ => ⟨⟨{a | a ∈ [q]}, q⟩, ⟨(q, [q]), List.mem_singleton_self _, rfl⟩⟩) n = ∅ := by
  obtain ⟨N, reached⟩ := fair_firing_computes_hornClosure (programClauses selfLoop) ∅
    (schedule := fun _ => ⟨⟨{a | a ∈ [q]}, q⟩, ⟨(q, [q]), List.mem_singleton_self _, rfl⟩⟩)
    (by
      rintro ⟨clause, rule, inProgram, rfl⟩ N
      simp only [selfLoop, List.mem_singleton] at inProgram
      subst inProgram
      exact ⟨N, le_rfl, rfl⟩)
  exact ⟨N, fun n le => (reached n le).trans selfLoop_closure_empty⟩

#print axioms isLeast_target
#print axioms run_le_target
#print axioms run_eventually_eq_target
#print axioms schedule_independent
#print axioms roundRobin_fair
#print axioms target_fire_eq_hornClosure
#print axioms fair_firing_computes_hornClosure
#print axioms effectiveSteps_le_card
#print axioms dfs_programs_same_rules
#print axioms goal_in_closure
#print axioms dfs_leftRecursive_never_succeeds
#print axioms dfs_factFirst_succeeds
#print axioms dfs_selfLoop_never_ends
#print axioms selfLoop_closure_empty
#print axioms selfLoop_fair_run_settles
#print axioms provableWithin_append
#print axioms provableWithin_sound
#print axioms exists_provableWithin_iff
#print axioms provableWithin_congr
#print axioms bounded_dfs_both_orders
#print axioms bounded_dfs_selfLoop

end Mettapedia.GSLT.OpenEnded.ChaoticIteration
