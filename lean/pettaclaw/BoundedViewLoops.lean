/-!
# BoundedViewLoops — why a bounded window of results loops, and how
accumulated findings end the loop

An agent that decides each turn from its last `k` results, and from nothing
else, has no other state. While the environment is deterministic and
read-only (re-reading a file returns the same text), agent and environment
form one deterministic map on windows, and a deterministic map that
revisits a state cycles forever. The sections below prove:

1. once a window recurs, the run cycles, and what the first cycle lacks
   (submitting the finished work, say) never happens;
2. with finitely many possible results, a window recurs within the number
   of possible windows;
3. for `n > k`, every window-`k` policy fails on some instance to read `n`
   items and then finish;
4. accumulated findings succeed for every `n`, with a window of one result;
5. the agent cannot react to a harness event that leaves its view unchanged;
6. a supervisor that restarts a process whenever a post-turn predicate holds,
   keeping only the last result, turns the agent into a window-1 agent when
   the predicate holds after every first turn.

Correspondence (hand-maintained, as in the sibling files): the window ↔ the
recent results the harness shows the agent each turn; the notes ↔ a
findings list the agent appends to and the harness persists; `supervise` ↔
a restart rule that keeps only the last results.

Scope, stated openly: the environment is read-only during the phase
considered. An environment the agent writes to can hold its progress
instead; that is the remedy of the notes, kept outside the agent.
-/

namespace BoundedViewLoops

/-! ## Runs are orbits -/

/-- The orbit of a deterministic step, by iteration. Every run below is one. -/
def orbit {S : Type} (f : S → S) (s : S) : Nat → S
  | 0 => s
  | t + 1 => f (orbit f s t)

/-- Equal states have equal futures. -/
theorem orbit_shift {S : Type} (f : S → S) (s : S) {i j : Nat}
    (h : orbit f s i = orbit f s j) : ∀ m, orbit f s (i + m) = orbit f s (j + m)
  | 0 => h
  | m + 1 => congrArg f (orbit_shift f s h m)

/-- Once an orbit revisits a state, every state it ever reaches was reached
before the revisit. -/
theorem orbit_trapped {S : Type} (f : S → S) (s : S) {i j : Nat} (hij : i < j)
    (h : orbit f s i = orbit f s j) : ∀ t, ∃ u, u < j ∧ orbit f s t = orbit f s u
  | 0 => ⟨0, by omega, rfl⟩
  | t + 1 => by
    obtain ⟨u, hu, e⟩ := orbit_trapped f s hij h t
    by_cases hu' : u + 1 < j
    · exact ⟨u + 1, hu', congrArg f e⟩
    · exact ⟨i, hij, by rw [h, show j = u + 1 by omega]; exact congrArg f e⟩

/-! ## The window agent -/

/-- Slide a result into a window of `k`: the newest enters at the front,
the oldest leaves once more than `k` are held. -/
def slide {Obs : Type} (k : Nat) (o : Obs) (w : List Obs) : List Obs :=
  (o :: w).take k

/-- An agent whose only state is a window of its last `k` results. The
policy `π` is deterministic; the environment `env` is read-only, so the
result of an action is the same whenever it is taken. -/
structure WindowAgent (Obs Act : Type) where
  k : Nat
  π : List Obs → Act
  env : Act → Obs

namespace WindowAgent
variable {Obs Act : Type} (A : WindowAgent Obs Act)

/-- One turn: act on the window, then slide the result in. -/
def turn (w : List Obs) : List Obs := slide A.k (A.env (A.π w)) w

/-- The window held at turn `t` (starting empty), and the action taken then. -/
def view (t : Nat) : List Obs := orbit A.turn [] t
def act (t : Nat) : Act := A.π (A.view t)

/-- The results so far, newest first. -/
def results : Nat → List Obs
  | 0 => []
  | t + 1 => A.env (A.act t) :: results t

theorem view_succ (t : Nat) :
    A.view (t + 1) = slide A.k (A.env (A.act t)) (A.view t) := rfl

/-! ## 1. Periodicity -/

/-- **Periodicity.** If the windows at turns `i < j` agree, then from turn
`i` on the windows, and with them the actions, repeat with period `j - i`. -/
theorem periodic {i j : Nat} (hij : i < j) (h : A.view i = A.view j)
    (t : Nat) (ht : i ≤ t) :
    A.view (t + (j - i)) = A.view t ∧ A.act (t + (j - i)) = A.act t := by
  obtain ⟨m, rfl⟩ : ∃ m, t = i + m := ⟨t - i, by omega⟩
  have e : A.view (i + m + (j - i)) = A.view (i + m) := by
    rw [show i + m + (j - i) = j + m by omega]
    exact (orbit_shift A.turn [] h m).symm
  exact ⟨e, congrArg A.π e⟩

/-- **What the first cycle lacks never happens.** If the window at turn `j`
repeats an earlier one, an action not taken before turn `j` (submitting the
finished work, say) is never taken. -/
theorem never_taken {i j : Nat} (hij : i < j) (h : A.view i = A.view j)
    (a : Act) (hnot : ∀ t, t < j → A.act t ≠ a) (t : Nat) : A.act t ≠ a := by
  obtain ⟨u, hu, e⟩ := orbit_trapped A.turn [] hij h t
  rw [show A.act t = A.act u from congrArg A.π e]
  exact hnot u hu

end WindowAgent

/-! ## 2. The pigeonhole bound -/

/-- A duplicate-free list drawn from `L` is no longer than `L`. -/
theorem nodup_length_le {α : Type} [DecidableEq α] :
    ∀ (xs L : List α), xs.Nodup → (∀ x ∈ xs, x ∈ L) → xs.length ≤ L.length
  | [], _, _, _ => Nat.zero_le _
  | x :: xs, L, hnd, hsub => by
    obtain ⟨hx, hnd'⟩ := List.nodup_cons.mp hnd
    have ih := nodup_length_le xs (L.filter (· ≠ x)) hnd' fun y hy =>
      List.mem_filter.mpr ⟨hsub y (List.mem_cons_of_mem x hy),
        decide_eq_true fun e : y = x => hx (e ▸ hy)⟩
    have hlt : (L.filter (· ≠ x)).length < L.length :=
      List.length_filter_lt_length_iff_exists.mpr
        ⟨x, hsub x List.mem_cons_self, fun h => of_decide_eq_true h rfl⟩
    simp only [List.length_cons]; omega

/-- The values of a sequence before time `n`, newest first. -/
def firsts {α : Type} (g : Nat → α) : Nat → List α
  | 0 => []
  | n + 1 => g n :: firsts g n

theorem mem_firsts {α : Type} (g : Nat → α) {x : α} :
    ∀ {n}, x ∈ firsts g n → ∃ u, u < n ∧ g u = x
  | 0, h => absurd h List.not_mem_nil
  | n + 1, h => (List.mem_cons.mp h).elim (fun e => ⟨n, by omega, e.symm⟩)
      fun h' => let ⟨u, hu, e⟩ := mem_firsts g h'; ⟨u, by omega, e⟩

theorem length_firsts {α : Type} (g : Nat → α) (n : Nat) :
    (firsts g n).length = n := by
  induction n <;> simp [firsts, *]

/-- Either a value has repeated before time `n`, or the values so far are
distinct. -/
theorem repeat_or_nodup {α : Type} [DecidableEq α] (g : Nat → α) :
    ∀ n, (∃ i j, i < j ∧ j < n ∧ g i = g j) ∨ (firsts g n).Nodup
  | 0 => .inr List.nodup_nil
  | n + 1 => by
    rcases repeat_or_nodup g n with ⟨i, j, hij, hj, e⟩ | hnd
    · exact .inl ⟨i, j, hij, by omega, e⟩
    · by_cases hm : g n ∈ firsts g n
      · obtain ⟨u, hu, e⟩ := mem_firsts g hm
        exact .inl ⟨u, n, hu, by omega, e⟩
      · exact .inr (List.nodup_cons.mpr ⟨hm, hnd⟩)

/-- **Pigeonhole.** A sequence with values in `L` repeats a value by time
`L.length`. -/
theorem pigeonhole {α : Type} [DecidableEq α] (g : Nat → α) (L : List α)
    (hg : ∀ t, g t ∈ L) : ∃ i j, i < j ∧ j ≤ L.length ∧ g i = g j := by
  rcases repeat_or_nodup g (L.length + 1) with ⟨i, j, hij, hj, e⟩ | hnd
  · exact ⟨i, j, hij, Nat.le_of_lt_succ hj, e⟩
  · have := nodup_length_le _ L hnd fun x hx =>
      let ⟨u, _, e⟩ := mem_firsts g hx; e ▸ hg u
    rw [length_firsts] at this
    exact absurd this (Nat.not_succ_le_self _)

/-- Every window of at most `k` results drawn from `obs`, listed out. -/
def windows {Obs : Type} (obs : List Obs) : Nat → List (List Obs)
  | 0 => [[]]
  | k + 1 => [] :: obs.flatMap fun o => (windows obs k).map (o :: ·)

theorem mem_windows {Obs : Type} (obs : List Obs) :
    ∀ (k : Nat) (w : List Obs), w.length ≤ k → (∀ o ∈ w, o ∈ obs) →
      w ∈ windows obs k
  | 0, [], _, _ => List.mem_singleton_self _
  | 0, _ :: _, h, _ => absurd h (Nat.not_succ_le_zero _)
  | _ + 1, [], _, _ => List.mem_cons_self
  | k + 1, o :: w, h, hw => List.mem_cons_of_mem _ <| List.mem_flatMap.mpr
      ⟨o, hw o List.mem_cons_self, List.mem_map_of_mem <| mem_windows obs k w
        (Nat.le_of_succ_le_succ h) fun x hx => hw x (List.mem_cons_of_mem o hx)⟩

namespace WindowAgent
variable {Obs Act : Type} (A : WindowAgent Obs Act)

/-- When every result is drawn from `obs`, every window is in `windows obs k`. -/
theorem view_mem (obs : List Obs) (henv : ∀ a, A.env a ∈ obs) (t : Nat) :
    A.view t ∈ windows obs A.k := by
  suffices h : (A.view t).length ≤ A.k ∧ ∀ o ∈ A.view t, o ∈ obs from
    mem_windows obs A.k _ h.1 h.2
  induction t with
  | zero => exact ⟨Nat.zero_le _, fun _ h => absurd h List.not_mem_nil⟩
  | succ t ih =>
    rw [view_succ, slide, List.length_take]
    exact ⟨Nat.min_le_left _ _, fun o ho => (List.mem_cons.mp
      (List.mem_of_mem_take ho)).elim (fun e => e ▸ henv _) (ih.2 o)⟩

/-- **Pigeonhole bound.** If every result is drawn from the finite list `obs`,
some window recurs by turn `M`, the length of the list `windows obs k` of
possible windows; from there on the run is periodic (`periodic`). -/
theorem view_repeats [DecidableEq Obs] (obs : List Obs)
    (henv : ∀ a, A.env a ∈ obs) :
    ∃ i j, i < j ∧ j ≤ (windows obs A.k).length ∧ A.view i = A.view j :=
  pigeonhole A.view _ (A.view_mem obs henv)

/-- **Within the bound, or never.** Every action the agent ever takes, it
takes before turn `M`: if it has not submitted its work by then, it never
will. -/
theorem taken_early_or_never [DecidableEq Obs] (obs : List Obs)
    (henv : ∀ a, A.env a ∈ obs) (t : Nat) :
    ∃ u, u < (windows obs A.k).length ∧ A.act u = A.act t := by
  obtain ⟨i, j, hij, hj, h⟩ := A.view_repeats obs henv
  obtain ⟨u, hu, e⟩ := orbit_trapped A.turn [] hij h t
  exact ⟨u, by omega, (congrArg A.π e).symm⟩

end WindowAgent

/-! ## 3. Distant dependence is out of reach

In a read-only environment the agent can always re-read an item, so what a
window loses is not the content of the world but the agent's own progress.
The task below needs exactly that. -/

/-- **The window forgets.** The window is exactly the newest `k` results, so
runs whose newest `k` results agree hold the same window, however they
differ further back: instances that differ only in an old result are
indistinguishable. -/
theorem WindowAgent.view_eq_take {Obs Act : Type} (A : WindowAgent Obs Act) :
    ∀ t, A.view t = (A.results t).take A.k
  | 0 => List.take_nil.symm
  | t + 1 => by
    rw [A.view_succ, A.view_eq_take t, slide]
    cases A.k <;> simp [List.take_take, results]

/-- Commands of a reading task. -/
inductive Cmd
  | read (i : Nat)
  | finish
deriving DecidableEq

/-- A run completes "read all `n` items, then finish" when its first
`finish` comes after every item has been read. -/
def ReadsAll (n : Nat) (act : Nat → Cmd) : Prop :=
  ∃ T, act T = .finish ∧ (∀ t, t < T → act t ≠ .finish) ∧
    ∀ i, i < n → ∃ t, t < T ∧ act t = .read i

/-- **No window policy outreads its window.** When every result is the same
`c` (results that do not say which item produced them), no window-`k` agent
reads `n > k` items and then finishes: from turn `k` on its window is `k`
copies of `c` whatever it read, so it takes at most `k + 1` distinct commands,
fewer than the `n + 1` the task needs. -/
theorem window_cannot_read_all {Obs : Type} (A : WindowAgent Obs Cmd) (c : Obs)
    (hc : ∀ a, A.env a = c) (n : Nat) (hn : A.k < n) : ¬ ReadsAll n A.act := by
  intro ⟨T, hT, _, hread⟩
  have hres : ∀ t, A.results t = List.replicate t c := fun t => by
    induction t with
    | zero => rfl
    | succ t ih => show A.env (A.act t) :: A.results t = _; rw [hc, ih]; rfl
  have hview : ∀ t, A.k ≤ t → A.view t = List.replicate A.k c := fun t ht => by
    rw [A.view_eq_take, hres, List.take_replicate, Nat.min_eq_left ht]
  have hmem : ∀ t, A.act t ∈ (List.range (A.k + 1)).map A.act := fun t => by
    obtain ⟨u, hu, e⟩ := orbit_trapped A.turn [] (Nat.lt_succ_self _)
      ((hview _ (Nat.le_refl _)).trans (hview _ (Nat.le_succ _)).symm) t
    exact List.mem_map.mpr ⟨u, List.mem_range.mpr hu, (congrArg A.π e).symm⟩
  have hnd : (Cmd.finish :: firsts Cmd.read n).Nodup :=
    List.nodup_cons.mpr
      ⟨fun h => (by obtain ⟨_, _, e⟩ := mem_firsts _ h; cases e),
        (repeat_or_nodup Cmd.read n).resolve_left
          fun ⟨_, _, hij, _, e⟩ => Nat.ne_of_lt hij (Cmd.read.inj e)⟩
  have hle := nodup_length_le _ _ hnd fun x hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hT ▸ hmem T
    · obtain ⟨i, hi, rfl⟩ := mem_firsts _ hx
      obtain ⟨t, _, ht⟩ := hread i hi
      exact ht ▸ hmem t
  simp only [List.length_cons, length_firsts, List.length_map,
    List.length_range] at hle
  exact Nat.lt_irrefl _ (Nat.lt_of_le_of_lt (Nat.le_of_succ_le_succ hle) hn)

/-! ## 4. Accumulated findings fix it -/

/-- Record a finding, unless it is already recorded. -/
def jot {N : Type} [DecidableEq N] : Option N → List N → List N
  | none, ns => ns
  | some x, ns => if x ∈ ns then ns else ns ++ [x]

/-- **Notes only grow**: what was recorded stays, in place. -/
theorem notes_only_grow {N : Type} [DecidableEq N] (f : Option N) (ns : List N) :
    ns <+: jot f ns := by
  cases f with
  | none => exact List.prefix_refl ns
  | some x => by_cases hx : x ∈ ns <;> simp [jot, hx]

/-- An agent with a window of `k` results and a list of findings. Each turn
the policy reads both and returns an action and, optionally, a finding to
record; what it carries between turns is the pair (window, notes). -/
structure NotesAgent (Obs Act N : Type) where
  k : Nat
  π : List Obs → List N → Act × Option N
  env : Act → Obs

namespace NotesAgent
variable {Obs Act N : Type} [DecidableEq N] (A : NotesAgent Obs Act N)

def turn (m : List Obs × List N) : List Obs × List N :=
  (slide A.k (A.env (A.π m.1 m.2).1) m.1, jot (A.π m.1 m.2).2 m.2)

/-- Window and notes at turn `t` (starting empty), and the action taken then. -/
def mind (t : Nat) : List Obs × List N := orbit A.turn ([], []) t
def act (t : Nat) : Act := (A.π (A.mind t).1 (A.mind t).2).1

end NotesAgent

/-- Read the items in order, noting each item as it is read; finish once all
`n` are noted. The window is never consulted. -/
def reader {Obs : Type} (n : Nat) (_ : List Obs) (ns : List Nat) :
    Cmd × Option Nat :=
  if ns.length < n then (.read ns.length, some ns.length) else (.finish, none)

/-- **Accumulated findings fix it.** A notes agent running `reader n`
completes "read all `n` items, then finish" for every `n`, on every
instance, at every window size: one result, or none. By
`window_cannot_read_all`, no window-1 agent does so on every instance once
`n ≥ 2`. -/
theorem notes_read_all {Obs : Type} (A : NotesAgent Obs Cmd Nat) (n : Nat)
    (hπ : A.π = reader n) : ReadsAll n A.act := by
  have hnotes : ∀ t, t ≤ n → (A.mind t).2 = List.range t := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
      show jot (A.π (A.mind t).1 (A.mind t).2).2 (A.mind t).2 = _
      rw [ih (by omega), hπ, List.range_succ]
      simp [reader, jot, show t < n by omega]
  have hact : ∀ t, t ≤ n → A.act t = if t < n then .read t else .finish :=
    fun t ht => by
      show (A.π (A.mind t).1 (A.mind t).2).1 = _
      rw [hnotes t ht, hπ]; simp [reader]; split <;> rfl
  refine ⟨n, by simp [hact n (Nat.le_refl n)], fun t ht => ?_,
    fun i hi => ⟨i, hi, ?_⟩⟩
  · simp [hact t (by omega), ht]
  · simp [hact i (by omega), hi]

/-! ## 5. Visibility -/

/-- **An agent cannot react to what it cannot see.** A policy is a function
of its view, so a harness event (a restart, a truncation, a limit being
reached) that leaves the view unchanged leaves the next action unchanged.
For an agent to respond to a limit, the limit has to appear in its view. -/
theorem invisible_event {S V Act : Type} (see : S → V) (π : V → Act)
    (event : S → S) (s : S) (h : see (event s) = see s) :
    π (see (event s)) = π (see s) :=
  congrArg π h

/-! ## 6. A supervisor that restarts after every first turn -/

/-- A supervised process: what survived the last restart, and the results
of its own turns (newest first). Within a process the agent sees both. -/
structure Proc (Obs : Type) where
  carried : List Obs
  log : List Obs

/-- One supervised turn: the agent acts; if `stop` holds on the post-turn
state, the process is ended and a fresh one carries only the last result. -/
def supervise {Obs Act : Type} (stop : Proc Obs → Bool) (ρ : Proc Obs → Act)
    (env : Act → Obs) (p : Proc Obs) : Proc Obs :=
  let q : Proc Obs := ⟨p.carried, env (ρ p) :: p.log⟩
  if stop q then ⟨q.log.take 1, []⟩ else q

/-- **Restarted after every first turn, the agent is a window-1 agent.** If
`stop` holds after every first turn, each turn is taken by a fresh process
carrying exactly the window of the window-1 agent whose policy is `ρ` on a
fresh process, so every theorem above about window agents applies. -/
theorem supervised_is_window_one {Obs Act : Type} (stop : Proc Obs → Bool)
    (ρ : Proc Obs → Act) (env : Act → Obs)
    (hfirst : ∀ c o, stop ⟨c, [o]⟩ = true) :
    ∀ t, orbit (supervise stop ρ env) ⟨[], []⟩ t =
      ⟨(⟨1, fun w => ρ ⟨w, []⟩, env⟩ : WindowAgent Obs Act).view t, []⟩
  | 0 => rfl
  | t + 1 => by
    show supervise stop ρ env (orbit (supervise stop ρ env) ⟨[], []⟩ t) = _
    rw [supervised_is_window_one stop ρ env hfirst t]
    simp [supervise, hfirst]
    rfl

/-- **No process completes a second turn**: each turn is taken by a process
with no turn of its own behind it. -/
theorem supervised_one_turn {Obs Act : Type} (stop : Proc Obs → Bool)
    (ρ : Proc Obs → Act) (env : Act → Obs)
    (hfirst : ∀ c o, stop ⟨c, [o]⟩ = true) (t : Nat) :
    (orbit (supervise stop ρ env) ⟨[], []⟩ t).log = [] := by
  rw [supervised_is_window_one stop ρ env hfirst t]

/-- **Corollary.** Restarted after every first turn, the agent cannot read
two items and then finish when results look alike, whatever it would do in
a longer-lived process. -/
theorem supervised_cannot_read_all {Obs : Type} (stop : Proc Obs → Bool)
    (ρ : Proc Obs → Cmd) (c : Obs) (hfirst : ∀ c o, stop ⟨c, [o]⟩ = true)
    (n : Nat) (hn : 2 ≤ n) :
    ¬ ReadsAll n fun t =>
      ρ (orbit (supervise stop ρ fun _ => c) ⟨[], []⟩ t) := by
  intro hr
  simp only [supervised_is_window_one stop ρ _ hfirst] at hr
  exact window_cannot_read_all ⟨1, fun w => ρ ⟨w, []⟩, fun _ => c⟩ c
    (fun _ => rfl) n hn hr

end BoundedViewLoops

/-! ## Axiom audit (kernel-level trust check) -/
#print axioms BoundedViewLoops.WindowAgent.periodic
#print axioms BoundedViewLoops.WindowAgent.never_taken
#print axioms BoundedViewLoops.WindowAgent.view_repeats
#print axioms BoundedViewLoops.WindowAgent.taken_early_or_never
#print axioms BoundedViewLoops.WindowAgent.view_eq_take
#print axioms BoundedViewLoops.window_cannot_read_all
#print axioms BoundedViewLoops.notes_only_grow
#print axioms BoundedViewLoops.notes_read_all
#print axioms BoundedViewLoops.invisible_event
#print axioms BoundedViewLoops.supervised_is_window_one
#print axioms BoundedViewLoops.supervised_one_turn
#print axioms BoundedViewLoops.supervised_cannot_read_all
