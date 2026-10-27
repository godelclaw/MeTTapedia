import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs.SearchScheduling

/-!
# A program's continuation as a chain of tokens

Today a program runs its effects one after another. As a process over the occurrence store it runs
the same effects, each **threaded** through a private continuation token: the step that performs
effect `j` also takes token `j` and also makes token `j + 1` (`threaded`, `chain`). The tokens are
occurrences like any other, at a name no one else holds; they are the program's continuation,
reflected into the store.

## The embedding preserves the effects and their order, under every scheduler

When the tokens are apart from the data (`TokenFree`, `EffectApart`):

* at a store holding the data and token `j`, the only enabled step of the program is the one that
  performs effect `j`, and it is enabled exactly when the effect is (`threaded_enabled_iff`,
  `chain_enabled_unique`);
* **every maximal run of the program, whatever the scheduler picks, is the chain itself**
  (`maximal_chain_iff`): the effects in today's order, each once, and nothing else;
* it ends with today's data and the last token (`fireList_chain`).

So the commit semantics, which lets any enabled commit fire, runs a sequential program exactly as
today; the continuation token, not the scheduler, orders it.

## Beside other processes

Other processes may run beside the program as long as they neither take nor make its tokens. They
may read the tokens (inspecting the continuation) and query their region.

* **The program's own order is kept** (`chain_order_beside`): in every run of the whole system the
  program's steps, picked out by their process tag, form a prefix of the chain, in order. A
  parallel mode can interleave other processes' commits with the program's, never reorder or
  repeat the program's own.
* **Taking the token cancels** (`cancel_stops_chain`): a cancelling commit takes the current token
  and makes none. After it no step of the program ever fires again, in any run: the continuation
  is gone and nothing remakes it.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uO uR

section Chain

variable {O : Type uO} [DecidableEq O] {R : Type uR} {label : O → R}

/-- **Thread a continuation through a commit**: also take token `k`, also make token `k'`. -/
def threaded (k k' : O) (e : Commit O R) : Commit O R :=
  ⟨insert k e.taken, e.kept, insert k' e.made, e.queries⟩

/-- **The process of a program**: its effects in order, effect `i` threaded from token
`tok (j + i)` to token `tok (j + i + 1)`. -/
def chain (tok : ℕ → O) : ℕ → List (Commit O R) → List (Commit O R)
  | _, [] => []
  | j, e :: rest => threaded (tok j) (tok (j + 1)) e :: chain tok (j + 1) rest

@[simp] theorem chain_nil (tok : ℕ → O) (j : ℕ) : chain tok j ([] : List (Commit O R)) = [] := rfl

@[simp] theorem chain_cons (tok : ℕ → O) (j : ℕ) (e : Commit O R) (rest : List (Commit O R)) :
    chain tok j (e :: rest) = threaded (tok j) (tok (j + 1)) e :: chain tok (j + 1) rest := rfl

theorem length_chain (tok : ℕ → O) : ∀ (j : ℕ) (effects : List (Commit O R)),
    (chain tok j effects).length = effects.length
  | _, [] => rfl
  | j, _ :: rest => by simp [length_chain tok (j + 1) rest]

/-- The members of a chain, by position. -/
theorem mem_chain {tok : ℕ → O} {c : Commit O R} :
    ∀ {j : ℕ} {effects : List (Commit O R)},
      c ∈ chain tok j effects ↔
        ∃ i, ∃ h : i < effects.length, c = threaded (tok (j + i)) (tok (j + i + 1)) effects[i]
  | _, [] => by simp
  | j, e :: rest => by
      rw [chain_cons, List.mem_cons, mem_chain]
      constructor
      · rintro (rfl | ⟨i, h, rfl⟩)
        · exact ⟨0, by simp, by simp⟩
        · exact ⟨i + 1, by simpa using h, by simp [Nat.add_assoc, Nat.add_comm 1 i]⟩
      · rintro ⟨i, h, rfl⟩
        cases i with
        | zero => exact Or.inl (by simp)
        | succ i =>
            refine Or.inr ⟨i, by simpa using h, ?_⟩
            simp [Nat.add_assoc, Nat.add_comm 1 i]

/-- Dropping steps of a chain drops effects. -/
theorem drop_chain (tok : ℕ → O) : ∀ (j k : ℕ) (effects : List (Commit O R)),
    (chain tok j effects).drop k = chain tok (j + k) (effects.drop k)
  | j, 0, effects => by simp
  | j, k + 1, [] => by simp
  | j, k + 1, e :: rest => by
      rw [chain_cons, List.drop_succ_cons, List.drop_succ_cons, drop_chain tok (j + 1) k rest]
      congr 1
      omega

/-- A store holds no token. -/
def TokenFree (tok : ℕ → O) (store : Finset O) : Prop := ∀ i, tok i ∉ store

/-- An effect is apart from the tokens: it does not take, keep or make one, and none lies in the
region of one of its predicate queries. -/
structure EffectApart (label : O → R) (tok : ℕ → O) (e : Commit O R) : Prop where
  taken : ∀ i, tok i ∉ e.taken
  kept : ∀ i, tok i ∉ e.kept
  made : ∀ i, tok i ∉ e.made
  queries : ∀ read ∈ e.queries, ∀ i, read.region (label (tok i)) = false

variable {tok : ℕ → O}

/-- At a store whose only token is `tok k`, a commit that takes token `tok i` is enabled only if
`i = k`. -/
theorem token_index (injective : Function.Injective tok) {store : Finset O}
    (free : TokenFree tok store) {k i : ℕ} {c : Commit O R} (takes : tok i ∈ c.taken)
    (enabled : Enabled label (insert (tok k) store) c) : i = k := by
  rcases Finset.mem_insert.mp (enabled.taken_subset takes) with same | inStore
  · exact injective same
  · exact absurd inStore (free i)

/-- Adding a token does not change what an apart predicate query sees. -/
theorem regionOf_insert_token {store : Finset O} {e : Commit O R} (apart : EffectApart label tok e)
    {read : PredicateQuery O R} (member : read ∈ e.queries) (k : ℕ) :
    regionOf label (insert (tok k) store) read.region = regionOf label store read.region := by
  ext o
  simp only [mem_regionOf, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | inStore, inRegion⟩
    · rw [apart.queries read member k] at inRegion; exact absurd inRegion (by decide)
    · exact ⟨inStore, inRegion⟩
  · rintro ⟨inStore, inRegion⟩
    exact ⟨Or.inr inStore, inRegion⟩

/-- **The threaded step is enabled exactly when the effect is.** -/
theorem threaded_enabled_iff (injective : Function.Injective tok) {store : Finset O}
    (free : TokenFree tok store) {e : Commit O R} (apart : EffectApart label tok e) (j : ℕ) :
    Enabled label (insert (tok j) store) (threaded (tok j) (tok (j + 1)) e) ↔
      Enabled label store e := by
  constructor
  · intro enabled
    refine ⟨fun o taken => ?_, fun o kept => ?_, ?_, ?_, fun read member => ?_⟩
    · rcases Finset.mem_insert.mp (enabled.taken_subset (Finset.mem_insert_of_mem taken)) with
        same | inStore
      · subst same; exact absurd taken (apart.taken j)
      · exact inStore
    · rcases Finset.mem_insert.mp (enabled.kept_subset kept) with same | inStore
      · subst same; exact absurd kept (apart.kept j)
      · exact inStore
    · exact Finset.disjoint_of_subset_left (Finset.subset_insert _ _) enabled.apart
    · exact Finset.disjoint_of_subset_left (Finset.subset_insert _ _)
        (Finset.disjoint_of_subset_right (Finset.subset_insert _ _) enabled.fresh)
    · have holds := enabled.queries_hold read member
      unfold PredicateQuery.Holds at holds ⊢
      rwa [regionOf_insert_token apart member j] at holds
  · intro enabled
    refine ⟨Finset.insert_subset_insert _ enabled.taken_subset,
      enabled.kept_subset.trans (Finset.subset_insert _ _), ?_, ?_, fun read member => ?_⟩
    · exact Finset.disjoint_insert_left.mpr ⟨apart.kept j, enabled.apart⟩
    · refine Finset.disjoint_insert_left.mpr ⟨?_, ?_⟩
      · rw [Finset.mem_insert, not_or]
        exact ⟨fun same => absurd (injective same) (by omega), free (j + 1)⟩
      · exact Finset.disjoint_insert_right.mpr ⟨apart.made j, enabled.fresh⟩
    · have holds := enabled.queries_hold read member
      unfold PredicateQuery.Holds at holds ⊢
      rwa [regionOf_insert_token apart member j]

/-- **Firing a threaded step** moves the token on and fires the effect. -/
theorem fire_threaded {store : Finset O} (free : TokenFree tok store) (e : Commit O R) (j k : ℕ) :
    fire (insert (tok j) store) (threaded (tok j) (tok k) e) = insert (tok k) (fire store e) := by
  ext o
  simp only [fire, threaded, Finset.mem_union, Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro (⟨rfl | inStore, notTaken⟩ | rfl | made)
    · exact absurd (Or.inl rfl) notTaken
    · exact Or.inr (Or.inl ⟨inStore, fun taken => notTaken (Or.inr taken)⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inr made)
  · rintro (rfl | ⟨inStore, notTaken⟩ | made)
    · exact Or.inr (Or.inl rfl)
    · refine Or.inl ⟨Or.inr inStore, ?_⟩
      rintro (same | taken)
      · subst same; exact free j inStore
      · exact notTaken taken
    · exact Or.inr (Or.inr made)

/-- Firing an apart effect keeps a store free of tokens. -/
theorem fire_tokenFree {store : Finset O} (free : TokenFree tok store) {e : Commit O R}
    (apart : EffectApart label tok e) : TokenFree tok (fire store e) := by
  intro i member
  rcases mem_fire.mp member with ⟨inStore, _⟩ | made
  · exact free i inStore
  · exact apart.made i made

theorem fireList_tokenFree {store : Finset O} (free : TokenFree tok store) :
    ∀ {effects : List (Commit O R)}, (∀ e ∈ effects, EffectApart label tok e) →
      TokenFree tok (fireList store effects)
  | [], _ => free
  | e :: rest, apart => by
      rw [fireList_cons]
      exact fireList_tokenFree (fire_tokenFree free (apart e List.mem_cons_self))
        fun x member => apart x (List.mem_cons_of_mem _ member)

/-- **The chain ends with the effects' store and the last token.** -/
theorem fireList_chain : ∀ {store : Finset O} {j : ℕ} {effects : List (Commit O R)},
    TokenFree tok store → (∀ e ∈ effects, EffectApart label tok e) →
    fireList (insert (tok j) store) (chain tok j effects) =
      insert (tok (j + effects.length)) (fireList store effects)
  | store, j, [], _, _ => by simp
  | store, j, e :: rest, free, apart => by
      rw [chain_cons, fireList_cons, fire_threaded free, fireList_cons,
        fireList_chain (fire_tokenFree free (apart e List.mem_cons_self))
          fun x member => apart x (List.mem_cons_of_mem _ member)]
      simp [Nat.add_assoc, Nat.add_comm 1]

/-! ## Every scheduler runs the chain -/

/-- A maximal run that starts with a commit continues as a maximal run. -/
theorem Maximal.tail {sys : Commit O R → Prop} {store : Finset O} {c : Commit O R}
    {rest : List (Commit O R)} (maximal : Maximal label sys store (c :: rest)) :
    Maximal label sys (fire store c) rest :=
  ⟨(isRun_cons_iff.mp maximal.1).2.2, by simpa using maximal.2⟩

theorem Maximal.cons {sys : Commit O R → Prop} {store : Finset O} {c : Commit O R}
    {rest : List (Commit O R)} (member : sys c) (enabled : Enabled label store c)
    (maximal : Maximal label sys (fire store c) rest) : Maximal label sys store (c :: rest) :=
  ⟨isRun_cons_iff.mpr ⟨member, enabled, maximal.1⟩, by simpa using maximal.2⟩

/-- **At most one step of a chain is enabled**: at a store holding token `tok k` and no other, the
only enabled step is the `k`-th, and none when `k` is past the end. -/
theorem chain_enabled_unique (injective : Function.Injective tok) {effects : List (Commit O R)}
    {store : Finset O} (free : TokenFree tok store) {k : ℕ} {c : Commit O R}
    (member : c ∈ chain tok 0 effects) (enabled : Enabled label (insert (tok k) store) c) :
    ∃ h : k < effects.length, c = threaded (tok k) (tok (k + 1)) effects[k] := by
  obtain ⟨i, h, rfl⟩ := mem_chain.mp member
  have same : 0 + i = k := token_index injective free (Finset.mem_insert_self _ _) enabled
  simp only [Nat.zero_add] at same
  subst same
  exact ⟨h, by simp⟩

/-- **The sequential embedding, suffix form.** -/
theorem maximal_suffix_iff (injective : Function.Injective tok) {initial : Finset O}
    (free : TokenFree tok initial) {effects : List (Commit O R)}
    (apart : ∀ e ∈ effects, EffectApart label tok e) :
    ∀ (rest done : List (Commit O R)), effects = done ++ rest →
      Executable label (fireList initial done) rest → ∀ run,
      Maximal label (fun c => c ∈ chain tok 0 effects)
          (insert (tok done.length) (fireList initial done)) run ↔
        run = chain tok done.length rest
  | [], done, split, _, run => by
      subst split
      have noneEnabled : Terminal label (fun c => c ∈ chain tok 0 (done ++ []))
          (insert (tok done.length) (fireList initial done)) := by
        intro c member enabled
        obtain ⟨h, _⟩ := chain_enabled_unique injective
          (fireList_tokenFree free fun e m => apart e (by simpa using m)) member enabled
        simp at h
      constructor
      · intro maximal
        cases run with
        | nil => rfl
        | cons c rest =>
            obtain ⟨member, enabled, _⟩ := isRun_cons_iff.mp maximal.1
            exact absurd enabled (noneEnabled c member)
      · rintro rfl
        exact ⟨IsRun.nil _, by simpa using noneEnabled⟩
  | e :: rest, done, split, executable, run => by
      have freeDone : TokenFree tok (fireList initial done) :=
        fireList_tokenFree free fun x m => apart x (by rw [split]; simp [m])
      have apartE : EffectApart label tok e := apart e (by rw [split]; simp)
      obtain ⟨enabledE, executableRest⟩ := executable_cons_iff.mp executable
      have position : (done.length) < effects.length := by rw [split]; simp
      have atPosition : effects[done.length] = e := by
        simp only [split, List.getElem_append_right (Nat.le_refl _), Nat.sub_self,
          List.getElem_cons_zero]
      have memberHead : threaded (tok done.length) (tok (done.length + 1)) e ∈ chain tok 0 effects :=
        mem_chain.mpr ⟨done.length, position, by simp [atPosition]⟩
      have enabledHead : Enabled label (insert (tok done.length) (fireList initial done))
          (threaded (tok done.length) (tok (done.length + 1)) e) :=
        (threaded_enabled_iff injective freeDone apartE _).mpr enabledE
      have next : fire (insert (tok done.length) (fireList initial done))
          (threaded (tok done.length) (tok (done.length + 1)) e) =
          insert (tok (done ++ [e]).length) (fireList initial (done ++ [e])) := by
        rw [fire_threaded freeDone, fireList_append]
        simp
      have ih := maximal_suffix_iff injective free apart rest (done ++ [e]) (by simp [split])
        (by rw [fireList_append]; simpa using executableRest)
      constructor
      · intro maximal
        cases run with
        | nil => exact absurd enabledHead (maximal.2 _ memberHead)
        | cons c tail =>
            obtain ⟨member, enabled, _⟩ := isRun_cons_iff.mp maximal.1
            obtain ⟨_, same⟩ := chain_enabled_unique injective freeDone member enabled
            rw [atPosition] at same
            subst same
            have tailMaximal := maximal.tail
            rw [next] at tailMaximal
            rw [(ih tail).mp tailMaximal]
            simp
      · rintro rfl
        rw [chain_cons]
        refine Maximal.cons memberHead enabledHead ?_
        rw [next]
        exact (ih _).mpr (by simp)

/-- **The sequential embedding preserves the effects and their order, under every scheduler.**
Every maximal run of the program's process from the data and the first token is the chain: today's
effects, in today's order, each once. -/
theorem maximal_chain_iff (injective : Function.Injective tok) {initial : Finset O}
    (free : TokenFree tok initial) {effects : List (Commit O R)}
    (apart : ∀ e ∈ effects, EffectApart label tok e) (executable : Executable label initial effects)
    (run : List (Commit O R)) :
    Maximal label (fun c => c ∈ chain tok 0 effects) (insert (tok 0) initial) run ↔
      run = chain tok 0 effects := by
  simpa using maximal_suffix_iff injective free apart effects [] (by simp) (by simpa using executable)
    run

/-- **One token at a time**: every store the program reaches holds exactly one token, beside data
with no token. -/
theorem chain_reaches_one_token (injective : Function.Injective tok) {effects : List (Commit O R)}
    (apart : ∀ e ∈ effects, EffectApart label tok e) :
    ∀ (run : List (Commit O R)) (k : ℕ) (data : Finset O), TokenFree tok data →
      IsRun label (fun c => c ∈ chain tok 0 effects) (insert (tok k) data) run →
      ∃ k' data', TokenFree tok data' ∧ fireList (insert (tok k) data) run = insert (tok k') data'
  | [], k, data, free, _ => ⟨k, data, free, rfl⟩
  | c :: rest, k, data, free, isRun => by
      obtain ⟨member, enabled, isRest⟩ := isRun_cons_iff.mp isRun
      obtain ⟨h, rfl⟩ := chain_enabled_unique injective free member enabled
      have apartK : EffectApart label tok effects[k] := apart _ (List.getElem_mem h)
      rw [fire_threaded free] at isRest
      obtain ⟨k', data', free', eq⟩ :=
        chain_reaches_one_token injective apart rest (k + 1) _ (fire_tokenFree free apartK) isRest
      exact ⟨k', data', free', by rw [fireList_cons, fire_threaded free]; exact eq⟩

/-- **The program's process is conflict-free**: at every store it reaches, at most one of its steps
is enabled. -/
theorem chain_conflictFree (injective : Function.Injective tok) {initial : Finset O}
    (free : TokenFree tok initial) {effects : List (Commit O R)}
    (apart : ∀ e ∈ effects, EffectApart label tok e) :
    ConflictFree label (fun c => c ∈ chain tok 0 effects) (insert (tok 0) initial) := by
  rintro t ⟨run, isRun, rfl⟩ c d memberC memberD ne enabledC enabledD
  obtain ⟨k, data, freeData, eq⟩ := chain_reaches_one_token injective apart run 0 initial free isRun
  rw [eq] at enabledC enabledD
  obtain ⟨_, rfl⟩ := chain_enabled_unique injective freeData memberC enabledC
  obtain ⟨_, rfl⟩ := chain_enabled_unique injective freeData memberD enabledD
  exact absurd rfl ne

/-! ## Beside other processes -/

/-- A commit that neither takes nor makes a token. It may keep (read) tokens and query their
region. -/
structure TokenNeutral (tok : ℕ → O) (c : Commit O R) : Prop where
  taken : ∀ i, tok i ∉ c.taken
  made : ∀ i, tok i ∉ c.made

/-- Firing a token-neutral commit leaves the token where it is. -/
theorem fire_insert_neutral {store : Finset O} {c : Commit O R} (neutral : TokenNeutral tok c)
    (k : ℕ) : fire (insert (tok k) store) c = insert (tok k) (fire store c) := by
  ext o
  simp only [mem_fire, Finset.mem_insert]
  constructor
  · rintro (⟨rfl | inStore, notTaken⟩ | made)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl ⟨inStore, notTaken⟩)
    · exact Or.inr (Or.inr made)
  · rintro (rfl | ⟨inStore, notTaken⟩ | made)
    · exact Or.inl ⟨Or.inl rfl, neutral.taken k⟩
    · exact Or.inl ⟨Or.inr inStore, notTaken⟩
    · exact Or.inr made

theorem fire_tokenFree_neutral {store : Finset O} (free : TokenFree tok store) {c : Commit O R}
    (neutral : TokenNeutral tok c) : TokenFree tok (fire store c) := by
  intro i member
  rcases mem_fire.mp member with ⟨inStore, _⟩ | made
  · exact free i inStore
  · exact neutral.made i made

/-- A cancelling commit takes some token and makes none. -/
structure Cancels (tok : ℕ → O) (c : Commit O R) : Prop where
  takes : ∃ i, tok i ∈ c.taken
  made : ∀ i, tok i ∉ c.made

/-- The program beside other processes and cancelling commits. -/
def beside (tok : ℕ → O) (effects : List (Commit O R)) (others cancels : Commit O R → Prop) :
    Commit O R → Prop :=
  fun c => c ∈ chain tok 0 effects ∨ others c ∨ cancels c

section Beside

variable {effects : List (Commit O R)} {others cancels : Commit O R → Prop}
  (neutral : ∀ c, others c → TokenNeutral tok c) (cancelling : ∀ c, cancels c → Cancels tok c)
  (tag : Commit O R → Bool) (tagOthers : ∀ c, others c → tag c = false)
  (tagCancels : ∀ c, cancels c → tag c = false)

include neutral cancelling tagOthers in
/-- **Once no token is left, the program is over**: from a store with no token, no step of the
program fires and nothing cancels. -/
theorem beside_without_token : ∀ (run : List (Commit O R)) (data : Finset O), TokenFree tok data →
    IsRun label (beside tok effects others cancels) data run →
    run.filter tag = [] ∧ ∀ c ∈ run, ¬ cancels c
  | [], _, _, _ => by simp
  | c :: rest, data, free, isRun => by
      obtain ⟨member, enabled, isRest⟩ := isRun_cons_iff.mp isRun
      rcases member with inChain | other | cancel
      · obtain ⟨i, _, rfl⟩ := mem_chain.mp inChain
        exact absurd (enabled.taken_subset (Finset.mem_insert_self _ _)) (free _)
      · have after := beside_without_token rest _
          (fire_tokenFree_neutral free (neutral c other)) isRest
        refine ⟨by simp [tagOthers c other, after.1], ?_⟩
        intro x member
        rcases List.mem_cons.mp member with same | inRest
        · intro cancel
          rw [same] at cancel
          obtain ⟨i, takes⟩ := (cancelling c cancel).takes
          exact free i (enabled.taken_subset takes)
        · exact after.2 x inRest
      · obtain ⟨i, takes⟩ := (cancelling c cancel).takes
        exact absurd (enabled.taken_subset takes) (free i)

include neutral cancelling tagOthers tagCancels in
/-- **The program's order beside other processes, and cancellation.** In every run of the program
beside token-neutral processes and cancelling commits, with a process tag that picks out the
program's steps, those steps form a prefix of the chain, in order; and after a cancellation none of
them fires. -/
theorem chain_order_cancel (injective : Function.Injective tok)
    (apart : ∀ e ∈ effects, EffectApart label tok e)
    (tagChain : ∀ c ∈ chain tok 0 effects, tag c = true) :
    ∀ (run : List (Commit O R)) (k : ℕ) (data : Finset O), TokenFree tok data →
      IsRun label (beside tok effects others cancels) (insert (tok k) data) run →
      (run.filter tag) <+: (chain tok 0 effects).drop k ∧
        ∀ pre c post, run = pre ++ c :: post → cancels c → post.filter tag = []
  | [], _, _, _, _ => by simp
  | c :: rest, k, data, free, isRun => by
      obtain ⟨member, enabled, isRest⟩ := isRun_cons_iff.mp isRun
      rcases member with inChain | other | cancel
      · obtain ⟨h, rfl⟩ := chain_enabled_unique injective free inChain enabled
        have apartK : EffectApart label tok effects[k] := apart _ (List.getElem_mem h)
        rw [fire_threaded free] at isRest
        obtain ⟨isPrefix, afterCancel⟩ := chain_order_cancel
          injective apart tagChain rest (k + 1) _ (fire_tokenFree free apartK) isRest
        refine ⟨?_, ?_⟩
        · rw [List.filter_cons_of_pos (tagChain _ inChain)]
          have drop : (chain tok 0 effects).drop k =
              threaded (tok k) (tok (k + 1)) effects[k] :: (chain tok 0 effects).drop (k + 1) := by
            rw [drop_chain, drop_chain, List.drop_eq_getElem_cons h, chain_cons]
            simp only [Nat.zero_add]
          rw [drop]
          exact (List.prefix_cons_inj _).mpr isPrefix
        · intro pre x post split cancel
          cases pre with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at split
              obtain ⟨rfl, -⟩ := split
              exact absurd (tagChain _ inChain) (by simp [tagCancels _ cancel])
          | cons y pre' =>
              simp only [List.cons_append, List.cons.injEq] at split
              exact afterCancel pre' x post split.2 cancel
      · rw [fire_insert_neutral (neutral c other)] at isRest
        obtain ⟨isPrefix, afterCancel⟩ := chain_order_cancel
          injective apart tagChain rest k _ (fire_tokenFree_neutral free (neutral c other)) isRest
        refine ⟨by rw [List.filter_cons_of_neg (by simp [tagOthers c other])]; exact isPrefix, ?_⟩
        intro pre x post split cancel
        cases pre with
        | nil =>
            simp only [List.nil_append, List.cons.injEq] at split
            obtain ⟨i, takes⟩ := (cancelling x cancel).takes
            rw [← split.1] at takes
            exact absurd takes ((neutral c other).taken i)
        | cons y pre' =>
            simp only [List.cons_append, List.cons.injEq] at split
            exact afterCancel pre' x post split.2 cancel
      · obtain ⟨i, takes⟩ := (cancelling c cancel).takes
        have same := token_index injective free takes enabled
        subst same
        have freeAfter : TokenFree tok (fire (insert (tok i) data) c) := by
          intro j member
          rcases mem_fire.mp member with ⟨inStore, notTaken⟩ | made
          · rcases Finset.mem_insert.mp inStore with same | inData
            · rw [injective same] at notTaken; exact notTaken takes
            · exact free j inData
          · exact (cancelling c cancel).made j made
        obtain ⟨none, noCancel⟩ :=
          beside_without_token neutral cancelling tag tagOthers rest _ freeAfter isRest
        refine ⟨?_, ?_⟩
        · rw [List.filter_cons_of_neg (by simp [tagCancels c cancel]), none]
          exact List.nil_prefix
        · intro pre x post split cancelX
          cases pre with
          | nil =>
              simp only [List.nil_append, List.cons.injEq] at split
              obtain ⟨-, rfl⟩ := split
              exact none
          | cons y pre' =>
              simp only [List.cons_append, List.cons.injEq] at split
              exact absurd cancelX (noCancel x (by rw [split.2]; simp))

end Beside

end Chain

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Programs
