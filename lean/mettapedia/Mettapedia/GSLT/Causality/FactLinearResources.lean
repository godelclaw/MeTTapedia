import Mettapedia.GSLT.Causality.ResourceConfluence

/-!
# Facts and linear resources in one system

A resource system (`ResourceInteraction.System`) lets each rule instance consume one bag, read a
second bag without consuming it, and produce a third. A *declaration of facts* splits the resources
into two kinds:

* a **fact** is never consumed by any instance: it may only be read, so rules keep it;
* a **linear** resource may be consumed: it is a message, a token, or a resource to spend.

A system *respects* the declaration (`ConsumesNoFacts`) when no instance consumes a fact. Reads may
touch both kinds: reading a fact is keeping it, and reading a linear resource is peeking at it.

## What the declaration buys

* **Facts only accumulate** (`factCount_le_fire`, `factCount_le_of_run`): along every run, each fact is
  present at least as often as before.
* **A fact read is never stranded** (`enables_iff_linear_of_run`): if an instance's fact reads were
  available at an earlier snapshot, then at any later state of the run it is enabled exactly when its
  linear demand (its consumption and its linear reads) fits. A commit therefore needs to validate the
  linear part of a join only; its fact reads may come from any earlier snapshot.
* **Every conflict is a shortage of a linear resource** (`concurrent_of_linear_fits`,
  `exists_linear_shortfall`): two enabled instances that are not concurrent lack some linear resource
  for their joint demand.
* **Keep-only systems have no conflicts** (`keepOnly_conflictFree`, `keepOnly_confluent`), and every run
  only grows the bag (`le_of_run_of_keepOnly`). Over bags this has a price: a keep-only instance that
  produces anything stays enabled forever, so no run from a state enabling it is ever quiescent
  (`keepOnly_never_quiescent`). Keeping facts in a bag store therefore needs either an idempotent store
  or a consumed activation (a rule instance fired once).

## What keep cannot do

* **No keep-only target is faithful to a consuming source up to an upward-closed observation**
  (`keepOnly_not_faithful`): if some source step loses an observable, no operationally complete
  encoding into a keep-only system reflects that observable through any upward-closed test of bags.
* The same holds in a mixed system for any test that reads facts only (`factObservation_not_faithful`):
  an observable that a step can remove must be carried by a linear resource.

## Controls

* **A crossed pair of joins** (`Crossed`): two joins each take `a` and `b`. Taken atomically, every
  quiescent state reached from `{r₁, r₂, a, b}` holds a result (`atomic_quiescent_has_result`). Taken one
  resource at a time, a run reaches the quiescent state `{h₁, h₂}`, where each join holds half of what it
  needs and no result exists (`sequential_deadlock`). When `a` and `b` are facts that the joins read, the
  sequential version cannot deadlock this way: each holder stays enabled (`factReads_never_stranded`).
* **A peek at a linear resource can go stale** (`linear_peek_stale`): an instance that read a linear token
  at a snapshot is disabled once another instance consumes the token, so peeks need validation at commit.
* **A consumable fact breaks the declaration** (`consumed_fact_not_monotone`): one instance that consumes a
  declared fact makes the fact count drop.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ResourceInteraction

universe uRes uRule

namespace System

variable {R : Type uRes} (S : System.{uRes, uRule} R)

/-! ## The declaration of facts -/

section Declaration

variable (fact : R → Prop)

/-- **The system respects a declaration of facts**: no instance consumes a fact. -/
def ConsumesNoFacts : Prop :=
  ∀ {site : S.Site} (i : S.Instance site), ∀ r ∈ S.consume i, ¬ fact r

/-- **Keep-only**: no instance consumes anything. Every rule keeps everything it reads. -/
def KeepOnly : Prop :=
  ∀ {site : S.Site} (i : S.Instance site), S.consume i = 0

/-- A keep-only system respects every declaration of facts. -/
theorem KeepOnly.consumesNoFacts {S : System.{uRes, uRule} R} (keep : S.KeepOnly) :
    S.ConsumesNoFacts fact := by
  intro site i r member
  rw [keep i] at member
  exact absurd member (Multiset.notMem_zero r)

end Declaration

variable [DecidableEq R]

/-- The count of a resource after a firing: what was there, less what is consumed, plus what is
produced. -/
theorem count_fire (M : Multiset R) {site : S.Site} (i : S.Instance site) (r : R) :
    (S.fire M i).count r = M.count r - (S.consume i).count r + (S.produce i).count r := by
  simp [fire, Multiset.count_add, Multiset.count_sub]

/-! ## Facts only accumulate -/

section Facts

variable {fact : R → Prop}

/-- **A firing never lowers the count of a fact.** -/
theorem factCount_le_fire (respects : S.ConsumesNoFacts fact) (M : Multiset R)
    {site : S.Site} (i : S.Instance site) {r : R} (isFact : fact r) :
    M.count r ≤ (S.fire M i).count r := by
  have none : (S.consume i).count r = 0 :=
    Multiset.count_eq_zero.mpr fun member => respects i r member isFact
  rw [count_fire, none, Nat.sub_zero]
  exact Nat.le_add_right _ _

/-- **Along every run, each fact is present at least as often as at the start.** -/
theorem factCount_le_of_run (respects : S.ConsumesNoFacts fact) {M N : Multiset R}
    (run : Relation.ReflTransGen S.theory.rewrites M N) {r : R} (isFact : fact r) :
    M.count r ≤ N.count r := by
  induction run with
  | refl => exact le_rfl
  | tail _ step previous =>
    obtain ⟨site, i, -, rfl⟩ := step
    exact le_trans previous (S.factCount_le_fire respects _ i isFact)

variable [DecidablePred fact]

/-- The fact part of a bag. -/
def factPart (fact : R → Prop) [DecidablePred fact] (M : Multiset R) : Multiset R :=
  M.filter fact

/-- The linear part of a bag. -/
def linearPart (fact : R → Prop) [DecidablePred fact] (M : Multiset R) : Multiset R :=
  M.filter fun r => ¬ fact r

/-- **The fact part grows along every run.** -/
theorem factPart_le_of_run (respects : S.ConsumesNoFacts fact) {M N : Multiset R}
    (run : Relation.ReflTransGen S.theory.rewrites M N) : factPart fact M ≤ factPart fact N := by
  rw [Multiset.le_iff_count]
  intro r
  by_cases isFact : fact r
  · simp only [factPart, Multiset.count_filter_of_pos isFact]
    exact S.factCount_le_of_run respects run isFact
  · simp [factPart, Multiset.count_filter_of_neg isFact]

/-! ## A fact read is never stranded -/

/-- **Commit-time validation needs the linear demand only.** If an instance's fact reads were present
at a state `M`, then at every state `N` reached from `M` the instance is enabled exactly when its
consumption and its linear reads fit in `N`. -/
theorem enables_iff_linear_of_run (respects : S.ConsumesNoFacts fact) {M N : Multiset R}
    (run : Relation.ReflTransGen S.theory.rewrites M N) {site : S.Site} (i : S.Instance site)
    (factReads : factPart fact (S.read i) ≤ M) :
    S.Enables N i ↔ S.consume i + linearPart fact (S.read i) ≤ N := by
  constructor
  · intro enabled
    refine le_trans (add_le_add le_rfl ?_) enabled
    exact Multiset.filter_le _ _
  · intro fits
    unfold Enables
    rw [Multiset.le_iff_count] at fits factReads ⊢
    intro r
    have fitsAt := fits r
    have readsAt := factReads r
    simp only [Multiset.count_add] at fitsAt ⊢
    by_cases isFact : fact r
    · have none : (S.consume i).count r = 0 :=
        Multiset.count_eq_zero.mpr fun member => respects i r member isFact
      simp only [factPart, Multiset.count_filter_of_pos isFact] at readsAt
      rw [none, Nat.zero_add]
      exact le_trans readsAt (S.factCount_le_of_run respects run isFact)
    · have linearAt : (linearPart fact (S.read i)).count r = (S.read i).count r :=
        Multiset.count_filter_of_pos (p := fun r => ¬ fact r) isFact
      rw [linearAt] at fitsAt
      exact fitsAt

/-- **A fact read is never stranded.** An instance enabled at `M`, all of whose reads are facts, is
enabled at every later state that still holds its consumption. -/
theorem enables_of_run_of_factReads (respects : S.ConsumesNoFacts fact) {M N : Multiset R}
    (run : Relation.ReflTransGen S.theory.rewrites M N) {site : S.Site} {i : S.Instance site}
    (enabled : S.Enables M i) (readsFacts : ∀ r ∈ S.read i, fact r) (holds : S.consume i ≤ N) :
    S.Enables N i := by
  have factReads : factPart fact (S.read i) ≤ M := by
    have same : factPart fact (S.read i) = S.read i := Multiset.filter_eq_self.mpr readsFacts
    rw [same]
    exact le_trans (Multiset.le_add_left _ _) enabled
  have noLinear : linearPart fact (S.read i) = 0 :=
    Multiset.filter_eq_nil.mpr fun r member => not_not.mpr (readsFacts r member)
  refine (S.enables_iff_linear_of_run respects run i factReads).mpr ?_
  rw [noLinear, add_zero]
  exact holds

/-! ## Every conflict is a shortage of a linear resource -/

/-- **Two enabled instances whose joint linear demand fits are concurrent.** Facts never decide a
conflict: each is read, and readers share. -/
theorem concurrent_of_linear_fits (respects : S.ConsumesNoFacts fact) {M : Multiset R}
    {site₁ site₂ : S.Site} {i : S.Instance site₁} {j : S.Instance site₂}
    (enabledI : S.Enables M i) (enabledJ : S.Enables M j)
    (linearFits : ∀ r, ¬ fact r →
      (S.consume i + S.consume j + (S.read i ∪ S.read j)).count r ≤ M.count r) :
    S.Concurrent M i j := by
  rw [concurrent_iff_union, Multiset.le_iff_count]
  intro r
  by_cases isFact : fact r
  · have noneI : (S.consume i).count r = 0 :=
      Multiset.count_eq_zero.mpr fun member => respects i r member isFact
    have noneJ : (S.consume j).count r = 0 :=
      Multiset.count_eq_zero.mpr fun member => respects j r member isFact
    have readI := (Multiset.le_iff_count.mp (le_trans (Multiset.le_add_left _ _) enabledI)) r
    have readJ := (Multiset.le_iff_count.mp (le_trans (Multiset.le_add_left _ _) enabledJ)) r
    simp only [Multiset.count_add, Multiset.count_union, noneI, noneJ, Nat.zero_add]
    exact max_le readI readJ
  · exact linearFits r isFact

/-- **A conflict names a linear resource.** Two enabled instances that are not concurrent need more of
some linear resource than the bag holds. -/
theorem exists_linear_shortfall (respects : S.ConsumesNoFacts fact) {M : Multiset R}
    {site₁ site₂ : S.Site} {i : S.Instance site₁} {j : S.Instance site₂}
    (enabledI : S.Enables M i) (enabledJ : S.Enables M j) (conflict : ¬ S.Concurrent M i j) :
    ∃ r, ¬ fact r ∧ M.count r < (S.consume i + S.consume j + (S.read i ∪ S.read j)).count r := by
  by_contra none
  push Not at none
  exact conflict (S.concurrent_of_linear_fits respects enabledI enabledJ fun r isLinear =>
    none r isLinear)

end Facts

/-! ## Keep-only systems -/

section KeepOnly

variable {S}

/-- **A keep-only firing only adds.** -/
theorem le_fire_of_keepOnly (keep : S.KeepOnly) (M : Multiset R) {site : S.Site}
    (i : S.Instance site) : M ≤ S.fire M i := by
  rw [fire, keep i, tsub_zero]
  exact Multiset.le_add_right _ _

/-- **Along every keep-only run the bag only grows.** -/
theorem le_of_run_of_keepOnly (keep : S.KeepOnly) {M N : Multiset R}
    (run : Relation.ReflTransGen S.theory.rewrites M N) : M ≤ N := by
  induction run with
  | refl => exact le_rfl
  | tail _ step previous =>
    obtain ⟨site, i, -, rfl⟩ := step
    exact le_trans previous (le_fire_of_keepOnly keep _ i)

/-- **Keep-only enabledness persists along runs.** -/
theorem enables_of_run_of_keepOnly (keep : S.KeepOnly) {M N : Multiset R}
    (run : Relation.ReflTransGen S.theory.rewrites M N) {site : S.Site} {i : S.Instance site}
    (enabled : S.Enables M i) : S.Enables N i :=
  le_trans enabled (le_of_run_of_keepOnly keep run)

/-- **A keep-only system has no conflicts**: any two instances enabled at one bag are concurrent. -/
theorem concurrent_of_keepOnly (keep : S.KeepOnly) {M : Multiset R} {site₁ site₂ : S.Site}
    {i : S.Instance site₁} {j : S.Instance site₂} (enabledI : S.Enables M i)
    (enabledJ : S.Enables M j) : S.Concurrent M i j := by
  have respects : S.ConsumesNoFacts (fun _ => True) := keep.consumesNoFacts _
  exact S.concurrent_of_linear_fits respects enabledI enabledJ fun _ notFact =>
    absurd trivial notFact

theorem keepOnly_conflictFree (keep : S.KeepOnly) (catalogue : List S.Entry) :
    S.ConflictFree catalogue :=
  fun _ _ _ _ _ _ enabledFirst enabledSecond => concurrent_of_keepOnly keep enabledFirst enabledSecond

/-- **Keep-only firing is confluent**, whatever the catalogue. -/
theorem keepOnly_confluent (keep : S.KeepOnly) (catalogue : List S.Entry) {M N₁ N₂ : Multiset R}
    (reach₁ : Relation.ReflTransGen (S.CatalogueStep catalogue) M N₁)
    (reach₂ : Relation.ReflTransGen (S.CatalogueStep catalogue) M N₂) :
    Relation.Join (Relation.ReflTransGen (S.CatalogueStep catalogue)) N₁ N₂ :=
  S.confluent_of_conflictFree catalogue (keepOnly_conflictFree keep catalogue) reach₁ reach₂

/-- **Over bags, a productive keep-only instance never lets a run rest.** If a keep-only instance that
produces something is enabled at `M`, then every state reached from `M` enables it, and firing it there
gives a strictly larger bag. -/
theorem keepOnly_never_quiescent (keep : S.KeepOnly) {M : Multiset R} {site : S.Site}
    {i : S.Instance site} (enabled : S.Enables M i) (productive : S.produce i ≠ 0) {N : Multiset R}
    (run : Relation.ReflTransGen S.theory.rewrites M N) :
    S.Enables N i ∧ N < S.fire N i := by
  refine ⟨enables_of_run_of_keepOnly keep run enabled, ?_⟩
  rw [fire, keep i, tsub_zero]
  exact lt_add_of_pos_right _ (lt_of_le_of_ne (Multiset.zero_le _) (Ne.symm productive))

end KeepOnly

/-! ## What keep cannot do -/

section Faithfulness

variable {S}

/-- **No keep-only target is faithful to a step that loses an observable.** Suppose a source step from
`P` to `P'` loses an observable that `P` shows. Then no encoding into a keep-only system is both
operationally complete (each source step is matched by a run of the target, of any length) and reflects
the observable through a test of bags that is closed upwards. -/
theorem keepOnly_not_faithful (keep : S.KeepOnly) {Source : Type*} (step : Source → Source → Prop)
    (shows : Source → Prop) {P P' : Source} (fires : step P P') (shown : shows P) (lost : ¬ shows P')
    (encode : Source → Multiset R) (test : Multiset R → Prop)
    (upward : ∀ {M N : Multiset R}, M ≤ N → test M → test N)
    (complete : ∀ {Q Q' : Source}, step Q Q' →
      Relation.ReflTransGen S.theory.rewrites (encode Q) (encode Q'))
    (reflects : ∀ Q, test (encode Q) ↔ shows Q) : False :=
  lost ((reflects P').mp (upward (le_of_run_of_keepOnly keep (complete fires))
    ((reflects P).mpr shown)))

/-- **In a mixed system, an observable a step can remove must be carried by a linear resource.** No
encoding into a system respecting a declaration of facts is operationally complete and reflects a
losable observable through an upward-closed test that reads the fact part only. -/
theorem factObservation_not_faithful {fact : R → Prop} [DecidablePred fact]
    (respects : S.ConsumesNoFacts fact) {Source : Type*} (step : Source → Source → Prop)
    (shows : Source → Prop) {P P' : Source} (fires : step P P') (shown : shows P) (lost : ¬ shows P')
    (encode : Source → Multiset R) (test : Multiset R → Prop)
    (upward : ∀ {M N : Multiset R}, M ≤ N → test M → test N)
    (complete : ∀ {Q Q' : Source}, step Q Q' →
      Relation.ReflTransGen S.theory.rewrites (encode Q) (encode Q'))
    (reflects : ∀ Q, test (factPart fact (encode Q)) ↔ shows Q) : False :=
  lost ((reflects P').mp (upward (S.factPart_le_of_run respects (complete fires))
    ((reflects P).mpr shown)))

end Faithfulness

end System

/-! ## Controls -/

namespace FactLinearControls

/-! ### Crossed joins -/

/-- Resources of the crossed joins: the two shared inputs, two receivers, two half-filled holders and
two results. -/
inductive Crossed where
  | a | b | receiver₁ | receiver₂ | holder₁ | holder₂ | result₁ | result₂
  deriving DecidableEq, Repr

open Crossed

/-- The steps of the joins taken one input at a time: the first join takes `a` and then `b`, the second
takes `b` and then `a`. -/
inductive HalfStep where
  | take₁a | take₁b | take₂b | take₂a
  deriving DecidableEq, Repr

/-- **Atomic joins**: each join takes its receiver, `a` and `b` at once. -/
def atomic : System Crossed where
  Site := Unit
  Instance := fun _ => Bool
  consume := fun (first : Bool) => match first with
    | true => {receiver₁, a, b}
    | false => {receiver₂, a, b}
  read := fun _ => 0
  produce := fun (first : Bool) => match first with
    | true => {result₁}
    | false => {result₂}

/-- **Sequential joins**: each join takes one input, holds it, then takes the other. -/
def sequential : System Crossed where
  Site := Unit
  Instance := fun _ => HalfStep
  consume := fun (step : HalfStep) => match step with
    | .take₁a => {receiver₁, a}
    | .take₁b => {holder₁, b}
    | .take₂b => {receiver₂, b}
    | .take₂a => {holder₂, a}
  read := fun _ => 0
  produce := fun (step : HalfStep) => match step with
    | .take₁a => {holder₁}
    | .take₁b => {result₁}
    | .take₂b => {holder₂}
    | .take₂a => {result₂}

/-- **Sequential joins over facts**: the inputs `a` and `b` are read, not taken. -/
def sequentialReads : System Crossed where
  Site := Unit
  Instance := fun _ => HalfStep
  consume := fun (step : HalfStep) => match step with
    | .take₁a => {receiver₁}
    | .take₁b => {holder₁}
    | .take₂b => {receiver₂}
    | .take₂a => {holder₂}
  read := fun (step : HalfStep) => match step with
    | .take₁a => {a}
    | .take₁b => {b}
    | .take₂b => {b}
    | .take₂a => {a}
  produce := fun (step : HalfStep) => match step with
    | .take₁a => {holder₁}
    | .take₁b => {result₁}
    | .take₂b => {holder₂}
    | .take₂a => {result₂}

def start : Multiset Crossed := {receiver₁, receiver₂, a, b}

/-- A state holds a result. -/
def HasResult (M : Multiset Crossed) : Prop := result₁ ∈ M ∨ result₂ ∈ M

instance (M : Multiset Crossed) : Decidable (HasResult M) := by
  unfold HasResult
  infer_instance

/-- A state is quiescent in a system when no instance is enabled there. -/
def Quiescent {R : Type} (S : System R) (M : Multiset R) : Prop :=
  ∀ {site : S.Site} (i : S.Instance site), ¬ S.Enables M i

theorem atomic_reachable {M : Multiset Crossed}
    (run : Relation.ReflTransGen atomic.theory.rewrites start M) :
    M = start ∨ M = {result₁, receiver₂} ∨ M = {result₂, receiver₁} := by
  induction run with
  | refl => exact Or.inl rfl
  | tail _ step previous =>
    obtain ⟨site, first, enabled, rfl⟩ := step
    cases site
    rcases previous with rfl | rfl | rfl <;> cases first <;> revert enabled <;>
      unfold System.Enables System.fire <;> decide

/-- **Taken atomically, every quiescent state reached holds a result.** -/
theorem atomic_quiescent_has_result {M : Multiset Crossed}
    (run : Relation.ReflTransGen atomic.theory.rewrites start M) (quiet : Quiescent atomic M) :
    HasResult M := by
  rcases atomic_reachable run with rfl | rfl | rfl
  · exact absurd (by unfold System.Enables; decide : atomic.Enables start (site := ()) true)
      (quiet (site := ()) true)
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)

/-- **Taken one input at a time, the crossed joins deadlock**: a run reaches `{h₁, h₂}`, which is
quiescent and holds no result. -/
theorem sequential_deadlock :
    Relation.ReflTransGen sequential.theory.rewrites start ({holder₁, holder₂} : Multiset Crossed) ∧
      Quiescent sequential ({holder₁, holder₂} : Multiset Crossed) ∧
      ¬ HasResult ({holder₁, holder₂} : Multiset Crossed) := by
  refine ⟨?_, ?_, by decide⟩
  · refine Relation.ReflTransGen.tail (b := ({holder₁, receiver₂, b} : Multiset Crossed)) ?_
      ⟨(), HalfStep.take₂b, by unfold System.Enables; decide, by unfold System.fire; decide⟩
    exact Relation.ReflTransGen.single
      ⟨(), HalfStep.take₁a, by unfold System.Enables; decide, by unfold System.fire; decide⟩
  · intro site step
    cases site
    cases step <;> unfold System.Enables <;> decide

/-- The sequential joins over facts respect the declaration that `a` and `b` are facts. -/
theorem sequentialReads_respects : sequentialReads.ConsumesNoFacts (fun r => r = a ∨ r = b) := by
  intro site step
  cases site
  cases step <;> decide

/-- **Over facts, a holder is never stranded.** In the sequential joins that read `a` and `b`, every
state reached from the start that holds `h₁` enables the second step of the first join, and likewise for
`h₂`. -/
theorem factReads_never_stranded {M : Multiset Crossed}
    (run : Relation.ReflTransGen sequentialReads.theory.rewrites start M) :
    (holder₁ ∈ M → sequentialReads.Enables M (site := ()) HalfStep.take₁b) ∧
      (holder₂ ∈ M → sequentialReads.Enables M (site := ()) HalfStep.take₂a) := by
  have stays : ∀ r, (r = a ∨ r = b) → r ∈ M := fun r isFact => by
    have grows := sequentialReads.factCount_le_of_run sequentialReads_respects run isFact
    have present : 0 < start.count r := by rcases isFact with rfl | rfl <;> decide
    exact Multiset.count_pos.mp (lt_of_lt_of_le present grows)
  constructor
  · intro holds
    show ({holder₁} : Multiset Crossed) + {b} ≤ M
    rw [Multiset.le_iff_subset (by decide)]
    intro x member
    simp only [Multiset.singleton_add, Multiset.mem_cons, Multiset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact holds
    · exact stays _ (Or.inr rfl)
  · intro holds
    show ({holder₂} : Multiset Crossed) + {a} ≤ M
    rw [Multiset.le_iff_subset (by decide)]
    intro x member
    simp only [Multiset.singleton_add, Multiset.mem_cons, Multiset.mem_singleton] at member
    rcases member with rfl | rfl
    · exact holds
    · exact stays _ (Or.inl rfl)

/-! ### A peek at a linear resource, and a consumed fact -/

/-- Resources: one token, and the outputs of a peeking reader and of a consumer. -/
inductive Peek where
  | token | peeked | taken
  deriving DecidableEq, Repr

/-- A reader peeks at the token (instance `true`); a consumer takes it (instance `false`). -/
def peekSystem : System Peek where
  Site := Unit
  Instance := fun _ => Bool
  consume := fun (reader : Bool) => match reader with
    | true => 0
    | false => {Peek.token}
  read := fun (reader : Bool) => match reader with
    | true => {Peek.token}
    | false => 0
  produce := fun (reader : Bool) => match reader with
    | true => {Peek.peeked}
    | false => {Peek.taken}

/-- **A peek at a linear resource goes stale**: the reader is enabled at the snapshot `{token}`, the
consumer then takes the token, and the reader is disabled. Its read must be validated at commit. -/
theorem linear_peek_stale :
    peekSystem.Enables {Peek.token} (site := ()) true ∧
      peekSystem.theory.rewrites ({Peek.token} : Multiset Peek) ({Peek.taken} : Multiset Peek) ∧
      ¬ peekSystem.Enables {Peek.taken} (site := ()) true :=
  ⟨by unfold System.Enables; decide,
    ⟨(), false, by unfold System.Enables; decide, by unfold System.fire; decide⟩,
    by unfold System.Enables; decide⟩

/-- **A consumed fact breaks the declaration**: if the token is declared a fact, the consumer violates
the declaration, and a single step lowers the count of the token. -/
theorem consumed_fact_not_monotone :
    ¬ peekSystem.ConsumesNoFacts (fun r => r = Peek.token) ∧
      ({Peek.taken} : Multiset Peek).count Peek.token < ({Peek.token} : Multiset Peek).count Peek.token := by
  refine ⟨fun respects => respects (site := ()) false Peek.token (by decide) rfl, by decide⟩

end FactLinearControls

end Mettapedia.GSLT.Causality.ResourceInteraction
