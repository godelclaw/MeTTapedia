import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.ScopeExtrusion
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.CommutativeMatching
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannelCalculus

/-!
# Quoted names and fresh names: what a name is, and who can build it

In the rho-calculus a name is a quoted process, `@P`, and two names are equal when their processes
are. Rholang adds `new`, which gives names that no process can write down. This module puts both
kinds in one syntax and says, with proofs, what each kind buys.

## Names with a support

A name (`Name A F`) is a fresh atom `nu a` (the result of `new`), a public symbol, or an
expression built from names: a quoted term. Its **support** is the set of fresh atoms it mentions
(`Name.support`).

* **What a process can build is exactly what its atoms support** (`builds_iff_support`). A process
  that holds the fresh atoms `K` (its rights) can write down a name exactly when the name's support
  lies inside `K`.
* **A public quoted name is built by every context** (`Public.builds`). Choosing a name that differs
  from every name a given process uses is always possible (`exists_public_fresh`), but the chosen
  name is fresh only relative to that process: an unknown context with no rights at all builds it
  too (`relative_fresh_forgeable`). A fresh atom is built only by holders (`builds_nu_iff`).
* **A quoted term that mentions fresh atoms is as private as all of them together**
  (`builds_node_iff`): its holders are the holders of every atom in it, a compound capability.

## Rights by support, and the extrusion closure

`heldBy K` is the rights predicate of `ChannelAddressing` read through supports: a name is held when
its support lies inside `K`. Every public name is held by every process (`heldBy_public`), so every
message on a public name can be taken by a context with no rights (`public_occurrence_interceptable`),
while a message on a name whose fresh atoms a context lacks is out of reach of all its commits
(`unheld_occurrence_unreachable`).
`SupportRun` is the dynamic run of `ScopeExtrusion` with names that have supports: what a process
learns is the support of the names carried by what it takes, keeps or sees in a predicate query
(`learnedAtoms`), and what it makes carries names built from its atoms (`BuildsFromSupport`).

* **The closure bounds what can be learned** (`SupportRun.rights_subset_closed`): a set of atoms that
  is closed in the store (`ClosedAtoms`) and contains a process's rights contains every atom the
  process ever holds. So the names the process can ever address are those supported by the closed
  set: every public name, and no fresh atom outside it.
* **Non-interference relative to a closed set of atoms** (`SupportRun.noninterference_closed`).
* **A fresh atom carried on a public name lies in every closed set** (`public_carriage_extrudes`):
  sending a fresh name on a quoted public channel extrudes it to every context.
* **Opaque names are the special case** (`supportRun_nu_iff`): when every location and every carried
  name is a fresh atom, `SupportRun` is exactly `ScopeExtrusion.DynamicRun` with no constants.

## Equality of names, and of stored code

Name equality is the term equality of the declared theory `E` (decision §10); with no declared law
it is syntactic. A data position, where a process or a rule is stored and a reader can match it, is
a delayed quote:

* **Readers collapse every respected equivalence to `E`** (`collapse_to_E`): when every value has a
  ground pattern, a relation on stored values that no reader can tell apart is contained in `E`. So
  two programs equal in behaviour but different as code are different as data, and an equivalence
  of processes (bisimilarity over borrowed contexts, for instance) is a congruence for parallel
  contexts, never for data contexts.
* With a commuting `par` declared, `par(a, b)` and `par(b, a)` are one name (`NameControls.par_comm_one_name`);
  `par(a, nil)` and `a` are two (`NameControls.par_unit_two_names`), as the unit law is not declared. Rho's
  name equality modulo structural congruence is the case where the structural laws are declared in
  `E`.
* In the quoted-channel calculus, where channels are compared syntactically, the structurally
  congruent pair `nil ∣ nil`, `nil` is equal for guarded contexts and separated once payload
  positions are admissible (`rho_structural_congruence_unsound`, from `QuotedChannelCalculus`).
  Rewriting stored processes modulo structural congruence is observable there.

## Controls

* **Forging a quoted name intercepts a message** (`NameControls.forged_name_intercepts`): a process
  sends a secret on a public quoted name chosen apart from its own names; a context with no rights
  builds the same name and takes the secret.
* **A fresh name is not forged** (`NameControls.fresh_name_not_intercepted`): the same secret on a fresh
  atom is outside every commit scoped to empty rights, and the context runs alike with and without
  it (the garbage law of `ChannelAddressing`).
* **Extrusion on a public channel** (`NameControls.public_send_extrudes`): a process with no rights takes
  a message on a public name carrying a fresh atom and then sends on that atom.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits

universe uA uF uO uR

/-! ## Names -/

/-- Names: a fresh atom, a public symbol, or a quoted expression built from names. -/
inductive Name (A : Type uA) (F : Type uF) where
  | nu (a : A)
  | sym (f : F)
  | node (f : F) (l r : Name A F)
  deriving DecidableEq

namespace Name

variable {A : Type uA} {F : Type uF}

/-- The fresh atoms a name mentions. -/
def support [DecidableEq A] : Name A F → Finset A
  | nu a => {a}
  | sym _ => ∅
  | node _ l r => l.support ∪ r.support

/-- The size of a name. -/
def size : Name A F → ℕ
  | nu _ => 1
  | sym _ => 1
  | node _ l r => l.size + r.size + 1

end Name

variable {A : Type uA} [DecidableEq A] {F : Type uF}

open Name

/-- The names a process holding the fresh atoms `K` can write down. -/
inductive Builds (K : Finset A) : Name A F → Prop
  | nu {a : A} : a ∈ K → Builds K (.nu a)
  | sym (f : F) : Builds K (.sym f)
  | node (f : F) {l r : Name A F} : Builds K l → Builds K r → Builds K (.node f l r)

/-- **What a process can build is what its atoms support.** -/
theorem builds_iff_support {K : Finset A} : ∀ {n : Name A F}, Builds K n ↔ n.support ⊆ K
  | .nu a => by
      constructor
      · rintro ⟨member⟩
        simpa [support] using member
      · intro sub
        exact .nu (by simpa [support] using sub)
  | .sym f => by
      constructor
      · intro _
        simp [support]
      · intro _
        exact .sym f
  | .node f l r => by
      constructor
      · rintro (_ | _ | ⟨_, left, right⟩)
        exact Finset.union_subset (builds_iff_support.mp left) (builds_iff_support.mp right)
      · intro sub
        exact .node f (builds_iff_support.mpr (Finset.union_subset_left sub))
          (builds_iff_support.mpr (Finset.union_subset_right sub))

theorem builds_nu_iff {K : Finset A} {a : A} : Builds K (.nu a : Name A F) ↔ a ∈ K := by
  rw [builds_iff_support]
  simp [support]

/-- A quoted term with fresh atoms in it is built exactly by holders of all of them. -/
theorem builds_node_iff {K : Finset A} {f : F} {l r : Name A F} :
    Builds K (.node f l r) ↔ Builds K l ∧ Builds K r := by
  rw [builds_iff_support, builds_iff_support, builds_iff_support]
  simp [support, Finset.union_subset_iff]

/-- A name is **public** when it mentions no fresh atom. -/
def Public (n : Name A F) : Prop := n.support = ∅

/-- **A public name is built by every context.** -/
theorem Public.builds {n : Name A F} (public_ : Public n) (K : Finset A) : Builds K n := by
  rw [builds_iff_support, public_]
  exact Finset.empty_subset K

/-- A tower of quotations of one symbol. -/
def tower (f : F) : ℕ → Name A F
  | 0 => .sym f
  | k + 1 => .node f (tower f k) (.sym f)

theorem tower_public (f : F) : ∀ k, Public (tower (A := A) f k)
  | 0 => rfl
  | k + 1 => by
      have := tower_public f k
      unfold Public at this ⊢
      simp [tower, support, this]

omit [DecidableEq A] in
theorem size_tower (f : F) : ∀ k, (tower (A := A) f k).size = 2 * k + 1
  | 0 => rfl
  | k + 1 => by
      simp only [tower, size, size_tower f k]
      omega

/-- **A name apart from any given finite set of names exists, and is public.** This is how a
process without `new` makes a name that differs from all of its own. -/
theorem exists_public_fresh (X : Finset (Name A F)) (f : F) : ∃ n, Public n ∧ n ∉ X := by
  refine ⟨tower f (X.sup size), tower_public f _, fun member => ?_⟩
  have le := Finset.le_sup (f := size) member
  rw [size_tower] at le
  omega

/-- **Freshness relative to a process is not freshness.** The name a process builds to differ from
all its names is built by every context, even one holding no fresh atom. -/
theorem relative_fresh_forgeable (X : Finset (Name A F)) (f : F) :
    ∃ n, n ∉ X ∧ ∀ K : Finset A, Builds K n := by
  obtain ⟨n, public_, notIn⟩ := exists_public_fresh X f
  exact ⟨n, notIn, public_.builds⟩

/-- **A fresh atom is built only by its holders.** -/
theorem nu_not_builds {K : Finset A} {a : A} (notHeld : a ∉ K) : ¬ Builds K (.nu a : Name A F) :=
  fun built => notHeld (builds_nu_iff.mp built)

/-! ## Rights by support -/

/-- Rights by support: a name is held when its fresh atoms are. -/
def heldBy (K : Finset A) (n : Name A F) : Bool := decide (n.support ⊆ K)

theorem heldBy_iff {K : Finset A} {n : Name A F} : heldBy K n = true ↔ Builds K n := by
  simp [heldBy, builds_iff_support]

/-- Every process holds every public name. -/
theorem heldBy_public {n : Name A F} (public_ : Public n) (K : Finset A) : heldBy K n = true :=
  heldBy_iff.mpr (public_.builds K)

/-- On fresh atoms, rights by support are the rights of `ScopeExtrusion`. -/
theorem heldBy_nu (K : Finset A) : (fun a => heldBy K (.nu a : Name A F)) = holds K := by
  funext a
  simp [heldBy, holds, support]

/-! ## Support-scoped runs and the extrusion closure -/

section Runs

variable {O : Type uO} [DecidableEq O] {R : Type uR}
variable (label : O → R) (loc : R → Name A F) (carried : R → Finset (Name A F))

/-- The fresh atoms a commit learns: the supports of the names carried by what it takes, keeps or
sees in a predicate query. -/
def learnedAtoms (c : Commit O R) : Finset A :=
  c.learnedFrom.biUnion fun o => (carried (label o)).biUnion Name.support

/-- A commit builds what its made occurrences carry from the atoms it holds and learns. -/
def BuildsFromSupport (rights : Finset A) (c : Commit O R) : Prop :=
  ∀ o ∈ c.made, ∀ n ∈ carried (label o), n.support ⊆ rights ∪ learnedAtoms label carried c

/-- One process's run, with rights (fresh atoms) that grow by what it learns. -/
inductive SupportRun : Finset O → Finset A → List (Commit O R) → Finset O → Finset A → Prop
  | nil (store : Finset O) (rights : Finset A) : SupportRun store rights [] store rights
  | cons {store : Finset O} {rights : Finset A} {c : Commit O R} {rest : List (Commit O R)}
      {store' : Finset O} {rights' : Finset A}
      (enabled : Enabled label store c) (inScope : Scoped label loc (heldBy rights) c)
      (builds : BuildsFromSupport label carried rights c)
      (after : SupportRun (fire store c) (rights ∪ learnedAtoms label carried c) rest store' rights') :
      SupportRun store rights (c :: rest) store' rights'

/-- A set of atoms is **closed** in a store: every occurrence at a name it supports carries only
names it supports. -/
def ClosedAtoms (C : Finset A) (store : Finset O) : Prop :=
  ∀ o ∈ store, (loc (label o)).support ⊆ C → ∀ n ∈ carried (label o), n.support ⊆ C

variable {label loc carried}

omit [DecidableEq O] in
theorem scoped_support {rights : Finset A} {c : Commit O R}
    (inScope : Scoped label loc (heldBy rights) c) :
    (∀ o ∈ c.taken, (loc (label o)).support ⊆ rights) ∧
      (∀ o ∈ c.kept, (loc (label o)).support ⊆ rights) ∧
      (∀ o ∈ c.made, (loc (label o)).support ⊆ rights) ∧
      (∀ read ∈ c.queries, ∀ r, read.region r = true → (loc r).support ⊆ rights) := by
  refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun read h r inRegion => ?_⟩
  · simpa [heldBy] using inScope.taken o h
  · simpa [heldBy] using inScope.kept o h
  · simpa [heldBy] using inScope.made o h
  · simpa [heldBy] using inScope.queries read h r inRegion

namespace SupportRun

/-- **Rights only grow.** -/
theorem rights_mono {store store' : Finset O} {rights rights' : Finset A} {run : List (Commit O R)}
    (dynamic : SupportRun label loc carried store rights run store' rights') : rights ⊆ rights' := by
  induction dynamic with
  | nil => exact le_rfl
  | cons _ _ _ _ ih => exact Finset.subset_union_left.trans ih

/-- What a scoped commit learns lies in a closed set containing its rights. -/
theorem learned_subset_closed {C : Finset A} {store : Finset O} {rights : Finset A}
    {c : Commit O R} (closed : ClosedAtoms label loc carried C store) (inside : rights ⊆ C)
    (enabled : Enabled label store c) (inScope : Scoped label loc (heldBy rights) c) :
    learnedAtoms label carried c ⊆ C := by
  obtain ⟨takenIn, keptIn, -, readsIn⟩ := scoped_support inScope
  intro a member
  obtain ⟨o, used, inCarried⟩ := Finset.mem_biUnion.mp member
  obtain ⟨n, carriedN, inSupport⟩ := Finset.mem_biUnion.mp inCarried
  have heldAndPresent : (loc (label o)).support ⊆ rights ∧ o ∈ store := by
    rcases Finset.mem_union.mp used with used | seen
    · rcases Finset.mem_union.mp used with taken | kept
      · exact ⟨takenIn o taken, enabled.taken_subset taken⟩
      · exact ⟨keptIn o kept, enabled.kept_subset kept⟩
    · obtain ⟨read, inQueries, inSeen⟩ := mem_seenOf.mp seen
      have holdsRead := enabled.queries_hold read inQueries
      unfold PredicateQuery.Holds at holdsRead
      rw [← holdsRead] at inSeen
      obtain ⟨inStore, inRegion⟩ := mem_regionOf.mp inSeen
      exact ⟨readsIn read inQueries _ inRegion, inStore⟩
  exact closed o heldAndPresent.2 (heldAndPresent.1.trans inside) n carriedN inSupport

/-- A step of a process whose rights lie in a closed set keeps the set closed. -/
theorem closed_fire {C : Finset A} {store : Finset O} {rights : Finset A} {c : Commit O R}
    (closed : ClosedAtoms label loc carried C store) (inside : rights ⊆ C)
    (enabled : Enabled label store c) (inScope : Scoped label loc (heldBy rights) c)
    (builds : BuildsFromSupport label carried rights c) :
    ClosedAtoms label loc carried C (fire store c) := by
  intro o member atC n carriedN
  rcases mem_fire.mp member with ⟨inStore, _⟩ | made
  · exact closed o inStore atC n carriedN
  · exact (builds o made n carriedN).trans
      (Finset.union_subset inside (learned_subset_closed closed inside enabled inScope))

/-- **A closed set containing the rights bounds every atom the process can learn.** -/
theorem rights_subset_closed {C : Finset A} {store store' : Finset O} {rights rights' : Finset A}
    {run : List (Commit O R)} (dynamic : SupportRun label loc carried store rights run store' rights')
    (closed : ClosedAtoms label loc carried C store) (inside : rights ⊆ C) :
    rights' ⊆ C ∧ ClosedAtoms label loc carried C store' := by
  induction dynamic with
  | nil => exact ⟨inside, closed⟩
  | cons enabled inScope builds _ ih =>
      exact ih (closed_fire closed inside enabled inScope builds)
        (Finset.union_subset inside (learned_subset_closed closed inside enabled inScope))

/-- **The names a process can ever address are the names its closed set supports**: every public
name, and no name mentioning a fresh atom outside the set. -/
theorem never_builds_outside {C : Finset A} {store store' : Finset O} {rights rights' : Finset A}
    {run : List (Commit O R)} (dynamic : SupportRun label loc carried store rights run store' rights')
    (closed : ClosedAtoms label loc carried C store) (inside : rights ⊆ C) {a : A} (outside : a ∉ C) :
    ¬ Builds rights' (.nu a : Name A F) :=
  nu_not_builds fun held => outside ((rights_subset_closed dynamic closed inside).1 held)

omit [DecidableEq O] in
theorem scoped_mono {small large : Finset A} (sub : small ⊆ large) {c : Commit O R}
    (inScope : Scoped label loc (heldBy small) c) : Scoped label loc (heldBy large) c := by
  obtain ⟨takenIn, keptIn, madeIn, readsIn⟩ := scoped_support inScope
  refine ⟨fun o h => ?_, fun o h => ?_, fun o h => ?_, fun read h r inRegion => ?_⟩
  · simpa [heldBy] using (takenIn o h).trans sub
  · simpa [heldBy] using (keptIn o h).trans sub
  · simpa [heldBy] using (madeIn o h).trans sub
  · simpa [heldBy] using (readsIn read h r inRegion).trans sub

/-- **Non-interference relative to a closed set of atoms.** Two stores that agree on the names the
set supports, and in which the set is closed, run a process whose rights lie in the set alike. -/
theorem noninterference_closed {C : Finset A} :
    ∀ {first second : Finset O} {rights : Finset A} {run : List (Commit O R)},
      ClosedAtoms label loc carried C first → ClosedAtoms label loc carried C second → rights ⊆ C →
      restrict label loc (heldBy C) first = restrict label loc (heldBy C) second →
      ∀ {first' : Finset O} {rights' : Finset A},
        SupportRun label loc carried first rights run first' rights' →
        ∃ second', SupportRun label loc carried second rights run second' rights' ∧
          restrict label loc (heldBy C) first' = restrict label loc (heldBy C) second' := by
  intro first second rights run closedFirst closedSecond inside agree first' rights' dynamic
  induction dynamic generalizing second with
  | nil => exact ⟨second, .nil _ _, agree⟩
  | @cons store rights c rest store' rights' enabled inScope builds after ih =>
      have scopedC : Scoped label loc (heldBy C) c := scoped_mono inside inScope
      have enabledSecond : Enabled label second c := by
        rw [enabled_iff_restrict scopedC, ← agree, ← enabled_iff_restrict scopedC]
        exact enabled
      have learnedFirst : learnedAtoms label carried c ⊆ C :=
        learned_subset_closed closedFirst inside enabled inScope
      have agreeNext : restrict label loc (heldBy C) (fire store c) =
          restrict label loc (heldBy C) (fire second c) := by
        rw [restrict_fire scopedC, restrict_fire scopedC, agree]
      obtain ⟨second', run', agree'⟩ := ih
        (closed_fire closedFirst inside enabled inScope builds)
        (closed_fire closedSecond inside enabledSecond inScope builds)
        (Finset.union_subset inside learnedFirst) agreeNext
      exact ⟨second', .cons enabledSecond inScope builds run', agree'⟩

end SupportRun

omit [DecidableEq O] in
/-- **A fresh atom carried on a public name lies in every closed set.** Sending a fresh name on a
quoted public channel extrudes it to every context. -/
theorem public_carriage_extrudes {C : Finset A} {store : Finset O}
    (closed : ClosedAtoms label loc carried C store) {o : O} (member : o ∈ store)
    (public_ : Public (loc (label o))) {a : A} (carriedA : (.nu a : Name A F) ∈ carried (label o)) :
    a ∈ C := by
  have atC : (loc (label o)).support ⊆ C := by
    rw [public_]
    exact Finset.empty_subset C
  exact closed o member atC _ carriedA (by simp [support])

/-! ### Interception -/

omit [DecidableEq O] in
/-- **Every message on a public name can be intercepted by a context with no rights**: taking it is
enabled and scoped to every rights set, empty ones included. -/
theorem public_occurrence_interceptable {S : Finset O} {o : O} (member : o ∈ S)
    (public_ : Public (loc (label o))) (K : Finset A) :
    Enabled label S (Commit.takeOne o : Commit O R) ∧ Scoped label loc (heldBy K) (Commit.takeOne o : Commit O R) := by
  refine ⟨⟨by simpa using member, by simp, by simp, by simp,
    by simp⟩, ⟨fun o' h => ?_, by simp, by simp, by simp⟩⟩
  simp only [Commit.takeOne_taken, Finset.mem_singleton] at h
  subst h
  exact heldBy_public public_ K

omit [DecidableEq O] in
/-- **A message on a name whose fresh atoms a context does not hold is out of its reach**: no commit
scoped to its rights takes it, keeps it, or sees it in a predicate query. -/
theorem unheld_occurrence_unreachable {K : Finset A} {o : O}
    (unheld : ¬ (loc (label o)).support ⊆ K) {c : Commit O R}
    (inScope : Scoped label loc (heldBy K) c) :
    o ∉ c.taken ∧ o ∉ c.kept ∧ ∀ read ∈ c.queries, read.region (label o) = false := by
  obtain ⟨takenIn, keptIn, -, readsIn⟩ := scoped_support inScope
  refine ⟨fun taken => unheld (takenIn o taken), fun kept => unheld (keptIn o kept),
    fun read member => ?_⟩
  by_contra inRegion
  exact unheld (readsIn read member (label o) (by simpa using inRegion))

/-! ### Opaque names are the special case -/

section Opaque

variable [DecidableEq F] {kloc : R → A} {knames : R → Finset A}

theorem learnedAtoms_nu (c : Commit O R) :
    learnedAtoms label (fun r => (knames r).image (Name.nu (F := F))) c = learned label knames c := by
  unfold learnedAtoms learned
  congr 1
  funext o
  ext a
  simp [support]

omit [DecidableEq O] [DecidableEq F] in
theorem scoped_nu_iff {K : Finset A} {c : Commit O R} :
    Scoped label (fun r => (Name.nu (kloc r) : Name A F)) (heldBy K) c ↔
      Scoped label kloc (holds K) c := by
  have same : ∀ a : A, heldBy K (Name.nu a : Name A F) = holds K a := fun a =>
    congrFun (heldBy_nu (F := F) K) a
  constructor
  · intro inScope
    exact ⟨fun o h => by rw [← same]; exact inScope.taken o h,
      fun o h => by rw [← same]; exact inScope.kept o h,
      fun o h => by rw [← same]; exact inScope.made o h,
      fun read h r inRegion => by rw [← same]; exact inScope.queries read h r inRegion⟩
  · intro inScope
    exact ⟨fun o h => by rw [same]; exact inScope.taken o h,
      fun o h => by rw [same]; exact inScope.kept o h,
      fun o h => by rw [same]; exact inScope.made o h,
      fun read h r inRegion => by rw [same]; exact inScope.queries read h r inRegion⟩

theorem buildsFromSupport_nu_iff {K : Finset A} {c : Commit O R} :
    BuildsFromSupport label (fun r => (knames r).image (Name.nu (F := F))) K c ↔
      BuildsFromHeld label knames ∅ K c := by
  unfold BuildsFromSupport BuildsFromHeld
  rw [learnedAtoms_nu]
  constructor
  · intro builds o made a member
    have := builds o made (Name.nu a) (Finset.mem_image_of_mem _ member)
    simpa [support] using this
  · intro builds o made n member
    obtain ⟨a, inNames, rfl⟩ := Finset.mem_image.mp member
    have := builds o made inNames
    simpa [support] using this

/-- **Opaque names are the special case.** When every location and every carried name is a fresh
atom, a support-scoped run is exactly a run of `ScopeExtrusion` with no constants. -/
theorem supportRun_nu_iff {store store' : Finset O} {rights rights' : Finset A}
    {run : List (Commit O R)} :
    SupportRun label (fun r => (Name.nu (kloc r) : Name A F))
        (fun r => (knames r).image (Name.nu (F := F))) store rights run store' rights' ↔
      DynamicRun label kloc knames ∅ store rights run store' rights' := by
  constructor
  · intro dynamic
    induction dynamic with
    | nil => exact .nil _ _
    | cons enabled inScope builds _ ih =>
        refine .cons enabled (scoped_nu_iff.mp inScope) (buildsFromSupport_nu_iff.mp builds) ?_
        rw [← learnedAtoms_nu (F := F) (knames := knames)]
        exact ih
  · intro dynamic
    induction dynamic with
    | nil => exact .nil _ _
    | cons enabled inScope builds _ ih =>
        refine .cons enabled (scoped_nu_iff.mpr inScope) (buildsFromSupport_nu_iff.mpr builds) ?_
        rw [learnedAtoms_nu (F := F) (knames := knames)]
        exact ih

end Opaque

end Runs

/-! ## Stored code collapses to the declared theory -/

section Collapse

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources

universe uV uT uP

variable {V : Type uV} {T : Type uT} {P : Type uP}

/-- A term layer **has ground patterns** when every value is written by a pattern that solves
exactly the values `E`-equal to it. -/
def HasGroundPatterns (L : TermLayer V T P) : Prop :=
  ∀ t : T, ∃ p : P, ∀ σ u, L.Solves σ p u ↔ L.E t u

/-- **Readers collapse every respected relation to `E`.** If no reader (no pattern, under no
substitution) tells `t` from `u`, then `t` and `u` are `E`-equal. -/
theorem collapse_to_E {L : TermLayer V T P} (ground : HasGroundPatterns L) {t u : T}
    (indistinguishable : ∀ (p : P) (σ : Subst V T), L.Solves σ p t ↔ L.Solves σ p u) : L.E t u := by
  obtain ⟨p, solves⟩ := ground t
  exact (solves (fun _ => none) u).mp
    ((indistinguishable p _).mp ((solves _ t).mpr (L.equivalence.refl t)))

/-- Conversely, `E`-equal values are told apart by no reader. -/
theorem indistinguishable_of_E {L : TermLayer V T P} {t u : T} (same : L.E t u) (p : P)
    (σ : Subst V T) : L.Solves σ p t ↔ L.Solves σ p u :=
  ⟨fun solves => solves.of_equiv same, fun solves => solves.of_equiv (L.equivalence.symm same)⟩

/-- **The only equivalence of stored code that every reader respects is `E`.** -/
theorem readers_respect_iff {L : TermLayer V T P} (ground : HasGroundPatterns L) (t u : T) :
    (∀ (p : P) (σ : Subst V T), L.Solves σ p t ↔ L.Solves σ p u) ↔ L.E t u :=
  ⟨collapse_to_E ground, indistinguishable_of_E⟩

end Collapse

section Commutative

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative

universe uS uX

variable {S : Type uS} [DecidableEq S] {X : Type uX} [DecidableEq X]

omit [DecidableEq S] [DecidableEq X] in
/-- The ground pattern of a value. -/
def groundPat : Tm S → Pat X S
  | .leaf a => .leaf a
  | .node f l r => .node f (groundPat l) (groundPat r)

omit [DecidableEq S] [DecidableEq X] in
theorem groundPat_inst (σ : Subst X (Tm S)) : ∀ t : Tm S, (groundPat t).inst σ = some t
  | .leaf a => rfl
  | .node f l r => by
      simp only [groundPat, Pat.inst, groundPat_inst σ l, groundPat_inst σ r]

/-- Every declaration of commuting symbols has ground patterns. -/
theorem hasGroundPatterns (comm : S → Bool) : HasGroundPatterns (termLayer (V := X) comm) := by
  intro t
  refine ⟨groundPat t, fun σ u => ?_⟩
  constructor
  · rintro ⟨w, inst, rel⟩
    have : w = t := by
      have h : (groundPat t).inst σ = some w := inst
      rw [groundPat_inst] at h
      exact (Option.some.inj h).symm
    subst this
    exact rel
  · intro rel
    exact ⟨t, groundPat_inst σ t, rel⟩

end Commutative

/-! ## The quoted-channel calculus: structural congruence is observable through payloads -/

section Rho

open Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannel (guarded quoteFree barbs
  guarded_equal_quoteFree_distinct relEquiv_quoteFree_iff_eq)

/-- Processes of the quoted-channel calculus. -/
abbrev QProc := Mettapedia.Languages.ProcessCalculi.RhoCalculus.QuotedChannel.Proc

/-- Structural congruence of the quoted-channel calculus: parallel composition is associative,
commutative, and has `nil` as unit, as a congruence. -/
inductive StructCong : QProc → QProc → Prop
  | refl (p : QProc) : StructCong p p
  | symm {p q : QProc} : StructCong p q → StructCong q p
  | trans {p q r : QProc} : StructCong p q → StructCong q r → StructCong p r
  | parNil (p : QProc) : StructCong (.par p .nil) p
  | parComm (p q : QProc) : StructCong (.par p q) (.par q p)
  | parAssoc (p q r : QProc) : StructCong (.par (.par p q) r) (.par p (.par q r))
  | parCongr {p p' q q' : QProc} : StructCong p p' → StructCong q q' → StructCong (.par p q) (.par p' q')

/-- **Structural congruence is not sound once payload positions are admissible.** The pair
`nil ∣ nil`, `nil` is structurally congruent and equal for guarded contexts, and an echo followed by
a listener separates it. Channels compared syntactically make rewriting stored processes modulo
structural congruence observable. -/
theorem rho_structural_congruence_unsound :
    StructCong (.par .nil .nil) .nil ∧ guarded.RelEquiv barbs (.par .nil .nil) .nil ∧
      ¬ quoteFree.RelEquiv barbs (.par .nil .nil) .nil :=
  ⟨.parNil .nil, guarded_equal_quoteFree_distinct.2⟩

/-- In that calculus, the payload-closed equivalence meets structural congruence in identity. -/
theorem rho_payload_closed_is_identity {p q : QProc} (related : quoteFree.RelEquiv barbs p q) :
    p = q :=
  (relEquiv_quoteFree_iff_eq p q).mp related

end Rho

/-! ## Controls -/

namespace NameControls

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Sources.Commutative

/-- Symbols of the controls. -/
inductive Sym where
  | ch | secret | ack | other
  deriving DecidableEq, Repr

/-- The public name a process builds to be apart from its own names (`@(ch ch)`). -/
def quoted : Name ℕ Sym := .node .ch (.sym .ch) (.sym .ch)

theorem quoted_public : Public quoted := rfl

/-- Payloads: a secret, or a name carried in a message. -/
inductive Payload where
  | secret
  | carry (n : Name ℕ Sym)
  deriving DecidableEq

/-- Occurrence `0`: the secret on the quoted public name. Occurrence `1`: the secret on the fresh
atom `0`. Occurrence `2`: a message on the quoted name carrying the fresh atom `0`. Occurrence `3`:
a send on the fresh atom `0`. Everything else is an acknowledgement on the symbol `other`. -/
def lbl : ℕ → Name ℕ Sym × Payload
  | 0 => (quoted, .secret)
  | 1 => (.nu 0, .secret)
  | 2 => (quoted, .carry (.nu 0))
  | 3 => (.nu 0, .secret)
  | _ => (.sym .other, .secret)

/-- The names a label carries. -/
def carriedOf : Name ℕ Sym × Payload → Finset (Name ℕ Sym)
  | (_, .carry n) => {n}
  | (_, .secret) => ∅

/-- The context takes the occurrence `o`. -/
def takeOcc (o : ℕ) : Commit ℕ (Name ℕ Sym × Payload) := ⟨{o}, ∅, ∅, []⟩

/-- **Forging a quoted name intercepts a message.** The sender's name differs from every name in
its own set `{ch}`, yet a context with no rights takes the secret sent on it: the take is enabled
and scoped to empty rights. -/
theorem forged_name_intercepts :
    quoted ∉ ({.sym .ch} : Finset (Name ℕ Sym)) ∧ Builds (∅ : Finset ℕ) quoted ∧
      Enabled lbl {0} (takeOcc 0) ∧ Scoped lbl Prod.fst (heldBy ∅) (takeOcc 0) := by
  refine ⟨by decide, quoted_public.builds ∅, ?_, ?_⟩
  · exact ⟨by simp [takeOcc], by simp [takeOcc], by simp [takeOcc], by simp [takeOcc],
      by simp [takeOcc]⟩
  · exact ⟨fun o h => by simp [takeOcc] at h; subst h; decide, by simp [takeOcc],
      by simp [takeOcc], by simp [takeOcc]⟩

/-- **A fresh name is not forged.** No commit scoped to empty rights takes the secret on the fresh
atom `0`, and a context with empty rights runs alike with and without that secret. -/
theorem fresh_name_not_intercepted :
    ¬ Scoped lbl Prod.fst (heldBy ∅) (takeOcc 1) ∧
      ∀ (run : List (Commit ℕ (Name ℕ Sym × Payload)))
        (_ : ∀ e ∈ run, Scoped lbl Prod.fst (heldBy ∅) e) (store : Finset ℕ),
        (Executable lbl store run ↔ Executable lbl (store ∪ {1}) run) ∧
          restrict lbl Prod.fst (heldBy ∅) (fireList store run) =
            restrict lbl Prod.fst (heldBy ∅) (fireList (store ∪ {1}) run) := by
  refine ⟨fun inScope => ?_, fun run inScope store => ?_⟩
  · have := inScope.taken 1 (by simp [takeOcc])
    revert this
    decide
  · exact garbage_unobservable inScope (by intro o member; simp at member; subst member; decide)

/-- **Extrusion on a public channel.** A process with no rights takes the message on the quoted
public name, learns the fresh atom it carries, and sends on that atom. -/
theorem public_send_extrudes :
    SupportRun lbl Prod.fst carriedOf {2} ∅ [takeOcc 2, ⟨∅, ∅, {3}, []⟩] {3} {0} := by
  refine .cons ⟨by simp [takeOcc], by simp [takeOcc], by simp [takeOcc], by simp [takeOcc],
      by simp [takeOcc]⟩
    ⟨fun o h => by simp [takeOcc] at h; subst h; decide, by simp [takeOcc], by simp [takeOcc],
      by simp [takeOcc]⟩
    (by intro o h; simp [takeOcc] at h) ?_
  refine .cons ⟨by simp, by simp, by simp, by decide, by simp⟩
    ⟨by simp, by simp, fun o h => by simp at h; subst h; decide, by simp⟩
    (by intro o h; simp at h; subst h; simp [lbl, carriedOf]) ?_
  convert SupportRun.nil (label := lbl) (loc := Prod.fst) (carried := carriedOf)
    ({3} : Finset ℕ) ({0} : Finset ℕ) using 2 <;> decide

/-- The control's message extrudes atom `0` into every closed set of the store `{2}`. -/
theorem public_send_in_every_closed (C : Finset ℕ)
    (closed : ClosedAtoms lbl Prod.fst carriedOf C ({2} : Finset ℕ)) : 0 ∈ C :=
  public_carriage_extrudes (o := 2) closed (by simp) (show Public quoted from rfl)
    (by simp [lbl, carriedOf])

/-- Symbols of the code controls: a `par` that commutes, and two atoms. -/
inductive Code where
  | par | a | b | nil
  deriving DecidableEq, Repr

/-- `par` is declared commutative. -/
def parComm : Code → Bool
  | .par => true
  | _ => false

/-- The code layer modulo commutativity of `par`. -/
abbrev Lpar : TermLayer ℕ (Tm Code) (Pat ℕ Code) := termLayer parComm

/-- **With commutativity of `par` declared, `par(a, b)` and `par(b, a)` are one name**: every
reader treats them alike. -/
theorem par_comm_one_name : ∀ (p : Pat ℕ Code) (σ : Subst ℕ (Tm Code)),
    Lpar.Solves σ p (.node .par (.leaf .a) (.leaf .b)) ↔
      Lpar.Solves σ p (.node .par (.leaf .b) (.leaf .a)) :=
  indistinguishable_of_E (L := Lpar)
    (show ceq parComm (.node .par (.leaf .a) (.leaf .b)) (.node .par (.leaf .b) (.leaf .a)) = true
      by decide)

/-- **`par(a, nil)` and `a` are two names**: the unit law is not declared, and the ground pattern of
the first tells them apart. -/
theorem par_unit_two_names :
    ¬ ∀ (p : Pat ℕ Code) (σ : Subst ℕ (Tm Code)),
      Lpar.Solves σ p (.node .par (.leaf .a) (.leaf .nil)) ↔ Lpar.Solves σ p (.leaf .a) := by
  intro same
  have same' : ceq parComm (.node .par (.leaf .a) (.leaf .nil)) (.leaf .a) = true :=
    collapse_to_E (hasGroundPatterns (X := ℕ) parComm) same
  revert same'
  decide

end NameControls

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.OccurrenceCommits.Reflection
