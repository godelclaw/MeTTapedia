import Mettapedia.Machines.ConstructorContext
import Mettapedia.Machines.Cursor.TailSummary
import Mettapedia.Machines.Cursor.Fold
import Mathlib.Tactic

/-!
# Allocation-indexed atom summaries for constructor holes

A child contributes inherited (OR) bits, required (AND) bits, structural
facts guarded by a validity bit, a variable summary, and two closure tests.
Closure tests are made at the parent's arena, using the child's home. A
context thus acts on a *located* summary; a bare closure bit is insufficient.

The aggregate is a product monoid. Head adjustments and the parent's home
are installed only at the end. Fixed siblings can be aggregated at entry;
filling the hole needs two aggregate merges, independent of sibling count.
Bit families are parameters: finite native words instantiate them without
fixing a language's set of properties in the abstract theory.
-/

set_option autoImplicit false

namespace Mettapedia.Machines.ConstructorSummary

open ConstructorContext Cursor.TailSummary

universe u
variable {Bit : Type u}

theorem vars_join_assoc (a b c : Vars) :
    Vars.join (Vars.join a b) c = Vars.join a (Vars.join b c) := by
  cases a <;> cases b <;> cases c <;> simp [Vars.join]
  all_goals split_ifs <;> simp_all

@[ext] structure Aggregate (Bit : Type u) where
  inherited : Bit → Bool
  required : Bit → Bool
  facts : Bit → Bool
  valid : Bool
  closed : Bool
  generation : Bool
  vars : Vars

namespace Aggregate

def unit : Aggregate Bit :=
  ⟨fun _ => false, fun _ => true, fun _ => false, true, true, true, .none⟩

def merge (a b : Aggregate Bit) : Aggregate Bit :=
  ⟨fun i => a.inherited i || b.inherited i,
   fun i => a.required i && b.required i,
   fun i => a.facts i || b.facts i,
   a.valid && b.valid, a.closed && b.closed,
   a.generation && b.generation, Vars.join a.vars b.vars⟩

theorem merge_assoc (a b c : Aggregate Bit) :
    merge (merge a b) c = merge a (merge b c) := by
  ext <;> simp [merge, Bool.or_assoc, Bool.and_assoc, vars_join_assoc]

@[simp] theorem unit_merge (a : Aggregate Bit) : merge unit a = a := by
  ext <;> simp [merge, unit, Vars.join]

@[simp] theorem merge_unit (a : Aggregate Bit) : merge a unit = a := by
  ext <;> simp [merge, unit, Vars.join_none]

def fold (xs : List (Aggregate Bit)) : Aggregate Bit := xs.foldr merge unit

theorem fold_append (xs ys : List (Aggregate Bit)) :
    fold (xs ++ ys) = merge (fold xs) (fold ys) := by
  induction xs with
  | nil => simp [fold]
  | cons x xs ih =>
      simp only [List.cons_append, fold, List.foldr_cons] at *
      rw [ih, merge_assoc]

end Aggregate

/-- Summary of a completed atom. `generation` is the stored additional bit;
`closed || (valid && generation)` is the predicate used when admitting its generation. -/
structure Summary (Bit : Type u) where
  home : Home
  aggregate : Aggregate Bit

/-- The constructor's fixed allocation and fixed head-specific adjustments.
The runtime must identify the constructor head before choosing this plan. -/
structure Label (Bit : Type u) where
  arena : Nat
  older : Option Nat
  headAdds : Bit → Bool
  headForbids : Bit → Bool

def sameArena (here : Nat) : Home → Bool
  | .global => true
  | .arena there => there == here

def generationAdmits (label : Label Bit) (child : Summary Bit) : Bool :=
  match child.home with
  | .global => child.aggregate.closed
  | .arena there =>
      (there == label.arena || label.older == some there) &&
        (child.aggregate.closed || (child.aggregate.valid && child.aggregate.generation))

/-- Normalize one child's allocation-dependent contribution for this parent.
The ordinary structural facts exclude the separate generation/slack bits. -/
def contribution (label : Label Bit) (child : Summary Bit) : Aggregate Bit :=
  { child.aggregate with
    closed := child.aggregate.closed && sameArena label.arena child.home
    generation := generationAdmits label child }

/-- Native head adjustments and validity masking happen after the child fold. -/
def finish (label : Label Bit) (a : Aggregate Bit) : Summary Bit :=
  ⟨.arena label.arena,
   { a with
     inherited := fun i => a.inherited i || label.headAdds i
     required := fun i => a.required i && !label.headForbids i
     facts := fun i => a.valid && a.facts i
     generation := label.older.isSome && a.generation && !a.closed && a.valid }⟩

def combine (label : Label Bit) (children : List (Summary Bit)) : Summary Bit :=
  finish label (Aggregate.fold (children.map (contribution label)))

/-- Fixed siblings are scanned once while entering the context. -/
structure Prepared (Bit : Type u) where
  label : Label Bit
  left : Aggregate Bit
  right : Aggregate Bit

def prepare (frame : Frame (Label Bit) (Summary Bit)) : Prepared Bit :=
  ⟨frame.label, Aggregate.fold (frame.before.map (contribution frame.label)),
    Aggregate.fold (frame.after.map (contribution frame.label))⟩

/-- Two merges and one final adjustment; no traversal of the fixed siblings. -/
def complete (prepared : Prepared Bit) (hole : Summary Bit) : Summary Bit :=
  finish prepared.label (Aggregate.merge prepared.left
    (Aggregate.merge (contribution prepared.label hole) prepared.right))

theorem complete_eq_frame (frame : Frame (Label Bit) (Summary Bit))
    (hole : Summary Bit) :
    complete (prepare frame) hole = frame.apply combine hole := by
  simp only [complete, prepare, Frame.apply, combine, List.map_append,
    List.map_cons, Aggregate.fold_append]
  rfl

/-- A located recursive value model, providing an actual summary algebra. -/
inductive Term (Bit : Type u)
  | resident (summary : Summary Bit)
  | node (label : Label Bit) (children : List (Term Bit))

def summarize : Term Bit → Summary Bit
  | .resident summary => summary
  | .node label children => combine label (children.map summarize)

def algebra : SummaryAlgebra (Label Bit) (Term Bit) (Summary Bit) where
  build := Term.node
  observe := summarize
  combine := combine
  build_observe := by intros; simp [summarize]

/-- The precomputed per-cell action agrees with the full recursive fold. -/
theorem prepared_summary_exact (frame : Frame (Label Bit) (Term Bit))
    (value : Term Bit) :
    complete (prepare (frame.map summarize)) (summarize value) =
      summarize (frame.apply Term.node value) := by
  rw [complete_eq_frame]
  exact ((algebra (Bit := Bit)).observe_frame frame value).symm

/-- Every entry of the backward summary pass is the exact summary of the
corresponding suffix value, with its own allocation context. -/
theorem all_cells_exact (frames : List (Frame (Label Bit) (Term Bit)))
    (value : Term Bit) (index : Nat) (within : index ≤ frames.length) :
    ((algebra (Bit := Bit)).summaries frames value)[index]? =
      some (summarize (plug Term.node (frames.drop index) value)) :=
  (algebra (Bit := Bit)).summaries_at frames value index within

/-! Arena renaming preserves the actual allocation-dependent predicates only
when distinct arenas stay distinct and the older link moves with its label.
These laws transport a justified summary; they do not validate heap epochs,
interning tables, scalar caches, or ownership of opaque resources. -/

def Summary.mapArena (arena : Nat → Nat) (summary : Summary Bit) : Summary Bit :=
  ⟨summary.home.map arena, summary.aggregate⟩

def Label.mapArena (arena : Nat → Nat) (label : Label Bit) : Label Bit :=
  { label with arena := arena label.arena, older := label.older.map arena }

def Prepared.mapArena (arena : Nat → Nat) (prepared : Prepared Bit) : Prepared Bit :=
  { prepared with label := prepared.label.mapArena arena }

theorem Summary.mapArena_id (summary : Summary Bit) : summary.mapArena id = summary := by
  cases summary
  simp only [Summary.mapArena, Home.map_id]

theorem Summary.mapArena_comp (first second : Nat → Nat) (summary : Summary Bit) :
    (summary.mapArena first).mapArena second = summary.mapArena (second ∘ first) := by
  simp only [Summary.mapArena, Home.map_comp]

theorem Label.mapArena_id (label : Label Bit) : label.mapArena id = label := by
  cases label
  simp only [Label.mapArena, id_eq, Option.map_id]

theorem Label.mapArena_comp (first second : Nat → Nat) (label : Label Bit) :
    (label.mapArena first).mapArena second = label.mapArena (second ∘ first) := by
  simp only [Label.mapArena, Option.map_map, Function.comp_def]

private theorem arena_beq_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (one two : Nat) : (arena one == arena two) = (one == two) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, injective.eq_iff]

private theorem older_beq_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (one two : Option Nat) : (one.map arena == two.map arena) = (one == two) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Option.map_inj_right (f := arena) (fun _ _ equal => injective equal)]

theorem sameArena_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (here : Nat) (home : Home) :
    sameArena (arena here) (home.map arena) = sameArena here home := by
  cases home with
  | global => rfl
  | arena there => exact arena_beq_map arena injective there here

theorem generationAdmits_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (label : Label Bit) (child : Summary Bit) :
    generationAdmits (label.mapArena arena) (child.mapArena arena) =
      generationAdmits label child := by
  rcases child with ⟨home, aggregate⟩
  cases home with
  | global => rfl
  | arena there =>
    have older := older_beq_map arena injective label.older (some there)
    simpa only [generationAdmits, Label.mapArena, Summary.mapArena, Home.map,
      arena_beq_map arena injective, Option.map_some] using
      congrArg (fun same => (there == label.arena || same) &&
        (aggregate.closed || (aggregate.valid && aggregate.generation))) older

theorem contribution_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (label : Label Bit) (child : Summary Bit) :
    contribution (label.mapArena arena) (child.mapArena arena) = contribution label child := by
  change { child.aggregate with
    closed := child.aggregate.closed && sameArena (arena label.arena) (child.home.map arena)
    generation := generationAdmits (label.mapArena arena) (child.mapArena arena) } = _
  rw [sameArena_map arena injective, generationAdmits_map arena injective]
  rfl

theorem finish_map (arena : Nat → Nat) (label : Label Bit) (aggregate : Aggregate Bit) :
    finish (label.mapArena arena) aggregate = (finish label aggregate).mapArena arena := by
  simp only [finish, Label.mapArena, Summary.mapArena, Home.map, Option.isSome_map]

theorem combine_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (label : Label Bit) (children : List (Summary Bit)) :
    combine (label.mapArena arena) (children.map (Summary.mapArena arena)) =
      (combine label children).mapArena arena := by
  simp only [combine, List.map_map, Function.comp_def, contribution_map arena injective]
  exact finish_map arena label _

/-- A prepared constructor keeps its fixed aggregates and its constant amount
of completion work while its arena label and the hole move together. -/
theorem complete_map (arena : Nat → Nat) (injective : Function.Injective arena)
    (prepared : Prepared Bit) (hole : Summary Bit) :
    complete (prepared.mapArena arena) (hole.mapArena arena) =
      (complete prepared hole).mapArena arena := by
  simp only [complete, Prepared.mapArena, contribution_map arena injective]
  exact finish_map arena prepared.label _

/-! Retained expression assembly uses the existing pull-fold client. Its
unpublished accumulator keeps arbitrary child values separately from their
observations and accumulated summary:
summary equality alone cannot establish occurrence or position preservation.
Only the completed exact-arity fold exposes a finished constructor. Pulls,
aggregate merges and head adjustment have separate roles; none is a bound on
allocation, native instructions, or elapsed time. -/

namespace Assembly

variable {Bit Child : Type}

/-- Unpublished constructor storage. Children are prepended to the private
inventory; the allocation-dependent aggregate has not had its head adjusted. -/
structure Draft (Child Bit : Type) where
  remaining : Nat
  reversed : List Child
  aggregate : Aggregate Bit

def initial (arity : Nat) : Draft Child Bit := ⟨arity, [], Aggregate.unit⟩

/-- Exactly one child contributes at an accepted append. An extra child
refuses the whole assembly, rather than silently truncating its inventory. -/
def append (label : Label Bit) (observe : Child → Summary Bit) :
    Option (Draft Child Bit) → Child → Option (Draft Child Bit)
  | none, _ => none
  | some ⟨0, _, _⟩, _ => none
  | some ⟨remaining + 1, reversed, aggregate⟩, child =>
      some ⟨remaining, child :: reversed,
        Aggregate.merge aggregate (contribution label (observe child))⟩

theorem append_one (label : Label Bit) (observe : Child → Summary Bit) (remaining : Nat)
    (reversed : List Child) (aggregate : Aggregate Bit) (child : Child) :
    append label observe (some ⟨remaining + 1, reversed, aggregate⟩) child =
      some ⟨remaining, child :: reversed,
        Aggregate.merge aggregate (contribution label (observe child))⟩ := rfl

theorem append_after_full_refused (label : Label Bit) (observe : Child → Summary Bit)
    (reversed : List Child) (aggregate : Aggregate Bit) (child : Child) :
    append label observe (some ⟨0, reversed, aggregate⟩) child = none := rfl

theorem variable_conflict_absorbs (vars : Vars) :
    Vars.join .many vars = .many ∧ Vars.join vars .many = .many := by
  cases vars <;> exact ⟨rfl, rfl⟩

theorem append_variable_conflict (label : Label Bit) (observe : Child → Summary Bit) (remaining : Nat)
    (reversed : List Child) (aggregate : Aggregate Bit) (child : Child)
    (conflict : aggregate.vars = .many) :
    (append label observe (some ⟨remaining + 1, reversed, aggregate⟩) child).map
      (fun draft => draft.aggregate.vars) = some .many := by
  simp [append, Aggregate.merge, conflict, Vars.join]

theorem refused_fold (label : Label Bit) (observe : Child → Summary Bit) (children : List Child) :
    children.foldl (append label observe) none = none := by
  induction children with
  | nil => rfl
  | cons child rest ih => exact ih

/-- The prefix invariant holds from any actual retained draft: one accepted
append consumes one slot and one contribution, while preserving every child. -/
theorem fold_from (label : Label Bit) (observe : Child → Summary Bit) (draft : Draft Child Bit)
    (children : List Child) (fits : children.length ≤ draft.remaining) :
    children.foldl (append label observe) (some draft) =
      some ⟨draft.remaining - children.length, children.reverse ++ draft.reversed,
        Aggregate.merge draft.aggregate
          (Aggregate.fold (children.map (contribution label ∘ observe)))⟩ := by
  induction children generalizing draft with
  | nil => simp [Aggregate.fold]
  | cons child rest ih =>
      rcases draft with ⟨remaining, reversed, aggregate⟩
      cases remaining with
      | zero => simp at fits
      | succ remaining =>
          have smaller : rest.length ≤ remaining := by simpa using fits
          rw [List.foldl_cons]
          change rest.foldl (append label observe)
            (some ⟨remaining, child :: reversed,
              Aggregate.merge aggregate (contribution label (observe child))⟩) = _
          rw [ih _ smaller]
          simp [Aggregate.fold, Aggregate.merge_assoc, List.reverse_cons, List.append_assoc]

def prefixDraft (label : Label Bit) (observe : Child → Summary Bit) (arity : Nat) (children : List Child) : Draft Child Bit :=
  ⟨arity - children.length, children.reverse,
    Aggregate.fold (children.map (contribution label ∘ observe))⟩

theorem prefix_invariant (label : Label Bit) (observe : Child → Summary Bit) (arity : Nat)
    (children : List Child) (fits : children.length ≤ arity) :
    children.foldl (append label observe) (some (initial arity)) =
      some (prefixDraft label observe arity children) := by
  simpa [initial, prefixDraft] using fold_from label observe (initial arity) children fits

theorem overflow_refused (label : Label Bit) (observe : Child → Summary Bit) (draft : Draft Child Bit)
    (children : List Child) (overflow : draft.remaining < children.length) :
    children.foldl (append label observe) (some draft) = none := by
  induction children generalizing draft with
  | nil => simp at overflow
  | cons child rest ih =>
      rcases draft with ⟨remaining, reversed, aggregate⟩
      cases remaining with
      | zero => exact refused_fold label observe rest
      | succ remaining =>
          have smaller : remaining < rest.length := by simpa using overflow
          exact ih ⟨remaining, child :: reversed,
            Aggregate.merge aggregate (contribution label (observe child))⟩ smaller

/-- A chunk changes only the same private accumulator. No summary is
reinitialized and no already accepted child is appended again. -/
theorem chunk_composition (label : Label Bit) (observe : Child → Summary Bit) (draft : Option (Draft Child Bit))
    (first second : List Child) :
    second.foldl (append label observe) (first.foldl (append label observe) draft) =
      (first ++ second).foldl (append label observe) draft :=
  (List.foldl_append ..).symm

/-- Publication contains the complete ordered inventory and its adjusted
summary, unlike the unadjusted private draft. -/
structure Publication (Child Bit : Type) where
  children : List Child
  summary : Summary Bit

def publish (label : Label Bit) : Option (Draft Child Bit) → Option (Publication Child Bit)
  | some ⟨0, reversed, aggregate⟩ => some ⟨reversed.reverse, finish label aggregate⟩
  | _ => none

theorem publish_prefix (label : Label Bit) (observe : Child → Summary Bit) (children : List Child) :
    publish label (some (prefixDraft label observe children.length children)) =
      some ⟨children, combine label (children.map observe)⟩ := by
  simp [publish, prefixDraft, combine, List.map_map, Function.comp_def]

theorem missing_children_unpublished (label : Label Bit) (observe : Child → Summary Bit) (arity : Nat)
    (children : List Child) (missing : children.length < arity) :
    publish label (children.foldl (append label observe) (some (initial arity))) = none := by
  rw [prefix_invariant label observe arity children (Nat.le_of_lt missing)]
  have positive : 0 < arity - children.length := Nat.sub_pos_of_lt missing
  obtain ⟨remaining, equal⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  simp [prefixDraft, publish, equal]

theorem extra_children_unpublished (label : Label Bit) (observe : Child → Summary Bit) (arity : Nat)
    (children : List Child) (extra : arity < children.length) :
    publish label (children.foldl (append label observe) (some (initial arity))) = none := by
  rw [overflow_refused label observe (initial arity) children extra]
  rfl

abbrev source := Cursor.Sequence.tails Child
abbrev reader (label : Label Bit) (observe : Child → Summary Bit) := Cursor.Fold.client (append label observe)
abbrev Saved (label : Label Bit) (observe : Child → Summary Bit) :=
  Nat × Cursor.Outcome source (reader label observe) ()

def run (label : Label Bit) (observe : Child → Summary Bit)
    (arity allowance : Nat) (children : List Child) :
    Saved label observe :=
  Cursor.advance source (reader label observe) (fun _ _ => 1) allowance
    (Cursor.Fold.start source (append label observe) children (some (initial arity)))

def resume (label : Label Bit) (observe : Child → Summary Bit)
    (allowance : Nat) (saved : Saved label observe) : Saved label observe :=
  Cursor.resume source (reader label observe) (fun _ _ => 1) allowance saved

/-- A paused draft is never exported, including after the last child but
before the fold's exhaustion/return inspections. -/
def published (label : Label Bit) (observe : Child → Summary Bit) (saved : Saved label observe) : Option (Publication Child Bit) :=
  match saved.2 with
  | .paused _ => none
  | .done result => publish label result.2.1

theorem zero_allowance (label : Label Bit) (observe : Child → Summary Bit) (arity : Nat) (children : List Child) :
    run label observe arity 0 children = (0, .paused
      (Cursor.Fold.start source (append label observe) children (some (initial arity)))) := rfl

theorem resume_zero (label : Label Bit) (observe : Child → Summary Bit) (saved : Saved label observe) : resume label observe 0 saved = saved :=
  Cursor.resume_zero _ _ _ _

theorem pause_composition (label : Label Bit) (observe : Child → Summary Bit) (arity first second : Nat)
    (children : List Child) :
    resume label observe second (run label observe arity first children) =
      run label observe arity (first + second) children :=
  (Cursor.advance_add _ _ _ _ _ _).symm

/-- The actual cursor retains the exact prefix aggregate, ordered children,
unused slots and unpolled source. The charge counts pulls, not C work. -/
theorem cursor_prefix (label : Label Bit) (observe : Child → Summary Bit) (arity allowance : Nat)
    (children : List Child) (within : allowance ≤ children.length)
    (fits : allowance ≤ arity) :
    run label observe arity allowance children =
      (allowance, .paused (Cursor.Fold.start source (append label observe)
        (children.drop allowance) (some (prefixDraft label observe arity (children.take allowance))))) := by
  unfold run reader
  rw [Cursor.Fold.prefix_exact _ _ _ allowance within]
  rw [prefix_invariant label observe arity (children.take allowance) (by
    simpa [List.length_take, Nat.min_eq_left within] using fits)]

theorem paused_prefix_unpublished (label : Label Bit) (observe : Child → Summary Bit) (arity allowance : Nat)
    (children : List Child) (within : allowance ≤ children.length) :
    published label observe (run label observe arity allowance children) = none := by
  unfold run reader
  rw [Cursor.Fold.prefix_exact _ _ _ allowance within]
  rfl

/-- Completion has exactly the independent existing constructor summary and
every original child. The extra charged pull checks exhaustion. -/
theorem complete_eq_combine (label : Label Bit) (observe : Child → Summary Bit) (children : List Child) :
    run label observe children.length (children.length + 2) children =
      (children.length + 1, .done ⟨(), some (prefixDraft label observe children.length children), []⟩) ∧
    published label observe (run label observe children.length (children.length + 2) children) =
      some ⟨children, combine label (children.map observe)⟩ := by
  have completed : run label observe children.length (children.length + 2) children =
      (children.length + 1, .done ⟨(), some (prefixDraft label observe children.length children), []⟩) := by
    unfold run reader
    rw [Cursor.Fold.complete_exact, prefix_invariant label observe children.length children (by rfl)]
  refine ⟨completed, ?_⟩
  rw [completed]
  exact publish_prefix label observe children

theorem completed_missing_refused (label : Label Bit) (observe : Child → Summary Bit) (arity : Nat)
    (children : List Child) (missing : children.length < arity) :
    published label observe (run label observe arity (children.length + 2) children) = none := by
  unfold run reader
  rw [Cursor.Fold.complete_exact]
  exact missing_children_unpublished label observe arity children missing

theorem completed_extra_refused (label : Label Bit) (observe : Child → Summary Bit) (arity : Nat)
    (children : List Child) (extra : arity < children.length) :
    published label observe (run label observe arity (children.length + 2) children) = none := by
  unfold run reader
  rw [Cursor.Fold.complete_exact]
  exact extra_children_unpublished label observe arity children extra

/-- Any publication of a completed input has the declared arity, every child
in its original position, and exactly the existing full constructor summary. -/
theorem completion_sound (label : Label Bit) (observe : Child → Summary Bit) (arity : Nat)
    (children : List Child) (value : Publication Child Bit)
    (accepted : published label observe (run label observe arity (children.length + 2) children) = some value) :
    arity = children.length ∧ value.children = children ∧
      value.summary = combine label (children.map observe) := by
  rcases lt_trichotomy children.length arity with missing | full | extra
  · rw [completed_missing_refused label observe arity children missing] at accepted
    cases accepted
  · subst arity
    rw [(complete_eq_combine label observe children).2] at accepted
    cases Option.some.inj accepted
    exact ⟨rfl, rfl, rfl⟩
  · rw [completed_extra_refused label observe arity children extra] at accepted
    cases accepted

/-- The existing recursive value algebra supplies an actual observer. The
retained fold publishes the original terms, not only their observations. -/
theorem term_completion (label : Label Bit) (children : List (Term Bit)) :
    published label summarize
      (run label summarize children.length (children.length + 2) children) =
        some ⟨children, (algebra (Bit := Bit)).observe
          ((algebra (Bit := Bit)).build label children)⟩ := by
  simpa only [algebra, summarize] using (complete_eq_combine label summarize children).2

end Assembly

namespace Controls

def plain (arena : Nat) (older : Option Nat := none) : Label Unit :=
  ⟨arena, older, fun _ => false, fun _ => false⟩

def leaf (arena : Nat) : Summary Unit := ⟨.arena arena, Aggregate.unit⟩

/-- Equal closure bits at different homes cannot be substituted for one
another in a parent closure test. -/
theorem child_home_is_necessary :
    (leaf 1).aggregate.closed = (leaf 2).aggregate.closed ∧
    (combine (plain 1) [leaf 1]).aggregate.closed = true ∧
    (combine (plain 1) [leaf 2]).aggregate.closed = false := by decide

/-- Linking the older arena admits a child without claiming same-arena closure. -/
theorem older_arena_is_distinct :
    (combine (plain 1 (some 2)) [leaf 2]).aggregate.closed = false ∧
    (combine (plain 1 (some 2)) [leaf 2]).aggregate.generation = true := by decide

/-- A generation bit without valid structural facts is not evidence of
closure, matching the native generation-admission predicate. -/
theorem invalid_generation_is_not_admitted :
    let child : Summary Unit := ⟨.arena 2,
      { Aggregate.unit with closed := false, valid := false }⟩
    generationAdmits (plain 1 (some 2)) child = false := by decide

/-- Facts from an invalid child do not become a valid parent cache. -/
theorem unknown_facts_stay_unknown :
    let child : Summary Unit := ⟨.global,
      { Aggregate.unit with facts := fun _ => true, valid := false }⟩
    (combine (plain 1) [child]).aggregate.valid = false ∧
    (combine (plain 1) [child]).aggregate.facts () = false := by decide

/-- The frame's head adjustment cannot be omitted merely because all
children share the same ordinary bit fold. -/
theorem head_adjustment_is_necessary :
    let special : Label Unit := { plain 1 with headAdds := fun _ => true }
    (combine special [leaf 1]).aggregate.inherited () = true ∧
    (combine (plain 1) [leaf 1]).aggregate.inherited () = false := by decide

/-- Ignoring the hole's variable summary loses a real distinction. -/
theorem hole_vars_are_necessary :
    let child : Summary Unit := ⟨.arena 1,
      { Aggregate.unit with vars := .one 7 }⟩
    (combine (plain 1) [child]).aggregate.vars = .one 7 ∧
    (combine (plain 1) []).aggregate.vars = .none := by decide

/-- Moving both distinct domains and the older edge preserves the two
different native closure predicates. -/
theorem mapped_older_edge_preserves_reuse :
    (combine ((plain 17 (some 29)).mapArena (· + 1000))
      [(leaf 29).mapArena (· + 1000)]).aggregate.closed = false ∧
    (combine ((plain 17 (some 29)).mapArena (· + 1000))
      [(leaf 29).mapArena (· + 1000)]).aggregate.generation = true := by decide

/-- Merging two allocation domains invents a same-arena reuse decision even
though the child's ordinary property bits did not change. -/
theorem coalesced_arenas_invent_reuse :
    (contribution (plain 17) (leaf 29)).closed = false ∧
    (contribution ((plain 17).mapArena (fun _ => 1000))
      ((leaf 29).mapArena (fun _ => 1000))).closed = true := by decide

/-- Omitting the transported older link loses a legitimate generation reuse. -/
theorem missing_older_edge_loses_reuse :
    generationAdmits (plain 17 (some 29)) (leaf 29) = true ∧
    generationAdmits (plain 1017) ((leaf 29).mapArena (· + 1000)) = false := by decide

/-- Moving the hole while keeping its old constructor label also changes the
allocation-dependent decision. -/
theorem unmoved_label_loses_reuse :
    (contribution (plain 17) (leaf 17)).closed = true ∧
    (contribution (plain 17) ((leaf 17).mapArena (· + 1000))).closed = false := by decide

end Controls

namespace Assembly.Controls

open ConstructorSummary.Controls

def named (id : Nat) : Summary Unit :=
  ⟨.arena 1, { Aggregate.unit with vars := .one id }⟩

/-- A pause keeps two accepted child occurrences, one unused slot, the
unadjusted summary, and the third child at the source cursor. -/
theorem actual_prefix_keeps_inventory :
    run (plain 1) id 3 2 [named 7, leaf 1, named 7] =
      (2, .paused (Cursor.Fold.start source (append (plain 1) id) [named 7]
        (some ⟨1, [leaf 1, named 7],
          Aggregate.merge (contribution (plain 1) (named 7))
            (contribution (plain 1) (leaf 1))⟩))) := rfl

/-- Two slices publish the same complete constructor without replaying their
shared prefix. Repeated occurrences of one variable retain its identity. -/
theorem resumed_children_complete :
    published (plain 1) id
      (resume (plain 1) id 3 (run (plain 1) id 3 2 [named 7, leaf 1, named 7])) =
        some ⟨[named 7, leaf 1, named 7],
          combine (plain 1) [named 7, leaf 1, named 7]⟩ ∧
    (combine (plain 1) [named 7, leaf 1, named 7]).aggregate.vars = .one 7 := by
  constructor
  · rw [pause_composition]
    exact (complete_eq_combine (plain 1) id [named 7, leaf 1, named 7]).2
  · rfl

theorem zero_resume_keeps_partial_constructor :
    resume (plain 1) id 0 (run (plain 1) id 3 2 [named 7, leaf 1, named 7]) =
      run (plain 1) id 3 2 [named 7, leaf 1, named 7] := resume_zero _ _ _

/-- Filling every slot is still an unpublished fold prefix. -/
theorem full_prefix_is_unpublished :
    published (plain 1) id (run (plain 1) id 2 2 [named 7, named 9]) = none := rfl

theorem a_missing_child_cannot_publish :
    published (plain 1) id (run (plain 1) id 2 3 [named 7]) = none := rfl

/-- Appending a duplicate instead of stopping at the declared arity refuses;
the duplicate does not disappear into idempotent summary bits. -/
theorem an_extra_duplicate_cannot_publish :
    published (plain 1) id (run (plain 1) id 2 5 [named 7, named 9, named 9]) = none := rfl

/-- Replacing a distinct child by a duplicate preserves the slot count but
changes the variable summary, so the two constructors are distinguishable. -/
theorem replacing_a_child_by_a_duplicate_changes_variables :
    (published (plain 1) id (run (plain 1) id 2 4 [named 7, named 9])).map
      (fun value => value.summary.aggregate.vars) = some .many ∧
    (published (plain 1) id (run (plain 1) id 2 4 [named 7, named 7])).map
      (fun value => value.summary.aggregate.vars) = some (.one 7) := by decide

/-- Summary bits may agree after reordering. Publication nevertheless retains
the distinct ordered child inventory rather than treating it as a bag. -/
theorem reordered_children_keep_distinct_positions :
    combine (plain 1) [leaf 1, leaf 2] = combine (plain 1) [leaf 2, leaf 1] ∧
    (published (plain 1) id (run (plain 1) id 2 4 [leaf 1, leaf 2])).map
      (fun value => value.children.map (·.home)) = some [.arena 1, .arena 2] ∧
    (published (plain 1) id (run (plain 1) id 2 4 [leaf 1, leaf 2])).map
      (fun value => value.children.map (·.home)) ≠
    (published (plain 1) id (run (plain 1) id 2 4 [leaf 2, leaf 1])).map
      (fun value => value.children.map (·.home)) := by
  exact ⟨rfl, by decide, by decide⟩

/-- After two distinct variables conflict, an additional child cannot
restore the misleading single-variable summary. -/
theorem variable_conflict_stays_absorbing :
    (published (plain 1) id (run (plain 1) id 3 5 [named 7, named 9, named 7])).map
      (fun value => value.summary.aggregate.vars) = some .many := by decide

/-- The head's adjustment is absent from the accumulated child fold and is
installed at publication, through the existing final adjustment operation. -/
theorem head_adjustment_waits_for_publication :
    let special : Label Unit := { plain 1 with headAdds := fun _ => true }
    (prefixDraft special id 1 [leaf 1]).aggregate.inherited () = false ∧
    (published special id (run special id 1 3 [leaf 1])).map
      (fun value => value.summary.aggregate.inherited ()) = some true := by decide

/-- Assembly tests closure at the parent allocation. An older-generation
child is admitted without being relabelled as same-arena storage. -/
theorem retained_assembly_uses_child_home :
    (published (plain 1 (some 2)) id
      (run (plain 1 (some 2)) id 1 3 [leaf 2])).map
      (fun value => (value.summary.aggregate.closed, value.summary.aggregate.generation)) =
        some (false, true) ∧
    (published (plain 1 (some 2)) id
      (run (plain 1 (some 2)) id 1 3 [leaf 1])).map
      (fun value => (value.summary.aggregate.closed, value.summary.aggregate.generation)) =
        some (true, false) := by decide

/-- Distinct child identities may have exactly the same located summary. -/
def identicalObservation (_ : Nat) : Summary Unit := leaf 1

/-- Reordering equal observations preserves the complete summary but changes
the actual ordered values returned by the constructor. -/
theorem equal_observations_do_not_identify_reordered_children :
    (published (plain 1) identicalObservation
      (run (plain 1) identicalObservation 2 4 [11, 22])).map (·.summary) =
    (published (plain 1) identicalObservation
      (run (plain 1) identicalObservation 2 4 [22, 11])).map (·.summary) ∧
    (published (plain 1) identicalObservation
      (run (plain 1) identicalObservation 2 4 [11, 22])).map (·.children) ≠
    (published (plain 1) identicalObservation
      (run (plain 1) identicalObservation 2 4 [22, 11])).map (·.children) := by
  exact ⟨rfl, by decide⟩

/-- Replacing a child by another occurrence of its peer preserves arity and
summary, but it does not preserve the constructor's actual child inventory. -/
theorem equal_observations_do_not_identify_duplicate_replacement :
    (published (plain 1) identicalObservation
      (run (plain 1) identicalObservation 2 4 [11, 22])).map (·.summary) =
    (published (plain 1) identicalObservation
      (run (plain 1) identicalObservation 2 4 [11, 11])).map (·.summary) ∧
    (published (plain 1) identicalObservation
      (run (plain 1) identicalObservation 2 4 [11, 22])).map (·.children) ≠
    (published (plain 1) identicalObservation
      (run (plain 1) identicalObservation 2 4 [11, 11])).map (·.children) := by
  exact ⟨rfl, by decide⟩

end Assembly.Controls

end Mettapedia.Machines.ConstructorSummary
