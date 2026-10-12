import Mathlib.Logic.Equiv.Basic
import Mathlib.Data.Set.Basic
import Mathlib.Data.Fin.VecNotation

/-!
# Relations on names that do not see which names they are

A relation on names that is defined without mentioning the names outside a
set is closed under the renamings that fix that set.  Which renamings it is
closed under decides what it can say about the names outside the set.  This
module is about names only: a type with decidable equality, a set of fixed
names, and a relation.  No term and no rule occurs.

## Closed under the permutations: the equality pattern and nothing else

The **equality pattern** of some names is which of them are one name.  Two
lists of names outside the fixed set with one equality pattern are carried one
to the other by a permutation that fixes the set
(`exists_perm_of_same_pattern`).  So a relation on any number of names that is
closed under such permutations holds of both or of neither
(`holds_iff_of_same_pattern`): it is a set of equality patterns.

For two names there are two patterns, one name or two names, and so **four
relations: the empty one, equality, difference, and the full one**
(`pair_relation_one_of_four`).  A relation closed under the injective
renamings is closed under the permutations, so this covers it.

## Closed under all renamings: what holds of two names holds of one

A renaming that need not be injective can make two names one
(`mergeInto`).  A relation closed under every renaming that fixes the set
is kept by every coarsening of the pattern (`holds_of_coarser_pattern`): what
holds of some names holds when some of them are made one.  For two names that
leaves **three relations: the empty one, equality, and the full one**
(`pair_relation_one_of_three`).  Difference is the one that is lost: it is
closed under the injective renamings and under no merging
(`difference_closed_injective`, `difference_not_closed_merge`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.NameEquality

universe u

variable {α : Type u} [DecidableEq α]

/-- **The renaming that makes one name into another**, and leaves every other
name as it is. -/
def mergeInto (moved kept : α) : α → α := fun name => if name = moved then kept else name

/-- **Positive**: the moved name becomes the kept one. -/
theorem mergeInto_moved (moved kept : α) : mergeInto moved kept moved = kept := by
  simp [mergeInto]

/-- **Negative**: no other name moves. -/
theorem mergeInto_of_ne {moved kept name : α} (other : name ≠ moved) :
    mergeInto moved kept name = name := by
  simp [mergeInto, other]

/-- A merging fixes every set that does not hold the moved name. -/
theorem mergeInto_fixes {fixed : Set α} {moved : α} (outside : moved ∉ fixed) (kept : α) :
    ∀ name ∈ fixed, mergeInto moved kept name = name :=
  fun _ inFixed => mergeInto_of_ne fun same => outside (same ▸ inFixed)

/-- A merging of two names is not injective. -/
theorem mergeInto_not_injective {moved kept : α} (different : moved ≠ kept) :
    ¬ Function.Injective (mergeInto moved kept) := fun injective =>
  different (injective ((mergeInto_moved moved kept).trans
    (mergeInto_of_ne (Ne.symm different)).symm))

/-! ## Permutations: two lists of names with one equality pattern -/

/-- **Names with one equality pattern are carried to each other by a
permutation that fixes the set**: two lists of names outside a set, such that
two places hold one name in the first list exactly when they do in the second. -/
theorem exists_perm_of_same_pattern (fixed : Set α) :
    ∀ {count : Nat} (first second : Fin count → α), (∀ index, first index ∉ fixed) →
      (∀ index, second index ∉ fixed) →
      (∀ index other, first index = first other ↔ second index = second other) →
        ∃ naming : Equiv.Perm α, (∀ name ∈ fixed, naming name = name) ∧
          ∀ index, naming (first index) = second index
  | 0, _, _, _, _, _ => ⟨Equiv.refl α, fun _ _ => rfl, fun index => index.elim0⟩
  | count + 1, first, second, outsideFirst, outsideSecond, pattern => by
      obtain ⟨naming, fixes, maps⟩ := exists_perm_of_same_pattern fixed
        (fun index : Fin count => first index.succ) (fun index => second index.succ)
        (fun index => outsideFirst index.succ) (fun index => outsideSecond index.succ)
        (fun index other => pattern index.succ other.succ)
      by_cases known : ∃ other : Fin count, first 0 = first other.succ
      · obtain ⟨other, same⟩ := known
        refine ⟨naming, fixes, fun index => ?_⟩
        refine Fin.cases ?_ (fun later => maps later) index
        rw [same, maps other]
        exact ((pattern 0 other.succ).mp same).symm
      · refine ⟨naming.trans (Equiv.swap (naming (first 0)) (second 0)), fun name inFixed => ?_,
          fun index => ?_⟩
        · show Equiv.swap (naming (first 0)) (second 0) (naming name) = name
          rw [fixes name inFixed]
          refine Equiv.swap_apply_of_ne_of_ne (fun same => ?_) (fun same => ?_)
          · have images : naming name = naming (first 0) := (fixes name inFixed).trans same
            exact outsideFirst 0 (naming.injective images ▸ inFixed)
          · exact outsideSecond 0 (same ▸ inFixed)
        · refine Fin.cases ?_ (fun later => ?_) index
          · exact Equiv.swap_apply_left _ _
          · show Equiv.swap (naming (first 0)) (second 0) (naming (first later.succ)) =
              second later.succ
            rw [maps later]
            refine Equiv.swap_apply_of_ne_of_ne (fun same => ?_) (fun same => ?_)
            · exact known ⟨later, (naming.injective ((maps later).trans same)).symm⟩
            · exact known ⟨later, ((pattern later.succ 0).mpr same).symm⟩

/-- **A relation on names that is closed under the permutations fixing a set
is a set of equality patterns**: it holds of both or of neither of two lists
of names outside the set with one equality pattern. -/
theorem holds_iff_of_same_pattern {fixed : Set α} {count : Nat}
    {holds : (Fin count → α) → Prop}
    (closed : ∀ naming : Equiv.Perm α, (∀ name ∈ fixed, naming name = name) →
      ∀ names, holds names → holds (naming ∘ names))
    {first second : Fin count → α} (outsideFirst : ∀ index, first index ∉ fixed)
    (outsideSecond : ∀ index, second index ∉ fixed)
    (pattern : ∀ index other, first index = first other ↔ second index = second other) :
    holds first ↔ holds second := by
  constructor
  · intro held
    obtain ⟨naming, fixes, maps⟩ :=
      exists_perm_of_same_pattern fixed first second outsideFirst outsideSecond pattern
    have moved := closed naming fixes first held
    rwa [show (naming ∘ first) = second from funext maps] at moved
  · intro held
    obtain ⟨naming, fixes, maps⟩ :=
      exists_perm_of_same_pattern fixed second first outsideSecond outsideFirst
        fun index other => (pattern index other).symm
    have moved := closed naming fixes second held
    rwa [show (naming ∘ second) = first from funext maps] at moved

/-! ## All renamings: a coarser pattern -/

/-- **A relation on names that is closed under every renaming fixing a set is
kept when names are made one**: if it holds of a list of names outside the
set, it holds of every list in which two places hold one name whenever they do
in the first. -/
theorem holds_of_coarser_pattern {fixed : Set α} {count : Nat}
    {holds : (Fin count → α) → Prop}
    (closed : ∀ naming : α → α, (∀ name ∈ fixed, naming name = name) →
      ∀ names, holds names → holds (naming ∘ names))
    {first second : Fin count → α} (outsideFirst : ∀ index, first index ∉ fixed)
    (coarser : ∀ index other, first index = first other → second index = second other)
    (held : holds first) : holds second := by
  classical
  let naming : α → α := fun name =>
    if found : ∃ index, first index = name then second found.choose else name
  have maps : ∀ index, naming (first index) = second index := by
    intro index
    have found : ∃ other, first other = first index := ⟨index, rfl⟩
    show (if found : ∃ other, first other = first index then second found.choose
      else first index) = second index
    rw [dif_pos found]
    exact coarser _ _ found.choose_spec
  have fixes : ∀ name ∈ fixed, naming name = name := by
    intro name inFixed
    have absent : ¬ ∃ index, first index = name := fun ⟨index, same⟩ =>
      outsideFirst index (same ▸ inFixed)
    show (if found : ∃ index, first index = name then second found.choose else name) = name
    rw [dif_neg absent]
  have moved := closed naming fixes first held
  rwa [show (naming ∘ first) = second from funext maps] at moved

/-! ## Two names -/

omit [DecidableEq α] in
/-- The equality pattern of two names: one name, or two. -/
theorem pair_pattern {first second other last : α} (same : first = second ↔ other = last) :
    ∀ index place : Fin 2,
      ![first, second] index = ![first, second] place ↔
        ![other, last] index = ![other, last] place := by
  refine Fin.forall_fin_two.mpr ⟨Fin.forall_fin_two.mpr ⟨?_, ?_⟩, Fin.forall_fin_two.mpr ⟨?_, ?_⟩⟩
  · simp
  · simpa using same
  · simpa [eq_comm] using same
  · simp

/-- **A relation on two names that is closed under the permutations fixing a
set is one of four on the names outside the set: the empty one, equality,
difference, or the full one.**  In particular a relation closed under the
injective renamings that fix the set. -/
theorem pair_relation_one_of_four {fixed : Set α} {holds : α → α → Prop}
    (closed : ∀ naming : Equiv.Perm α, (∀ name ∈ fixed, naming name = name) →
      ∀ first second, holds first second → holds (naming first) (naming second)) :
    (∀ first second, first ∉ fixed → second ∉ fixed → ¬ holds first second) ∨
      (∀ first second, first ∉ fixed → second ∉ fixed → (holds first second ↔ first = second)) ∨
      (∀ first second, first ∉ fixed → second ∉ fixed → (holds first second ↔ first ≠ second)) ∨
      ∀ first second, first ∉ fixed → second ∉ fixed → holds first second := by
  have onPairs : ∀ {first second other last : α}, first ∉ fixed → second ∉ fixed →
      other ∉ fixed → last ∉ fixed → (first = second ↔ other = last) →
        (holds first second ↔ holds other last) := by
    intro first second other last outFirst outSecond outOther outLast same
    exact holds_iff_of_same_pattern (count := 2) (fixed := fixed)
      (holds := fun names => holds (names 0) (names 1))
      (fun naming fixes names held => closed naming fixes _ _ held)
      (first := ![first, second]) (second := ![other, last])
      (Fin.forall_fin_two.mpr ⟨outFirst, outSecond⟩)
      (Fin.forall_fin_two.mpr ⟨outOther, outLast⟩) (pair_pattern same)
  by_cases onOne : ∃ name, name ∉ fixed ∧ holds name name
  · obtain ⟨name, outName, heldOne⟩ := onOne
    have diagonal : ∀ other, other ∉ fixed → holds other other := fun other outOther =>
      (onPairs outName outName outOther outOther ⟨fun _ => rfl, fun _ => rfl⟩).mp heldOne
    by_cases onTwo : ∃ first second, first ∉ fixed ∧ second ∉ fixed ∧ first ≠ second ∧
        holds first second
    · obtain ⟨left, right, outLeft, outRight, different, heldTwo⟩ := onTwo
      refine .inr (.inr (.inr fun first second outFirst outSecond => ?_))
      by_cases same : first = second
      · exact same ▸ diagonal first outFirst
      · exact (onPairs outLeft outRight outFirst outSecond
          ⟨fun equal => absurd equal different, fun equal => absurd equal same⟩).mp heldTwo
    · refine .inr (.inl fun first second outFirst outSecond => ⟨fun held => ?_, fun same => ?_⟩)
      · by_contra different
        exact onTwo ⟨first, second, outFirst, outSecond, different, held⟩
      · exact same ▸ diagonal first outFirst
  · by_cases onTwo : ∃ first second, first ∉ fixed ∧ second ∉ fixed ∧ first ≠ second ∧
        holds first second
    · obtain ⟨left, right, outLeft, outRight, different, heldTwo⟩ := onTwo
      refine .inr (.inr (.inl fun first second outFirst outSecond => ⟨fun held same => ?_,
        fun other => ?_⟩))
      · exact onOne ⟨first, outFirst, same ▸ held⟩
      · exact (onPairs outLeft outRight outFirst outSecond
          ⟨fun equal => absurd equal different, fun equal => absurd equal other⟩).mp heldTwo
    · refine .inl fun first second outFirst outSecond held => ?_
      by_cases same : first = second
      · exact onOne ⟨first, outFirst, same ▸ held⟩
      · exact onTwo ⟨first, second, outFirst, outSecond, same, held⟩

/-- **What holds of two names holds when the second is made the first**, for
a relation closed under every renaming that fixes a set, and a second name
outside the set. -/
theorem holds_of_merged {fixed : Set α} {holds : α → α → Prop}
    (closed : ∀ naming : α → α, (∀ name ∈ fixed, naming name = name) →
      ∀ first second, holds first second → holds (naming first) (naming second))
    {first second : α} (outside : second ∉ fixed) (held : holds first second) :
    holds first first := by
  by_cases same : first = second
  · subst same
    exact held
  · have moved := closed (mergeInto second first) (mergeInto_fixes outside first) _ _ held
    rwa [mergeInto_of_ne same, mergeInto_moved] at moved

/-- **A relation on two names that is closed under every renaming fixing a
set is one of three on the names outside the set: the empty one, equality, or
the full one.**  It is never difference. -/
theorem pair_relation_one_of_three {fixed : Set α} {holds : α → α → Prop}
    (closed : ∀ naming : α → α, (∀ name ∈ fixed, naming name = name) →
      ∀ first second, holds first second → holds (naming first) (naming second)) :
    (∀ first second, first ∉ fixed → second ∉ fixed → ¬ holds first second) ∨
      (∀ first second, first ∉ fixed → second ∉ fixed → (holds first second ↔ first = second)) ∨
      ∀ first second, first ∉ fixed → second ∉ fixed → holds first second := by
  rcases pair_relation_one_of_four (fixed := fixed) (holds := holds)
      (fun naming fixes first second held => closed naming fixes first second held) with
    empty | equality | difference | full
  · exact .inl empty
  · exact .inr (.inl equality)
  · refine .inl fun first second outFirst outSecond held => ?_
    have merged := holds_of_merged closed outSecond held
    exact (difference first first outFirst outFirst).mp merged rfl
  · exact .inr (.inr full)

/-! ## Difference: closed under the injective renamings, under no merging -/

omit [DecidableEq α] in
/-- **Positive**: difference is kept by every injective renaming. -/
theorem difference_closed_injective {naming : α → α} (injective : Function.Injective naming)
    {first second : α} (different : first ≠ second) : naming first ≠ naming second :=
  fun same => different (injective same)

/-- **Negative**: difference is not kept by the merging of two names. -/
theorem difference_not_closed_merge {first second : α} (different : first ≠ second) :
    ¬ (mergeInto second first first ≠ mergeInto second first second) := by
  rw [mergeInto_of_ne different, mergeInto_moved]
  exact fun apart => apart rfl

#print axioms exists_perm_of_same_pattern
#print axioms holds_iff_of_same_pattern
#print axioms holds_of_coarser_pattern
#print axioms pair_relation_one_of_four
#print axioms holds_of_merged
#print axioms pair_relation_one_of_three
#print axioms difference_closed_injective
#print axioms difference_not_closed_merge

end Mettapedia.Logic.HostingStyles.NameEquality
