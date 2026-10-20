import Mettapedia.OSLF.MeTTaIL.CollectionSelection
import Mettapedia.OSLF.MeTTaIL.CanonicalBags
import Mettapedia.OSLF.MeTTaIL.DerivedContexts

/-!
# Collection selection against the canonical collection model

The shared finite selector realizes `CanonicalBags.Presents`: permutation for
bags, membership equality for sets. Its residuals also construct existing
one-hole contexts. Both removing and retaining a selected set member are
needed for contextual reduction modulo idempotence.

These results concern a single collection layer. Licensed recursive site
generation, scoped matching and admission consume additional typing and
binding obligations; they are not discharged by this module.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionSelection

open Syntax CanonicalBags DerivedContexts

/-- Choose the residual semantics declared by the collection kind. Ordered
vectors continue to use their positional matcher. -/
def kindResiduals (kind : CollType) (items : List Pattern) (selected : Nat) :
    List (List Pattern) :=
  residuals (kind == .hashSet) items selected

def kindAllocations (kind : CollType) (count : Nat) (items : List Pattern) :
    List (List Pattern × List Pattern) :=
  allocations (kind == .hashSet) count items

theorem residuals_present_exact {kind : CollType} {items rest : List Pattern} {selected : Nat}
    (unordered : kind ≠ .vec) (distinct : kind = .hashSet → items.Nodup)
    (within : selected < items.length) :
    (∃ actual ∈ kindResiduals kind items selected, Presents kind actual rest) ↔
      Presents kind items (items[selected] :: rest) := by
  cases kind with
  | vec => exact False.elim (unordered rfl)
  | hashBag => exact bag_residuals_exact within
  | hashSet => exact set_residuals_exact (distinct rfl) within

theorem allocations_present_exact {kind : CollType} {items selected rest : List Pattern}
    (unordered : kind ≠ .vec) (distinct : kind = .hashSet → items.Nodup) :
    (∃ actual, (selected, actual) ∈ kindAllocations kind selected.length items ∧
      Presents kind actual rest) ↔ Presents kind items (selected ++ rest) := by
  cases kind with
  | vec => exact False.elim (unordered rfl)
  | hashBag => exact bag_allocations_exact
  | hashSet => exact set_allocations_exact (distinct rfl)

/-- Canonical sets meet the finite selector's sole carrier invariant. -/
theorem canonical_set_distinct (items : List Pattern) :
    (arrange .hashSet items).Nodup := List.nodup_dedup _

theorem presents_cons {kind : CollType} {first second : List Pattern}
    (same : Presents kind first second) (item : Pattern) :
    Presents kind (item :: first) (item :: second) := by
  cases kind with
  | vec => exact congrArg (List.cons item) same
  | hashBag => exact same.cons item
  | hashSet =>
      intro candidate
      simp only [List.mem_cons, same candidate]

/-- A selected collection element is the hole; its residual is carried
unchanged by the existing structural context representation. -/
def residualContext (kind : CollType) (rest : List Pattern) : OneHoleContext :=
  .collection kind [] .hole rest none

theorem residualContext_fill (kind : CollType) (rest : List Pattern) (item : Pattern) :
    (residualContext kind rest).fill item = .collection kind (item :: rest) none := rfl

/-- Every semantically valid residual has an enumerated representative whose
context reconstructs the source and preserves any replacement modulo the
existing canonical equality. -/
theorem context_representative {kind : CollType} {items rest : List Pattern} {selected : Nat}
    (unordered : kind ≠ .vec) (distinct : kind = .hashSet → items.Nodup)
    (within : selected < items.length)
    (covers : Presents kind items (items[selected] :: rest)) :
    ∃ actual ∈ kindResiduals kind items selected,
      Same (.collection kind items none) ((residualContext kind actual).fill items[selected]) ∧
      ∀ replacement,
        Same ((residualContext kind actual).fill replacement)
          ((residualContext kind rest).fill replacement) := by
  obtain ⟨actual, member, same⟩ := (residuals_present_exact unordered distinct within).mpr covers
  have reconstructs : Presents kind items (items[selected] :: actual) :=
    (residuals_present_exact unordered distinct within).mp ⟨actual, member, Presents.of_eq rfl⟩
  refine ⟨actual, member, ?_, ?_⟩
  · exact canon_collection_of_presents kind none (reconstructs.map canon)
  · intro replacement
    exact canon_collection_of_presents kind none ((presents_cons same replacement).map canon)

/-- A real set context may retain a copy of its hole value. -/
example :
    Same (.collection .hashSet [.fvar "a"] none)
      ((residualContext .hashSet [.fvar "a"]).fill (.fvar "a")) := by
  apply same_of_bagStep
  exact .members (by intro item; simp [OneHoleContext.fill])

/-- The retained-copy context produces a different successor from consumption. -/
example :
    ¬ Same ((residualContext .hashSet [.fvar "a"]).fill (.fvar "b"))
      ((residualContext .hashSet []).fill (.fvar "b")) := by
  intro same
  change canon (.collection .hashSet [.fvar "b", .fvar "a"] none) =
    canon (.collection .hashSet [.fvar "b"] none) at same
  rw [canon_collection, canon_collection] at same
  have members := presents_of_arrange_eq (Pattern.collection.inj same).2.1
  have missing := (members (canon (.fvar "a"))).mp (by simp)
  simp [canon] at missing

/-- Keeping the selected occurrence would change the original bag's meaning. -/
example :
    ¬ Same (.collection .hashBag [.fvar "a"] none)
      ((residualContext .hashBag [.fvar "a"]).fill (.fvar "a")) := by
  intro same
  change canon (.collection .hashBag [.fvar "a"] none) =
    canon (.collection .hashBag [.fvar "a", .fvar "a"] none) at same
  rw [canon_collection, canon_collection] at same
  have lengths := congrArg List.length (Pattern.collection.inj same).2.1
  simp [arrange_bag, (PatternLexOrder.sortLex_perm _).length_eq] at lengths

end Mettapedia.OSLF.MeTTaIL.CollectionSelection
