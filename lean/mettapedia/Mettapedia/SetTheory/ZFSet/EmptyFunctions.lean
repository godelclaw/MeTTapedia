import Mathlib.SetTheory.ZFC.Basic

/-!
# Functions out of the empty set

Read as a set, a function from `x` to `y` is a set of pairs, and `ZFSet.funs x y`
is the set of all such functions.  Out of the empty set there is exactly one
function, the empty set itself, whatever the codomain (`funs_empty`).  The
function sets out of the empty set are therefore one and the same set for every
codomain (`funs_empty_eq`): numbers to the empty power and propositions to the
empty power coincide.  Out of an inhabited set the codomain matters
(`funs_singleton_ne`).

Types keep the codomains apart.  `Empty → α` and `Empty → β` are different types,
each with exactly one inhabitant, so they are equivalent (`emptyFunctionsEquiv`)
without being identified by the type theory.
-/

set_option autoImplicit false

namespace Mettapedia.SetTheory.ZFSetEmptyFunctions

universe u

/-- No pair has its first component in the empty set. -/
theorem prod_empty_left (y : ZFSet.{u}) : ZFSet.prod ∅ y = ∅ := by
  rw [ZFSet.eq_empty]
  intro z member
  obtain ⟨a, inEmpty, _⟩ := ZFSet.mem_prod.mp member
  exact ZFSet.notMem_empty a inEmpty

/-- A function out of the empty set is the empty set. -/
theorem isFunc_empty_iff (y f : ZFSet.{u}) : ZFSet.IsFunc ∅ y f ↔ f = ∅ := by
  constructor
  · rintro ⟨inside, -⟩
    rw [ZFSet.eq_empty]
    intro z member
    have inProd := inside member
    rw [prod_empty_left] at inProd
    exact ZFSet.notMem_empty z inProd
  · rintro rfl
    refine ⟨fun z member => (ZFSet.notMem_empty z member).elim, ?_⟩
    intro z member
    exact (ZFSet.notMem_empty z member).elim

/-- **Exactly one function out of the empty set**, whatever the codomain. -/
theorem funs_empty (y : ZFSet.{u}) : ZFSet.funs ∅ y = {∅} := by
  ext f
  rw [ZFSet.mem_funs, isFunc_empty_iff, ZFSet.mem_singleton]

/-- **The function sets out of the empty set coincide for all codomains.** -/
theorem funs_empty_eq (y y' : ZFSet.{u}) : ZFSet.funs ∅ y = ZFSet.funs ∅ y' := by
  rw [funs_empty, funs_empty]

/-- There is no function from an inhabited set into the empty set. -/
theorem funs_singleton_empty : ZFSet.funs {∅} (∅ : ZFSet.{u}) = ∅ := by
  rw [ZFSet.eq_empty]
  intro f member
  obtain ⟨inside, total⟩ := ZFSet.mem_funs.mp member
  obtain ⟨w, inF, -⟩ := total ∅ (ZFSet.mem_singleton.mpr rfl)
  have inProd := inside inF
  rw [ZFSet.pair_mem_prod] at inProd
  exact ZFSet.notMem_empty w inProd.2

/-- The constant function from `{∅}` to `{∅}`. -/
theorem singleton_pair_mem_funs :
    ({ZFSet.pair ∅ ∅} : ZFSet.{u}) ∈ ZFSet.funs {∅} {∅} := by
  rw [ZFSet.mem_funs]
  refine ⟨?_, ?_⟩
  · intro z member
    rw [ZFSet.mem_singleton.mp member, ZFSet.pair_mem_prod]
    exact ⟨ZFSet.mem_singleton.mpr rfl, ZFSet.mem_singleton.mpr rfl⟩
  · intro z member
    refine ⟨∅, ?_, ?_⟩
    · rw [ZFSet.mem_singleton.mp member]
      exact ZFSet.mem_singleton.mpr rfl
    · intro w inF
      rw [ZFSet.mem_singleton.mp member] at inF
      exact (ZFSet.pair_inj.mp (ZFSet.mem_singleton.mp inF)).2

/-- **Out of an inhabited set the codomain matters**: there is a function from
`{∅}` to `{∅}` and none from `{∅}` to `∅`. -/
theorem funs_singleton_ne : ZFSet.funs {∅} (∅ : ZFSet.{u}) ≠ ZFSet.funs {∅} {∅} := by
  intro equal
  have member := singleton_pair_mem_funs.{u}
  rw [← equal, funs_singleton_empty] at member
  exact ZFSet.notMem_empty _ member

/-- **The type face**: functions out of an empty type into any two types are
equivalent, each type having exactly one inhabitant. -/
def emptyFunctionsEquiv (α β : Sort*) : (Empty → α) ≃ (Empty → β) :=
  Equiv.ofUnique _ _

end Mettapedia.SetTheory.ZFSetEmptyFunctions
