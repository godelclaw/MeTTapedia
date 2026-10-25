import Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure

/-!
# Tarski universes for the well-founded material interpretation

The local Tarski property includes subset closure, an internal bound on all
subsets of each member, and the cardinality alternative for every subset of
the universe. These are the three clauses used in Tarski's Axiom A.

Inaccessible rank segments satisfy all three clauses as well as the existing
Grothendieck closure predicate. Cofinal inaccessible cardinals therefore
supply both sorts of enclosure for the material HOL model. This is a common
sufficient construction, not an equivalence of axiom packages or a necessity
claim for inaccessible cardinals.

Reference: Brown and Pąk, "A Tale of Two Set Theories", Section 2 (2019),
https://arxiv.org/abs/1907.08368.
-/

set_option autoImplicit false
namespace Mettapedia.Logic.HOL.Embedding.ZFSetTarskiUniverses
open ZFSetUniverseClosure
open scoped ZFSet Cardinal
universe u

/-- The exact local clauses of Tarski's Axiom A, with equipotence expressed
by an equivalence of the actual member types. -/
structure IsTarskiUniverse (U : ZFSet.{u}) : Prop where
  subset_mem : ∀ {a b : ZFSet.{u}}, a ∈ U → b ⊆ a → b ∈ U
  subsets_bounded : ∀ {a : ZFSet.{u}}, a ∈ U →
    ∃ b ∈ U, ∀ c : ZFSet.{u}, c ⊆ a → c ∈ b
  subset_alternative : ∀ {a : ZFSet.{u}}, a ⊆ U → Nonempty (a ≃ U) ∨ a ∈ U

/-- Regularity bounds the ranks of a small subset of an inaccessible stage. -/
theorem mem_of_subset_of_card_lt {κ : Cardinal.{u}} (inaccessible : κ.IsInaccessible)
    {a : ZFSet.{u}} (included : a ⊆ V_ κ.ord) (small : a.card < κ) : a ∈ V_ κ.ord := by
  let values : Shrink a → ZFSet.{u} := fun i => ((equivShrink a).symm i).1
  have range_eq : ZFSet.range values = a := by
    apply ZFSet.ext
    intro value
    rw [ZFSet.mem_range]
    constructor
    · rintro ⟨i, rfl⟩
      exact ((equivShrink a).symm i).2
    · intro present
      exact ⟨equivShrink a ⟨value, present⟩, by simp [values]⟩
  have ranks : (ZFSet.range values).rank < κ.ord := by
    rw [ZFSet.rank_range]
    apply Ordinal.iSup_lt_of_lt_cof
    · rw [inaccessible.isRegular.cof_ord]
      exact small
    · intro i
      exact (Cardinal.isSuccLimit_ord inaccessible.aleph0_lt.le).succ_lt
        (ZFSet.mem_vonNeumann.mp (included ((equivShrink a).symm i).2))
  exact ZFSet.mem_vonNeumann.mpr (range_eq ▸ ranks)

/-- A proper-size subset is an element; the only remaining cardinality is
that of the whole inaccessible rank segment. -/
theorem inaccessible_tarski {κ : Cardinal.{u}} (inaccessible : κ.IsInaccessible) :
    IsTarskiUniverse (V_ κ.ord) where
  subset_mem := (inaccessible_closed inaccessible).subset_mem
  subsets_bounded ha :=
    ⟨ZFSet.powerset _, (inaccessible_closed inaccessible).power_mem ha,
      fun _ subset => ZFSet.mem_powerset.mpr subset⟩
  subset_alternative := by
    intro a included
    by_cases small : a.card < κ
    · exact .inr (mem_of_subset_of_card_lt inaccessible included small)
    · have card_eq : a.card = (V_ κ.ord).card := by
        apply le_antisymm (ZFSet.card_mono included)
        rw [ZFSet.card_vonNeumann, inaccessible.preBeth_ord]
        exact le_of_not_gt small
      apply Or.inl
      apply Cardinal.eq.mp
      rw [ZFSet.cardinalMk_coe_sort, ZFSet.cardinalMk_coe_sort, card_eq]

/-- The same rank segment supplies both independently stated universe
properties. The source of existence is the explicit cardinal assumption. -/
theorem exists_common_enclosure (cofinal : CofinalInaccessibles.{u}) (seed : ZFSet.{u}) :
    ∃ U : ZFSet.{u}, seed ∈ U ∧ Closed U ∧ IsTarskiUniverse U := by
  obtain ⟨κ, inaccessible, above⟩ := cofinal seed.rank
  exact ⟨V_ κ.ord, ZFSet.mem_vonNeumann.mpr above,
    inaccessible_closed inaccessible, inaccessible_tarski inaccessible⟩

/-- Containing a selected seed is not the Tarski universe property. -/
theorem singleton_seed_not_tarski :
    (∅ : ZFSet.{u}) ∈ ({∅} : ZFSet.{u}) ∧ ¬ IsTarskiUniverse ({∅} : ZFSet.{u}) := by
  refine ⟨ZFSet.mem_singleton.mpr rfl, ?_⟩
  intro enclosure
  obtain ⟨bound, present, bounds⟩ := enclosure.subsets_bounded (ZFSet.mem_singleton.mpr rfl)
  have empty : bound = ∅ := ZFSet.mem_singleton.mp present
  exact ZFSet.notMem_empty _ (empty ▸ bounds ∅ (by intro _ impossible; exact impossible))

end Mettapedia.Logic.HOL.Embedding.ZFSetTarskiUniverses
