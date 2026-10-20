import Mettapedia.GSLT.OpenEnded.IdealCompletion
import Mettapedia.GSLT.OpenEnded.SufficientBubbles
import Mathlib.Data.Set.Finite.Basic

/-!
# Realizing the open-ended top as a rule table

A checker for a presented calculus consults its rules only through a partial
lookup from rule identifiers to rule schemas. A finitely presented profile
has a lookup with finite support. Extension of profiles is extension of
lookups (`Table.le_def`), which is exactly how strict certificate-GSLT arrows
retain rules.

The ideal completion of finite tables is constructed in `IdealCompletion`.
This file shows that its points are usable source theories, not formal
ideals: they are exactly the partial rule tables, possibly infinite
(`realizeIso`). Derivability over a realized table is defined natively, by the
same rule-application relation used at every finite stage, and a derivation
over the realized top lives in one finite stage (`derives_realize_iff`). So a
finite proof never depends on the size of the ambient theory.

Bubbles of a top are its restrictions to sets of rule identifiers
(`restrictTo`). Sufficiency for a judgment is monotone, so the general
deletion-core criterion applies (`exists_least_bubble_iff_core`), and every
minimal sufficient bubble, in particular the least one when it exists, is
finite (`minimal_sufficient_finite`, `least_bubble_finite`). Least sufficient
bubbles are compact sub-objects of the top.

Two finite tables that disagree on one identifier have no common extension,
so, for instance, the finite tables with one identifier and two possible
schemas have no strongest top (`no_greatest_table_top`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OpenEnded.RuleTables

open Order Set
open Mettapedia.GSLT.OpenEnded.IdealCompletion
open Mettapedia.GSLT.OpenEnded.SufficientBubbles

universe u v w

/-- A partial lookup from rule identifiers to rule schemas. -/
@[ext] structure Table (Id : Type u) (Rule : Type v) where
  lookup : Id → Option Rule

namespace Table

variable {Id : Type u} {Rule : Type v}

instance : PartialOrder (Table Id Rule) where
  le first second := ∀ i r, first.lookup i = some r → second.lookup i = some r
  le_refl _ _ _ found := found
  le_trans _ _ _ firstSecond secondThird i r found := secondThird i r (firstSecond i r found)
  le_antisymm first second firstSecond secondFirst := by
    ext : 1
    funext i
    cases inFirst : first.lookup i with
    | none =>
        cases inSecond : second.lookup i with
        | none => rfl
        | some r =>
            have found := secondFirst i r inSecond
            rw [inFirst] at found
            cases found
    | some r => exact (firstSecond i r inFirst).symm

theorem le_def {first second : Table Id Rule} :
    first ≤ second ↔ ∀ i r, first.lookup i = some r → second.lookup i = some r :=
  Iff.rfl

/-- The identifiers a table defines. -/
def support (table : Table Id Rule) : Set Id :=
  {i | (table.lookup i).isSome}

theorem support_mono {first second : Table Id Rule} (le : first ≤ second) :
    first.support ⊆ second.support := by
  intro i member
  change (first.lookup i).isSome at member
  change (second.lookup i).isSome
  obtain ⟨r, found⟩ := Option.isSome_iff_exists.mp member
  rw [le i r found]
  rfl

/-- The table defining nothing. -/
def empty : Table Id Rule := ⟨fun _ => none⟩

theorem empty_le (table : Table Id Rule) : empty ≤ table := by
  intro i r found
  cases found

open Classical in
/-- Restrict a table to a set of identifiers. -/
noncomputable def restrictTo (table : Table Id Rule) (ids : Set Id) : Table Id Rule :=
  ⟨fun i => if i ∈ ids then table.lookup i else none⟩

theorem restrictTo_lookup_of_mem (table : Table Id Rule) {ids : Set Id} {i : Id}
    (member : i ∈ ids) : (table.restrictTo ids).lookup i = table.lookup i := by
  classical
  simp [restrictTo, member]

theorem restrictTo_lookup_of_not_mem (table : Table Id Rule) {ids : Set Id} {i : Id}
    (absent : i ∉ ids) : (table.restrictTo ids).lookup i = none := by
  classical
  simp [restrictTo, absent]

theorem restrictTo_le (table : Table Id Rule) (ids : Set Id) : table.restrictTo ids ≤ table := by
  intro i r found
  by_cases member : i ∈ ids
  · rwa [restrictTo_lookup_of_mem table member] at found
  · rw [restrictTo_lookup_of_not_mem table member] at found
    cases found

theorem restrictTo_mono (table : Table Id Rule) {ids ids' : Set Id} (included : ids ⊆ ids') :
    table.restrictTo ids ≤ table.restrictTo ids' := by
  intro i r found
  by_cases member : i ∈ ids
  · rw [restrictTo_lookup_of_mem table member] at found
    rw [restrictTo_lookup_of_mem table (included member)]
    exact found
  · rw [restrictTo_lookup_of_not_mem table member] at found
    cases found

theorem restrictTo_monotone_table {first second : Table Id Rule} (le : first ≤ second)
    (ids : Set Id) : first.restrictTo ids ≤ second.restrictTo ids := by
  intro i r found
  by_cases member : i ∈ ids
  · rw [restrictTo_lookup_of_mem first member] at found
    rw [restrictTo_lookup_of_mem second member]
    exact le i r found
  · rw [restrictTo_lookup_of_not_mem first member] at found
    cases found

theorem support_restrictTo_subset (table : Table Id Rule) (ids : Set Id) :
    (table.restrictTo ids).support ⊆ ids := by
  intro i member
  by_contra absent
  change ((table.restrictTo ids).lookup i).isSome at member
  rw [restrictTo_lookup_of_not_mem table absent] at member
  cases member

/-- A sub-table is the restriction of the larger table to its own support. -/
theorem restrictTo_support_of_le {small large : Table Id Rule} (le : small ≤ large) :
    large.restrictTo small.support = small := by
  ext : 1
  funext i
  by_cases member : i ∈ small.support
  · rw [restrictTo_lookup_of_mem large member]
    obtain ⟨r, found⟩ := Option.isSome_iff_exists.mp member
    rw [found, le i r found]
  · rw [restrictTo_lookup_of_not_mem large member]
    change ¬ (small.lookup i).isSome at member
    cases found : small.lookup i with
    | none => rfl
    | some r => rw [found] at member; exact absurd rfl member

end Table

open Table

variable {Id : Type u} {Rule : Type v}

/-- Finitely presented tables: finite support. -/
abbrev FinTable (Id : Type u) (Rule : Type v) :=
  {table : Table Id Rule // table.support.Finite}

/-- The finite restriction of a table to a finite set of identifiers. -/
noncomputable def finRestrict (table : Table Id Rule) {ids : Set Id} (finite : ids.Finite) :
    FinTable Id Rule :=
  ⟨table.restrictTo ids, finite.subset (support_restrictTo_subset table ids)⟩

/-! ## The ideal of finite stages of a table, and the table of an ideal -/

/-- The finite stages of a table. -/
noncomputable def stages (table : Table Id Rule) : Ideal (FinTable Id Rule) where
  carrier := {stage | stage.1 ≤ table}
  lower' := by
    intro first second below member
    exact le_trans (show second.1 ≤ first.1 from below) (show first.1 ≤ table from member)
  nonempty' := ⟨⟨empty, by
    have : (empty : Table Id Rule).support = ∅ := by
      ext i
      simp [support, empty]
    rw [this]
    exact finite_empty⟩, empty_le table⟩
  directed' := by
    intro first memberFirst second memberSecond
    have finite : (first.1.support ∪ second.1.support).Finite := first.2.union second.2
    refine ⟨finRestrict table finite, restrictTo_le table _, ?_, ?_⟩
    · intro i r found
      have inSupport : i ∈ first.1.support ∪ second.1.support :=
        Or.inl (by change (first.1.lookup i).isSome; rw [found]; rfl)
      change (table.restrictTo _).lookup i = some r
      rw [restrictTo_lookup_of_mem table inSupport]
      exact memberFirst i r found
    · intro i r found
      have inSupport : i ∈ first.1.support ∪ second.1.support :=
        Or.inr (by change (second.1.lookup i).isSome; rw [found]; rfl)
      change (table.restrictTo _).lookup i = some r
      rw [restrictTo_lookup_of_mem table inSupport]
      exact memberSecond i r found

theorem mem_stages {table : Table Id Rule} {stage : FinTable Id Rule} :
    stage ∈ stages table ↔ stage.1 ≤ table :=
  Iff.rfl

/-- Two stages of one ideal never disagree on an identifier. -/
theorem stages_agree {I : Ideal (FinTable Id Rule)} {first second : FinTable Id Rule}
    (memberFirst : first ∈ I) (memberSecond : second ∈ I) {i : Id} {r r' : Rule}
    (foundFirst : first.1.lookup i = some r) (foundSecond : second.1.lookup i = some r') :
    r = r' := by
  obtain ⟨upper, _, firstUpper, secondUpper⟩ := I.directed first memberFirst second memberSecond
  have one := firstUpper i r foundFirst
  have two := secondUpper i r' foundSecond
  rw [one] at two
  exact Option.some.inj two

open Classical in
/-- The table realized by a compatible growing family of finite stages. -/
noncomputable def realize (I : Ideal (FinTable Id Rule)) : Table Id Rule :=
  ⟨fun i => if found : ∃ stage ∈ I, (stage.1.lookup i).isSome then
    (Classical.choose found).1.lookup i else none⟩

theorem realize_lookup_of_mem {I : Ideal (FinTable Id Rule)} {stage : FinTable Id Rule}
    (member : stage ∈ I) {i : Id} {r : Rule} (found : stage.1.lookup i = some r) :
    (realize I).lookup i = some r := by
  classical
  have witness : ∃ stage ∈ I, (stage.1.lookup i).isSome :=
    ⟨stage, member, by rw [found]; rfl⟩
  simp only [realize, dif_pos witness]
  obtain ⟨chosenMember, chosenSome⟩ := Classical.choose_spec witness
  obtain ⟨r', chosenFound⟩ := Option.isSome_iff_exists.mp chosenSome
  rw [chosenFound, stages_agree chosenMember member chosenFound found]

theorem realize_lookup_eq_some {I : Ideal (FinTable Id Rule)} {i : Id} {r : Rule}
    (found : (realize I).lookup i = some r) : ∃ stage ∈ I, stage.1.lookup i = some r := by
  classical
  by_cases witness : ∃ stage ∈ I, (stage.1.lookup i).isSome
  · simp only [realize, dif_pos witness] at found
    exact ⟨_, (Classical.choose_spec witness).1, found⟩
  · simp only [realize, dif_neg witness] at found
    cases found

theorem stage_le_realize {I : Ideal (FinTable Id Rule)} {stage : FinTable Id Rule}
    (member : stage ∈ I) : stage.1 ≤ realize I :=
  fun _ _ found => realize_lookup_of_mem member found

/-- Every finite restriction of the realized table is covered by one stage. -/
theorem exists_stage_above_restrict (I : Ideal (FinTable Id Rule)) {ids : Set Id}
    (finite : ids.Finite) : ∃ stage ∈ I, (realize I).restrictTo ids ≤ stage.1 := by
  refine Set.Finite.induction_on
    (motive := fun ids _ => ∃ stage ∈ I, (realize I).restrictTo ids ≤ stage.1) ids finite ?_ ?_
  · obtain ⟨stage, member⟩ := I.nonempty
    refine ⟨stage, member, fun i r found => ?_⟩
    rw [restrictTo_lookup_of_not_mem _ (notMem_empty i)] at found
    cases found
  · intro a rest _ _ ih
    obtain ⟨stage, member, below⟩ := ih
    cases definedA : (realize I).lookup a with
    | none =>
        refine ⟨stage, member, fun i r found => ?_⟩
        by_cases same : i = a
        · subst same
          rw [restrictTo_lookup_of_mem _ (mem_insert i rest), definedA] at found
          cases found
        · by_cases inRest : i ∈ rest
          · apply below i r
            rw [restrictTo_lookup_of_mem _ inRest]
            rwa [restrictTo_lookup_of_mem _ (mem_insert_of_mem a inRest)] at found
          · rw [restrictTo_lookup_of_not_mem _ (by
              simp only [mem_insert_iff, not_or]; exact ⟨same, inRest⟩)] at found
            cases found
    | some ra =>
        obtain ⟨stageA, memberA, foundA⟩ := realize_lookup_eq_some definedA
        obtain ⟨upper, memberUpper, stageUpper, stageAUpper⟩ :=
          I.directed stage member stageA memberA
        refine ⟨upper, memberUpper, fun i r found => ?_⟩
        by_cases same : i = a
        · subst same
          rw [restrictTo_lookup_of_mem _ (mem_insert i rest), definedA] at found
          cases found
          exact stageAUpper i ra foundA
        · by_cases inRest : i ∈ rest
          · apply stageUpper i r
            apply below i r
            rw [restrictTo_lookup_of_mem _ inRest]
            rwa [restrictTo_lookup_of_mem _ (mem_insert_of_mem a inRest)] at found
          · rw [restrictTo_lookup_of_not_mem _ (by
              simp only [mem_insert_iff, not_or]; exact ⟨same, inRest⟩)] at found
            cases found

/-- A finite table below the realized table is a stage of the ideal. -/
theorem mem_of_le_realize {I : Ideal (FinTable Id Rule)} {stage : FinTable Id Rule}
    (le : stage.1 ≤ realize I) : stage ∈ I := by
  obtain ⟨upper, memberUpper, below⟩ := exists_stage_above_restrict I stage.2
  have same := restrictTo_support_of_le le
  rw [same] at below
  exact I.lower below memberUpper

theorem realize_stages (table : Table Id Rule) : realize (stages table) = table := by
  apply le_antisymm
  · intro i r found
    obtain ⟨stage, member, foundStage⟩ := realize_lookup_eq_some found
    exact member i r foundStage
  · intro i r found
    have finite : ({i} : Set Id).Finite := finite_singleton i
    apply realize_lookup_of_mem (stage := finRestrict table finite) (restrictTo_le table _)
    change (table.restrictTo {i}).lookup i = some r
    rw [restrictTo_lookup_of_mem table (mem_singleton i)]
    exact found

theorem stages_realize (I : Ideal (FinTable Id Rule)) : stages (realize I) = I := by
  ext stage
  exact ⟨fun le => mem_of_le_realize le, fun member => stage_le_realize member⟩

/-- **The ideal completion of finite rule tables is realized by arbitrary
partial rule tables.** -/
noncomputable def realizeIso : Ideal (FinTable Id Rule) ≃o Table Id Rule where
  toFun := realize
  invFun := stages
  left_inv := stages_realize
  right_inv := realize_stages
  map_rel_iff' := by
    intro I K
    constructor
    · intro le stage member
      exact mem_of_le_realize (le_trans (stage_le_realize member) le)
    · intro le i r found
      obtain ⟨stage, member, foundStage⟩ := realize_lookup_eq_some found
      exact realize_lookup_of_mem (le member) foundStage

/-- A finite table is realized by its principal ideal. -/
theorem realize_principal (stage : FinTable Id Rule) :
    realize (Ideal.principal stage) = stage.1 := by
  apply le_antisymm
  · intro i r found
    obtain ⟨other, member, foundOther⟩ := realize_lookup_eq_some found
    exact (Ideal.mem_principal.mp member) i r foundOther
  · exact stage_le_realize Ideal.mem_principal_self

/-! ## Derivations over a table -/

section Derivations

variable {J : Type w} (Instance : Rule → List J → J → Prop)

/-- Derivability over a table: a rule found by lookup, applied to an instance
whose premises are derivable. The instance relation is fixed by the calculus
and does not depend on the table. -/
inductive Derives (table : Table Id Rule) : J → Prop
  | byRule {j : J} (i : Id) (r : Rule) (premises : List J) :
      table.lookup i = some r → Instance r premises j →
      (∀ p ∈ premises, Derives table p) → Derives table j

variable {Instance}

theorem derives_mono {small large : Table Id Rule} (le : small ≤ large) {j : J}
    (derivation : Derives Instance small j) : Derives Instance large j := by
  induction derivation with
  | byRule i r premises found instance_ _ ih =>
      exact .byRule i r premises (le i r found) instance_ ih

private theorem exists_common_support {table : Table Id Rule} :
    ∀ premises : List J,
      (∀ p ∈ premises, ∃ ids : Set Id, ids.Finite ∧ Derives Instance (table.restrictTo ids) p) →
      ∃ ids : Set Id, ids.Finite ∧ ∀ p ∈ premises, Derives Instance (table.restrictTo ids) p
  | [], _ => ⟨∅, finite_empty, fun _ member => by cases member⟩
  | head :: tail, supported => by
      obtain ⟨headIds, headFinite, headDerives⟩ := supported head (List.mem_cons_self ..)
      obtain ⟨tailIds, tailFinite, tailDerives⟩ :=
        exists_common_support tail (fun p member => supported p (List.mem_cons_of_mem _ member))
      refine ⟨headIds ∪ tailIds, headFinite.union tailFinite, fun p member => ?_⟩
      rcases List.mem_cons.mp member with rfl | inTail
      · exact derives_mono (restrictTo_mono table subset_union_left) headDerives
      · exact derives_mono (restrictTo_mono table subset_union_right) (tailDerives p inTail)

/-- **Finite support.** Every derivation over a table is a derivation over its
restriction to finitely many rule identifiers. -/
theorem exists_finite_support {table : Table Id Rule} {j : J}
    (derivation : Derives Instance table j) :
    ∃ ids : Set Id, ids.Finite ∧ Derives Instance (table.restrictTo ids) j := by
  induction derivation with
  | byRule i r premises found instance_ _ ih =>
      obtain ⟨ids, finite, premisesDerive⟩ := exists_common_support premises ih
      refine ⟨insert i ids, finite.insert i, .byRule i r premises ?_ instance_ fun p member =>
        derives_mono (restrictTo_mono table (subset_insert i ids)) (premisesDerive p member)⟩
      rw [restrictTo_lookup_of_mem table (mem_insert i ids)]
      exact found

/-- **Compactness at the realized top.** A judgment is derivable over the table
realized by a growing family exactly when it is derivable at one finite stage
of the family. -/
theorem derives_realize_iff (I : Ideal (FinTable Id Rule)) (j : J) :
    Derives Instance (realize I) j ↔ ∃ stage ∈ I, Derives Instance stage.1 j := by
  constructor
  · intro derivation
    obtain ⟨ids, finite, restricted⟩ := exists_finite_support derivation
    exact ⟨finRestrict (realize I) finite, mem_of_le_realize (restrictTo_le _ _), restricted⟩
  · rintro ⟨stage, member, derivation⟩
    exact derives_mono (stage_le_realize member) derivation

/-! ## Bubbles of a top -/

/-- A set of rule identifiers is sufficient for a judgment when the
restriction of the top to it still derives the judgment. -/
def Sufficient (table : Table Id Rule) (j : J) (ids : Set Id) : Prop :=
  Derives Instance (table.restrictTo ids) j

theorem sufficient_upClosed (table : Table Id Rule) (j : J) :
    UpClosed (Sufficient (Instance := Instance) table j) :=
  fun _ _ included derivation => derives_mono (restrictTo_mono table included) derivation

/-- **The least sufficient bubble of a top exists exactly when its deletion
core is sufficient.** -/
theorem exists_least_bubble_iff_core (table : Table Id Rule) (j : J) :
    (∃ least, IsLeast {ids | Sufficient (Instance := Instance) table j ids} least) ↔
      Sufficient (Instance := Instance) table j (core (Sufficient (Instance := Instance) table j)) :=
  exists_least_iff_core_sufficient (sufficient_upClosed table j)

theorem restrictTo_restrictTo_le (table : Table Id Rule) (outer inner : Set Id) :
    (table.restrictTo outer).restrictTo inner ≤ table.restrictTo inner :=
  restrictTo_monotone_table (restrictTo_le table outer) inner

/-- **The least sufficient bubble, when it exists, is finite.** -/
theorem least_bubble_finite {table : Table Id Rule} {j : J} {least : Set Id}
    (isLeast : IsLeast {ids | Sufficient (Instance := Instance) table j ids} least) :
    least.Finite := by
  obtain ⟨ids, finite, restricted⟩ := exists_finite_support isLeast.1
  exact finite.subset (isLeast.2 (derives_mono (restrictTo_restrictTo_le table least ids) restricted))

/-- **Every minimal sufficient sub-table of a top is finite.** -/
theorem minimal_sufficient_finite {table bubble : Table Id Rule} {j : J}
    (minimal : Minimal (fun candidate => candidate ≤ table ∧ Derives Instance candidate j) bubble) :
    bubble.support.Finite := by
  obtain ⟨⟨_, derivation⟩, smallest⟩ := minimal
  obtain ⟨ids, finite, restricted⟩ := exists_finite_support derivation
  have within : bubble.restrictTo ids ≤ table := le_trans (restrictTo_le bubble ids) ‹bubble ≤ table›
  have back : bubble ≤ bubble.restrictTo ids := smallest ⟨within, restricted⟩ (restrictTo_le bubble ids)
  exact finite.subset ((support_mono back).trans (support_restrictTo_subset bubble ids))

end Derivations

/-! ## Incompatible finite profiles have no strongest top -/

/-- One identifier, two schemas. -/
def choiceTrue : FinTable Unit Bool := ⟨⟨fun _ => some true⟩, toFinite _⟩
def choiceFalse : FinTable Unit Bool := ⟨⟨fun _ => some false⟩, toFinite _⟩

theorem choices_incompatible (upper : FinTable Unit Bool) :
    ¬ (choiceTrue ≤ upper ∧ choiceFalse ≤ upper) := by
  rintro ⟨first, second⟩
  have one : upper.1.lookup () = some true := first () true rfl
  have two : upper.1.lookup () = some false := second () false rfl
  rw [one] at two
  cases two

/-- **The finite rule tables with one identifier and two schemas have no
strongest top.** -/
theorem no_greatest_table_top :
    ¬ ∃ top : Ideal (FinTable Unit Bool), ∀ I : Ideal (FinTable Unit Bool), I ≤ top :=
  no_greatest_of_incompatible choices_incompatible

#print axioms realizeIso
#print axioms realize_principal
#print axioms exists_finite_support
#print axioms derives_realize_iff
#print axioms exists_least_bubble_iff_core
#print axioms least_bubble_finite
#print axioms minimal_sufficient_finite
#print axioms no_greatest_table_top

end Mettapedia.GSLT.OpenEnded.RuleTables
