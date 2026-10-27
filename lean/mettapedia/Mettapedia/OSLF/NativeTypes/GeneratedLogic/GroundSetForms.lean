import Mettapedia.OSLF.NativeTypes.GeneratedLogic.GroundSetReadings
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Search

/-!
# Canonical forms for ground set languages, read with either

A language's own semantics reads a set modulo its laws, so a rule may take a member from a presentation that writes
it twice and leave the other copy: it consumes or keeps each member it takes. The front door decides this reading
with canonical forms whose regions list each set's steps at presentations with some members written twice.

- **The domain** (`atomSet`): sets of atoms of the sort. Canonical forms write each member once, in order
  (`BagForms.sortBags`), and equivalent terms have the same one (`canonical`).
- **Presentations** (`setPresentations`): a set with some of its members written twice. A rule takes one copy of each
  atom it takes, so the atoms it keeps are the copied ones.
- **Coherence** (`coherent`): a step from any presentation of a canonical set is matched, with the same labels and up
  to canonical form, by a step listed at one of these presentations, the one that copies the members the step keeps.
- **For the front door** (`forms`). On the pool from `{A}` it proves that some run reaches `{B}` and refutes that
  every run does, as the language's semantics has it.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep
open Mettapedia.OSLF.MeTTaIL.CanonicalBags (arrange arrange_mem)

variable {relEnv : RelationEnv} {language : LanguageDef} {carrier : GrammarRule} {sort : String}

/-! ## The domain -/

variable (language sort) in
/-- Whether a term is an atom of the sort. -/
def isAtom : Pattern → Bool
  | .apply label [] =>
    language.terms.any fun rule => rule.label == label && rule.category == sort && rule.params.isEmpty
  | _ => false

variable (language sort) in
/-- **The domain**: sets of atoms of the sort. -/
def atomSet : Pattern → Bool
  | .collection .hashSet values none => values.all (isAtom language sort)
  | _ => false

theorem isAtom_iff {value : Pattern} :
    isAtom language sort value = true ↔ ∃ label, value = token label ∧ AtomOf language sort label := by
  match value with
  | .apply label [] => simp [isAtom, token, AtomOf, and_assoc]
  | .apply _ (_ :: _) => simp [isAtom, token]
  | .bvar _ | .fvar _ | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ | .collection _ _ _ => simp [isAtom, token]

theorem atomSet_iff {term : Pattern} :
    atomSet language sort term = true ↔ ∃ values, term = set values ∧ Atoms language sort values := by
  match term with
  | .collection .hashSet values none =>
    constructor
    · intro checked
      exact ⟨values, rfl, fun value member => isAtom_iff.mp (List.all_eq_true.mp checked value member)⟩
    · rintro ⟨other, same, atoms⟩
      simp only [set, Pattern.collection.injEq, true_and, and_true] at same
      subst same
      exact List.all_eq_true.mpr fun value member => isAtom_iff.mpr (atoms value member)
  | .collection .hashSet _ (some _) | .collection .hashBag _ _ | .collection .vec _ _ => simp [atomSet, set]
  | .bvar _ | .fvar _ | .apply _ _ | .lambda _ _ | .multiLambda _ _ _ | .subst _ _ => simp [atomSet, set]

theorem atomSet_sortBags (term : Pattern) :
    atomSet language sort (BagForms.sortBags term) = atomSet language sort term := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro canonical
    obtain ⟨values, same, atoms⟩ := atomSet_iff.mp canonical
    obtain ⟨presented, rfl, -, sameMembers⟩ := presentation_of_canonical (tokens_of_atoms atoms) same
    exact atomSet_iff.mpr ⟨presented, rfl, atoms.of_subset fun value member => (sameMembers value).mp member⟩
  · intro admitted
    obtain ⟨values, rfl, atoms⟩ := atomSet_iff.mp admitted
    rw [sortBags_set atoms]
    exact atomSet_iff.mpr ⟨_, rfl, atoms.of_subset fun value member => (arrange_mem value).mp member⟩

/-- **Canonical forms for a ground set language**: each member written once, in order; the domain is read off them. -/
theorem canonicalDetermined (lang : GroundSetLanguage language carrier sort) :
    CanonicalDetermined relEnv language BagForms.sortBags (atomSet language sort) where
  object admitted := by
    obtain ⟨values, rfl, atoms⟩ := atomSet_iff.mp admitted
    exact elements_object atoms.elements
  determined := atomSet_sortBags
  equivalent admitted := by
    obtain ⟨values, rfl, atoms⟩ := atomSet_iff.mp admitted
    exact equivalent_sortBags lang.setCarrier atoms
  same _ equivalent := sortBags_same lang equivalent
  closed _ := by
    rw [BagForms.sortBags_eq_canon]
    exact BagForms.canon_wellScoped _ 0

/-- **Canonical forms for a ground set language**: each member written once, in order. -/
theorem canonical (lang : GroundSetLanguage language carrier sort) :
    Canonical relEnv language BagForms.sortBags (atomSet language sort) :=
  (canonicalDetermined lang).canonical

/-! ## Presentations and coherence -/

/-- **The presentations of a set**: the set with some of its members written twice. -/
def setPresentations : Pattern → List Pattern
  | .collection .hashSet values none => values.sublists.map fun copies => .collection .hashSet (values ++ copies) none
  | other => [other]

theorem mem_setPresentations {values copies : List Pattern} (sub : copies.Sublist values) :
    set (values ++ copies) ∈ setPresentations (set values) := by
  simp only [set, setPresentations, List.mem_map, List.mem_sublists]
  exact ⟨copies, sub, rfl⟩

/-- **Coherence**: a step from any presentation of a canonical set of atoms is matched, with the same labels and up
to canonical form, by a step listed at the presentation that copies the members the step keeps. -/
theorem coherent (lang : GroundSetLanguage language carrier sort) (fuel : ℕ) :
    Coherent relEnv language fuel BagForms.sortBags (atomSet language sort) setPresentations := by
  intro state redex witness contractum _ admitted canonState complete before _ valid
  obtain ⟨values, rfl, atoms⟩ := atomSet_iff.mp admitted
  have tokens := tokens_of_atoms atoms
  have distinct := canonical_nodup atoms canonState
  have redexCanonical : BagForms.sortBags redex = set values := (sortBags_same lang before).symm.trans canonState
  obtain ⟨presented, rfl, presentedTokens, sameMembers⟩ := presentation_of_canonical tokens redexCanonical
  obtain ⟨index, rule, takes, gives, rest, residual, found, ground, counted, rfl, rfl⟩ := ground_step lang.rules valid
  have residualMem := either_residual_mem counted ground.distinct
  have present : ∀ name ∈ takes, token name ∈ values := fun name member => by
    have := counted (token name)
    have taken : 0 < (takes.map token).count (token name) := List.count_pos_iff.mpr (List.mem_map_of_mem member)
    exact (sameMembers _).mp (List.count_pos_iff.mp (by omega))
  let kept := (takes.filter fun name => 2 ≤ presented.count (token name)).map token
  let copies := values.filter (· ∈ kept)
  obtain ⟨copied, fired, copiedMem⟩ := fires_at_copies (relEnv := relEnv) atoms canonState found ground present
    (distinct.filter _) (copies := copies) fun value member => (List.mem_filter.mp member).1
  have shown := mem_setPresentations (copies := copies) List.filter_sublist
  refine ⟨(.rule index [(rest, set copied)] [], set (gives.map token ++ copied)),
    mem_listedAt.mpr ⟨_, shown, mem_stepsAt_of_enough (enoughAt_iff.mp complete _ shown) fired⟩,
    fun label => by cases label <;> rfl, ?_⟩
  apply sortBags_set_congr
  · intro value member
    rcases List.mem_append.mp member with given | remaining
    · obtain ⟨name, -, rfl⟩ := List.mem_map.mp given
      exact ⟨name, rfl⟩
    · exact tokens value ((copiedMem value).mp remaining).1
  · intro value member
    rcases List.mem_append.mp member with given | remaining
    · obtain ⟨name, -, rfl⟩ := List.mem_map.mp given
      exact ⟨name, rfl⟩
    · exact presentedTokens value ((residualMem value).mp remaining).1
  · intro value
    simp only [List.mem_append, copiedMem value, residualMem value, sameMembers value, copies, kept, List.mem_filter,
      decide_eq_true_eq]
    tauto

/-- **Canonical forms for a ground set language read with either**, for the front door. -/
def forms (lang : GroundSetLanguage language carrier sort) (fuel : ℕ) : CanonicalForms relEnv language fuel :=
  .ofCoherent (canonical lang) (coherent lang fuel)

/-! ## The pool at the front door -/

def poolSignature : Mettapedia.OSLF.Framework.FiniteModels.Signature := [.operation "A" 0, .operation "B" 0]

abbrev poolForms : CanonicalForms RelationEnv.empty pool 2 := forms pool_ground 2

theorem pool_reaches_answer :
    ask RelationEnv.empty poolSignature pool 2 (reaches onlyB) onlyA none 3 (some poolForms) =
      .proved (.exploration 3) := by
  decide +kernel

theorem pool_eventually_answer :
    ask RelationEnv.empty poolSignature pool 2 (eventually onlyB) onlyA none 3 (some poolForms) =
      .refuted (.canonicalRegion 3) := by
  decide +kernel

/-- **Without these canonical forms the front door leaves it open.** -/
theorem pool_eventually_open :
    ask RelationEnv.empty poolSignature pool 2 (eventually onlyB) onlyA none 3 = .unknown 3 := by
  decide +kernel

/-- **The front door decides the pool as the language's semantics has it**: some run from `{A}` reaches `{B}`, and
not every run does, as `either_verdicts` derives from the least fixed points. -/
theorem pool_verdicts :
    Either.sat Env.closed (reaches onlyB) onlyA ∧ ¬ Either.sat Env.closed (eventually onlyB) onlyA := by
  rw [show Either = referenceStructure RelationEnv.empty pool from eitherStructure_of_premises_nil _ _ pool_premises_nil]
  exact ⟨ask_proved pool_reaches_answer, ask_refuted pool_eventually_answer⟩

/-! ## Mixtures at the front door -/

def pairSignature : Mettapedia.OSLF.Framework.FiniteModels.Signature :=
  [.operation "A" 0, .operation "B" 0, .operation "C" 0]

abbrev pairForms : CanonicalForms RelationEnv.empty pairPool 2 := forms pairPool_ground 2

theorem pair_mixture_answer :
    ask RelationEnv.empty pairSignature pairPool 2 (.possibly .any (.is onlyAC)) bothAB none 2 (some pairForms) =
      .proved (.canonicalRegion 2) := by
  decide +kernel

theorem pair_no_return_answer :
    ask RelationEnv.empty pairSignature pairPool 2 (.possibly .any (.is bothAB)) bothAB none 2 (some pairForms) =
      .refuted (.canonicalRegion 2) := by
  decide +kernel

theorem pair_four_answer :
    ask RelationEnv.empty pairSignature pairPool 2 (.atLeast 4 .forward .any .top) bothAB none 2 (some pairForms) =
      .proved (.canonicalRegion 2) := by
  decide +kernel

theorem pair_not_five_answer :
    ask RelationEnv.empty pairSignature pairPool 2 (.atLeast 5 .forward .any .top) bothAB none 2 (some pairForms) =
      .refuted (.canonicalRegion 2) := by
  decide +kernel

/-- **Without these canonical forms the front door does not see the mixture.** -/
theorem pair_mixture_open :
    ask RelationEnv.empty pairSignature pairPool 2 (.possibly .any (.is onlyAC)) bothAB none 2 = .unknown 2 := by
  decide +kernel

/-- **Under either, `{A, B}` has four successors**: the rule consumes or keeps each of `A` and `B`, giving `{C}`,
`{A, C}`, `{B, C}` and `{A, B, C}`. It steps to `{A, C}` and not back to `{A, B}`. -/
theorem pair_verdicts :
    (referenceStructure RelationEnv.empty pairPool).sat Env.closed (.possibly .any (.is onlyAC)) bothAB ∧
      ¬ (referenceStructure RelationEnv.empty pairPool).sat Env.closed (.possibly .any (.is bothAB)) bothAB ∧
      (referenceStructure RelationEnv.empty pairPool).sat Env.closed (.atLeast 4 .forward .any .top) bothAB ∧
      ¬ (referenceStructure RelationEnv.empty pairPool).sat Env.closed (.atLeast 5 .forward .any .top) bothAB :=
  ⟨ask_proved pair_mixture_answer, ask_refuted pair_no_return_answer, ask_proved pair_four_answer,
    ask_refuted pair_not_five_answer⟩

theorem pair_consume_answers :
    decideReading RelationEnv.empty pairPool 2 id BagForms.sortBags (.atLeast 1 .forward .any .top) bothAB 2 =
        some true ∧
      decideReading RelationEnv.empty pairPool 2 id BagForms.sortBags (.atLeast 2 .forward .any .top) bothAB 2 =
        some false := by
  decide +kernel

theorem pair_keep_answers :
    decideReading RelationEnv.empty pairPool 2 (saturate (setWidth pairPool + 1)) BagForms.sortBags
        (.atLeast 1 .forward .any .top) bothAB 2 = some true ∧
      decideReading RelationEnv.empty pairPool 2 (saturate (setWidth pairPool + 1)) BagForms.sortBags
        (.atLeast 2 .forward .any .top) bothAB 2 = some false := by
  decide +kernel

/-- **Under consume and under keep, `{A, B}` has one successor each**: consume takes both atoms, keep takes neither. -/
theorem pair_one_successor :
    (consumeStructure RelationEnv.empty pairPool).sat Env.closed (.atLeast 1 .forward .any .top) bothAB ∧
      ¬ (consumeStructure RelationEnv.empty pairPool).sat Env.closed (.atLeast 2 .forward .any .top) bothAB ∧
      (keepStructure RelationEnv.empty pairPool).sat Env.closed (.atLeast 1 .forward .any .top) bothAB ∧
      ¬ (keepStructure RelationEnv.empty pairPool).sat Env.closed (.atLeast 2 .forward .any .top) bothAB := by
  have consumeOne := decideReading_sound (by decide) pair_consume_answers.1
  have consumeTwo := decideReading_sound (by decide) pair_consume_answers.2
  have keepOne := decideReading_sound (by decide) pair_keep_answers.1
  have keepTwo := decideReading_sound (by decide) pair_keep_answers.2
  rw [bothAB_canonical] at consumeOne consumeTwo keepOne keepTwo
  exact ⟨consumeOne.mp rfl, fun holds => Bool.false_ne_true (consumeTwo.mpr holds), keepOne.mp rfl,
    fun holds => Bool.false_ne_true (keepTwo.mpr holds)⟩

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
