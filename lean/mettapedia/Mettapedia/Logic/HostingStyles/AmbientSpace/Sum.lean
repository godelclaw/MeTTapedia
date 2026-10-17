import Mettapedia.Logic.HostingStyles.AmbientSpace.Contexts
import Mettapedia.Logic.HostingStyles.AmbientSpace.SumOfTheories

/-!
# The family as one theory: the members summed over their spaces

Each member of the family hosts the theories of its own table.  The members
are summed over the spaces (`ambientSum`): one theory, whose interfaces are
the pairs of a space and an interface of the presentation.  The space is in
the interface, and in no term.

* **The one sentence, with contexts** (`ambientSum_hostOf_scopedFirstOrderTabular`).
  Under every reading in which the holes of atoms are free, the sum is a
  host, with all contexts, of the theories given by a table of rules without
  binder whose right sides mention only variables of their left sides, on the
  terms with free variables below a width, for every table and every width
  (`ScopedFirstOrderTabular`).
* **On terms** it is a host of the class that the candidate with a run hosts
  (`ambientSum_hostOf_firstOrderTabular`), under every reading.
* Each member is hosted by the sum, and the sum adds no context to a member
  (`member_hostedBy_ambientSum`, `member_exhausted_by_ambientSum`).
* **A term of the sum sits in one space**: there is no context from an
  interface at one space to an interface at another
  (`ambientSum_isEmpty_context_of_ne`).  Two parts in two spaces are no term
  of the sum.
* With the contexts of the members as they are, the sum has a linear size and
  receives no map from these theories (`linearSum_isEmpty_contextMap_scoped`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientSpace

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti
  (Theory RuleTable rewritingTheory TermContext withChoice withChoice_empty_tabular choiceTable
    empty_tabular)
open Mettapedia.GSLT.Dedukti.ConfluenceExamples (freeRule)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.ContextReadings

/-! ## The sum -/

/-- The readings of the members in which the interfaces of a class may be
used any number of times, as a family indexed by the spaces. -/
abbrev memberReadings (declared : Contexts.Interface → Prop) : SpaceTerm → ContextTheory.{0} :=
  fun space => (ambientTheory space).regionReading declared

/-- **The family as one theory**: the sum, over the spaces, of the readings
of the members in which the interfaces of a class may be used any number of
times.  An interface of the sum is a space and an interface of the
presentation. -/
def ambientSum (declared : Contexts.Interface → Prop) : ContextTheory.{0} :=
  ContextTheory.sum (memberReadings declared)

variable {declared : Contexts.Interface → Prop}

/-- **An interface of the sum carries its space.** -/
theorem ambientSum_interface :
    (ambientSum declared).Interface = (Σ _ : SpaceTerm, Contexts.Interface) :=
  rfl

/-- The terms of the sum at a space are the terms of the presentation: the
space is in no term. -/
theorem ambientSum_term (space : SpaceTerm) (interface : Contexts.Interface) :
    (ambientSum declared).Term ⟨space, interface⟩ = Contexts.Term ambient interface :=
  rfl

/-- **The steps of the sum at a space are those of the member at that
space.** -/
theorem ambientSum_rewrites_iff (space : SpaceTerm) {interface : Contexts.Interface}
    (term next : Contexts.Term ambient interface) :
    (ambientSum declared).rewrites (interface := ⟨space, interface⟩) term next ↔
      TermStep (ambientEvaluator space.1) ambient term next :=
  Iff.rfl

/-- Each member is hosted by the sum. -/
theorem member_hostedBy_ambientSum (space : SpaceTerm) :
    HostedBy ((ambientTheory space).regionReading declared) (ambientSum declared) :=
  ⟨ContextTheory.inject (memberReadings declared) space,
    ContextTheory.inject_hosting (memberReadings declared) space⟩

/-- **The sum adds no context to a member.** -/
theorem member_exhausted_by_ambientSum (space : SpaceTerm) :
    HostsExhaustively (ambientSum declared) ((ambientTheory space).regionReading declared) :=
  ⟨ContextTheory.inject (memberReadings declared) space,
    ContextTheory.inject_hosting (memberReadings declared) space,
    ContextTheory.inject_exhausting (memberReadings declared) space⟩

/-- What a member hosts, the sum hosts. -/
theorem hostedBy_ambientSum {source : ContextTheory.{0}} (space : SpaceTerm)
    (hosted : HostedBy source ((ambientTheory space).regionReading declared)) :
    HostedBy source (ambientSum declared) :=
  HostedBy.trans hosted (member_hostedBy_ambientSum space)

/-- **A term of the sum sits in one space**: no context of the sum goes from
an interface at one space to an interface at another. -/
theorem ambientSum_isEmpty_context_of_ne {first second : SpaceTerm} (apart : first ≠ second)
    (source target : Contexts.Interface) :
    IsEmpty ((ambientSum declared).Context
      (fun _ : Unit => (⟨first, source⟩ : (ambientSum declared).Interface)) ⟨second, target⟩) :=
  ContextTheory.sum_isEmpty_context_of_ne (memberReadings declared) apart source target

/-- **Positive**: at the space of the two rules of choice the atom of
`choose heads tails` has a transition to the atom of `heads`; **negative**: at
the empty space it has none.  One term, two interfaces of the sum. -/
theorem ambientSum_coin :
    (ambientSum declared).rewrites (interface := ⟨choiceSpace, AtomsReduce.closedAtom⟩)
        (atomTerm 0 coin) (atomTerm 0 (.con "heads")) ∧
      ∀ target : Contexts.Term ambient AtomsReduce.closedAtom,
        ¬ (ambientSum declared).rewrites (interface := ⟨emptySpaceTerm, AtomsReduce.closedAtom⟩)
          (atomTerm 0 coin) target :=
  ⟨choiceMember_two_reducts.1, emptyMember_choice_normal⟩

/-! ## The class, with contexts -/

/-- **The theories given by a table of first-order rules with bound right
sides, on the terms with free variables below a width**, with all the
contexts of those terms. -/
def ScopedFirstOrderTabular (source : ContextTheory.{0}) : Prop :=
  ∃ (theory : Theory) (table : RuleTable) (width : Nat),
    theory.Tabular table ∧ BoundFirstOrder table ∧ source = scopedRewriting width theory

/-- **Positive**: the closed terms of the pure calculus. -/
theorem closedPure_scopedFirstOrderTabular :
    ScopedFirstOrderTabular (scopedRewriting 0 Theory.empty) :=
  ⟨Theory.empty, ∅, 0, empty_tabular, empty_boundFirstOrder, rfl⟩

/-- **Positive**: the calculus with choice, on the terms with one free
variable. -/
theorem openChoice_scopedFirstOrderTabular :
    ScopedFirstOrderTabular (scopedRewriting 1 (withChoice Theory.empty)) :=
  ⟨withChoice Theory.empty, choiceTable, 1, withChoice_empty_tabular, choiceTable_boundFirstOrder,
    rfl⟩

/-- Every term of such a theory has finitely many reducts. -/
theorem ScopedFirstOrderTabular.finite_reducts {source : ContextTheory.{0}}
    (member : ScopedFirstOrderTabular source) (interface : source.Interface)
    (term : source.Term interface) : {next | source.rewrites term next}.Finite := by
  obtain ⟨theory, table, width, tabular, admitted, rfl⟩ := member
  have finite : {next : LF.Term | Dedukti.Step (Theory.ofTable table) term.1 next}.Finite :=
    step_finite_of_rootStep_finite (rootStep_finite_of_rightDetermined admitted.determined) term.1
  refine (finite.preimage Subtype.val_injective.injOn).subset ?_
  intro next step
  exact tabular.step_iff.mp step

/-- A closed term for each number. -/
def closedTower : Nat → LF.Term
  | 0 => .srt .type
  | count + 1 => .app (.srt .type) (closedTower count)

theorem closedTower_closed : ∀ count : Nat, LF.WellScoped 0 (closedTower count)
  | 0 => .srt
  | count + 1 => .app .srt (closedTower_closed count)

theorem closedTower_injective : Function.Injective closedTower := by
  intro first
  induction first with
  | zero =>
      intro second same
      cases second with
      | zero => rfl
      | succ second => cases same
  | succ first ih =>
      intro second same
      cases second with
      | zero => cases same
      | succ second =>
          simp only [closedTower, LF.Term.app.injEq, true_and] at same
          rw [ih same]

/-- **Negative**: the closed terms of the theory of the rule `c ⟶ x`.  The
constant reduces to every closed term. -/
theorem closedFree_not_scopedFirstOrderTabular :
    ¬ ScopedFirstOrderTabular (scopedRewriting 0 (Theory.ofTable {freeRule})) := by
  intro member
  have finite := member.finite_reducts ()
    (⟨.con "c", .con⟩ : {term : LF.Term // LF.WellScoped 0 term})
  refine Set.infinite_range_of_injective
    (f := fun count : Nat =>
      (⟨closedTower count, closedTower_closed count⟩ : {term : LF.Term // LF.WellScoped 0 term}))
    (fun first second same => closedTower_injective (congrArg Subtype.val same))
    (finite.subset ?_)
  rintro _ ⟨count, rfl⟩
  exact freeRule_step _

/-! ## The sentence -/

/-- **The sum is a host, with all contexts, of the theories given by a table
of first-order rules with bound right sides on the terms with free variables
below a width**, under every reading in which the holes of atoms are free.
Each theory is hosted at the interfaces that carry the space of its table. -/
theorem ambientSum_hostOf_scopedFirstOrderTabular (free : AtomsFree declared) :
    HostOf (ambientSum declared) ScopedFirstOrderTabular .contexts .hosting := by
  rintro reading ⟨theory, table, width, tabular, admitted, rfl⟩
  exact hostedBy_ambientSum (tableSpace table)
    ⟨scopedMemberMap theory table free width, scopedMemberMap_hosting tabular admitted free width⟩

/-- The cartesian reading. -/
theorem cartesianSum_hostOf_scopedFirstOrderTabular :
    HostOf (ambientSum fun _ => True) ScopedFirstOrderTabular .contexts .hosting :=
  ambientSum_hostOf_scopedFirstOrderTabular atomsFree_all

/-- The reading in which an atom may be discarded and copied, and a name and
a space are used once. -/
theorem atomRegionsSum_hostOf_scopedFirstOrderTabular :
    HostOf (ambientSum (ofSorts ["Atom"])) ScopedFirstOrderTabular .contexts .hosting :=
  ambientSum_hostOf_scopedFirstOrderTabular atomsFree_atoms

/-- **A theory given by a table, in a reading of the member at the space of
the table**, on terms: a term is read as its plain atom.  A reading has the
terms of the member. -/
noncomputable def regionMemberMap (regions : Contexts.Interface → Prop) (theory : Theory)
    (table : RuleTable) :
    ContextMap ((rewritingTheory theory).gslt ()).termsAlone
      ((ambientTheory (tableSpace table)).regionReading regions) :=
  ContextMap.ofTerms (source := (rewritingTheory theory).gslt ())
    (target := (ambientTheory (tableSpace table)).regionReading regions) AtomsReduce.closedAtom
    (fun term => atomTerm 0 term)
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact Relation.EqvGen.refl _)

/-- It is hosting: a reading has the static equivalence and the steps of the
member. -/
theorem regionMemberMap_hosting (regions : Contexts.Interface → Prop) {theory : Theory}
    {table : RuleTable} (tabular : theory.Tabular table) (admitted : BoundFirstOrder table) :
    (regionMemberMap regions theory table).Hosting :=
  (ContextMap.ofTerms_hosting_iff (source := (rewritingTheory theory).gslt ())
    (target := (ambientTheory (tableSpace table)).regionReading regions) AtomsReduce.closedAtom
    (fun term => atomTerm 0 term)
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact Relation.EqvGen.refl _)).mpr
    ((ContextMap.ofTerms_hosting_iff (source := (rewritingTheory theory).gslt ())
      (target := ambientTheory (tableSpace table)) AtomsReduce.closedAtom
      (fun term => atomTerm 0 term)
      (fun {first second} related => by
        have same : first = second := related
        rw [same]
        exact Relation.EqvGen.refl _)).mp (memberMap_hosting tabular admitted))

/-- **On terms the sum is a host of the theories given by a table of
first-order rules with bound right sides**, under every reading. -/
theorem ambientSum_hostOf_firstOrderTabular (regions : Contexts.Interface → Prop) :
    HostOf (ambientSum regions) FirstOrderTabular .terms .hosting := by
  rintro reading ⟨source, ⟨theory, table, tabular, admitted, rfl⟩, interface, rfl⟩
  exact hostedBy_ambientSum (tableSpace table)
    ⟨regionMemberMap regions theory table, regionMemberMap_hosting regions tabular admitted⟩

/-! ## With the contexts of the members as they are -/

/-- **The sum of the members with their contexts as they are has a linear
size**, so it receives no map from a theory on the terms with free variables
below a width: the readings in which the holes of atoms are free are
needed. -/
theorem linearSum_isEmpty_contextMap_scoped (width : Nat) (theory : Theory) :
    IsEmpty (ContextMap (scopedRewriting width theory)
      (ContextTheory.sum fun space : SpaceTerm => ambientTheory space)) :=
  (ContextTheory.LinearSize.sum (fun space : SpaceTerm => ambientTheory space) fun space =>
    QuoteDropOnly.linearSize ambientPresentation ambient_quoteDropOnly
      (ambientEvaluator space.1)).isEmpty_contextMap_of_discards
    (scopedRewriting_discards width theory)
    ⟨(⟨.srt .type, .srt⟩ : {term : LF.Term // LF.WellScoped width term})⟩

#print axioms ambientSum
#print axioms member_hostedBy_ambientSum
#print axioms member_exhausted_by_ambientSum
#print axioms ambientSum_isEmpty_context_of_ne
#print axioms ambientSum_coin
#print axioms closedPure_scopedFirstOrderTabular
#print axioms openChoice_scopedFirstOrderTabular
#print axioms ScopedFirstOrderTabular.finite_reducts
#print axioms closedFree_not_scopedFirstOrderTabular
#print axioms ambientSum_hostOf_scopedFirstOrderTabular
#print axioms cartesianSum_hostOf_scopedFirstOrderTabular
#print axioms atomRegionsSum_hostOf_scopedFirstOrderTabular
#print axioms regionMemberMap_hosting
#print axioms ambientSum_hostOf_firstOrderTabular
#print axioms linearSum_isEmpty_contextMap_scoped

end Mettapedia.Logic.HostingStyles.AmbientSpace
