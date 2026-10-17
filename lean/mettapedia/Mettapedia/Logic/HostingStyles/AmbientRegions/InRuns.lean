import Mettapedia.Logic.HostingStyles.AmbientRegions.WithoutRun
import Mettapedia.Logic.HostingStyles.AmbientRegions.AllHeadedHosting
import Mettapedia.Logic.HostingStyles.AmbientSpace.Sum

/-!
# Inside a run: one member hosts every table, on terms

The member of the ambient family at a space hosts the theories of the table
of that space; another table needs another member.  With the run constructor
one member reads a term of any table as the run of its atom in the space of
that table.

* **On terms each member of the contained presentation is a host of the
  theories of every table of first-order rules with bound right sides**
  (`contained_hostOf_firstOrderTabular_inRuns`), at every ambient space that
  answers nothing for a run; with headed root steps, at every ambient space
  (`headed_hostOf_firstOrderTabular_inRuns`); with every root step headed, at
  every ambient space, the tables without a variable as a left side
  (`allHeaded_hostOf_tabular_inRuns`).  This is the class that the
  candidate with a run at the root hosts on terms, beside the class that the
  member hosts with contexts.
* **Negative: with contexts that reading is not hosting**
  (`contained_singleRun_not_hosting_scoped`): a map that reads every term as
  one run cannot carry the application of two terms, in any reading of any
  member.  With contexts a table is hosted at the ambient space of the table
  (`contained_hostOf_scopedTabularAt`), by plain atoms.
* **Each family as one theory** (`containedSum`, `scopedSum`): the members
  summed over their ambient spaces are a host, with all contexts, of the
  theories of every table (`containedSum_hostOf_scopedFirstOrderTabular`,
  `scopedSum_hostOf_scopedFirstOrderTabular`).  A context of the sum stays at
  one ambient space (`containedSum_isEmpty_context_of_ne`); a term at one
  ambient space has parts in other spaces through its runs.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory RuleTable rewritingTheory)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.ContextReadings

section Reading

variable {presentation : ValidatedLanguageDef}

/-- **A theory, in a presentation that carries atoms and declares the run**,
on terms: a term is read as the run of its atom in the space of a list of
rules. -/
def runTermsMapIn (theory : Theory) (base : BasePremiseEvaluator)
    (declares : DeclaresRun presentation.language) (carries : CarriesAtoms presentation.language)
    (rules : List Dedukti.RewriteRule) :
    ContextMap ((rewritingTheory theory).gslt ()).termsAlone (contextTheory base presentation) :=
  ContextMap.ofTerms (source := (rewritingTheory theory).gslt ())
    (target := contextTheory base presentation) AtomsReduce.closedAtom
    (fun term => runAtomIn declares carries rules 0 term)
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact Relation.EqvGen.refl _)

/-- **That map is hosting**, when the steps of the presentation from the run
of the atom of a term are the runs of the atoms of the steps of the theory. -/
theorem runTermsMapIn_hosting (declares : DeclaresRun presentation.language)
    (carries : CarriesAtoms presentation.language) (only : QuoteDropOnly presentation.language)
    (sorted : QuoteDropSorted presentation.language)
    (names : NamesOnlyDropped presentation.language unquotedSorts) {base : BasePremiseEvaluator}
    {rules : List Dedukti.RewriteRule} {theory : Theory}
    (steps : ∀ {depth : Nat} {source : LF.Term} {target : Pattern},
      Step base presentation.language (runPattern (ruleSpace rules) (atomAt depth source)) target ↔
        ∃ next, target = runPattern (ruleSpace rules) (atomAt depth next) ∧
          Dedukti.Step theory source next) :
    (runTermsMapIn theory base declares carries rules).Hosting := by
  refine (ContextMap.ofTerms_hosting_iff (source := (rewritingTheory theory).gslt ())
    (target := contextTheory base presentation) AtomsReduce.closedAtom
    (fun term => runAtomIn declares carries rules 0 term)
    (fun {first second} related => by
      have same : first = second := related
      rw [same]
      exact Relation.EqvGen.refl _)).mpr ⟨?_, ?_, ?_⟩
  · intro first second related
    have same : runAtomIn declares carries rules 0 second = runAtomIn declares carries rules 0 first :=
      eq_runAtomIn_of_related declares carries only sorted names (base := base) (depth := 0) related
    exact (runAtomIn_injective declares carries rules 0 same).symm
  · intro first next step
    exact (termStep_runAtomIn_iff declares carries only sorted names steps (depth := 0)).mpr
      ⟨next, step, rfl⟩
  · intro first next step
    obtain ⟨nextTerm, sourceStep, rfl⟩ :=
      (termStep_runAtomIn_iff declares carries only sorted names steps (depth := 0)).mp step
    exact ⟨nextTerm, sourceStep, Relation.EqvGen.refl _⟩

end Reading

variable {admits : Pattern → Bool} {declared : Contexts.Interface → Prop}

/-- **On terms, each member of the contained presentation at an ambient space
that answers nothing for a run is a host of the theories of every table of
first-order rules with bound right sides**: a term is read as the run of its
atom in the space of its table. -/
theorem contained_hostOf_firstOrderTabular_inRuns (admitsAtoms : AdmitsAtoms admits)
    {ambientSpace : Pattern} (silent : RunSilent admits ambientSpace) :
    HostOf (containedTheory admits ambientSpace) FirstOrderTabular .terms .hosting := by
  rintro reading ⟨source, ⟨theory, table, tabular, admitted, rfl⟩, interface, rfl⟩
  exact ⟨runTermsMapIn (presentation := containedPresentation) theory _ contained_declaresRun
      region_carriesAtoms.1 table.toList,
    runTermsMapIn_hosting (presentation := containedPresentation) contained_declaresRun
      region_carriesAtoms.1 contained_quoteDropOnly contained_quoteDropSorted
      contained_namesOnlyDropped
      (contained_runAtom_step_iff admitsAtoms silent admitted.listed.1 admitted.listed.2
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)⟩

/-- **With headed root steps, at every ambient space**: each member is a
host, on terms, of the theories of every such table. -/
theorem headed_hostOf_firstOrderTabular_inRuns (admitsAtoms : AdmitsAtoms admits)
    (ambientSpace : Pattern) :
    HostOf (headedTheory admits ambientSpace) FirstOrderTabular .terms .hosting := by
  rintro reading ⟨source, ⟨theory, table, tabular, admitted, rfl⟩, interface, rfl⟩
  exact ⟨runTermsMapIn (presentation := headedPresentation) theory _ headedContained_declaresRun
      headedContained_carriesAtoms table.toList,
    runTermsMapIn_hosting (presentation := headedPresentation) headedContained_declaresRun
      headedContained_carriesAtoms headedContained_quoteDropOnly headedContained_quoteDropSorted
      headedContained_namesOnlyDropped
      (headed_runAtom_step_iff admitsAtoms ambientSpace admitted.listed.1 admitted.listed.2
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)⟩

/-- **With every root step headed, at every ambient space**: each member is a
host, on terms, of the theories of a table of first-order rules with bound
right sides none of whose left sides is a variable, each term read as the run
of its atom in the space of the table. -/
theorem allHeaded_hostOf_tabular_inRuns (admitsAtoms : AdmitsAtoms admits)
    (ambientSpace : Pattern) {table : RuleTable} (admitted : BoundFirstOrder table)
    (headed : ∀ rule ∈ table, ∀ index : Nat, rule.lhs ≠ .var index) :
    HostOf (allHeadedTheory admits ambientSpace)
      (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
      .terms .hosting := by
  rintro reading ⟨source, ⟨theory, tabular, rfl⟩, interface, rfl⟩
  exact ⟨runTermsMapIn (presentation := allHeadedPresentation) theory _ allHeaded_declaresRun
      allHeaded_carriesAtoms table.toList,
    runTermsMapIn_hosting (presentation := allHeadedPresentation) allHeaded_declaresRun
      allHeaded_carriesAtoms allHeaded_quoteDropOnly allHeaded_quoteDropSorted
      allHeaded_namesOnlyDropped
      (allHeaded_runAtom_step_iff admitsAtoms ambientSpace admitted.listed.1 admitted.listed.2
        (fun rule member => headed rule (Finset.mem_toList.mp member))
        (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined)⟩

/-- **The member at the empty space, under the matching evaluator, is a host
on terms of the theories of every table.** -/
theorem emptyMember_hostOf_firstOrderTabular_inRuns :
    HostOf (containedTheory anySubject emptySpace) FirstOrderTabular .terms .hosting :=
  contained_hostOf_firstOrderTabular_inRuns anySubject_admitsAtoms (runSilent_emptySpace anySubject)

/-- **Negative: with contexts, no map that reads every term as one run is
hosting**, from a theory on the terms with free variables below a width and
into any reading of any member of the contained presentation.  The image of
the application of two terms would have two runs. -/
theorem contained_singleRun_not_hosting_scoped {ambientSpace : Pattern} {theory : Theory}
    {width : Nat}
    (map : ContextMap (scopedRewriting width theory)
      ((containedTheory admits ambientSpace).regionReading declared))
    (single : ∀ term : (scopedRewriting width theory).Term (),
      tokens runLabel (map.term term).1 = 1) : ¬ map.Hosting :=
  not_hosting_of_uniform_tokens (presentation := containedPresentation) contained_quoteDropOnly
    (counted := runLabel) (by decide) (by decide) map (scopedApplication width theory) Nat.one_pos
    single (fixed := ⟨.srt .type, .srt⟩) (still := ⟨.srt .type, .srt⟩) (other := ⟨.srt .kind, .srt⟩)
    (fun same => absurd (show LF.Term.app (.srt .type) (.srt .type) =
      .app (.srt .type) (.srt .kind) from congrArg Subtype.val same) (by decide))
    (fun same => absurd (show LF.Term.app (.srt .type) (.srt .type) =
      .app (.srt .kind) (.srt .type) from congrArg Subtype.val same) (by decide))

/-! ## Each family as one theory -/

/-- The readings of the members of the contained presentation in which the
interfaces of a class may be used any number of times, as a family indexed by
the ambient spaces. -/
abbrev containedReadings (admits : Pattern → Bool) (declared : Contexts.Interface → Prop) :
    ContainedSpace → ContextTheory.{0} :=
  fun space => (containedTheory admits space.1).regionReading declared

/-- **The contained family as one theory**: the sum of those readings over
the ambient spaces. -/
def containedSum (admits : Pattern → Bool) (declared : Contexts.Interface → Prop) :
    ContextTheory.{0} :=
  ContextTheory.sum (containedReadings admits declared)

/-- The same family for the scoped presentation. -/
abbrev scopedReadings (admits : Pattern → Bool) (declared : Contexts.Interface → Prop) :
    ScopedSpace → ContextTheory.{0} :=
  fun space => (scopedTheory admits space.1).regionReading declared

/-- **The scoped family as one theory.** -/
def scopedSum (admits : Pattern → Bool) (declared : Contexts.Interface → Prop) :
    ContextTheory.{0} :=
  ContextTheory.sum (scopedReadings admits declared)

/-- **The contained family is a host, with all contexts, of the theories
given by a table of first-order rules with bound right sides on the terms
with free variables below a width**, under every reading in which the holes
of atoms are free and every guard that admits the atoms of terms.  Each
theory is hosted at the interfaces that carry the space of its table. -/
theorem containedSum_hostOf_scopedFirstOrderTabular (admitsAtoms : AdmitsAtoms admits)
    (free : AtomsFree declared) :
    HostOf (containedSum admits declared) ScopedFirstOrderTabular .contexts .hosting := by
  rintro reading ⟨theory, table, width, tabular, admitted, rfl⟩
  exact HostedBy.trans
    (contained_hostOf_scopedTabularAt admitsAtoms admitted free _ ⟨theory, width, tabular, rfl⟩)
    ⟨ContextTheory.inject (containedReadings admits declared) (containedSpaceOf (tableSpace table)),
      ContextTheory.inject_hosting (containedReadings admits declared)
        (containedSpaceOf (tableSpace table))⟩

/-- **The scoped family is a host of the same class, with all contexts.** -/
theorem scopedSum_hostOf_scopedFirstOrderTabular (admitsAtoms : AdmitsAtoms admits)
    (free : AtomsFree declared) :
    HostOf (scopedSum admits declared) ScopedFirstOrderTabular .contexts .hosting := by
  rintro reading ⟨theory, table, width, tabular, admitted, rfl⟩
  exact HostedBy.trans
    (scoped_hostOf_scopedTabularAt admitsAtoms admitted free _ ⟨theory, width, tabular, rfl⟩)
    ⟨ContextTheory.inject (scopedReadings admits declared) (scopedSpaceOf (tableSpace table)),
      ContextTheory.inject_hosting (scopedReadings admits declared)
        (scopedSpaceOf (tableSpace table))⟩

/-- **Negative**: a context of the sum stays at one ambient space. -/
theorem containedSum_isEmpty_context_of_ne {first second : ContainedSpace} (apart : first ≠ second)
    (source target : Contexts.Interface) :
    IsEmpty ((containedSum admits declared).Context
      (fun _ : Unit => (⟨first, source⟩ : (containedSum admits declared).Interface))
      ⟨second, target⟩) :=
  ContextTheory.sum_isEmpty_context_of_ne (containedReadings admits declared) apart source target

#print axioms runTermsMapIn_hosting
#print axioms containedSum_hostOf_scopedFirstOrderTabular
#print axioms scopedSum_hostOf_scopedFirstOrderTabular
#print axioms containedSum_isEmpty_context_of_ne
#print axioms contained_hostOf_firstOrderTabular_inRuns
#print axioms headed_hostOf_firstOrderTabular_inRuns
#print axioms allHeaded_hostOf_tabular_inRuns
#print axioms emptyMember_hostOf_firstOrderTabular_inRuns
#print axioms contained_singleRun_not_hosting_scoped

end Mettapedia.Logic.HostingStyles.AmbientRegions
