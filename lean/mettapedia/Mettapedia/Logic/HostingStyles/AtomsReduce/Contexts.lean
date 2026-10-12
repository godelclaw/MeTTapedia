import Mettapedia.Logic.HostingStyles.AtomsReduce.Hosting
import Mettapedia.Logic.HostingStyles.AtomsReduce.Quotation
import Mettapedia.Logic.HostingStyles.ContextReadings.Summary

/-!
# The candidate in which atoms reduce, with contexts

The probe hosts no computation with contexts under any reading, and under the
cartesian reading the reason is that no constructor takes what reduces
(`not_hosting_of_separateSort`).  This module redoes that cell for the
candidate in which what reduces is an atom.

* **The condition of that obstruction fails here**: constructors take atoms
  (`atomsReduce_takes_atoms`), and the application of an atom to an atom is a
  context of two holes whose two fillings both reduce in place
  (`applicationContext`, `application_left`, `application_right`,
  `application_reduces_both`).
* **Linear reading: the earlier obstruction stands.**  The static equivalence
  of the candidate is that of quotation and dropping, so its contexts have a
  linear size and there is no map of theories at all from a theory of the
  λΠ-calculus modulo (`atomsReduce_isEmpty_contextMap`,
  `atomsReduceProbe_not_hosts_tabular_contexts`).
* **Regions, names and spaces free and atoms used once**: a map from a
  theory that discards sends its terms to data, and data does not reduce
  here either; no map preserves transitions (`dataRegions_not_preserves`).
* **Every reading, the cartesian one included: the next obstruction is the
  run.**  The space is carried by a run at the root of the term, and a
  context of a reading places its fillings in a pattern.  A map that sends
  every term to a term with the same positive number of runs has, for a
  context of two holes, an image that uses at most one of them
  (`not_hosting_of_uniform_tokens`).  So no map that reads a term as one run
  is hosting, for any theory of the λΠ-calculus modulo and under any reading
  (`not_hosting_of_singleRun`); in particular the reading of the terms that
  hosts on terms does not extend to contexts (`runReading_not_hosting`).
  The witness is the context that applies its first hole to its second.
* On terms every reading has what the candidate has
  (`cartesian_hostOf_firstOrderTabular`).

What the readings in which atoms are free do host with all contexts, the pure
calculus on the terms with boundedly many free variables, is the content of
the module `ScopedContexts`.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AtomsReduce

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory rewritingTheory TermContext omega omega_step)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.ContextReadings

/-! ## What reduces is an ordinary argument -/

/-- **Constructors of the candidate take atoms**: the condition under which a
presentation hosts no pairing of terms that reduce does not hold. -/
theorem atomsReduce_takes_atoms : takesNoneOf atomsReduce "Atom" = false := by decide

/-- **Negative**: no constructor takes a name but dropping, and none takes a
term of a sort that the candidate does not have. -/
theorem atomsReduce_takesNoneOf_process : takesNoneOf atomsReduce "Process" = false ∧
    (atomsReduce.terms.all fun rule => rule.params.all fun parameter =>
      !(TermParam.typeExpr parameter).baseNames.contains "Process") = true := by
  decide

/-- **The application of an atom to an atom, as a context of two holes.** -/
def applicationContext (stage : List TypeExpr) :
    Contexts.Context atomsReducePresentation
      (fun _ : Bool => (⟨.base "Atom", stage⟩ : Contexts.Interface)) ⟨.base "Atom", stage⟩ :=
  binaryContext atomsReducePresentation (fun _ => "Atom") (rule := applicationConstructor)
    (firstName := "f") (secondName := "a") (by decide) rfl rfl stage

/-- The filling of the two holes: the function at `false`, the argument at
`true`. -/
def applicationFilling {stage : List TypeExpr}
    (function argument : Contexts.Term atomsReduce ⟨.base "Atom", stage⟩) :
    (index : Bool) → Contexts.Term atomsReduce ⟨.base "Atom", stage⟩ :=
  fun index => bif index then argument else function

theorem applicationContext_fill {stage : List TypeExpr}
    (function argument : Contexts.Term atomsReduce ⟨.base "Atom", stage⟩) :
    ((applicationContext stage).fill (applicationFilling function argument)).1 =
      .apply "App" [function.1, argument.1] :=
  rfl

/-- **A transition of the function is a transition of the application.** -/
theorem application_left {base : BasePremiseEvaluator} {stage : List TypeExpr}
    {function next : Contexts.Term atomsReduce ⟨.base "Atom", stage⟩}
    (argument : Contexts.Term atomsReduce ⟨.base "Atom", stage⟩)
    (step : TermStep base atomsReduce function next) :
    TermStep base atomsReduce
      ((applicationContext stage).fill (applicationFilling function argument))
      ((applicationContext stage).fill (applicationFilling next argument)) := by
  obtain ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩ := step
  refine ⟨(applicationContext stage).fill (applicationFilling redex argument),
    (applicationContext stage).fill (applicationFilling contractum argument), ?_, ⟨fuel + 1, ?_⟩, ?_⟩
  · exact (applicationContext stage).fill_resp base fun index => by
      cases index
      · exact before
      · exact Relation.EqvGen.refl _
  · exact step_appFunction (by simp [atomsReduce_rewrites]) argument.1 fired
  · exact (applicationContext stage).fill_resp base fun index => by
      cases index
      · exact after
      · exact Relation.EqvGen.refl _

/-- **A transition of the argument is a transition of the application.** -/
theorem application_right {base : BasePremiseEvaluator} {stage : List TypeExpr}
    {argument next : Contexts.Term atomsReduce ⟨.base "Atom", stage⟩}
    (function : Contexts.Term atomsReduce ⟨.base "Atom", stage⟩)
    (step : TermStep base atomsReduce argument next) :
    TermStep base atomsReduce
      ((applicationContext stage).fill (applicationFilling function argument))
      ((applicationContext stage).fill (applicationFilling function next)) := by
  obtain ⟨redex, contractum, before, ⟨fuel, fired⟩, after⟩ := step
  refine ⟨(applicationContext stage).fill (applicationFilling function redex),
    (applicationContext stage).fill (applicationFilling function contractum), ?_, ⟨fuel + 1, ?_⟩, ?_⟩
  · exact (applicationContext stage).fill_resp base fun index => by
      cases index
      · exact Relation.EqvGen.refl _
      · exact before
  · exact step_appArgument (by simp [atomsReduce_rewrites]) function.1 fired
  · exact (applicationContext stage).fill_resp base fun index => by
      cases index
      · exact Relation.EqvGen.refl _
      · exact after

/-- **A context of two holes whose two fillings both reduce**: the
application of the dropped quotation of the unit atom to itself has a
transition in which the function is released and one in which the argument
is, and the two results are apart.  Under every evaluator. -/
theorem application_reduces_both (base : BasePremiseEvaluator) :
    TermStep base atomsReduce
        ((applicationContext []).fill (applicationFilling droppedUnit droppedUnit))
        ((applicationContext []).fill (applicationFilling unitTerm droppedUnit)) ∧
      TermStep base atomsReduce
        ((applicationContext []).fill (applicationFilling droppedUnit droppedUnit))
        ((applicationContext []).fill (applicationFilling droppedUnit unitTerm)) ∧
      ¬ (termSetoid base atomsReduce closedAtom).r
        ((applicationContext []).fill (applicationFilling unitTerm droppedUnit))
        ((applicationContext []).fill (applicationFilling droppedUnit unitTerm)) :=
  ⟨application_left droppedUnit (droppedQuotation_release unitTerm),
    application_right droppedUnit (droppedQuotation_release unitTerm), fun related =>
      absurd (atomsReduce_quoteDropOnly.contract_eq related) (by decide)⟩

/-! ## The linear reading -/

/-- **With its contexts as they are, the candidate receives no map from a
theory of the λΠ-calculus modulo**, under any evaluator: its contexts use
each hole once, and such a theory discards. -/
theorem atomsReduce_isEmpty_contextMap (base : BasePremiseEvaluator) (theory : Theory) :
    IsEmpty (ContextMap (rewritingTheory theory) (contextTheory base atomsReducePresentation)) :=
  (QuoteDropOnly.linearSize atomsReducePresentation atomsReduce_quoteDropOnly
    base).isEmpty_contextMap_of_discards (rewritingTheory_discards theory)
    ⟨(.srt .type : LF.Term)⟩

/-- **With all its contexts the candidate is no host of the theories given by
a table.** -/
theorem atomsReduceProbe_not_hosts_tabular_contexts :
    ¬ atomsReduceProbe.Hosts TabularTheory .contexts .hosting :=
  QuoteDropOnly.not_hostOf_tabular_contexts atomsReducePresentation atomsReduce_quoteDropOnly
    matchingEvaluator

/-- Nor of the smaller class that it hosts on terms. -/
theorem atomsReduceProbe_not_hosts_firstOrderTabular_contexts :
    ¬ atomsReduceProbe.Hosts FirstOrderTabular .contexts .hosting :=
  fun hosts =>
    let ⟨map, _⟩ := hosts _ pure_firstOrderTabular
    (atomsReduce_isEmpty_contextMap matchingEvaluator Theory.empty).false map

/-! ## Regions: names and spaces free, atoms used once -/

/-- **The data of the candidate**: its names and its spaces, beneath any
binders.  Neither reduces. -/
def candidateData : Contexts.Interface → Prop := ofSorts ["CandidateName", "Space"]

/-- **Positive**: the closed names. -/
theorem candidateData_closedName : candidateData ⟨.base "CandidateName", []⟩ :=
  ofSorts_base (by decide) []

/-- **Negative**: the closed atoms. -/
theorem not_candidateData_closedAtom : ¬ candidateData closedAtom :=
  not_ofSorts_base (by decide) []

/-- The reading in which names and spaces may be discarded and copied, and an
atom is used once. -/
abbrev dataRegions : ContextTheory.{0} := atomsReduceTheory.regionReading candidateData

/-- **Under the reading with data free, no map from a theory of the
λΠ-calculus modulo preserves transitions**: such a theory discards, so its
terms are sent to data, and data does not reduce. -/
theorem dataRegions_not_preserves (theory : Theory)
    (map : ContextMap (rewritingTheory theory) dataRegions) : ¬ map.PreservesTransitions :=
  (atomsReduce_quoteDropOnly.keptWeight matchingEvaluator).regions_not_preserves
    (presentation := atomsReducePresentation) (data := ["CandidateName", "Space"])
    (active := ["Atom"]) atomsReduce_headedIn_atom (by decide) map
    (rewritingTheory_discards theory) (term := omega) (next := omega) (omega_step theory)

/-! ## Every reading: a map that reads a term as one run -/

/-- **A map whose images all have one positive count of some constructor
uses at most one hole of a context of two.**  No reading of a presentation
whose static equivalence is that of quotation and dropping hosts, by such a
map, a theory with a context of two holes that keeps apart what differs in
either hole. -/
theorem not_hosting_of_uniform_tokens {base : BasePremiseEvaluator}
    {presentation : ValidatedLanguageDef} (only : QuoteDropOnly presentation.language)
    {counted : String → Bool} (quote : counted "prime-quote" = false)
    (drop : counted "prime-drop" = false) {declared : Contexts.Interface → Prop}
    {source : ContextTheory.{0}}
    (map : ContextMap source ((contextTheory base presentation).regionReading declared))
    {interface : source.Interface} (pair : source.Context (fun _ : Bool => interface) interface)
    {count : Nat} (positive : 0 < count)
    (uniform : ∀ term : source.Term interface, tokens counted (map.term term).1 = count)
    {fixed still other : source.Term interface}
    (right : ¬ (source.equations interface).r
      (source.fill pair fun index => bif index then still else fixed)
      (source.fill pair fun index => bif index then other else fixed))
    (left : ¬ (source.equations interface).r
      (source.fill pair fun index => bif index then fixed else still)
      (source.fill pair fun index => bif index then fixed else other)) :
    ¬ map.Hosting := by
  intro hosting
  have reflects : map.ReflectsEquations := map.reflectsEquations_of_faithful hosting.faithful
  obtain ⟨shape, acts, -⟩ := exists_shape (map.context pair)
  have image : ∀ filling : Bool → source.Term interface,
      (termSetoid base presentation.language (map.interface interface)).r
        (map.term (source.fill pair filling))
        ((map.context pair).act fun index => map.term (filling index)) :=
    fun filling => map.equivariant pair filling
  have both : tokens counted (map.term (source.fill pair fun _ => fixed)).1 =
      tokens counted ((map.context pair).act fun _ => map.term fixed).1 :=
    only.tokens_eq quote drop (image fun _ => fixed)
  have counted_ : tokens counted ((map.context pair).act fun _ => map.term fixed).1 =
      contextTokens counted shape +
        (shape.holes.count true * count + shape.holes.count false * count) := by
    have shaped := congrArg (tokens counted) (acts fun _ => map.term fixed)
    rw [tokens_fill, sum_map_eq_sum_count, Fintype.sum_bool] at shaped
    simpa only [uniform] using shaped
  rw [uniform, counted_] at both
  have bound : shape.holes.count true + shape.holes.count false ≤ 1 := by
    by_contra more
    have two : 2 ≤ shape.holes.count true + shape.holes.count false := by omega
    have scaled := Nat.mul_le_mul_right count two
    rw [Nat.add_mul] at scaled
    omega
  have unused : ∀ index : Bool, shape.holes.count index = 0 →
      ∀ first second : Bool → source.Term interface,
        (∀ position, position ≠ index → first position = second position) →
          (source.equations interface).r (source.fill pair first) (source.fill pair second) := by
    intro index absent first second agree
    apply reflects
    have same : (map.context pair).act (fun position => map.term (first position)) =
        (map.context pair).act fun position => map.term (second position) := by
      apply Subtype.ext
      refine (acts fun position => map.term (first position)).trans
        (Eq.trans ?_ (acts fun position => map.term (second position)).symm)
      apply MultiHoleContext.fill_congr
      intro position member
      have apart : position ≠ index := fun same =>
        (List.count_eq_zero.mp absent) (same ▸ member)
      show (map.term (first position)).1 = (map.term (second position)).1
      rw [agree position apart]
    exact (termSetoid base presentation.language _).iseqv.trans (image first)
      ((termSetoid base presentation.language _).iseqv.trans
        (ContextMap.equations_of_eq
          (target := (contextTheory base presentation).regionReading declared) same)
        ((termSetoid base presentation.language _).iseqv.symm (image second)))
  by_cases second : shape.holes.count true = 0
  · exact right (unused true second _ _ fun position apart => by
      cases position with
      | false => rfl
      | true => exact (apart rfl).elim)
  · have first : shape.holes.count false = 0 := by omega
    exact left (unused false first _ _ fun position apart => by
      cases position with
      | false => exact (apart rfl).elim
      | true => rfl)

/-- The label of a run, as a count. -/
def runLabel (label : String) : Bool := label == "prime-run"

/-- **The run of a term in the space of a list of rules has exactly one
run.** -/
theorem tokens_run_runIn (rules : List Dedukti.RewriteRule) (term : LF.Term) :
    tokens runLabel (runTermIn rules term).1 = 1 := by
  have space : tokens runLabel (ruleSpace rules) = 0 :=
    tokens_ruleSpace (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) rules
  have subject : tokens runLabel (atomAt 0 term) = 0 :=
    tokens_atomAt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) term 0
  show tokens runLabel (runPattern (ruleSpace rules) (atomAt 0 term)) = 1
  simp [runPattern, tokens, tokensList, space, subject, runLabel]

/-- **Negative**: an atom of a term has no run. -/
theorem tokens_run_atomAt (term : LF.Term) : tokens runLabel (atomAt 0 term) = 0 :=
  tokens_atomAt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) term 0

/-- The context of a theory of the λΠ-calculus modulo that applies its first
hole to its second. -/
def termApplication (theory : Theory) :
    (rewritingTheory theory).Context (fun _ : Bool => ()) () :=
  (TermContext.app (.hole false) (.hole true) : TermContext Bool)

/-- **No map that reads every term as one run is hosting**, from any theory
of the λΠ-calculus modulo and into any reading of the candidate: the image of
the context that applies its first hole to its second can use only one of its
holes. -/
theorem not_hosting_of_singleRun {theory : Theory} {declared : Contexts.Interface → Prop}
    (map : ContextMap (rewritingTheory theory) (atomsReduceTheory.regionReading declared))
    (single : ∀ term : (rewritingTheory theory).Term (), tokens runLabel (map.term term).1 = 1) :
    ¬ map.Hosting :=
  not_hosting_of_uniform_tokens atomsReduce_quoteDropOnly (counted := runLabel) (by decide)
    (by decide) map (termApplication theory) Nat.one_pos single
    (fixed := (.srt .type : LF.Term)) (still := (.srt .type : LF.Term))
    (other := (.srt .kind : LF.Term))
    (fun same => absurd (show LF.Term.app (.srt .type) (.srt .type) =
      .app (.srt .type) (.srt .kind) from same) (by decide))
    (fun same => absurd (show LF.Term.app (.srt .type) (.srt .type) =
      .app (.srt .kind) (.srt .type) from same) (by decide))

/-- **The reading of the terms that hosts on terms does not extend to
contexts**: no map of theories, into any reading of the candidate, that sends
each term to its run in the space of one list of rules is hosting. -/
theorem runReading_not_hosting {theory : Theory} {declared : Contexts.Interface → Prop}
    (rules : List Dedukti.RewriteRule)
    (map : ContextMap (rewritingTheory theory) (atomsReduceTheory.regionReading declared))
    (reads : ∀ term : (rewritingTheory theory).Term (),
      (map.term term).1 = (runTermIn rules term).1) : ¬ map.Hosting :=
  not_hosting_of_singleRun map fun term => by rw [reads]; exact tokens_run_runIn rules term

/-! ## On terms every reading has what the candidate has -/

/-- **On terms the cartesian reading is a host of the same class.** -/
theorem cartesian_hostOf_firstOrderTabular :
    HostOf atomsReduceTheory.cartesianReading FirstOrderTabular .terms .hosting :=
  HostOf.trans atomsReduce_hostOf_firstOrderTabular
    ⟨atomsReduceTheory.toCartesianReading, atomsReduceTheory.toCartesianReading_hosting⟩

#print axioms atomsReduce_takes_atoms
#print axioms application_left
#print axioms application_right
#print axioms application_reduces_both
#print axioms atomsReduce_isEmpty_contextMap
#print axioms atomsReduceProbe_not_hosts_tabular_contexts
#print axioms atomsReduceProbe_not_hosts_firstOrderTabular_contexts
#print axioms dataRegions_not_preserves
#print axioms not_hosting_of_uniform_tokens
#print axioms tokens_run_runIn
#print axioms not_hosting_of_singleRun
#print axioms runReading_not_hosting
#print axioms cartesian_hostOf_firstOrderTabular

end Mettapedia.Logic.HostingStyles.AtomsReduce
