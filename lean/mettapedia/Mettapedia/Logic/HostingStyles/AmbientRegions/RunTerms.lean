import Mettapedia.Logic.HostingStyles.AmbientRegions.Hosting

/-!
# A run as a term, and its class of the static equivalence

In a language that declares the run as the candidate in which atoms reduce
does (`DeclaresRun`), the run of an atom in a space is an atom
(`runTermIn`), and the parts of a run that is a term are terms
(`run_parts_wellSorted_in`).  Where the static equivalence is that of
quotation and dropping, no equation moves a run:

* a term equal to a run is a run, of an equal space and an equal subject
  (`eq_runTermIn_of_related`);
* two runs are equal exactly when their spaces are and their subjects are
  (`runTermIn_related_iff`);
* a term equal to a term without quotation and dropping is that term
  (`eq_of_related_of_dropFree_in`).

These are the statements `eq_run_of_contract`, `run_parts_wellSorted` and
`eq_of_related_of_dropFree` of the earlier modules, for every language with
the stated declarations.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.AmbientRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.AtomsReduce
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

/-! ## Languages that declare the run -/

/-- **A language declares the run of an atom in a space, as an atom**: the
run constructor of the candidate in which atoms reduce, and no other
constructor of its label. -/
def DeclaresRun (lang : LanguageDef) : Prop :=
  runAtomConstructor ∈ lang.terms ∧
    ∀ rule ∈ lang.terms, rule.label = "prime-run" →
      rule.params = [.simple "space" (.base "Space"), .simple "subject" (.base "Atom")]

/-- **Positive**: the contained presentation. -/
theorem contained_declaresRun : DeclaresRun containedRun := by
  unfold DeclaresRun
  decide

/-- **Positive**: the scoped presentation. -/
theorem scoped_declaresRun : DeclaresRun scopedRun := by
  unfold DeclaresRun
  decide

/-- **Negative**: the ambient presentation has no run. -/
theorem ambient_not_declaresRun : ¬ DeclaresRun ambient := by
  unfold DeclaresRun
  decide

variable {lang : LanguageDef}

/-- The run of an atom in a space is an atom. -/
theorem run_wellSorted_in (declares : DeclaresRun lang) {bound : List TypeExpr}
    {space subject : Pattern}
    (spaceSorted : OpenPatternWellSorted lang FreeTypeContext.empty bound (.base "Space") space)
    (subjectSorted : OpenPatternWellSorted lang FreeTypeContext.empty bound (.base "Atom") subject) :
    OpenPatternWellSorted lang FreeTypeContext.empty bound (.base "Atom")
      (runPattern space subject) :=
  wellSorted_apply_two (lang := lang) (label := "prime-run") (firstName := "space")
    (secondName := "subject") declares.1 spaceSorted subjectSorted

/-- **The space and the subject of a run that is a term are terms.** -/
theorem run_parts_wellSorted_in (declares : DeclaresRun lang) {space subject : Pattern}
    {bound : List TypeExpr}
    (sorted : OpenPatternWellSorted lang FreeTypeContext.empty bound (.base "Atom")
      (runPattern space subject)) :
    OpenPatternWellSorted lang FreeTypeContext.empty bound (.base "Space") space ∧
      OpenPatternWellSorted lang FreeTypeContext.empty bound (.base "Atom") subject := by
  obtain ⟨typed, canonical, object, scope⟩ := sorted
  obtain ⟨rule, member, label, arguments⟩ := hasType_apply_inv typed
  rw [declares.2 rule member label] at arguments
  obtain ⟨spaceTyped, rest⟩ := arguments.simple_cons_inv
  obtain ⟨subjectTyped, -⟩ := rest.simple_cons_inv
  have canonicalParts : space.hasCanonicalBinderMetadata = true ∧
      subject.hasCanonicalBinderMetadata = true := by
    simpa [runPattern, Pattern.hasCanonicalBinderMetadata, Pattern.hasCanonicalBinderMetadataList]
      using canonical
  have objectParts : isObjectPattern space = true ∧ isObjectPattern subject = true := by
    simpa [runPattern, isObjectPattern, isObjectPatternList] using object
  have scopeParts : space.isWellScopedAt bound.length = true ∧
      subject.isWellScopedAt bound.length = true := by
    have whole : (runPattern space subject).isWellScopedAt bound.length = true := scope
    simpa [runPattern, Pattern.isWellScopedAt, Pattern.isWellScopedListAt] using whole
  exact ⟨⟨spaceTyped, canonicalParts.1, objectParts.1, scopeParts.1⟩,
    ⟨subjectTyped, canonicalParts.2, objectParts.2, scopeParts.2⟩⟩

/-- **The run of an atom in a space**, as an atom of a language that declares
the run, at the stage of both. -/
def runTermIn (declares : DeclaresRun lang) {stage : List TypeExpr}
    (space : Contexts.Term lang ⟨.base "Space", stage⟩)
    (atom : Contexts.Term lang ⟨.base "Atom", stage⟩) : Contexts.Term lang ⟨.base "Atom", stage⟩ :=
  ⟨runPattern space.1 atom.1, run_wellSorted_in declares space.2 atom.2⟩

@[simp] theorem runTermIn_val (declares : DeclaresRun lang) {stage : List TypeExpr}
    (space : Contexts.Term lang ⟨.base "Space", stage⟩)
    (atom : Contexts.Term lang ⟨.base "Atom", stage⟩) :
    (runTermIn declares space atom).1 = runPattern space.1 atom.1 :=
  rfl

/-- A term that is written as a run is the run of two terms. -/
theorem eq_runTermIn_of_val (declares : DeclaresRun lang) {stage : List TypeExpr}
    (term : Contexts.Term lang ⟨.base "Atom", stage⟩) {space subject : Pattern}
    (shape : term.1 = runPattern space subject) :
    ∃ (spaceTerm : Contexts.Term lang ⟨.base "Space", stage⟩)
      (atom : Contexts.Term lang ⟨.base "Atom", stage⟩),
      term = runTermIn declares spaceTerm atom ∧ spaceTerm.1 = space ∧ atom.1 = subject := by
  have parts := run_parts_wellSorted_in declares (shape ▸ term.2)
  exact ⟨⟨space, parts.1⟩, ⟨subject, parts.2⟩, Subtype.ext shape, rfl, rfl⟩

/-! ## No equation moves a run -/

/-- **A term whose contraction is a run is a run** of patterns with those
contractions, in every language in which quotation makes a name. -/
theorem eq_run_of_contract_in (sorted : QuoteDropSorted lang) {stage : List TypeExpr}
    (term : Contexts.Term lang ⟨.base "Atom", stage⟩) {space subject : Pattern}
    (same : contract term.1 = runPattern space subject) :
    ∃ otherSpace otherSubject, term.1 = runPattern otherSpace otherSubject ∧
      contract otherSpace = space ∧ contract otherSubject = subject := by
  obtain ⟨pattern, wellSorted⟩ := term
  cases pattern with
  | bvar index => simp [contract, runPattern] at same
  | fvar name => simp [contract, runPattern] at same
  | apply label arguments =>
      have notQuote : label ≠ "prime-quote" := by
        intro isQuote
        obtain ⟨rule, member, sameLabel, type⟩ := declared_constructor_of_hasType_apply wellSorted.1
        have category := (sorted.quote rule member (sameLabel.trans isQuote)).1
        rw [category] at type
        exact absurd (TypeExpr.base.inj type) (by decide)
      have unfolded : contract (Pattern.apply label arguments) = runPattern space subject := same
      rw [contract_apply_of_ne notQuote] at unfolded
      simp only [runPattern, Pattern.apply.injEq] at unfolded
      obtain ⟨rfl, parts⟩ := unfolded
      rcases arguments with _ | ⟨first, _ | ⟨second, _ | ⟨third, more⟩⟩⟩
      · simp at parts
      · simp at parts
      · simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at parts
        exact ⟨first, second, rfl, parts.1, parts.2⟩
      · simp at parts
  | lambda binder body => simp [contract, runPattern] at same
  | multiLambda arity binders body => simp [contract, runPattern] at same
  | subst body replacement => simp [contract, runPattern] at same
  | collection kind elements rest => simp [contract, runPattern] at same

/-- **Two runs are equal exactly when their spaces are equal and their
subjects are equal.** -/
theorem runTermIn_related_iff (only : QuoteDropOnly lang) (sorted : QuoteDropSorted lang)
    (declares : DeclaresRun lang) {base : BasePremiseEvaluator} {stage : List TypeExpr}
    {space otherSpace : Contexts.Term lang ⟨.base "Space", stage⟩}
    {atom otherAtom : Contexts.Term lang ⟨.base "Atom", stage⟩} :
    (termSetoid base lang ⟨.base "Atom", stage⟩).r (runTermIn declares space atom)
        (runTermIn declares otherSpace otherAtom) ↔
      contract space.1 = contract otherSpace.1 ∧ contract atom.1 = contract otherAtom.1 := by
  rw [only.termSetoid_iff sorted]
  show contract (runPattern space.1 atom.1) = contract (runPattern otherSpace.1 otherAtom.1) ↔ _
  rw [contract_runPattern', contract_runPattern']
  constructor
  · intro same
    exact runPattern_injective same
  · rintro ⟨spaces, atoms⟩
    rw [spaces, atoms]

/-- **A term equal to a run is a run, of an equal space and an equal
subject.** -/
theorem eq_runTermIn_of_related (only : QuoteDropOnly lang) (sorted : QuoteDropSorted lang)
    (declares : DeclaresRun lang) {base : BasePremiseEvaluator} {stage : List TypeExpr}
    {space : Contexts.Term lang ⟨.base "Space", stage⟩}
    {atom other : Contexts.Term lang ⟨.base "Atom", stage⟩}
    (related : (termSetoid base lang ⟨.base "Atom", stage⟩).r (runTermIn declares space atom)
      other) :
    ∃ (otherSpace : Contexts.Term lang ⟨.base "Space", stage⟩)
      (otherAtom : Contexts.Term lang ⟨.base "Atom", stage⟩),
      other = runTermIn declares otherSpace otherAtom ∧
        contract otherSpace.1 = contract space.1 ∧ contract otherAtom.1 = contract atom.1 := by
  have same : contract other.1 = runPattern (contract space.1) (contract atom.1) :=
    (only.contract_eq related).symm.trans (contract_runPattern' space.1 atom.1)
  obtain ⟨spacePattern, subject, shape, spaceSame, subjectSame⟩ :=
    eq_run_of_contract_in sorted other same
  obtain ⟨otherSpace, otherAtom, rfl, rfl, rfl⟩ := eq_runTermIn_of_val declares other shape
  exact ⟨otherSpace, otherAtom, rfl, spaceSame, subjectSame⟩

/-- The static equivalence of a language whose equations are those of
quotation and dropping is the same under every evaluator. -/
theorem termSetoid_base_irrelevant_in (only : QuoteDropOnly lang) (sorted : QuoteDropSorted lang)
    {first second : BasePremiseEvaluator} {interface : Contexts.Interface}
    {left right : Contexts.Term lang interface}
    (related : (termSetoid first lang interface).r left right) :
    (termSetoid second lang interface).r left right :=
  (only.termSetoid_iff sorted).mpr (only.contract_eq related)

/-- **A term, at a type of atoms or spaces, that the static equivalence
identifies with a term without quotation and dropping is that term**, in
every language in which names are taken by dropping alone. -/
theorem eq_of_related_of_dropFree_in (only : QuoteDropOnly lang) (sorted : QuoteDropSorted lang)
    (names : NamesOnlyDropped lang unquotedSorts) {base : BasePremiseEvaluator}
    {interface : Contexts.Interface} {term image : Contexts.Term lang interface}
    (inSorts : resultIn unquotedSorts interface.type = true)
    (fixed : contract image.1 = image.1) (dropFree : tokens dropLabel image.1 = 0)
    (related : (termSetoid base lang interface).r image term) : term = image := by
  apply Subtype.ext
  have same : contract term.1 = image.1 := (only.contract_eq related).symm.trans fixed
  rw [← same]
  exact (contract_of_dropFree names sorted term.2.1 inSorts term.2.2.2.1
    (by rw [same]; exact dropFree)).symm

/-- **Negative**: a dropped quotation in the subject of a run has two
spellings; the run of an atom need not be alone in its class. -/
theorem contained_run_spellings (base : BasePremiseEvaluator) :
    ∃ first second : Contexts.Term containedRun AtomsReduce.closedAtom,
      (termSetoid base containedRun AtomsReduce.closedAtom).r first second ∧ first ≠ second :=
  ⟨⟨runPattern emptySpace (dropped (quoted unitAtom)),
      checkOpenPatternWellSorted_sound (by decide +kernel)⟩,
    ⟨runPattern emptySpace (dropped (quoted (dropped (quoted unitAtom)))),
      checkOpenPatternWellSorted_sound (by decide +kernel)⟩,
    (contained_quoteDropOnly.termSetoid_iff contained_quoteDropSorted).mpr (by decide),
    fun same => absurd (congrArg Subtype.val same) (by decide)⟩

#print axioms contained_declaresRun
#print axioms scoped_declaresRun
#print axioms run_parts_wellSorted_in
#print axioms eq_run_of_contract_in
#print axioms runTermIn_related_iff
#print axioms eq_runTermIn_of_related
#print axioms eq_of_related_of_dropFree_in
#print axioms contained_run_spellings
#print axioms ambient_not_declaresRun
#print axioms run_wellSorted_in
#print axioms eq_runTermIn_of_val
#print axioms termSetoid_base_irrelevant_in

end Mettapedia.Logic.HostingStyles.AmbientRegions
