import Mettapedia.Logic.HostingStyles.SpacesAndRegions.SealingSpaces
import Mettapedia.Logic.HostingStyles.SpacesAndRegions.Trees
import Mettapedia.Logic.HostingStyles.ReductionRank
import Mettapedia.GSLT.LanguageDef.ReflectiveWellSorted

/-!
# The sealed part of the candidate of spaces and regions

A term of the candidate is **sealed** (`SealedTerm`) when its contraction is
sealed with plain runs beneath the binders of its stage.  The contraction is
the normal form of the static equivalence, so equal terms are sealed together
(`sealedTerm_of_related`): sealing, read this way, is a property of the terms
of the theory.  A term that is sealed as it is written is sealed
(`sealedTerm_of_sealed`); the converse fails where a name is a variable
(`sealedTerm_not_literal`).  The terms that are sealed as they are written
are the terms of the reflective carrier of the pattern syntax at the profile
of structural names (`reflective_iff_sealedAt`).

* **The transitions of the candidate, at an ambient space whose contraction
  quotes only what was quoted, keep a term sealed**
  (`sealedTerm_of_termStep`), under every guard and at every interface.  The
  plain spaces are such spaces.
* **The sealed terms with their transitions are a part of the theory**
  (`sealedPart`): at each interface the sealed terms, with the static
  equivalence and the transitions of the candidate between them, and the
  contexts of the candidate that send sealed terms to a sealed term
  (`stepClosedPart`).  Its inclusion into the candidate is a hosting map
  (`sealedInclusion_hosting`): it reflects the static equivalence, and it
  preserves and reflects transitions; that it reflects them is that the part
  is closed under them.  What a sealed term reaches in the candidate it
  reaches in the part (`sealedPart_reaches_iff`).
* **The hypothesis on the ambient space is needed on terms too**
  (`sealedTerm_not_kept_at_quotingSpace`).
* **A run in the part** (`sealedTerm_run_iff`): the run of an atom in a space
  is sealed exactly when the contraction of the space is plain and the atom
  is sealed.  So containment holds inside the part: a transition of a sealed
  run is the run of a transition of its atom, between sealed atoms, in the
  member at the space of the run (`sealedPart_run_termStep_iff`).
* **Sealing does nothing to the step of a dropped quotation to itself**
  (`sealedPart_droppedQuotation_self`): the dropped quotation of a closed
  sealed atom is sealed in both of its spellings, and the release steps from
  one to the other.  The part has no rank (`sealedPart_not_rank`).
* **Hosting of a table survives on the part**, on terms
  (`sealedPart_hostOf_tabularAt`), and on terms read in runs at every ambient
  space whose contraction quotes only what was quoted
  (`sealedPart_hostOf_tabular_inRuns`): the atom of a term has no quotation
  and no run, and the space of a table is plain.  With contexts it survives
  in a reading of the part, in the module of the contexts of the sealed part.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.SpacesAndRegions

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.GSLT.LanguageDef.EquationSemantics
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory termSetoid TermStep)
open Mettapedia.GSLT.Dedukti (Theory RuleTable rewritingTheory)
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ScopedPattern
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.Languages.MeTTa
open Mettapedia.Languages.MeTTa.PrimeCandidates.LanguageDef
open Mettapedia.Languages.MeTTa.PrimeComparisons.HostingStyles
open Mettapedia.Logic.HostingStyles.AtomsReduce
  (atomAt atomInterface atomAt_wellSorted contract_atomAt tokens_atomAt releaseRule step_release
    step_lamBody contract_dropped contract_quoted contract_dropQuote_dropQuote contract_ruleSpace
    ruleSpace unquotedSorts BoundFirstOrder scopedRewriting AtomsFree)
open Mettapedia.Logic.HostingStyles.AmbientSpace
open Mettapedia.Logic.HostingStyles.AmbientRegions
open Mettapedia.Logic.HostingStyles.ContextReadings (tokens tokensList)

universe u

variable {admits : Pattern → Bool}

/-! ## A part of a theory that its steps keep -/

/-- **The part of a theory on the terms with a property that its steps
keep**: those terms, with the static equivalence and the steps of the theory
between them, and the contexts of the theory that send terms with the
property to a term with it.  Positive: the sealed part of the candidate at an
ambient space whose contraction quotes only what was quoted (`sealedPart`).
Negative: at the space of the rule `$0 ⟶ *@$0` the transitions do not keep
the sealed terms, so they are no such part there
(`sealedTerm_not_kept_at_quotingSpace`). -/
def stepClosedPart (theory : ContextTheory.{u})
    (holds : {interface : theory.Interface} → theory.Term interface → Prop)
    (closed : ∀ {interface : theory.Interface} {term next : theory.Term interface},
      holds term → theory.rewrites term next → holds next) : ContextTheory.{u} where
  Interface := theory.Interface
  Term := fun interface => { term : theory.Term interface // holds term }
  equations := fun interface =>
    { r := fun first second => (theory.equations interface).r first.1 second.1
      iseqv :=
        { refl := fun term => (theory.equations interface).iseqv.refl term.1
          symm := fun related => (theory.equations interface).iseqv.symm related
          trans := fun first second => (theory.equations interface).iseqv.trans first second } }
  rewrites := fun term next => theory.rewrites term.1 next.1
  rewrites_resp_left := by
    intro interface term term' next related step
    obtain ⟨reached, moved, same⟩ := theory.rewrites_resp_left related step
    exact ⟨⟨reached, closed term'.2 moved⟩, moved, same⟩
  rewrites_resp_right := fun step related => theory.rewrites_resp_right step related
  Context := fun {arity} holes result =>
    { context : theory.Context holes result //
        ∀ filling : (index : arity) → theory.Term (holes index),
          (∀ index, holds (filling index)) → holds (theory.fill context filling) }
  fill := fun context filling =>
    ⟨theory.fill context.1 fun index => (filling index).1,
      context.2 _ fun index => (filling index).2⟩
  fill_resp := fun context _ _ related => theory.fill_resp context.1 related
  identity := fun interface =>
    ⟨theory.identity interface, fun filling kept => by
      rw [theory.fill_identity]
      exact kept ()⟩
  fill_identity := fun interface filling =>
    Subtype.ext (theory.fill_identity interface fun index => (filling index).1)
  plug := fun context inner =>
    ⟨theory.plug context.1 fun index => (inner index).1, fun filling kept => by
      rw [theory.fill_plug]
      exact context.2 _ fun index => (inner index).2 _ fun position => kept ⟨index, position⟩⟩
  fill_plug := fun context inner filling =>
    Subtype.ext (theory.fill_plug context.1 (fun index => (inner index).1)
      fun position => (filling position).1)
  relabel := fun rename bijective context =>
    ⟨theory.relabel rename bijective context.1, fun filling kept => by
      rw [theory.fill_relabel]
      exact context.2 _ fun index => kept (rename index)⟩
  fill_relabel := fun rename bijective context filling =>
    Subtype.ext (theory.fill_relabel rename bijective context.1 fun index => (filling index).1)
  constant := fun term =>
    ⟨theory.constant term.1, fun filling _ => by
      rw [theory.fill_constant]
      exact term.2⟩
  fill_constant := fun term filling =>
    Subtype.ext (theory.fill_constant term.1 fun index => (filling index).1)

section Part

variable {theory : ContextTheory.{u}}
  {holds : {interface : theory.Interface} → theory.Term interface → Prop}
  {closed : ∀ {interface : theory.Interface} {term next : theory.Term interface},
    holds term → theory.rewrites term next → holds next}

/-- The inclusion of such a part into the theory. -/
def stepClosedPartInclusion (theory : ContextTheory.{u})
    (holds : {interface : theory.Interface} → theory.Term interface → Prop)
    (closed : ∀ {interface : theory.Interface} {term next : theory.Term interface},
      holds term → theory.rewrites term next → holds next) :
    ContextMap (stepClosedPart theory holds closed) theory where
  interface := fun interface => interface
  term := fun term => term.1
  context := fun context => context.1
  term_resp := fun related => related
  equivariant := fun _ _ => (theory.equations _).iseqv.refl _

/-- **The inclusion of a part that the steps keep is a hosting map**: it
reflects the static equivalence, and it preserves and reflects steps.  That
it reflects them is that the steps keep the property. -/
theorem stepClosedPartInclusion_hosting :
    (stepClosedPartInclusion theory holds closed).Hosting := by
  rw [ContextMap.hosting_iff, ContextMap.preservesTransitions_iff_rewrites,
    ContextMap.reflectsTransitions_iff_rewrites]
  refine ⟨fun related => related, fun step => step, ?_⟩
  intro interface term next step
  exact ⟨⟨next, closed term.2 step⟩, step, (theory.equations _).iseqv.refl next⟩

end Part

/-! ## Sealed terms -/

/-- **A sealed term of the candidate**: its contraction is sealed with plain
runs, beneath the binders of its stage. -/
def SealedTerm {interface : Contexts.Interface}
    (term : Contexts.Term spacesAndRegions interface) : Prop :=
  SealedWithPlainRuns interface.stage.length (contract term.1)

/-- **A term that is sealed with plain runs as it is written is sealed.** -/
theorem sealedTerm_of_sealed {interface : Contexts.Interface}
    {term : Contexts.Term spacesAndRegions interface}
    (kept : SealedWithPlainRuns interface.stage.length term.1) : SealedTerm term :=
  kept.contract

/-- More binders around a pattern keep it sealed with plain runs. -/
theorem SealedWithPlainRuns.mono {small large : Nat} {pattern : Pattern}
    (kept : SealedWithPlainRuns small pattern) (scope : small ≤ large) :
    SealedWithPlainRuns large pattern :=
  ⟨binderSafeAt_mono "prime-quote" kept.1 scope, kept.2⟩

/-- **The atom of a λΠ term is sealed with plain runs**, beneath the binders
it is beneath: it has no quotation and no run. -/
theorem sealedWithPlainRuns_atomAt (depth : Nat) (term : LF.Term) :
    SealedWithPlainRuns depth (atomAt depth term) := by
  have quiet : tokens quoteOrRun (atomAt depth term) = 0 :=
    tokens_atomAt (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) term depth
  have closed : (atomAt depth term).isWellScopedAt depth = true := by
    have sorted := (atomAt_wellSorted_of spacesAndRegions_carriesAtoms term depth).2.2.2
    rw [List.length_replicate] at sorted
    exact sorted
  exact ⟨sealedAt_of_wellScoped (counted := quoteOrRun) (by decide) _ depth closed quiet,
    runsPlain_of_tokens_eq_zero (counted := quoteOrRun) (by decide) _ quiet⟩

/-- **Positive**: the atom of a λΠ term, at every stage. -/
theorem sealedTerm_atom (depth : Nat) (term : LF.Term) :
    SealedTerm (atomTermIn (presentation := spacesAndRegionsPresentation)
      spacesAndRegions_carriesAtoms depth term) := by
  refine sealedTerm_of_sealed ?_
  show SealedWithPlainRuns (List.replicate depth (TypeExpr.base "Atom")).length (atomAt depth term)
  rw [List.length_replicate]
  exact sealedWithPlainRuns_atomAt depth term

/-- The abstraction whose body drops a quotation of its bound variable, as a
closed atom of the candidate. -/
def capturingTerm : Contexts.Term spacesAndRegions ⟨.base "Atom", []⟩ :=
  ⟨.apply "Lam" [unitAtom, .lambda none (dropped (quoted (.bvar 0)))],
    checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **Negative**: an abstraction whose body drops a quotation of its bound
variable. -/
theorem not_sealedTerm_capturing : ¬ SealedTerm capturingTerm :=
  fun kept => absurd kept.1 (by decide +kernel)

/-- **Equal terms are sealed together.** -/
theorem sealedTerm_of_related {base : BasePremiseEvaluator} {interface : Contexts.Interface}
    {first second : Contexts.Term spacesAndRegions interface}
    (related : (termSetoid base spacesAndRegions interface).r first second)
    (kept : SealedTerm first) : SealedTerm second := by
  unfold SealedTerm at kept ⊢
  rw [← spacesAndRegions_quoteDropOnly.contract_eq related]
  exact kept

/-- The quotation of the dropping of a name that is a variable, as a name at
the stage of one name. -/
def requotedName :
    Contexts.Term spacesAndRegions ⟨.base "CandidateName", [.base "CandidateName"]⟩ :=
  ⟨quoted (dropped (.bvar 0)), checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **A sealed term need not be sealed as it is written**: where a name is a
variable, the quotation of its dropping is equal to it, and has it beneath a
quotation. -/
theorem sealedTerm_not_literal :
    SealedTerm requotedName ∧ sealedAt 1 requotedName.1 = false :=
  ⟨⟨by decide +kernel, by decide +kernel⟩, by decide +kernel⟩

/-- **The terms that are sealed as they are written are the terms of the
reflective carrier of the pattern syntax**, at the profile whose one
presentation is that of structural names. -/
theorem reflective_iff_sealedAt {bound : List TypeExpr} {type : TypeExpr} {pattern : Pattern} :
    ReflectiveWellSorted.OpenPatternWellSorted { presentations := [reflectionPresentation] }
        spacesAndRegions FreeTypeContext.empty bound type pattern ↔
      OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty bound type pattern ∧
        sealedAt bound.length pattern = true := by
  simp [ReflectiveWellSorted.OpenPatternWellSorted, ReflectiveWellSorted.ReflectiveScopeSafeAt,
    reflectionPresentation, sealedAt]

/-! ## Transitions keep a term sealed, where the ambient space quotes only what was quoted -/

/-- **A transition of the candidate, at an ambient space whose contraction
quotes only what was quoted, keeps a term sealed**, under every guard and at
every interface. -/
theorem sealedTerm_of_termStep {ambientSpace : Pattern}
    (safe : QuotesOnlyQuoted (contract ambientSpace)) {interface : Contexts.Interface}
    {source target : Contexts.Term spacesAndRegions interface}
    (step : TermStep (regionEvaluator admits ambientSpace) spacesAndRegions source target)
    (kept : SealedTerm source) : SealedTerm target := by
  obtain ⟨redex, contractum, before, fired, after⟩ := step
  exact sealedTerm_of_related after
    (spacesAndRegions_step_sealedUpToStatics safe fired (sealedTerm_of_related before kept))

/-- The abstraction whose body mentions its bound variable outside every
quotation, as a closed atom of the candidate. -/
def mentioningTerm : Contexts.Term spacesAndRegions ⟨.base "Atom", []⟩ :=
  ⟨mentionsItsVariable, checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The abstraction whose body drops the quotation of that body, as a closed
atom of the candidate. -/
def quotingTerm : Contexts.Term spacesAndRegions ⟨.base "Atom", []⟩ :=
  ⟨quotesItsVariable, checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- **The hypothesis on the ambient space is needed**: at the space of the
rule `$0 ⟶ *@$0`, which is a space of the candidate, a sealed term has a
transition to a term that is not sealed. -/
theorem sealedTerm_not_kept_at_quotingSpace :
    OpenPatternWellSorted spacesAndRegions FreeTypeContext.empty [] (.base "Space") quotingSpace ∧
      SealedTerm mentioningTerm ∧
        TermStep (regionEvaluator anySubject quotingSpace) spacesAndRegions mentioningTerm
          quotingTerm ∧
          ¬ SealedTerm quotingTerm :=
  ⟨checkOpenPatternWellSorted_sound (by decide +kernel),
    sealedTerm_of_sealed quotingSpace_unseals.1,
    ⟨mentioningTerm, quotingTerm, Relation.EqvGen.refl _, quotingSpace_unseals.2.1,
      Relation.EqvGen.refl _⟩,
    fun kept => absurd kept.1 (by decide +kernel)⟩

/-! ## The sealed part -/

/-- **The sealed part of the candidate**, at an ambient space whose
contraction quotes only what was quoted: at each interface its sealed terms,
with the static equivalence and the transitions of the candidate between
them, and the contexts of the candidate that send sealed terms to a sealed
term. -/
def sealedPart (admits : Pattern → Bool) (ambientSpace : Pattern)
    (safe : QuotesOnlyQuoted (contract ambientSpace)) : ContextTheory.{0} :=
  stepClosedPart (spacesAndRegionsTheory admits ambientSpace) (fun term => SealedTerm term)
    (fun kept step => sealedTerm_of_termStep safe step kept)

/-- The inclusion of the sealed part into the candidate. -/
def sealedInclusion (admits : Pattern → Bool) (ambientSpace : Pattern)
    (safe : QuotesOnlyQuoted (contract ambientSpace)) :
    ContextMap (sealedPart admits ambientSpace safe) (spacesAndRegionsTheory admits ambientSpace) :=
  stepClosedPartInclusion (spacesAndRegionsTheory admits ambientSpace) (fun term => SealedTerm term)
    (fun kept step => sealedTerm_of_termStep safe step kept)

/-- **The sealed terms with their transitions are a part of the theory,
closed under its transitions**: the inclusion reflects the static
equivalence, and it preserves and reflects transitions.  A transition of the
candidate from a sealed term is a transition of the part. -/
theorem sealedInclusion_hosting (admits : Pattern → Bool) (ambientSpace : Pattern)
    (safe : QuotesOnlyQuoted (contract ambientSpace)) :
    (sealedInclusion admits ambientSpace safe).Hosting :=
  stepClosedPartInclusion_hosting

/-- **A reduction of the candidate from a sealed term is a reduction of the
sealed part, and conversely**: what a sealed term reaches in the candidate is
sealed, and it reaches it in the part. -/
theorem sealedPart_reaches_iff (admits : Pattern → Bool) (ambientSpace : Pattern)
    (safe : QuotesOnlyQuoted (contract ambientSpace)) {interface : Contexts.Interface}
    (source : (sealedPart admits ambientSpace safe).Term interface)
    (target : Contexts.Term spacesAndRegions interface) :
    (spacesAndRegionsTheory admits ambientSpace).Reaches source.1 target ↔
      ∃ kept : SealedTerm target,
        (sealedPart admits ambientSpace safe).Reaches source ⟨target, kept⟩ := by
  constructor
  · intro reaches
    induction reaches with
    | refl => exact ⟨source.2, .refl⟩
    | tail _ step ih =>
        obtain ⟨kept, reached⟩ := ih
        exact ⟨sealedTerm_of_termStep safe step kept, .tail reached step⟩
  · rintro ⟨kept, reaches⟩
    have lifted : ∀ {final : (sealedPart admits ambientSpace safe).Term interface},
        (sealedPart admits ambientSpace safe).Reaches source final →
          (spacesAndRegionsTheory admits ambientSpace).Reaches source.1 final.1 := by
      intro final reached
      induction reached with
      | refl => exact .refl
      | tail _ step ih => exact .tail ih step
    exact lifted reaches

/-! ## A run in the part -/

/-- **The run of an atom in a space is sealed exactly when the contraction of
the space is plain and the atom is sealed.** -/
theorem sealedTerm_run_iff {stage : List TypeExpr}
    (space : Contexts.Term spacesAndRegions ⟨.base "Space", stage⟩)
    (atom : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩) :
    SealedTerm (runTerm space atom) ↔ plainSpace (contract space.1) = true ∧ SealedTerm atom := by
  unfold SealedTerm
  rw [runTerm_val, runPattern, contract_apply_of_ne (by decide)]
  exact sealedWithPlainRuns_runPattern stage.length (contract space.1) (contract atom.1)

/-- **Containment inside the part**: a transition of a sealed run, at every
ambient space, is the run of a transition of its atom to a sealed atom in the
member at the space of the run, whose contraction is plain. -/
theorem sealedPart_run_termStep_iff {ambientSpace : Pattern} {stage : List TypeExpr}
    (space : Contexts.Term spacesAndRegions ⟨.base "Space", stage⟩)
    (atom target : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩)
    (kept : SealedTerm (runTerm space atom)) :
    TermStep (regionEvaluator admits ambientSpace) spacesAndRegions (runTerm space atom) target ↔
      plainSpace (contract space.1) = true ∧ SealedTerm atom ∧
        ∃ next : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩, SealedTerm next ∧
          TermStep (regionEvaluator admits space.1) spacesAndRegions atom next ∧
            (termSetoid (regionEvaluator admits ambientSpace) spacesAndRegions
              ⟨.base "Atom", stage⟩).r target (runTerm space next) := by
  obtain ⟨plainRun, keptAtom⟩ := (sealedTerm_run_iff space atom).mp kept
  rw [show runTerm space atom = runTermIn spacesAndRegions_declaresRun space atom from rfl,
    spacesAndRegions_run_termStep_iff]
  constructor
  · rintro ⟨next, moved, related⟩
    exact ⟨plainRun, keptAtom, next,
      sealedTerm_of_termStep (quotesOnlyQuoted_of_plainSpace plainRun) moved keptAtom, moved,
      related⟩
  · rintro ⟨-, -, next, -, moved, related⟩
    exact ⟨next, moved, related⟩

/-! ## The step of a dropped quotation to itself -/

/-- The unit atom, as a closed atom of the candidate. -/
def unitTerm : Contexts.Term spacesAndRegions ⟨.base "Atom", []⟩ :=
  ⟨unitAtom, checkOpenPatternWellSorted_sound (by decide +kernel)⟩

/-- The dropping of the quotation of an atom, as an atom of the candidate. -/
def dropQuoteTerm {stage : List TypeExpr}
    (atom : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩) :
    Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩ :=
  ⟨dropped (quoted atom.1),
    wellSorted_apply_one (lang := spacesAndRegions) (label := "prime-drop") (category := "Atom")
      (name := "name") (sort := "CandidateName") (by decide)
      (wellSorted_apply_one (lang := spacesAndRegions) (label := "prime-quote")
        (category := "CandidateName") (name := "term") (sort := "Atom") (by decide) atom.2)⟩

/-- **Every dropped quotation of the candidate has a transition to itself**,
under every evaluator: the equation writes it as the dropped quotation of
itself, which the release steps back to it. -/
theorem droppedQuotation_self_step {base : BasePremiseEvaluator} {stage : List TypeExpr}
    (atom : Contexts.Term spacesAndRegions ⟨.base "Atom", stage⟩) :
    TermStep base spacesAndRegions (dropQuoteTerm atom) (dropQuoteTerm atom) :=
  ⟨dropQuoteTerm (dropQuoteTerm atom), dropQuoteTerm atom,
    (spacesAndRegions_quoteDropOnly.termSetoid_iff spacesAndRegions_quoteDropSorted).mpr
      (contract_dropQuote_dropQuote atom.1).symm,
    ⟨1, step_release
      (by rw [show spacesAndRegions.rewrites = allHeaded.rewrites from spacesAndRegions_rewrites]
          exact allHeaded_mem_plain (by simp)) (dropped (quoted atom.1))⟩,
    Relation.EqvGen.refl _⟩

/-- **The dropped quotation of a closed sealed atom is sealed, in both of its
spellings.**  Sealing asks that the atom of a quotation be closed; the
dropped quotation of a closed atom is closed. -/
theorem sealedTerm_dropQuote {atom : Contexts.Term spacesAndRegions ⟨.base "Atom", []⟩}
    (kept : SealedTerm atom) :
    SealedTerm (dropQuoteTerm atom) ∧ SealedTerm (dropQuoteTerm (dropQuoteTerm atom)) := by
  have once : SealedTerm (dropQuoteTerm atom) := by
    unfold SealedTerm at kept ⊢
    show SealedWithPlainRuns 0 (contract (dropped (quoted atom.1)))
    rw [contract_dropped, contract_quoted]
    rcases contractRoot_quote_cases (contract atom.1) with ⟨name, isDrop, value⟩ | same
    · rw [value]
      rw [isDrop] at kept
      exact kept
    · rw [same]
      refine (sealedWithPlainRuns_apply_iff (label := "prime-drop") (by decide) 0 _).mpr ?_
      intro argument member
      rw [List.mem_singleton.mp member]
      exact ⟨by rw [show Pattern.apply "prime-quote" [contract atom.1] = quoted (contract atom.1)
          from rfl, sealedAt_quoted]; exact kept.1,
        (runsPlain_apply_of_ne (by decide) _).mpr fun inner inside => by
          rw [List.mem_singleton.mp inside]; exact kept.2⟩
  refine ⟨once, ?_⟩
  unfold SealedTerm at once ⊢
  show SealedWithPlainRuns 0 (contract (dropped (quoted (dropped (quoted atom.1)))))
  rw [contract_dropQuote_dropQuote]
  exact once

/-- **Sealing does nothing to the step of a dropped quotation to itself**:
it is a transition of the sealed part. -/
theorem sealedPart_droppedQuotation_self (admits : Pattern → Bool) (ambientSpace : Pattern)
    (safe : QuotesOnlyQuoted (contract ambientSpace))
    {atom : Contexts.Term spacesAndRegions ⟨.base "Atom", []⟩} (kept : SealedTerm atom) :
    (sealedPart admits ambientSpace safe).rewrites (interface := ⟨.base "Atom", []⟩)
      ⟨dropQuoteTerm atom, (sealedTerm_dropQuote kept).1⟩
      ⟨dropQuoteTerm atom, (sealedTerm_dropQuote kept).1⟩ :=
  droppedQuotation_self_step atom

/-- **The sealed part has no rank**: the dropped quotation of the unit atom
is sealed, and it has a transition to itself. -/
theorem sealedPart_not_rank (admits : Pattern → Bool) (ambientSpace : Pattern)
    (safe : QuotesOnlyQuoted (contract ambientSpace)) :
    IsEmpty (sealedPart admits ambientSpace safe).Rank :=
  ⟨fun ranked => ranked.not_cycle (.single (sealedPart_droppedQuotation_self admits ambientSpace
    safe (atom := unitTerm) ⟨by decide +kernel, by decide +kernel⟩))⟩

/-! ## Hosting of a table survives on the part -/

/-- The contraction of the space of a table is plain. -/
theorem plainSpace_contract_tableSpace (table : RuleTable) :
    plainSpace (contract (tableSpace table).1) = true := by
  show plainSpace (contract (ruleSpace table.toList)) = true
  rw [contract_ruleSpace]
  exact plainSpace_ruleSpace table.toList

/-- So it quotes only what was quoted: it stores no quotation. -/
theorem quotesOnlyQuoted_contract_tableSpace (table : RuleTable) :
    QuotesOnlyQuoted (contract (tableSpace table).1) :=
  quotesOnlyQuoted_of_plainSpace (plainSpace_contract_tableSpace table)

/-- **Hosting of a table survives on the sealed part**: at the space of a
table of first-order rules with bound right sides none of whose left sides is
a variable, the sealed part of the candidate is a host, on terms, of the
theories given by that table. -/
theorem sealedPart_hostOf_tabularAt (admitsAtoms : AdmitsAtoms admits) {table : RuleTable}
    (admitted : BoundFirstOrder table)
    (headed : ∀ rule ∈ table, ∀ index : Nat, rule.lhs ≠ .var index) :
    HostOf (sealedPart admits (tableSpace table).1 (quotesOnlyQuoted_contract_tableSpace table))
      (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
      .terms .hosting := by
  rintro reading ⟨source, ⟨theory, tabular, rfl⟩, interface, rfl⟩
  have steps : ∀ {depth : Nat} {source : LF.Term} {target : Pattern},
      Step (regionEvaluator admits (tableSpace table).1) spacesAndRegions (atomAt depth source)
          target ↔
        ∃ next, target = atomAt depth next ∧ Dedukti.Step theory source next :=
    spacesAndRegions_atom_step_iff admitsAtoms admitted.listed.1 admitted.listed.2
      (fun rule member => headed rule (Finset.mem_toList.mp member))
      (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined
  have transitions := fun (source : LF.Term)
      (target : Contexts.Term spacesAndRegions (atomInterface 0)) =>
    termStep_atomTermIn_iff (presentation := spacesAndRegionsPresentation)
      spacesAndRegions_carriesAtoms spacesAndRegions_quoteDropOnly spacesAndRegions_quoteDropSorted
      spacesAndRegions_namesOnlyDropped steps (depth := 0) (source := source) (target := target)
  let image : LF.Term → (sealedPart admits (tableSpace table).1
      (quotesOnlyQuoted_contract_tableSpace table)).Term (atomInterface 0) := fun term =>
    ⟨atomTermIn (presentation := spacesAndRegionsPresentation) spacesAndRegions_carriesAtoms 0 term,
      sealedTerm_atom 0 term⟩
  have respects : ∀ {first second : LF.Term},
      ((rewritingTheory theory).gslt ()).equations.r first second →
        ((sealedPart admits (tableSpace table).1
          (quotesOnlyQuoted_contract_tableSpace table)).equations
          (atomInterface 0)).r (image first) (image second) := by
    intro first second related
    have same : first = second := related
    rw [same]
  refine ⟨ContextMap.ofTerms (source := (rewritingTheory theory).gslt ())
    (target := sealedPart admits (tableSpace table).1 (quotesOnlyQuoted_contract_tableSpace table))
    (atomInterface 0) image respects, ?_⟩
  refine (ContextMap.ofTerms_hosting_iff (source := (rewritingTheory theory).gslt ())
    (target := sealedPart admits (tableSpace table).1 (quotesOnlyQuoted_contract_tableSpace table))
    (atomInterface 0) image respects).mpr ⟨?_, ?_, ?_⟩
  · intro first second related
    have same := eq_atomTermIn_of_related (presentation := spacesAndRegionsPresentation)
      spacesAndRegions_carriesAtoms spacesAndRegions_quoteDropOnly spacesAndRegions_quoteDropSorted
      spacesAndRegions_namesOnlyDropped
      (base := regionEvaluator admits (tableSpace table).1) (depth := 0) related
    exact (atomTermIn_injective spacesAndRegions_carriesAtoms 0 same).symm
  · intro first next step
    exact (transitions first _).mpr ⟨next, step, rfl⟩
  · intro first next step
    obtain ⟨reached, sourceStep, same⟩ := (transitions first next.1).mp step
    refine ⟨reached, sourceStep, ?_⟩
    show (termSetoid (regionEvaluator admits (tableSpace table).1) spacesAndRegions
      (atomInterface 0)).r next.1 (image reached).1
    rw [same]
    exact Relation.EqvGen.refl _

/-- **The run of the atom of a λΠ term in the space of a list of rules is a
sealed term**, at every stage. -/
theorem sealedTerm_runAtom (rules : List Dedukti.RewriteRule) (depth : Nat) (term : LF.Term) :
    SealedTerm (runAtomIn (presentation := spacesAndRegionsPresentation)
      spacesAndRegions_declaresRun spacesAndRegions_carriesAtoms rules depth term) := by
  show SealedWithPlainRuns (List.replicate depth (TypeExpr.base "Atom")).length
    (contract (runPattern (ruleSpace rules) (atomAt depth term)))
  rw [contract_runAtom, List.length_replicate]
  exact (sealedWithPlainRuns_runPattern depth (ruleSpace rules) (atomAt depth term)).mpr
    ⟨plainSpace_ruleSpace rules, sealedWithPlainRuns_atomAt depth term⟩

/-- **In runs, at every ambient space whose contraction quotes only what was
quoted**: the sealed part is a host, on terms, of the theories of a table of
first-order rules with bound right sides none of whose left sides is a
variable, each term read as the run of its atom in the space of the table. -/
theorem sealedPart_hostOf_tabular_inRuns (admitsAtoms : AdmitsAtoms admits)
    (ambientSpace : Pattern) (safe : QuotesOnlyQuoted (contract ambientSpace))
    {table : RuleTable} (admitted : BoundFirstOrder table)
    (headed : ∀ rule ∈ table, ∀ index : Nat, rule.lhs ≠ .var index) :
    HostOf (sealedPart admits ambientSpace safe)
      (fun source => ∃ theory : Theory, theory.Tabular table ∧ source = rewritingTheory theory)
      .terms .hosting := by
  rintro reading ⟨source, ⟨theory, tabular, rfl⟩, interface, rfl⟩
  have steps : ∀ {depth : Nat} {source : LF.Term} {target : Pattern},
      Step (regionEvaluator admits ambientSpace) spacesAndRegions
          (runPattern (ruleSpace table.toList) (atomAt depth source)) target ↔
        ∃ next, target = runPattern (ruleSpace table.toList) (atomAt depth next) ∧
          Dedukti.Step theory source next :=
    spacesAndRegions_runAtom_step_iff admitsAtoms ambientSpace admitted.listed.1 admitted.listed.2
      (fun rule member => headed rule (Finset.mem_toList.mp member))
      (fun rule => (tabular.rules rule).trans Finset.mem_toList.symm) tabular.undefined
  have transitions := fun (source : LF.Term)
      (target : Contexts.Term spacesAndRegions (atomInterface 0)) =>
    termStep_runAtomIn_iff (presentation := spacesAndRegionsPresentation)
      spacesAndRegions_declaresRun spacesAndRegions_carriesAtoms spacesAndRegions_quoteDropOnly
      spacesAndRegions_quoteDropSorted spacesAndRegions_namesOnlyDropped steps (depth := 0)
      (source := source) (target := target)
  let image : LF.Term → (sealedPart admits ambientSpace safe).Term (atomInterface 0) :=
    fun term =>
      ⟨runAtomIn (presentation := spacesAndRegionsPresentation) spacesAndRegions_declaresRun
          spacesAndRegions_carriesAtoms table.toList 0 term,
        sealedTerm_runAtom table.toList 0 term⟩
  have respects : ∀ {first second : LF.Term},
      ((rewritingTheory theory).gslt ()).equations.r first second →
        ((sealedPart admits ambientSpace safe).equations (atomInterface 0)).r (image first)
          (image second) := by
    intro first second related
    have same : first = second := related
    rw [same]
  refine ⟨ContextMap.ofTerms (source := (rewritingTheory theory).gslt ())
    (target := sealedPart admits ambientSpace safe) (atomInterface 0) image respects, ?_⟩
  refine (ContextMap.ofTerms_hosting_iff (source := (rewritingTheory theory).gslt ())
    (target := sealedPart admits ambientSpace safe) (atomInterface 0) image respects).mpr
    ⟨?_, ?_, ?_⟩
  · intro first second related
    have same := eq_runAtomIn_of_related (presentation := spacesAndRegionsPresentation)
      spacesAndRegions_declaresRun spacesAndRegions_carriesAtoms spacesAndRegions_quoteDropOnly
      spacesAndRegions_quoteDropSorted spacesAndRegions_namesOnlyDropped
      (base := regionEvaluator admits ambientSpace) (rules := table.toList) (depth := 0) related
    exact (runAtomIn_injective spacesAndRegions_declaresRun spacesAndRegions_carriesAtoms
      table.toList 0 same).symm
  · intro first next step
    exact (transitions first _).mpr ⟨next, step, rfl⟩
  · intro first next step
    obtain ⟨reached, sourceStep, same⟩ := (transitions first next.1).mp step
    refine ⟨reached, sourceStep, ?_⟩
    show (termSetoid (regionEvaluator admits ambientSpace) spacesAndRegions (atomInterface 0)).r
      next.1 (image reached).1
    rw [same]
    exact Relation.EqvGen.refl _

#print axioms stepClosedPart
#print axioms sealedTerm_of_sealed
#print axioms sealedTerm_atom
#print axioms not_sealedTerm_capturing
#print axioms sealedTerm_of_related
#print axioms sealedTerm_not_literal
#print axioms reflective_iff_sealedAt
#print axioms sealedTerm_of_termStep
#print axioms sealedTerm_not_kept_at_quotingSpace
#print axioms stepClosedPartInclusion_hosting
#print axioms sealedPart
#print axioms sealedInclusion
#print axioms sealedInclusion_hosting
#print axioms sealedPart_reaches_iff
#print axioms sealedTerm_run_iff
#print axioms sealedPart_run_termStep_iff
#print axioms droppedQuotation_self_step
#print axioms sealedTerm_dropQuote
#print axioms sealedPart_droppedQuotation_self
#print axioms sealedPart_not_rank
#print axioms plainSpace_contract_tableSpace
#print axioms sealedPart_hostOf_tabularAt
#print axioms sealedTerm_runAtom
#print axioms sealedPart_hostOf_tabular_inRuns

end Mettapedia.Logic.HostingStyles.SpacesAndRegions
