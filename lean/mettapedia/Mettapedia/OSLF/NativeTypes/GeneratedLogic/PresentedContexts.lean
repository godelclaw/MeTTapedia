import Mettapedia.OSLF.NativeTypes.GeneratedLogic.ContextLabels
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.LocalDriverReading
import Mettapedia.GSLT.LanguageDef.Contexts.Structural
import Mettapedia.GSLT.Contexts.ContextHennessyMilner

/-!
# The presented context theory's transitions are the front door's context steps

A language presents a theory of contexts (`LanguageDef.Contexts.contextTheory`): its interfaces are types with the
binders in scope, its contexts are linear patterns with holes, and a one-hole context is a label whose transitions say
that the term placed in it steps. The front door's context labels place a term in a pattern at a metavariable.

- **In an equation-free language a presented step is a step of the least contextual relation**
  (`Contexts.termStep_iff_step`).
- **Placing a closed term at a fresh metavariable is filling the hole** (`plug_fill`, in `ContextLabels`).
- **So, in an equation-free language whose rules are aligned with the reference relation, a presented transition
  between states is the front door's context step** (`transition_iff`): the label's one-hole shape, with its hole
  written as a metavariable, is the context label. Between closed interfaces every term is a state
  (`isState_of_closed`), so there the two are the same transitions (`transition_iff_closed`).

The presented theory's bisimilarity, as any probe sees it, is characterized by the probe's modal formulas when steps are
finitely many up to the equations (`ContextTheory.bisimilar_iff_agree`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresentedContexts

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Engine (RelationEnv)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (engineBasePremises)
open Mettapedia.OSLF.MeTTaIL.DerivedContexts (OneHoleContext)
open Mettapedia.OSLF.MeTTaIL.ReferenceStep (ReferenceProfile contextualStep_iff_step)
open Mettapedia.GSLT.LanguageDef (ValidatedLanguageDef)
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory TermStep Interface Term termStep_iff_step)
open Mettapedia.OSLF.NativeTypes.GeneratedLogic.LocalReading (reference_step_any_iff)

variable {relEnv : RelationEnv} {presentation : ValidatedLanguageDef}

/-- **A term of a closed interface is a state**: well-sorted terms are object terms, scoped by their stage. -/
theorem isState_of_closed {interface : Interface} (closed : interface.stage = [])
    (term : Term presentation.language interface) : IsState term.1 := by
  obtain ⟨-, -, object, scopeSafe⟩ := term.2
  refine ⟨?_, object⟩
  have length : interface.stage.length = 0 := by rw [closed]; rfl
  have : term.1.isWellScopedAt interface.stage.length = true := scopeSafe
  rwa [length] at this

/-- **A presented transition between states is the front door's context step**, in an equation-free language whose
rules are aligned with the reference relation: the label's one-hole shape, with its hole written as a fresh
metavariable, is the context label. -/
theorem transition_iff (free : presentation.language.isEquationFree = true)
    (profile : ReferenceProfile presentation.language) {source target : Interface}
    (label : (contextTheory (engineBasePremises relEnv) presentation).Label source target)
    {hole : String} {context : OneHoleContext} (avoids : contextAvoidsHole hole context = true)
    (shape : ∀ term, ((contextTheory (engineBasePremises relEnv) presentation).apply label term).1 =
      context.fill term.1)
    {term : Term presentation.language source} {next : Term presentation.language target}
    (termState : IsState term.1) (placedState : IsState (context.fill term.1)) (nextState : IsState next.1) :
    (contextTheory (engineBasePremises relEnv) presentation).Transition term label next ↔
      (referenceStructure relEnv presentation.language).step term.1
        (.context hole (context.fill (.fvar hole)) .any) next.1 := by
  rw [step_context_iff_plug (congruent_of_isEquationFree free hole _) termState, plug_fill context avoids termState.1,
    reference_step_any_iff free]
  change TermStep _ _ ((contextTheory (engineBasePremises relEnv) presentation).apply label term) next ↔ _
  refine (termStep_iff_step (engineBasePremises relEnv) presentation.language free
    ((contextTheory (engineBasePremises relEnv) presentation).apply label term) next).trans ?_
  have filled : ((contextTheory (engineBasePremises relEnv) presentation).apply label term).1 = context.fill term.1 :=
    shape term
  rw [filled, contextualStep_iff_step relEnv presentation.language profile]
  exact ⟨fun step => ⟨placedState, nextState, step⟩, fun ⟨_, _, step⟩ => step⟩

/-- **Between closed interfaces a presented transition is the front door's context step.** -/
theorem transition_iff_closed (free : presentation.language.isEquationFree = true)
    (profile : ReferenceProfile presentation.language) {source target : Interface} (sourceClosed : source.stage = [])
    (targetClosed : target.stage = [])
    (label : (contextTheory (engineBasePremises relEnv) presentation).Label source target)
    {hole : String} {context : OneHoleContext} (avoids : contextAvoidsHole hole context = true)
    (shape : ∀ term, ((contextTheory (engineBasePremises relEnv) presentation).apply label term).1 =
      context.fill term.1)
    (term : Term presentation.language source) (next : Term presentation.language target) :
    (contextTheory (engineBasePremises relEnv) presentation).Transition term label next ↔
      (referenceStructure relEnv presentation.language).step term.1
        (.context hole (context.fill (.fvar hole)) .any) next.1 :=
  transition_iff free profile label avoids shape (isState_of_closed sourceClosed term)
    (shape term ▸ isState_of_closed targetClosed ((contextTheory (engineBasePremises relEnv) presentation).apply label term))
    (isState_of_closed targetClosed next)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.PresentedContexts
