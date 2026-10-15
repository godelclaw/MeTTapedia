import Mettapedia.GSLT.Causality.Abstraction
import Mettapedia.GSLT.Core.SemanticImplementation
import Mettapedia.GSLT.Contexts.ContextMorphism
import Mettapedia.GSLT.Contexts.TransitionProfile
import Mettapedia.GSLT.Contexts.RelativeEquivalence
import Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes

/-!
# Operational realization with admitted interventions

An equation-class operational cover and an existing `InterventionMap` yield
a cover of saturated observations when their context square commutes at every
source state. All formulas in the translated language, including negations,
then preserve and reflect satisfaction. Their formula-generated OSLF native
types transport as well; no equivalence of the entire ambient topoi follows.

Transport of full counterfactual equivalence additionally requires coverage
of the target atoms and admitted contexts. This exposes the vocabulary
obligation instead of equating a cover of input tests with a cover of every
component intervention.

The bridge from `ContextMap.Hosting` supplies the operational and context
laws at an interface using the already proved hosting and equivariance laws.
It works with equations rather than equality of raw representatives. A
public macro-step relation can be used when host execution lowers one source
step to several internal steps; no micro-step equality is imposed here.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Causality.ContextualRealization

open Mettapedia.GSLT
open Mettapedia.GSLT.HennessyMilner
open Mettapedia.GSLT.IndexedOperational
open Mettapedia.GSLT.MinimalEnablingContext
open Mettapedia.GSLT.AdmissibleContextCongruence
open Mettapedia.GSLT.Causality.Abstraction

universe uS uT uM uC uC' uC'' uR uR' uR'' uA uA'

section Saturation

variable {S : GSLT.{uS}} {T : GSLT.{uT}}
  {sourceRules : ContextualRules.{uC, uR} S} {targetRules : ContextualRules.{uC', uR'} T}
  {A : AdmissibleClass sourceRules} {B : AdmissibleClass targetRules}
  (operational : SemanticCoveredTranslation S T) (interventions : InterventionMap A B)
  (sourceObservations : ContextualRules.Observations.{uA} S)
  (targetObservations : ContextualRules.Observations.{uA'} T)
  (mapAtom : sourceObservations.Atom → targetObservations.Atom)
  (atomLaw : ∀ atom term, sourceObservations.observes atom term ↔
    targetObservations.observes (mapAtom atom) (operational.mapTerm term))
  (square : ∀ ⦃context⦄, A.Admissible context → ∀ term,
    T.Equiv (operational.mapTerm (sourceRules.plug context term))
      (targetRules.plug (interventions.map context) (operational.mapTerm term)))

/-- Ordinary observations use the same independently justified operational
cover as the context-sensitive observations. -/
def passiveCover : SystemCover (Hierarchy.passive sourceObservations)
    (Hierarchy.passive targetObservations) :=
  operational.systemCover ⟨sourceObservations.Atom, sourceObservations.observes⟩
    ⟨targetObservations.Atom, targetObservations.observes⟩
    sourceObservations.observes_resp targetObservations.observes_resp mapAtom atomLaw

include atomLaw in
theorem association_iff (atomsOnto : Function.Surjective mapAtom) (left right : S.Term) :
    Hierarchy.Agree B targetObservations .association
        (operational.mapTerm left) (operational.mapTerm right) ↔
      Hierarchy.Agree A sourceObservations .association left right :=
  (Hierarchy.passive_bisimilar_iff B targetObservations _ _).symm.trans
    (((passiveCover operational sourceObservations targetObservations mapAtom atomLaw).bisimilar_map_iff
      atomsOnto (fun label => ⟨label, rfl⟩) left right).trans
        (Hierarchy.passive_bisimilar_iff A sourceObservations left right))

/-- Saturating an operational cover retains exactly its translated contexts
and observations, with outgoing reflection up to target equations. -/
def saturatedCover : SystemCover (A.saturated sourceObservations) (B.saturated targetObservations) where
  mapTerm := operational.mapTerm
  mapAtom atom := (mapAtom atom.1, interventions.label atom.2)
  mapLabel := interventions.label
  mapEquiv := operational.mapEquiv
  observes_iff atom term :=
    (atomLaw atom.1 (sourceRules.plug atom.2.1 term)).trans
      (targetObservations.observes_resp (mapAtom atom.1) (square atom.2.2 term))
  mapAct {label source target} step := by
    have image := operational.mapStep step
    obtain ⟨next, advances, equivalent⟩ := T.rewrites_resp_left (square label.2 source) image
    exact T.rewrites_resp_right advances (T.equations.iseqv.symm equivalent)
  liftAct {label source target} step := by
    obtain ⟨middle, advances, equivalent⟩ :=
      T.rewrites_resp_left (T.equations.iseqv.symm (square label.2 source)) step
    obtain ⟨next, sourceStep, mapped⟩ := operational.liftStep advances
    exact ⟨next, sourceStep, T.equations.iseqv.trans mapped
      (T.equations.iseqv.symm equivalent)⟩

include atomLaw square

theorem formula_iff (formula : Formula (A.saturated sourceObservations).Atom
    (A.saturated sourceObservations).Label) (term : S.Term) :
    (B.saturated targetObservations).sat
        (formula.map (saturatedCover operational interventions sourceObservations
          targetObservations mapAtom atomLaw square).mapAtom interventions.label)
        (operational.mapTerm term) ↔
      (A.saturated sourceObservations).sat formula term :=
  (saturatedCover operational interventions sourceObservations targetObservations
    mapAtom atomLaw square).sat_map formula term

/-- No target-vocabulary surjectivity is needed to reflect a distinction
already expressible through the source observation boundary. -/
theorem counterfactual_of_map {left right : S.Term}
    (related : Hierarchy.Agree B targetObservations .counterfactual
      (operational.mapTerm left) (operational.mapTerm right)) :
    Hierarchy.Agree A sourceObservations .counterfactual left right :=
  (saturatedCover operational interventions sourceObservations targetObservations
    mapAtom atomLaw square).bisimilar_of_map related

theorem counterfactual_iff (atomsOnto : Function.Surjective mapAtom)
    (contextsOnto : Function.Surjective interventions.label) (left right : S.Term) :
    Hierarchy.Agree B targetObservations .counterfactual
        (operational.mapTerm left) (operational.mapTerm right) ↔
      Hierarchy.Agree A sourceObservations .counterfactual left right := by
  apply (saturatedCover operational interventions sourceObservations targetObservations
    mapAtom atomLaw square).bisimilar_map_iff _ contextsOnto
  rintro ⟨atom, context⟩
  obtain ⟨sourceAtom, rfl⟩ := atomsOnto atom
  obtain ⟨sourceContext, rfl⟩ := contextsOnto context
  exact ⟨(sourceAtom, sourceContext), rfl⟩

/-- One-shot interventions transport by the operational cover and the
equation-class square, using every admitted target context. -/
theorem intervention_iff (atomsOnto : Function.Surjective mapAtom)
    (contextsOnto : Function.Surjective interventions.label) (left right : S.Term) :
    Hierarchy.Agree B targetObservations .intervention
        (operational.mapTerm left) (operational.mapTerm right) ↔
      Hierarchy.Agree A sourceObservations .intervention left right := by
  constructor
  · intro related context allowed
    apply (association_iff (A := A) (B := B) operational sourceObservations targetObservations
      mapAtom atomLaw atomsOnto _ _).mp
    exact reductionBisimilar_trans targetObservations
      (reductionBisimilar_of_equiv targetObservations (square allowed left))
      (reductionBisimilar_trans targetObservations
        (related (interventions.admissible allowed))
        (reductionBisimilar_of_equiv targetObservations
          (T.equations.iseqv.symm (square allowed right))))
  · intro related context allowed
    obtain ⟨⟨origin, admitted⟩, same⟩ := contextsOnto ⟨context, allowed⟩
    have image : interventions.map origin = context := congrArg Subtype.val same
    rw [← image]
    exact reductionBisimilar_trans targetObservations
      (reductionBisimilar_of_equiv targetObservations
        (T.equations.iseqv.symm (square admitted left)))
      (reductionBisimilar_trans targetObservations
        ((association_iff (A := A) (B := B) operational sourceObservations targetObservations
          mapAtom atomLaw atomsOnto _ _).mpr (related admitted))
        (reductionBisimilar_of_equiv targetObservations (square admitted right)))

theorem all_rungs_iff (atomsOnto : Function.Surjective mapAtom)
    (contextsOnto : Function.Surjective interventions.label)
    (rung : Hierarchy.Rung) (left right : S.Term) :
    Hierarchy.Agree B targetObservations rung (operational.mapTerm left) (operational.mapTerm right) ↔
      Hierarchy.Agree A sourceObservations rung left right := by
  cases rung with
  | association =>
      exact association_iff operational sourceObservations targetObservations mapAtom atomLaw atomsOnto left right
  | intervention =>
      exact intervention_iff operational interventions sourceObservations targetObservations
        mapAtom atomLaw square atomsOnto contextsOnto left right
  | counterfactual =>
      exact counterfactual_iff operational interventions sourceObservations targetObservations
        mapAtom atomLaw square atomsOnto contextsOnto left right

end Saturation

/-! ## Composition of the context square -/

section Composition

variable {S : GSLT.{uS}} {M : GSLT.{uM}} {T : GSLT.{uT}}
  {sourceRules : ContextualRules.{uC, uR} S}
  {middleRules : ContextualRules.{uC', uR'} M}
  {targetRules : ContextualRules.{uC'', uR''} T}
  {A : AdmissibleClass sourceRules} {B : AdmissibleClass middleRules}
  {C : AdmissibleClass targetRules}

theorem composed_square (earlier : SemanticCoveredTranslation S M)
    (later : SemanticCoveredTranslation M T)
    (first : InterventionMap A B) (second : InterventionMap B C)
    (firstSquare : ∀ ⦃context⦄, A.Admissible context → ∀ term,
      M.Equiv (earlier.mapTerm (sourceRules.plug context term))
        (middleRules.plug (first.map context) (earlier.mapTerm term)))
    (secondSquare : ∀ ⦃context⦄, B.Admissible context → ∀ term,
      T.Equiv (later.mapTerm (middleRules.plug context term))
        (targetRules.plug (second.map context) (later.mapTerm term)))
    {context : sourceRules.Context} (allowed : A.Admissible context) (term : S.Term) :
    T.Equiv ((earlier.comp later).mapTerm (sourceRules.plug context term))
      (targetRules.plug ((first.comp second).map context)
        ((earlier.comp later).mapTerm term)) :=
  T.equations.iseqv.trans (later.mapEquiv (firstSquare allowed term))
    (secondSquare (first.admissible allowed) (earlier.mapTerm term))

end Composition

/-! ## Hosting maps provide the contextual realization laws -/

section Hosting

universe u

variable {source target : ContextTheory.{u}} (map : ContextMap source target)

/-- A hosting map induces the existing equation-class operational cover at
each retained interface. The context information is not discarded. -/
def hostingOperational (hosting : map.Hosting) (origin : source.Interface) :
    SemanticCoveredTranslation (source.gslt origin) (target.gslt (map.interface origin)) where
  mapTerm := map.term
  mapEquiv := map.term_resp
  mapStep step := (map.preservesTransitions_iff_rewrites.mp hosting.preserves) step
  liftStep step := by
    obtain ⟨next, advances, equivalent⟩ :=
      (map.reflectsTransitions_iff_rewrites.mp hosting.reflects) step
    exact ⟨next, advances, (target.equations _).iseqv.symm equivalent⟩

def hostingInterventions (origin : source.Interface)
    (A : AdmissibleClass (source.contextualRules origin))
    (B : AdmissibleClass (target.contextualRules (map.interface origin)))
    (admitted : ∀ ⦃context⦄, A.Admissible context → B.Admissible (map.context context)) :
    InterventionMap A B where
  map := map.context
  admissible allowed := admitted allowed

/-- The actual hosting equivariance law proves the intervention square;
it is not an extra hypothesis on a separately invented context model. -/
theorem hosting_square (hosting : map.Hosting) (origin : source.Interface)
    (A : AdmissibleClass (source.contextualRules origin))
    (B : AdmissibleClass (target.contextualRules (map.interface origin)))
    (admitted : ∀ ⦃context⦄, A.Admissible context → B.Admissible (map.context context))
    (context : (source.contextualRules origin).Context) (term : source.Term origin) :
    (target.gslt (map.interface origin)).Equiv
      ((hostingOperational map hosting origin).mapTerm
        ((source.contextualRules origin).plug context term))
      ((target.contextualRules (map.interface origin)).plug
        ((hostingInterventions map origin A B admitted).map context)
        ((hostingOperational map hosting origin).mapTerm term)) := by
  change (target.equations (map.interface origin)).r
    (map.term (source.apply context term))
    (target.apply (map.context context) (map.term term))
  exact map.apply_equivariant context term

end Hosting

/-! ## Formula-generated native types -/

section NativeTypes

variable {S T : GSLT}
  {sourceRules : ContextualRules.{uC, uR} S} {targetRules : ContextualRules.{uC', uR'} T}
  {A : AdmissibleClass sourceRules} {B : AdmissibleClass targetRules}
  (operational : SemanticCoveredTranslation S T) (interventions : InterventionMap A B)
  (sourceObservations : ContextualRules.Observations.{uA} S)
  (targetObservations : ContextualRules.Observations.{uA'} T)
  (mapAtom : sourceObservations.Atom → targetObservations.Atom)
  (atomLaw : ∀ atom term, sourceObservations.observes atom term ↔
    targetObservations.observes (mapAtom atom) (operational.mapTerm term))
  (square : ∀ ⦃context⦄, A.Admissible context → ∀ term,
    T.Equiv (operational.mapTerm (sourceRules.plug context term))
      (targetRules.plug (interventions.map context) (operational.mapTerm term)))

theorem formulaNativeType_iff (formula : Formula (A.saturated sourceObservations).Atom
    (A.saturated sourceObservations).Label) (term : S.Term) :
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF T).satisfies (S := ())
      (operational.mapTerm term)
      (Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaNativeType
        (B.saturated targetObservations)
        (formula.map (saturatedCover operational interventions sourceObservations
          targetObservations mapAtom atomLaw square).mapAtom interventions.label)).pred ↔
    (Mettapedia.OSLF.Framework.GSLTTypeSynthesis.gsltOSLF S).satisfies (S := ()) term
      (Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.formulaNativeType
        (A.saturated sourceObservations) formula).pred :=
  Mettapedia.OSLF.Framework.HennessyMilnerNativeTypes.systemCover_formulaNativeType_iff
    (A.saturated sourceObservations)
    (saturatedCover operational interventions sourceObservations targetObservations
      mapAtom atomLaw square) formula term

end NativeTypes

end Mettapedia.GSLT.Causality.ContextualRealization
