import Mettapedia.GSLT.Core.ProofRelevantGSLT
import Mathlib.CategoryTheory.Yoneda

/-!
# The category of proof-relevant GSLTs

A proof-relevant translation retains three pieces of executable structure:
the term map, the forward evidence map, and the local lifting algorithm.  This
module proves that the existing identity and composition operations satisfy
the category laws without quotienting any of those algorithms.

The equality of translations is therefore intentionally stronger than
equality of their proposition-valued operational shadows.  The functor
`forgetEvidence` performs that explicit erasure only after the category has
been constructed.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ProofRelevant

open CategoryTheory
open Mettapedia.GSLT.IndexedOperational

universe u

/-- Extensionality for proof-relevant translations includes both executable
evidence maps.  The equation-respect field is proof-irrelevant. -/
theorem Translation.ext_data
    {source target : ProofRelevantGSLT.{u}}
    {left right : Translation source target}
    (mapTerm : left.mapTerm = right.mapTerm)
    (mapEvidence : HEq (@Translation.mapEvidence _ _ left)
      (@Translation.mapEvidence _ _ right))
    (liftEvidence : HEq (@Translation.liftEvidence _ _ left)
      (@Translation.liftEvidence _ _ right)) :
    left = right := by
  cases left
  cases right
  cases mapTerm
  cases mapEvidence
  cases liftEvidence
  rfl

/-- Composing identity before a proof-relevant translation retains its chosen
lifting algorithm exactly. -/
theorem Translation.identity_comp
    {source target : ProofRelevantGSLT.{u}}
    (route : Translation source target) :
    Translation.comp (Translation.id source) route = route := by
  cases route with
  | mk mapTerm mapEquiv mapEvidence liftEvidence =>
    apply Translation.ext_data
    · rfl
    · rfl
    · apply heq_of_eq
      funext sourceTerm targetTerm targetEvidence
      obtain ⟨sourceTarget, sourceEvidence, endpoint⟩ :=
        liftEvidence targetEvidence
      rcases endpoint with ⟨⟨endpoint⟩⟩
      subst targetTerm
      simp [Translation.comp, Translation.id]

/-- Composing identity after a proof-relevant translation retains its chosen
lifting algorithm exactly. -/
theorem Translation.comp_identity
    {source target : ProofRelevantGSLT.{u}}
    (route : Translation source target) :
    Translation.comp route (Translation.id target) = route := by
  apply Translation.ext_data <;> rfl

/-- Proof-relevant translation composition is associative, including the
selected evidence returned by the three local lifting algorithms. -/
theorem Translation.comp_assoc
    {first second third fourth : ProofRelevantGSLT.{u}}
    (one : Translation first second)
    (two : Translation second third)
    (three : Translation third fourth) :
    Translation.comp (Translation.comp one two) three =
      Translation.comp one (Translation.comp two three) := by
  apply Translation.ext_data
  · rfl
  · rfl
  · apply heq_of_eq
    funext sourceTerm targetTerm targetEvidence
    obtain ⟨laterTarget, laterEvidence, laterEndpoint⟩ :=
      three.liftEvidence targetEvidence
    obtain ⟨middleTarget, middleEvidence, middleEndpoint⟩ :=
      two.liftEvidence laterEvidence
    obtain ⟨sourceTarget, sourceEvidence, sourceEndpoint⟩ :=
      one.liftEvidence middleEvidence
    rcases laterEndpoint with ⟨⟨laterEndpoint⟩⟩
    subst targetTerm
    rcases middleEndpoint with ⟨⟨middleEndpoint⟩⟩
    subst laterTarget
    rcases sourceEndpoint with ⟨⟨sourceEndpoint⟩⟩
    subst middleTarget
    simp [Translation.comp]

/-- Proof-relevant GSLTs and their two-sided evidence translations form a
category before any occurrence evidence is erased. -/
instance proofRelevantGSLTCategory :
    CategoryTheory.Category (ProofRelevantGSLT.{u}) where
  Hom := Translation
  id := Translation.id
  comp earlier later := Translation.comp earlier later
  id_comp := Translation.identity_comp
  comp_id := Translation.comp_identity
  assoc := Translation.comp_assoc

/-- Retained primitive events form a covariant functor out of the category of
proof-relevant GSLTs.  This is the categorical action shared by occurrence
indices, observation disciplines, biform meanings, and accounting ledgers. -/
def eventFunctor : ProofRelevantGSLT.{u} ⥤ Type u where
  obj system := system.Event
  map translation := TypeCat.ofHom translation.mapEvent
  map_id system := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext event
    exact Translation.mapEvent_id event
  map_comp earlier later := by
    apply TypeCat.Hom.ext
    apply TypeCat.Fun.ext
    funext event
    exact Translation.mapEvent_comp earlier later event

/-- Erasing occurrence evidence is a functor to the existing category of
locally covered proposition-valued GSLTs. -/
def forgetEvidence : ProofRelevantGSLT.{u} ⥤ CoveredTheory.{u} where
  obj system := ⟨system.theory⟩
  map translation := translation.toCovered
  map_id _ := by
    apply CoveredTranslation.ext
    rfl
  map_comp _ _ := by
    apply CoveredTranslation.ext
    rfl

/-! ## Complete probes and an occurrence-erasing boundary -/

namespace OccurrenceControls

/-- A genuine transition with two differently labeled occurrences. -/
def parallelEvents : ProofRelevantGSLT where
  theory := {
    Term := Bool
    equations := ⟨Eq, ⟨Eq.refl, Eq.symm, Eq.trans⟩⟩
    rewrites source target := source = false ∧ target = true
    rewrites_resp_left := by
      intro source source' target equal event
      subst source'
      exact ⟨target, event, rfl⟩
    rewrites_resp_right := by
      intro source target target' event equal
      subst target'
      exact event }
  steps := {
    Evidence := fun source target => {label : Bool // source = false ∧ target = true}
    erases_iff := by
      intro source target
      exact ⟨fun ⟨event⟩ => event.property, fun step => ⟨⟨false, step⟩⟩⟩ }

/-- Change occurrence labels without changing endpoints or the enabled graph. -/
def exchange : parallelEvents ⟶ parallelEvents where
  mapTerm := id
  mapEquiv := fun equal => equal
  mapEvidence event := ⟨!event.val, event.property⟩
  liftEvidence := fun {_source target} event =>
    ⟨target, ⟨!event.val, event.property⟩, ⟨⟨rfl⟩⟩⟩

def firstEvent : parallelEvents.Event := ⟨false, true, ⟨false, rfl, rfl⟩⟩

theorem exchange_changes_occurrence :
    exchange.mapEvent firstEvent ≠ (𝟙 parallelEvents : parallelEvents ⟶ parallelEvents).mapEvent
      firstEvent := by
  intro same
  have labels := congrArg (fun event : parallelEvents.Event => event.evidence.val) same
  change true = false at labels
  cases labels

theorem exchange_ne_identity : exchange ≠ 𝟙 parallelEvents := by
  intro same
  exact exchange_changes_occurrence (congrArg (fun route => route.mapEvent firstEvent) same)

theorem exchange_twice : exchange ≫ exchange = 𝟙 parallelEvents := by
  apply Translation.ext_data
  · rfl
  · apply heq_of_eq
    funext source target event
    apply Subtype.ext
    exact Bool.not_not event.val
  · apply heq_of_eq
    funext source target event
    rcases event with ⟨label, valid⟩
    cases label <;> rfl

/-- The endpoint interface cannot detect this nontrivial notation change. -/
theorem forget_exchange_eq_identity :
    forgetEvidence.map exchange = forgetEvidence.map (𝟙 parallelEvents) := by
  apply CoveredTranslation.ext
  rfl

/-- Erasing occurrence data is a lawful functor but is not a faithful one. -/
theorem forgetEvidence_not_faithful : ¬ forgetEvidence.{0}.Faithful := by
  intro faithful
  exact exchange_ne_identity (faithful.map_injective forget_exchange_eq_identity)

/-- Complete representable probes retain the lost distinction. In particular,
the probe from this system to itself can supply its identity translation. -/
theorem full_probes_separate_exchange :
    yoneda.map exchange ≠ yoneda.map (𝟙 parallelEvents) := by
  intro same
  exact exchange_ne_identity (yoneda.map_injective same)

/-- An isomorphism of the full representable interfaces reconstructs an
isomorphism in this occurrence-sensitive category. This is relative to the
declared objects and arrows; it says nothing about an omitted physical or
phenomenal structure. -/
noncomputable def reconstruct (first second : ProofRelevantGSLT.{u})
    (comparison : yoneda.obj first ≅ yoneda.obj second) : first ≅ second :=
  Yoneda.fullyFaithful.preimageIso comparison

end OccurrenceControls

#print axioms Translation.ext_data
#print axioms Translation.identity_comp
#print axioms Translation.comp_identity
#print axioms Translation.comp_assoc
#print axioms eventFunctor
#print axioms forgetEvidence

end Mettapedia.GSLT.ProofRelevant
