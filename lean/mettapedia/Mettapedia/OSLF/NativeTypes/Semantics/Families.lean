import Mettapedia.OSLF.NativeTypes.Semantics.Modal
import Mettapedia.OSLF.NativeTypes.Semantics.Modal.Possibility
import Mettapedia.TypeTheory.GuardEvidenceComprehension

open Mettapedia.OSLF.Framework

/-!
# Native predicates and their retained dependent output families

A native output includes its equation-invariant predicate and a dependent
family with exactly that support. Its comprehension retains witnesses, while
the predicate refinement forgets their selection. Reindexing acts on both
outputs and preserves their projection square.

Generated dependent modalities instantiate this interface with full response
families and explicit equation paths, rather than one successful execution.
Comparisons of independently specified outputs preserve native membership,
comprehension, universal evidence properties and ordered observer readouts.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Families

open GSLTTypeSynthesis
open Mettapedia.TypeTheory.GuardEvidenceComprehension

universe u v w

structure NativeOutput (system : Mettapedia.GSLT.GSLT.{u}) where
  predicate : EquationPredicate system
  Family : system.Term → Type v
  supportExact : ∀ term, Nonempty (Family term) ↔ predicate term

namespace NativeOutput

variable {system : Mettapedia.GSLT.GSLT.{u}} (output : NativeOutput.{u,v} system)

def nativeType : GSLTNativeType system := ⟨(), output.predicate⟩

abbrev Comprehension := Sigma output.Family

abbrev Refinement := {term : system.Term // output.predicate term}

def project (point : output.Comprehension) : output.Refinement :=
  ⟨point.1, (output.supportExact point.1).mp ⟨point.2⟩⟩

theorem project_surjective : Function.Surjective output.project := by
  rintro ⟨term, supported⟩
  obtain ⟨witness⟩ := (output.supportExact term).mpr supported
  exact ⟨⟨term, witness⟩, rfl⟩

theorem project_injective_iff : Function.Injective output.project ↔
    ∀ term, Subsingleton (output.Family term) := by
  constructor
  · intro injective term
    refine ⟨fun first second => ?_⟩
    have same : output.project ⟨term, first⟩ = output.project ⟨term, second⟩ := rfl
    exact eq_of_heq (Sigma.mk.inj_iff.mp (injective same)).2
  · intro singleton first second same
    rcases first with ⟨firstTerm, firstWitness⟩
    rcases second with ⟨secondTerm, secondWitness⟩
    have terms := congrArg Subtype.val same
    cases terms
    exact Sigma.ext rfl (heq_of_eq ((singleton firstTerm).elim firstWitness secondWitness))

theorem satisfies_iff_family (term : system.Term) :
    (gsltOSLF system).satisfies (S := ()) term output.nativeType.pred ↔
      Nonempty (output.Family term) :=
  (output.supportExact term).symm

def onClasses : Quotient system.equations → Prop :=
  descendPredicate system output.predicate

theorem quotient_iff_family (term : system.Term) :
    output.onClasses (Quotient.mk system.equations term) ↔ Nonempty (output.Family term) :=
  (output.supportExact term).symm

def reindex {source : Mettapedia.GSLT.GSLT.{u}}
    (translation : EquationRespectingMap source system) : NativeOutput.{u,v} source where
  predicate := translation.pullback output.predicate
  Family term := output.Family (translation.toFun term)
  supportExact term := output.supportExact (translation.toFun term)

def comprehensionMap {source : Mettapedia.GSLT.GSLT.{u}}
    (translation : EquationRespectingMap source system) :
    (output.reindex translation).Comprehension → output.Comprehension
  | ⟨term, witness⟩ => ⟨translation.toFun term, witness⟩

def refinementMap {source : Mettapedia.GSLT.GSLT.{u}}
    (translation : EquationRespectingMap source system) :
    (output.reindex translation).Refinement → output.Refinement
  | ⟨term, supported⟩ => ⟨translation.toFun term, supported⟩

theorem reindex_projection_square {source : Mettapedia.GSLT.GSLT.{u}}
    (translation : EquationRespectingMap source system)
    (point : (output.reindex translation).Comprehension) :
    output.project (output.comprehensionMap translation point) =
      output.refinementMap translation ((output.reindex translation).project point) := by
  cases point
  rfl

theorem reindex_preserves_selected_witness {source : Mettapedia.GSLT.GSLT.{u}}
    (translation : EquationRespectingMap source system)
    (point : (output.reindex translation).Comprehension) :
    (output.comprehensionMap translation point).1 = translation.toFun point.1 ∧
      HEq (output.comprehensionMap translation point).2 point.2 := ⟨rfl, HEq.rfl⟩

end NativeOutput

namespace NativeOutput

section Comparison

variable {source target : Mettapedia.GSLT.GSLT.{u}}
  (sourceOutput : NativeOutput.{u,v} source) (targetOutput : NativeOutput.{u,w} target)
  (mapTerm : source.Term → target.Term)
  (fibreEquiv : ∀ term, sourceOutput.Family term ≃ targetOutput.Family (mapTerm term))

include fibreEquiv

/-- Comparing independently specified retained families transports their
native support. The family equivalence must come from the implementation;
neither predicate is defined by this comparison. -/
theorem predicate_iff (term : source.Term) :
    sourceOutput.predicate term ↔ targetOutput.predicate (mapTerm term) := by
  constructor
  · intro supported
    obtain ⟨witness⟩ := (sourceOutput.supportExact term).mpr supported
    exact (targetOutput.supportExact (mapTerm term)).mp ⟨fibreEquiv term witness⟩
  · intro supported
    obtain ⟨witness⟩ := (targetOutput.supportExact (mapTerm term)).mpr supported
    exact (sourceOutput.supportExact term).mp ⟨(fibreEquiv term).symm witness⟩

theorem nativeType_iff (term : source.Term) :
    (gsltOSLF source).satisfies (S := ()) term sourceOutput.nativeType.pred ↔
      (gsltOSLF target).satisfies (S := ()) (mapTerm term) targetOutput.nativeType.pred :=
  predicate_iff sourceOutput targetOutput mapTerm fibreEquiv term

/-- The comparison is an equivalence over the source context. It makes no
surjectivity claim about target terms outside the compiled image. -/
def comprehensionEquiv :
    sourceOutput.Comprehension ≃ Sigma (fun term => targetOutput.Family (mapTerm term)) :=
  Equiv.sigmaCongrRight fibreEquiv

@[simp] theorem comprehensionEquiv_fst (point : sourceOutput.Comprehension) :
    (comprehensionEquiv sourceOutput targetOutput mapTerm fibreEquiv point).1 = point.1 := rfl

@[simp] theorem comprehensionEquiv_snd (point : sourceOutput.Comprehension) :
    (comprehensionEquiv sourceOutput targetOutput mapTerm fibreEquiv point).2 =
      fibreEquiv point.1 point.2 := rfl

/-- Move a retained witness into the independently specified target family. -/
def mapComprehension (point : sourceOutput.Comprehension) : targetOutput.Comprehension :=
  ⟨mapTerm point.1, fibreEquiv point.1 point.2⟩

def mapRefinement (point : sourceOutput.Refinement) : targetOutput.Refinement :=
  ⟨mapTerm point.1, (predicate_iff sourceOutput targetOutput mapTerm fibreEquiv point.1).mp
    point.2⟩

theorem comparison_projection_square (point : sourceOutput.Comprehension) :
    targetOutput.project (mapComprehension sourceOutput targetOutput mapTerm fibreEquiv point) =
      mapRefinement sourceOutput targetOutput mapTerm fibreEquiv (sourceOutput.project point) := rfl

/-- A faithful state encoding and fibre equivalences cannot merge selected
receipts, even when their truth-only supports agree. -/
theorem mapComprehension_injective (faithful : Function.Injective mapTerm) :
    Function.Injective (mapComprehension sourceOutput targetOutput mapTerm fibreEquiv) := by
  rintro ⟨firstTerm, firstWitness⟩ ⟨secondTerm, secondWitness⟩ same
  have terms : firstTerm = secondTerm := faithful (congrArg Sigma.fst same)
  cases terms
  have witnesses : fibreEquiv firstTerm firstWitness = fibreEquiv firstTerm secondWitness :=
    eq_of_heq (Sigma.mk.inj_iff.mp same).2
  exact Sigma.ext rfl (heq_of_eq ((fibreEquiv firstTerm).injective witnesses))

/-- Universal questions over the retained evidence need exact fibre coverage,
not determinism of the execution that produced that evidence. -/
theorem forall_evidence_iff (term : source.Term)
    (sourceProperty : sourceOutput.Family term → Prop)
    (targetProperty : targetOutput.Family (mapTerm term) → Prop)
    (agrees : ∀ witness, sourceProperty witness ↔ targetProperty (fibreEquiv term witness)) :
    (∀ witness, sourceProperty witness) ↔ (∀ witness, targetProperty witness) := by
  constructor
  · intro allSource targetWitness
    obtain ⟨sourceWitness, rfl⟩ := (fibreEquiv term).surjective targetWitness
    exact (agrees sourceWitness).mp (allSource sourceWitness)
  · intro allTarget sourceWitness
    exact (agrees sourceWitness).mpr (allTarget (fibreEquiv term sourceWitness))

theorem exists_evidence_iff (term : source.Term)
    (sourceProperty : sourceOutput.Family term → Prop)
    (targetProperty : targetOutput.Family (mapTerm term) → Prop)
    (agrees : ∀ witness, sourceProperty witness ↔ targetProperty (fibreEquiv term witness)) :
    (∃ witness, sourceProperty witness) ↔ (∃ witness, targetProperty witness) := by
  constructor
  · rintro ⟨witness, satisfies⟩
    exact ⟨fibreEquiv term witness, (agrees witness).mp satisfies⟩
  · rintro ⟨targetWitness, satisfies⟩
    obtain ⟨sourceWitness, rfl⟩ := (fibreEquiv term).surjective targetWitness
    exact ⟨sourceWitness, (agrees sourceWitness).mpr satisfies⟩

/-- A scalar representation is licensed by at most one retained receipt,
which is stronger than at most one distinct truth-only result. This theorem
does not supply any separate effect or termination obligation. -/
theorem subsingleton_family_iff (term : source.Term) :
    Subsingleton (sourceOutput.Family term) ↔
      Subsingleton (targetOutput.Family (mapTerm term)) := by
  constructor
  · intro singleton
    exact ⟨fun first second => (fibreEquiv term).symm.injective (singleton.elim _ _)⟩
  · intro singleton
    exact ⟨fun first second => (fibreEquiv term).injective (singleton.elim _ _)⟩

/-- A transported observer reads the same ordered list of selected witnesses.
No commutation or duplicate-removal law is assumed. -/
theorem ordered_readout_eq {Observation : Type*} (term : source.Term)
    (sourceReadout : sourceOutput.Family term → Observation)
    (targetReadout : targetOutput.Family (mapTerm term) → Observation)
    (agrees : ∀ witness, targetReadout (fibreEquiv term witness) = sourceReadout witness)
    (witnesses : List (sourceOutput.Family term)) :
    (witnesses.map (fibreEquiv term)).map targetReadout = witnesses.map sourceReadout := by
  simp only [List.map_map]
  apply List.map_congr_left
  intro witness _
  exact agrees witness

end Comparison

end NativeOutput

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL
open Mettapedia.OSLF.NativeTypes.Modal.Rules

def modalOutput {plan : GeneralExecutionAdmission.Plan} (schema : Schema plan)
    (A : String → RuleBinding.ContextualValue → Prop) (B : Continuation.{v}) :
    NativeOutput (Mettapedia.OSLF.NativeTypes.Semantics.Modal.focusTheory schema) where
  predicate := Mettapedia.OSLF.NativeTypes.Semantics.Modal.predicate schema A B
  Family := Mettapedia.OSLF.NativeTypes.Semantics.Modal.Family schema A B
  supportExact _ := Mettapedia.OSLF.NativeTypes.Semantics.Modal.family_support_iff

/-- The ordinary possibility output retains an actual primitive receipt and
its postcondition, while its support is the canonical native diamond. -/
def possibilityOutput (plan : GeneralExecutionAdmission.Plan) (bound : List TypeExpr) (carrier : TypeExpr)
    (postcondition : EquationPredicate (GeneralOccurrenceSemantics.gslt plan bound carrier)) :
    NativeOutput (GeneralOccurrenceSemantics.gslt plan bound carrier) where
  predicate := Mettapedia.OSLF.NativeTypes.Semantics.Modal.possibilityPredicate plan bound carrier postcondition
  Family := Mettapedia.OSLF.NativeTypes.Semantics.Modal.PossibilityFamily plan bound carrier postcondition
  supportExact _ := Mettapedia.OSLF.NativeTypes.Semantics.Modal.possibility_family_support_iff

/-- The generic comprehension contains the complete implementation. It has
not replaced it with the proof-irrelevant native support certificate. -/
theorem modal_output_keeps_complete_family {plan : GeneralExecutionAdmission.Plan}
    {schema : Schema plan} {A : String → RuleBinding.ContextualValue → Prop} {B : Continuation.{v}}
    (point : (modalOutput schema A B).Comprehension) (assignment : ScopedRuleMatching.Assignment)
    (request : TypedRequest schema A point.2.implementation.anchor assignment) :
    schema.rhs? assignment = some (point.2.response assignment request).target ∧
      (GeneralOccurrenceSemantics.gslt plan schema.bound schema.programCarrier).Step
        (point.2.response assignment request).source (point.2.response assignment request).target ∧
      Nonempty (substituteContinuation B assignment (point.2.response assignment request).target) :=
  (Mettapedia.OSLF.NativeTypes.Semantics.Modal.Family.response_readout point.2 assignment request).2

end Mettapedia.OSLF.NativeTypes.Semantics.Families
