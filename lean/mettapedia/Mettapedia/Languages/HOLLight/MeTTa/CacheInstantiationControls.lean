import Mettapedia.Languages.HOLLight.MeTTa.InferenceHistory
import Mettapedia.Languages.HOLLight.MeTTa.CacheAuthorizationControls

/-!
# Source instantiation controls

Two distinct Boolean hypotheses can become one after type substitution.
The source executes its insertion traversal and retains the resulting order.
Shadowed malformed maplets remain subject to complete admission checks.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.HOLLight.MeTTa.CacheInstantiationControls

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.ProcessCalculi.MORK (Subst applySubst)
open Mettapedia.Languages.MeTTa.PeTTa
open Mettapedia.Languages.OpenTheory
open SignatureFormation DefinitionAdapters CacheAuthorization Eval
open Effects (State)

def constants : Const → Atom := DeclarationTable.primitiveIdentity
def alpha : Ty := .var (.global "A")
def beta : Ty := .var (.global "B")
def substitutions : List (Ty × Ty) := [(Ty.bool, alpha), (Ty.bool, beta)]
def termVariable (type : Ty) : CanonicalTerm :=
  (CheckedSourceTerm.ofVariable ⟨.global "x", type⟩).canonical
def hypothesis (type : Ty) : CanonicalTerm :=
  CanonicalTerm.equalityOfSameType (termVariable type) (termVariable type) rfl

theorem boolean_hypotheses (type : Ty) : (hypothesis type).IsBool := rfl

theorem distinct_before_instantiation : hypothesis alpha ≠ hypothesis beta := by
  intro equal
  have terms := congrArg CanonicalTerm.term equal
  simp [hypothesis, termVariable, alpha, beta, CanonicalTerm.equalityOfSameType,
    CanonicalTerm.equalityDB, CheckedSourceTerm.canonical, CheckedSourceTerm.ofVariable,
    SourceTerm.toDB, boundIndex, Ty.equality, Ty.function, Name.global] at terms

private theorem applied_hypothesis (maplets : List (Ty × Ty)) (type : Ty) :
    (SourceSubstitution.typeOnlySubstitution maplets).apply (hypothesis type) =
      hypothesis ((SourceSubstitution.typeSubstitution maplets).apply type) := by
  apply CanonicalTerm.ext_term
  simp [hypothesis, termVariable, CanonicalTerm.equalityOfSameType, CanonicalTerm.equalityDB,
    CheckedSourceTerm.canonical, CheckedSourceTerm.ofVariable, SourceTerm.toDB, boundIndex,
    SourceSubstitution.typeOnlySubstitution, TypeCorrectTermSubstitution.apply,
    TypeCorrectTermSubstitution.ofTypes, TermSubst.applyChecked, TermSubst.applyDB,
    TermSubst.lookup, TypeSubst.applyVar, Ty.equality, Ty.function, Ty.bool]

theorem unchanged_without_instantiation :
    CacheInstantiation.hypotheses constants (SourceSubstitution.typeOnlySubstitution [])
      [hypothesis alpha, hypothesis beta] = [hypothesis alpha, hypothesis beta] := by
  have different : TheoremMetadata.hypothesisAtom constants (hypothesis alpha) ≠
      TheoremMetadata.hypothesisAtom constants (hypothesis beta) := by
    simp [TheoremMetadata.hypothesisAtom, hypothesis, termVariable, alpha, beta,
      CanonicalTerm.equalityOfSameType, CanonicalTerm.equalityDB, CheckedSourceTerm.canonical,
      CheckedSourceTerm.ofVariable, SourceTerm.toDB, boundIndex, Representation.termAtom,
      TypeSubstitution.typeAtom, TypeSubstitution.nameAtom, Representation.variableAtom,
      Ty.equality, Ty.function, Name.global]
  unfold CacheInstantiation.hypotheses
  simp [applied_hypothesis, SourceSubstitution.typeSubstitution, SourceSubstitution.variableEntries,
    TypeSubst.ofList, List.KeyedUnion.merge, different]

theorem coalesced_source_order :
    CacheInstantiation.hypotheses constants (SourceSubstitution.typeOnlySubstitution substitutions)
      [hypothesis alpha, hypothesis beta, hypothesis Ty.bool] = [hypothesis Ty.bool] := by
  have first : (SourceSubstitution.typeSubstitution substitutions).apply alpha = Ty.bool := by
    change (SourceSubstitution.typeSubstitution substitutions).apply (.var (.global "A")) = Ty.bool
    rw [SourceSubstitution.apply_variable]
    simp [substitutions, SourceSubstitution.variableType, alpha]
  have second : (SourceSubstitution.typeSubstitution substitutions).apply beta = Ty.bool := by
    change (SourceSubstitution.typeSubstitution substitutions).apply (.var (.global "B")) = Ty.bool
    rw [SourceSubstitution.apply_variable]
    simp [substitutions, SourceSubstitution.variableType, alpha, beta, Name.global]
  unfold CacheInstantiation.hypotheses
  simp [applied_hypothesis, first, second, Ty.bool, List.KeyedUnion.merge]

/-- The retained authored hypothesis traversal executes this coalescence;
the result is not inferred from a set-support comparison. -/
theorem authored_coalescence (state : State) :
    PureReturns program
      [("maplets", TypeSubstitution.maplets Representation.registeredOperatorAtom substitutions),
        ("items", Premises.keys ([hypothesis alpha, hypothesis beta, hypothesis Ty.bool].map
          (TheoremMetadata.hypothesisAtom constants)))] state
      (.expression [.symbol "hol-light:inst-types", .var "maplets", .var "items"]) state
      (Premises.keys [TheoremMetadata.hypothesisAtom constants (hypothesis Ty.bool)]) := by
  have executed := TypeInstantiation.Hypotheses.authored_hypotheses_return constants substitutions
    [hypothesis alpha, hypothesis beta, hypothesis Ty.bool]
    [("maplets", TypeSubstitution.maplets Representation.registeredOperatorAtom substitutions),
      ("items", Premises.keys ([hypothesis alpha, hypothesis beta, hypothesis Ty.bool].map
        (TheoremMetadata.hypothesisAtom constants)))] state "maplets" "items" rfl rfl
  rw [← CacheInstantiation.type_hypotheses_encoded, coalesced_source_order] at executed
  exact executed

def world : TheoryContext := SourceProfile.primitiveContext
private theorem boolean_formed : TypeFormed world.signature Ty.bool :=
  ContextControls.boolean_formed.mono (ContextControls.core_includes.trans
    (SourceProfile.core_includes_individual.trans SourceProfile.individual_includes))
private theorem boolean_resolved : TypeFormation.Resolved world.signature Ty.bool := by
  have formed := boolean_formed
  simp only [Ty.bool, TypeFormed] at formed
  simp only [Ty.bool, TypeFormation.Resolved]
  exact ⟨⟨0, formed.1⟩, by simp⟩

def shadowed : List TermMapletReading.Entry :=
  [(SourceSubstitution.Controls.checkedBool "q", ⟨.global "p", Ty.bool⟩),
    (CheckedSourceTerm.ofVariable ⟨.global "x", alpha⟩, ⟨.global "p", Ty.bool⟩)]

private theorem shadowed_formed : ∀ entry ∈ shadowed, TermMapletReading.EntryFormed world.signature entry := by
  intro entry member
  simp only [shadowed, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · have resolved : TermReading.SourceResolved world.signature
        (SourceSubstitution.Controls.checkedBool "q").source := by
      simp only [SourceSubstitution.Controls.checkedBool, CheckedSourceTerm.ofVariable,
        TermReading.SourceResolved]
      exact ⟨rfl, boolean_resolved⟩
    have annotations : AnnotationsFormed world.signature
        (SourceSubstitution.Controls.checkedBool "q").canonical.term := by
      simpa [SourceSubstitution.Controls.checkedBool, CheckedSourceTerm.ofVariable,
        CheckedSourceTerm.canonical, SourceTerm.toDB, boundIndex] using
        AnnotationsFormed.free (sourceVar := ⟨.global "q", Ty.bool⟩) boolean_formed
    exact ⟨resolved, annotations, boolean_formed, rfl,
      boolean_resolved, boolean_formed⟩
  · have resolved : TermReading.SourceResolved world.signature
        (CheckedSourceTerm.ofVariable ⟨.global "x", alpha⟩).source := by
      simp [CheckedSourceTerm.ofVariable, TermReading.SourceResolved, alpha,
        TypeFormation.Resolved, Name.global]
    have formed : TypeFormed world.signature alpha := by simp [alpha, TypeFormed]
    have annotations : AnnotationsFormed world.signature
        (CheckedSourceTerm.ofVariable ⟨.global "x", alpha⟩).canonical.term := by
      simpa [CheckedSourceTerm.ofVariable, CheckedSourceTerm.canonical, SourceTerm.toDB, boundIndex] using
        AnnotationsFormed.free (sourceVar := ⟨.global "x", alpha⟩) formed
    exact ⟨resolved, annotations, formed, rfl, boolean_resolved, boolean_formed⟩

theorem shadowed_invalid : ¬ SourceSubstitution.TermMapletsAdmissible
    (TermMapletReading.sourceEntries shadowed) := by
  exact SourceSubstitution.Controls.shadowed_wrong_type_refused

/-- Complete source validation refuses the shadowed wrong-typed replacement,
even though first-match lookup would never select it. -/
theorem authored_shadowed_invalid_refused (state : State) (axioms receipts : Atom)
    (cache : List (Atom × Atom)) (key : Atom) :
    let source := ProofLookup.sourceState
      (OperatorTable.tableAtom DeclarationTable.sourcePrimitive.operators (fun _ => .symbol "HOL:Primitive"))
      (DeclarationTable.tableAtom DeclarationTable.sourcePrimitive constants) axioms receipts cache
    PureReturns program [("state", source), ("request", .expression [.symbol "INST",
      TermMapletReading.sourceAtom shadowed, key])] state
      (.expression [.symbol "hol-light:infer", .var "state", .var "request"]) state (.symbol "None") := by
  exact TermInstantiationRule.Dispatcher.authored_infer_invalid_maplets_refused world
    DeclarationTable.sourcePrimitive (fun _ => .symbol "HOL:Primitive") constants shadowed shadowed_formed
    shadowed_invalid axioms receipts key cache _ state "state" "request" rfl rfl

end Mettapedia.Languages.HOLLight.MeTTa.CacheInstantiationControls
