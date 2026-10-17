import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ModalModel
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ContextLaws

/-!
# Open native membership and computation controls

The controls apply to every generated modal signature. They read an actual
open membership expression, substitute supplied code and classifier terms,
and compare its decoded inhabitants with independent parameter predicates.
A diagonal predicate is a dependent identity postcondition. Native beta
computation and vocabulary refusal are checked separately.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ExpressionControls

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Calculi.NativeDependent.Refinement
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Mettapedia.OSLF.NativeTypes.Semantics
open Presheaf CubeEnrichment CubeNativeDeclarations
open Classifier Families Operations Arguments
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

universe u
variable {D : CubeEnrichment.Signature} {I : Type} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)
    (algebra : StructuralImages.Algebra operational) (vertex : Vertex D)
    (interfaces : I → Interface D.Carrier)
    (observed : ∀ index, ResponseSemantics.Observations operational (interfaces index))

noncomputable section

def membershipExpr (carrier : D.Carrier) : TypeExpr (Declarations.symbols interfaces) 2 :=
  SignatureSum.typeLeft (typingType carrier (.var 0) (.var 1))

/-- The actual evaluator reads the two free variables as value and classifier
in the independently assembled membership scope. -/
theorem membership_expr_read (carrier : D.Carrier) :
    (ModalModel.model operational algebra vertex interfaces observed).evaluateType
      (typingScope operational carrier) (membershipExpr interfaces carrier) =
        some (typingMeaning operational carrier) := by
  simp only [membershipExpr, ModalModel.model, ModalModel.fromRequests,
    SignatureSum.evaluateType_left]
  let base := Classifier.Model.model operational algebra vertex
  have same : (Fin.cases (.var 0) (fun _ => .var 1) : Substitution (symbols D) 2 2) =
      TermExpr.var := by
    funext position
    cases position using Fin.cases with
    | zero => rfl
    | succ position =>
        have zero : position = 0 := Fin.eq_zero position
        cases zero
        rfl
  change base.evaluateType (typingScope operational carrier)
    (.family (.typing carrier) (Fin.cases (.var 0) (fun _ => .var 1))) = _
  rw [same]
  have identity := base.evaluateSubstitution_identity (typingScope operational carrier)
  have read := base.evaluate_family (typingScope operational carrier) (.typing carrier) TermExpr.var
    (𝟙 (typingScope operational carrier).1)
    ((base.evaluateSubstitution_eq_some_iff _ _ _ _).mp identity)
  exact read.trans (congrArg some (LocalType.reindex_id (typingMeaning operational carrier)))

/-- This is substitution of native syntax into the open expression, not
evaluation of an independently named semantic membership function. -/
theorem substituted_membership_read (carrier : D.Carrier) {n : Nat}
    (scope : Scope W n) (value classifier : TermExpr (Declarations.symbols interfaces) n)
    (valueName classifierName : scope.1 ⟶ Carrier.presheaf operational carrier)
    (valueRead : (ModalModel.model operational algebra vertex interfaces observed).evaluateTerm scope value =
      some (codeValue operational carrier valueName))
    (classifierRead : (ModalModel.model operational algebra vertex interfaces observed).evaluateTerm scope classifier =
      some (codeValue operational carrier classifierName)) :
    (ModalModel.model operational algebra vertex interfaces observed).evaluateType scope
      ((membershipExpr interfaces carrier).substitute (Fin.cases value (fun _ => classifier))) =
        some (typingAt operational carrier valueName classifierName) := by
  have mappingRead : (ModalModel.model operational algebra vertex interfaces observed).evaluateSubstitution
      scope (typingScope operational carrier) (Fin.cases value (fun _ => classifier)) =
        some (pairArguments operational carrier valueName classifierName) := by
    apply (ModelData.evaluateSubstitution_eq_some_iff _ _ _ _ _).mpr
    intro position
    cases position using Fin.cases with
    | zero =>
        exact valueRead.trans (congrArg some
          (pair_component_zero operational carrier valueName classifierName).symm)
    | succ position =>
        have zero : position = 0 := Fin.eq_zero position
        cases zero
        exact classifierRead.trans (congrArg some
          (pair_component_one operational carrier valueName classifierName).symm)
  exact ModalModel.type_substitute operational algebra vertex interfaces observed
    (membershipExpr interfaces carrier) scope (typingScope operational carrier) _ _ mappingRead
    (typingMeaning operational carrier) (membership_expr_read operational algebra vertex interfaces observed carrier)

/-- An independently specified predicate names the classifier assigned to an
open native classifier variable. -/
def targetName {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (predicate : Subfunctor (FunctorToTypes.prod (operational carrier) P)) :
    P ⟶ Carrier.presheaf operational carrier :=
  CertifiedSections.predicateName operational carrier kind predicate ≫
    validInclusion operational carrier kind

theorem target_membership_exact {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (predicate : Subfunctor (FunctorToTypes.prod (operational carrier) P))
    (value : P ⟶ operational carrier) (world : Wᵒᵖ) (parameter : P.obj world) :
    Nonempty ((typingAt operational carrier (value ≫ Carrier.injection operational carrier)
      (targetName operational carrier kind predicate)).decoded.obj ⟨world, parameter⟩) ↔
      (value.app world parameter, parameter) ∈ predicate.obj world := by
  rw [typingAt_inhabited_iff]
  exact FamilyNaming.member_name predicate world (value.app world parameter) parameter

/-- The target classifier depends on the supplied rely input. -/
def identityPostcondition {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (input : P ⟶ operational carrier) : Subfunctor (FunctorToTypes.prod (operational carrier) P) where
  obj world pair := pair.1 = input.app world pair.2
  map arrow pair equality := by
    change (operational carrier).map arrow pair.1 = input.app _ (P.map arrow pair.2)
    exact (congrArg ((operational carrier).map arrow) equality).trans
      (input.naturality_apply arrow pair.2).symm

theorem identity_target_exact {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (input result : P ⟶ operational carrier) (world : Wᵒᵖ) (parameter : P.obj world) :
    Nonempty ((typingAt operational carrier (result ≫ Carrier.injection operational carrier)
      (targetName operational carrier kind (identityPostcondition operational carrier input))).decoded.obj
        ⟨world, parameter⟩) ↔ result.app world parameter = input.app world parameter :=
  target_membership_exact operational carrier kind _ result world parameter

theorem identity_target_positive {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (input : P ⟶ operational carrier) (world : Wᵒᵖ) (parameter : P.obj world) :
    Nonempty ((typingAt operational carrier (input ≫ Carrier.injection operational carrier)
      (targetName operational carrier kind (identityPostcondition operational carrier input))).decoded.obj
        ⟨world, parameter⟩) :=
  (identity_target_exact operational carrier kind input input world parameter).mpr rfl

theorem identity_target_wrong_result {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (input result : P ⟶ operational carrier) (world : Wᵒᵖ) (parameter : P.obj world)
    (different : result.app world parameter ≠ input.app world parameter) :
    ¬ Nonempty ((typingAt operational carrier (result ≫ Carrier.injection operational carrier)
      (targetName operational carrier kind (identityPostcondition operational carrier input))).decoded.obj
        ⟨world, parameter⟩) :=
  fun member => different ((identity_target_exact operational carrier kind input result world parameter).mp member)

theorem true_target_positive {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (value : P ⟶ operational carrier) (world : Wᵒᵖ) (parameter : P.obj world) :
    Nonempty ((typingAt operational carrier (value ≫ Carrier.injection operational carrier)
      (targetName operational carrier kind ⊤)).decoded.obj ⟨world, parameter⟩) :=
  (target_membership_exact operational carrier kind ⊤ value world parameter).mpr trivial

theorem false_target_negative {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (value : P ⟶ operational carrier) (world : Wᵒᵖ) (parameter : P.obj world) :
    ¬ Nonempty ((typingAt operational carrier (value ≫ Carrier.injection operational carrier)
      (targetName operational carrier kind ⊥)).decoded.obj ⟨world, parameter⟩) :=
  fun member => (target_membership_exact operational carrier kind ⊥ value world parameter).mp member

/-- The open native expression and its independently decoded membership
agree at the actual environment containing the supplied program and target.
This connects the evaluator control to the predicate controls above. -/
theorem open_target_exact {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (predicate : Subfunctor (FunctorToTypes.prod (operational carrier) P))
    (value : P ⟶ operational carrier) (world : Wᵒᵖ) (parameter : P.obj world) :
    (ModalModel.model operational algebra vertex interfaces observed).evaluateType
      (typingScope operational carrier) (membershipExpr interfaces carrier) = some (typingMeaning operational carrier) ∧
    (Nonempty ((typingMeaning operational carrier).decoded.obj
      ⟨world, (pairNameInverse operational carrier).app world
        (.operational (value.app world parameter),
          (targetName operational carrier kind predicate).app world parameter)⟩) ↔
      (value.app world parameter, parameter) ∈ predicate.obj world) := by
  refine ⟨membership_expr_read operational algebra vertex interfaces observed carrier, ?_⟩
  exact (typing_inhabited_iff operational carrier world _ _).trans
    (FamilyNaming.member_name predicate world (value.app world parameter) parameter)

/-- An input-dependent target keeps equality with the rely value; an unrelated
output does not pass merely because both have the same carrier. -/
theorem open_identity_target_exact {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) (kind : HSort)
    (input result : P ⟶ operational carrier) (world : Wᵒᵖ) (parameter : P.obj world) :
    (ModalModel.model operational algebra vertex interfaces observed).evaluateType
      (typingScope operational carrier) (membershipExpr interfaces carrier) = some (typingMeaning operational carrier) ∧
    (Nonempty ((typingMeaning operational carrier).decoded.obj
      ⟨world, (pairNameInverse operational carrier).app world
        (.operational (result.app world parameter),
          (targetName operational carrier kind (identityPostcondition operational carrier input)).app world parameter)⟩) ↔
      result.app world parameter = input.app world parameter) :=
  open_target_exact operational algebra vertex interfaces observed carrier kind
    (identityPostcondition operational carrier input) result world parameter

/-- The same generated open expression has inhabited and empty fibres when
the classifier variable receives respectively the true and false target. -/
theorem open_true_false_targets (carrier : D.Carrier) (kind : HSort)
    (world : Wᵒᵖ) (value : (operational carrier).obj world) :
    (ModalModel.model operational algebra vertex interfaces observed).evaluateType
      (typingScope operational carrier) (membershipExpr interfaces carrier) = some (typingMeaning operational carrier) ∧
    Nonempty ((typingMeaning operational carrier).decoded.obj
      ⟨world, (pairNameInverse operational carrier).app world
        (.operational value, (targetName operational carrier kind
          (⊤ : Subfunctor (FunctorToTypes.prod (operational carrier) (operational carrier)))).app world value)⟩) ∧
    ¬ Nonempty ((typingMeaning operational carrier).decoded.obj
      ⟨world, (pairNameInverse operational carrier).app world
        (.operational value, (targetName operational carrier kind
          (⊥ : Subfunctor (FunctorToTypes.prod (operational carrier) (operational carrier)))).app world value)⟩) := by
  refine ⟨membership_expr_read operational algebra vertex interfaces observed carrier, ?_, ?_⟩
  · exact (open_target_exact operational algebra vertex interfaces observed carrier kind ⊤
      (𝟙 (operational carrier)) world value).2.mpr trivial
  · exact fun member => (open_target_exact operational algebra vertex interfaces observed carrier kind ⊥
      (𝟙 (operational carrier)) world value).2.mp member

def nativeCode (carrier : D.Carrier) (n : Nat) : TypeExpr (Declarations.symbols interfaces) n :=
  .family (.inl (.code carrier)) Fin.elim0

@[simp] theorem nativeCode_substitute (carrier : D.Carrier) {n m : Nat}
    (mapping : Substitution (Declarations.symbols interfaces) n m) :
    (nativeCode interfaces carrier n).substitute mapping = nativeCode interfaces carrier m := by
  apply congrArg (TypeExpr.family (S := Declarations.symbols interfaces) (.inl (.code carrier)))
  funext position
  exact Fin.elim0 position

@[simp] theorem nativeCode_rename (carrier : D.Carrier) {n m : Nat} (mapping : Renaming n m) :
    (nativeCode interfaces carrier n).rename mapping = nativeCode interfaces carrier m := by
  rw [← TypeExpr.substitute_variables]
  exact nativeCode_substitute interfaces carrier _

def identityExpr (carrier : D.Carrier) (n : Nat) : TermExpr (Declarations.symbols interfaces) n :=
  .lam (nativeCode interfaces carrier n) (nativeCode interfaces carrier (n + 1)) (.var 0)

def identityApp (carrier : D.Carrier) {n : Nat} (argument : TermExpr (Declarations.symbols interfaces) n) :=
  TermExpr.app (nativeCode interfaces carrier n) (nativeCode interfaces carrier (n + 1))
    (identityExpr interfaces carrier n) argument

theorem identity_substitute (carrier : D.Carrier) {n m : Nat}
    (mapping : Substitution (Declarations.symbols interfaces) n m) :
    (identityExpr interfaces carrier n).substitute mapping = identityExpr interfaces carrier m := by
  simp only [identityExpr, TermExpr.substitute, nativeCode_substitute, liftSubstitution_zero]

theorem identity_app_substitute (carrier : D.Carrier) {n m : Nat}
    (argument : TermExpr (Declarations.symbols interfaces) n)
    (mapping : Substitution (Declarations.symbols interfaces) n m) :
    (identityApp interfaces carrier argument).substitute mapping =
      identityApp interfaces carrier (argument.substitute mapping) := by
  simp only [identityApp, TermExpr.substitute, nativeCode_substitute, identity_substitute]

def nativeCodeFormed (carrier : D.Carrier) {n : Nat}
    {context : ContextExpr (Declarations.symbols interfaces) n}
    (formed : Derivation (Declarations.signature vertex interfaces) (.context context)) :
    Derivation (Declarations.signature vertex interfaces) (.type context (nativeCode interfaces carrier n)) :=
  deriveList (.typeFamily context (.inl (.code carrier)) Fin.elim0)
    (.cons formed (.cons (Declarations.headerFormation vertex interfaces |>.typeHeader (.inl (.code carrier)))
      (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil)))

/-- Beta equality is constructed from the original native rule and then
interpreted in the generated model. No computational equality is assumed. -/
def identityBeta (carrier : D.Carrier) {n : Nat}
    {context : ContextExpr (Declarations.symbols interfaces) n}
    {argument : TermExpr (Declarations.symbols interfaces) n}
    (formed : Derivation (Declarations.signature vertex interfaces) (.context context))
    (typed : Derivation (Declarations.signature vertex interfaces)
      (.term context argument (nativeCode interfaces carrier n))) :
    Derivation (Declarations.signature vertex interfaces)
      (.termEq context (identityApp interfaces carrier argument) argument (nativeCode interfaces carrier n)) := by
  let domain := nativeCodeFormed vertex interfaces carrier formed
  let extended := extendContextFormed formed domain
  let body := nativeCodeFormed vertex interfaces carrier extended
  have newest : Derivation (Declarations.signature vertex interfaces)
      (.term (.snoc context (nativeCode interfaces carrier n)) (.var 0)
        (nativeCode interfaces carrier (n + 1))) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero, nativeCode_rename] using
      deriveList (.variable _ 0) (.cons extended .nil)
  simpa only [RuleCode.conclusion, TermExpr.substitute, instantiate_zero,
    nativeCode_substitute, identityApp, identityExpr] using
    deriveList (.piBeta context (nativeCode interfaces carrier n)
      (nativeCode interfaces carrier (n + 1)) (.var 0) argument)
      (.cons domain (.cons body (.cons newest (.cons typed .nil))))

theorem identity_beta_meaning (carrier : D.Carrier) {n : Nat}
    {context : ContextExpr (Declarations.symbols interfaces) n}
    {argument : TermExpr (Declarations.symbols interfaces) n}
    (formed : Derivation (Declarations.signature vertex interfaces) (.context context))
    (typed : Derivation (Declarations.signature vertex interfaces)
      (.term context argument (nativeCode interfaces carrier n))) :
    Interprets (ModalModel.model operational algebra vertex interfaces observed)
      (.termEq context (identityApp interfaces carrier argument) argument (nativeCode interfaces carrier n)) :=
  ModalModel.sound operational algebra vertex interfaces observed
    (identityBeta vertex interfaces carrier formed typed)

/-- A complete open beta example without supplied typing or context proofs. -/
def identityVariableBeta (carrier : D.Carrier) :
    Derivation (Declarations.signature vertex interfaces)
      (.termEq (.snoc .nil (nativeCode interfaces carrier 0))
        (identityApp interfaces carrier (.var 0)) (.var 0) (nativeCode interfaces carrier 1)) := by
  let empty : Derivation (Declarations.signature vertex interfaces) (.context .nil) :=
    deriveList .contextNil .nil
  let code := nativeCodeFormed vertex interfaces carrier empty
  let context := extendContextFormed empty code
  have newest : Derivation (Declarations.signature vertex interfaces)
      (.term (.snoc .nil (nativeCode interfaces carrier 0)) (.var 0) (nativeCode interfaces carrier 1)) := by
    simpa only [RuleCode.conclusion, ContextExpr.lookup_zero, nativeCode_rename] using
      deriveList (.variable _ 0) (.cons context .nil)
  exact identityBeta vertex interfaces carrier context newest

theorem identity_variable_meaning (carrier : D.Carrier) :
    Interprets (ModalModel.model operational algebra vertex interfaces observed)
      (.termEq (.snoc .nil (nativeCode interfaces carrier 0))
        (identityApp interfaces carrier (.var 0)) (.var 0) (nativeCode interfaces carrier 1)) :=
  ModalModel.sound operational algebra vertex interfaces observed
    (identityVariableBeta vertex interfaces carrier)

def identityJudgment (carrier : D.Carrier) : Judgment (Declarations.symbols interfaces) :=
  .termEq (.snoc .nil (nativeCode interfaces carrier 0))
    (identityApp interfaces carrier (.var 0)) (.var 0) (nativeCode interfaces carrier 1)

def identityCertificate (carrier : D.Carrier) :=
  Certificates.Refinement.erase (identityVariableBeta vertex interfaces carrier)

theorem identity_full_check [DecidableEq D.Carrier] [DecidableEq D.Former] [DecidableEq I]
    (carrier : D.Carrier) :
    Declarations.check vertex interfaces NativeLogic.full
      (identityCertificate vertex interfaces carrier) (identityJudgment interfaces carrier) = .accepted :=
  (Declarations.check_exact vertex interfaces NativeLogic.full _ _).mpr
    ⟨NativeLogic.full_permits _, NativeLogic.full_certificatePermitted _,
      identityVariableBeta vertex interfaces carrier, rfl⟩

/-- The same valid beta certificate is refused specifically because its
application and function are outside the selected vocabulary. -/
theorem identity_vocabulary_refused [DecidableEq D.Carrier] [DecidableEq D.Former] [DecidableEq I]
    (carrier : D.Carrier) :
    Declarations.check vertex interfaces ⟨[]⟩
      (identityCertificate vertex interfaces carrier) (identityJudgment interfaces carrier) =
        .vocabularyRefused := by
  change NativeLogic.check _ _ _ = _
  rw [NativeLogic.check_vocabulary_exact]
  have refused : NativeLogic.Fragment.accepts ⟨[]⟩ (identityJudgment interfaces carrier) = false := rfl
  simp only [NativeLogic.checkedVocabulary, refused, Bool.false_and, Bool.false_eq_true, if_false]

/-- A context proof is deliberately the wrong certificate for the valid
identity equation. Full vocabulary therefore reports a bad certificate. -/
theorem identity_wrong_certificate [DecidableEq D.Carrier] [DecidableEq D.Former] [DecidableEq I]
    (carrier : D.Carrier) :
    Declarations.check vertex interfaces NativeLogic.full
      (.node .contextNil Fin.elim0) (identityJudgment interfaces carrier) = .certificateRejected := by
  change NativeLogic.check _ _ _ = _
  rw [NativeLogic.check_vocabulary_exact]
  simp only [NativeLogic.checkedVocabulary, NativeLogic.full_accepts,
    NativeLogic.full_certificateAllowed, Bool.true_and, if_true]
  rfl

/-- Vocabulary refusal and semantic falsity are separate: this expression
has its full native meaning and its valid certificate is accepted in full. -/
theorem vocabulary_refusal_with_semantics
    [DecidableEq D.Carrier] [DecidableEq D.Former] [DecidableEq I]
    (carrier : D.Carrier) :
    Interprets (ModalModel.model operational algebra vertex interfaces observed) (identityJudgment interfaces carrier) ∧
      Declarations.check vertex interfaces NativeLogic.full
        (identityCertificate vertex interfaces carrier) (identityJudgment interfaces carrier) = .accepted ∧
      Declarations.check vertex interfaces ⟨[]⟩
        (identityCertificate vertex interfaces carrier) (identityJudgment interfaces carrier) = .vocabularyRefused ∧
      Declarations.check vertex interfaces NativeLogic.full
        (.node .contextNil Fin.elim0) (identityJudgment interfaces carrier) = .certificateRejected :=
  ⟨identity_variable_meaning operational algebra vertex interfaces observed carrier,
    identity_full_check vertex interfaces carrier, identity_vocabulary_refused vertex interfaces carrier,
    identity_wrong_certificate vertex interfaces carrier⟩

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ExpressionControls
