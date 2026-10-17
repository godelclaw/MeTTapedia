import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.ContinuationSemantics
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyEvidence
import Mettapedia.OSLF.NativeTypes.Semantics.Classifier.CertifiedSections

/-!
# Constant dependent continuations over one genuine rely

Two independently certified classifier variables supply the rely and target.
The generated target parameter is constructed by the original native lambda
rules, binding both the rely value and its actual membership evidence.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyParameters

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory
open Calculi.NativeDependent.Refinement
open NativeLocalTypeFormers ContextualLocalUniverses ContextualModelTelescopes
open DisplayedPresheafComprehension
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.NativeTypes.Semantics
open Presheaf CubeEnrichment CubeNativeDeclarations
open Classifier Families Operations CertifiedProjection

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)
    (algebra : StructuralImages.Algebra operational) (vertex : Vertex D)
variable (rely target focus : D.Carrier) (kind sort : HSort)

noncomputable section

attribute [local irreducible] Classifier.Model.model

abbrev interface : Interface D.Carrier := ⟨[], [(rely, kind)], target, focus, sort⟩

abbrev firstContext : ContextExpr (symbols D) 1 :=
  .snoc .nil (certifiedCode rely kind 0)

abbrev pairContext : ContextExpr (symbols D) 2 :=
  .snoc (firstContext rely kind) (certifiedCode target sort 1)

def pairFormed : Derivation (Theory vertex) (.context (pairContext rely target kind sort)) :=
  let first := extendFormed vertex (emptyFormed vertex)
    (certifiedFormed vertex rely kind (emptyFormed vertex))
  extendFormed vertex first (certifiedFormed vertex target sort first)

def relyTyped : Derivation (Theory vertex)
    (.term (pairContext rely target kind sort) (.var 1) (certifiedCode rely kind 2)) := by
  have typed := weakenTerm vertex (certifiedVariable vertex rely kind (emptyFormed vertex))
    (certifiedFormed vertex target sort
      (extendFormed vertex (emptyFormed vertex) (certifiedFormed vertex rely kind (emptyFormed vertex))))
  simpa only [TermExpr.rename, certifiedCode_rename, Fin.succ_zero_eq_one] using typed

def targetTyped : Derivation (Theory vertex)
    (.term (pairContext rely target kind sort) (.var 0) (certifiedCode target sort 2)) :=
  certifiedVariable vertex target sort
    (extendFormed vertex (emptyFormed vertex) (certifiedFormed vertex rely kind (emptyFormed vertex)))

abbrev relyTerm : TermExpr (symbols D) 2 := classifierValue rely kind (.var 1)
abbrev valueType : TypeExpr (symbols D) 2 := codeType rely 2
abbrev membershipType : TypeExpr (symbols D) 3 :=
  typingType rely (.var 0) ((relyTerm rely kind).rename Fin.succ)
abbrev withValue : ContextExpr (symbols D) 3 :=
  .snoc (pairContext rely target kind sort) (valueType rely)
abbrev withEvidence : ContextExpr (symbols D) 4 :=
  .snoc (withValue rely target kind sort) (membershipType rely kind)

def valueFormed : Derivation (Theory vertex)
    (.type (pairContext rely target kind sort) (valueType rely)) :=
  codeFormed vertex rely (pairFormed vertex rely target kind sort)

def membershipFormed : Derivation (Theory vertex)
    (.type (withValue rely target kind sort) (membershipType rely kind)) := by
  have classifier := classifierValueFormed vertex rely kind
    (pairFormed vertex rely target kind sort) (relyTyped vertex rely target kind sort)
  have there := weakenTerm vertex classifier (valueFormed vertex rely target kind sort)
  rw [codeType_rename] at there
  exact typingFormed vertex rely
    (extendFormed vertex (pairFormed vertex rely target kind sort) (valueFormed vertex rely target kind sort))
    (.var 0) ((relyTerm rely kind).rename Fin.succ)
    (codeVariable vertex rely (pairFormed vertex rely target kind sort)) there

def evidenceFormed : Derivation (Theory vertex) (.context (withEvidence rely target kind sort)) :=
  extendFormed vertex
    (extendFormed vertex (pairFormed vertex rely target kind sort) (valueFormed vertex rely target kind sort))
    (membershipFormed vertex rely target kind sort)

def targetThere : Derivation (Theory vertex)
    (.term (withEvidence rely target kind sort) (.var 2) (certifiedCode target sort 4)) := by
  have first := weakenTerm vertex (targetTyped vertex rely target kind sort)
    (valueFormed vertex rely target kind sort)
  rw [certifiedCode_rename] at first
  have second := weakenTerm vertex first (membershipFormed vertex rely target kind sort)
  simpa only [TermExpr.rename, certifiedCode_rename, Fin.succ_zero_eq_one, Fin.succ_one_eq_two] using second

abbrev constantContinuation : TermExpr (symbols D) 2 :=
  .lam (valueType rely) (.pi (membershipType rely kind) (certifiedCode target sort 4))
    (.lam (membershipType rely kind) (certifiedCode target sort 4) (.var 2))

def continuationTyped : Derivation (Theory vertex)
    (.term (pairContext rely target kind sort) (constantContinuation rely target kind sort)
      (relyFunction rely (relyTerm rely kind) (certifiedCode target sort 4))) := by
  let result := certifiedFormed vertex target sort (evidenceFormed vertex rely target kind sort)
  let inner := deriveList (.lambda (withValue rely target kind sort) (membershipType rely kind)
    (certifiedCode target sort 4) (.var 2))
    (.cons (membershipFormed vertex rely target kind sort)
      (.cons result (.cons (targetThere vertex rely target kind sort) .nil)))
  let body := deriveList (.piFormation (withValue rely target kind sort)
    (membershipType rely kind) (certifiedCode target sort 4))
    (.cons (membershipFormed vertex rely target kind sort) (.cons result .nil))
  exact deriveList (.lambda (pairContext rely target kind sort) (valueType rely)
    (.pi (membershipType rely kind) (certifiedCode target sort 4))
    (.lam (membershipType rely kind) (certifiedCode target sort 4) (.var 2)))
    (.cons (valueFormed vertex rely target kind sort) (.cons body (.cons inner .nil)))

abbrev prefixMapping : Substitution (symbols D)
    (prefixSize (D := D) (interface rely target focus kind sort)) 2 := fun _ => .var 1

abbrev parameterMapping : Substitution (symbols D)
    (arity (D := D) (interface rely target focus kind sort)) 2 :=
  extendSubstitution (prefixMapping rely target focus kind sort) (constantContinuation rely target kind sort)

def prefixTyped : Derivation (Theory vertex)
    (.substitution (pairContext rely target kind sort)
      (parameterPrefix (D := D) (interface rely target focus kind sort)) (prefixMapping rely target focus kind sort)) := by
  have empty := deriveList (.substitutionNil (pairContext rely target kind sort))
    (.cons (pairFormed vertex rely target kind sort) .nil)
  have value : Derivation (Theory vertex)
      (.term (pairContext rely target kind sort) (.var 1)
        ((certifiedCode rely kind 0).substitute Fin.elim0)) := by
    rw [certifiedCode_substitute]
    exact relyTyped vertex rely target kind sort
  have tree := deriveList (.substitutionExtend (pairContext rely target kind sort) .nil
    (certifiedCode rely kind 0) Fin.elim0 (.var 1))
    (.cons empty (.cons (certifiedFormed vertex rely kind (emptyFormed vertex)) (.cons value .nil)))
  have context : parameterPrefix (D := D) (interface rely target focus kind sort) = firstContext rely kind := by
    change (ContextExpr.snoc .nil ((certifiedCode rely kind 0).rename Fin.elim0)) = _
    rw [certifiedCode_rename]
  rw [context]
  have mapping : extendSubstitution (Fin.elim0 : Substitution (symbols D) 0 2) (.var 1) =
      prefixMapping rely target focus kind sort := by funext position; fin_cases position; rfl
  rw [← mapping]
  exact tree

theorem target_substituted :
    (targetParameter (D := D) (interface rely target focus kind sort)).substitute (prefixMapping rely target focus kind sort) =
      relyFunction rely (relyTerm rely kind) (certifiedCode target sort 4) := by
  refine (targetParameter_substitute (interface rely target focus kind sort)
    (prefixMapping rely target focus kind sort)).trans ?_
  let zero : Fin (prefixSize (D := D) (interface rely target focus kind sort)) :=
    ⟨0, by change 0 < 1; decide⟩
  have relies : relyArguments (D := D) (interface rely target focus kind sort) =
      [(rely, classifierValue rely kind (.var zero))] := by
    change [(rely, classifierValue rely kind (.var ((0 : Fin 1).castAdd 0)))] = _
    rfl
  rw [relies]
  change relyFunction rely ((classifierValue rely kind (.var zero)).substitute
    (prefixMapping rely target focus kind sort)) (certifiedCode target sort 4) = _
  rw [IndexSyntax.classifierValue_substitute]
  rfl

def parametersTyped : Derivation (Theory vertex)
    (.substitution (pairContext rely target kind sort)
      (parameters (D := D) (interface rely target focus kind sort))
      (parameterMapping rely target focus kind sort)) := by
  have output := continuationTyped vertex rely target kind sort
  rw [← target_substituted rely target focus kind sort] at output
  exact deriveList (.substitutionExtend (pairContext rely target kind sort)
    (parameterPrefix (D := D) (interface rely target focus kind sort))
    (targetParameter (D := D) (interface rely target focus kind sort))
    (prefixMapping rely target focus kind sort) (constantContinuation rely target kind sort))
    (.cons (prefixTyped vertex rely target focus kind sort)
      (.cons (targetParameterFormed vertex (interface rely target focus kind sort)) (.cons output .nil)))



abbrev firstScope : Scope W 1 :=
  Families.emptyScope.snoc (certifiedMeaning operational rely kind)

abbrev pairScope : Scope W 2 :=
  (firstScope operational rely kind).snoc
    (certifiedAt operational target sort (firstScope operational rely kind).1)

theorem first_read :
    (Classifier.Model.model operational algebra vertex).evaluateContext (firstContext rely kind) =
      some (firstScope operational rely kind) :=
  (Classifier.Model.model operational algebra vertex).evaluateContext_snoc .nil _ Families.emptyScope
    (certifiedMeaning operational rely kind) rfl
    (Classifier.Realization.certified_empty_read operational algebra vertex rely kind)

theorem pair_read :
    (Classifier.Model.model operational algebra vertex).evaluateContext (pairContext rely target kind sort) =
      some (pairScope operational rely target kind sort) :=
  (Classifier.Model.model operational algebra vertex).evaluateContext_snoc (firstContext rely kind) _
    (firstScope operational rely kind)
    (certifiedAt operational target sort (firstScope operational rely kind).1)
    (first_read operational algebra vertex rely kind)
    (Classifier.Realization.certified_read operational algebra vertex _ target sort)

def parameterMap : (pairScope operational rely target kind sort).1 ⟶
    (ContinuationSemantics.parameterScope operational algebra vertex
      (interface rely target focus kind sort)).1 :=
  Classical.choose
    (((parametersTyped vertex rely target focus kind sort).native_sound
      (Classifier.Model.model operational algebra vertex)
      (Classifier.Realization.realization operational algebra vertex)).substitutionAt
      (pairScope operational rely target kind sort)
      (ContinuationSemantics.parameterScope operational algebra vertex (interface rely target focus kind sort))
      (pair_read operational algebra vertex rely target kind sort)
      (ContinuationSemantics.parameters_read operational algebra vertex (interface rely target focus kind sort)))

theorem parameterMap_read :
    (Classifier.Model.model operational algebra vertex).evaluateSubstitution
      (pairScope operational rely target kind sort)
      (ContinuationSemantics.parameterScope operational algebra vertex (interface rely target focus kind sort))
      (parameterMapping rely target focus kind sort) =
        some (parameterMap operational algebra vertex rely target focus kind sort) :=
  Classical.choose_spec
    (((parametersTyped vertex rely target focus kind sort).native_sound
      (Classifier.Model.model operational algebra vertex)
      (Classifier.Realization.realization operational algebra vertex)).substitutionAt
      (pairScope operational rely target kind sort)
      (ContinuationSemantics.parameterScope operational algebra vertex (interface rely target focus kind sort))
      (pair_read operational algebra vertex rely target kind sort)
      (ContinuationSemantics.parameters_read operational algebra vertex (interface rely target focus kind sort)))

def firstMap {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind) : P ⟶ (firstScope operational rely kind).1 :=
  (NativeModel W).toCwf.pair ((NativeModel W).toEmpty P)
    (certifiedMeaning operational rely kind) (CertifiedSections.ofName operational rely kind relyName)

def secondSection {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort) :
    ((certifiedAt operational target sort (firstScope operational rely kind).1).reindex
      (firstMap operational rely kind relyName)).decoded.sections :=
  cast (congrArg (fun type : NativeType P => (type.decoded.sections : Type u))
    (CubeNativeSemanticTelescopes.closed_weaken (certifiedMeaning operational target sort)
      (firstMap operational rely kind relyName)).symm)
    (CertifiedSections.ofName operational target sort targetName)

def pairMap {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort) :
    P ⟶ (pairScope operational rely target kind sort).1 :=
  (NativeModel W).toCwf.pair (firstMap operational rely kind relyName)
    (certifiedAt operational target sort (firstScope operational rely kind).1)
    (secondSection operational rely target kind sort relyName targetName)

def encode {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort) :
    P ⟶ (ContinuationSemantics.parameterScope operational algebra vertex
      (interface rely target focus kind sort)).1 :=
  pairMap operational rely target kind sort relyName targetName ≫
    parameterMap operational algebra vertex rely target focus kind sort

theorem pairMap_zero {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort) :
    (pairScope operational rely target kind sort).2.components
      (pairMap operational rely target kind sort relyName targetName) 0 =
        ⟨certifiedAt operational target sort P,
          CertifiedSections.ofName operational target sort targetName⟩ := by
  refine (ScopeData.components_pair_zero _ _ _ _).trans ?_
  apply Sigma.ext
  · exact CubeNativeSemanticTelescopes.closed_weaken _ _
  · change HEq (secondSection operational rely target kind sort relyName targetName)
      (CertifiedSections.ofName operational target sort targetName)
    unfold secondSection
    exact cast_heq _ _

theorem pairMap_one {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort) :
    (pairScope operational rely target kind sort).2.components
      (pairMap operational rely target kind sort relyName targetName) 1 =
        ⟨certifiedAt operational rely kind P,
          CertifiedSections.ofName operational rely kind relyName⟩ := by
  exact (ScopeData.components_pair_succ _ _ _ _ (0 : Fin 1)).trans
    (ScopeData.components_pair_zero _ _ _ _)


private theorem sectionPoint_heq {P : Wᵒᵖ ⥤ Type u} {A B : NativeType P}
    (types : A = B) {first : A.decoded.sections} {second : B.decoded.sections}
    (values : HEq first second) (point : P.Elements) :
    HEq (first.val point) (second.val point) := by
  cases types
  cases values
  rfl


private theorem substitutedValue_point {P Q : Wᵒᵖ ⥤ Type u}
    {A : NativeType Q} {B : NativeType P}
    {first : A.decoded.sections} {second : B.decoded.sections}
    (mapping : P ⟶ Q)
    (related : Value.substitute (K := (NativeModel W).toCwf) ⟨A, first⟩ mapping = ⟨B, second⟩)
    (point : P.Elements) : HEq (first.val (mapping.mapElements.obj point)) (second.val point) := by
  have types : A.reindex mapping = B := congrArg Sigma.fst related
  have terms : HEq (substituteTerm (C := DisplayedPresheafCwf.presheafCwf W)
      (type := A) first mapping) second :=
    (Sigma.mk.inj related).2
  exact (NativeLocalTypeOperations.substituteTerm_value A first mapping point).symm.trans
    (sectionPoint_heq types terms point)

/-- Reading a certified code commutes with an actual native term substitution,
including the required dependent type transport. -/
theorem certifiedRead_substitution {P Q : Wᵒᵖ ⥤ Type u}
    (carrier : D.Carrier) (selected : HSort)
    (first : (certifiedAt operational carrier selected Q).decoded.sections)
    (second : (certifiedAt operational carrier selected P).decoded.sections)
    (mapping : P ⟶ Q)
    (related : Value.substitute (K := (NativeModel W).toCwf)
      ⟨certifiedAt operational carrier selected Q, first⟩ mapping =
        ⟨certifiedAt operational carrier selected P, second⟩) :
    mapping ≫ IndexSemantics.readClassifier operational carrier selected first =
      IndexSemantics.readClassifier operational carrier selected second := by
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro parameter
  have values : first.val ⟨world, mapping.app world parameter⟩ = second.val ⟨world, parameter⟩ :=
    eq_of_heq (substitutedValue_point mapping related (⟨world, parameter⟩ : P.Elements))
  exact congrArg Subtype.val
    (congrArg ((certifiedRead operational carrier selected).app ⟨world, PUnit.unit⟩) values)

def relySection :
    (certifiedAt operational rely kind (pairScope operational rely target kind sort).1).decoded.sections :=
  Classical.choose
    (((relyTyped vertex rely target kind sort).native_sound
      (Classifier.Model.model operational algebra vertex)
      (Classifier.Realization.realization operational algebra vertex)).termAt
      (pairScope operational rely target kind sort)
      (certifiedAt operational rely kind (pairScope operational rely target kind sort).1)
      (pair_read operational algebra vertex rely target kind sort)
      (Classifier.Realization.certified_read operational algebra vertex _ rely kind))

theorem relySection_read :
    (Classifier.Model.model operational algebra vertex).evaluateTerm
      (pairScope operational rely target kind sort) (.var 1) =
        some ⟨certifiedAt operational rely kind (pairScope operational rely target kind sort).1,
          relySection operational algebra vertex rely target kind sort⟩ :=
  Classical.choose_spec
    (((relyTyped vertex rely target kind sort).native_sound
      (Classifier.Model.model operational algebra vertex)
      (Classifier.Realization.realization operational algebra vertex)).termAt
      (pairScope operational rely target kind sort)
      (certifiedAt operational rely kind (pairScope operational rely target kind sort).1)
      (pair_read operational algebra vertex rely target kind sort)
      (Classifier.Realization.certified_read operational algebra vertex _ rely kind))

def relyClassifier : (pairScope operational rely target kind sort).1 ⟶ Carrier.presheaf operational rely :=
  IndexSemantics.readClassifier operational rely kind
    (relySection operational algebra vertex rely target kind sort)

theorem relyClassifier_read :
    (Classifier.Model.model operational algebra vertex).evaluateTerm
      (pairScope operational rely target kind sort) (relyTerm rely kind) =
        some (Arguments.codeValue operational rely
          (relyClassifier operational algebra vertex rely target kind sort)) :=
  IndexSemantics.classifierValue_read operational algebra vertex _ rely kind (.var 1)
    (relySection operational algebra vertex rely target kind sort)
    (relySection_read operational algebra vertex rely target kind sort)

theorem pairMap_rely {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort) :
    pairMap operational rely target kind sort relyName targetName ≫
      relyClassifier operational algebra vertex rely target kind sort =
        relyName ≫ validInclusion operational rely kind := by
  have variableRead :=  Option.some.inj (relySection_read operational algebra vertex rely target kind sort)
  have related : Value.substitute (K := (NativeModel W).toCwf)
      ⟨certifiedAt operational rely kind (pairScope operational rely target kind sort).1,
        relySection operational algebra vertex rely target kind sort⟩
      (pairMap operational rely target kind sort relyName targetName) =
        ⟨certifiedAt operational rely kind P, CertifiedSections.ofName operational rely kind relyName⟩ :=
    (congrArg (fun value => Value.substitute (K := (NativeModel W).toCwf) value
      (pairMap operational rely target kind sort relyName targetName)) variableRead).symm.trans
        (pairMap_one operational rely target kind sort relyName targetName)
  refine (certifiedRead_substitution operational rely kind
    (relySection operational algebra vertex rely target kind sort)
    (CertifiedSections.ofName operational rely kind relyName)
    (pairMap operational rely target kind sort relyName targetName) related).trans ?_
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro parameter
  exact congrArg Subtype.val
    (CertifiedSections.read_ofName operational rely kind relyName ⟨world, parameter⟩)


abbrev valueScope : Scope W 3 :=
  (pairScope operational rely target kind sort).snoc
    (codeAt operational rely (pairScope operational rely target kind sort).1)

def valueName : (valueScope operational rely target kind sort).1 ⟶ Carrier.presheaf operational rely where
  app _ := TypeCat.ofHom fun value => value.2
  naturality _ _ _ := rfl

abbrev valueProjection : (valueScope operational rely target kind sort).1 ⟶
    (pairScope operational rely target kind sort).1 :=
  totalProjection (codeAt operational rely (pairScope operational rely target kind sort).1).decoded

abbrev membershipMeaning := typingAt operational rely
  (valueName operational rely target kind sort)
  (valueProjection operational rely target kind sort ≫ relyClassifier operational algebra vertex rely target kind sort)

abbrev evidenceScope : Scope W 4 :=
  (valueScope operational rely target kind sort).snoc (membershipMeaning operational algebra vertex rely target kind sort)

theorem value_read :
    (Classifier.Model.model operational algebra vertex).evaluateContext (withValue rely target kind sort) =
      some (valueScope operational rely target kind sort) :=
  (Classifier.Model.model operational algebra vertex).evaluateContext_snoc (pairContext rely target kind sort) _
    (pairScope operational rely target kind sort) _
    (pair_read operational algebra vertex rely target kind sort)
    (Classifier.Realization.code_read operational algebra vertex _ rely)

theorem valueName_read :
    (Classifier.Model.model operational algebra vertex).evaluateTerm
      (valueScope operational rely target kind sort) (.var 0) =
        some (Arguments.codeValue operational rely (valueName operational rely target kind sort)) := by
  apply congrArg some
  apply Sigma.ext
  · exact CubeNativeSemanticTelescopes.closed_weaken _ _
  · rfl

theorem membership_read :
    (Classifier.Model.model operational algebra vertex).evaluateType
      (valueScope operational rely target kind sort) (membershipType rely kind) =
        some (membershipMeaning operational algebra vertex rely target kind sort) := by
  have classifier := (Classifier.Model.model operational algebra vertex).evaluateTerm_rename
    (NativeLocalTypeOperations.products_substitution W) (relyTerm rely kind)
    (valueScope operational rely target kind sort) (pairScope operational rely target kind sort)
    Fin.succ (ModelRenaming.weaken _ _)
    (Arguments.codeValue operational rely (relyClassifier operational algebra vertex rely target kind sort))
    (relyClassifier_read operational algebra vertex rely target kind sort)
  rw [Vectors.codeValue_substitution] at classifier
  exact Classifier.Realization.typing_read operational algebra vertex _ rely _ _ _ _
    (valueName_read operational algebra vertex rely target kind sort) classifier

theorem evidence_read :
    (Classifier.Model.model operational algebra vertex).evaluateContext (withEvidence rely target kind sort) =
      some (evidenceScope operational algebra vertex rely target kind sort) :=
  (Classifier.Model.model operational algebra vertex).evaluateContext_snoc (withValue rely target kind sort) _
    (valueScope operational rely target kind sort) _
    (value_read operational algebra vertex rely target kind sort)
    (membership_read operational algebra vertex rely target kind sort)



theorem parameterClassifier_restrict :
    parameterMap operational algebra vertex rely target focus kind sort ≫
      SingleRelyEvidence.parameterClassifier vertex operational algebra
        (interface rely target focus kind sort) 0 =
      relyClassifier operational algebra vertex rely target kind sort := by
  let iface := interface rely target focus kind sort
  let classifier := SingleRelyEvidence.parameterClassifier vertex operational algebra iface 0
  have substituted :
      (SingleRelyEvidence.parameterClassifierTerm iface 0).substitute
        (parameterMapping rely target focus kind sort) = relyTerm rely kind := by
    unfold SingleRelyEvidence.parameterClassifierTerm
    rw [ContinuationSemantics.relyEntry]
    simp only [IndexSyntax.classifierValue_substitute, TermExpr.substitute]
    rfl
  have read := (Classifier.Model.model operational algebra vertex).evaluateTerm_substitute
    (NativeLocalTypeOperations.products_substitution W)
    (SingleRelyEvidence.parameterClassifierTerm iface 0)
    (pairScope operational rely target kind sort)
    (ContinuationSemantics.parameterScope operational algebra vertex iface)
    (parameterMapping rely target focus kind sort)
    (ModelSubstitution.ofEvaluated _ _ _ _ _ (parameterMap_read operational algebra vertex rely target focus kind sort))
    (Arguments.codeValue operational rely classifier)
    (SingleRelyEvidence.parameterClassifier_read vertex operational algebra iface 0)
  rw [substituted, Vectors.codeValue_substitution] at read
  exact Vectors.codeValue_injective operational rely
    (Option.some.inj (read.symm.trans (relyClassifier_read operational algebra vertex rely target kind sort)))

theorem encoded_classifier {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort) :
    encode operational algebra vertex rely target focus kind sort relyName targetName ≫
      SingleRelyEvidence.parameterClassifier vertex operational algebra
        (interface rely target focus kind sort) 0 =
      relyName ≫ validInclusion operational rely kind := by
  unfold encode
  rw [Category.assoc, parameterClassifier_restrict]
  exact pairMap_rely operational algebra vertex rely target kind sort relyName targetName


def targetSection :
    (certifiedAt operational target sort (pairScope operational rely target kind sort).1).decoded.sections :=
  Classical.choose
    (((targetTyped vertex rely target kind sort).native_sound
      (Classifier.Model.model operational algebra vertex)
      (Classifier.Realization.realization operational algebra vertex)).termAt
      (pairScope operational rely target kind sort)
      (certifiedAt operational target sort (pairScope operational rely target kind sort).1)
      (pair_read operational algebra vertex rely target kind sort)
      (Classifier.Realization.certified_read operational algebra vertex _ target sort))

theorem targetSection_read :
    (Classifier.Model.model operational algebra vertex).evaluateTerm
      (pairScope operational rely target kind sort) (.var 0) =
        some ⟨certifiedAt operational target sort (pairScope operational rely target kind sort).1,
          targetSection operational algebra vertex rely target kind sort⟩ :=
  Classical.choose_spec
    (((targetTyped vertex rely target kind sort).native_sound
      (Classifier.Model.model operational algebra vertex)
      (Classifier.Realization.realization operational algebra vertex)).termAt
      (pairScope operational rely target kind sort)
      (certifiedAt operational target sort (pairScope operational rely target kind sort).1)
      (pair_read operational algebra vertex rely target kind sort)
      (Classifier.Realization.certified_read operational algebra vertex _ target sort))

def targetClassifier : (pairScope operational rely target kind sort).1 ⟶ Carrier.presheaf operational target :=
  IndexSemantics.readClassifier operational target sort
    (targetSection operational algebra vertex rely target kind sort)

theorem pairMap_target {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort) :
    pairMap operational rely target kind sort relyName targetName ≫
      targetClassifier operational algebra vertex rely target kind sort =
        targetName ≫ validInclusion operational target sort := by
  have variableRead := Option.some.inj (targetSection_read operational algebra vertex rely target kind sort)
  have related : Value.substitute (K := (NativeModel W).toCwf)
      ⟨certifiedAt operational target sort (pairScope operational rely target kind sort).1,
        targetSection operational algebra vertex rely target kind sort⟩
      (pairMap operational rely target kind sort relyName targetName) =
        ⟨certifiedAt operational target sort P, CertifiedSections.ofName operational target sort targetName⟩ :=
    (congrArg (fun value => Value.substitute (K := (NativeModel W).toCwf) value
      (pairMap operational rely target kind sort relyName targetName)) variableRead).symm.trans
        (pairMap_zero operational rely target kind sort relyName targetName)
  refine (certifiedRead_substitution operational target sort
    (targetSection operational algebra vertex rely target kind sort)
    (CertifiedSections.ofName operational target sort targetName)
    (pairMap operational rely target kind sort relyName targetName) related).trans ?_
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro parameter
  exact congrArg Subtype.val
    (CertifiedSections.read_ofName operational target sort targetName ⟨world, parameter⟩)

attribute [local irreducible] relySection relyClassifier pairMap

private def memberPoint {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (value type : P ⟶ Carrier.presheaf operational carrier)
    (world : Wᵒᵖ) (parameter : P.obj world)
    (member : Code.Member (value.app world parameter) (type.app world parameter)) :
    (typingAt operational carrier value type).decoded.obj ⟨world, parameter⟩ :=
  ⟨⟨(value.app world parameter, type.app world parameter), member⟩, rfl⟩


abbrev evidenceProjection : (evidenceScope operational algebra vertex rely target kind sort).1 ⟶
    (valueScope operational rely target kind sort).1 :=
  totalProjection (membershipMeaning operational algebra vertex rely target kind sort).decoded

abbrev originalProjection := evidenceProjection operational algebra vertex rely target kind sort ≫
  valueProjection operational rely target kind sort

def evidenceTargetSection :
    (certifiedAt operational target sort (evidenceScope operational algebra vertex rely target kind sort).1).decoded.sections :=
  Classical.choose
    (((targetThere vertex rely target kind sort).native_sound
      (Classifier.Model.model operational algebra vertex)
      (Classifier.Realization.realization operational algebra vertex)).termAt
      (evidenceScope operational algebra vertex rely target kind sort)
      (certifiedAt operational target sort (evidenceScope operational algebra vertex rely target kind sort).1)
      (evidence_read operational algebra vertex rely target kind sort)
      (Classifier.Realization.certified_read operational algebra vertex _ target sort))

theorem evidenceTarget_read :
    (Classifier.Model.model operational algebra vertex).evaluateTerm
      (evidenceScope operational algebra vertex rely target kind sort) (.var 2) =
        some ⟨certifiedAt operational target sort (evidenceScope operational algebra vertex rely target kind sort).1,
          evidenceTargetSection operational algebra vertex rely target kind sort⟩ :=
  Classical.choose_spec
    (((targetThere vertex rely target kind sort).native_sound
      (Classifier.Model.model operational algebra vertex)
      (Classifier.Realization.realization operational algebra vertex)).termAt
      (evidenceScope operational algebra vertex rely target kind sort)
      (certifiedAt operational target sort (evidenceScope operational algebra vertex rely target kind sort).1)
      (evidence_read operational algebra vertex rely target kind sort)
      (Classifier.Realization.certified_read operational algebra vertex _ target sort))

def evidenceTarget : (evidenceScope operational algebra vertex rely target kind sort).1 ⟶ Carrier.presheaf operational target :=
  IndexSemantics.readClassifier operational target sort
    (evidenceTargetSection operational algebra vertex rely target kind sort)

theorem evidenceTarget_restrict :
    originalProjection operational algebra vertex rely target kind sort ≫
      targetClassifier operational algebra vertex rely target kind sort =
        evidenceTarget operational algebra vertex rely target kind sort := by
  have first := Option.some.inj (targetSection_read operational algebra vertex rely target kind sort)
  have last := Option.some.inj (evidenceTarget_read operational algebra vertex rely target kind sort)
  have projection : Value.substitute (K := (NativeModel W).toCwf)
      ((pairScope operational rely target kind sort).2.lookup 0)
      (originalProjection operational algebra vertex rely target kind sort) =
        (evidenceScope operational algebra vertex rely target kind sort).2.lookup 2 := by
    change Value.substitute (K := (NativeModel W).toCwf)
      ((pairScope operational rely target kind sort).2.lookup 0)
      (originalProjection operational algebra vertex rely target kind sort) =
        Value.substitute (K := (NativeModel W).toCwf)
          (Value.substitute (K := (NativeModel W).toCwf)
            ((pairScope operational rely target kind sort).2.lookup 0)
            (valueProjection operational rely target kind sort))
          (evidenceProjection operational algebra vertex rely target kind sort)
    exact Value.substitute_composition (K := (NativeModel W).toCwf)
      ((pairScope operational rely target kind sort).2.lookup 0)
      (valueProjection operational rely target kind sort)
      (evidenceProjection operational algebra vertex rely target kind sort)
  have related := (congrArg (fun value => Value.substitute (K := (NativeModel W).toCwf) value
    (originalProjection operational algebra vertex rely target kind sort)) first).symm.trans
      (projection.trans last)
  exact certifiedRead_substitution operational target sort
    (targetSection operational algebra vertex rely target kind sort)
    (evidenceTargetSection operational algebra vertex rely target kind sort)
    (originalProjection operational algebra vertex rely target kind sort) related

/-- An actual operational rely value and its independently supplied membership
produce a point of the full value-and-evidence context. -/
def inputPoint {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort)
    (world : Wᵒᵖ) (parameter : P.obj world) (value : (operational rely).obj world)
    (member : Code.Member (.operational value) (relyName.app world parameter).val) :
    (evidenceScope operational algebra vertex rely target kind sort).1.obj world := by
  let original := (pairMap operational rely target kind sort relyName targetName).app world parameter
  have classifiers : (relyClassifier operational algebra vertex rely target kind sort).app world original =
      (relyName.app world parameter).val :=
    ConcreteCategory.congr_hom
      (NatTrans.congr_app (pairMap_rely operational algebra vertex rely target kind sort relyName targetName) world)
      parameter
  have actual : Code.Member (.operational value)
      ((relyClassifier operational algebra vertex rely target kind sort).app world original) := by
    rw [classifiers]
    exact member
  let supplied : (valueScope operational rely target kind sort).1.obj world :=
    ⟨original, .operational value⟩
  let evidence : (membershipMeaning operational algebra vertex rely target kind sort).decoded.obj
      ⟨world, supplied⟩ :=
    memberPoint operational rely (valueName operational rely target kind sort)
      (valueProjection operational rely target kind sort ≫ relyClassifier operational algebra vertex rely target kind sort)
      world supplied actual
  exact ⟨supplied, evidence⟩

theorem inputPoint_rely {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort)
    (world : Wᵒᵖ) (parameter : P.obj world) (value : (operational rely).obj world)
    (member : Code.Member (.operational value) (relyName.app world parameter).val) :
    (inputPoint operational algebra vertex rely target kind sort relyName targetName world parameter value member).1.2 =
      .operational value := rfl


theorem inputPoint_target {P : Wᵒᵖ ⥤ Type u}
    (relyName : P ⟶ validPresheaf operational rely kind)
    (targetName : P ⟶ validPresheaf operational target sort)
    (world : Wᵒᵖ) (parameter : P.obj world) (value : (operational rely).obj world)
    (member : Code.Member (.operational value) (relyName.app world parameter).val) :
    (evidenceTarget operational algebra vertex rely target kind sort).app world
      (inputPoint operational algebra vertex rely target kind sort relyName targetName world parameter value member) =
        (targetName.app world parameter).val := by
  rw [← evidenceTarget_restrict]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app (pairMap_target operational algebra vertex rely target kind sort relyName targetName) world)
    parameter

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.SingleRelyParameters
