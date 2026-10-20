import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.Formation
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementClassifyingEvidence
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementAbstractModelMapComposition

/-!
# Classifying the full authored open native signature

The ambient curried-focus signature receives actual earlier-declaration
formation trees. Its response-presheaf semantics qualifies as a model of all
mixed dependent expressions. The generated contextual model therefore maps
into this semantics with the declaration-admitted uniqueness of complete
contextual cells. This is the dependent classifying property for the declared
signature; it does not identify that model with the bare closed logical
extension or all subobjects of the semantic presheaf category.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.Classifying

open _root_.CategoryTheory
open Mettapedia.TypeTheory
open Calculi.NativeDependent Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf

variable (installed : Joined.Installed)

private abbrev bound : Nat := 4
private theorem positive : 0 < bound := by decide

/-- Formation uses the actual ambient focus carrier, including nonempty
local binder prefixes. -/
def coreHeaders : HeaderFormation (SourceModel.coreSignature installed) :=
  SignatureSum.headers installed.indexed.operational.signature
    (Declarations.signature installed.indexed.classifierVertex
      (CurriedInterfaces.interface installed.indexed))
    installed.indexed.operational.formation
    (Declarations.headerFormation installed.indexed.classifierVertex
      (CurriedInterfaces.interface installed.indexed))

private def carry {judgment : Judgment _}
    (tree : Derivation (SourceModel.coreSignature installed) judgment) :
    Derivation (SourceModel.signature installed) (SignatureSum.judgmentLeft judgment) :=
  SignatureExtension.derivation _ _ (Formation.preservesCore installed) tree

private def sourceCarrierFormed (carrier : (SourceModel.D installed).Carrier) :
    Derivation (SourceModel.signature installed)
      (.type .nil (SourceInjection.sourceType installed.indexed carrier)) :=
  carry installed
    (SignatureSum.derivationLeft installed.indexed.operational.signature
      (Declarations.signature installed.indexed.classifierVertex
        (CurriedInterfaces.interface installed.indexed))
      ((NativeCubeProfile.sourceCarriers installed.indexed.operational).formed carrier))

private def emptyFormed : Derivation (SourceModel.signature installed) (.context .nil) :=
  deriveList .contextNil .nil

private def injectionContextFormed (carrier : (SourceModel.D installed).Carrier) :
    Derivation (SourceModel.signature installed)
      (.context (SourceInjection.injectionContext installed.indexed carrier)) :=
  deriveList (.contextExtend .nil (SourceInjection.sourceType installed.indexed carrier))
    (.cons (emptyFormed installed)
      (.cons (sourceCarrierFormed installed carrier) .nil))

private def codeFormed (carrier : (SourceModel.D installed).Carrier) {n : Nat}
    {context : ContextExpr (SourceInjection.symbols installed.indexed) n}
    (formed : Derivation (SourceModel.signature installed) (.context context)) :
    Derivation (SourceModel.signature installed)
      (.type context (SourceInjection.codeType installed.indexed carrier n)) :=
  deriveList (.typeFamily context (.inl (.inr (.inl (.code carrier)))) Fin.elim0)
    (.cons formed (.cons (emptyFormed installed)
      (.cons (deriveList (.substitutionNil context) (.cons formed .nil)) .nil)))

private theorem emptyFormed_before (limit : Nat) :
    (emptyFormed installed).before limit :=
  deriveList_before .contextNil .nil limit True.intro True.intro

private theorem sourceCarrierFormed_before (carrier : (SourceModel.D installed).Carrier) :
    (sourceCarrierFormed installed carrier).before bound :=
  SignatureExtension.derivation_before _ _ (Formation.preservesCore installed) _ bound
    (SignatureSum.derivationLeft_before installed.indexed.operational.signature
      (Declarations.signature installed.indexed.classifierVertex
        (CurriedInterfaces.interface installed.indexed)) _ bound
      ((NativeCubeProfile.sourceCarriers installed.indexed.operational).before carrier))

private theorem injectionContextFormed_before (carrier : (SourceModel.D installed).Carrier) :
    (injectionContextFormed installed carrier).before bound := by
  apply deriveList_before
  · refine ⟨True.intro, ?_⟩
    exact ((sourceCarrierFormed installed carrier).before_judgment
      (sourceCarrierFormed_before installed carrier)).2
  · exact ⟨emptyFormed_before installed bound,
      sourceCarrierFormed_before installed carrier, True.intro⟩

private theorem codeFormed_before (carrier : (SourceModel.D installed).Carrier) {n : Nat}
    {context : ContextExpr (SourceInjection.symbols installed.indexed) n}
    (formed : Derivation (SourceModel.signature installed) (.context context))
    (ordered : formed.before bound) :
    (codeFormed installed carrier formed).before bound := by
  have contextBefore := formed.before_judgment ordered
  apply deriveList_before
  · exact ⟨contextBefore, positive, fun position => Fin.elim0 position⟩
  · exact ⟨ordered, emptyFormed_before installed bound,
      deriveList_before (.substitutionNil context) _ bound
        ⟨contextBefore, True.intro, fun position => Fin.elim0 position⟩ ⟨ordered, True.intro⟩,
      True.intro⟩

/-- The source alphabet's declarations and all its derivations survive before
new source-to-code injections are installed. -/
def headers :
    HeaderFormation (SourceModel.signature installed) where
  typeHeader symbol := match symbol with
    | .inl symbol => carry installed
          ((coreHeaders installed).typeHeader symbol)
    | .inr impossible => nomatch impossible
  typeHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact SignatureExtension.derivation_before _ _
          (Formation.preservesCore installed) _ _
          ((coreHeaders installed).typeHeader_before symbol)
    | inr impossible => exact nomatch impossible
  termHeader symbol := match symbol with
    | .inl symbol => carry installed
          ((coreHeaders installed).termHeader symbol)
    | .inr carrier => injectionContextFormed installed carrier
  termHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact SignatureExtension.derivation_before _ _
          (Formation.preservesCore installed) _ _
          ((coreHeaders installed).termHeader_before symbol)
    | inr carrier => exact injectionContextFormed_before installed carrier
  termResult symbol := match symbol with
    | .inl symbol => carry installed
          ((coreHeaders installed).termResult symbol)
    | .inr carrier => codeFormed installed carrier
        (injectionContextFormed installed carrier)
  termResult_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact SignatureExtension.derivation_before _ _
          (Formation.preservesCore installed) _ _
          ((coreHeaders installed).termResult_before symbol)
    | inr carrier =>
        exact codeFormed_before installed carrier _
          (injectionContextFormed_before installed carrier)
  predicateHeader symbol := match symbol with
    | .inl symbol => carry installed
          ((coreHeaders installed).predicateHeader symbol)
    | .inr impossible => nomatch impossible
  predicateHeader_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact SignatureExtension.derivation_before _ _
          (Formation.preservesCore installed) _ _
          ((coreHeaders installed).predicateHeader_before symbol)
    | inr impossible => exact nomatch impossible


noncomputable section

/-- Qualification is earned from the actual presheaf operations and the
independently proved generated-header realization. -/
def qualified : Contextual.Interpretation.QualifiedModel
    (SourceModel.signature installed) (NativeModel (Interpretation.worlds installed)) where
  localModel := PresheafNativePredicateModel.model (Interpretation.worlds installed)
  data := (Interpretation.model installed).toAbstract
  realization := (Interpretation.realization installed).toAbstract
  products_substitution :=
    (PresheafNativePredicateModel.qualification (Interpretation.worlds installed)).stableProducts
  products_beta :=
    (PresheafNativePredicateModel.qualification (Interpretation.worlds installed)).productBeta
  products_eta :=
    (PresheafNativePredicateModel.qualification (Interpretation.worlds installed)).productEta

abbrev generated := Contextual.Interpretation.sourceData.{0,1} (headers installed)
abbrev semantic := Contextual.Interpretation.targetData (qualified installed)

/-- The whole generated dependent contextual model, rather than only modal
heads, has this constructor- and declaration-preserving interpretation. -/
def interpretation : Abstract.ModelMap (generated installed) (semantic installed) :=
  Contextual.Classifying.interpretation (headers installed) (qualified installed)

local instance interpretationCategory :
    Category.{1} (Abstract.ModelMap (generated installed) (semantic installed)) :=
  Contextual.ClassifyingCells.modelMapCategory (headers installed)
    ((qualified installed).commonCarrierLift.{0,1,0,1,0,0,0,0})

/-- The comparison is a complete corrected contextual isomorphism. Only
local declaration squares are admitted; whole-expression agreement follows. -/
@[instance_reducible] def interpretationUnique
    (other : Abstract.ModelMap (generated installed) (semantic installed)) :
    Unique (interpretation installed ≅ other) :=
  Contextual.Classifying.comparisonUnique (headers installed) (qualified installed) other

/-- A complete generated derivation supplies a presheaf interpretation with
an arbitrary natural client map. No term-evaluation success is assumed. -/
def client {n : Nat} (context : ContextExpr (Interpretation.symbols installed) n)
    (term : TermExpr (Interpretation.symbols installed) n)
    (type : TypeExpr (Interpretation.symbols installed) n)
    (scope : Scope (Interpretation.worlds installed) n)
    (meaning : NativeLocalTypeFormers.NativeType scope.1)
    (contextRead : (Interpretation.model installed).evaluateContext context = some scope)
    (typeRead : (Interpretation.model installed).evaluateType scope type = some meaning)
    {program : (Interpretation.worlds installed)ᵒᵖ ⥤ Type}
    (interface : program ⟶ scope.1) :
    RefinementPresheafCertificates.Interpretation
      (SourceModel.signature installed) context term type program where
  model := Interpretation.model installed
  realization := Interpretation.realization installed
  semanticContext := scope
  semanticType := meaning
  contextRead := contextRead
  typeRead := typeRead
  interface := interface


section Sections

variable {installed}
variable {n : Nat} {context : ContextExpr (Interpretation.symbols installed) n}
    {term : TermExpr (Interpretation.symbols installed) n}
    {type : TypeExpr (Interpretation.symbols installed) n}
variable (tree : Derivation (SourceModel.signature installed) (.term context term type))
    (scope : Scope (Interpretation.worlds installed) n)
    (meaning : NativeLocalTypeFormers.NativeType scope.1)
    (contextRead : (Interpretation.model installed).evaluateContext context = some scope)
    (typeRead : (Interpretation.model installed).evaluateType scope type = some meaning)

include contextRead in
private theorem abstract_context_read :
    (qualified installed).data.evaluateContext context =
      some (NativeAbstractScope.toGeneric scope) :=
  ((Interpretation.model installed).evaluateContext_compare context).trans
    (congrArg (Option.map NativeAbstractScope.toGeneric) contextRead)

include typeRead in
private theorem abstract_type_read :
    (qualified installed).data.evaluateType (NativeAbstractScope.toGeneric scope) type = some meaning :=
  ((Interpretation.model installed).evaluateType_compare type scope).trans typeRead

/-- Read the full generated type-and-term class through an arbitrary admitted
model map, retaining the complete dependent section at its original context. -/
def sectionImage (mapping : Abstract.ModelMap (generated installed) (semantic installed)) :
    meaning.decoded.sections :=
  Contextual.ClassifyingEvidence.sectionImage (qualified installed) tree
    (NativeAbstractScope.toGeneric scope) meaning
    (abstract_context_read scope contextRead) (abstract_type_read scope meaning typeRead)
    (headers installed) mapping

/-- The generated classifying section equals the independently evaluated
native section, even for an independently supplied model map. -/
theorem sectionImage_readout
    (mapping : Abstract.ModelMap (generated installed) (semantic installed)) :
    (Interpretation.model installed).evaluateTerm scope term =
      some ⟨meaning, sectionImage tree scope meaning contextRead typeRead mapping⟩ := by
  rw [sectionImage, Contextual.ClassifyingEvidence.sectionImage_readout]
  exact ((Interpretation.model installed).evaluateTerm_compare term scope).symm.trans
    (Abstract.Derivation.termSection_readout (qualified installed).data
      (qualified installed).realization (qualified installed).products_substitution
      (qualified installed).products_beta (qualified installed).products_eta tree
      (NativeAbstractScope.toGeneric scope) meaning
      (abstract_context_read scope contextRead) (abstract_type_read scope meaning typeRead))

theorem sectionImage_unique
    (first second : Abstract.ModelMap (generated installed) (semantic installed)) :
    sectionImage tree scope meaning contextRead typeRead first =
      sectionImage tree scope meaning contextRead typeRead second := by
  have same := Option.some.inj
    ((sectionImage_readout tree scope meaning contextRead typeRead first).symm.trans
      (sectionImage_readout tree scope meaning contextRead typeRead second))
  exact eq_of_heq (Sigma.mk.inj same).2

/-- Generated computation equations identify complete sections read by any
admitted maps, not merely their inhabitance or final carrier. -/
theorem sectionImage_equation {other : TermExpr (Interpretation.symbols installed) n}
    (otherTree : Derivation (SourceModel.signature installed) (.term context other type))
    (equation : Derivation (SourceModel.signature installed) (.termEq context term other type))
    (first second : Abstract.ModelMap (generated installed) (semantic installed)) :
    sectionImage tree scope meaning contextRead typeRead first =
      sectionImage otherTree scope meaning contextRead typeRead second := by
  rcases (Interpretation.sound installed equation).termEqAt scope meaning contextRead typeRead with
    ⟨value, firstRead, secondRead⟩
  have firstValue := Option.some.inj
    ((sectionImage_readout tree scope meaning contextRead typeRead first).symm.trans firstRead)
  have secondValue := Option.some.inj
    ((sectionImage_readout otherTree scope meaning contextRead typeRead second).symm.trans secondRead)
  exact (eq_of_heq (Sigma.mk.inj firstValue).2).trans
    (eq_of_heq (Sigma.mk.inj secondValue).2).symm

/-- Source substitution builds a new independently checked derivation. -/
def substituteTree {m : Nat} {source : ContextExpr (Interpretation.symbols installed) m}
    (mapping : Substitution (Interpretation.symbols installed) n m)
    (typed : Derivation (SourceModel.signature installed) (.substitution source context mapping)) :
    Derivation (SourceModel.signature installed)
      (.term source (term.substitute mapping) (type.substitute mapping)) :=
  deriveList (.substituteTerm source context mapping term type) (.cons typed (.cons tree .nil))

/-- Interpreting an actually substituted generated class is the displayed
pullback of its original complete section, independently of the chosen map. -/
theorem sectionImage_substitution {m : Nat}
    {source : ContextExpr (Interpretation.symbols installed) m}
    (mapping : Substitution (Interpretation.symbols installed) n m)
    (typed : Derivation (SourceModel.signature installed) (.substitution source context mapping))
    (sourceScope : Scope (Interpretation.worlds installed) m)
    (sourceRead : (Interpretation.model installed).evaluateContext source = some sourceScope)
    (arrow : sourceScope.1 ⟶ scope.1)
    (mappingRead : (Interpretation.model installed).evaluateSubstitution sourceScope scope mapping = some arrow)
    (first second : Abstract.ModelMap (generated installed) (semantic installed)) :
    sectionImage (substituteTree tree mapping typed) sourceScope (meaning.reindex arrow) sourceRead
      (Interpretation.type_substitution installed type sourceScope scope mapping arrow mappingRead meaning typeRead)
      first =
      DisplayedPresheafComprehension.reindexDisplayedSection arrow meaning.decoded
        (sectionImage tree scope meaning contextRead typeRead second) := by
  have original := sectionImage_readout tree scope meaning contextRead typeRead second
  have substituted := Interpretation.term_substitution installed term sourceScope scope mapping arrow mappingRead
    ⟨meaning, sectionImage tree scope meaning contextRead typeRead second⟩ original
  have generatedRead := sectionImage_readout (substituteTree tree mapping typed) sourceScope
    (meaning.reindex arrow) sourceRead
    (Interpretation.type_substitution installed type sourceScope scope mapping arrow mappingRead meaning typeRead)
    first
  have equalValues := Option.some.inj (generatedRead.symm.trans substituted)
  exact eq_of_heq (Sigma.mk.inj equalValues).2

/-- Naturality uses actual displayed reindexing and an arbitrary client.
Generated equations identify sections, while the original tree is retained. -/
theorem client_substitution
    {program incoming : (Interpretation.worlds installed)ᵒᵖ ⥤ Type}
    (interface : program ⟶ scope.1) (mapping : incoming ⟶ program) :
    (RefinementPresheafCertificateSubstitution.reindex
      (client installed context term type scope meaning contextRead typeRead interface) mapping).classifyingValueSection
        (headers installed) tree =
      DisplayedPresheafComprehension.reindexDisplayedSection mapping
        (client installed context term type scope meaning contextRead typeRead interface).valueFamily
        ((client installed context term type scope meaning contextRead typeRead interface).classifyingValueSection
          (headers installed) tree) :=
  RefinementPresheafCertificates.Interpretation.classifyingValueSection_substitution
    _ (headers installed) tree mapping

end Sections

section Composition

open Mettapedia.GSLT.Core.ContextualLadder
open Contextual.ClassifyingCells Contextual.ModelMapComparison

universe p
variable {C : CwfWithTerminal.{1,1,1,1}}
    (target : Contextual.Interpretation.QualifiedModel.{0,1,1,1,1,p}
      (SourceModel.signature installed) C)

/-- Postcomposition transports the entire contextual and predicate action. -/
def postcompose (mapping : Abstract.ModelMap (semantic installed) target.data) :
    Abstract.ModelMap (generated installed) target.data :=
  (interpretation installed).comp mapping

/-- Every later declaration-preserving implementation is uniquely isomorphic
to the composite, through complete declaration-admitted contextual cells. -/
@[instance_reducible] def postcomposeUnique
    (mapping : Abstract.ModelMap (semantic installed) target.data)
    (other : Abstract.ModelMap (generated installed) target.data) :
    Unique (@Iso (Abstract.ModelMap (generated installed) target.data)
      (modelMapCategory (headers installed) target)
      (postcompose installed target mapping) other) :=
  admittedIsoUnique (headers installed) target (postcompose installed target mapping) other

/-- The comparison's effect on arbitrary open dependent families is derived
from primitive and logical preservation, with no whole-family agreement field. -/
theorem postcompose_type
    (mapping : Abstract.ModelMap (semantic installed) target.data)
    (other : Abstract.ModelMap (generated installed) target.data)
    {n : Nat} (scope : Contextual.SyntacticReification.Scope (SourceModel.signature installed) n)
    (type : (Contextual.Interpretation.SourceModel.{0,1}
      (SourceModel.signature installed)).toCwf.Ty
        (ULift.up ((Contextual.quotientProjection (SourceModel.signature installed)).obj scope.source))) :
    HEq ((postcompose installed target mapping).morphism.toFamilyMorphism.mapType type)
      (other.morphism.toFamilyMorphism.mapType type) :=
  Contextual.ModelMapComparison.type_heq (headers installed) _ _ scope type

/-- The same comparison includes arbitrary definable predicates, without
identifying them with every semantic subobject of the target model. -/
theorem postcompose_predicate
    (mapping : Abstract.ModelMap (semantic installed) target.data)
    (other : Abstract.ModelMap (generated installed) target.data)
    {n : Nat} (scope : Contextual.SyntacticReification.Scope (SourceModel.signature installed) n)
    (predicate : (Contextual.Interpretation.sourceLocalModel.{0,1}
      (SourceModel.signature installed)).doctrine.Predicate
        (ULift.up ((Contextual.quotientProjection (SourceModel.signature installed)).obj scope.source))) :
    HEq ((postcompose installed target mapping).predicates.doctrine.hom _ predicate)
      (other.predicates.doctrine.hom _ predicate) :=
  Contextual.ModelMapComparison.predicate_heq (headers installed) _ _ scope predicate

end Composition

end
end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Open.Classifying
