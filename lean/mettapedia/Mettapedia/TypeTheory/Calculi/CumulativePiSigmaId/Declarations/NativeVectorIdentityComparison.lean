import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllParameterInterpretation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeIdentityCongruence
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeIdentity
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListMaps
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllUniverseMaps
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllUniverseMapPrograms
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Instances.DeclarationConstantTransport
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.HeadMorphism

/-!
# Compatible native Vector and identity declarations

The existing common-upper Vector signature and the existing identity-bearing
List signature are combined at the same universe bound. Their declaration
supports are disjoint. Both formation certificates and all original roots
survive the union. The identity declaration type is formed in the root-free
tower and transported into the joined typed-equality judgment.

Both All type programs have typed-equality formation and a formed input
context in this signature, by ordered parameter interpretation.
The Vector evidence maps retain their formation-sensitive typings and their
constructor computations in this same joined signature. These results do not
establish a neutral-vector inverse, preservation for every untyped root,
global normalization, or conservativity of the combined package.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorIdentityComparison
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeIndexedFamilies
open NativeNaturalVectorFamilies
open NativeVectorAll.Universes.CumulativeElimination

abbrev vectorSignature := NativeVectorAll.Universes.CumulativeElimination.signature
abbrev identitySignature := IntrinsicMaps.listSignatureAt upperLevel

theorem compatible : Signature.Compatible vectorSignature identitySignature := by
  intro name first second firstFound secondFound
  change (NativeNaturalVectorFamilies.rawSignature.entries name).map _ = some first at firstFound
  obtain ⟨firstSource, firstKnown, _⟩ := Option.map_eq_some_iff.mp firstFound
  change (Intrinsic.rawSignature.entries name).map _ = some second at secondFound
  obtain ⟨secondSource, secondKnown, _⟩ := Option.map_eq_some_iff.mp secondFound
  have firstMember := Signature.entries_ofList_mem NativeNaturalVectorFamilies.declarations firstKnown
  have secondMember := Signature.entries_ofList_mem Intrinsic.declarations secondKnown
  have leftNames : name ∈ NativeNaturalVectorFamilies.declarations.map Prod.fst :=
    List.mem_map.mpr ⟨_, firstMember, rfl⟩
  have rightNames : name ∈ Intrinsic.declarations.map Prod.fst :=
    List.mem_map.mpr ⟨_, secondMember, rfl⟩
  have separate : List.Disjoint (NativeNaturalVectorFamilies.declarations.map Prod.fst)
      (Intrinsic.declarations.map Prod.fst) := by
    simp [NativeNaturalVectorFamilies.declarations, Intrinsic.declarations,
      NativeNaturalVectorFamilies.natName, NativeNaturalVectorFamilies.zeroName,
      NativeNaturalVectorFamilies.succName, NativeNaturalVectorFamilies.natEliminateName,
      NativeNaturalVectorFamilies.vecName, NativeNaturalVectorFamilies.vnilName,
      NativeNaturalVectorFamilies.vconsName, NativeNaturalVectorFamilies.vecEliminateName,
      Intrinsic.listName, Intrinsic.nilName, Intrinsic.consName, Intrinsic.eliminateName,
      Intrinsic.identityEliminateName]
  exact False.elim (List.disjoint_left.mp separate leftNames rightNames)

def signature := Signature.merge vectorSignature identitySignature
abbrev rules := extendRules Tower.rules signature

theorem formed : signature.Formed Tower.rules :=
  (NativeVectorAll.Universes.CumulativeElimination.levelInstance.formed
    NativeNaturalVectorFamilies.rawSignature_formed).merge
      (IntrinsicMaps.listSignatureAt_formed upperLevel) compatible

/-- Both installed rule packages include into the same formed signature. -/
theorem vectorInclusion : NativeVectorAll.Universes.CumulativeElimination.rules.Morphism
    rules (fun head => head) :=
  extensionMorphism Tower.rules (Signature.merge_left vectorSignature identitySignature)

theorem identityInclusion : (extendRules Tower.rules identitySignature).Morphism
    rules (fun head => head) :=
  extensionMorphism Tower.rules (Signature.merge_right compatible)

/-- The Vector package by itself has no identity-eliminator declaration. -/
theorem identity_absent_from_vector : vectorSignature.entries Intrinsic.identityEliminateName = none := rfl

theorem forward_formed : FormationSensitive.Judgment rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forward
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forwardType :=
  NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.forward_formed.monoSignature
    (Signature.merge_left vectorSignature identitySignature)

theorem backward_formed : FormationSensitive.Judgment rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backward
    NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backwardType :=
  NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.backward_formed.monoSignature
    (Signature.merge_left vectorSignature identitySignature)

theorem vector_steps {n : Nat} {left right : Tower.Tm n}
    (path : TypedEquality.Reduces NativeVectorAll.Universes.CumulativeElimination.rules left right) :
    TypedEquality.Reduces rules left right := by
  induction path with
  | refl => exact .refl
  | tail _ step ih =>
      apply Relation.ReflTransGen.tail ih
      simpa only [Tm.mapHead_id] using
        step.mapHead (fun head => head) vectorInclusion.headEq vectorInclusion.computation

/-- The whole constructor-vector round trip runs in the identity-bearing
signature, retaining the final supplied tail as well as every head. -/
theorem vector_roundtrip {n : Nat} (source target : LevelExpr Nat)
    (element predicate : Tower.Tm n) (values : List (Tower.Tm n)) (bundle : Tower.Tm n) :
    TypedEquality.Reduces rules
      (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map target source
        element predicate (NativeVectorAll.CanonicalAdequacy.numeral values.length)
          (NativeVectorAll.CanonicalAdequacy.encodeVector element values))
        (.app (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.map source target
          element predicate (NativeVectorAll.CanonicalAdequacy.numeral values.length)
            (NativeVectorAll.CanonicalAdequacy.encodeVector element values)) bundle))
      (PairSpine.expand values.length bundle) :=
  vector_steps (NativeVectorAll.Universes.CumulativeElimination.EvidenceMaps.roundtrip_steps
    source target element predicate values bundle)

theorem opaqueInclusion : NativeVectorAll.Universes.OpaqueFormation.rules.Morphism rules (fun head => head) :=
  extensionMorphism Tower.rules (NativeVectorAll.Universes.OpaqueFormation.includes.trans
    (Signature.merge_left vectorSignature identitySignature))

theorem primitive_typed {n : Nat} (context : Tower.Ctx n) (index : Fin 8) :
    TypedEquality.Typed rules context (.const (NativeVectorAll.Universes.ParameterInterpretation.names index))
      (liftClosed (NativeVectorAll.Universes.ParameterInterpretation.types index)) :=
  (NativeVectorAll.Universes.ParameterInterpretation.primitive_typed context index).of_morphism opaqueInclusion

/-- The same actual input context is formed in typed equality. -/
theorem all_context_formed : TypedEquality.Normalization.CtxFormed rules NativeVectorAll.Universes.context :=
  NativeVectorAll.Universes.ParameterInterpretation.context_full_formed.of_morphism vectorInclusion

theorem lower_all_typed : TypedEquality.Typed rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.subject (sortTm NativeVectorAll.Universes.resultLevel) :=
  NativeVectorAll.Universes.ParameterInterpretation.lower_full_typed.of_morphism vectorInclusion

theorem upper_all_typed : TypedEquality.Typed rules NativeVectorAll.Universes.context
    (NativeVectorAll.Universes.Canonical.typeProgramAtUniverse upperLevel) (sortTm upperLevel) :=
  NativeVectorAll.Universes.ParameterInterpretation.upper_full_typed.of_morphism vectorInclusion

theorem all_inputs_typed {n : Nat} {context : Tower.Ctx n}
    {element predicate length vector : Tower.Tm n}
    (elementTyped : TypedEquality.Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : TypedEquality.Typed rules context predicate
      (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (lengthTyped : TypedEquality.Typed rules context length natTm)
    (vectorTyped : TypedEquality.Typed rules context vector (vecApp element length)) :
    TypedEquality.SubstMor rules NativeVectorAll.Universes.context context
      (NativeVectorAll.Universes.arguments element predicate length vector) := by
  intro index
  fin_cases index
  · exact vectorTyped
  · exact lengthTyped
  · exact predicateTyped
  · exact elementTyped

theorem lower_all_at {n : Nat} {context : Tower.Ctx n}
    {element predicate length vector : Tower.Tm n}
    (elementTyped : TypedEquality.Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : TypedEquality.Typed rules context predicate
      (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (lengthTyped : TypedEquality.Typed rules context length natTm)
    (vectorTyped : TypedEquality.Typed rules context vector (vecApp element length)) :
    TypedEquality.Typed rules context
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse NativeVectorAll.Universes.resultLevel
        element predicate length vector) (sortTm NativeVectorAll.Universes.resultLevel) := by
  simpa only [NativeVectorAll.Universes.Canonical.allTypeAtUniverse,
    NativeVectorAll.Universes.Canonical.typeProgramAtUniverse, NativeVectorAll.Universes.subject,
    sortTm, subst] using
    lower_all_typed.substitute (all_inputs_typed elementTyped predicateTyped lengthTyped vectorTyped)

theorem upper_all_at {n : Nat} {context : Tower.Ctx n}
    {element predicate length vector : Tower.Tm n}
    (elementTyped : TypedEquality.Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel))
    (predicateTyped : TypedEquality.Typed rules context predicate
      (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)))
    (lengthTyped : TypedEquality.Typed rules context length natTm)
    (vectorTyped : TypedEquality.Typed rules context vector (vecApp element length)) :
    TypedEquality.Typed rules context
      (NativeVectorAll.Universes.Canonical.allTypeAtUniverse upperLevel element predicate length vector)
      (sortTm upperLevel) := by
  simpa only [NativeVectorAll.Universes.Canonical.allTypeAtUniverse, sortTm, subst] using
    upper_all_typed.substitute (all_inputs_typed elementTyped predicateTyped lengthTyped vectorTyped)

def identityLevels := IntrinsicMaps.sameLevelSubstitution upperLevel
def identityType := RussellTarski.substLevelsTm identityLevels Intrinsic.identityEliminateType

def identityLevel := LevelExpr.subst identityLevels Intrinsic.identityEliminateDeclarationLevel

theorem identity_entry : signature.entries Intrinsic.identityEliminateName =
    some { type := identityType } := by
  apply Signature.merge_entries_right compatible
  rfl

theorem identity_type_typed : TypedEquality.Typed rules (.nil : Tower.Ctx 0)
    identityType (sortTm identityLevel) := by
  have typed := FormationSensitiveNativeIdentity.TowerFormation.identityEliminateType_typed.mapHead
    (RussellTarski.levelSubstMorphism identityLevels)
  exact typed.of_morphism (Declaration.includeMorphism Tower.rules signature)

theorem identity_constant_typed {n : Nat} (context : Tower.Ctx n) :
    TypedEquality.Typed rules context (.const Intrinsic.identityEliminateName)
      (liftClosed identityType) := by
  apply TypedEquality.Derivable.const (u := .sort identityLevel)
  · change signature.typeOf? Intrinsic.identityEliminateName = some identityType
    exact congrArg (Option.map Entry.type) identity_entry
  · exact identity_type_typed
  · exact .sort _

theorem identity_iota {n : Nat} (type point motive method : Tower.Tm n) :
    rules.computation.step
      (Intrinsic.identityEliminateApp type point motive method point (.refl point)) method :=
  RootStep.declared (Or.inr ⟨Intrinsic.IotaEvidence.identity type point motive method⟩)

theorem natural_iota {n : Nat} (motive zeroCase succCase : Tower.Tm n) :
    rules.computation.step (natEliminateApp motive zeroCase succCase zeroTm) zeroCase :=
  RootStep.declared (Or.inl ⟨IotaEvidence.natZero motive zeroCase succCase⟩)

#print axioms formed
#print axioms identity_constant_typed
#print axioms identity_iota
#print axioms natural_iota

/-! ## Substitution of complete identity arguments -/

def identityMotiveTypeAt {n : Nat} (type point : Tower.Tm n) : Tower.Tm n :=
  .pi type (.pi (.id (rename wk type) (rename wk point) (.var 0)) (sortTm upperLevel))

def identityFullContext := RussellTarski.substLevelsCtx identityLevels
  NativeIndexedFamilies.Intrinsic.contextAXPDYQ

theorem identity_generic_application : TypedEquality.Typed rules identityFullContext
    (Intrinsic.identityEliminateApp (.var 5) (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
    (.app (.app (.var 3) (.var 1)) (.var 0)) :=
  .appElim (.appElim (.appElim (.appElim (.appElim (.appElim
    (identity_constant_typed identityFullContext) (.var 5)) (.var 4)) (.var 3)) (.var 2))
      (.var 1)) (.var 0)

def identityArguments {n : Nat} (type point motive method endpoint path : Tower.Tm n) : Sub Tower.Head 6 n :=
  consSub path (consSub endpoint
    (NativeIndexedFamilies.Intrinsic.identitySchemaSubstitution type point motive method))

theorem identity_application_typed {n : Nat} {context : Tower.Ctx n}
    {type point motive method endpoint path : Tower.Tm n}
    (formedType : TypedEquality.Typed rules context type (sortTm upperLevel))
    (pointTyped : TypedEquality.Typed rules context point type)
    (motiveTyped : TypedEquality.Typed rules context motive (identityMotiveTypeAt type point))
    (methodTyped : TypedEquality.Typed rules context method (.app (.app motive point) (.refl point)))
    (endpointTyped : TypedEquality.Typed rules context endpoint type)
    (pathTyped : TypedEquality.Typed rules context path (.id type point endpoint)) :
    TypedEquality.Typed rules context (Intrinsic.identityEliminateApp type point motive method endpoint path)
      (.app (.app motive endpoint) path) := by
  have parameters : TypedEquality.SubstMor rules identityFullContext context
      (identityArguments type point motive method endpoint path) := by
    intro index
    fin_cases index
    · exact pathTyped
    · exact endpointTyped
    · exact methodTyped
    · exact motiveTyped
    · exact pointTyped
    · exact formedType
  exact identity_generic_application.substitute parameters


def identityContext := RussellTarski.substLevelsCtx identityLevels Intrinsic.contextAXPD

theorem identity_context_formed : TypedEquality.Normalization.CtxFormed rules identityContext := by
  have whole : TypedEquality.Normalization.IsType rules (.nil : Tower.Ctx 0) identityType :=
    ⟨_, .sort _, identity_type_typed⟩
  obtain ⟨element, afterElement⟩ := TypedEquality.Normalization.IsType.pi_parts whole
  obtain ⟨point, afterPoint⟩ := TypedEquality.Normalization.IsType.pi_parts afterElement
  obtain ⟨motive, afterMotive⟩ := TypedEquality.Normalization.IsType.pi_parts afterPoint
  obtain ⟨method, _⟩ := TypedEquality.Normalization.IsType.pi_parts afterMotive
  exact .snoc (.snoc (.snoc (.snoc .nil element) point) motive) method

theorem identity_redex_typed : TypedEquality.Typed rules identityContext
    (Intrinsic.identityEliminateApp (.var 3) (.var 2) (.var 1) (.var 0)
      (.var 2) (.refl (.var 2)))
    (.app (.app (.var 1) (.var 2)) (.refl (.var 2))) := by
  exact identity_application_typed (.var 3) (.var 2) (.var 1) (.var 0)
    (.var 2) (.reflIntro (.var 2))

theorem identity_beta : TypedEquality.Equal rules identityContext
    (Intrinsic.identityEliminateApp (.var 3) (.var 2) (.var 1) (.var 0)
      (.var 2) (.refl (.var 2))) (.var 0)
    (.app (.app (.var 1) (.var 2)) (.refl (.var 2))) :=
  .root (identity_iota _ _ _ _) identity_redex_typed (.var 0)

theorem vector_nil_iota {n : Nat} (element motive nilCase consCase : Tower.Tm n) :
    rules.computation.step
      (vecEliminateApp element motive nilCase consCase zeroTm (vnilApp element)) nilCase :=
  RootStep.declared (Or.inl ⟨NativeNaturalVectorFamilies.IotaEvidence.vecNil
    element motive nilCase consCase⟩)

#print axioms all_context_formed
#print axioms lower_all_typed
#print axioms upper_all_typed
#print axioms identity_application_typed
#print axioms identity_absent_from_vector
#print axioms forward_formed
#print axioms backward_formed
#print axioms vector_roundtrip
#print axioms identity_beta
#print axioms vector_nil_iota

/-! ## Congruence with the installed identity eliminator -/

namespace Congruence

def program {n : Nat} : Tower.Tm n :=
  NativeIdentityCongruence.instantiate upperLevel
    (.const NativeIndexedFamilies.Intrinsic.identityEliminateName)

def programType {n : Nat} : Tower.Tm n :=
  liftClosed (RussellTarski.substLevelsTm (fun _ => upperLevel) NativeIdentityCongruence.type)

theorem program_typed {n : Nat} (context : Tower.Ctx n) :
    TypedEquality.Typed rules context program programType :=
  NativeIdentityCongruence.instantiate_typed signature upperLevel _ (identity_constant_typed context)

/-- A closed application discharges the implementation premise with the
actual identity constant of the joined signature. -/
theorem closed_typed : TypedEquality.Typed rules (.nil : Tower.Ctx 0) program programType :=
  NativeIdentityCongruence.instantiate_typed signature upperLevel _ (identity_constant_typed .nil)

theorem rename_program {n m : Nat} (rho : Ren n m) :
    rename rho (Congruence.program : Tower.Tm n) = (Congruence.program : Tower.Tm m) := by
  unfold Congruence.program NativeIdentityCongruence.instantiate
  rw [rename_subst]
  apply subst_ext
  intro index
  fin_cases index
  rfl

theorem substitute_program {n m : Nat} (sigma : Sub Tower.Head n m) :
    subst sigma (Congruence.program : Tower.Tm n) = (Congruence.program : Tower.Tm m) := by
  unfold Congruence.program NativeIdentityCongruence.instantiate
  rw [subst_comp]
  apply subst_ext
  intro index
  fin_cases index
  rfl


private def body {n : Nat} : Tower.Tm (n + 6) :=
  NativeIndexedFamilies.Intrinsic.identityEliminateApp (.var 5) (.var 2)
    (.lam (.lam (.id (.var 6) (.app (.var 5) (.var 4)) (.app (.var 5) (.var 1)))))
    (.refl (.app (.var 3) (.var 2))) (.var 1) (.var 0)

private def motive {n : Nat} (target function point : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.id (rename wk (rename wk target))
    (.app (rename wk (rename wk function)) (rename wk (rename wk point)))
    (.app (rename wk (rename wk function)) (.var 1))))

theorem reflexivity_steps {n : Nat} (source target function point : Tower.Tm n) :
    TypedEquality.Reduces rules
      (TypedEquality.Normalization.appSpine program
        [source, target, function, point, point, .refl point])
      (.refl (.app function point)) := by
  let sigma : Sub Tower.Head (n + 6) n :=
    consSub (.refl point) (consSub point (consSub point
      (consSub function (consSub target (consSub source ids)))))
  have beta := TypedEquality.Normalization.lams_beta (R := rules) 6
    (body : Tower.Tm (n + 6)) [source, target, function, point, point, .refl point] rfl
  have assignment : TypedEquality.Normalization.extendSub ids
      (fun j => [source, target, function, point, point, .refl point].getD j
        TypedEquality.Normalization.defaultTm) 6 = sigma := rfl
  rw [assignment] at beta
  have targetEq : subst sigma body =
      NativeIndexedFamilies.Intrinsic.identityEliminateApp source point
        (motive target function point) (.refl (.app function point)) point (.refl point) := rfl
  rw [targetEq] at beta
  exact beta.trans (Relation.ReflTransGen.single (.root (identity_iota _ _ _ _)))

#print axioms closed_typed
#print axioms program_typed
#print axioms reflexivity_steps

namespace NaturalControl

open TypedEquality

theorem natural_typed {n : Nat} (context : Tower.Ctx n) :
    Typed rules context natTm (sortTm natLevel) :=
  .const (type := sortTm natLevel) (u := .sort (.succ natLevel))
    (by rfl) (.headType (.sort natLevel)) (.sort (.succ natLevel))

theorem zero_typed {n : Nat} (context : Tower.Ctx n) : Typed rules context zeroTm natTm :=
  .const (type := natTm) (u := .sort natLevel) (by rfl) (natural_typed .nil) (.sort natLevel)

theorem natural_upper {n : Nat} (context : Tower.Ctx n) :
    Typed rules context natTm (sortTm upperLevel) := by
  apply Derivable.sub (natural_typed context)
  apply Derivable.subUniv
  intro valuation
  exact Nat.zero_le _

def functionType {n : Nat} : Tower.Tm n := .pi natTm natTm
def function {n : Nat} : Tower.Tm n := .lam (.var 0)

theorem functionType_formed {n : Nat} (context : Tower.Ctx n) :
    Typed rules context functionType (sortTm (.max natLevel natLevel)) :=
  .piForm (natural_typed context) (.sort _) (natural_typed _) (.sort _) (.sorts _ _)

theorem function_typed {n : Nat} (context : Tower.Ctx n) : Typed rules context function functionType :=
  .lamIntro (functionType_formed context) (.sort _) (.var 0)

def subject : Tower.Tm 0 := TypedEquality.Normalization.appSpine Congruence.program
  [natTm, natTm, function, zeroTm, zeroTm, .refl zeroTm]

theorem subject_at_applications : Typed rules (.nil : Tower.Ctx 0) subject
    (.id natTm (.app function zeroTm) (.app function zeroTm)) :=
  .appElim (.appElim (.appElim (.appElim (.appElim (.appElim
    Congruence.closed_typed (natural_upper .nil)) (natural_upper .nil))
      (function_typed .nil)) (zero_typed .nil)) (zero_typed .nil)) (.reflIntro (zero_typed .nil))

theorem function_beta : Equal rules (.nil : Tower.Ctx 0) (.app function zeroTm) zeroTm natTm :=
  .betaPi (functionType_formed .nil) (.sort _) (.var 0) (zero_typed .nil)

theorem subject_typed : Typed rules (.nil : Tower.Ctx 0) subject (.id natTm zeroTm zeroTm) :=
  .conv subject_at_applications
    (.idCong (.refl (natural_typed .nil)) (.sort _) function_beta function_beta) (.sort _)

theorem computes : Reduces rules subject (.refl zeroTm) :=
  (Congruence.reflexivity_steps natTm natTm function zeroTm).trans
    (Relation.ReflTransGen.single (.congRefl (.betaPi (.var 0) zeroTm)))

theorem source_syntax_distinct : subject ≠ (.refl zeroTm : Tower.Tm 0) := by decide

#print axioms subject_typed
#print axioms computes

end NaturalControl

namespace Pair

def program {n : Nat} : Tower.Tm n :=
  NativeIdentityCongruence.Pair.instantiate upperLevel (Congruence.program : Tower.Tm n)

def programType {n : Nat} : Tower.Tm n :=
  liftClosed (RussellTarski.substLevelsTm (fun _ => upperLevel) NativeIdentityCongruence.Pair.type)

theorem program_typed {n : Nat} (context : Tower.Ctx n) :
    TypedEquality.Typed rules context program programType :=
  NativeIdentityCongruence.Pair.instantiate_typed signature upperLevel _ (Congruence.program_typed context)

def carrier {n : Nat} (domain family : Tower.Tm n) : Tower.Tm n :=
  .sigma domain (.app (rename wk family) (.var 0))

private def function {n : Nat} (head : Tower.Tm n) : Tower.Tm n :=
  .lam (.pair (rename wk head) (.var 0))

private def body {n : Nat} : Tower.Tm (n + 6) :=
  NativeIdentityCongruence.Pair.bodyAt (Congruence.program : Tower.Tm (n + 6))

theorem closed_typed : TypedEquality.Typed rules (.nil : Tower.Ctx 0) program programType :=
  NativeIdentityCongruence.Pair.instantiate_typed signature upperLevel _ Congruence.closed_typed

theorem reflexivity_steps {n : Nat} (domain family head tail : Tower.Tm n) :
    TypedEquality.Reduces rules
      (TypedEquality.Normalization.appSpine program
        [domain, family, head, tail, tail, .refl tail])
      (.refl (.pair head tail)) := by
  have sourceEq : (program : Tower.Tm n) = TypedEquality.Normalization.lams 6 body := by
    unfold program
    rw [NativeIdentityCongruence.Pair.instantiate_lams]
    simp only [NativeIdentityCongruence.Pair.liftOperation, rename_program]
    rfl
  rw [sourceEq]
  let sigma : Sub Tower.Head (n + 6) n :=
    consSub (.refl tail) (consSub tail (consSub tail
      (consSub head (consSub family (consSub domain ids)))))
  have beta := TypedEquality.Normalization.lams_beta (R := rules) 6
    (body : Tower.Tm (n + 6)) [domain, family, head, tail, tail, .refl tail] rfl
  have assignment : TypedEquality.Normalization.extendSub ids
      (fun j => [domain, family, head, tail, tail, .refl tail].getD j
        TypedEquality.Normalization.defaultTm) 6 = sigma := rfl
  rw [assignment] at beta
  have targetEq : subst sigma body = TypedEquality.Normalization.appSpine Congruence.program
      [.app family head, carrier domain family, function head, tail, tail, .refl tail] := by
    unfold body NativeIdentityCongruence.Pair.bodyAt
    rw [TypedEquality.Normalization.subst_appSpine, substitute_program]
    rfl
  rw [targetEq] at beta
  have first := beta.trans
    (Congruence.reflexivity_steps (.app family head) (carrier domain family) (function head) tail)
  have substituted : inst0 tail (.pair (rename wk head) (.var 0)) = .pair head tail := by
    change Tm.pair (inst0 tail (rename wk head)) tail = Tm.pair head tail
    rw [inst0_rename_wk]
  have contraction : StepCore rules.computation rules.headEq
      (.app (function head) tail) (.pair head tail) := by
    simpa only [function, substituted] using
      (StepCore.betaPi (root := rules.computation) (headEq := rules.headEq)
        (.pair (rename wk head) (.var 0)) tail)
  exact first.trans (Relation.ReflTransGen.single (.congRefl contraction))


#print axioms closed_typed
#print axioms reflexivity_steps

namespace NaturalControl

open TypedEquality
open Congruence.NaturalControl (natural_typed natural_upper zero_typed)

def family : Tower.Tm 0 := .lam (.id natTm (.var 0) (.var 0))
def familyType : Tower.Tm 0 := .pi natTm (sortTm upperLevel)

theorem familyType_formed : Typed rules (.nil : Tower.Ctx 0) familyType
    (sortTm (.max natLevel (.succ upperLevel))) :=
  .piForm (natural_typed .nil) (.sort _) (.headType (.sort upperLevel))
    (.sort _) (.sorts _ _)

theorem family_body_typed : Typed rules (.snoc (.nil : Tower.Ctx 0) natTm)
    (.id natTm (.var 0) (.var 0)) (sortTm upperLevel) := by
  apply Derivable.sub (.idForm (natural_typed _) (.sort natLevel) (.var 0) (.var 0))
  apply Derivable.subUniv
  intro valuation
  exact Nat.zero_le _

theorem family_typed : Typed rules (.nil : Tower.Ctx 0) family familyType :=
  .lamIntro familyType_formed (.sort _) family_body_typed

theorem family_beta : Equal rules (.nil : Tower.Ctx 0) (.app family zeroTm)
    (.id natTm zeroTm zeroTm) (sortTm upperLevel) :=
  .betaPi familyType_formed (.sort _) family_body_typed (zero_typed .nil)

def tail : Tower.Tm 0 := .refl zeroTm

theorem tail_typed : Typed rules (.nil : Tower.Ctx 0) tail (.app family zeroTm) :=
  .conv (.reflIntro (zero_typed .nil)) (.symm family_beta) (.sort upperLevel)

def carrier : Tower.Tm 0 := Congruence.Pair.carrier natTm family

def result : Tower.Tm 0 := .refl (.pair zeroTm tail)
def resultType : Tower.Tm 0 := .id carrier (.pair zeroTm tail) (.pair zeroTm tail)

def subject : Tower.Tm 0 := TypedEquality.Normalization.appSpine Congruence.Pair.program
  [natTm, family, zeroTm, tail, tail, .refl tail]

theorem subject_typed : Typed rules (.nil : Tower.Ctx 0) subject resultType :=
  .appElim (.appElim (.appElim (.appElim (.appElim (.appElim
    Congruence.Pair.closed_typed (natural_upper .nil)) family_typed) (zero_typed .nil))
      tail_typed) tail_typed) (.reflIntro tail_typed)

theorem carrier_formed : Typed rules (.nil : Tower.Ctx 0) carrier
    (sortTm (.max natLevel upperLevel)) :=
  .sigmaForm (natural_typed .nil) (.sort natLevel)
    (.appElim family_typed.weaken (.var 0)) (.sort upperLevel) (.sorts _ _)

theorem result_typed : Typed rules (.nil : Tower.Ctx 0) result resultType :=
  .reflIntro (.pairIntro carrier_formed (.sort _) (zero_typed .nil) tail_typed)

theorem computes : Reduces rules subject result :=
  Congruence.Pair.reflexivity_steps natTm family zeroTm tail

#print axioms subject_typed
#print axioms result_typed
#print axioms computes

end NaturalControl

end Pair

end Congruence

/-! ## Typed constructor computation for the actual All type programs -/

namespace AllComputation.Nil

open TypedEquality
open Congruence.NaturalControl (natural_typed zero_typed)

def context : Tower.Ctx 4 := NativeVectorAll.Universes.context
def element : Tower.Tm 4 := .var 3
def predicate : Tower.Tm 4 := .var 2

theorem element_typed : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel) := .var 3
theorem predicate_typed : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)) := .var 2

theorem nil_typed : Typed rules context (vnilApp element) (vecApp element zeroTm) :=
  .appElim (primitive_typed context 5) element_typed

theorem lower_typed : Typed rules context
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse NativeVectorAll.Universes.resultLevel element predicate zeroTm (vnilApp element))
    (sortTm NativeVectorAll.Universes.resultLevel) :=
  lower_all_at element_typed predicate_typed (zero_typed context) nil_typed

theorem upper_typed : Typed rules context
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse upperLevel element predicate zeroTm (vnilApp element))
    (sortTm upperLevel) :=
  upper_all_at element_typed predicate_typed (zero_typed context) nil_typed

theorem unit_typed (level : LevelExpr Nat) : Typed rules context NativeVectorAll.unitType (sortTm level) := by
  apply Derivable.sub (.idForm (natural_typed context) (.sort natLevel) (zero_typed context) (zero_typed context))
  apply Derivable.subUniv
  intro valuation
  exact Nat.zero_le _

theorem nil_root (level : LevelExpr Nat) : rules.computation.step
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse level element predicate zeroTm (vnilApp element))
    NativeVectorAll.unitType := by
  rw [NativeVectorAll.Universes.Canonical.allTypeAtUniverse_eq_eliminate]
  exact RootStep.declared (Or.inl ⟨NativeNaturalVectorFamilies.IotaEvidence.vecNil _ _ _ _⟩)

theorem lower_equal : Equal rules context
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse NativeVectorAll.Universes.resultLevel element predicate zeroTm (vnilApp element))
    NativeVectorAll.unitType (sortTm NativeVectorAll.Universes.resultLevel) :=
  .root (nil_root NativeVectorAll.Universes.resultLevel) lower_typed (unit_typed NativeVectorAll.Universes.resultLevel)

theorem upper_equal : Equal rules context
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse upperLevel element predicate zeroTm (vnilApp element))
    NativeVectorAll.unitType (sortTm upperLevel) :=
  .root (nil_root upperLevel) upper_typed (unit_typed upperLevel)

theorem annotations_equal : Equal rules context
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse NativeVectorAll.Universes.resultLevel element predicate zeroTm (vnilApp element))
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse upperLevel element predicate zeroTm (vnilApp element))
    (sortTm upperLevel) :=
  .trans (.subEq lower_equal (.subUniv (by intro valuation; exact Nat.le_max_left _ _))) (.symm upper_equal)

#print axioms lower_equal
#print axioms upper_equal
#print axioms annotations_equal

end AllComputation.Nil

namespace AllComputation.Cons

open TypedEquality
open NativeVectorAll.Universes.ParameterInterpretation

def context : Tower.Ctx 5 := .snoc NativeVectorAll.Universes.context (.var 3)
def element : Tower.Tm 5 := .var 4
def predicate : Tower.Tm 5 := .var 3
def number : Tower.Tm 5 := .var 2
def head : Tower.Tm 5 := .var 0
def tail : Tower.Tm 5 := .var 1

theorem element_typed : Typed rules context element (sortTm NativeVectorAll.Universes.dataLevel) := .var 4
theorem predicate_typed : Typed rules context predicate (.pi element (sortTm NativeVectorAll.Universes.predicateLevel)) := .var 3
theorem number_typed : Typed rules context number natTm := .var 2
theorem head_typed : Typed rules context head element := .var 0
theorem tail_typed : Typed rules context tail (vecApp element number) := .var 1

theorem successor_typed : Typed rules context (succApp number) natTm :=
  .appElim (NativeVectorIdentityComparison.primitive_typed context 2) number_typed

theorem constructor_typed : Typed rules context (vconsApp element number head tail)
    (vecApp element (succApp number)) :=
  .appElim (.appElim (.appElim (.appElim (NativeVectorIdentityComparison.primitive_typed context 6)
    element_typed) number_typed) head_typed) tail_typed

def tailType (level : LevelExpr Nat) : Tower.Tm 5 :=
  NativeVectorAll.Universes.Canonical.allTypeAtUniverse level element predicate number tail

def rawResult (level : LevelExpr Nat) : Tower.Tm 5 :=
  TypedEquality.Normalization.appSpine (NativeVectorAll.allTypeConsCase predicate)
    [number, head, tail, tailType level]

def result (level : LevelExpr Nat) : Tower.Tm 5 :=
  .sigma (.app predicate head) (rename wk (tailType level))

def inputSub : Sub Tower.Head 13 5 :=
  liftSub NativeVectorAll.Universes.ParameterInterpretation.inputSub

theorem base_assignment : SubstMor rules NativeVectorAll.Universes.ParameterInterpretation.context
    NativeVectorAll.Universes.context NativeVectorAll.Universes.ParameterInterpretation.inputSub :=
  fun index => (NativeVectorAll.Universes.ParameterInterpretation.inputs_typed index).of_morphism opaqueInclusion

theorem assignment : SubstMor rules TypeBranch.context context inputSub := base_assignment.lift (.var 3)

theorem shifted_program (level : LevelExpr Nat) :
    rename wk (NativeVectorAll.Universes.Canonical.typeProgramAtUniverse level) = tailType level := by
  unfold tailType NativeVectorAll.Universes.Canonical.allTypeAtUniverse
  have same : NativeVectorAll.Universes.arguments element predicate number tail =
      (fun index => rename wk (ids index) : Sub Tower.Head 4 5) := by
    funext index
    fin_cases index <;> rfl
  rw [same, ← rename_subst, subst_ids]

theorem tail_readback (level : LevelExpr Nat) :
    subst inputSub (TypeBranch.tailType level) = tailType level := by
  unfold inputSub TypeBranch.tailType
  rw [subst_liftSub_wk, term_readback, shifted_program]

theorem branch_readback :
    subst inputSub TypeBranch.branch = NativeVectorAll.allTypeConsCase predicate := rfl

theorem raw_readback (level : LevelExpr Nat) :
    subst inputSub (TypeBranch.rawResult level) = rawResult level := by
  unfold TypeBranch.rawResult
  rw [TypedEquality.Normalization.subst_appSpine, branch_readback]
  simp only [List.map_cons, List.map_nil]
  rw [tail_readback]
  rfl

theorem result_readback (level : LevelExpr Nat) :
    subst inputSub (TypeBranch.result level) = result level := by
  change Tm.sigma (.app (subst inputSub (.var 3)) (subst inputSub (.var 0)))
    (subst (liftSub inputSub) (rename wk (TypeBranch.tailType level))) = _
  rw [subst_liftSub_wk, tail_readback]
  rfl

theorem raw_typed (level : LevelExpr Nat) (accepted : TypeBranch.branchAccepted level = true)
    (tailTyped : Typed Tower.rules TypeBranch.context (TypeBranch.tailType level) (sortTm level)) :
    Typed rules context (rawResult level) (sortTm level) := by
  have linked := ((TypeBranch.raw_typed level accepted tailTyped).of_morphism
    (Declaration.includeMorphism Tower.rules signature)).substitute assignment
  simpa only [raw_readback, sortTm, subst] using linked

theorem beta_typed (level : LevelExpr Nat) (accepted : TypeBranch.branchAccepted level = true)
    (bound : Tower.rules.cumulative (.sort NativeVectorAll.Universes.predicateLevel) (.sort level))
    (tailTyped : Typed Tower.rules TypeBranch.context (TypeBranch.tailType level) (sortTm level)) :
    Equal rules context (rawResult level) (result level) (sortTm level) := by
  have linked := ((TypeBranch.beta_typed level accepted bound tailTyped).of_morphism
    (Declaration.includeMorphism Tower.rules signature)).substitute assignment
  simpa only [raw_readback, result_readback, sortTm, subst] using linked

theorem cons_root (level : LevelExpr Nat) : rules.computation.step
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse level element predicate
      (succApp number) (vconsApp element number head tail)) (rawResult level) := by
  simp only [rawResult, tailType, NativeVectorAll.Universes.Canonical.allTypeAtUniverse_eq_eliminate]
  exact RootStep.declared (Or.inl ⟨NativeNaturalVectorFamilies.IotaEvidence.vecCons _ _ _ _ _ _ _⟩)

theorem lower_equal : Equal rules context
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse NativeVectorAll.Universes.resultLevel element predicate
      (succApp number) (vconsApp element number head tail)) (result NativeVectorAll.Universes.resultLevel) (sortTm NativeVectorAll.Universes.resultLevel) := by
  have source := lower_all_at element_typed predicate_typed successor_typed constructor_typed
  have raw := raw_typed NativeVectorAll.Universes.resultLevel TypeBranch.lower_branch_accepted TypeBranch.lower_tail_typed
  exact .trans (.root (cons_root NativeVectorAll.Universes.resultLevel) source raw)
    (beta_typed NativeVectorAll.Universes.resultLevel TypeBranch.lower_branch_accepted
      (by intro valuation; exact Nat.le_max_right _ _) TypeBranch.lower_tail_typed)

theorem upper_equal : Equal rules context
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse upperLevel element predicate
      (succApp number) (vconsApp element number head tail)) (result upperLevel) (sortTm upperLevel) := by
  have source := upper_all_at element_typed predicate_typed successor_typed constructor_typed
  have raw := raw_typed upperLevel TypeBranch.upper_branch_accepted TypeBranch.upper_tail_typed
  exact .trans (.root (cons_root upperLevel) source raw)
    (beta_typed upperLevel TypeBranch.upper_branch_accepted
      (by intro valuation; exact Nat.le_trans (Nat.le_max_right _ _) (Nat.le_max_left _ _))
      TypeBranch.upper_tail_typed)

#print axioms lower_equal
#print axioms upper_equal

end AllComputation.Cons

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorIdentityComparison
