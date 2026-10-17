import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredBindingDeclarations
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeSequenceBindings
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.BindingSignaturePackage
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeListDeclarations
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.IntrinsicNativeListMapComputation
import Mettapedia.GSLT.LanguageDef.BindingSignatureValuation
import Mettapedia.GSLT.LanguageDef.BindingSignatureWire
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeWireData
import Mettapedia.GSLT.LanguageDef.InferenceCettaWireFormat
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Finset.Basic

/-!
# Native meanings of the original authored type expressions

This extension retains the original `TypeExpr` grammar. `nativeType?` is an
operational representation map; it does not reflect collection-kind equality.
The checked native collection refinement retains its full original type index
and collection discriminator in the actual native term. Multiple binders
receive actual `Nat → A` meanings, and collection payloads use the existing
native List declarations. Vector, bag and set observations remain distinct;
a List representation does not make their quotient equalities identical.

The earlier base/arrow installation keeps its own decoder and coverage.
The present decoder refuses undeclared base sorts and earns the formation
of every accepted complete type in a literal declaration environment.
-/

set_option autoImplicit false

open Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration BindingSignatureEmbedding
open NativeIndexedFamilies IntrinsicMaps

variable {n m : Nat}

/-- This returns actual native syntax, never an alternative carrier grammar.
No constructor supplies a fallback for an unknown base sort. -/
def nativeType? (language : LanguageDef) : TypeExpr → Option (Tower.Tm 0)
  | .base name => (NativeSignature.findSort? language name).map
      (fun position => .const (AuthoredBindingDeclarations.sortDeclName language position))
  | .arrow domain codomain => do
      let left ← nativeType? language domain
      let right ← nativeType? language codomain
      pure (closedArrow left right)
  | .multiBinder domain => (nativeType? language domain).map NativeSequenceBindings.sequenceType
  | .collection _ element => (nativeType? language element).map Intrinsic.listApp

theorem nativeType?_sound {language : LanguageDef} {source : TypeExpr} {native : Tower.Tm 0}
    (read : nativeType? language source = some native) : DeclaredType language source := by
  induction source generalizing native with
  | base name =>
      obtain ⟨position, found, _⟩ := Option.map_eq_some_iff.mp read
      rw [← NativeSignature.findSort?_sound found]
      exact .base position
  | arrow domain codomain leftIH rightIH =>
      cases left : nativeType? language domain with
      | none => simp [nativeType?, left] at read
      | some leftNative =>
          cases right : nativeType? language codomain with
          | none => simp [nativeType?, left, right] at read
          | some rightNative => exact .arrow (leftIH left) (rightIH right)
  | multiBinder domain ih =>
      obtain ⟨value, found, _⟩ := Option.map_eq_some_iff.mp read
      exact .multiBinder (ih found)
  | collection kind element ih =>
      obtain ⟨value, found, _⟩ := Option.map_eq_some_iff.mp read
      exact .collection kind (ih found)

theorem nativeType?_complete {language : LanguageDef} {source : TypeExpr}
    (formed : DeclaredType language source) : ∃ native, nativeType? language source = some native := by
  induction formed with
  | base position =>
      obtain ⟨actual, found⟩ := NativeSignature.findSort?_complete ⟨position, rfl⟩
      exact ⟨.const (AuthoredBindingDeclarations.sortDeclName language actual), by simp [nativeType?, found]⟩
  | arrow _ _ leftIH rightIH =>
      obtain ⟨left, leftRead⟩ := leftIH
      obtain ⟨right, rightRead⟩ := rightIH
      exact ⟨closedArrow left right, by simp [nativeType?, leftRead, rightRead]⟩
  | multiBinder _ ih =>
      obtain ⟨domain, read⟩ := ih
      exact ⟨NativeSequenceBindings.sequenceType domain, by simp [nativeType?, read]⟩
  | collection kind _ ih =>
      obtain ⟨element, read⟩ := ih
      exact ⟨Intrinsic.listApp element, by simp [nativeType?, read]⟩

theorem nativeType?_exact (language : LanguageDef) (source : TypeExpr) :
    (∃ native, nativeType? language source = some native) ↔ DeclaredType language source :=
  ⟨fun ⟨_, read⟩ => nativeType?_sound read, nativeType?_complete⟩

def nativeType {language : LanguageDef} (source : DeclaredSort language) : Tower.Tm 0 :=
  (nativeType? language source.val).get (by
    obtain ⟨value, read⟩ := nativeType?_complete source.property
    rw [read]
    rfl)

theorem nativeType_read {language : LanguageDef} (source : DeclaredSort language) :
    nativeType? language source.val = some (nativeType source) :=
  (Option.some_get _).symm

@[simp] theorem nativeType_arrow {language : LanguageDef} (domain codomain : DeclaredSort language) :
    nativeType (DeclaredSort.arrow domain codomain) = closedArrow (nativeType domain) (nativeType codomain) := by
  have read := (nativeType_read (DeclaredSort.arrow domain codomain)).symm
  simpa [nativeType?, DeclaredSort.arrow, nativeType_read domain, nativeType_read codomain] using read

@[simp] theorem nativeType_multiBinder {language : LanguageDef} (domain : DeclaredSort language) :
    nativeType (DeclaredSort.multiBinder domain) = NativeSequenceBindings.sequenceType (nativeType domain) := by
  have read := (nativeType_read (DeclaredSort.multiBinder domain)).symm
  simpa only [DeclaredSort.multiBinder, nativeType?, nativeType_read domain,
    Option.map_some, Option.some.injEq] using read

@[simp] theorem nativeType_collection {language : LanguageDef} (kind : CollType) (element : DeclaredSort language) :
    nativeType (DeclaredSort.collection kind element) = Intrinsic.listApp (nativeType element) := by
  have read := (nativeType_read (DeclaredSort.collection kind element)).symm
  simpa only [DeclaredSort.collection, nativeType?, nativeType_read element,
    Option.map_some, Option.some.injEq] using read

namespace CollectionObservation

universe u v

/-- These are existing mathematical collection carriers, not another source
syntax. Their equality deliberately retains the declared kind's observations. -/
def Space (kind : CollType) (element : Type u) : Type u :=
  match kind with
  | .vec => List element
  | .hashBag => Multiset element
  | .hashSet => Finset element

/-- The raw List representation is observed through the correct quotient.
Set-valued semantic observation uses classical equality only in this model;
no decidable equality on arbitrary native function values is asserted. -/
noncomputable def observe {element : Type u} (kind : CollType) : List element → Space kind element := by
  classical
  cases kind with
  | vec => exact id
  | hashBag => exact fun values => (values : Multiset element)
  | hashSet => exact List.toFinset

/-- This relation is stated independently of the chosen quotient objects. -/
def Related {element : Type u} : CollType → List element → List element → Prop
  | .vec, left, right => left = right
  | .hashBag, left, right => left.Perm right
  | .hashSet, left, right => ∀ value, value ∈ left ↔ value ∈ right

theorem observe_exact {element : Type u} (kind : CollType) (left right : List element) :
    observe kind left = observe kind right ↔ Related kind left right := by
  classical
  cases kind with
  | vec => rfl
  | hashBag => exact Quotient.eq
  | hashSet =>
      change left.toFinset = right.toFinset ↔ ∀ value, value ∈ left ↔ value ∈ right
      constructor
      · intro same value
        apply Iff.of_eq
        simpa only [List.mem_toFinset] using congrArg (fun finite => value ∈ finite) same
      · intro same
        apply Finset.ext
        intro value
        simpa only [List.mem_toFinset] using same value

theorem Related.refl {element : Type u} (kind : CollType) (values : List element) :
    Related kind values values := by
  cases kind with
  | vec => rfl
  | hashBag => exact List.Perm.refl values
  | hashSet => intro value; exact Iff.rfl

theorem Related.symm {element : Type u} {kind : CollType} {left right : List element}
    (related : Related kind left right) : Related kind right left := by
  cases kind with
  | vec => exact Eq.symm related
  | hashBag => exact List.Perm.symm related
  | hashSet => exact fun value => (related value).symm

theorem Related.trans {element : Type u} {kind : CollType} {first second third : List element}
    (left : Related kind first second) (right : Related kind second third) : Related kind first third := by
  cases kind with
  | vec => exact Eq.trans left right
  | hashBag => exact List.Perm.trans left right
  | hashSet => exact fun value => (left value).trans (right value)

/-- Mapping does not invent collection equality: vectors retain order, bags
retain counts, and sets retain precisely their membership observations. -/
theorem Related.map {element : Type u} {target : Type v} {kind : CollType}
    {left right : List element} (related : Related kind left right) (function : element → target) :
    Related kind (left.map function) (right.map function) := by
  cases kind with
  | vec => exact congrArg (List.map function) related
  | hashBag => exact List.Perm.map function related
  | hashSet =>
      intro value
      constructor
      · intro member
        obtain ⟨source, found, rfl⟩ := List.mem_map.mp member
        exact List.mem_map.mpr ⟨source, (related source).mp found, rfl⟩
      · intro member
        obtain ⟨source, found, rfl⟩ := List.mem_map.mp member
        exact List.mem_map.mpr ⟨source, (related source).mpr found, rfl⟩

theorem bag_preserves_count {element : Type u} [DecidableEq element]
    {left right : List element} (related : Related .hashBag left right) (value : element) :
    left.count value = right.count value := related.count_eq value

theorem set_duplicate {element : Type u} (value : element) (rest : List element) :
    Related .hashSet (value :: value :: rest) (value :: rest) := by
  intro selected
  simp only [List.mem_cons]
  tauto

theorem bag_duplicate_visible {element : Type u} (value : element) :
    ¬ Related .hashBag [value, value] [value] := by
  intro related
  have counts := related.length_eq
  simp only [List.length_cons, List.length_nil] at counts
  omega

theorem vector_order_visible : ¬ Related .vec [0, 1] [1, 0] := by
  change ¬ ([0, 1] : List Nat) = [1, 0]
  decide

theorem bag_order_forgotten {element : Type u} (left right : element) :
    Related .hashBag [left, right] [right, left] := .swap right left []

/-- The original valuation's ordered collection values may be observed
without pretending its raw List equality already is quotient equality. -/
noncomputable def sourceValue {base : String → Type u} (kind : CollType) (element : TypeExpr)
    (value : Mettapedia.GSLT.LanguageDef.BindingSyntax.Valuation.Value base (.collection kind element)) :
    Space kind (Mettapedia.GSLT.LanguageDef.BindingSyntax.Valuation.Value base element) := observe kind value

/-- The finite observation checker compares native syntax, rather than
claiming extensional equality of the functions a syntax term may denote. -/
def checkLists {element : Type u} [DecidableEq element] :
    CollType → List element → List element → Bool
  | .vec, left, right => decide (left = right)
  | .hashBag, left, right => decide (left.Perm right)
  | .hashSet, left, right =>
      left.all (fun value => decide (value ∈ right)) &&
      right.all (fun value => decide (value ∈ left))

theorem checkLists_exact {element : Type u} [DecidableEq element]
    (kind : CollType) (left right : List element) :
    checkLists kind left right = true ↔ Related kind left right := by
  cases kind with
  | vec => exact decide_eq_true_iff
  | hashBag => exact decide_eq_true_iff
  | hashSet =>
      simp only [checkLists, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq]
      constructor
      · intro both value
        exact ⟨both.1 value, both.2 value⟩
      · intro same
        exact ⟨fun value member => (same value).mp member, fun value member => (same value).mpr member⟩

open IntrinsicNativeListMapComputation in
/-- Both payloads are read against the same selected native element type.
Malformed spines never acquire a collection observation. -/
def check (kind : CollType) (element left right : Tower.Tm n) : Bool :=
  match decode element left, decode element right with
  | some first, some second => checkLists kind first second
  | _, _ => false

open IntrinsicNativeListMapComputation in
/-- The observer's authority names the original literal syntax readback and
the independently stated kind-sensitive collection relation. -/
theorem check_exact (kind : CollType) (element left right : Tower.Tm n) :
    check kind element left right = true ↔
      ∃ first second, left = encode element first ∧ right = encode element second ∧
        Related kind first second := by
  cases first : decode element left with
  | none =>
      simp only [check, first, Bool.false_eq_true, false_iff]
      rintro ⟨leftValues, _, same, _, _⟩
      rw [same, decode_encode] at first
      cases first
  | some leftValues =>
      cases second : decode element right with
      | none =>
          simp only [check, first, second, Bool.false_eq_true, false_iff]
          rintro ⟨_, rightValues, _, same, _⟩
          rw [same, decode_encode] at second
          cases second
      | some rightValues =>
          rw [check, first, second, checkLists_exact]
          constructor
          · intro related
            exact ⟨leftValues, rightValues, decode_sound element left leftValues first,
              decode_sound element right rightValues second, related⟩
          · rintro ⟨firstValues, secondValues, leftSame, rightSame, related⟩
            have l : firstValues = leftValues := by
              have parsed := decode_encode element firstValues
              rw [← leftSame, first] at parsed
              exact Option.some.inj parsed.symm
            have r : secondValues = rightValues := by
              have parsed := decode_encode element secondValues
              rw [← rightSame, second] at parsed
              exact Option.some.inj parsed.symm
            cases l
            cases r
            exact related

open IntrinsicNativeListMapComputation in
@[simp] theorem check_encode (kind : CollType) (element : Tower.Tm n)
    (left right : List (Tower.Tm n)) :
    check kind element (encode element left) (encode element right) = checkLists kind left right := by
  simp only [check, decode_encode]

open IntrinsicNativeListMapComputation in
/-- Capture-aware native substitution preserves the collection observation,
including every physical occurrence in a repeated bag payload. -/
theorem check_substitute {kind : CollType} {element left right : Tower.Tm n}
    (accepted : check kind element left right = true) (action : Sub Tower.Head n m) :
    check kind (subst action element) (subst action left) (subst action right) = true := by
  obtain ⟨first, second, leftSame, rightSame, related⟩ := (check_exact kind element left right).1 accepted
  apply (check_exact _ _ _ _).2
  exact ⟨first.map (subst action), second.map (subst action),
    by rw [leftSame, encode_subst], by rw [rightSame, encode_subst], related.map _⟩

end CollectionObservation

namespace Core

/-- Retain the actual three constructor declarations used by sequence
indices; no natural-number eliminator is needed by this finite program. -/
def naturalDeclarations : List (DeclName × Entry Tower.Head) :=
  NativeNaturalVectorFamilies.declarations.take 3

def localDeclarations (language : LanguageDef) : List (DeclName × Entry Tower.Head) :=
  naturalDeclarations ++ AuthoredBindingDeclarations.sortDeclarations language

/-- The original List/relator instance retains its actual root computation;
the new authored sorts and numeral constructors remain opaque declarations. -/
def signature (language : LanguageDef) : Signature Tower.Head where
  entries := fun name =>
    ((FormationSensitiveNativeList.Instantiated.levelInstance Tower.zero).signature.entries name).orElse
      (fun _ => (Signature.ofList (localDeclarations language)).entries name)
  computation := (FormationSensitiveNativeList.Instantiated.levelInstance Tower.zero).signature.computation

def rules (language : LanguageDef) : Rules Tower.Head := extendRules Tower.rules (signature language)

abbrev Typing (language : LanguageDef) {n : Nat} :=
  FormationSensitive.Typing (rules language) (n := n)

theorem listExtension (language : LanguageDef) :
    (FormationSensitiveNativeList.Instantiated.levelInstance Tower.zero).signature.Extends (signature language) where
  entries := by
    intro name entry found
    simp only [signature, found, Option.orElse_some]
  computation := fun step => step

private theorem list_absent_numeric (namePrefix : DeclName) (number : Nat) :
    (FormationSensitiveNativeList.Instantiated.levelInstance Tower.zero).signature.entries
      (.num namePrefix number) = none := by
  simp [LevelInstance.signature, Signature.instantiateLevels,
    IntrinsicRelator.rawSignature, IntrinsicRelator.mapRelName, IntrinsicRelator.nilRelName,
    IntrinsicRelator.consRelName, IntrinsicRelator.eliminateName,
    Intrinsic.rawSignature, Intrinsic.declarations, Signature.ofList, Signature.insert,
    Signature.empty, Intrinsic.listName, Intrinsic.nilName, Intrinsic.consName,
    Intrinsic.eliminateName, Intrinsic.identityEliminateName]

private theorem natural_absent_numeric (namePrefix : DeclName) (number : Nat) :
    (Signature.ofList naturalDeclarations).entries (.num namePrefix number) = none := by
  simp [naturalDeclarations, NativeNaturalVectorFamilies.declarations,
    NativeNaturalVectorFamilies.natName, NativeNaturalVectorFamilies.zeroName,
    NativeNaturalVectorFamilies.succName, Signature.ofList, Signature.insert, Signature.empty]

theorem sort_lookup (language : LanguageDef) (position : Fin language.types.length) :
    (signature language).entries (AuthoredBindingDeclarations.sortDeclName language position) =
      some AuthoredBindingDeclarations.sortEntry := by
  simp only [signature, AuthoredBindingDeclarations.sortDeclName]
  rw [list_absent_numeric, Option.orElse_none, localDeclarations,
    Signature.entries_ofList_append, natural_absent_numeric, Option.orElse_none]
  exact Signature.entries_ofFn (AuthoredBindingDeclarations.sortDeclName language)
    (fun _ => AuthoredBindingDeclarations.sortEntry)
    (AuthoredBindingDeclarations.sortDeclName_injective language) position

theorem naturals (language : LanguageDef) : NativeSequenceBindings.NaturalLookups (signature language) where
  natural := by
    simp [signature, Signature.typeOf?, localDeclarations, naturalDeclarations,
      FormationSensitiveNativeList.Instantiated.levelInstance,
      LevelInstance.signature, Signature.instantiateLevels, IntrinsicRelator.rawSignature,
      Intrinsic.rawSignature, Intrinsic.declarations, Signature.ofList, Signature.insert, Signature.empty,
      NativeNaturalVectorFamilies.declarations, NativeNaturalVectorFamilies.natName,
      NativeNaturalVectorFamilies.zeroName, NativeNaturalVectorFamilies.succName,
      IntrinsicRelator.mapRelName, IntrinsicRelator.nilRelName, IntrinsicRelator.consRelName,
      IntrinsicRelator.eliminateName, Intrinsic.listName, Intrinsic.nilName, Intrinsic.consName,
      Intrinsic.eliminateName, Intrinsic.identityEliminateName]
  zero := by
    simp [signature, Signature.typeOf?, localDeclarations, naturalDeclarations,
      FormationSensitiveNativeList.Instantiated.levelInstance,
      LevelInstance.signature, Signature.instantiateLevels, IntrinsicRelator.rawSignature,
      Intrinsic.rawSignature, Intrinsic.declarations, Signature.ofList, Signature.insert, Signature.empty,
      NativeNaturalVectorFamilies.declarations, NativeNaturalVectorFamilies.natName,
      NativeNaturalVectorFamilies.zeroName, NativeNaturalVectorFamilies.succName,
      IntrinsicRelator.mapRelName, IntrinsicRelator.nilRelName, IntrinsicRelator.consRelName,
      IntrinsicRelator.eliminateName, Intrinsic.listName, Intrinsic.nilName, Intrinsic.consName,
      Intrinsic.eliminateName, Intrinsic.identityEliminateName]
  successor := by
    simp [signature, Signature.typeOf?, localDeclarations, naturalDeclarations,
      FormationSensitiveNativeList.Instantiated.levelInstance,
      LevelInstance.signature, Signature.instantiateLevels, IntrinsicRelator.rawSignature,
      Intrinsic.rawSignature, Intrinsic.declarations, Signature.ofList, Signature.insert, Signature.empty,
      NativeNaturalVectorFamilies.declarations, NativeNaturalVectorFamilies.natName,
      NativeNaturalVectorFamilies.zeroName, NativeNaturalVectorFamilies.succName,
      IntrinsicRelator.mapRelName, IntrinsicRelator.nilRelName, IntrinsicRelator.consRelName,
      IntrinsicRelator.eliminateName, Intrinsic.listName, Intrinsic.nilName, Intrinsic.consName,
      Intrinsic.eliminateName, Intrinsic.identityEliminateName]

theorem sort_formed (language : LanguageDef) (position : Fin language.types.length) :
    Typing language .nil (.const (AuthoredBindingDeclarations.sortDeclName language position)) (sortTm Tower.zero) := by
  exact FormationSensitive.Typing.const (R := rules language) (Γ := .nil)
    (by change (signature language).typeOf? _ = _; rw [Signature.typeOf?, sort_lookup]; rfl)
    (.headType (.sort Tower.zero)) (.sort (.succ Tower.zero))

theorem listConstant_typed (language : LanguageDef) (context : Tower.Ctx n) :
    Typing language context (.const Intrinsic.listName) (liftClosed (listTypeAt Tower.zero)) :=
  (FormationSensitiveNativeList.Instantiated.listConstant_typed Tower.zero context).monoSignature
    (listExtension language)

theorem listApp_typed (language : LanguageDef) {context : Tower.Ctx n} {element : Tower.Tm n}
    (formed : Typing language context element (sortTm Tower.zero)) :
    Typing language context (Intrinsic.listApp element) (sortTm Tower.zero) :=
  FormationSensitiveNativeList.Instantiated.listApp_of_constant Tower.zero
    (listConstant_typed language context) formed

theorem nilConstant_typed (language : LanguageDef) (context : Tower.Ctx n) :
    Typing language context (.const Intrinsic.nilName) (liftClosed (nilTypeAt Tower.zero)) :=
  (FormationSensitiveNativeList.Instantiated.nilConstant_typed Tower.zero context).monoSignature
    (listExtension language)

theorem consConstant_typed (language : LanguageDef) (context : Tower.Ctx n) :
    Typing language context (.const Intrinsic.consName) (liftClosed (consTypeAt Tower.zero)) :=
  (FormationSensitiveNativeList.Instantiated.consConstant_typed Tower.zero context).monoSignature
    (listExtension language)

theorem nilApp_typed (language : LanguageDef) {context : Tower.Ctx n} {element : Tower.Tm n}
    (formed : Typing language context element (sortTm Tower.zero)) :
    Typing language context (Intrinsic.nilApp element) (Intrinsic.listApp element) :=
  FormationSensitiveNativeList.Instantiated.nilApp_of_constant Tower.zero
    (nilConstant_typed language context) formed

theorem consApp_typed (language : LanguageDef) {context : Tower.Ctx n}
    {element head tail : Tower.Tm n} (formed : Typing language context element (sortTm Tower.zero))
    (headTyped : Typing language context head element)
    (tailTyped : Typing language context tail (Intrinsic.listApp element)) :
    Typing language context (Intrinsic.consApp element head tail) (Intrinsic.listApp element) :=
  FormationSensitiveNativeList.Instantiated.consApp_of_constant Tower.zero
    (consConstant_typed language context) formed headTyped tailTyped

/-- The original native List encoder earns formation-sensitive typing for
all its actual payload terms in the admitted context. -/
theorem encode_typed (language : LanguageDef) {context : Tower.Ctx n}
    {element : Tower.Tm n} (formed : Typing language context element (sortTm Tower.zero))
    (values : List (Tower.Tm n)) (typed : ∀ value ∈ values, Typing language context value element) :
    Typing language context (IntrinsicNativeListMapComputation.encode element values)
      (Intrinsic.listApp element) := by
  induction values with
  | nil => exact nilApp_typed language formed
  | cons head tail ih =>
      exact consApp_typed language formed (typed head List.mem_cons_self)
        (ih (fun value member => typed value (List.mem_cons_of_mem head member)))

/-- Every successful full type decoding earns actual refined formation. -/
theorem type_formed {language : LanguageDef} {source : TypeExpr} {native : Tower.Tm 0}
    (read : nativeType? language source = some native) :
    Typing language .nil native (sortTm Tower.zero) := by
  induction source generalizing native with
  | base name =>
      obtain ⟨position, _, same⟩ := Option.map_eq_some_iff.mp read
      cases same
      exact sort_formed language position
  | arrow domain codomain leftIH rightIH =>
      cases left : nativeType? language domain with
      | none => simp [nativeType?, left] at read
      | some leftNative =>
          cases right : nativeType? language codomain with
          | none => simp [nativeType?, left, right] at read
          | some rightNative =>
              have same : closedArrow leftNative rightNative = native := by
                simpa [nativeType?, left, right] using read
              cases same
              exact NativeSequenceBindings.closedArrow_formed (leftIH left) (rightIH right)
  | multiBinder domain ih =>
      simp only [nativeType?, Option.map_eq_some_iff] at read
      obtain ⟨element, elementRead, same⟩ := read
      cases same
      exact NativeSequenceBindings.sequenceType_formed (naturals language) (ih elementRead)
  | collection kind element ih =>
      simp only [nativeType?, Option.map_eq_some_iff] at read
      obtain ⟨element, elementRead, same⟩ := read
      cases same
      exact listApp_typed language (ih elementRead)

/-- The common compiler's formation interface is earned from the actual
full type decoder; it does not accept a supplied typing/adequacy callback. -/
def formation (language : LanguageDef) :
    ClosedOperators.Formation (S := sourceSignature language) (nativeType (language := language)) (rules language) where
  typeUniverse := .sort Tower.zero
  joined := .sort (.max Tower.zero Tower.zero)
  universeIs := .sort Tower.zero
  joinSelf := .sorts Tower.zero Tower.zero
  collapseSelf := by
    intro valuation
    simp [LevelExpr.eval, Tower.zero, LevelTower.zero]
  typeFormed := fun sort => type_formed (nativeType_read sort)

end Core

namespace StructuralPrograms

open Mettapedia.OSLF
open Mettapedia.GSLT.LanguageDef.BindingSyntax

variable {language : LanguageDef}

/-- The operators below are the original full source operators with their
original declared binding arities, reindexed by checked type formation. -/
def lambdaOperator (domain codomain : DeclaredSort language) :
    (sourceSignature language).Op (DeclaredSort.arrow domain codomain) where
  original := .lambda domain.val codomain.val
  arity := [([domain], codomain)]
  projects := rfl

def substitutionOperator (domain codomain : DeclaredSort language) :
    (sourceSignature language).Op codomain where
  original := .subst domain.val codomain.val
  arity := [([domain], codomain), ([], domain)]
  projects := rfl

def multiLambdaOperator (domain codomain : DeclaredSort language) (count : Nat) :
    (sourceSignature language).Op (DeclaredSort.arrow (DeclaredSort.multiBinder domain) codomain) where
  original := .multiLambda domain.val codomain.val count
  arity := [(List.replicate count domain, codomain)]
  projects := by simp [Binding.mapArities, Binding.mapArity, List.map_replicate]

def collectionOperator (kind : CollType) (element : DeclaredSort language) (count : Nat) :
    (sourceSignature language).Op (DeclaredSort.collection kind element) where
  original := .collection kind element.val count
  arity := List.replicate count ([], element)
  projects := by simp [Binding.mapArities, Binding.mapArity, List.map_replicate]

theorem lambda_typed (domain codomain : DeclaredSort language) :
    Core.Typing language .nil ClosedOperators.Derived.identity
      (ClosedOperators.operatorType (nativeType (language := language)) (lambdaOperator domain codomain)) := by
  change Core.Typing language .nil ClosedOperators.Derived.identity
    (closedArrow (closedArrow (nativeType domain) (nativeType codomain))
      (nativeType (DeclaredSort.arrow domain codomain)))
  rw [nativeType_arrow]
  exact ClosedOperators.Derived.identity_typing (Core.formation language)
    ((Core.formation language).closedArrow_formed
      (Core.type_formed (nativeType_read domain)) (Core.type_formed (nativeType_read codomain)))

theorem substitution_typed (domain codomain : DeclaredSort language) :
    Core.Typing language .nil ClosedOperators.Derived.identity
      (ClosedOperators.operatorType (nativeType (language := language)) (substitutionOperator domain codomain)) := by
  change Core.Typing language .nil ClosedOperators.Derived.identity
    (closedArrow (closedArrow (nativeType domain) (nativeType codomain))
      (closedArrow (nativeType domain) (nativeType codomain)))
  exact ClosedOperators.Derived.identity_typing (Core.formation language)
    ((Core.formation language).closedArrow_formed
      (Core.type_formed (nativeType_read domain)) (Core.type_formed (nativeType_read codomain)))

/-- The full original multiple-binder operator has an actual formed native
program, with no finite-list replacement for its sequence argument. -/
theorem multiLambda_typed (domain codomain : DeclaredSort language) (count : Nat) :
    Core.Typing language .nil (NativeSequenceBindings.introduction count)
      (ClosedOperators.operatorType (nativeType (language := language))
        (multiLambdaOperator domain codomain count)) := by
  change Core.Typing language .nil (NativeSequenceBindings.introduction count)
    (closedArrow (ClosedOperators.spineType (S := sourceSignature language)
      (nativeType (language := language)) (List.replicate count domain) (nativeType codomain))
      (nativeType (DeclaredSort.arrow (DeclaredSort.multiBinder domain) codomain)))
  rw [NativeSequenceBindings.curriedType_bindingSpine (source := sourceSignature language)
    (nativeType (language := language)) domain (nativeType codomain) count,
    nativeType_arrow, nativeType_multiBinder]
  exact NativeSequenceBindings.introduction_typed (Core.naturals language) count
    (Core.type_formed (nativeType_read domain)) (Core.type_formed (nativeType_read codomain))

/-- Source collection arguments are physical positions in their original
left-to-right declaration order. Their de Bruijn indices run in reverse. -/
def collectionBody (element : DeclaredSort language) (count : Nat) :
    Tower.Tm (List.replicate count element).length :=
  IntrinsicNativeListMapComputation.encode (liftClosed (nativeType element))
    ((List.finRange (List.replicate count element).length).reverse.map Tm.var)

def collectionProgram (element : DeclaredSort language) (count : Nat) : Tower.Tm 0 :=
  TelescopeAbstraction.closeTerm
    (ClosedOperators.typeContext (S := sourceSignature language)
      (nativeType (language := language)) (List.replicate count element))
    (collectionBody element count)

private theorem argumentsType_replicate (element : DeclaredSort language) (count : Nat) (result : Tower.Tm 0) :
    ClosedOperators.argumentsType (S := sourceSignature language) (nativeType (language := language))
      (List.replicate count ([], element)) result =
      NativeSequenceBindings.curriedType count (nativeType element) result := by
  induction count with
  | zero => rfl
  | succ count ih =>
      simp only [List.replicate_succ, ClosedOperators.argumentsType,
        ClosedOperators.bindingType, ClosedOperators.spineType, ih,
        NativeSequenceBindings.curriedType_succ]

theorem collectionBody_typed (element : DeclaredSort language) (count : Nat) :
    Core.Typing language
      (ClosedOperators.typeContext (S := sourceSignature language)
        (nativeType (language := language)) (List.replicate count element))
      (collectionBody element count) (liftClosed (Intrinsic.listApp (nativeType element))) := by
  apply Core.encode_typed language
    (FormationCheckedTelescopePrograms.liftClosed_typing
      (Core.type_formed (nativeType_read element)) _)
  intro value member
  obtain ⟨position, _, rfl⟩ := List.mem_map.mp member
  have actual := FormationSensitive.Typing.var (R := Core.rules language)
    (Γ := ClosedOperators.typeContext (S := sourceSignature language)
      (nativeType (language := language)) (List.replicate count element)) position
  have lookup := ClosedOperators.Formation.typeContext_lookup
    (S := sourceSignature language) (nativeType (language := language))
    (Binding.varOfIdx (List.replicate count element) position)
  rw [Binding.varIdx_varOfIdx (S := sourceSignature language)
    (List.replicate count element) position] at lookup
  have selected : (List.replicate count element).get position = element := by simp
  have resultType := congrArg (fun sort : DeclaredSort language =>
    (liftClosed (nativeType sort) : Tower.Tm (List.replicate count element).length)) selected
  exact (lookup.trans resultType) ▸ actual

/-- A real closed program constructs the original native List payload from
all declared source occurrences; vector, bag and set share representation
without sharing their observation relation. -/
theorem collection_typed (kind : CollType) (element : DeclaredSort language) (count : Nat) :
    Core.Typing language .nil (collectionProgram element count)
      (ClosedOperators.operatorType (nativeType (language := language))
        (collectionOperator kind element count)) := by
  have formed := Core.listApp_typed language (Core.type_formed (nativeType_read element))
  have closed := (Core.formation language).closeTerm_typing formed
    (collectionBody element count) (collectionBody_typed element count)
  have closedType := (ClosedOperators.closeType_spine (S := sourceSignature language) (nativeType (language := language))
    (List.replicate count element) (Intrinsic.listApp (nativeType element))).trans
    (NativeSequenceBindings.curriedType_bindingSpine (source := sourceSignature language)
      (nativeType (language := language)) element (Intrinsic.listApp (nativeType element)) count)
  have expectedType :
      ClosedOperators.operatorType (nativeType (language := language))
        (collectionOperator kind element count) =
        NativeSequenceBindings.curriedType count (nativeType element) (Intrinsic.listApp (nativeType element)) :=
    (argumentsType_replicate element count (nativeType (DeclaredSort.collection kind element))).trans
      (congrArg (NativeSequenceBindings.curriedType count (nativeType element))
        (nativeType_collection kind element))
  exact expectedType.symm ▸ (closedType ▸ closed)


/-- This exact native action fills de Bruijn slots from physical source
argument positions, with no out-of-range branch. -/
def collectionSub (element : DeclaredSort language) (count : Nat)
    (values : Fin (List.replicate count element).length → Tower.Tm n) :
    Sub Tower.Head (List.replicate count element).length n :=
  fun position => values position.rev

theorem collectionBody_substitute (element : DeclaredSort language) (count : Nat)
    (values : Fin (List.replicate count element).length → Tower.Tm n) :
    subst (collectionSub element count values) (collectionBody element count) =
      IntrinsicNativeListMapComputation.encode (liftClosed (nativeType element)) (List.ofFn values) := by
  simp only [collectionBody, IntrinsicNativeListMapComputation.encode_subst,
    subst_liftClosed, List.map_map, Function.comp_def, Presentation.subst, collectionSub,
    List.finRange_reverse, List.map_map, Fin.rev_rev]
  rw [← List.ofFn_eq_map]

/-- Applying the retained closure consumes the arguments in exactly the
same source order used to construct the payload. -/
theorem collectionApplication (element : DeclaredSort language) (count : Nat)
    (values : Fin (List.replicate count element).length → Tower.Tm n) :
    TelescopeAbstraction.applyClosed
      (ClosedOperators.typeContext (S := sourceSignature language)
        (nativeType (language := language)) (List.replicate count element))
      (collectionSub element count values) (liftClosed (collectionProgram element count)) =
      (List.ofFn values).foldl Tm.app (liftClosed (collectionProgram element count)) := by
  rw [NativeSequenceBindings.applyClosed_arguments
    (ClosedOperators.typeContext (S := sourceSignature language)
      (nativeType (language := language)) (List.replicate count element))
    (collectionSub element count values) (liftClosed (collectionProgram element count))]
  change (List.map (fun position => values position.rev)
      (List.finRange (List.replicate count element).length).reverse).foldl Tm.app _ = _
  rw [List.finRange_reverse, List.map_map]
  simp only [Function.comp_def, Fin.rev_rev]
  rw [← List.ofFn_eq_map]


open StructuralConversionCode

/-- Reuse the existing telescope certificate compiler for every physical
argument. Its internal intermediate endpoints remain actual native terms. -/
def collectionCode (element : DeclaredSort language) (count : Nat)
    (values : Fin (List.replicate count element).length → Tower.Tm n) :
    Code Tower.Head (fun _ => Empty) n :=
  FormationCheckedTelescopePrograms.applicationCode
    (ClosedOperators.typeContext (S := sourceSignature language)
      (nativeType (language := language)) (List.replicate count element))
    (collectionSub element count values) (collectionBody element count)

theorem collectionCode_checked (element : DeclaredSort language) (count : Nat)
    (values : Fin (List.replicate count element).length → Tower.Tm n) :
    (collectionCode element count values).check (fun _ _ => False)
      FormationCheckedTelescopePrograms.noRoot
      ((List.ofFn values).foldl Tm.app (liftClosed (collectionProgram element count)))
      (IntrinsicNativeListMapComputation.encode (liftClosed (nativeType element)) (List.ofFn values)) = true := by
  have actual := FormationCheckedTelescopePrograms.applicationCode_checked
    (ClosedOperators.typeContext (S := sourceSignature language)
      (nativeType (language := language)) (List.replicate count element))
    (collectionSub element count values) (collectionBody element count)
  have endpoints := congrArg₂
    (fun input output : Tower.Tm n =>
      (collectionCode element count values).check (fun _ _ => False)
        FormationCheckedTelescopePrograms.noRoot input output)
    (collectionApplication element count values) (collectionBody_substitute element count values)
  exact endpoints ▸ actual


theorem collectionCode_steps (element : DeclaredSort language) (count : Nat)
    (values : Fin (List.replicate count element).length → Tower.Tm n) :
    (collectionCode element count values).stepCount = count := by
  exact (FormationCheckedTelescopePrograms.applicationCode_stepCount
    (ClosedOperators.typeContext (S := sourceSignature language)
      (nativeType (language := language)) (List.replicate count element))
    (collectionSub element count values) (collectionBody element count)).trans
      List.length_replicate

end StructuralPrograms

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration BindingSignatureEmbedding
open NativeIndexedFamilies IntrinsicMaps


universe u

/-- The independently defined source multiple-binder valuation reads each
position from the same natural index as the native prefix substitution. -/
theorem sourcePrefix_position (language : LanguageDef) (base : String → Type u)
    (domain : TypeExpr) (count : Nat)
    (values : Nat → Mettapedia.GSLT.LanguageDef.BindingSyntax.Valuation.Value base domain)
    (position : Mettapedia.OSLF.Binding.Var
      (Srt := TypeExpr)
      (List.replicate count domain) domain) :
    (Mettapedia.OSLF.Binding.CategoricalBindingModel.projectVar
      (S := Mettapedia.GSLT.LanguageDef.BindingSyntax.signatureOf language)
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.Valuation.Value base) position)
      (Mettapedia.GSLT.LanguageDef.BindingSyntax.Valuation.sequencePrefix language base domain count values) =
      values (Mettapedia.OSLF.Binding.varIdx (S := Mettapedia.GSLT.LanguageDef.BindingSyntax.signatureOf language) position).val := by
  induction count generalizing values with
  | zero => cases position
  | succ count ih =>
      change Mettapedia.OSLF.Binding.Var
        (Srt := TypeExpr)
        (domain :: List.replicate count domain) domain at position
      cases position with
      | zero => rfl
      | succ prior =>
          change (Mettapedia.OSLF.Binding.CategoricalBindingModel.projectVar
            (S := Mettapedia.GSLT.LanguageDef.BindingSyntax.signatureOf language)
            (Mettapedia.GSLT.LanguageDef.BindingSyntax.Valuation.Value base) prior)
            (Mettapedia.GSLT.LanguageDef.BindingSyntax.Valuation.sequencePrefix language base domain count
              (fun index => values (index + 1))) = values ((Mettapedia.OSLF.Binding.varIdx (S := Mettapedia.GSLT.LanguageDef.BindingSyntax.signatureOf language) prior).val + 1)
          exact ih (fun index => values (index + 1)) prior

namespace FullHeaders

variable {language : LanguageDef}

/-- The parameter interpretation is exactly the original independent source
operation, followed by checked complete type formation. -/
def parameter? (language : LanguageDef) (parameter : TermParam) : Option (DeclaredSort language) :=
  (Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter).bind (sort? language)

theorem parameter_source {parameter : TermParam} {sorted : DeclaredSort language}
    (accepted : parameter? language parameter = some sorted) :
    Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter = some sorted.val := by
  cases original : Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter with
  | none => simp [parameter?, original] at accepted
  | some source =>
      simp only [parameter?, original, Option.bind_some] at accepted
      rw [sort?_source accepted]

/-- Finite headers retain each parameter occurrence and its original type;
there is no generated alternative source constructor grammar. -/
def header? (language : LanguageDef) (origin : Fin language.terms.length) : Option (Tower.Tm 0) := do
  let parameters ← NativeSignature.decodeList (parameter? language) language.terms[origin.val].params
  let result ← sort? language (.base language.terms[origin.val].category)
  pure (ClosedOperators.argumentsType (S := sourceSignature language)
    (nativeType (language := language)) (parameters.map (fun sort => ([], sort))) (nativeType result))

/-- Header admission refers only to the authored typing of parameter shapes
and its finite sort declarations, independently of this native header decoder. -/
def AdmittedHeader (language : LanguageDef) (origin : Fin language.terms.length) : Prop :=
  (∀ parameter ∈ language.terms[origin.val].params,
    ∃ source, Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter = some source ∧
      DeclaredType language source) ∧
  DeclaredType language (.base language.terms[origin.val].category)

theorem header_sound {origin : Fin language.terms.length} {native : Tower.Tm 0}
    (accepted : header? language origin = some native) : AdmittedHeader language origin := by
  cases parameterRead : NativeSignature.decodeList (parameter? language) language.terms[origin.val].params with
  | none => simp [header?, parameterRead] at accepted
  | some parameters =>
      cases resultRead : sort? language (.base language.terms[origin.val].category) with
      | none => simp [header?, parameterRead, resultRead] at accepted
      | some result =>
          have original := NativeSignature.decodeList_sound parameterRead
          have decorated : List.Forall₂
              (fun parameter sorted =>
                (∃ source, Mettapedia.GSLT.LanguageDef.WellSorted.parameterType? parameter = some source ∧
                  DeclaredType language source) ∧ parameter? language parameter = some sorted)
              language.terms[origin.val].params parameters :=
            original.imp (fun parameter sorted found =>
              ⟨⟨sorted.val, parameter_source found, sorted.property⟩, found⟩)
          exact ⟨((List.forall₂_and_left _ _).mp decorated).1,
            (sort?_source resultRead) ▸ result.property⟩

theorem header_complete {origin : Fin language.terms.length}
    (formed : AdmittedHeader language origin) : ∃ native, header? language origin = some native := by
  have each : ∀ parameter ∈ language.terms[origin.val].params,
      ∃ sorted, parameter? language parameter = some sorted := by
    intro parameter member
    obtain ⟨source, interpreted, sourceFormed⟩ := formed.1 parameter member
    exact ⟨⟨source, sourceFormed⟩, by simp only [parameter?, interpreted, Option.bind_some]; exact sort?_readback ⟨source, sourceFormed⟩⟩
  obtain ⟨parameters, parameterRead⟩ := NativeSignature.decodeList_exists each
  have resultRead := sort?_readback (⟨.base language.terms[origin.val].category, formed.2⟩ : DeclaredSort language)
  exact ⟨_, by simp only [header?, parameterRead, resultRead]; rfl⟩

theorem header_exact (language : LanguageDef) (origin : Fin language.terms.length) :
    (∃ native, header? language origin = some native) ↔ AdmittedHeader language origin :=
  ⟨fun ⟨_, accepted⟩ => header_sound accepted, header_complete⟩

/-- Every accepted native header is formed before its constructor is
installed; arbitrary forward theorem or constructor soundness is not assumed. -/
theorem header_formed {origin : Fin language.terms.length} {native : Tower.Tm 0}
    (accepted : header? language origin = some native) :
    Core.Typing language .nil native (sortTm Tower.zero) := by
  cases parameterRead : NativeSignature.decodeList (parameter? language) language.terms[origin.val].params with
  | none => simp [header?, parameterRead] at accepted
  | some parameters =>
      cases resultRead : sort? language (.base language.terms[origin.val].category) with
      | none => simp [header?, parameterRead, resultRead] at accepted
      | some result =>
          have same : ClosedOperators.argumentsType (S := sourceSignature language)
              (nativeType (language := language)) (parameters.map (fun sort => ([], sort)))
              (nativeType result) = native := by
            simpa [header?, parameterRead, resultRead] using accepted
          exact same ▸ (Core.formation language).argumentsType_formed
            (parameters.map (fun sort => ([], sort))) (Core.type_formed (nativeType_read result))

def headers? (language : LanguageDef) : Option (List (Tower.Tm 0)) :=
  NativeSignature.decodeList (header? language) (List.finRange language.terms.length)

theorem headers_length {headers : List (Tower.Tm 0)} (read : headers? language = some headers) :
    headers.length = language.terms.length := by
  have actual := (NativeSignature.decodeList_sound read).length_eq.symm
  simpa only [List.length_finRange] using actual

theorem headers_complete (formed : ∀ origin, AdmittedHeader language origin) :
    ∃ headers, headers? language = some headers :=
  NativeSignature.decodeList_exists (fun origin _ => header_complete (formed origin))

/-- A successful finite declaration compilation retains its literal source
header decoder equation rather than a supplied adequacy assertion. -/
structure Installation (language : LanguageDef) where
  headers : List (Tower.Tm 0)
  decoded : headers? language = some headers

def install? (language : LanguageDef) : Option (Installation language) :=
  match read : headers? language with
  | none => none
  | some headers => some ⟨headers, read⟩

theorem install?_complete (formed : ∀ origin, AdmittedHeader language origin) :
    ∃ installed, install? language = some installed := by
  obtain ⟨headers, read⟩ := headers_complete formed
  unfold install?
  split
  · rename_i refused
    rw [read] at refused
    cases refused
  · exact ⟨_, rfl⟩

namespace Installation

variable (installed : Installation language)

theorem count : installed.headers.length = language.terms.length :=
  headers_length installed.decoded

def header (origin : Fin language.terms.length) : Tower.Tm 0 :=
  installed.headers[origin.val]'(by rw [installed.count]; exact origin.isLt)

theorem header_read (origin : Fin language.terms.length) :
    header? language origin = some (installed.header origin) := by
  have related := (NativeSignature.decodeList_sound installed.decoded).get
    (i := origin.val) (by simpa only [List.length_finRange] using origin.isLt)
    (by rw [installed.count]; exact origin.isLt)
  have index : (List.finRange language.terms.length).get
      ⟨origin.val, by simpa only [List.length_finRange] using origin.isLt⟩ = origin := by
    apply Fin.ext
    simp only [List.get_eq_getElem, List.getElem_finRange, Fin.val_cast]
  rw [index] at related
  simpa only [header, List.get_eq_getElem] using related

/-- Read the original finite parameter vector from the same header decoder;
there is no default for a malformed or unsupported binder declaration. -/
def parameters (installed : Installation language) (origin : Fin language.terms.length) : List (DeclaredSort language) :=
  (NativeSignature.decodeList (parameter? language) language.terms[origin.val].params).get (by
    cases read : NativeSignature.decodeList (parameter? language) language.terms[origin.val].params with
    | none =>
        have accepted := installed.header_read origin
        simp [header?, read] at accepted
    | some parameters => rfl)

theorem parameters_read (origin : Fin language.terms.length) :
    NativeSignature.decodeList (parameter? language) language.terms[origin.val].params =
      some (installed.parameters origin) := (Option.some_get _).symm

def result (installed : Installation language) (origin : Fin language.terms.length) : DeclaredSort language :=
  (sort? language (.base language.terms[origin.val].category)).get (by
    cases read : sort? language (.base language.terms[origin.val].category) with
    | none =>
        have accepted := installed.header_read origin
        simp [header?, installed.parameters_read origin, read] at accepted
    | some result => rfl)

theorem result_read (origin : Fin language.terms.length) :
    sort? language (.base language.terms[origin.val].category) = some (installed.result origin) :=
  (Option.some_get _).symm

theorem parameters_count (origin : Fin language.terms.length) :
    (installed.parameters origin).length = language.terms[origin.val].params.length :=
  (NativeSignature.decodeList_sound (installed.parameters_read origin)).length_eq.symm

theorem header_parameters (origin : Fin language.terms.length) :
    installed.header origin = ClosedOperators.argumentsType (S := sourceSignature language)
      (nativeType (language := language))
      ((installed.parameters origin).map (fun sort => ([], sort)))
      (nativeType (installed.result origin)) := by
  have accepted := installed.header_read origin
  simpa [header?, installed.parameters_read origin, installed.result_read origin] using accepted.symm

theorem source_admitted (source : Installation language) : ∀ origin, AdmittedHeader language origin :=
  fun origin => header_sound (source.header_read origin)

/-- Every authored constructor position is retained, including repeated types
and physically distinct parameter occurrences. -/
def declarations : List (DeclName × Entry Tower.Head) :=
  List.ofFn (fun origin : Fin language.terms.length =>
    (AuthoredBindingDeclarations.constructorDeclName language origin, ⟨installed.header origin, none⟩))

def signature : Signature Tower.Head where
  entries := fun name => (Core.signature language).entries name |>.orElse
    (fun _ => (Signature.ofList installed.declarations).entries name)
  computation := (Core.signature language).computation

def rules : Rules Tower.Head := extendRules Tower.rules installed.signature

abbrev Typing {n : Nat} := FormationSensitive.Typing installed.rules (n := n)

theorem extension : (Core.signature language).Extends installed.signature where
  entries := by
    intro name entry found
    simp only [signature, found, Option.orElse_some]
  computation := fun step => step

private theorem constructor_absent (origin : Fin language.terms.length) :
    (Core.signature language).entries
      (AuthoredBindingDeclarations.constructorDeclName language origin) = none := by
  have listNone : (FormationSensitiveNativeList.Instantiated.levelInstance Tower.zero).signature.entries
      (AuthoredBindingDeclarations.constructorDeclName language origin) = none := by
    simp [AuthoredBindingDeclarations.constructorDeclName,
      FormationSensitiveNativeList.Instantiated.levelInstance,
      LevelInstance.signature, Signature.instantiateLevels, IntrinsicRelator.rawSignature,
      Intrinsic.rawSignature, Intrinsic.declarations, Signature.ofList, Signature.insert, Signature.empty,
      IntrinsicRelator.mapRelName, IntrinsicRelator.nilRelName, IntrinsicRelator.consRelName,
      IntrinsicRelator.eliminateName, Intrinsic.listName, Intrinsic.nilName, Intrinsic.consName,
      Intrinsic.eliminateName, Intrinsic.identityEliminateName]
  have naturalNone : (Signature.ofList Core.naturalDeclarations).entries
      (AuthoredBindingDeclarations.constructorDeclName language origin) = none := by
    simp [AuthoredBindingDeclarations.constructorDeclName, Core.naturalDeclarations,
      NativeNaturalVectorFamilies.declarations, NativeNaturalVectorFamilies.natName,
      NativeNaturalVectorFamilies.zeroName, NativeNaturalVectorFamilies.succName,
      Signature.ofList, Signature.insert, Signature.empty]
  have sortNone : (Signature.ofList (AuthoredBindingDeclarations.sortDeclarations language)).entries
      (AuthoredBindingDeclarations.constructorDeclName language origin) = none := by
    cases found : (Signature.ofList (AuthoredBindingDeclarations.sortDeclarations language)).entries
        (AuthoredBindingDeclarations.constructorDeclName language origin) with
    | none => rfl
    | some entry =>
        have member := Signature.entries_ofList_mem _ found
        obtain ⟨position, same⟩ := List.mem_ofFn.mp member
        exact (AuthoredBindingDeclarations.constructor_ne_sort language origin position
          (congrArg Prod.fst same).symm).elim
  simp only [Core.signature, listNone, Option.orElse_none, Core.localDeclarations,
    Signature.entries_ofList_append, naturalNone, sortNone]

 theorem constructor_lookup (origin : Fin language.terms.length) :
    installed.signature.entries (AuthoredBindingDeclarations.constructorDeclName language origin) =
      some ⟨installed.header origin, none⟩ := by
  change ((Core.signature language).entries
    (AuthoredBindingDeclarations.constructorDeclName language origin)).orElse _ = _
  rw [constructor_absent, Option.orElse_none]
  exact Signature.entries_ofFn
    (AuthoredBindingDeclarations.constructorDeclName language)
    (fun origin => ⟨installed.header origin, none⟩)
    (AuthoredBindingDeclarations.constructorDeclName_injective language) origin

/-- A literal constructor name selects exactly its independently decoded
full source header, so a changed result or parameter type is rejected. -/
theorem constructor_type_exact (origin : Fin language.terms.length) (type : Tower.Tm 0) :
    installed.signature.typeOf? (AuthoredBindingDeclarations.constructorDeclName language origin) = some type ↔
      type = installed.header origin := by
  simp only [Signature.typeOf?, installed.constructor_lookup, Option.map_some, Option.some.injEq]
  exact eq_comm

/-- Unknown names cannot acquire a declaration from this finite installation. -/
theorem missing_type {name : DeclName}
    (coreMissing : (Core.signature language).entries name = none)
    (constructorsMissing : ∀ origin, name ≠ AuthoredBindingDeclarations.constructorDeclName language origin) :
    installed.signature.typeOf? name = none := by
  have declarationsMissing : (Signature.ofList installed.declarations).entries name = none := by
    cases found : (Signature.ofList installed.declarations).entries name with
    | none => rfl
    | some entry =>
        have member := Signature.entries_ofList_mem _ found
        obtain ⟨origin, same⟩ := List.mem_ofFn.mp member
        exact (constructorsMissing origin (congrArg Prod.fst same).symm).elim
  simp only [Signature.typeOf?, signature, coreMissing, Option.orElse_none,
    declarationsMissing, Option.map_none]

 theorem header_formed (origin : Fin language.terms.length) :
    installed.Typing .nil (installed.header origin) (sortTm Tower.zero) :=
  (FullHeaders.header_formed (installed.header_read origin)).monoSignature installed.extension

 theorem constructor_typed (origin : Fin language.terms.length) :
    installed.Typing .nil
      (.const (AuthoredBindingDeclarations.constructorDeclName language origin))
      (installed.header origin) := by
  simpa only [TelescopeAbstraction.liftClosed_zero] using
    (FormationSensitive.Typing.const (R := installed.rules) (Γ := .nil)
      (by change installed.signature.typeOf? _ = _
          rw [Signature.typeOf?, installed.constructor_lookup]; rfl)
      (installed.header_formed origin) (.sort Tower.zero))

 theorem declaration_count : installed.declarations.length = language.terms.length :=
  List.length_ofFn

end Installation

/-- Executable full installation has exactly the independently admitted
finite family of original source constructor headers as its coverage. -/
theorem install?_exact (language : LanguageDef) :
    (∃ installed, install? language = some installed) ↔
      ∀ origin, AdmittedHeader language origin :=
  ⟨fun ⟨installed, _⟩ => installed.source_admitted, install?_complete⟩

/-- The source function type of an opened binding argument retains its
innermost-first binder list and its original result sort. -/
def bindingSort : List (DeclaredSort language) → DeclaredSort language → DeclaredSort language
  | [], result => result
  | domain :: rest, result => bindingSort rest (DeclaredSort.arrow domain result)

theorem bindingSort_native (bound : List (DeclaredSort language)) (result : DeclaredSort language) :
    nativeType (bindingSort bound result) =
      ClosedOperators.bindingType (S := sourceSignature language)
        (nativeType (language := language)) bound result := by
  induction bound generalizing result with
  | nil => rfl
  | cons domain rest ih =>
      exact (ih (DeclaredSort.arrow domain result)).trans
        (congrArg (ClosedOperators.spineType (S := sourceSignature language)
          (nativeType (language := language)) rest) (nativeType_arrow domain result))

namespace ParameterPrograms

open Mettapedia.GSLT.LanguageDef.BindingSyntax
open Mettapedia.OSLF

/-- Reconstruct the representation form declared by the original parameter;
only a multiple binder needs a sequence-reading native adapter. -/
def program {parameter : TermParam} {binders : List TypeExpr} {result : TypeExpr} :
    ParameterScope parameter binders result → Tower.Tm 0
  | .simple _ _ => ClosedOperators.Derived.identity
  | .abstraction _ _ _ _ => ClosedOperators.Derived.identity
  | .abstractionBase _ _ _ => ClosedOperators.Derived.identity
  | .multiAbstraction _ _ _ _ count => NativeSequenceBindings.introduction count
  | .multiAbstractionBase _ _ _ count => NativeSequenceBindings.introduction count

private theorem subtype_list_injective :
    Function.Injective (List.map (Subtype.val : DeclaredSort language → TypeExpr)) := by
  exact List.map_injective_iff.mpr Subtype.val_injective

private theorem singleton_preimage {source : TypeExpr} {bound : List (DeclaredSort language)}
    (read : [source] = bound.map Subtype.val) :
    ∃ selected, bound = [selected] ∧ selected.val = source := by
  have length : bound.length = 1 := by
    have counts := congrArg List.length read
    simpa only [List.length_cons, List.length_nil, List.length_map] using counts.symm
  obtain ⟨selected, rfl⟩ := List.length_eq_one_iff.mp length
  exact ⟨selected, rfl, (List.cons.inj read).1.symm⟩

private theorem empty_preimage {bound : List (DeclaredSort language)}
    (read : [] = bound.map Subtype.val) : bound = [] := by
  have counts := congrArg List.length read
  exact List.length_eq_zero_iff.mp (by simpa only [List.length_nil, List.length_map] using counts.symm)

/-- Each source binder profile earns a typed native adaptation from its full
finite binding telescope to its exact original parameter type. -/
theorem program_typed
    {parameter : TermParam} {sourceBound : List TypeExpr} {sourceResult : TypeExpr}
    (scope : ParameterScope parameter sourceBound sourceResult)
    (bound : List (DeclaredSort language)) (result selected : DeclaredSort language)
    (boundRead : sourceBound = bound.map Subtype.val)
    (resultRead : sourceResult = result.val)
    (parameterRead : parameter? language parameter = some selected) :
    Core.Typing language .nil (program scope)
      (closedArrow
        (ClosedOperators.bindingType (S := sourceSignature language)
          (nativeType (language := language)) bound result)
        (nativeType selected)) := by
  have original := parameter_source parameterRead
  cases scope with
  | simple name type =>
      obtain rfl := empty_preimage boundRead
      have selectedSame : selected = result := by
        apply Subtype.ext
        exact (Option.some.inj original).symm.trans resultRead
      cases selectedSame
      exact ClosedOperators.Derived.identity_typing (Core.formation language)
        (Core.type_formed (nativeType_read result))
  | abstraction binder name domain codomain =>
      obtain ⟨domainSort, rfl, domainRead⟩ := singleton_preimage boundRead
      have selectedSame : selected = DeclaredSort.arrow domainSort result := by
        apply Subtype.ext
        exact (Option.some.inj original).symm.trans
          (congrArg₂ TypeExpr.arrow domainRead.symm resultRead)
      cases selectedSame
      exact StructuralPrograms.lambda_typed domainSort result
  | abstractionBase binder name sort =>
      obtain ⟨domainSort, rfl, domainRead⟩ := singleton_preimage boundRead
      have selectedSame : selected = DeclaredSort.arrow domainSort result := by
        apply Subtype.ext
        exact (Option.some.inj original).symm.trans
          (congrArg₂ TypeExpr.arrow domainRead.symm resultRead)
      cases selectedSame
      exact StructuralPrograms.lambda_typed domainSort result
  | multiAbstraction binders name domain codomain count =>
      have shape : selected.val = .arrow (.multiBinder domain) result.val :=
        (Option.some.inj original).symm.trans (congrArg (TypeExpr.arrow (.multiBinder domain)) resultRead)
      have typed : DeclaredType language (.arrow (.multiBinder domain) result.val) :=
        shape ▸ selected.property
      have domainTyped : DeclaredType language domain := by
        cases typed with
        | arrow first _ => cases first with | multiBinder formed => exact formed
      let domainSort : DeclaredSort language := ⟨domain, domainTyped⟩
      have bounds : bound = List.replicate count domainSort := by
        apply subtype_list_injective
        exact boundRead.symm.trans (by simp only [List.map_replicate]; rfl)
      have selectedSame : selected = DeclaredSort.arrow (DeclaredSort.multiBinder domainSort) result := by
        apply Subtype.ext
        exact (Option.some.inj original).symm.trans (congrArg (TypeExpr.arrow (.multiBinder domain)) resultRead)
      cases selectedSame
      cases bounds
      exact StructuralPrograms.multiLambda_typed domainSort result count
  | multiAbstractionBase binders name sort count =>
      have typed : DeclaredType language (.arrow (.multiBinder (.base sort)) (.base sort)) :=
        (Option.some.inj original).symm ▸ selected.property
      have domainTyped : DeclaredType language (.base sort) := by
        cases typed with
        | arrow first _ => cases first with | multiBinder formed => exact formed
      let domainSort : DeclaredSort language := ⟨.base sort, domainTyped⟩
      have bounds : bound = List.replicate count domainSort := by
        apply subtype_list_injective
        exact boundRead.symm.trans (by simp only [List.map_replicate]; rfl)
      have selectedSame : selected = DeclaredSort.arrow (DeclaredSort.multiBinder domainSort) result := by
        apply Subtype.ext
        exact (Option.some.inj original).symm.trans
          (congrArg (TypeExpr.arrow (.multiBinder (.base sort))) resultRead)
      cases selectedSame
      cases bounds
      exact StructuralPrograms.multiLambda_typed domainSort result count

/-- Preserve the complete original parameter order and each binder count. -/
def programs : {parameters : List TermParam} → {arity : List (List TypeExpr × TypeExpr)} →
    ParameterScopes parameters arity → List (Tower.Tm 0)
  | _, _, .nil => []
  | _, _, .cons first rest => program first :: programs rest

theorem programs_count {parameters : List TermParam} {arity : List (List TypeExpr × TypeExpr)}
    (scopes : ParameterScopes parameters arity) : (programs scopes).length = arity.length := by
  induction scopes with
  | nil => rfl
  | cons first rest ih => exact congrArg Nat.succ ih

/-- The actual parameter adapter vector is typed position by position against
both the retained source binding arity and the decoded original header. -/
theorem programs_typed
    {parameters : List TermParam} {sourceArity : List (List TypeExpr × TypeExpr)}
    (scopes : ParameterScopes parameters sourceArity)
    (selected : List (DeclaredSort language))
    (decoded : List.Forall₂ (fun parameter sort => parameter? language parameter = some sort)
      parameters selected)
    (arity : List (List (DeclaredSort language) × DeclaredSort language))
    (read : sourceArity = Binding.mapArities Subtype.val arity) :
    List.Forall₂ (fun slot pair => Core.Typing language .nil pair.2
      (closedArrow (ClosedOperators.bindingType (S := sourceSignature language)
        (nativeType (language := language)) slot.1 slot.2) (nativeType pair.1)))
      arity (selected.zip (programs scopes)) := by
  induction scopes generalizing selected arity with
  | nil =>
      cases decoded
      cases arity with
      | nil => exact .nil
      | cons first rest => cases read
  | @cons parameter parameters sourceBound sourceResult sourceRest first later ih =>
      cases decoded with
      | @cons _ sort _ selected readFirst readLater =>
          cases arity with
          | nil => cases read
          | cons slot arity =>
              rcases slot with ⟨bound, result⟩
              have aligned := List.cons.inj read
              exact .cons
                (program_typed first bound result sort
                  (congrArg Prod.fst aligned.1) (congrArg Prod.snd aligned.1) readFirst)
                (ih selected readLater arity aligned.2)

end ParameterPrograms

end FullHeaders

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions.FullHeaders

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration BindingSignatureEmbedding
open Mettapedia.OSLF
open Mettapedia.GSLT.LanguageDef.BindingSyntax

variable {language : LanguageDef}

namespace ConstructorPrograms

/-- Transport only a proved context length; all domains still come from the
original admitted source types and the common native context constructor. -/
private def alignedContext (sorts : List (DeclaredSort language)) (count : Nat)
    (length : sorts.length = count) : Tower.Ctx count :=
  length ▸ ClosedOperators.typeContext (S := sourceSignature language)
    (nativeType (language := language)) sorts

private theorem alignedContext_lookup (sorts : List (DeclaredSort language))
    (count : Nat) (length : sorts.length = count) (position : Fin count) :
    Ctx.lookup (alignedContext sorts count length) position =
      liftClosed (nativeType (sorts[position.val]'(by rw [length]; exact position.isLt))) := by
  cases length
  have actual := ClosedOperators.Formation.typeContext_lookup
    (S := sourceSignature language) (nativeType (language := language))
    (Binding.varOfIdx sorts position)
  rw [Binding.varIdx_varOfIdx (S := sourceSignature language) sorts position] at actual
  have selected : sorts.get position = sorts[position.val]'position.isLt := rfl
  exact actual.trans (congrArg (fun sort : DeclaredSort language =>
    (liftClosed (nativeType sort) : Tower.Tm sorts.length)) selected)

/-- Both telescopes and the adapter vector share the same literal physical
positions. The tuple is compiled parameter metadata, not a source syntax. -/
def inputs (maps : List ((DeclaredSort language × DeclaredSort language) × Tower.Tm 0)) :
    Tower.Ctx maps.length :=
  alignedContext (maps.reverse.map (fun map => map.1.1)) maps.length (by simp)

def outputs (maps : List ((DeclaredSort language × DeclaredSort language) × Tower.Tm 0)) :
    Tower.Ctx maps.length :=
  alignedContext (maps.reverse.map (fun map => map.1.2)) maps.length (by simp)

def domainAt (maps : List ((DeclaredSort language × DeclaredSort language) × Tower.Tm 0))
    (position : Fin maps.length) : Tower.Tm 0 :=
  nativeType (maps.reverse[position.val]'(by rw [List.length_reverse]; exact position.isLt)).1.1

def codomainAt (maps : List ((DeclaredSort language × DeclaredSort language) × Tower.Tm 0))
    (position : Fin maps.length) : Tower.Tm 0 :=
  nativeType (maps.reverse[position.val]'(by rw [List.length_reverse]; exact position.isLt)).1.2

def programAt (maps : List ((DeclaredSort language × DeclaredSort language) × Tower.Tm 0))
    (position : Fin maps.length) : Tower.Tm 0 :=
  (maps.reverse[position.val]'(by rw [List.length_reverse]; exact position.isLt)).2

theorem inputs_lookup (maps : List ((DeclaredSort language × DeclaredSort language) × Tower.Tm 0))
    (position : Fin maps.length) :
    Ctx.lookup (inputs maps) position = liftClosed (domainAt maps position) := by
  simpa only [inputs, domainAt, List.getElem_map] using
    alignedContext_lookup (maps.reverse.map (fun map => map.1.1)) maps.length (by simp) position

theorem outputs_lookup (maps : List ((DeclaredSort language × DeclaredSort language) × Tower.Tm 0))
    (position : Fin maps.length) :
    Ctx.lookup (outputs maps) position = liftClosed (codomainAt maps position) := by
  simpa only [outputs, codomainAt, List.getElem_map] using
    alignedContext_lookup (maps.reverse.map (fun map => map.1.2)) maps.length (by simp) position

/-- Adapter metadata is earned from the original scoped source declarations. -/
def maps {parameters : List TermParam} {sourceArity : List (List TypeExpr × TypeExpr)}
    (scopes : ParameterScopes parameters sourceArity)
    (selected : List (DeclaredSort language))
    (arity : List (List (DeclaredSort language) × DeclaredSort language)) :
    List ((DeclaredSort language × DeclaredSort language) × Tower.Tm 0) :=
  (arity.zip (selected.zip (ParameterPrograms.programs scopes))).map
    (fun pair => ((bindingSort pair.1.1 pair.1.2, pair.2.1), pair.2.2))

theorem maps_typed
    {parameters : List TermParam} {sourceArity : List (List TypeExpr × TypeExpr)}
    (scopes : ParameterScopes parameters sourceArity)
    (selected : List (DeclaredSort language))
    (decoded : List.Forall₂ (fun parameter sort => parameter? language parameter = some sort)
      parameters selected)
    (arity : List (List (DeclaredSort language) × DeclaredSort language))
    (read : sourceArity = Binding.mapArities Subtype.val arity) :
    ∀ map ∈ maps scopes selected arity,
      Core.Typing language .nil map.2
        (closedArrow (nativeType map.1.1) (nativeType map.1.2)) := by
  intro map member
  unfold maps at member
  obtain ⟨pair, pairMember, mapEqual⟩ := List.mem_map.mp member
  subst map
  have typed := List.forall₂_zip
    (ParameterPrograms.programs_typed scopes selected decoded arity read) pairMember
  exact (congrArg (fun domain => closedArrow domain (nativeType pair.2.1))
    (bindingSort_native pair.1.1 pair.1.2)).symm ▸ typed

private theorem selected_programs_length
    {parameters : List TermParam} {sourceArity : List (List TypeExpr × TypeExpr)}
    (scopes : ParameterScopes parameters sourceArity)
    (selected : List (DeclaredSort language))
    (decoded : List.Forall₂ (fun parameter sort => parameter? language parameter = some sort)
      parameters selected) : selected.length = (ParameterPrograms.programs scopes).length := by
  induction scopes generalizing selected with
  | nil => cases decoded; rfl
  | cons first later ih =>
      cases decoded with
      | cons readFirst readLater => exact congrArg Nat.succ (ih _ readLater)

/-- Every physical source argument survives the finite metadata assembly. -/
theorem maps_inputs
    {parameters : List TermParam} {sourceArity : List (List TypeExpr × TypeExpr)}
    (scopes : ParameterScopes parameters sourceArity)
    (selected : List (DeclaredSort language))
    (decoded : List.Forall₂ (fun parameter sort => parameter? language parameter = some sort)
      parameters selected)
    (arity : List (List (DeclaredSort language) × DeclaredSort language))
    (read : sourceArity = Binding.mapArities Subtype.val arity) :
    (maps scopes selected arity).map (fun map => map.1.1) =
      arity.map (fun slot => bindingSort slot.1 slot.2) := by
  have related := ParameterPrograms.programs_typed scopes selected decoded arity read
  have inventory := List.map_fst_zip (l₁ := arity)
    (l₂ := selected.zip (ParameterPrograms.programs scopes)) (Nat.le_of_eq related.length_eq)
  have actual := congrArg (List.map (fun slot => bindingSort slot.1 slot.2)) inventory
  simpa only [maps, List.map_map, Function.comp_def] using actual

/-- Output parameters remain the literal decoded constructor header vector. -/
theorem maps_outputs
    {parameters : List TermParam} {sourceArity : List (List TypeExpr × TypeExpr)}
    (scopes : ParameterScopes parameters sourceArity)
    (selected : List (DeclaredSort language))
    (decoded : List.Forall₂ (fun parameter sort => parameter? language parameter = some sort)
      parameters selected)
    (arity : List (List (DeclaredSort language) × DeclaredSort language))
    (read : sourceArity = Binding.mapArities Subtype.val arity) :
    (maps scopes selected arity).map (fun map => map.1.2) = selected := by
  have related := ParameterPrograms.programs_typed scopes selected decoded arity read
  have inventory := List.map_snd_zip (l₁ := arity)
    (l₂ := selected.zip (ParameterPrograms.programs scopes)) (Nat.le_of_eq related.length_eq.symm)
  have actual := congrArg (List.map Prod.fst) inventory
  have first : (maps scopes selected arity).map (fun map => map.1.2) =
      (selected.zip (ParameterPrograms.programs scopes)).map Prod.fst := by
    simpa only [maps, List.map_map, Function.comp_def] using actual
  exact first.trans (List.map_fst_zip
    (Nat.le_of_eq (selected_programs_length scopes selected decoded)))

theorem maps_programs
    {parameters : List TermParam} {sourceArity : List (List TypeExpr × TypeExpr)}
    (scopes : ParameterScopes parameters sourceArity)
    (selected : List (DeclaredSort language))
    (decoded : List.Forall₂ (fun parameter sort => parameter? language parameter = some sort)
      parameters selected)
    (arity : List (List (DeclaredSort language) × DeclaredSort language))
    (read : sourceArity = Binding.mapArities Subtype.val arity) :
    (maps scopes selected arity).map Prod.snd = ParameterPrograms.programs scopes := by
  have related := ParameterPrograms.programs_typed scopes selected decoded arity read
  have inventory := List.map_snd_zip (l₁ := arity)
    (l₂ := selected.zip (ParameterPrograms.programs scopes)) (Nat.le_of_eq related.length_eq.symm)
  have actual := congrArg (List.map Prod.snd) inventory
  have first : (maps scopes selected arity).map Prod.snd =
      (selected.zip (ParameterPrograms.programs scopes)).map Prod.snd := by
    simpa only [maps, List.map_map, Function.comp_def] using actual
  exact first.trans (List.map_snd_zip
    (Nat.le_of_eq (selected_programs_length scopes selected decoded).symm))

/-- The full header installation inherits formation from the already formed
Core declaration package through its proved literal signature extension. -/
def formation (installed : Installation language) :
    ClosedOperators.Formation (S := sourceSignature language)
      (nativeType (language := language)) installed.rules where
  typeUniverse := (Core.formation language).typeUniverse
  joined := (Core.formation language).joined
  universeIs := (Core.formation language).universeIs
  joinSelf := (Core.formation language).joinSelf
  collapseSelf := (Core.formation language).collapseSelf
  typeFormed := fun sort => ((Core.formation language).typeFormed sort).monoSignature installed.extension

private theorem alignedContext_formed (installed : Installation language)
    (sorts : List (DeclaredSort language)) (count : Nat) (length : sorts.length = count) :
    FormationSensitive.ContextFormation installed.rules (alignedContext sorts count length) := by
  cases length
  exact (formation installed).typeContext_formed sorts

/-- The actual declared constructor is composed with its source-prescribed
closed parameter adapters, using the shared telescope operations. -/
def program (origin : Fin language.terms.length)
    (vector : List ((DeclaredSort language × DeclaredSort language) × Tower.Tm 0)) : Tower.Tm 0 :=
  FormationCheckedTelescopePrograms.adaptClosed (inputs vector) (outputs vector) (programAt vector)
    (.const (AuthoredBindingDeclarations.constructorDeclName language origin))

/-- Primitive adapter typings and literal header alignment construct the
formed operator; no whole source-term adequacy is supplied as a premise. -/
private theorem program_typed (installed : Installation language) (origin : Fin language.terms.length)
    (vector : List ((DeclaredSort language × DeclaredSort language) × Tower.Tm 0))
    (primitive : ∀ map ∈ vector, Core.Typing language .nil map.2
      (closedArrow (nativeType map.1.1) (nativeType map.1.2)))
    (result : DeclaredSort language)
    (headerRead : installed.header origin = TelescopeAbstraction.closeType (outputs vector)
      (liftClosed (nativeType result))) :
    installed.Typing .nil (program origin vector)
      (TelescopeAbstraction.closeType (inputs vector) (liftClosed (nativeType result))) := by
  have typed : installed.Typing .nil
      (.const (AuthoredBindingDeclarations.constructorDeclName language origin))
      (TelescopeAbstraction.closeType (outputs vector) (liftClosed (nativeType result))) :=
    headerRead ▸ installed.constructor_typed origin
  apply FormationCheckedTelescopePrograms.adaptClosed_typing
    (FormationSensitive.towerUniverseRegularity.includeSignature installed.signature)
    FormationCheckedTelescopePrograms.tower_joins (inputs vector) (outputs vector)
    (alignedContext_formed installed _ _ _) (domainAt vector) (codomainAt vector) (programAt vector)
    (inputs_lookup vector) (outputs_lookup vector) _ typed
  intro position
  have member : vector.reverse[position.val]'(by rw [List.length_reverse]; exact position.isLt) ∈ vector :=
    List.mem_reverse.mp (List.getElem_mem _)
  exact (primitive _ member).monoSignature installed.extension

/-- Original membership chooses the same finite row used by installation. -/
def sourceMaps (installed : Installation language) (rule : GrammarRule) (member : rule ∈ language.terms)
    {sourceArity : List (List TypeExpr × TypeExpr)} (scopes : ParameterScopes rule.params sourceArity)
    (arity : List (List (DeclaredSort language) × DeclaredSort language)) :=
  maps scopes (installed.parameters (AuthoredBindingDeclarations.Functional.constructorIndex rule member)) arity

theorem sourceMaps_typed (installed : Installation language) (rule : GrammarRule)
    (member : rule ∈ language.terms) {sourceArity : List (List TypeExpr × TypeExpr)}
    (scopes : ParameterScopes rule.params sourceArity)
    (arity : List (List (DeclaredSort language) × DeclaredSort language))
    (read : sourceArity = Binding.mapArities Subtype.val arity) :
    ∀ map ∈ sourceMaps installed rule member scopes arity,
      Core.Typing language .nil map.2
        (closedArrow (nativeType map.1.1) (nativeType map.1.2)) := by
  apply maps_typed scopes _ _ arity read
  have decoded := NativeSignature.decodeList_sound
    (installed.parameters_read (AuthoredBindingDeclarations.Functional.constructorIndex rule member))
  rw [AuthoredBindingDeclarations.Functional.constructorIndex_read] at decoded
  exact decoded

private theorem alignedContext_closeType (sorts : List (DeclaredSort language))
    (count : Nat) (length : sorts.length = count) (result : Tower.Tm 0) :
    TelescopeAbstraction.closeType (alignedContext sorts count length) (liftClosed result) =
      ClosedOperators.spineType (S := sourceSignature language)
        (nativeType (language := language)) sorts result := by
  cases length
  exact ClosedOperators.closeType_spine (S := sourceSignature language) (nativeType (language := language)) sorts result

private theorem spine_append (first second : List (DeclaredSort language)) (result : Tower.Tm 0) :
    ClosedOperators.spineType (S := sourceSignature language) nativeType (first ++ second) result =
      ClosedOperators.spineType (S := sourceSignature language) nativeType second
        (ClosedOperators.spineType (S := sourceSignature language) nativeType first result) := by
  induction first generalizing result with
  | nil => rfl
  | cons first rest ih => exact ih (closedArrow (nativeType first) result)

private theorem spine_reverse (sorts : List (DeclaredSort language)) (result : Tower.Tm 0) :
    ClosedOperators.spineType (S := sourceSignature language) nativeType sorts.reverse result =
      ClosedOperators.argumentsType (S := sourceSignature language) nativeType
        (sorts.map (fun sort => ([], sort))) result := by
  induction sorts with
  | nil => rfl
  | cons first rest ih =>
      rw [List.reverse_cons, spine_append]
      exact congrArg (closedArrow (nativeType first)) ih

private theorem closure_outputs
    (vector : List ((DeclaredSort language × DeclaredSort language) × Tower.Tm 0)) (result : Tower.Tm 0) :
    TelescopeAbstraction.closeType (outputs vector) (liftClosed result) =
      ClosedOperators.argumentsType (S := sourceSignature language) nativeType
        ((vector.map (fun map => map.1.2)).map (fun sort => ([], sort))) result := by
  rw [outputs, alignedContext_closeType, List.map_reverse]
  exact spine_reverse _ result

private theorem binding_arguments (arity : List (List (DeclaredSort language) × DeclaredSort language))
    (result : Tower.Tm 0) :
    ClosedOperators.argumentsType (S := sourceSignature language) nativeType
      ((arity.map (fun slot => bindingSort slot.1 slot.2)).map (fun sort => ([], sort))) result =
      ClosedOperators.argumentsType (S := sourceSignature language) nativeType arity result := by
  induction arity with
  | nil => rfl
  | cons first rest ih =>
      exact congrArg₂ closedArrow (bindingSort_native first.1 first.2) ih

private theorem closure_inputs
    {parameters : List TermParam} {sourceArity : List (List TypeExpr × TypeExpr)}
    (scopes : ParameterScopes parameters sourceArity)
    (selected : List (DeclaredSort language))
    (decoded : List.Forall₂ (fun parameter sort => parameter? language parameter = some sort)
      parameters selected)
    (arity : List (List (DeclaredSort language) × DeclaredSort language))
    (read : sourceArity = Binding.mapArities Subtype.val arity) (result : Tower.Tm 0) :
    TelescopeAbstraction.closeType (inputs (maps scopes selected arity)) (liftClosed result) =
      ClosedOperators.argumentsType (S := sourceSignature language) nativeType arity result := by
  rw [inputs, alignedContext_closeType, List.map_reverse, maps_inputs scopes selected decoded arity read]
  exact (spine_reverse _ result).trans (binding_arguments arity result)

/-- Full ordinary source constructors obtain actual native operator programs;
the program uses only the original selected row, scopes and admitted types. -/
def sourceProgram (installed : Installation language) (rule : GrammarRule) (member : rule ∈ language.terms)
    {sourceArity : List (List TypeExpr × TypeExpr)} (scopes : ParameterScopes rule.params sourceArity)
    (arity : List (List (DeclaredSort language) × DeclaredSort language)) : Tower.Tm 0 :=
  program (AuthoredBindingDeclarations.Functional.constructorIndex rule member)
    (sourceMaps installed rule member scopes arity)

/-- The full constructor program earns the original source binding-operator
interface, including declared function, collection and multiple-binder inputs. -/
theorem sourceProgram_typed (installed : Installation language) (rule : GrammarRule)
    (member : rule ∈ language.terms) {sourceArity : List (List TypeExpr × TypeExpr)}
    (scopes : ParameterScopes rule.params sourceArity)
    (arity : List (List (DeclaredSort language) × DeclaredSort language))
    (read : sourceArity = Binding.mapArities Subtype.val arity)
    (result : DeclaredSort language) (resultRead : result.val = .base rule.category) :
    installed.Typing .nil (sourceProgram installed rule member scopes arity)
      (ClosedOperators.argumentsType (S := sourceSignature language) nativeType arity (nativeType result)) := by
  let origin := AuthoredBindingDeclarations.Functional.constructorIndex rule member
  let vector := sourceMaps installed rule member scopes arity
  have decoded := NativeSignature.decodeList_sound (installed.parameters_read origin)
  rw [AuthoredBindingDeclarations.Functional.constructorIndex_read] at decoded
  have resultSame : installed.result origin = result := by
    apply Subtype.ext
    have original := sort?_source (installed.result_read origin)
    have row := AuthoredBindingDeclarations.Functional.constructorIndex_read rule member
    exact original.trans ((congrArg (fun selected => TypeExpr.base selected.category) row).trans resultRead.symm)
  have outputSame := maps_outputs scopes (installed.parameters origin) decoded arity read
  have headerRead : installed.header origin =
      TelescopeAbstraction.closeType (outputs vector) (liftClosed (nativeType result)) := by
    have nativeHeader := installed.header_parameters origin
    have outputClosure := closure_outputs vector (nativeType result)
    have resultTypeSame := congrArg
      (ClosedOperators.argumentsType (S := sourceSignature language) nativeType
        ((installed.parameters origin).map (fun sort => ([], sort))))
      (congrArg (nativeType (language := language)) resultSame)
    have interfaceSame := congrArg (fun parameters =>
      ClosedOperators.argumentsType (S := sourceSignature language) nativeType
        (parameters.map (fun sort => ([], sort))) (nativeType result)) outputSame
    exact nativeHeader.trans (resultTypeSame.trans (interfaceSame.symm.trans outputClosure.symm))
  have typed := program_typed installed origin vector
    (sourceMaps_typed installed rule member scopes arity read) result headerRead
  have sourceClosure := closure_inputs scopes (installed.parameters origin) decoded arity read (nativeType result)
  exact sourceClosure ▸ typed

end ConstructorPrograms
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions.FullHeaders


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions
namespace NativeCollections

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Presentation.Declaration BindingSignatureEmbedding
open NativeIndexedFamilies IntrinsicMaps
open NativeNaturalVectorFamilies (natTm)

variable {n m : Nat}

/-- The discriminator is ordinary native data, retained in the checked term. -/
def tag {n : Nat} : CollType → Tower.Tm n
  | .vec => NativeSequenceBindings.numeral 0
  | .hashBag => NativeSequenceBindings.numeral 1
  | .hashSet => NativeSequenceBindings.numeral 2

def kind? {n : Nat} (term : Tower.Tm n) : Option CollType :=
  if term = tag .vec then some .vec
  else if term = tag .hashBag then some .hashBag
  else if term = tag .hashSet then some .hashSet else none

@[simp] theorem kind?_tag {n : Nat} (kind : CollType) :
    kind? (tag (n := n) kind) = some kind := by
  cases kind <;> simp [kind?, tag, NativeSequenceBindings.numeral,
    NativeNaturalVectorFamilies.zeroTm, NativeNaturalVectorFamilies.succApp]

theorem kind?_sound {term : Tower.Tm n} {kind : CollType}
    (read : kind? term = some kind) : term = tag kind := by
  unfold kind? at read
  split at read
  · cases read; assumption
  · split at read
    · cases read; assumption
    · split at read
      · cases read; assumption
      · cases read

def pack (kind : CollType) (element : Tower.Tm n) (values : List (Tower.Tm n)) : Tower.Tm n :=
  .pair (tag kind) (IntrinsicNativeListMapComputation.encode element values)

/-- Independent native formation of the three physical collection shapes.
The kind occurs in the actual constructor term, not just a request annotation. -/
inductive Classifies (element : Tower.Tm n) : CollType → Tower.Tm n → Prop where
  | vector (values : List (Tower.Tm n)) : Classifies element .vec (pack .vec element values)
  | bag (values : List (Tower.Tm n)) : Classifies element .hashBag (pack .hashBag element values)
  | finiteSet (values : List (Tower.Tm n)) : Classifies element .hashSet (pack .hashSet element values)

def read (element : Tower.Tm n) : Tower.Tm n → Option (CollType × List (Tower.Tm n))
  | .pair first second => do
      let kind ← kind? first
      let values ← IntrinsicNativeListMapComputation.decode element second
      pure (kind, values)
  | _ => none

@[simp] theorem read_pack (kind : CollType) (element : Tower.Tm n)
    (values : List (Tower.Tm n)) : read element (pack kind element values) = some (kind, values) := by
  simp [read, pack]

theorem read_sound {element term : Tower.Tm n} {kind : CollType} {values : List (Tower.Tm n)}
    (accepted : read element term = some (kind, values)) : term = pack kind element values := by
  cases term <;> try { simp only [read] at accepted; cases accepted }
  rename_i first second
  simp only [read] at accepted
  cases firstRead : kind? first with
  | none => simp [firstRead] at accepted
  | some actualKind =>
      cases secondRead : IntrinsicNativeListMapComputation.decode element second with
      | none => simp [firstRead, secondRead] at accepted
      | some actualValues =>
          simp [firstRead, secondRead] at accepted
          rcases accepted with ⟨rfl, rfl⟩
          exact congrArg₂ Tm.pair (kind?_sound firstRead)
            (IntrinsicNativeListMapComputation.decode_sound element second _ secondRead)

theorem classifies_pack (kind : CollType) (element : Tower.Tm n) (values : List (Tower.Tm n)) :
    Classifies element kind (pack kind element values) := by
  cases kind
  · exact .vector values
  · exact .bag values
  · exact .finiteSet values

theorem read_classifies {element term : Tower.Tm n} {kind : CollType} {values : List (Tower.Tm n)}
    (accepted : read element term = some (kind, values)) : Classifies element kind term :=
  (read_sound accepted).symm ▸ classifies_pack kind element values

theorem classifies_read {element term : Tower.Tm n} {kind : CollType}
    (formed : Classifies element kind term) : ∃ values, read element term = some (kind, values) := by
  cases formed <;> exact ⟨_, read_pack _ _ _⟩

/-- The checker binds its selected kind to the discriminator it actually reads. -/
def check (kind : CollType) (element term : Tower.Tm n) : Bool :=
  match read element term with
  | some (actual, _) => decide (actual = kind)
  | none => false

theorem check_exact (kind : CollType) (element term : Tower.Tm n) :
    check kind element term = true ↔ Classifies element kind term := by
  constructor
  · intro accepted
    cases decoded : read element term with
    | none => simp [check, decoded] at accepted
    | some result =>
        rcases result with ⟨actual, values⟩
        have same : actual = kind := by simpa [check, decoded] using accepted
        exact same ▸ read_classifies decoded
  · intro formed
    obtain ⟨values, decoded⟩ := classifies_read formed
    simp [check, decoded]

@[simp] theorem check_pack (requested actual : CollType) (element : Tower.Tm n)
    (values : List (Tower.Tm n)) :
    check requested element (pack actual element values) = decide (actual = requested) := by
  simp [check]

theorem wrong_kind_refused {requested actual : CollType} (different : actual ≠ requested)
    (element : Tower.Tm n) (values : List (Tower.Tm n)) :
    check requested element (pack actual element values) = false := by
  simp [different]

/-- Native equality is stated by actual native shapes and their independent
vector, bag and finite-set rules. It is not ambient kernel conversion. -/
inductive Equivalent (element : Tower.Tm n) : Tower.Tm n → Tower.Tm n → Prop where
  | vector (values : List (Tower.Tm n)) :
      Equivalent element (pack .vec element values) (pack .vec element values)
  | bag (left right : List (Tower.Tm n)) (same : left.Perm right) :
      Equivalent element (pack .hashBag element left) (pack .hashBag element right)
  | finiteSet (left right : List (Tower.Tm n)) (same : ∀ value, value ∈ left ↔ value ∈ right) :
      Equivalent element (pack .hashSet element left) (pack .hashSet element right)

theorem equivalent_pack (kind : CollType) (element : Tower.Tm n)
    {left right : List (Tower.Tm n)} (same : CollectionObservation.Related kind left right) :
    Equivalent element (pack kind element left) (pack kind element right) := by
  cases kind with
  | vec => cases same; exact .vector left
  | hashBag => exact .bag left right same
  | hashSet => exact .finiteSet left right same

def checkEquivalent (element left right : Tower.Tm n) : Bool :=
  match read element left, read element right with
  | some (leftKind, leftValues), some (rightKind, rightValues) =>
      decide (leftKind = rightKind) && CollectionObservation.checkLists leftKind leftValues rightValues
  | _, _ => false

theorem checkEquivalent_exact (element left right : Tower.Tm n) :
    checkEquivalent element left right = true ↔ Equivalent element left right := by
  constructor
  · intro accepted
    cases readLeft : read element left with
    | none => simp [checkEquivalent, readLeft] at accepted
    | some first =>
        rcases first with ⟨leftKind, leftValues⟩
        cases readRight : read element right with
        | none => simp [checkEquivalent, readLeft, readRight] at accepted
        | some second =>
            rcases second with ⟨rightKind, rightValues⟩
            have checked : leftKind = rightKind ∧
                CollectionObservation.Related leftKind leftValues rightValues := by
              simpa only [checkEquivalent, readLeft, readRight, Bool.and_eq_true,
                decide_eq_true_eq, CollectionObservation.checkLists_exact] using accepted
            rcases checked with ⟨rfl, same⟩
            rw [read_sound readLeft, read_sound readRight]
            exact equivalent_pack leftKind element same
  · intro equivalent
    cases equivalent with
    | vector values => simp [checkEquivalent, CollectionObservation.checkLists]
    | bag left right same =>
        simp [checkEquivalent, CollectionObservation.checkLists, same]
    | finiteSet left right same =>
        simp only [checkEquivalent, read_pack, decide_true, Bool.true_and,
          CollectionObservation.checkLists_exact]
        exact same

theorem equivalent_reflects (kind : CollType) (element : Tower.Tm n)
    (left right : List (Tower.Tm n)) :
    Equivalent element (pack kind element left) (pack kind element right) ↔
      CollectionObservation.Related kind left right := by
  rw [← checkEquivalent_exact]
  simp only [checkEquivalent, read_pack, decide_true, Bool.true_and,
    CollectionObservation.checkLists_exact]

theorem cross_kind_equation_refused {first second : CollType} (different : first ≠ second)
    (element : Tower.Tm n) (left right : List (Tower.Tm n)) :
    checkEquivalent element (pack first element left) (pack second element right) = false := by
  simp [checkEquivalent, different]

@[simp] theorem pack_rename (action : Ren n m) (kind : CollType) (element : Tower.Tm n)
    (values : List (Tower.Tm n)) :
    Presentation.rename action (pack kind element values) =
      pack kind (Presentation.rename action element) (values.map (Presentation.rename action)) := by
  cases kind <;> simp [pack, tag, IntrinsicNativeListMapComputation.encode_rename,
    Presentation.rename]

@[simp] theorem pack_substitute (action : Sub Tower.Head n m) (kind : CollType)
    (element : Tower.Tm n) (values : List (Tower.Tm n)) :
    Presentation.subst action (pack kind element values) =
      pack kind (Presentation.subst action element) (values.map (Presentation.subst action)) := by
  cases kind <;> simp [pack, tag, IntrinsicNativeListMapComputation.encode_subst,
    Presentation.subst]

theorem classifies_substitute {element term : Tower.Tm n} {kind : CollType}
    (formed : Classifies element kind term) (action : Sub Tower.Head n m) :
    Classifies (Presentation.subst action element) kind (Presentation.subst action term) := by
  cases formed <;> rw [pack_substitute] <;> exact classifies_pack _ _ _

theorem equivalent_substitute {element left right : Tower.Tm n}
    (equivalent : Equivalent element left right) (action : Sub Tower.Head n m) :
    Equivalent (Presentation.subst action element)
      (Presentation.subst action left) (Presentation.subst action right) := by
  cases equivalent with
  | vector values => rw [pack_substitute]; exact .vector _
  | bag left right same =>
      rw [pack_substitute, pack_substitute]
      exact .bag _ _ (same.map _)
  | finiteSet left right same =>
      rw [pack_substitute, pack_substitute]
      exact .finiteSet _ _ (CollectionObservation.Related.map (kind := .hashSet) same _)

/-- All kind refinements share this native representation type. The checked
Classifies judgment, rather than equality of this type, retains their kind. -/
def packetType (element : Tower.Tm n) : Tower.Tm n :=
  .sigma natTm (Presentation.rename wk (Intrinsic.listApp element))

@[simp] theorem packetType_rename (action : Ren n m) (element : Tower.Tm n) :
    Presentation.rename action (packetType element) = packetType (Presentation.rename action element) := by
  simp only [packetType, Presentation.rename, natTm, Intrinsic.listApp, rename_comp]
  rfl

theorem packetType_formed (language : LanguageDef) {context : Tower.Ctx n} {element : Tower.Tm n}
    (formed : Core.Typing language context element (sortTm Tower.zero)) :
    Core.Typing language context (packetType element) (sortTm Tower.zero) := by
  have second := (Core.listApp_typed language formed).weaken (extension := natTm)
  exact .cumul (.sigmaForm (NativeSequenceBindings.natural_formed (Core.naturals language))
    (.sort Tower.zero) second (.sort Tower.zero) (.sorts Tower.zero Tower.zero)) (by
      intro valuation
      simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval, Tower.zero, LevelTower.zero])

theorem pack_typed (language : LanguageDef) {context : Tower.Ctx n} {element : Tower.Tm n}
    (formed : Core.Typing language context element (sortTm Tower.zero)) (kind : CollType)
    (values : List (Tower.Tm n))
    (typed : ∀ value ∈ values, Core.Typing language context value element) :
    Core.Typing language context (pack kind element values) (packetType element) := by
  have tagTyped : Core.Typing language context (tag kind) natTm := by
    cases kind <;> exact NativeSequenceBindings.numeral_typed (Core.naturals language) _
  exact .pairIntro (packetType_formed language formed) (.sort Tower.zero) tagTyped
    (by simpa only [inst0_rename_wk] using Core.encode_typed language formed values typed)

/-- Representation erasure is an actual native projection with a checked
structural computation, not a host-side replacement of the payload. -/
def erase (term : Tower.Tm n) : Tower.Tm n := .snd term

def eraseCode (kind : CollType) (element : Tower.Tm n) (values : List (Tower.Tm n)) :
    StructuralConversionCode.StepCode Tower.Head (fun _ => Empty) n :=
  .betaSigmaSnd (tag kind) (IntrinsicNativeListMapComputation.encode element values)

@[simp] theorem eraseCode_read (kind : CollType) (element : Tower.Tm n)
    (values : List (Tower.Tm n)) :
    StructuralConversionCode.StepCode.decode Eq (fun code : Empty => nomatch code)
      (eraseCode kind element values) =
        some (erase (pack kind element values), IntrinsicNativeListMapComputation.encode element values) := rfl


/-- The full original type expression is retained as native wire data. The
existing source codec, rather than an alternative type grammar, supplies it. -/
def index (source : TypeExpr) : Tower.Tm n :=
  NativeWireData.encode (Mettapedia.GSLT.LanguageDef.InferenceCettaWire.AuthoredRule.typeTerm source)

theorem index_injective : Function.Injective (index (n := n)) := by
  intro first second same
  have wireSame := NativeWireData.encode_injective same
  have decoded := congrArg Mettapedia.GSLT.LanguageDef.InferenceCettaWire.AuthoredRule.decodeType? wireSame
  simpa only [Mettapedia.GSLT.LanguageDef.InferenceCettaWire.AuthoredRule.decodeType?_typeTerm,
    Option.some.injEq] using decoded

@[simp] theorem index_rename (action : Ren n m) (source : TypeExpr) :
    Presentation.rename action (index source) = index source :=
  NativeWireData.rename_encode action _

@[simp] theorem index_substitute (action : Sub Tower.Head n m) (source : TypeExpr) :
    Presentation.subst action (index source) = index source :=
  NativeWireData.subst_encode action _

def indexed (source : TypeExpr) (payload : Tower.Tm n) : Tower.Tm n := .pair (index source) payload

def sourcePack {language : LanguageDef} (kind : CollType) (element : DeclaredSort language)
    (values : List (Tower.Tm n)) : Tower.Tm n :=
  indexed (.collection kind element.val) (pack kind (liftClosed (nativeType element)) values)

/-- This native refinement carries and checks the entire original type index,
including nested collection kinds, in addition to its actual collection shape. -/
inductive At (language : LanguageDef) : TypeExpr → Tower.Tm n → Prop where
  | collection (kind : CollType) (element : DeclaredSort language) {payload : Tower.Tm n}
      (native : Classifies (liftClosed (nativeType element)) kind payload) :
      At language (.collection kind element.val) (indexed (.collection kind element.val) payload)

def checkAt (language : LanguageDef) : TypeExpr → Tower.Tm n → Bool
  | source@(.collection kind body), .pair header payload =>
      match sort? language body with
      | some element => decide (header = index source) && check kind (liftClosed (nativeType element)) payload
      | none => false
  | _, _ => false

theorem checkAt_exact (language : LanguageDef) (source : TypeExpr) (term : Tower.Tm n) :
    checkAt language source term = true ↔ At language source term := by
  constructor
  · intro accepted
    cases source <;> try { cases accepted }
    rename_i kind source
    cases term <;> try { cases accepted }
    rename_i header payload
    cases decoded : sort? language source with
    | none => simp [checkAt, decoded] at accepted
    | some element =>
        have both : header = index (.collection kind source) ∧
            Classifies (liftClosed (nativeType element)) kind payload := by
          simpa only [checkAt, decoded, Bool.and_eq_true, decide_eq_true_eq, check_exact] using accepted
        rcases both with ⟨rfl, native⟩
        exact sort?_source decoded ▸ At.collection kind element native
  · intro admitted
    cases admitted with
    | collection kind element native =>
        simpa [checkAt, indexed, sort?_readback] using
          (check_exact kind (liftClosed (nativeType element)) _).2 native

/-- Source authority binds the full original type index to both actual
native endpoints. Equality is still the independent native payload relation. -/
inductive EquationAt (language : LanguageDef) : TypeExpr → Tower.Tm n → Tower.Tm n → Prop where
  | collection (kind : CollType) (element : DeclaredSort language) {left right : Tower.Tm n}
      (leftKind : Classifies (liftClosed (nativeType element)) kind left)
      (rightKind : Classifies (liftClosed (nativeType element)) kind right)
      (same : Equivalent (liftClosed (nativeType element)) left right) :
      EquationAt language (.collection kind element.val)
        (indexed (.collection kind element.val) left) (indexed (.collection kind element.val) right)

def checkEquationAt (language : LanguageDef) : TypeExpr → Tower.Tm n → Tower.Tm n → Bool
  | source@(.collection kind body), .pair leftHeader left, .pair rightHeader right =>
      match sort? language body with
      | some element => decide (leftHeader = index source) && decide (rightHeader = index source) &&
          check kind (liftClosed (nativeType element)) left && check kind (liftClosed (nativeType element)) right &&
          checkEquivalent (liftClosed (nativeType element)) left right
      | none => false
  | _, _, _ => false

theorem checkEquationAt_exact (language : LanguageDef) (source : TypeExpr) (left right : Tower.Tm n) :
    checkEquationAt language source left right = true ↔ EquationAt language source left right := by
  constructor
  · intro accepted
    cases source <;> try { cases accepted }
    rename_i kind source
    cases left <;> try { cases accepted }
    rename_i leftHeader left
    cases right <;> try { cases accepted }
    rename_i rightHeader right
    cases decoded : sort? language source with
    | none => simp [checkEquationAt, decoded] at accepted
    | some element =>
        have all : leftHeader = index (.collection kind source) ∧
            rightHeader = index (.collection kind source) ∧
            Classifies (liftClosed (nativeType element)) kind left ∧
            Classifies (liftClosed (nativeType element)) kind right ∧
            Equivalent (liftClosed (nativeType element)) left right := by
          simpa only [checkEquationAt, decoded, Bool.and_eq_true, decide_eq_true_eq, check_exact,
            checkEquivalent_exact, and_assoc] using accepted
        rcases all with ⟨rfl, rfl, first, second, same⟩
        exact sort?_source decoded ▸ EquationAt.collection kind element first second same
  · intro admitted
    cases admitted with
    | collection kind element first second same =>
        simp only [checkEquationAt, indexed, sort?_readback, Bool.and_eq_true,
          decide_true, check_exact, checkEquivalent_exact, true_and]
        exact ⟨⟨first, second⟩, same⟩

@[simp] theorem checkAt_sourcePack (language : LanguageDef) (kind : CollType)
    (element : DeclaredSort language) (values : List (Tower.Tm n)) :
    checkAt language (.collection kind element.val) (sourcePack kind element values) = true := by
  simp [checkAt, sourcePack, indexed, sort?_readback]

@[simp] theorem checkEquationAt_sourcePack (language : LanguageDef) (kind : CollType)
    (element : DeclaredSort language) (left right : List (Tower.Tm n)) :
    checkEquationAt language (.collection kind element.val)
        (sourcePack kind element left) (sourcePack kind element right) =
      CollectionObservation.checkLists kind left right := by
  simp [checkEquationAt, sourcePack, indexed, checkEquivalent, sort?_readback]

theorem wrong_type_refused {language : LanguageDef} {requested actual : TypeExpr}
    (different : actual ≠ requested) (payload : Tower.Tm n) :
    checkAt language requested (indexed actual payload) = false := by
  have distinct : index (n := n) actual ≠ index requested := fun same => different (index_injective same)
  cases requested <;> simp only [checkAt, indexed]
  rename_i kind body
  cases sort? language body <;> simp [distinct]

@[simp] theorem sourcePack_substitute {language : LanguageDef} (action : Sub Tower.Head n m)
    (kind : CollType) (element : DeclaredSort language) (values : List (Tower.Tm n)) :
    Presentation.subst action (sourcePack kind element values) =
      sourcePack kind element (values.map (Presentation.subst action)) := by
  simp only [sourcePack, indexed, Presentation.subst, index_substitute, pack_substitute, subst_liftClosed]

theorem at_substitute {language : LanguageDef} {source : TypeExpr} {term : Tower.Tm n}
    (admitted : At language source term) (action : Sub Tower.Head n m) :
    At language source (Presentation.subst action term) := by
  cases admitted with
  | collection kind element native =>
      have mapped := classifies_substitute native action
      simp only [subst_liftClosed] at mapped
      simpa only [indexed, Presentation.subst, index_substitute] using At.collection kind element mapped

theorem equationAt_substitute {language : LanguageDef} {source : TypeExpr} {left right : Tower.Tm n}
    (same : EquationAt language source left right) (action : Sub Tower.Head n m) :
    EquationAt language source (Presentation.subst action left) (Presentation.subst action right) := by
  cases same with
  | collection kind element first second same =>
      have firstMapped := classifies_substitute first action
      have secondMapped := classifies_substitute second action
      have mapped := equivalent_substitute same action
      simp only [subst_liftClosed] at firstMapped secondMapped mapped
      simpa only [indexed, Presentation.subst, index_substitute] using
        EquationAt.collection kind element firstMapped secondMapped mapped

theorem sourcePack_injective {language : LanguageDef} {first second : CollType}
    {leftElement rightElement : DeclaredSort language} {left right : List (Tower.Tm n)}
    (same : sourcePack first leftElement left = sourcePack second rightElement right) :
    TypeExpr.collection first leftElement.val = TypeExpr.collection second rightElement.val ∧ left = right := by
  have endpoints := Tm.pair.inj same
  have sourceSame := index_injective endpoints.1
  have parts := TypeExpr.collection.inj sourceSame
  obtain ⟨rfl, elementSame⟩ := parts
  have sortedSame : leftElement = rightElement := Subtype.ext elementSame
  cases sortedSame
  have decoded := congrArg (read (liftClosed (nativeType leftElement))) endpoints.2
  have paired : (first, left) = (first, right) := by simpa only [read_pack, Option.some.injEq] using decoded
  exact ⟨sourceSame, congrArg Prod.snd paired⟩

theorem equationAt_reflects (language : LanguageDef) (kind : CollType)
    (element : DeclaredSort language) (left right : List (Tower.Tm n)) :
    EquationAt language (.collection kind element.val) (sourcePack kind element left) (sourcePack kind element right) ↔
      CollectionObservation.Related kind left right := by
  rw [← checkEquationAt_exact, checkEquationAt_sourcePack, CollectionObservation.checkLists_exact]

/-- Erasure uses two actual native second projections: first discard the
source type index, then discard the collection discriminator. -/
def eraseSource (term : Tower.Tm n) : Tower.Tm n := .snd (.snd term)

def eraseSourceCode {language : LanguageDef} (kind : CollType) (element : DeclaredSort language)
    (values : List (Tower.Tm n)) : StructuralConversionCode.Code Tower.Head (fun _ => Empty) n :=
  .trans (.single (.congSnd (.betaSigmaSnd (index (.collection kind element.val))
      (pack kind (liftClosed (nativeType element)) values))))
    (.single (eraseCode kind (liftClosed (nativeType element)) values))

@[simp] theorem eraseSourceCode_read {language : LanguageDef} (kind : CollType)
    (element : DeclaredSort language) (values : List (Tower.Tm n)) :
    (eraseSourceCode kind element values).check Eq (fun code : Empty => nomatch code)
      (eraseSource (sourcePack kind element values))
      (IntrinsicNativeListMapComputation.encode (liftClosed (nativeType element)) values) = true := by
  simp [eraseSourceCode, StructuralConversionCode.Code.check, StructuralConversionCode.Code.decode,
    StructuralConversionCode.StepCode.decode, StructuralConversionCode.mapEndpoints,
    StructuralConversionCode.joinEndpoints, eraseSource, sourcePack, indexed, eraseCode, pack]

/-- This native lambda adds the physical source index and collection kind
around an existing payload. It does not validate that payload. -/
def introduction (kind : CollType) (source : TypeExpr) : Tower.Tm 0 :=
  .lam (.pair (index source) (.pair (tag kind) (.var 0)))

def introductionCode (kind : CollType) (source : TypeExpr) (payload : Tower.Tm n) :
    StructuralConversionCode.StepCode Tower.Head (fun _ => Empty) n :=
  .betaPi (.pair (index source) (.pair (tag kind) (.var 0))) payload

@[simp] theorem introductionCode_read {language : LanguageDef} (kind : CollType)
    (element : DeclaredSort language) (values : List (Tower.Tm n)) :
    StructuralConversionCode.StepCode.check Eq (fun code : Empty => nomatch code)
      (introductionCode kind (.collection kind element.val)
        (IntrinsicNativeListMapComputation.encode (liftClosed (nativeType element)) values))
      (.app (liftClosed (introduction kind (.collection kind element.val)))
        (IntrinsicNativeListMapComputation.encode (liftClosed (nativeType element)) values))
      (sourcePack kind element values) = true := by
  cases kind <;>
    simp [StructuralConversionCode.StepCode.check, StructuralConversionCode.StepCode.decode,
      introductionCode, introduction, liftClosed, Presentation.rename, liftRen, inst0, Presentation.subst,
      NativeWireData.rename_encode, index, NativeWireData.subst_encode, tag, sourcePack, indexed, pack]

namespace IndexedSignature

/-- The native wire constants and the actual Nat/List/authored-sort constants
have disjoint literal declaration names. -/
private theorem core_disjoint (language : LanguageDef) {name : DeclName} {entry : Entry Tower.Head}
    (known : (Core.signature language).entries name = some entry) :
    NativeWireData.signature.entries name = none := by
  by_cases h0 : name = Intrinsic.listName
  · subst name
    decide
  by_cases h1 : name = Intrinsic.nilName
  · subst name
    decide
  by_cases h2 : name = Intrinsic.consName
  · subst name
    decide
  by_cases h3 : name = Intrinsic.eliminateName
  · subst name
    decide
  by_cases h4 : name = Intrinsic.identityEliminateName
  · subst name
    decide
  by_cases h5 : name = IntrinsicRelator.mapRelName
  · subst name
    decide
  by_cases h6 : name = IntrinsicRelator.nilRelName
  · subst name
    decide
  by_cases h7 : name = IntrinsicRelator.consRelName
  · subst name
    decide
  by_cases h8 : name = IntrinsicRelator.eliminateName
  · subst name
    decide
  by_cases h9 : name = NativeNaturalVectorFamilies.natName
  · subst name
    decide
  by_cases h10 : name = NativeNaturalVectorFamilies.zeroName
  · subst name
    decide
  by_cases h11 : name = NativeNaturalVectorFamilies.succName
  · subst name
    decide
  have listMissing :
      (FormationSensitiveNativeList.Instantiated.levelInstance Tower.zero).signature.entries name = none := by
    simp [FormationSensitiveNativeList.Instantiated.levelInstance,
      LevelInstance.signature, Signature.instantiateLevels, IntrinsicRelator.rawSignature,
      Intrinsic.rawSignature, Intrinsic.declarations, Signature.ofList, Signature.insert,
      Signature.empty, *]
  have naturalMissing : (Signature.ofList Core.naturalDeclarations).entries name = none := by
    simp [Core.naturalDeclarations, NativeNaturalVectorFamilies.declarations,
      Signature.ofList, Signature.insert, Signature.empty, *]
  have localRead : (Signature.ofList (AuthoredBindingDeclarations.sortDeclarations language)).entries name = some entry := by
    simpa only [Core.signature, listMissing, Option.orElse_none, Core.localDeclarations,
      Signature.entries_ofList_append, naturalMissing] using known
  have member := Signature.entries_ofList_mem _ localRead
  obtain ⟨position, same⟩ := List.mem_ofFn.mp member
  have nameSame : AuthoredBindingDeclarations.sortDeclName language position = name := congrArg Prod.fst same
  subst name
  simp [NativeWireData.signature, AuthoredBindingDeclarations.sortDeclName,
    NativeWireData.dataName, NativeWireData.applicationName, NativeWireData.consName,
    NativeWireData.nilName, NativeWireData.naturalPrefix]

/-- One opt-in declaration environment retains both original libraries and
the original List computation. Neither signature replaces the other's entries. -/
def signature (language : LanguageDef) : Signature Tower.Head where
  entries name := ((Core.signature language).entries name).orElse
    (fun _ => NativeWireData.signature.entries name)
  computation := (Core.signature language).computation

def rules (language : LanguageDef) : Rules Tower.Head := extendRules Tower.rules (signature language)
abbrev Typing (language : LanguageDef) {n : Nat} := FormationSensitive.Typing (rules language) (n := n)

theorem coreExtension (language : LanguageDef) : (Core.signature language).Extends (signature language) where
  entries := by
    intro name entry found
    simp only [signature, found, Option.orElse_some]
  computation := fun step => step

theorem wireExtension (language : LanguageDef) : NativeWireData.signature.Extends (signature language) where
  entries := by
    intro name entry found
    cases coreRead : (Core.signature language).entries name with
    | none => simp only [signature, coreRead, Option.orElse_none, found]
    | some coreEntry =>
        have missing := core_disjoint language coreRead
        rw [found] at missing
        cases missing
  computation := by
    intro n left right impossible
    cases impossible

theorem index_typed (language : LanguageDef) (source : TypeExpr) (context : Tower.Ctx n) :
    Typing language context (index source) NativeWireData.dataType :=
  (NativeWireData.encode_typing context _).monoSignature (wireExtension language)

def indexedType (element : Tower.Tm n) : Tower.Tm n :=
  .sigma NativeWireData.dataType (Presentation.rename wk (packetType element))

@[simp] theorem indexedType_rename (action : Ren n m) (element : Tower.Tm n) :
    Presentation.rename action (indexedType element) = indexedType (Presentation.rename action element) := by
  simp only [indexedType, Presentation.rename, NativeWireData.dataType, rename_comp]
  congr 1
  rw [← packetType_rename]
  simp only [rename_comp]
  rfl

theorem indexedType_formed (language : LanguageDef) {context : Tower.Ctx n} {element : Tower.Tm n}
    (formed : Core.Typing language context element (sortTm Tower.zero)) :
    Typing language context (indexedType element) (sortTm Tower.zero) := by
  have first := (NativeWireData.dataType_formed context).monoSignature (wireExtension language)
  have second := ((packetType_formed language formed).monoSignature (coreExtension language)).weaken
    (extension := NativeWireData.dataType)
  exact .cumul (.sigmaForm first (.sort Tower.zero) second (.sort Tower.zero)
    (.sorts Tower.zero Tower.zero)) (by
      intro valuation
      simp [Mettapedia.TypeTheory.UniverseLevel.LevelExpr.eval, Tower.zero, LevelTower.zero])

/-- Native pairing programs can wrap any already typed List payload. The
separate refinement checker still has to validate its literal List spine. -/
theorem wrap_typed (language : LanguageDef) {context : Tower.Ctx n} {element payload : Tower.Tm n}
    (source : TypeExpr) (kind : CollType)
    (formed : Core.Typing language context element (sortTm Tower.zero))
    (payloadTyped : Typing language context payload (Intrinsic.listApp element)) :
    Typing language context (indexed source (.pair (tag kind) payload)) (indexedType element) := by
  have tagTyped : Typing language context (tag kind) natTm := by
    cases kind <;>
      exact (NativeSequenceBindings.numeral_typed (Core.naturals language) _).monoSignature
        (coreExtension language)
  have packetTyped : Typing language context (.pair (tag kind) payload) (packetType element) :=
    FormationSensitive.Typing.pairIntro (R := rules language) ((packetType_formed language formed).monoSignature (coreExtension language))
      (.sort Tower.zero) tagTyped (by
        change Typing language context payload (inst0 (tag kind) (Presentation.rename wk (Intrinsic.listApp element)))
        rw [inst0_rename_wk]
        exact payloadTyped)
  exact FormationSensitive.Typing.pairIntro (R := rules language)
    (indexedType_formed language formed) (.sort Tower.zero)
    (index_typed language source context) (by
      change Typing language context (.pair (tag kind) payload)
        (inst0 (index source) (Presentation.rename wk (packetType element)))
      rw [inst0_rename_wk]
      exact packetTyped)

theorem sourcePack_typed (language : LanguageDef) {context : Tower.Ctx n}
    (kind : CollType) (element : DeclaredSort language) (values : List (Tower.Tm n))
    (typed : ∀ value ∈ values, Core.Typing language context value (liftClosed (nativeType element))) :
    Typing language context (sourcePack kind element values)
      (indexedType (liftClosed (nativeType element))) := by
  have formed := FormationCheckedTelescopePrograms.liftClosed_typing
    (Core.type_formed (nativeType_read element)) context
  exact wrap_typed language (.collection kind element.val) kind formed
    ((Core.encode_typed language formed values typed).monoSignature (coreExtension language))

/-- The actual wrapping lambda has its independently formed native interface. -/
theorem introduction_typed (language : LanguageDef) (kind : CollType) (element : DeclaredSort language) :
    Typing language .nil (introduction kind (.collection kind element.val))
      (closedArrow (Intrinsic.listApp (nativeType element)) (indexedType (nativeType element))) := by
  let domain : Tower.Tm 0 := Intrinsic.listApp (nativeType element)
  have elementFormed := Core.type_formed (nativeType_read element)
  have domainFormed := (Core.listApp_typed language elementFormed).monoSignature (coreExtension language)
  have outputFormed := indexedType_formed language elementFormed
  have functionFormed : Typing language .nil
      (closedArrow domain (indexedType (nativeType element))) (sortTm Tower.zero) :=
    NativeSequenceBindings.closedArrow_formed domainFormed outputFormed
  have insideElement := FormationCheckedTelescopePrograms.liftClosed_typing elementFormed (.snoc .nil domain)
  have argument : Typing language (.snoc .nil domain) (.var 0)
      (Intrinsic.listApp (liftClosed (nativeType element))) := by
    have variableTyped := FormationSensitive.Typing.var (R := rules language) (Γ := .snoc .nil domain) 0
    change Typing language (.snoc .nil domain) (.var 0) (Presentation.rename wk domain) at variableTyped
    have same : Presentation.rename wk domain = Intrinsic.listApp (liftClosed (nativeType element)) := by
      apply congrArg Intrinsic.listApp
      exact rename_ext (rho := (wk : Ren 0 1)) (xi := Fin.elim0)
        (fun position => Fin.elim0 position) (nativeType element)
    exact same ▸ variableTyped
  have body := wrap_typed language (.collection kind element.val) kind insideElement argument
  apply FormationSensitive.Typing.lamIntro (R := rules language) functionFormed (.sort Tower.zero)
  simpa only [introduction, indexed, liftClosed_closedArrow, liftClosed,
    indexedType_rename] using body

theorem eraseSource_typed (language : LanguageDef) {context : Tower.Ctx n}
    (kind : CollType) (element : DeclaredSort language) (values : List (Tower.Tm n))
    (typed : ∀ value ∈ values, Core.Typing language context value (liftClosed (nativeType element))) :
    Typing language context (eraseSource (sourcePack kind element values))
      (Intrinsic.listApp (liftClosed (nativeType element))) := by
  have sourceTyped := sourcePack_typed language kind element values typed
  have first : Typing language context (.snd (sourcePack kind element values))
      (packetType (liftClosed (nativeType element))) := by
    simpa only [indexedType, inst0_rename_wk] using FormationSensitive.Typing.sndElim sourceTyped
  simpa only [packetType, eraseSource, inst0_rename_wk] using FormationSensitive.Typing.sndElim first

end IndexedSignature

end NativeCollections
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions.FullHeaders
namespace CollectionConstructors

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration BindingSignatureEmbedding TelescopeAbstraction
open NativeIndexedFamilies IntrinsicMaps
open Mettapedia.OSLF
open Mettapedia.GSLT.LanguageDef.BindingSyntax

variable {language : LanguageDef} {n : Nat}

/-- Even an empty collection obtains its element formation from the actual
original constructor header, rather than guessing from its zero arguments. -/
theorem element_declared (installed : Installation language) (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String) (kind : CollType) (element : TypeExpr)
    (shape : rule.params = [.simple parameter (.collection kind element)]) :
    DeclaredType language element := by
  have admitted := installed.source_admitted
    (AuthoredBindingDeclarations.Functional.constructorIndex rule member)
  unfold AdmittedHeader at admitted
  rw [AuthoredBindingDeclarations.Functional.constructorIndex_read] at admitted
  obtain ⟨source, read, formed⟩ := admitted.1 (.simple parameter (.collection kind element))
    (by rw [shape]; exact List.mem_singleton_self _)
  change some (.collection kind element) = some source at read
  have collectionFormed : DeclaredType language (.collection kind element) :=
    (Option.some.inj read).symm ▸ formed
  cases collectionFormed with
  | collection _ elementFormed => exact elementFormed

def elementSort (installed : Installation language) (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String) (kind : CollType) (element : TypeExpr)
    (shape : rule.params = [.simple parameter (.collection kind element)]) : DeclaredSort language :=
  ⟨element, element_declared installed rule member parameter kind element shape⟩

theorem parameter_read (installed : Installation language) (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String) (kind : CollType) (element : TypeExpr)
    (shape : rule.params = [.simple parameter (.collection kind element)]) :
    parameter? language (.simple parameter (.collection kind element)) =
      some (DeclaredSort.collection kind (elementSort installed rule member parameter kind element shape)) := by
  simp only [parameter?, Mettapedia.GSLT.LanguageDef.WellSorted.parameterType?, Option.bind_some]
  change sort? language
    (DeclaredSort.collection kind (elementSort installed rule member parameter kind element shape)).val = _
  exact sort?_readback _

theorem parameters_exact (installed : Installation language) (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String) (kind : CollType) (element : TypeExpr)
    (shape : rule.params = [.simple parameter (.collection kind element)]) :
    installed.parameters (AuthoredBindingDeclarations.Functional.constructorIndex rule member) =
      [DeclaredSort.collection kind (elementSort installed rule member parameter kind element shape)] := by
  have actual := installed.parameters_read
    (AuthoredBindingDeclarations.Functional.constructorIndex rule member)
  rw [AuthoredBindingDeclarations.Functional.constructorIndex_read, shape] at actual
  have expected : NativeSignature.decodeList (parameter? language)
      [.simple parameter (.collection kind element)] =
        some [DeclaredSort.collection kind (elementSort installed rule member parameter kind element shape)] := by
    simp only [NativeSignature.decodeList, parameter_read installed rule member parameter kind element shape]
    rfl
  exact Option.some.inj (actual.symm.trans expected)

theorem header_exact (installed : Installation language) (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String) (kind : CollType) (element : TypeExpr)
    (shape : rule.params = [.simple parameter (.collection kind element)]) :
    installed.header (AuthoredBindingDeclarations.Functional.constructorIndex rule member) =
      closedArrow
        (Intrinsic.listApp (nativeType (elementSort installed rule member parameter kind element shape)))
        (nativeType (installed.result (AuthoredBindingDeclarations.Functional.constructorIndex rule member))) := by
  let origin := AuthoredBindingDeclarations.Functional.constructorIndex rule member
  let selected := elementSort installed rule member parameter kind element shape
  have nativeHeader := installed.header_parameters origin
  have selectedParameters := parameters_exact installed rule member parameter kind element shape
  have mapped := congrArg (fun parameters : List (DeclaredSort language) =>
    ClosedOperators.argumentsType (S := sourceSignature language) (nativeType (language := language))
      (parameters.map (fun sort => ([], sort))) (nativeType (installed.result origin))) selectedParameters
  have simplified : ClosedOperators.argumentsType (S := sourceSignature language)
      (nativeType (language := language)) [([], DeclaredSort.collection kind selected)]
      (nativeType (installed.result origin)) =
        closedArrow (Intrinsic.listApp (nativeType selected)) (nativeType (installed.result origin)) := by
    change closedArrow (nativeType (DeclaredSort.collection kind selected)) _ = _
    rw [nativeType_collection]
    rfl
  exact nativeHeader.trans (mapped.trans simplified)

def body (origin : Fin language.terms.length) (element : DeclaredSort language) (count : Nat) :
    Tower.Tm (List.replicate count element).length :=
  .app (.const (AuthoredBindingDeclarations.constructorDeclName language origin))
    (StructuralPrograms.collectionBody element count)

def program (origin : Fin language.terms.length) (element : DeclaredSort language) (count : Nat) : Tower.Tm 0 :=
  closeTerm (ClosedOperators.typeContext (S := sourceSignature language)
    (nativeType (language := language)) (List.replicate count element)) (body origin element count)

/-- All physical source elements are passed to the original List constructor
program, then to the actual literal source constructor declaration. -/
theorem body_typed (installed : Installation language) (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String) (kind : CollType) (element : TypeExpr)
    (shape : rule.params = [.simple parameter (.collection kind element)]) (count : Nat) :
    let selected := elementSort installed rule member parameter kind element shape
    let origin := AuthoredBindingDeclarations.Functional.constructorIndex rule member
    installed.Typing
      (ClosedOperators.typeContext (S := sourceSignature language)
        (nativeType (language := language)) (List.replicate count selected))
      (body origin selected count) (liftClosed (nativeType (installed.result origin))) := by
  let selected := elementSort installed rule member parameter kind element shape
  let origin := AuthoredBindingDeclarations.Functional.constructorIndex rule member
  let context := ClosedOperators.typeContext (S := sourceSignature language)
    (nativeType (language := language)) (List.replicate count selected)
  have constructorTyped := installed.constructor_typed origin
  rw [header_exact installed rule member parameter kind element shape] at constructorTyped
  have functionTyped := FormationCheckedTelescopePrograms.liftClosed_typing constructorTyped context
  have payload := (StructuralPrograms.collectionBody_typed selected count).monoSignature installed.extension
  exact NativeSequenceBindings.apply_closedArrow functionTyped payload

/-- This covers the full original bare-collection constructor branch,
including arbitrary admitted element types and zero physical elements. -/
theorem program_typed (installed : Installation language) (rule : GrammarRule)
    (member : rule ∈ language.terms) (parameter : String) (kind : CollType) (element : TypeExpr)
    (shape : rule.params = [.simple parameter (.collection kind element)]) (count : Nat) :
    let selected := elementSort installed rule member parameter kind element shape
    let origin := AuthoredBindingDeclarations.Functional.constructorIndex rule member
    installed.Typing .nil (program origin selected count)
      (ClosedOperators.argumentsType (S := sourceSignature language) nativeType
        (List.replicate count ([], selected)) (nativeType (installed.result origin))) := by
  let selected := elementSort installed rule member parameter kind element shape
  let origin := AuthoredBindingDeclarations.Functional.constructorIndex rule member
  have resultFormed := (Core.type_formed (nativeType_read (installed.result origin))).monoSignature installed.extension
  have typed := (ConstructorPrograms.formation installed).closeTerm_typing resultFormed
    (body origin selected count) (body_typed installed rule member parameter kind element shape count)
  have closed := ClosedOperators.closeType_spine (S := sourceSignature language)
    (nativeType (language := language)) (List.replicate count selected) (nativeType (installed.result origin))
  have sourceArrows := StructuralPrograms.argumentsType_replicate selected count (nativeType (installed.result origin))
  have repeated := NativeSequenceBindings.curriedType_bindingSpine
    (source := sourceSignature language) (nativeType (language := language)) selected
    (nativeType (installed.result origin)) count
  have actual : installed.Typing .nil (program origin selected count)
      (NativeSequenceBindings.curriedType count (nativeType selected) (nativeType (installed.result origin))) :=
    (closed.trans repeated) ▸ typed
  exact (congrArg (fun type => installed.Typing .nil (program origin selected count) type) sourceArrows).mpr actual

/-- The selected certificate uses the existing telescope compiler. All
intermediate applications and the final literal List payload are retained. -/
def code (origin : Fin language.terms.length) (element : DeclaredSort language) (count : Nat)
    (values : Fin (List.replicate count element).length → Tower.Tm n) :
    StructuralConversionCode.Code Tower.Head (fun _ => Empty) n :=
  FormationCheckedTelescopePrograms.applicationCode
    (ClosedOperators.typeContext (S := sourceSignature language)
      (nativeType (language := language)) (List.replicate count element))
    (StructuralPrograms.collectionSub element count values) (body origin element count)

theorem code_checked (origin : Fin language.terms.length) (element : DeclaredSort language) (count : Nat)
    (values : Fin (List.replicate count element).length → Tower.Tm n) :
    (code origin element count values).check (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot
      ((List.ofFn values).foldl Tm.app (liftClosed (program origin element count)))
      (.app (.const (AuthoredBindingDeclarations.constructorDeclName language origin))
        (IntrinsicNativeListMapComputation.encode (liftClosed (nativeType element)) (List.ofFn values))) = true := by
  have actual := FormationCheckedTelescopePrograms.applicationCode_checked
    (ClosedOperators.typeContext (S := sourceSignature language)
      (nativeType (language := language)) (List.replicate count element))
    (StructuralPrograms.collectionSub element count values) (body origin element count)
  have input : applyClosed
      (ClosedOperators.typeContext (S := sourceSignature language)
        (nativeType (language := language)) (List.replicate count element))
      (StructuralPrograms.collectionSub element count values) (liftClosed (program origin element count)) =
        (List.ofFn values).foldl Tm.app (liftClosed (program origin element count)) := by
    rw [NativeSequenceBindings.applyClosed_arguments
      (ClosedOperators.typeContext (S := sourceSignature language)
        (nativeType (language := language)) (List.replicate count element))
      (StructuralPrograms.collectionSub element count values) (liftClosed (program origin element count))]
    change (List.map (fun position => values position.rev)
      (List.finRange (List.replicate count element).length).reverse).foldl Tm.app _ = _
    rw [List.finRange_reverse, List.map_map]
    simp only [Function.comp_def, Fin.rev_rev]
    rw [← List.ofFn_eq_map]
  have output : subst (StructuralPrograms.collectionSub element count values) (body origin element count) =
      .app (.const (AuthoredBindingDeclarations.constructorDeclName language origin))
        (IntrinsicNativeListMapComputation.encode (liftClosed (nativeType element)) (List.ofFn values)) := by
    simp only [body, Presentation.subst, StructuralPrograms.collectionBody_substitute]
  exact congrArg₂ (fun left right => (code origin element count values).check
    (fun _ _ => False) FormationCheckedTelescopePrograms.noRoot left right) input output ▸ actual

theorem code_steps (origin : Fin language.terms.length) (element : DeclaredSort language) (count : Nat)
    (values : Fin (List.replicate count element).length → Tower.Tm n) :
    (code origin element count values).stepCount = count := by
  exact (FormationCheckedTelescopePrograms.applicationCode_stepCount
    (ClosedOperators.typeContext (S := sourceSignature language)
      (nativeType (language := language)) (List.replicate count element))
    (StructuralPrograms.collectionSub element count values) (body origin element count)).trans List.length_replicate

end CollectionConstructors
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions.FullHeaders


namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions.FullHeaders
namespace Operational

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.NativeTypes.Generation
open Mettapedia.OSLF.NativeTypes.Generation.BindingSemanticAdmission
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Presentation Presentation.Declaration BindingSignatureEmbedding
open Mettapedia.OSLF
open Mettapedia.GSLT.LanguageDef.BindingSyntax

variable {language : LanguageDef}

private theorem collection_element_formed (result : DeclaredSort language) (kind : CollType)
    (element : TypeExpr) (read : result.val = .collection kind element) :
    DeclaredType language element := by
  have formed : DeclaredType language (.collection kind element) := read ▸ result.property
  cases formed with | collection _ elementFormed => exact elementFormed

def collectionElement (result : DeclaredSort language) (kind : CollType) (element : TypeExpr)
    (read : result.val = .collection kind element) : DeclaredSort language :=
  ⟨element, collection_element_formed result kind element read⟩

/-- All six branches are the original source operators. The programs preserve
operational representations; checked source refinements remain separate. -/
def operatorImage (installed : Installation language) :
    {sourceResult : TypeExpr} → Operator language sourceResult →
    (result : DeclaredSort language) → result.val = sourceResult →
    List (List (DeclaredSort language) × DeclaredSort language) → Tower.Tm 0
  | _, .constructor rule member _ scopes, _, _, arity =>
      ConstructorPrograms.sourceProgram installed rule member scopes arity
  | _, .collectionConstructor rule member parameter kind element shape count, _, _, _ =>
      CollectionConstructors.program
        (AuthoredBindingDeclarations.Functional.constructorIndex rule member)
        (CollectionConstructors.elementSort installed rule member parameter kind element shape) count
  | _, .lambda _ _, _, _, _ => ClosedOperators.Derived.identity
  | _, .multiLambda _ _ count, _, _, _ => NativeSequenceBindings.introduction count
  | _, .subst _ _, _, _, _ => ClosedOperators.Derived.identity
  | _, .collection kind element count, result, read, _ =>
      StructuralPrograms.collectionProgram (collectionElement result kind element read) count

def images (installed : Installation language) : ClosedOperators.Images (sourceSignature language) Tower.Head :=
  fun {result} operator => operatorImage installed operator.original result rfl operator.arity

/-- Each operator earns its original binding-arity interface from literal
header formation and the actual native programs. No whole-term preservation
assumption is stored in the installation. -/
theorem operatorImage_typed (installed : Installation language) {sourceResult : TypeExpr}
    (original : Operator language sourceResult) (result : DeclaredSort language)
    (resultRead : result.val = sourceResult)
    (arity : List (List (DeclaredSort language) × DeclaredSort language))
    (projects : (signatureOf language).arity original = Binding.mapArities Subtype.val arity) :
    installed.Typing .nil (operatorImage installed original result resultRead arity)
      (ClosedOperators.argumentsType (S := sourceSignature language) nativeType arity (nativeType result)) := by
  cases original with
  | constructor rule member ordinary scopes =>
      exact ConstructorPrograms.sourceProgram_typed installed rule member scopes arity projects result resultRead
  | collectionConstructor rule member parameter kind element shape count =>
      let selected := CollectionConstructors.elementSort installed rule member parameter kind element shape
      let origin := AuthoredBindingDeclarations.Functional.constructorIndex rule member
      have aritySame : arity = List.replicate count ([], selected) := by
        apply Binding.mapArities_injective Subtype.val_injective
        simpa only [signatureOf, Binding.mapArities, Binding.mapArity, List.map_replicate,
          List.map_nil, selected, CollectionConstructors.elementSort] using projects.symm
      have resultSame : installed.result origin = result := by
        apply Subtype.ext
        have actual := sort?_source (installed.result_read origin)
        have row := AuthoredBindingDeclarations.Functional.constructorIndex_read rule member
        exact actual.trans ((congrArg (fun selected => TypeExpr.base selected.category) row).trans resultRead.symm)
      subst arity
      exact resultSame ▸ CollectionConstructors.program_typed installed rule member parameter kind element shape count
  | lambda domain codomain =>
      have formed : DeclaredType language (.arrow domain codomain) := resultRead ▸ result.property
      cases formed with
      | arrow domainFormed codomainFormed =>
          let first : DeclaredSort language := ⟨domain, domainFormed⟩
          let last : DeclaredSort language := ⟨codomain, codomainFormed⟩
          have resultSame : result = DeclaredSort.arrow first last := Subtype.ext resultRead
          have aritySame : arity = [([first], last)] := by
            apply Binding.mapArities_injective Subtype.val_injective
            simpa only [signatureOf, Binding.mapArities, Binding.mapArity,
              List.map_cons, List.map_nil] using projects.symm
          subst result
          subst arity
          exact (StructuralPrograms.lambda_typed first last).monoSignature installed.extension
  | multiLambda domain codomain count =>
      have formed : DeclaredType language (.arrow (.multiBinder domain) codomain) := resultRead ▸ result.property
      cases formed with
      | arrow domainSequence codomainFormed =>
          cases domainSequence with
          | multiBinder domainFormed =>
              let first : DeclaredSort language := ⟨domain, domainFormed⟩
              let last : DeclaredSort language := ⟨codomain, codomainFormed⟩
              have resultSame : result = DeclaredSort.arrow (DeclaredSort.multiBinder first) last := Subtype.ext resultRead
              have aritySame : arity = [(List.replicate count first, last)] := by
                apply Binding.mapArities_injective Subtype.val_injective
                simpa only [signatureOf, Binding.mapArities, Binding.mapArity,
                  List.map_cons, List.map_nil, List.map_replicate] using projects.symm
              subst result
              subst arity
              exact (StructuralPrograms.multiLambda_typed first last count).monoSignature installed.extension
  | subst domain codomain =>
      have found : ([], domain) ∈ Binding.mapArities Subtype.val arity := by
        rw [← projects]
        exact List.mem_cons_of_mem _ (List.mem_singleton_self _)
      obtain ⟨slot, _, same⟩ := List.mem_map.mp found
      have domainRead : slot.2.val = domain := congrArg Prod.snd same
      let first : DeclaredSort language := ⟨domain, domainRead ▸ slot.2.property⟩
      have aritySame : arity = [([first], result), ([], first)] := by
        apply Binding.mapArities_injective Subtype.val_injective
        simpa only [signatureOf, Binding.mapArities, Binding.mapArity,
          List.map_cons, List.map_nil, resultRead] using projects.symm
      subst arity
      exact (StructuralPrograms.substitution_typed first result).monoSignature installed.extension
  | collection kind element count =>
      let selected := collectionElement result kind element resultRead
      have resultSame : result = DeclaredSort.collection kind selected := Subtype.ext resultRead
      have aritySame : arity = List.replicate count ([], selected) := by
        apply Binding.mapArities_injective Subtype.val_injective
        simpa only [signatureOf, Binding.mapArities, Binding.mapArity, List.map_replicate,
          List.map_nil, selected, collectionElement] using projects.symm
      have typed := (StructuralPrograms.collection_typed kind selected count).monoSignature installed.extension
      have resultTypeSame := congrArg (fun sort => ClosedOperators.argumentsType
        (S := sourceSignature language) nativeType (List.replicate count ([], selected)) (nativeType sort)) resultSame
      exact aritySame.symm ▸ (resultTypeSame.symm ▸ typed)

/-- The common native binding fold now has an earned formation realization
for the full original TypeExpr signature and every source operator. -/
def realization (installed : Installation language) :
    ClosedOperators.Realization (S := sourceSignature language) nativeType (images installed) installed.rules where
  toFormation := ConstructorPrograms.formation installed
  imageTyped := fun {result} operator =>
    operatorImage_typed installed operator.original result rfl operator.arity operator.projects

theorem compiled_judgment (installed : Installation language)
    {bound : List (DeclaredSort language)} {result : DeclaredSort language}
    (source : Binding.Term (sourceSignature language) bound result) :
    FormationSensitive.Judgment installed.rules
      (ClosedOperators.typeContext (nativeType (language := language)) bound)
      (ClosedOperators.compile (images installed) source) (liftClosed (nativeType result)) :=
  (realization installed).compile_judgment source

/-- The all-source simultaneous substitution square reuses the already
proved generic fold law, including every original binder spine. -/
theorem compiled_substitution (installed : Installation language)
    {sourceContext targetContext : List (DeclaredSort language)}
    (action : Binding.Sub (sourceSignature language) sourceContext targetContext)
    {result : DeclaredSort language} (source : Binding.Term (sourceSignature language) sourceContext result) :
    ClosedOperators.compile (images installed) (Binding.bind action source) =
      Presentation.subst (ClosedOperators.compileSub (images installed) action)
        (ClosedOperators.compile (images installed) source) :=
  (ClosedOperators.compile_substitution (images installed) action source).symm

end Operational
end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions.FullHeaders

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions.Literal

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation Presentation.BindingSignatureEmbedding

open Mettapedia.GSLT.LanguageDef

/-- The literal representation retains complete source operator descriptors,
including internal source types and original authored rows. It is separate
from the operational programs that deliberately erase some of this data. -/
def names (scope : Lean.Name) (language : LanguageDef) : Names (BindingSyntax.signatureOf language) where
  sort := BindingSyntax.Wire.sortName scope
  operator := BindingSyntax.Wire.operatorName scope language

def encode (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (source : Binding.Term (BindingSyntax.signatureOf language) context sort) : Tower.Tm context.length :=
  BindingSignatureEmbedding.encode (names scope language) source

theorem operator_names_injective (scope : Lean.Name) (language : LanguageDef) {sort : TypeExpr} :
    Function.Injective ((names scope language).operator (sort := sort)) :=
  BindingSyntax.Wire.operatorName_injective scope language

theorem encode_injective (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr} :
    Function.Injective (encode scope language (context := context) (sort := sort)) :=
  fun first second same => BindingSignatureEmbedding.encode_injective_of_operator_names
    (names scope language) (fun {_} => operator_names_injective scope language) first second same

/-- Renaming acts on the actual native variables; operator descriptors do
not hide any source body or binder. -/
theorem encode_rename (scope : Lean.Name) (language : LanguageDef)
    {context target : List TypeExpr} {sort : TypeExpr}
    (action : Binding.Ren (BindingSyntax.signatureOf language) context target)
    (source : Binding.Term (BindingSyntax.signatureOf language) context sort) :
    Presentation.rename (encodeRen action) (encode scope language source) =
      encode scope language (Binding.rename action source) :=
  BindingSignatureEmbedding.encode_rename (names scope language) action source

theorem encode_substitution (scope : Lean.Name) (language : LanguageDef)
    {context target : List TypeExpr} {sort : TypeExpr}
    (action : Binding.Sub (BindingSyntax.signatureOf language) context target)
    (source : Binding.Term (BindingSyntax.signatureOf language) context sort) :
    Presentation.subst (encodeSub (names scope language) action) (encode scope language source) =
      encode scope language (Binding.bind action source) :=
  BindingSignatureEmbedding.encode_substitution (names scope language) action source

/-- This concerns a native profile with no declared computation roots.
Source collection laws are supplied through their own explicit evidence;
they are not silently installed as ambient native conversion rules. -/
theorem conversion_iff_eq (scope : Lean.Name) (language : LanguageDef)
    (rules : Rules Tower.Head) (empty : rules.computation = RootComputation.empty)
    (symmetric : Std.Symm rules.headEq)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Binding.Term (BindingSyntax.signatureOf language) context sort) :
    Conv rules.headEq (encode scope language first) (encode scope language second) rules.computation ↔
      first = second :=
  BindingSignatureEmbedding.encode_conversion_iff_eq (names scope language)
    (fun {_} => operator_names_injective scope language) rules empty symmetric first second

theorem encoded_checked_iff_eq (scope : Lean.Name) (language : LanguageDef)
    (rules : Rules Tower.Head) [DecidableRel rules.headEq]
    (empty : rules.computation = RootComputation.empty) (symmetric : Std.Symm rules.headEq)
    {context : List TypeExpr} {sort : TypeExpr}
    (first second : Binding.Term (BindingSyntax.signatureOf language) context sort) :
    (∃ code : StructuralConversionCode.Code Tower.Head (fun _ => Empty) context.length,
      code.check rules.headEq FormationCheckedTelescopePrograms.noRoot
        (encode scope language first) (encode scope language second) = true) ↔ first = second :=
  BindingSignatureEmbedding.encoded_checked_iff_eq (names scope language)
    (fun {_} => operator_names_injective scope language) rules empty symmetric first second

namespace FiniteDeclarations

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations

/-- The actual source descriptors distinguish all sort and operator roles,
including operators with different result sorts. -/
theorem declarationName_injective (scope : Lean.Name) (language : LanguageDef) :
    Function.Injective (BindingSignaturePackage.declarationName (names scope language)) := by
  intro first second same
  cases first with
  | inl first =>
    cases second with
    | inl second => exact congrArg Sum.inl (BindingSyntax.Wire.sortName_injective scope same)
    | inr second =>
        exact False.elim (BindingSyntax.Wire.sortName_ne_operatorName scope language first second.2 same)
  | inr first =>
    cases second with
    | inl second =>
        exact False.elim (BindingSyntax.Wire.sortName_ne_operatorName scope language second first.2 same.symm)
    | inr second =>
        apply congrArg Sum.inr
        have decoded := congrArg (BindingSyntax.Wire.readOperatorName scope language) same
        simpa only [BindingSignaturePackage.declarationName, names,
          BindingSyntax.Wire.readOperatorName_operatorName, Option.some.injEq] using decoded

/-- The inventory is computed from the actual source term and ambient
context. Complete nested binding spines are retained by the shared package. -/
def inventory {language : LanguageDef} {context : List TypeExpr} {sort : TypeExpr}
    (source : Binding.Term (BindingSyntax.signatureOf language) context sort) :=
  BindingSignaturePackage.inventory source

def signature (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (source : Binding.Term (BindingSyntax.signatureOf language) context sort) : Declaration.Signature Tower.Head :=
  BindingSignaturePackage.signature (names scope language) (inventory source)

def rules (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (source : Binding.Term (BindingSyntax.signatureOf language) context sort) : Rules Tower.Head :=
  BindingSignaturePackage.rules (names scope language) (inventory source)

theorem wellFormed (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (source : Binding.Term (BindingSyntax.signatureOf language) context sort) :
    (signature scope language source).WellFormed Tower.rules :=
  BindingSignaturePackage.source_wellFormed (names scope language)
    (declarationName_injective scope language) source

/-- Every original scoped term earns a formed judgment in its computed
finite declaration package. No lookup for unused or infinitely many source
sorts is assumed, and no source type is replaced by an operational erasure. -/
theorem formed_judgment (scope : Lean.Name) (language : LanguageDef)
    {context : List TypeExpr} {sort : TypeExpr}
    (source : Binding.Term (BindingSyntax.signatureOf language) context sort) :
    FormationSensitive.Judgment (rules scope language source)
      (BindingSignatureEmbedding.context (names scope language) context)
      (Literal.encode scope language source) (sortType (names scope language) sort) :=
  BindingSignaturePackage.source_judgment (names scope language)
    (declarationName_injective scope language) source

end FiniteDeclarations

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.AuthoredTypeExpressions.Literal


set_option autoImplicit false

