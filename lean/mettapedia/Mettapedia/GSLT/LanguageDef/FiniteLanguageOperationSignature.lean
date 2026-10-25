import Mathlib.CategoryTheory.PathCategory.Basic
import Mathlib.Data.List.OfFn
import Mettapedia.GSLT.LanguageDef.StructuralCategory
import Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec

/-!
# Finite authored language-operation signatures

A validated language package contains finitely many named language codes and
finitely many primitive language-changing routes.  This module turns precisely
that authored data into:

* a quiver whose paths are the freely composed route programs;
* a functor into validated GSLT language definitions;
* declaration-aware two-sort syntax for codes and routes; and
* an executable, syntax-directed route recognizer.

The syntax encoding uses the declaration-aware two-sort calculus. The finite
signature and its structural interpretation are parameters, with no selected
candidate assembly.

There is no separate composition tree: route programs are Mathlib
`Quiver.Path`s.  The syntax recognizer is defined solely from the finite
authored names and endpoints; semantic GSLT morphisms enter only through the
separate structural interpretation.
-/

namespace Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature

open _root_.CategoryTheory
open scoped _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.StructuralMorphism
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Syntax
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Context
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationEnv
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSpec
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Renaming
open Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.Substitution

/-- The four names shared by every finite language-operation presentation. -/
structure CoreNames where
  languageType : DeclName
  routeType : DeclName
  identity : DeclName
  compose : DeclName
deriving DecidableEq, Repr

/-- A finite, named presentation of validated languages and primitive routes.

The route table is endpoint-indexed by its `source` and `target` functions.
Each route is also supplied with its already validated structural GSLT
morphism.  `declaredNamesNodup` is the executable no-shadowing boundary between
the four shared names, language constants, and primitive-route constants. -/
structure Signature where
  Language : Type
  languageCount : Nat
  routeCount : Nat
  names : CoreNames
  languageIndex : Fin languageCount ≃ Language
  languageName : Language ↪ DeclName
  routeName : Fin routeCount ↪ DeclName
  source : Fin routeCount → Language
  target : Fin routeCount → Language
  presentation : Language → ValidatedLanguageDef
  routeMorphism : ∀ route,
    StructuralMorphism (presentation (source route)) (presentation (target route))
  declaredNamesNodup :
    ([names.languageType, names.routeType, names.identity, names.compose] ++
      List.ofFn (fun index => languageName (languageIndex index)) ++
      List.ofFn routeName).Nodup

namespace Signature

abbrev Route (signature : Signature) := Fin signature.routeCount

instance languageDecidableEq (signature : Signature) :
    DecidableEq signature.Language :=
  signature.languageIndex.symm.decidableEq

/-- Primitive arrows are exactly entries of the authored route table. -/
inductive Generator (signature : Signature) :
    signature.Language → signature.Language → Type
  | named (route : signature.Route) :
      Generator signature (signature.source route) (signature.target route)

instance operationQuiver (signature : Signature) : Quiver signature.Language where
  Hom := signature.Generator

/-- Freely composed route programs. -/
abbrev Program (signature : Signature)
    (source target : signature.Language) := Quiver.Path source target

def identityProgram (signature : Signature) (language : signature.Language) :
    signature.Program language language :=
  .nil

def namedProgram (signature : Signature) (route : signature.Route) :
    signature.Program (signature.source route) (signature.target route) :=
  Quiver.Hom.toPath (.named route)

/-- The authored primitive routes as a prefunctor into validated GSLT
languages. -/
def structuralPrefunctor (signature : Signature) :
    signature.Language ⥤q ValidatedLanguageDef where
  obj := signature.presentation
  map
    | .named route => signature.routeMorphism route

/-- The structural interpretation of a route program is supplied by the free
path-category lift, rather than by another recursive interpreter. -/
def structuralInterpretation (signature : Signature) :
    Paths signature.Language ⥤ ValidatedLanguageDef :=
  Paths.lift signature.structuralPrefunctor

@[simp]
theorem structuralInterpretation_named (signature : Signature)
    (route : signature.Route) :
    signature.structuralInterpretation.map (signature.namedProgram route) =
      signature.routeMorphism route := by
  rfl

/-! ## Closed two-sort syntax -/

def languageType (signature : Signature) : ScopedTerm n :=
  .const signature.names.languageType

def languageTerm (signature : Signature)
    (language : signature.Language) : ScopedTerm n :=
  .const (signature.languageName language)

def routeType (signature : Signature) (source target : ScopedTerm n) : ScopedTerm n :=
  .app (.app (.const signature.names.routeType) source) target

def routeTypeFormer (signature : Signature) : ScopedTerm 0 :=
  .pi signature.languageType (.pi signature.languageType .u0)

def identityType (signature : Signature) : ScopedTerm 0 :=
  .pi signature.languageType
    (signature.routeType (.var 0) (.var 0))

def composeType (signature : Signature) : ScopedTerm 0 :=
  .pi signature.languageType
    (.pi signature.languageType
      (.pi signature.languageType
        (.pi (signature.routeType (.var 2) (.var 1))
          (.pi (signature.routeType (.var 2) (.var 1))
            (signature.routeType (.var 4) (.var 2))))))

def coreSpecs (signature : Signature) : List DeclSpec :=
  [{ name := signature.names.languageType, type := .u0 },
   { name := signature.names.routeType, type := signature.routeTypeFormer },
   { name := signature.names.identity, type := signature.identityType },
   { name := signature.names.compose, type := signature.composeType }]

def languageSpec (signature : Signature)
    (language : signature.Language) : DeclSpec :=
  { name := signature.languageName language
    type := signature.languageType }

def routeSpec (signature : Signature) (route : signature.Route) : DeclSpec :=
  { name := signature.routeName route
    type := signature.routeType
      (signature.languageTerm (signature.source route))
      (signature.languageTerm (signature.target route)) }

def operationSpecs (signature : Signature) : List DeclSpec :=
  signature.coreSpecs ++
    List.ofFn (fun index =>
      signature.languageSpec (signature.languageIndex index)) ++
    List.ofFn signature.routeSpec

def operationDeclEnv (signature : Signature) : DeclEnv :=
  envOfSpecs signature.operationSpecs

def identityTerm (signature : Signature)
    (language : signature.Language) : ScopedTerm 0 :=
  .app (.const signature.names.identity) (signature.languageTerm language)

def composeTerm (signature : Signature)
    (first middle last : signature.Language)
    (earlier later : ScopedTerm 0) : ScopedTerm 0 :=
  .app
    (.app
      (.app
        (.app
          (.app (.const signature.names.compose)
            (signature.languageTerm first))
          (signature.languageTerm middle))
        (signature.languageTerm last))
      earlier)
    later

def routeTerm (signature : Signature) (route : signature.Route) : ScopedTerm 0 :=
  .const (signature.routeName route)

/-- Compile a route path into closed two-sort syntax. -/
def encodeProgram (signature : Signature) {source target : signature.Language} :
    signature.Program source target → ScopedTerm 0
  | .nil => signature.identityTerm source
  | .cons prior generator =>
      match generator with
      | .named route =>
          signature.composeTerm source (signature.source route)
            (signature.target route) (signature.encodeProgram prior)
            (signature.routeTerm route)

/-! ## Finite name decoding -/

/-- Executable inverse search for a finite injectively named family. -/
def decodeIndex? {α : Type} [DecidableEq α] :
    {count : Nat} → (Fin count → α) → α → Option (Fin count)
  | 0, _, _ => none
  | _ + 1, names, name =>
      if names 0 = name then some 0
      else
        (decodeIndex? (fun index => names index.succ) name).map Fin.succ

@[simp]
theorem decodeIndex_encode {α : Type} [DecidableEq α]
    {count : Nat} (names : Fin count → α)
    (injective : Function.Injective names) (index : Fin count) :
    decodeIndex? names (names index) = some index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count inductionHypothesis =>
      refine Fin.cases ?_ ?_ index
      · simp [decodeIndex?]
      · intro prior
        have different : names 0 ≠ names prior.succ := by
          intro equal
          have indexEqual : (0 : Fin (count + 1)) = prior.succ :=
            injective equal
          have valueEqual : 0 = prior.val + 1 := congrArg Fin.val indexEqual
          exact (Nat.zero_ne_add_one prior.val) valueEqual
        have tailInjective :
            Function.Injective (fun i : Fin count => names i.succ) :=
          fun _ _ equal => Fin.ext (Nat.add_right_cancel
            (congrArg Fin.val (injective equal)))
        simp [decodeIndex?, different,
          inductionHypothesis (fun i : Fin count => names i.succ)
            tailInjective prior]

theorem decodeIndex_eq_some {α : Type} [DecidableEq α]
    {count : Nat} (names : Fin count → α) (name : α) (index : Fin count)
    (accepted : decodeIndex? names name = some index) :
    names index = name := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count inductionHypothesis =>
      by_cases firstMatches : names 0 = name
      · rw [decodeIndex?, if_pos firstMatches] at accepted
        cases accepted
        exact firstMatches
      · rw [decodeIndex?, if_neg firstMatches] at accepted
        cases tailAccepted :
            decodeIndex? (fun i : Fin count => names i.succ) name with
        | none => simp [tailAccepted] at accepted
        | some tailIndex =>
            rw [tailAccepted] at accepted
            cases accepted
            exact inductionHypothesis
              (fun i : Fin count => names i.succ) tailIndex tailAccepted

def decodeLanguageName? (signature : Signature) (name : DeclName) :
    Option signature.Language :=
  (decodeIndex?
    (fun index => signature.languageName (signature.languageIndex index))
    name).map signature.languageIndex

def decodeRouteName? (signature : Signature) (name : DeclName) :
    Option signature.Route :=
  decodeIndex? signature.routeName name

@[simp]
theorem decodeLanguageName_languageName (signature : Signature)
    (language : signature.Language) :
    signature.decodeLanguageName? (signature.languageName language) =
      some language := by
  unfold decodeLanguageName?
  have decoded := decodeIndex_encode
    (fun index => signature.languageName (signature.languageIndex index))
    (signature.languageName.injective.comp signature.languageIndex.injective)
    (signature.languageIndex.symm language)
  simpa using congrArg (Option.map signature.languageIndex) decoded

@[simp]
theorem decodeRouteName_routeName (signature : Signature)
    (route : signature.Route) :
    signature.decodeRouteName? (signature.routeName route) = some route :=
  decodeIndex_encode signature.routeName signature.routeName.injective route

def decodeLanguageTerm? (signature : Signature) :
    ScopedTerm 0 → Option signature.Language
  | .const name => signature.decodeLanguageName? name
  | _ => none

@[simp]
theorem decodeLanguageTerm_languageTerm (signature : Signature)
    (language : signature.Language) :
    signature.decodeLanguageTerm? (signature.languageTerm language) =
      some language := by
  simp [decodeLanguageTerm?, languageTerm]

theorem decodeLanguageTerm_eq_some (signature : Signature)
    {term : ScopedTerm 0} {language : signature.Language}
    (accepted : signature.decodeLanguageTerm? term = some language) :
    term = signature.languageTerm language := by
  cases term with
  | const name =>
      unfold decodeLanguageTerm? at accepted
      unfold decodeLanguageName? at accepted
      cases decodedIndex : decodeIndex?
          (fun index => signature.languageName (signature.languageIndex index))
          name with
      | none => simp [decodedIndex] at accepted
      | some index =>
          simp [decodedIndex] at accepted
          subst language
          exact congrArg ScopedTerm.const
            (decodeIndex_eq_some
              (fun index => signature.languageName
                (signature.languageIndex index))
              name index decodedIndex).symm
  | _ => simp [decodeLanguageTerm?] at accepted

/-- A recovered route program with intrinsically indexed endpoints. -/
structure DecodedProgram (signature : Signature) where
  source : signature.Language
  target : signature.Language
  program : signature.Program source target

/-- Transport a path across checked endpoint equalities. -/
def reindexProgram (signature : Signature)
    {source target newSource newTarget : signature.Language}
    (sourceEq : source = newSource) (targetEq : target = newTarget) :
    signature.Program source target → signature.Program newSource newTarget := by
  subst newSource
  subst newTarget
  exact id

def composeDecoded? (signature : Signature)
    (first middle last : signature.Language)
    (earlier later : signature.DecodedProgram) :
    Option signature.DecodedProgram :=
  if earlierSource : earlier.source = first then
    if earlierTarget : earlier.target = middle then
      if laterSource : later.source = middle then
        if laterTarget : later.target = last then
          some
            { source := first
              target := last
              program := Quiver.Path.comp
                (signature.reindexProgram earlierSource earlierTarget
                  earlier.program)
                (signature.reindexProgram laterSource laterTarget
                  later.program) }
        else none
      else none
    else none
  else none

/-- Syntax-directed recognition of the finite authored route fragment. -/
def decodeProgram? (signature : Signature) :
    ScopedTerm 0 → Option signature.DecodedProgram
  | .app (.const name) languageTerm =>
      if name = signature.names.identity then
        (signature.decodeLanguageTerm? languageTerm).map fun language =>
          { source := language
            target := language
            program := signature.identityProgram language }
      else none
  | .const name =>
      (signature.decodeRouteName? name).map fun route =>
        { source := signature.source route
          target := signature.target route
          program := signature.namedProgram route }
  | .app
      (.app
        (.app
          (.app
            (.app (.const name) firstTerm)
            middleTerm)
          lastTerm)
        earlierTerm)
      laterTerm =>
      if name = signature.names.compose then
        match signature.decodeLanguageTerm? firstTerm,
            signature.decodeLanguageTerm? middleTerm,
            signature.decodeLanguageTerm? lastTerm,
            signature.decodeProgram? earlierTerm,
            signature.decodeProgram? laterTerm with
        | some first, some middle, some last, some earlier, some later =>
            signature.composeDecoded? first middle last earlier later
        | _, _, _, _, _ => none
      else none
  | _ => none
termination_by term => term

@[simp]
theorem composeDecoded_programs (signature : Signature)
    {first middle last : signature.Language}
    (earlier : signature.Program first middle)
    (later : signature.Program middle last) :
    signature.composeDecoded? first middle last
        { source := first, target := middle, program := earlier }
        { source := middle, target := last, program := later } =
      some
        { source := first
          target := last
          program := Quiver.Path.comp earlier later } := by
  simp [composeDecoded?, reindexProgram]

/-- Encoding followed by independent recognition recovers every route path. -/
@[simp]
theorem decodeProgram_encodeProgram (signature : Signature)
    {source target : signature.Language}
    (program : signature.Program source target) :
    signature.decodeProgram? (signature.encodeProgram program) =
      some { source := source, target := target, program := program } := by
  induction program with
  | nil =>
      simp [encodeProgram, identityTerm, decodeProgram?, identityProgram]
  | cons prior generator inductionHypothesis =>
      cases generator with
      | named route =>
          simp [encodeProgram, composeTerm, routeTerm, decodeProgram?,
            inductionHypothesis, composeDecoded_programs, namedProgram]

/-- A composition term cannot disguise a disagreement between the recovered
target of its first route and the written middle endpoint. -/
theorem decodeProgram_compose_rejects_earlier_target
    (signature : Signature)
    {first actualMiddle writtenMiddle last : signature.Language}
    (earlier : signature.Program first actualMiddle)
    (later : signature.Program writtenMiddle last)
    (different : actualMiddle ≠ writtenMiddle) :
    signature.decodeProgram?
      (signature.composeTerm first writtenMiddle last
        (signature.encodeProgram earlier) (signature.encodeProgram later)) =
      none := by
  simp only [composeTerm, decodeProgram?]
  simp [decodeProgram_encodeProgram, composeDecoded?, different]

/-! ## Generated declarations and exact typing -/

@[simp]
theorem operationSpecs_names (signature : Signature) :
    signature.operationSpecs.map DeclSpec.name =
      [signature.names.languageType, signature.names.routeType,
        signature.names.identity, signature.names.compose] ++
      List.ofFn (fun index =>
        signature.languageName (signature.languageIndex index)) ++
      List.ofFn signature.routeName := by
  simp [operationSpecs, coreSpecs, languageSpec, routeSpec, Function.comp_def]

theorem languageSpec_mem (signature : Signature)
    (language : signature.Language) :
    signature.languageSpec language ∈ signature.operationSpecs := by
  simp only [operationSpecs, List.mem_append]
  exact Or.inl (Or.inr (List.mem_ofFn.mpr
    ⟨signature.languageIndex.symm language,
      congrArg signature.languageSpec
        (signature.languageIndex.apply_symm_apply language)⟩))

theorem routeSpec_mem (signature : Signature) (route : signature.Route) :
    signature.routeSpec route ∈ signature.operationSpecs := by
  simp [operationSpecs, List.mem_ofFn]

theorem operationSpecs_value_none (signature : Signature)
    {specification : DeclSpec}
    (membership : specification ∈ signature.operationSpecs) :
    specification.value? = none := by
  have everySpecification :
      ∀ entry ∈ signature.operationSpecs, entry.value? = none := by
    simp [operationSpecs, coreSpecs, languageSpec, routeSpec]
    intro entry generated
    rcases generated with ⟨language, rfl⟩ | ⟨route, rfl⟩ <;> rfl
  exact everySpecification specification membership

theorem operationSpecs_signatureWellFormed (signature : Signature) :
    SignatureWellFormed signature.operationSpecs where
  noShadowing := by
    simpa only [operationSpecs_names] using signature.declaredNamesNodup
  obligations := by
    constructor
    · intro specification membership value valueEquation
      rw [signature.operationSpecs_value_none membership] at valueEquation
      simp at valueEquation
    · intro specification membership value valueEquation
      rw [signature.operationSpecs_value_none membership] at valueEquation
      simp at valueEquation

@[simp]
theorem typeOf_languageType (signature : Signature) :
    typeOf? signature.operationDeclEnv signature.names.languageType =
      some .u0 := by
  simpa [operationDeclEnv] using
    (typeOf_envOfSpecs_eq_of_mem_of_nodup
      (s := { name := signature.names.languageType, type := .u0 })
      signature.operationSpecs_signatureWellFormed.noShadowing
      (by simp [operationSpecs, coreSpecs]))

@[simp]
theorem typeOf_routeType (signature : Signature) :
    typeOf? signature.operationDeclEnv signature.names.routeType =
      some signature.routeTypeFormer := by
  simpa [operationDeclEnv] using
    (typeOf_envOfSpecs_eq_of_mem_of_nodup
      (s := { name := signature.names.routeType, type := signature.routeTypeFormer })
      signature.operationSpecs_signatureWellFormed.noShadowing
      (by simp [operationSpecs, coreSpecs]))

@[simp]
theorem typeOf_identity (signature : Signature) :
    typeOf? signature.operationDeclEnv signature.names.identity =
      some signature.identityType := by
  simpa [operationDeclEnv] using
    (typeOf_envOfSpecs_eq_of_mem_of_nodup
      (s := { name := signature.names.identity, type := signature.identityType })
      signature.operationSpecs_signatureWellFormed.noShadowing
      (by simp [operationSpecs, coreSpecs]))

@[simp]
theorem typeOf_compose (signature : Signature) :
    typeOf? signature.operationDeclEnv signature.names.compose =
      some signature.composeType := by
  simpa [operationDeclEnv] using
    (typeOf_envOfSpecs_eq_of_mem_of_nodup
      (s := { name := signature.names.compose, type := signature.composeType })
      signature.operationSpecs_signatureWellFormed.noShadowing
      (by simp [operationSpecs, coreSpecs]))

@[simp]
theorem typeOf_languageName (signature : Signature)
    (language : signature.Language) :
    typeOf? signature.operationDeclEnv (signature.languageName language) =
      some signature.languageType := by
  simpa [operationDeclEnv, languageSpec] using
    typeOf_envOfSpecs_eq_of_mem_of_nodup
      signature.operationSpecs_signatureWellFormed.noShadowing
      (signature.languageSpec_mem language)

@[simp]
theorem typeOf_routeName (signature : Signature) (route : signature.Route) :
    typeOf? signature.operationDeclEnv (signature.routeName route) =
      some (signature.routeType
        (signature.languageTerm (signature.source route))
        (signature.languageTerm (signature.target route))) := by
  simpa [operationDeclEnv, routeSpec] using
    typeOf_envOfSpecs_eq_of_mem_of_nodup
      signature.operationSpecs_signatureWellFormed.noShadowing
      (signature.routeSpec_mem route)

theorem hasType_languageTerm (signature : Signature)
    (language : signature.Language) :
    HasTypeDecl signature.operationDeclEnv .nil
      (signature.languageTerm language) signature.languageType :=
  hasType_const_from_lookup
    (E := signature.operationDeclEnv) (Γ := .nil)
    (c := signature.languageName language) (A0 := signature.languageType)
    (signature.typeOf_languageName language)

theorem hasType_identityTerm (signature : Signature)
    (language : signature.Language) :
    HasTypeDecl signature.operationDeclEnv .nil
      (signature.identityTerm language)
      (signature.routeType (signature.languageTerm language)
        (signature.languageTerm language)) := by
  unfold identityTerm
  simpa [identityType, routeType, languageType, inst0, subst, rename,
    liftRen] using
    (HasTypeDecl.app_elim
      (hasType_const_from_lookup (E := signature.operationDeclEnv)
        (Γ := .nil) (c := signature.names.identity)
        (A0 := signature.identityType) signature.typeOf_identity)
      (signature.hasType_languageTerm language))

theorem hasType_routeTerm (signature : Signature) (route : signature.Route) :
    HasTypeDecl signature.operationDeclEnv .nil
      (signature.routeTerm route)
      (signature.routeType
        (signature.languageTerm (signature.source route))
        (signature.languageTerm (signature.target route))) :=
  hasType_const_from_lookup
    (E := signature.operationDeclEnv) (Γ := .nil)
    (c := signature.routeName route)
    (A0 := signature.routeType
      (signature.languageTerm (signature.source route))
      (signature.languageTerm (signature.target route)))
    (signature.typeOf_routeName route)

private def instantiatePiCodomain (type argument : ScopedTerm n) : ScopedTerm n :=
  match type with
  | .pi _ codomain => inst0 argument codomain
  | other => other

private theorem instantiatePiCodomain_composeType (signature : Signature)
    (first middle last : signature.Language) :
    instantiatePiCodomain
        (instantiatePiCodomain
          (instantiatePiCodomain signature.composeType
            (signature.languageTerm first))
          (signature.languageTerm middle))
        (signature.languageTerm last) =
      .pi
        (signature.routeType (signature.languageTerm first)
          (signature.languageTerm middle))
        (.pi
          (liftClosed (signature.routeType (signature.languageTerm middle)
            (signature.languageTerm last)))
          (liftClosed (signature.routeType (signature.languageTerm first)
            (signature.languageTerm last)))) := by
  rfl

theorem hasType_composeTerm (signature : Signature)
    (first middle last : signature.Language)
    (earlier later : ScopedTerm 0)
    (earlierTyped : HasTypeDecl signature.operationDeclEnv .nil earlier
      (signature.routeType (signature.languageTerm first)
        (signature.languageTerm middle)))
    (laterTyped : HasTypeDecl signature.operationDeclEnv .nil later
      (signature.routeType (signature.languageTerm middle)
        (signature.languageTerm last))) :
    HasTypeDecl signature.operationDeclEnv .nil
      (signature.composeTerm first middle last earlier later)
      (signature.routeType (signature.languageTerm first)
        (signature.languageTerm last)) := by
  let firstTerm : ScopedTerm 0 := signature.languageTerm first
  let middleTerm : ScopedTerm 0 := signature.languageTerm middle
  let lastTerm : ScopedTerm 0 := signature.languageTerm last
  have composeTyped : HasTypeDecl signature.operationDeclEnv .nil
      (.const signature.names.compose) signature.composeType :=
    hasType_const_from_lookup
      (E := signature.operationDeclEnv) (Γ := .nil)
      (c := signature.names.compose) (A0 := signature.composeType)
      signature.typeOf_compose
  have languagesApplied :=
    HasTypeDecl.app_elim
      (HasTypeDecl.app_elim
        (HasTypeDecl.app_elim composeTyped
          (signature.hasType_languageTerm first))
        (signature.hasType_languageTerm middle))
      (signature.hasType_languageTerm last)
  have languagesApplied' : HasTypeDecl signature.operationDeclEnv .nil
      (.app
        (.app
          (.app (.const signature.names.compose) firstTerm)
          middleTerm)
        lastTerm)
      (.pi (signature.routeType firstTerm middleTerm)
        (.pi (liftClosed (signature.routeType middleTerm lastTerm))
          (liftClosed (signature.routeType firstTerm lastTerm)))) := by
    change HasTypeDecl signature.operationDeclEnv .nil
      (.app
        (.app
          (.app (.const signature.names.compose)
            (signature.languageTerm first))
          (signature.languageTerm middle))
        (signature.languageTerm last))
      (instantiatePiCodomain
        (instantiatePiCodomain
          (instantiatePiCodomain signature.composeType
            (signature.languageTerm first))
          (signature.languageTerm middle))
        (signature.languageTerm last)) at languagesApplied
    rw [instantiatePiCodomain_composeType] at languagesApplied
    simpa [firstTerm, middleTerm, lastTerm] using languagesApplied
  have earlierApplied := HasTypeDecl.app_elim languagesApplied' earlierTyped
  have laterApplied := HasTypeDecl.app_elim earlierApplied laterTyped
  simpa [composeTerm, firstTerm, middleTerm, lastTerm, inst0, subst,
    subst_liftClosed, liftClosed_zero] using laterApplied

/-- Every generated route program has its exact dependent route type. -/
theorem encodeProgram_typed (signature : Signature)
    {source target : signature.Language}
    (program : signature.Program source target) :
    HasTypeDecl signature.operationDeclEnv .nil
      (signature.encodeProgram program)
      (signature.routeType (signature.languageTerm source)
        (signature.languageTerm target)) := by
  induction program with
  | nil => exact signature.hasType_identityTerm source
  | cons prior generator inductionHypothesis =>
      cases generator with
      | named route =>
          exact signature.hasType_composeTerm source
            (signature.source route) (signature.target route)
            (signature.encodeProgram prior) (signature.routeTerm route)
            inductionHypothesis (signature.hasType_routeTerm route)

/-- The finite syntax recognizer accepts only well-typed route programs. -/
theorem decodeProgram_typed (signature : Signature)
    (term : ScopedTerm 0) (decoded : signature.DecodedProgram)
    (accepted : signature.decodeProgram? term = some decoded) :
    HasTypeDecl signature.operationDeclEnv .nil term
      (signature.routeType (signature.languageTerm decoded.source)
        (signature.languageTerm decoded.target)) := by
  fun_induction signature.decodeProgram? term generalizing decoded with
  | case1 languageTerm =>
      cases decodedLanguage : signature.decodeLanguageTerm? languageTerm with
      | none => simp [decodedLanguage] at accepted
      | some language =>
          have languageTermEq :=
            signature.decodeLanguageTerm_eq_some decodedLanguage
          simp [decodedLanguage] at accepted
          subst languageTerm
          subst decoded
          exact signature.hasType_identityTerm language
  | case2 _ _ _ => simp at accepted
  | case3 name =>
      cases routeDecoded : signature.decodeRouteName? name with
      | none => simp [routeDecoded] at accepted
      | some route =>
          have nameEq : name = signature.routeName route :=
            (decodeIndex_eq_some signature.routeName name route routeDecoded).symm
          subst name
          simp at accepted
          subst decoded
          exact signature.hasType_routeTerm route
  | case4 firstTerm middleTerm lastTerm earlierTerm laterTerm
      first middle last earlier later laterDecoded earlierDecoded
      lastDecoded middleDecoded firstDecoded earlierIH laterIH =>
      have firstTermEq := signature.decodeLanguageTerm_eq_some firstDecoded
      have middleTermEq := signature.decodeLanguageTerm_eq_some middleDecoded
      have lastTermEq := signature.decodeLanguageTerm_eq_some lastDecoded
      subst firstTerm
      subst middleTerm
      subst lastTerm
      have earlierTyped := earlierIH earlier earlierDecoded
      have laterTyped := laterIH later laterDecoded
      unfold composeDecoded? at accepted
      split_ifs at accepted with earlierSource earlierTarget laterSource laterTarget
      · simp [earlierSource, earlierTarget] at earlierTyped
        simp [laterSource, laterTarget] at laterTyped
        cases accepted
        exact signature.hasType_composeTerm first middle last
          earlierTerm laterTerm earlierTyped laterTyped
  | case5 _ _ _ _ _ _ _ _ => simp at accepted
  | case6 _ _ _ _ _ _ _ => simp at accepted
  | case7 _ _ _ _ => simp at accepted

/-- A closed two-sort term accepted by an independently generated finite route
signature. -/
structure RecognizedOperation (signature : Signature) where
  term : ScopedTerm 0
  decoded : signature.DecodedProgram
  recognized : signature.decodeProgram? term = some decoded

namespace RecognizedOperation

theorem wellTyped {signature : Signature}
    (operation : signature.RecognizedOperation) :
    HasTypeDecl signature.operationDeclEnv .nil operation.term
      (signature.routeType
        (signature.languageTerm operation.decoded.source)
        (signature.languageTerm operation.decoded.target)) :=
  signature.decodeProgram_typed operation.term operation.decoded
    operation.recognized

def structuralRoute {signature : Signature}
    (operation : signature.RecognizedOperation) :
    signature.presentation operation.decoded.source ⟶
      signature.presentation operation.decoded.target :=
  signature.structuralInterpretation.map operation.decoded.program

end RecognizedOperation


/-! ## Canonical spelling and the exact operation quotient -/

universe uTarget


variable (signature : Signature)

/-! ## The exact syntax quotient -/

/-- Two recognized terms present the same operation exactly when their
decoder outputs the same endpoint-indexed free path. -/
def SameProgram (first second : signature.RecognizedOperation) : Prop :=
  first.decoded = second.decoded

theorem sameProgram_refl (operation : signature.RecognizedOperation) :
    SameProgram signature operation operation :=
  rfl

theorem sameProgram_symm {first second : signature.RecognizedOperation}
    (same : SameProgram signature first second) :
    SameProgram signature second first :=
  same.symm

theorem sameProgram_trans {first second third : signature.RecognizedOperation}
    (firstSecond : SameProgram signature first second)
    (secondThird : SameProgram signature second third) :
    SameProgram signature first third :=
  firstSecond.trans secondThird

/-- The spelling quotient induced by exact decoded-program equality. -/
def recognizedSetoid : Setoid signature.RecognizedOperation where
  r := SameProgram signature
  iseqv :=
    { refl := sameProgram_refl signature
      symm := sameProgram_symm signature
      trans := sameProgram_trans signature }

abbrev OperationQuotient := Quotient (recognizedSetoid signature)

/-- The canonical spelling of one decoded free program is itself recognized. -/
def canonical (decoded : signature.DecodedProgram) :
    signature.RecognizedOperation := by
  rcases decoded with ⟨source, target, program⟩
  exact
    { term := signature.encodeProgram program
      decoded := ⟨source, target, program⟩
      recognized := signature.decodeProgram_encodeProgram program }

@[simp] theorem canonical_term (decoded : signature.DecodedProgram) :
    (canonical signature decoded).term =
      signature.encodeProgram decoded.program := by
  cases decoded
  rfl

@[simp] theorem canonical_decoded (decoded : signature.DecodedProgram) :
    (canonical signature decoded).decoded = decoded := by
  cases decoded
  rfl

/-- Forget only the surface spelling of a recognized term. -/
def quotientToDecoded :
    OperationQuotient signature → signature.DecodedProgram :=
  Quotient.lift (fun operation => operation.decoded) (by
    intro first second same
    exact same)

/-- Select the canonical surface spelling of a decoded program. -/
def decodedToQuotient (decoded : signature.DecodedProgram) :
    OperationQuotient signature :=
  Quotient.mk (recognizedSetoid signature) (canonical signature decoded)

/-- Recognized operation syntax, modulo exact decoded-program equality,
is precisely the endpoint-indexed free path language. -/
def operationQuotientEquiv :
    OperationQuotient signature ≃ signature.DecodedProgram where
  toFun := quotientToDecoded signature
  invFun := decodedToQuotient signature
  left_inv quotient := by
    refine Quotient.inductionOn quotient ?_
    intro operation
    apply Quotient.sound
    exact canonical_decoded signature operation.decoded
  right_inv decoded := canonical_decoded signature decoded

/-! ## Canonicalization and strongest true reflection -/

/-- Normalize a recognized raw term to the canonical spelling of the exact
free path recovered by the independent decoder. -/
def normalize? (term : ScopedTerm 0) : Option (ScopedTerm 0) :=
  (signature.decodeProgram? term).map fun decoded =>
    signature.encodeProgram decoded.program

@[simp] theorem normalize_encode {source target : signature.Language}
    (program : signature.Program source target) :
    normalize? signature (signature.encodeProgram program) =
      some (signature.encodeProgram program) := by
  simp [normalize?]

theorem normalize_of_decode (term : ScopedTerm 0)
    (decoded : signature.DecodedProgram)
    (accepted : signature.decodeProgram? term = some decoded) :
    normalize? signature term =
      some (signature.encodeProgram decoded.program) := by
  simp [normalize?, accepted]

/-- Normalization preserves the exact endpoint-indexed path recovered by the
independent decoder. -/
theorem normalize_preserves_decode (term : ScopedTerm 0)
    (decoded : signature.DecodedProgram)
    (accepted : signature.decodeProgram? term = some decoded) :
    signature.decodeProgram? (signature.encodeProgram decoded.program) =
      some decoded := by
  rcases decoded with ⟨source, target, program⟩
  exact signature.decodeProgram_encodeProgram program

/-- The canonical result of normalization is independently well typed at the
same recovered endpoints as the authored spelling. -/
theorem normalize_preserves_typing (term : ScopedTerm 0)
    (decoded : signature.DecodedProgram)
    (_accepted : signature.decodeProgram? term = some decoded) :
    Mettapedia.TypeTheory.Calculi.TwoSortPiSigmaId.DeclarationSemantics.HasTypeDecl
      signature.operationDeclEnv .nil
      (signature.encodeProgram decoded.program)
      (signature.routeType
        (signature.languageTerm decoded.source)
        (signature.languageTerm decoded.target)) := by
  rcases decoded with ⟨source, target, program⟩
  exact signature.encodeProgram_typed program

/-- Once a term has been normalized, applying normalization again is inert. -/
theorem normalize_idempotent_of_decode (term : ScopedTerm 0)
    (decoded : signature.DecodedProgram)
    (accepted : signature.decodeProgram? term = some decoded) :
    normalize? signature (signature.encodeProgram decoded.program) =
      normalize? signature term := by
  rw [normalize_of_decode signature term decoded accepted]
  exact normalize_encode signature decoded.program

/-- Canonical encoding is injective at fixed intrinsic endpoints. -/
theorem encodeProgram_injective {source target : signature.Language} :
    Function.Injective
      (@Signature.encodeProgram signature source target) := by
  intro first second equal
  have decodedEqual := congrArg signature.decodeProgram? equal
  simp only [signature.decodeProgram_encodeProgram] at decodedEqual
  have structuresEqual := Option.some.inj decodedEqual
  cases structuresEqual
  rfl

/-- The independent decoder recognizes an explicitly written composition of
two canonical route programs.  Unlike `decodeProgram_encodeProgram`, this
lemma deliberately retains the authored composition node. -/
theorem decodeProgram_compose_encode
    {first middle last : signature.Language}
    (earlier : signature.Program first middle)
    (later : signature.Program middle last) :
    signature.decodeProgram?
        (signature.composeTerm first middle last
          (signature.encodeProgram earlier)
          (signature.encodeProgram later)) =
      some
        { source := first
          target := last
          program := Quiver.Path.comp earlier later } := by
  simp only [
    Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.composeTerm,
    Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature.Signature.decodeProgram?]
  simp [signature.decodeProgram_encodeProgram,
    signature.composeDecoded_programs]

/-! ## Universal factorization -/

/-- An interpretation of surface operations is admissible at the categorical
waist exactly when it is insensitive to surface spellings with the same
decoded endpoint-indexed path. -/
structure InvariantInterpretation (Target : Type uTarget) where
  apply : signature.RecognizedOperation → Target
  respects : ∀ first second,
    SameProgram signature first second → apply first = apply second

namespace InvariantInterpretation

variable {signature : Signature} {Target : Type uTarget}

/-- The induced interpretation of decoded free programs. -/
def factor (interpretation : InvariantInterpretation signature Target) :
    signature.DecodedProgram → Target :=
  fun decoded => interpretation.apply (canonical signature decoded)

/-- The factor agrees with the original interpretation on every recognized
surface spelling. -/
theorem factor_agrees
    (interpretation : InvariantInterpretation signature Target)
    (operation : signature.RecognizedOperation) :
    interpretation.factor operation.decoded = interpretation.apply operation :=
  interpretation.respects _ _
    (canonical_decoded signature operation.decoded)

/-- No other map from decoded free programs can have the same action on all
recognized spellings. -/
theorem factor_unique
    (interpretation : InvariantInterpretation signature Target)
    (candidate : signature.DecodedProgram → Target)
    (agrees : ∀ operation : signature.RecognizedOperation,
      candidate operation.decoded = interpretation.apply operation) :
    candidate = interpretation.factor := by
  funext decoded
  have canonicalAgreement := agrees (canonical signature decoded)
  simpa [factor] using canonicalAgreement

/-- Every spelling-invariant interpretation factors uniquely through the
endpoint-indexed free program language. -/
theorem existsUnique_factor
    (interpretation : InvariantInterpretation signature Target) :
    ∃! factor : signature.DecodedProgram → Target,
      ∀ operation : signature.RecognizedOperation,
        factor operation.decoded = interpretation.apply operation := by
  exact ⟨interpretation.factor, interpretation.factor_agrees,
    fun candidate agrees => interpretation.factor_unique candidate agrees⟩

end InvariantInterpretation

end Signature

end Mettapedia.GSLT.LanguageDef.FiniteLanguageOperationSignature
