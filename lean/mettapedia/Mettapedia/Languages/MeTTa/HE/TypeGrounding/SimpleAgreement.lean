import Mettapedia.Languages.MeTTa.HE.TypeGrounding.Fragment
import Mettapedia.Logic.HOL.Syntax.ClosedElaboration
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Conformance
import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.Normal

/-!
# Agreement of HE's exact type relation with simply typed HOL

On saturated expressions over static declarations, HE's exact type relation
(`Spec.Type.Presentation.Exact.RuntimeTypePackagesRel`) and Church-style HOL
elaboration (`NamedElaboration.infer`) agree:

* `hol_iff_exact`: HOL elaborates the translation of `e` at the image of a
  static type `T` exactly when HE's exact relation assigns `e` the single
  candidate `T` and no subatom of `e` falls back to `%Undefined%`.

The fallback condition is part of the agreement, not a convenience.  HE's
specified relation assigns an ill-typed application the gradual candidate
`%Undefined%`, which is consistent with every expected type, so an enclosing
application can still be typed.  HOL rejects the enclosing term.  The
boundary witness is `TypeGrounding.SpecBoundary`.

Supporting results: on the fragment the exact candidate list of every atom
is a singleton, either a static type or `%Undefined%` (`exact_shape`), and
a HOL-typed expression has exactly one candidate (`exact_unique_of_holTyped`).
-/

namespace Mettapedia.Languages.MeTTa.HE.TypeGrounding

open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.HOL.NamedElaboration
open Spec.Type
open Spec.Type.Conformance
open Spec.Type.Presentation
open Spec.Type.Presentation.Exact

/-! ## HOL elaboration of declared constants and saturated applications -/

theorem holTyped_iff_elaborates (space : Space) (expression type : Atom) :
    HOLTyped space expression type ↔
      Elaborates (spaceSignature space) (toNamed expression) (toTy type) := Iff.rfl

/-- `applySpine` is the left fold of curried application. -/
theorem applySpine_eq_foldl :
    ∀ (function : HOLTerm) (arguments : List Atom),
      applySpine function arguments =
        arguments.foldl (fun accumulated argument =>
          .app accumulated (toNamed argument)) function
  | _, [] => rfl
  | function, argument :: arguments => by
      rw [applySpine, applySpine_eq_foldl]
      rfl

/-- A constant of a declaration space elaborates exactly at the image of its
declared type. -/
theorem elaborates_declared_iff {space : Space} {constant : Atom} {type : Ty Atom} :
    Elaborates (spaceSignature space) (.constant constant) type ↔
      ∃ declared, declaredType? space constant = some declared ∧
        type = toTy declared := by
  rw [elaborates_constant_iff]
  constructor
  · rintro ⟨holConstant, lookup⟩
    cases declaredLookup : declaredType? space constant with
    | none =>
        rw [spaceSignature_of_undeclared declaredLookup] at lookup
        cases lookup
    | some declared =>
        rw [spaceSignature_of_declared declaredLookup] at lookup
        simp only [Option.some.injEq] at lookup
        exact ⟨declared, rfl, (congrArg Sigma.fst lookup).symm⟩
  · rintro ⟨declared, lookup, rfl⟩
    exact ⟨_, spaceSignature_of_declared lookup⟩

/-- A saturated application of a declared arrow elaborates exactly at the
image of the arrow's return type, when each argument elaborates at the image
of its declared argument type. -/
theorem elaborates_application_iff {space : Space} {name : String}
    {arguments argumentTypes : List Atom} {type returnType : Atom}
    {result : Ty Atom}
    (declared : declaredType? space (.symbol name) = some type)
    (function : FunctionTypeRel type argumentTypes returnType)
    (nonempty : argumentTypes ≠ [])
    (lengths : arguments.length = argumentTypes.length) :
    Elaborates (spaceSignature space)
        (toNamed (.expression (.symbol name :: arguments))) result ↔
      result = toTy returnType ∧
        List.Forall₂ (fun argument argumentType =>
          Elaborates (spaceSignature space) (toNamed argument) (toTy argumentType))
          arguments argumentTypes := by
  simp only [toNamed]
  rw [applySpine_eq_foldl, elaborates_foldl_app_iff]
  constructor
  · rintro ⟨holArguments, functionElaborates, all⟩
    obtain ⟨declared', lookup, typeEq⟩ := elaborates_declared_iff.mp functionElaborates
    rw [declared] at lookup
    cases lookup
    rw [toTy_of_functionType function nonempty, spineTy_eq_foldr] at typeEq
    have holLength : holArguments.length = (argumentTypes.map toTy).length := by
      rw [List.length_map, ← lengths]
      exact all.length_eq.symm
    obtain ⟨holEq, resultEq⟩ := foldr_arr_injective holLength typeEq
    subst holEq
    exact ⟨resultEq, List.forall₂_map_right_iff.mp all⟩
  · rintro ⟨rfl, all⟩
    refine ⟨argumentTypes.map toTy, ?_, List.forall₂_map_right_iff.mpr all⟩
    rw [← spineTy_eq_foldr, ← toTy_of_functionType function nonempty]
    exact elaborates_declared_iff.mpr ⟨type, declared, rfl⟩

/-! ## Variable-free and `%Undefined%`-free atoms -/

theorem typeVarsList_eq_nil_iff :
    ∀ atoms : List Atom,
      TypeSubst.typeVarsList atoms = [] ↔ ∀ atom ∈ atoms, TypeSubst.typeVars atom = []
  | [] => by simp [TypeSubst.typeVarsList]
  | atom :: atoms => by
      simp [TypeSubst.typeVarsList, typeVarsList_eq_nil_iff atoms]

/-- Variable-free atoms are fixed by every renaming of type variables. -/
theorem renameTypeVars_of_typeVars_nil (rename : String → String) (atom : Atom)
    (ground : TypeSubst.typeVars atom = []) :
    Spec.Type.RuntimeRefinement.renameTypeVars rename atom = atom := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      TypeSubst.typeVarsList atoms = [] →
        atoms.map (Spec.Type.RuntimeRefinement.renameTypeVars rename) = atoms) with
  | symbol name => simp [Spec.Type.RuntimeRefinement.renameTypeVars]
  | var name => simp [TypeSubst.typeVars] at ground
  | grounded value => simp [Spec.Type.RuntimeRefinement.renameTypeVars]
  | expression atoms ih =>
      simp only [TypeSubst.typeVars] at ground
      simp [Spec.Type.RuntimeRefinement.renameTypeVars, ih ground]
  | nil => rfl
  | cons head tail headIH tailIH =>
      rename_i ground
      simp only [TypeSubst.typeVarsList, List.append_eq_nil_iff] at ground
      simp [headIH ground.1, tailIH ground.2]

/-- Variable-free atoms are fixed by every finite type substitution. -/
theorem typeSubst_apply_of_typeVars_nil (substitution : TypeSubst) {atom : Atom}
    (ground : TypeSubst.typeVars atom = []) : substitution.apply atom = atom :=
  TypeSubst.apply_eq_self_of_variables_not_keys substitution atom
    (by intro name member; simp [ground] at member)

/-- A static type is variable-free. -/
theorem StaticType.typeVars_nil {type : Atom} (static : StaticType type) :
    TypeSubst.typeVars type = [] := by
  induction static with
  | base _ _ _ ground => exact ground
  | arrow function _ _ _ _ argumentIH returnIH =>
      rw [FunctionTypeRel] at function
      subst function
      simp only [TypeSubst.typeVars]
      rw [typeVarsList_eq_nil_iff]
      intro atom member
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
      rcases member with rfl | member | rfl
      · rfl
      · exact argumentIH atom member
      · exact returnIH

/-- A static type does not mention `%Undefined%`. -/
theorem StaticType.undefinedFree {type : Atom} (static : StaticType type) :
    UndefinedFree type := by
  induction static with
  | base _ _ free _ => exact free
  | arrow function _ _ _ _ argumentIH returnIH =>
      rw [FunctionTypeRel] at function
      subst function
      intro occurs
      rcases occurs.expression_cases with equal | ⟨child, member, inner⟩
      · cases equal
      · simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at member
        rcases member with rfl | member | rfl
        · have equal := inner.symbol_eq
          simp [Atom.undefinedType] at equal
        · exact argumentIH child member inner
        · exact returnIH inner

/-! ## Alpha variants and choices of variable-free candidates -/

theorem alphaVariant_eq_of_ground {avoid : List String} {source target : Atom}
    (variant : TypeCandidateAlphaVariantRel avoid source target)
    (ground : TypeSubst.typeVars source = []) : target = source := by
  obtain ⟨rename, _, presentation, _⟩ := variant
  rw [presentation, renameTypeVars_of_typeVars_nil rename source ground]

theorem alphaVariant_self_of_ground (avoid : List String) {source : Atom}
    (ground : TypeSubst.typeVars source = []) :
    TypeCandidateAlphaVariantRel avoid source source :=
  ⟨id, Function.injective_id,
    (renameTypeVars_of_typeVars_nil id source ground).symm,
    by intro name member; simp [ground] at member⟩

theorem argumentAlphaVariants_eq_of_ground :
    ∀ {avoid : List String} {sources targets : List Atom},
      ArgumentAlphaVariantsRel avoid sources targets →
      (∀ source ∈ sources, TypeSubst.typeVars source = []) → targets = sources
  | _, _, _, .nil _, _ => rfl
  | _, _, _, .cons head tail, ground => by
      rw [alphaVariant_eq_of_ground head (ground _ (by simp)),
        argumentAlphaVariants_eq_of_ground tail
          (fun source member => ground source (List.mem_cons_of_mem _ member))]

theorem argumentAlphaVariants_self_of_ground :
    ∀ (avoid : List String) (sources : List Atom),
      (∀ source ∈ sources, TypeSubst.typeVars source = []) →
      ArgumentAlphaVariantsRel avoid sources sources
  | avoid, [], _ => .nil avoid
  | avoid, source :: sources, ground =>
      .cons (alphaVariant_self_of_ground avoid (ground source (by simp)))
        (argumentAlphaVariants_self_of_ground _ sources
          (fun source member => ground source (List.mem_cons_of_mem _ member)))

theorem operatorAlphaVariants_eq_of_ground :
    ∀ {avoid : List String} {sources targets : List Atom},
      OperatorAlphaVariantsRel avoid sources targets →
      (∀ source ∈ sources, TypeSubst.typeVars source = []) → targets = sources
  | _, _, _, .nil, _ => rfl
  | _, _, _, .cons head tail, ground => by
      rw [alphaVariant_eq_of_ground head (ground _ (by simp)),
        operatorAlphaVariants_eq_of_ground tail
          (fun source member => ground source (List.mem_cons_of_mem _ member))]

theorem operatorAlphaVariants_self_of_ground (avoid : List String) :
    ∀ (sources : List Atom),
      (∀ source ∈ sources, TypeSubst.typeVars source = []) →
      OperatorAlphaVariantsRel avoid sources sources
  | [], _ => .nil
  | source :: sources, ground =>
      .cons (alphaVariant_self_of_ground avoid (ground source (by simp)))
        (operatorAlphaVariants_self_of_ground avoid sources
          (fun source member => ground source (List.mem_cons_of_mem _ member)))

/-- One candidate per argument gives exactly one ordered choice. -/
theorem orderedCartesian_singletons :
    ∀ types : List Atom, orderedCartesian (types.map fun type => [type]) = [types]
  | [] => rfl
  | type :: types => by
      simp [orderedCartesian, orderedCartesian_singletons types]

theorem scopesSeparated_of_ground {choices : List (List Atom)} {operators : List Atom}
    (ground : ∀ operator ∈ operators, TypeSubst.typeVars operator = []) :
    ApplicationPackageScopesSeparated choices operators := by
  apply ApplicationPackageScopesSeparated.mk
  intro _ _ operator member name occurs
  simp [ground operator member] at occurs

/-- A one-operator, one-choice application scan has one outcome. -/
theorem applicationPackageMatrix_single_iff {actualTypes : List Atom}
    {operatorType : Atom} {results : List TypePackage} :
    ApplicationPackageMatrixRel [actualTypes] [operatorType] results ↔
      ∃ outcome, ApplicationPackageOutcomeRel actualTypes operatorType outcome ∧
        results = outcome.toList := by
  constructor
  · rintro ⟨rows, rowsRel, flat⟩
    cases rowsRel with
    | cons rowRel rest =>
        cases rest
        obtain ⟨outcomes, outcomesRel, filtered⟩ := rowRel
        cases outcomesRel with
        | cons outcomeRel restOutcomes =>
            cases restOutcomes
            refine ⟨_, outcomeRel, ?_⟩
            rw [← flat, ← filtered]
            rename_i outcome
            cases outcome <;> rfl
  · rintro ⟨outcome, outcomeRel, rfl⟩
    refine ⟨[outcome.toList], .cons ⟨[outcome], .cons outcomeRel .nil, ?_⟩ .nil, by simp⟩
    cases outcome <;> rfl

/-! ## Matching static expected types -/

mutual

theorem reduced_ground_eq {substitution output : TypeSubst} {left right : Atom}
    (derivation : ReducedTypePresentationMatchRel substitution left right output)
    (leftGround : TypeSubst.typeVars left = [])
    (rightGround : TypeSubst.typeVars right = [])
    (leftFree : UndefinedFree left) (rightFree : UndefinedFree right) :
    left = right ∧ output = substitution :=
  match derivation with
  | .undefinedLeft _ _ => absurd .refl leftFree
  | .undefinedRight _ _ => absurd .refl rightFree
  | .expression children => by
      have lists := reducedList_ground_eq children
        (by simpa [TypeSubst.typeVars] using leftGround)
        (by simpa [TypeSubst.typeVars] using rightGround)
        (fun _ member => leftFree.of_child member)
        (fun _ member => rightFree.of_child member)
      exact ⟨by rw [lists.1], lists.2⟩
  | .ordinary _ _ shape leftApply rightApply applied => by
      rw [typeSubst_apply_of_typeVars_nil _ leftGround] at leftApply
      rw [typeSubst_apply_of_typeVars_nil _ rightGround] at rightApply
      subst leftApply rightApply
      cases applied with
      | identical => exact ⟨rfl, rfl⟩
      | bindLeft _ => simp [TypeSubst.typeVars] at leftGround
      | bindRight _ _ => simp [TypeSubst.typeVars] at rightGround
      | expression _ => exact shape.elim

theorem reducedList_ground_eq {substitution output : TypeSubst}
    {lefts rights : List Atom}
    (derivation : ReducedTypePresentationListMatchRel substitution lefts rights output)
    (leftGround : TypeSubst.typeVarsList lefts = [])
    (rightGround : TypeSubst.typeVarsList rights = [])
    (leftFree : ∀ atom ∈ lefts, UndefinedFree atom)
    (rightFree : ∀ atom ∈ rights, UndefinedFree atom) :
    lefts = rights ∧ output = substitution :=
  match derivation with
  | .nil _ => ⟨rfl, rfl⟩
  | .cons head tail => by
      simp only [TypeSubst.typeVarsList, List.append_eq_nil_iff] at leftGround rightGround
      have heads := reduced_ground_eq head leftGround.1 rightGround.1
        (leftFree _ (by simp)) (rightFree _ (by simp))
      have tails := reducedList_ground_eq tail leftGround.2 rightGround.2
        (fun atom member => leftFree atom (List.mem_cons_of_mem _ member))
        (fun atom member => rightFree atom (List.mem_cons_of_mem _ member))
      obtain ⟨rfl, rfl⟩ := heads
      obtain ⟨rfl, rfl⟩ := tails
      exact ⟨rfl, rfl⟩

end

/-- Every variable-free, `%Undefined%`-free atom matches itself without
extending the presentation. -/
theorem reduced_ground_refl (substitution : TypeSubst) (atom : Atom)
    (ground : TypeSubst.typeVars atom = []) (free : UndefinedFree atom) :
    ReducedTypePresentationMatchRel substitution atom atom substitution := by
  induction atom using Atom.rec (motive_2 := fun atoms =>
      TypeSubst.typeVarsList atoms = [] → (∀ atom ∈ atoms, UndefinedFree atom) →
        ReducedTypePresentationListMatchRel substitution atoms atoms substitution) with
  | symbol name =>
      exact .ordinary free.ne free.ne trivial
        (typeSubst_apply_of_typeVars_nil _ ground)
        (typeSubst_apply_of_typeVars_nil _ ground) (.identical _ _)
  | var name => simp [TypeSubst.typeVars] at ground
  | grounded value =>
      exact .ordinary free.ne free.ne trivial
        (typeSubst_apply_of_typeVars_nil _ ground)
        (typeSubst_apply_of_typeVars_nil _ ground) (.identical _ _)
  | expression atoms ih =>
      exact .expression (ih (by simpa [TypeSubst.typeVars] using ground)
        (fun _ member => free.of_child member))
  | nil => exact .nil _
  | cons head tail headIH tailIH =>
      rename_i ground free
      simp only [TypeSubst.typeVarsList, List.append_eq_nil_iff] at ground
      exact .cons (headIH ground.1 (free head (by simp)))
        (tailIH ground.2 (fun atom member => free atom (List.mem_cons_of_mem _ member)))

/-- Against a static expected type, a candidate that is static or the
gradual `%Undefined%` matches without changing the presentation, and a static
candidate must equal the expected type. -/
theorem corePlusR2_static {substitution output : TypeSubst} {expected actual : Atom}
    (expectedStatic : StaticType expected)
    (actualCases : actual = Atom.undefinedType ∨ StaticType actual)
    (derivation : CorePlusR2TypePresentationMatchRel substitution expected actual output) :
    output = substitution ∧ (actual = Atom.undefinedType ∨ expected = actual) := by
  cases derivation with
  | undefinedLeft => exact absurd rfl expectedStatic.ne_undefined
  | undefinedRight => exact ⟨rfl, Or.inl rfl⟩
  | atomLeft => exact absurd rfl expectedStatic.ne_atom
  | atomRight =>
      rcases actualCases with equal | actualStatic
      · simp [Atom.undefinedType, Atom.atomType] at equal
      · exact absurd rfl actualStatic.ne_atom
  | reduced _ actualNotUndefined _ _ reduced =>
      have actualStatic : StaticType actual := by
        rcases actualCases with equal | actualStatic
        · exact absurd equal actualNotUndefined
        · exact actualStatic
      obtain ⟨equal, unchanged⟩ := reduced_ground_eq reduced
        expectedStatic.typeVars_nil actualStatic.typeVars_nil
        expectedStatic.undefinedFree actualStatic.undefinedFree
      exact ⟨unchanged, Or.inr equal⟩

/-- The corresponding derivation exists. -/
theorem corePlusR2_static_exists (substitution : TypeSubst) {expected actual : Atom}
    (expectedStatic : StaticType expected)
    (accepted : actual = Atom.undefinedType ∨ expected = actual) :
    CorePlusR2TypePresentationMatchRel substitution expected actual substitution := by
  rcases accepted with rfl | rfl
  · exact .undefinedRight _ _
  · exact .reduced expectedStatic.ne_undefined expectedStatic.ne_undefined
      expectedStatic.ne_atom expectedStatic.ne_atom
      (reduced_ground_refl substitution expected expectedStatic.typeVars_nil
        expectedStatic.undefinedFree)

/-- An argument fold against static expected types leaves the presentation
unchanged; each candidate is either the expected type or `%Undefined%`. -/
theorem argumentList_static :
    ∀ {expecteds actuals : List Atom} {substitution output : TypeSubst},
      PresentationArgumentListMatchRel expecteds actuals substitution output →
      (∀ expected ∈ expecteds, StaticType expected) →
      (∀ actual ∈ actuals, actual = Atom.undefinedType ∨ StaticType actual) →
      output = substitution ∧
        List.Forall₂ (fun expected actual =>
          actual = Atom.undefinedType ∨ expected = actual) expecteds actuals
  | _, _, _, _, .nil _, _, _ => ⟨rfl, .nil⟩
  | _, _, _, _, .cons head tail, expectedStatic, actualCases => by
      obtain ⟨unchanged, accepted⟩ := corePlusR2_static
        (expectedStatic _ (by simp)) (actualCases _ (by simp)) head
      subst unchanged
      obtain ⟨tailUnchanged, tailAccepted⟩ := argumentList_static tail
        (fun expected member => expectedStatic expected (List.mem_cons_of_mem _ member))
        (fun actual member => actualCases actual (List.mem_cons_of_mem _ member))
      exact ⟨tailUnchanged, .cons accepted tailAccepted⟩

theorem argumentList_static_exists (substitution : TypeSubst) :
    ∀ {expecteds actuals : List Atom},
      (∀ expected ∈ expecteds, StaticType expected) →
      List.Forall₂ (fun expected actual =>
        actual = Atom.undefinedType ∨ expected = actual) expecteds actuals →
      PresentationArgumentListMatchRel expecteds actuals substitution substitution
  | _, _, _, .nil => .nil _
  | _, _, expectedStatic, .cons accepted rest =>
      .cons (corePlusR2_static_exists substitution (expectedStatic _ (by simp)) accepted)
        (argumentList_static_exists substitution
          (fun expected member => expectedStatic expected (List.mem_cons_of_mem _ member))
          rest)

/-! ## HE's exact relation on constants -/

/-- HE's exact candidate list for an atom, as observed presentations. -/
def ExactTypes (space : Space) (atom : Atom) (types : List Atom) : Prop :=
  ∃ packages, RuntimeTypePackagesRel space atom packages ∧ observedTypes packages = types

/-- No subatom of `atom` falls back to HE's gradual `%Undefined%`
candidate. -/
def NoUndefinedFallback (space : Space) (atom : Atom) : Prop :=
  ∀ sub, Subatom sub atom → ¬ExactTypes space sub [Atom.undefinedType]

theorem getAnnotatedTypes_of_declared_symbol {space : Space} {name : String}
    {type : Atom} (declared : declaredType? space (.symbol name) = some type) :
    getAnnotatedTypes space (.symbol name) = [type] := by
  simp only [declaredType?] at declared
  split at declared
  · next found listEq =>
      simp only [Option.some.injEq] at declared
      rw [listEq, declared]
  · simp at declared

theorem toNamed_of_declared {space : Space} {atom type : Atom}
    (declared : declaredType? space atom = some type) :
    toNamed atom = .constant atom := by
  cases atom with
  | symbol name => rfl
  | grounded value => rfl
  | var name => simp [declaredType?] at declared
  | expression atoms => simp [declaredType?] at declared

/-- HE's exact relation gives a declared constant its declared type. -/
theorem constant_packages {space : Space} {atom type : Atom}
    (declared : declaredType? space atom = some type) :
    RuntimeTypePackagesRel space atom [publishedPackage type] := by
  cases atom with
  | symbol name =>
      have annotated := getAnnotatedTypes_of_declared_symbol declared
      have rel := annotationTypesRel_getAnnotatedTypes (.symbol name) space.atoms
      have listEq : getAnnotatedTypes (Space.ofList space.atoms) (.symbol name) = [type] :=
        annotated
      rw [listEq] at rel
      simpa using RuntimeTypePackagesRel.symbolKnown rel (by simp)
  | grounded value =>
      simp only [declaredType?, Option.some.injEq] at declared
      subst declared
      exact .grounded ((intrinsicGroundedTypeRel_iff_getGroundedType value _).mpr rfl)
  | var name => simp [declaredType?] at declared
  | expression atoms => simp [declaredType?] at declared

/-- ...and nothing else. -/
theorem constant_packages_eq {space : Space} {atom type : Atom}
    (declared : declaredType? space atom = some type) {packages : List TypePackage}
    (derivation : RuntimeTypePackagesRel space atom packages) :
    packages = [publishedPackage type] := by
  cases atom with
  | symbol name =>
      have annotated := getAnnotatedTypes_of_declared_symbol declared
      cases derivation with
      | symbolKnown rel _ =>
          have listEq := annotationTypesRel_eq_getAnnotatedTypes rel
          change getAnnotatedTypes space (.symbol name) = _ at listEq
          rw [annotated] at listEq
          subst listEq
          rfl
      | symbolUndefined rel =>
          have listEq := annotationTypesRel_eq_getAnnotatedTypes rel
          change getAnnotatedTypes space (.symbol name) = [] at listEq
          rw [annotated] at listEq
          cases listEq
  | grounded value =>
      simp only [declaredType?, Option.some.injEq] at declared
      subst declared
      cases derivation with
      | grounded intrinsic =>
          rw [(intrinsicGroundedTypeRel_iff_getGroundedType _ _).mp intrinsic]
  | var name => simp [declaredType?] at declared
  | expression atoms => simp [declaredType?] at declared

/-- An expression that the space does not annotate has no direct
annotation in the exact relation. -/
theorem expression_annotations_nil {space : Space} {atoms : List Atom}
    (annotationFree : getAnnotatedTypes space (.expression atoms) = []) :
    AnnotationTypesRel (.expression atoms) space.atoms [] := by
  have rel := annotationTypesRel_getAnnotatedTypes (.expression atoms) space.atoms
  have listEq : getAnnotatedTypes (Space.ofList space.atoms) (.expression atoms) = [] :=
    annotationFree
  rwa [listEq] at rel

/-! ## HE's exact relation on saturated applications -/

/-- Construct HE's exact derivation of a saturated application whose
argument candidates are all accepted by the declared argument types. -/
theorem application_packages_success {space : Space}
    {name : String}
    {arguments argumentTypes actualTypes : List Atom}
    {packageLists : List (List TypePackage)} {type returnType : Atom}
    (notState : name ≠ "StateValue")
    (annotationFree : getAnnotatedTypes space (.expression (.symbol name :: arguments)) = [])
    (declared : declaredType? space (.symbol name) = some type)
    (static : StaticType type)
    (function : FunctionTypeRel type argumentTypes returnType)
    (argumentPackages : List.Forall₂ (RuntimeTypePackagesRel space) arguments packageLists)
    (observed : packageLists.map observedTypes = actualTypes.map (fun type => [type]))
    (ground : ∀ actual ∈ actualTypes, TypeSubst.typeVars actual = [])
    (accepted : List.Forall₂ (fun expected actual =>
      actual = Atom.undefinedType ∨ expected = actual) argumentTypes actualTypes) :
    RuntimeTypePackagesRel space (.expression (.symbol name :: arguments))
      [inferredPackage [] returnType] := by
  obtain ⟨_, argumentStatic, _, _⟩ := static.of_functionType function
  have typeGround := static.typeVars_nil
  apply RuntimeTypePackagesRel.expressionInferred
    (operatorPackages := [publishedPackage type])
    (rawArgumentLists := actualTypes.map (fun type => [type]))
    (rawOperators := [type])
    (freshArgumentChoices := [actualTypes])
    (freshOperators := [type])
    (fun _ => Or.inl (by simp [notState]))
    (expression_annotations_nil annotationFree)
    (constant_packages declared)
    argumentPackages observed rfl rfl
  · rw [orderedCartesian_singletons]
    exact .cons (argumentAlphaVariants_self_of_ground _ actualTypes ground) .nil
  · exact operatorAlphaVariants_self_of_ground _ [type] (by simp [typeGround])
  · exact scopesSeparated_of_ground (by simp [typeGround])
  · apply applicationPackageMatrix_single_iff.mpr
    refine ⟨some (inferredPackage [] returnType), .success ?_, rfl⟩
    exact ApplicationPackageSuccessRel.mk function
      (argumentList_static_exists [] argumentStatic accepted)
  · simp

/-- Construct HE's exact derivation of an application whose single operator
candidate accepts no choice of the argument candidates: the gradual
`%Undefined%` fallback. -/
theorem application_packages_failure {space : Space}
    {name : String}
    {arguments actualTypes : List Atom}
    {packageLists : List (List TypePackage)} {type : Atom}
    (notState : name ≠ "StateValue")
    (annotationFree : getAnnotatedTypes space (.expression (.symbol name :: arguments)) = [])
    (declared : declaredType? space (.symbol name) = some type)
    (typeGround : TypeSubst.typeVars type = [])
    (argumentPackages : List.Forall₂ (RuntimeTypePackagesRel space) arguments packageLists)
    (observed : packageLists.map observedTypes = actualTypes.map (fun type => [type]))
    (ground : ∀ actual ∈ actualTypes, TypeSubst.typeVars actual = [])
    (noSuccess : ∀ result, ¬ApplicationPackageSuccessRel actualTypes type result) :
    RuntimeTypePackagesRel space (.expression (.symbol name :: arguments))
      [publishedPackage Atom.undefinedType] := by
  apply RuntimeTypePackagesRel.expressionUndefined
    (operatorPackages := [publishedPackage type])
    (rawArgumentLists := actualTypes.map (fun type => [type]))
    (rawOperators := [type])
    (freshArgumentChoices := [actualTypes])
    (freshOperators := [type])
    (fun _ => Or.inl (by simp [notState]))
    (expression_annotations_nil annotationFree)
    (constant_packages declared)
    argumentPackages observed rfl rfl
  · rw [orderedCartesian_singletons]
    exact .cons (argumentAlphaVariants_self_of_ground _ actualTypes ground) .nil
  · exact operatorAlphaVariants_self_of_ground _ [type] (by simp [typeGround])
  · exact scopesSeparated_of_ground (by simp [typeGround])
  · exact applicationPackageMatrix_single_iff.mpr ⟨none, .failure noSuccess, rfl⟩

/-- Inversion of HE's exact relation at a saturated application whose
arguments have singleton, variable-free candidates.  Either every argument is
accepted and the declared return is emitted, or the scan fails and the
gradual `%Undefined%` candidate is emitted. -/
theorem application_packages_cases {space : Space}
    {name : String}
    {arguments argumentTypes : List Atom} {type returnType : Atom}
    (notState : name ≠ "StateValue")
    (annotationFree : getAnnotatedTypes space (.expression (.symbol name :: arguments)) = [])
    (declared : declaredType? space (.symbol name) = some type)
    (static : StaticType type)
    (function : FunctionTypeRel type argumentTypes returnType)
    {packages : List TypePackage}
    (derivation : RuntimeTypePackagesRel space
      (.expression (.symbol name :: arguments)) packages) :
    ∃ packageLists : List (List TypePackage),
      List.Forall₂ (RuntimeTypePackagesRel space) arguments packageLists ∧
      ∀ actualTypes : List Atom,
        packageLists.map observedTypes = actualTypes.map (fun type => [type]) →
        (∀ actual ∈ actualTypes, TypeSubst.typeVars actual = []) →
        (∃ substitution,
            PresentationArgumentListMatchRel argumentTypes actualTypes [] substitution ∧
              packages = [inferredPackage substitution returnType]) ∨
          ((∀ substitution,
              ¬PresentationArgumentListMatchRel argumentTypes actualTypes [] substitution) ∧
            packages = [publishedPackage Atom.undefinedType]) := by
  have typeGround := static.typeVars_nil
  cases derivation with
  | stateValue _ => exact absurd rfl notState
  | expressionKnown _ annotated nonempty =>
      have none := AnnotationTypesRel.unique annotated (expression_annotations_nil annotationFree)
      exact absurd none nonempty
  | expressionInferred _ _ operatorRel argumentRel observedArguments observedOperators
      avoidEq argumentVariants operatorVariants _ matrix nonempty =>
      refine ⟨_, argumentRel, ?_⟩
      intro actualTypes observed ground
      have operatorsEq := constant_packages_eq declared operatorRel
      subst operatorsEq
      rw [observed] at observedArguments
      subst observedArguments observedOperators
      rw [orderedCartesian_singletons] at argumentVariants
      cases argumentVariants with
      | cons variant rest =>
          cases rest
          have freshEq := argumentAlphaVariants_eq_of_ground variant ground
          subst freshEq
          have operatorEq := operatorAlphaVariants_eq_of_ground operatorVariants
            (by simp [publishedPackage, observedTypes,
              Spec.Type.Presentation.RuntimeTypePackage.published, typeGround])
          simp only [observedTypes, publishedPackage,
            Spec.Type.Presentation.RuntimeTypePackage.published, List.map_cons,
            List.map_nil] at operatorEq
          subst operatorEq
          obtain ⟨outcome, outcomeRel, resultsEq⟩ :=
            applicationPackageMatrix_single_iff.mp matrix
          cases outcomeRel with
          | success success =>
              cases success with
              | mk shape fold =>
                  obtain ⟨rfl, rfl⟩ := FunctionTypeRel.unique shape function
                  exact Or.inl ⟨_, fold, resultsEq⟩
          | failure _ =>
              simp at resultsEq
              exact absurd resultsEq nonempty
  | expressionUndefined _ _ operatorRel argumentRel observedArguments observedOperators
      avoidEq argumentVariants operatorVariants _ matrix =>
      refine ⟨_, argumentRel, ?_⟩
      intro actualTypes observed ground
      have operatorsEq := constant_packages_eq declared operatorRel
      subst operatorsEq
      rw [observed] at observedArguments
      subst observedArguments observedOperators
      rw [orderedCartesian_singletons] at argumentVariants
      cases argumentVariants with
      | cons variant rest =>
          cases rest
          have freshEq := argumentAlphaVariants_eq_of_ground variant ground
          subst freshEq
          have operatorEq := operatorAlphaVariants_eq_of_ground operatorVariants
            (by simp [publishedPackage, observedTypes,
              Spec.Type.Presentation.RuntimeTypePackage.published, typeGround])
          simp only [observedTypes, publishedPackage,
            Spec.Type.Presentation.RuntimeTypePackage.published, List.map_cons,
            List.map_nil] at operatorEq
          subst operatorEq
          obtain ⟨outcome, outcomeRel, resultsEq⟩ :=
            applicationPackageMatrix_single_iff.mp matrix
          cases outcomeRel with
          | success _ => simp at resultsEq
          | failure noSuccess =>
              refine Or.inr ⟨fun substitution fold => ?_, rfl⟩
              exact noSuccess _ (ApplicationPackageSuccessRel.mk function fold)

/-! ## Subatoms of saturated expressions -/

theorem SaturatedTerm.subatom {space : Space} {expression : Atom}
    (saturated : SaturatedTerm space expression) :
    ∀ {sub : Atom}, Subatom sub expression → SaturatedTerm space sub := by
  induction saturated with
  | constant declared static =>
      rename_i atom type
      intro sub occurs
      cases atom with
      | symbol name => rw [occurs.symbol_eq]; exact .constant declared static
      | grounded value => rw [occurs.grounded_eq]; exact .constant declared static
      | var name => simp [declaredType?] at declared
      | expression atoms => simp [declaredType?] at declared
  | application notState annotationFree declared static function lengths arguments argumentIH =>
      intro sub occurs
      rcases occurs.expression_cases with rfl | ⟨child, member, inner⟩
      · exact .application notState annotationFree declared static function lengths arguments
      · simp only [List.mem_cons] at member
        rcases member with rfl | member
        · rw [inner.symbol_eq]
          exact .constant declared static
        · exact argumentIH child member inner

/-- Every right element of a pointwise relation has a related left element. -/
theorem forall₂_right_mem {α β : Type} {relation : α → β → Prop} :
    ∀ {lefts : List α} {rights : List β}, List.Forall₂ relation lefts rights →
      ∀ right ∈ rights, ∃ left ∈ lefts, relation left right
  | _, _, .nil => by simp
  | _, _, .cons head tail => by
      intro right member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨_, by simp, head⟩
      · obtain ⟨left, leftMember, related⟩ := forall₂_right_mem tail right member
        exact ⟨left, List.mem_cons_of_mem _ leftMember, related⟩

/-- Weaken a pointwise relation using membership of the left elements. -/
theorem forall₂_imp_of_mem {α β : Type} {first second : α → β → Prop} :
    ∀ {lefts : List α} {rights : List β}, List.Forall₂ first lefts rights →
      (∀ left ∈ lefts, ∀ right, first left right → second left right) →
      List.Forall₂ second lefts rights
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, implication =>
      .cons (implication _ (by simp) _ head)
        (forall₂_imp_of_mem tail (fun left member right related =>
          implication left (List.mem_cons_of_mem _ member) right related))

/-- Collect the singleton candidates of the arguments of an application. -/
private theorem collect_candidates {space : Space} :
    ∀ {arguments : List Atom} {packageLists : List (List TypePackage)},
      List.Forall₂ (RuntimeTypePackagesRel space) arguments packageLists →
      (∀ argument ∈ arguments, ∀ {packages : List TypePackage},
        RuntimeTypePackagesRel space argument packages →
          ∃ type, observedTypes packages = [type] ∧
            (type = Atom.undefinedType ∨ StaticType type)) →
      ∃ actualTypes : List Atom,
        packageLists.map observedTypes = actualTypes.map (fun type => [type]) ∧
        List.Forall₂ (fun argument type => ExactTypes space argument [type] ∧
          (type = Atom.undefinedType ∨ StaticType type)) arguments actualTypes
  | _, _, .nil, _ => ⟨[], rfl, .nil⟩
  | _, _, .cons head tail, shape => by
      obtain ⟨type, observed, cases⟩ := shape _ (by simp) head
      obtain ⟨actualTypes, mapped, all⟩ := collect_candidates tail
        (fun argument member => shape argument (List.mem_cons_of_mem _ member))
      exact ⟨type :: actualTypes, by simp [observed, mapped],
        .cons ⟨⟨_, head, observed⟩, cases⟩ all⟩

private theorem candidates_ground {space : Space} {arguments actualTypes : List Atom}
    (all : List.Forall₂ (fun argument type => ExactTypes space argument [type] ∧
      (type = Atom.undefinedType ∨ StaticType type)) arguments actualTypes) :
    ∀ actual ∈ actualTypes, TypeSubst.typeVars actual = [] := by
  intro actual member
  obtain ⟨_, _, _, cases⟩ := forall₂_right_mem all actual member
  rcases cases with rfl | static
  · rfl
  · exact static.typeVars_nil

private theorem observed_inferred_empty (returnType : Atom) :
    observedTypes [inferredPackage [] returnType] = [returnType] := by
  simp [observedTypes, inferredPackage]

private theorem observed_published (type : Atom) :
    observedTypes [publishedPackage type] = [type] := rfl

/-! ## Shape of the exact relation on the fragment -/

/-- On saturated expressions every exact candidate list is a singleton: a
static type or the gradual `%Undefined%`. -/
theorem exact_shape {space : Space}
    {expression : Atom} (saturated : SaturatedTerm space expression) :
    ∀ {packages : List TypePackage}, RuntimeTypePackagesRel space expression packages →
      ∃ type, observedTypes packages = [type] ∧
        (type = Atom.undefinedType ∨ StaticType type) := by
  induction saturated with
  | constant declared static =>
      intro packages derivation
      rw [constant_packages_eq declared derivation]
      exact ⟨_, rfl, Or.inr static⟩
  | application notState annotationFree declared static function _ _ argumentIH =>
      intro packages derivation
      obtain ⟨_, argumentStatic, _, returnStatic⟩ := static.of_functionType function
      obtain ⟨packageLists, argumentRel, cases⟩ :=
        application_packages_cases notState annotationFree declared static function derivation
      obtain ⟨actualTypes, mapped, all⟩ := collect_candidates argumentRel argumentIH
      have actualCases : ∀ actual ∈ actualTypes,
          actual = Atom.undefinedType ∨ StaticType actual := by
        intro actual member
        obtain ⟨_, _, _, cases⟩ := forall₂_right_mem all actual member
        exact cases
      rcases cases actualTypes mapped (candidates_ground all) with
        ⟨substitution, fold, rfl⟩ | ⟨_, rfl⟩
      · obtain ⟨rfl, _⟩ := argumentList_static fold argumentStatic actualCases
        exact ⟨_, observed_inferred_empty _, Or.inr returnStatic⟩
      · exact ⟨_, observed_published _, Or.inl rfl⟩

/-! ## From HOL to HE -/

/-- Every left element of a pointwise relation has a related right element. -/
theorem forall₂_left_mem {α β : Type} {relation : α → β → Prop} :
    ∀ {lefts : List α} {rights : List β}, List.Forall₂ relation lefts rights →
      ∀ left ∈ lefts, ∃ right ∈ rights, relation left right
  | _, _, .nil => by simp
  | _, _, .cons head tail => by
      intro left member
      simp only [List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨_, by simp, head⟩
      · obtain ⟨right, rightMember, related⟩ := forall₂_left_mem tail left member
        exact ⟨right, List.mem_cons_of_mem _ rightMember, related⟩

/-- Weaken a pointwise relation using membership of both elements. -/
theorem forall₂_imp_of_mem₂ {α β : Type} {first second : α → β → Prop} :
    ∀ {lefts : List α} {rights : List β}, List.Forall₂ first lefts rights →
      (∀ left ∈ lefts, ∀ right ∈ rights, first left right → second left right) →
      List.Forall₂ second lefts rights
  | _, _, .nil, _ => .nil
  | _, _, .cons head tail, implication =>
      .cons (implication _ (by simp) _ (by simp) head)
        (forall₂_imp_of_mem₂ tail (fun left member right rightMember related =>
          implication left (List.mem_cons_of_mem _ member) right
            (List.mem_cons_of_mem _ rightMember) related))

private theorem choose_packages {space : Space} :
    ∀ {arguments types : List Atom},
      List.Forall₂ (fun argument type => ExactTypes space argument [type]) arguments types →
      ∃ packageLists : List (List TypePackage),
        List.Forall₂ (RuntimeTypePackagesRel space) arguments packageLists ∧
          packageLists.map observedTypes = types.map (fun type => [type])
  | _, _, .nil => ⟨[], .nil, rfl⟩
  | _, _, .cons ⟨packages, derivation, observed⟩ tail => by
      obtain ⟨packageLists, rest, mapped⟩ := choose_packages tail
      exact ⟨packages :: packageLists, .cons derivation rest, by simp [observed, mapped]⟩

private theorem observed_of_unique {space : Space} :
    ∀ {arguments types : List Atom} {packageLists : List (List TypePackage)},
      List.Forall₂ (fun argument type => ∀ {packages : List TypePackage},
        RuntimeTypePackagesRel space argument packages → observedTypes packages = [type])
        arguments types →
      List.Forall₂ (RuntimeTypePackagesRel space) arguments packageLists →
      packageLists.map observedTypes = types.map (fun type => [type])
  | _, _, _, .nil, .nil => rfl
  | _, _, _, .cons unique tail, .cons derivation rest => by
      simp [unique derivation, observed_of_unique tail rest]

private theorem accepted_static_eq :
    ∀ {expecteds actuals : List Atom},
      List.Forall₂ (fun expected actual =>
        actual = Atom.undefinedType ∨ expected = actual) expecteds actuals →
      (∀ actual ∈ actuals, actual ≠ Atom.undefinedType) → expecteds = actuals
  | _, _, .nil, _ => rfl
  | _, _, .cons accepted rest, notUndefined => by
      rcases accepted with undefined | rfl
      · exact absurd undefined (notUndefined _ (by simp))
      · rw [accepted_static_eq rest
          (fun actual member => notUndefined actual (List.mem_cons_of_mem _ member))]

/-- A HOL-typed saturated expression has, in HE's exact relation, exactly the
static type whose HOL image it has, and no other candidate list. -/
theorem exact_of_elaborates {space : Space}
    {expression : Atom} (saturated : SaturatedTerm space expression) :
    ∀ {holType : Ty Atom}, Elaborates (spaceSignature space) (toNamed expression) holType →
      ∃ type, StaticType type ∧ holType = toTy type ∧
        ExactTypes space expression [type] ∧
        ∀ {packages : List TypePackage}, RuntimeTypePackagesRel space expression packages →
          observedTypes packages = [type] := by
  induction saturated with
  | constant declared static =>
      intro holType elaborated
      rw [toNamed_of_declared declared] at elaborated
      obtain ⟨declared', lookup, rfl⟩ := elaborates_declared_iff.mp elaborated
      rw [declared] at lookup
      cases lookup
      exact ⟨_, static, rfl, ⟨_, constant_packages declared, rfl⟩,
        fun derivation => by rw [constant_packages_eq declared derivation]; rfl⟩
  | @application name arguments argumentTypes type returnType notState annotationFree
      declared static function lengths _ argumentIH =>
      intro holType elaborated
      obtain ⟨nonempty, argumentStatic, _, returnStatic⟩ := static.of_functionType function
      obtain ⟨rfl, argumentsElaborate⟩ :=
        (elaborates_application_iff declared function nonempty lengths).mp elaborated
      have argumentExact : List.Forall₂ (fun argument argumentType =>
          ExactTypes space argument [argumentType] ∧
            ∀ {packages : List TypePackage}, RuntimeTypePackagesRel space argument packages →
              observedTypes packages = [argumentType]) arguments argumentTypes := by
        refine forall₂_imp_of_mem₂ argumentsElaborate ?_
        intro argument member argumentType typeMember elaboratedArgument
        obtain ⟨found, foundStatic, holEq, exact, unique⟩ :=
          argumentIH argument member elaboratedArgument
        have equal : argumentType = found :=
          toTy_injective (argumentStatic argumentType typeMember) foundStatic holEq
        subst equal
        exact ⟨exact, unique⟩
      have accepted : List.Forall₂ (fun expected actual =>
          actual = Atom.undefinedType ∨ expected = actual) argumentTypes argumentTypes :=
        List.forall₂_same.mpr (fun _ _ => Or.inr rfl)
      have ground : ∀ actual ∈ argumentTypes, TypeSubst.typeVars actual = [] :=
        fun actual member => (argumentStatic actual member).typeVars_nil
      obtain ⟨packageLists, argumentRel, mapped⟩ :=
        choose_packages (argumentExact.imp (fun _ _ both => both.1))
      refine ⟨returnType, returnStatic, rfl,
        ⟨_, application_packages_success notState annotationFree declared static function
          argumentRel mapped ground accepted, observed_inferred_empty _⟩, ?_⟩
      intro packages derivation
      obtain ⟨packageLists', argumentRel', cases⟩ :=
        application_packages_cases notState annotationFree declared static function derivation
      have mapped' := observed_of_unique
        (argumentExact.imp (fun _ _ both => both.2)) argumentRel'
      rcases cases argumentTypes mapped' ground with
        ⟨substitution, fold, rfl⟩ | ⟨noFold, rfl⟩
      · obtain ⟨rfl, _⟩ := argumentList_static fold argumentStatic
          (fun actual member => Or.inr (argumentStatic actual member))
        exact observed_inferred_empty _
      · exact absurd (argumentList_static_exists [] argumentStatic accepted) (noFold [])

/-- Every subatom of a HOL-typed saturated expression is HOL-typed. -/
theorem elaborates_subatom {space : Space} {expression : Atom}
    (saturated : SaturatedTerm space expression) :
    ∀ {holType : Ty Atom}, Elaborates (spaceSignature space) (toNamed expression) holType →
      ∀ {sub : Atom}, Subatom sub expression →
        ∃ subType, Elaborates (spaceSignature space) (toNamed sub) subType := by
  induction saturated with
  | constant declared static =>
      rename_i atom type
      intro holType elaborated sub occurs
      cases atom with
      | symbol name => rw [occurs.symbol_eq]; exact ⟨_, elaborated⟩
      | grounded value => rw [occurs.grounded_eq]; exact ⟨_, elaborated⟩
      | var name => simp [declaredType?] at declared
      | expression atoms => simp [declaredType?] at declared
  | application notState _ declared static function lengths _ argumentIH =>
      intro holType elaborated sub occurs
      obtain ⟨nonempty, _, _, _⟩ := static.of_functionType function
      obtain ⟨_, argumentsElaborate⟩ :=
        (elaborates_application_iff declared function nonempty lengths).mp elaborated
      rcases occurs.expression_cases with rfl | ⟨child, member, inner⟩
      · exact ⟨_, elaborated⟩
      · simp only [List.mem_cons] at member
        rcases member with rfl | member
        · rw [inner.symbol_eq]
          exact ⟨_, elaborates_declared_iff.mpr ⟨_, declared, rfl⟩⟩
        · obtain ⟨argumentType, _, childElaborates⟩ :=
            forall₂_left_mem argumentsElaborate child member
          exact argumentIH child member childElaborates inner

/-! ## From HE to HOL -/

/-- HE's exact relation, with no `%Undefined%` fallback at any subatom, gives
a saturated expression a type only when HOL does. -/
theorem elaborates_of_exact {space : Space}
    {expression : Atom} (saturated : SaturatedTerm space expression) :
    NoUndefinedFallback space expression →
    ∀ {type : Atom}, ExactTypes space expression [type] →
      Elaborates (spaceSignature space) (toNamed expression) (toTy type) := by
  induction saturated with
  | constant declared static =>
      intro _ type exact
      obtain ⟨packages, derivation, observed⟩ := exact
      rw [constant_packages_eq declared derivation, observed_published] at observed
      cases observed
      rw [toNamed_of_declared declared]
      exact elaborates_declared_iff.mpr ⟨_, declared, rfl⟩
  | @application name arguments argumentTypes type returnType notState annotationFree
      declared static function lengths saturatedArguments argumentIH =>
      intro noFallback resultType exact
      obtain ⟨packages, derivation, observed⟩ := exact
      obtain ⟨nonempty, argumentStatic, _, _⟩ := static.of_functionType function
      obtain ⟨packageLists, argumentRel, cases⟩ :=
        application_packages_cases notState annotationFree declared static function derivation
      obtain ⟨actualTypes, mapped, all⟩ := collect_candidates argumentRel
        (fun argument member => exact_shape (saturatedArguments argument member))
      have actualStatic : List.Forall₂ (fun argument actual =>
          ExactTypes space argument [actual] ∧ StaticType actual) arguments actualTypes := by
        refine forall₂_imp_of_mem all ?_
        intro argument member actual both
        obtain ⟨exact, cases⟩ := both
        rcases cases with rfl | actualIsStatic
        · exact absurd exact
            (noFallback argument (Subatom.of_mem (List.mem_cons_of_mem _ member)))
        · exact ⟨exact, actualIsStatic⟩
      rcases cases actualTypes mapped (candidates_ground all) with
        ⟨substitution, fold, rfl⟩ | ⟨_, rfl⟩
      · obtain ⟨rfl, accepted⟩ := argumentList_static fold argumentStatic
          (fun actual member => by
            obtain ⟨_, _, _, isStatic⟩ := forall₂_right_mem actualStatic actual member
            exact Or.inr isStatic)
        have typesEq := accepted_static_eq accepted (fun actual member => by
          obtain ⟨_, _, _, isStatic⟩ := forall₂_right_mem actualStatic actual member
          exact isStatic.ne_undefined)
        subst typesEq
        rw [observed_inferred_empty] at observed
        cases observed
        apply (elaborates_application_iff declared function nonempty lengths).mpr ⟨rfl, ?_⟩
        refine forall₂_imp_of_mem actualStatic ?_
        intro argument member actual both
        exact argumentIH argument member
          (fun sub inner => noFallback sub
            (inner.trans (Subatom.of_mem (List.mem_cons_of_mem _ member))))
          both.1
      · exact absurd ⟨_, derivation, observed_published _⟩ (noFallback _ .refl)

/-! ## Agreement -/

/-- **Agreement of HE's exact type relation with simply typed HOL.**  For a
saturated expression over static declarations and a static type `T`, HOL
elaborates the expression at the image of `T` exactly when HE's exact
relation gives it the single candidate `T` and no subatom of it falls back
to the gradual `%Undefined%` candidate. -/
theorem hol_iff_exact {space : Space}
    {expression type : Atom} (saturated : SaturatedTerm space expression)
    (static : StaticType type) :
    HOLTyped space expression type ↔
      ExactTypes space expression [type] ∧ NoUndefinedFallback space expression := by
  constructor
  · intro typed
    obtain ⟨found, foundStatic, holEq, exact, _⟩ :=
      exact_of_elaborates saturated typed
    have equal := toTy_injective static foundStatic holEq
    subst equal
    refine ⟨exact, ?_⟩
    intro sub occurs subExact
    obtain ⟨packages, derivation, observed⟩ := subExact
    obtain ⟨_, subTyped⟩ := elaborates_subatom saturated typed occurs
    obtain ⟨subType, subStatic, _, _, unique⟩ :=
      exact_of_elaborates (saturated.subatom occurs) subTyped
    rw [unique derivation] at observed
    simp only [List.cons.injEq, and_true] at observed
    exact subStatic.ne_undefined observed
  · rintro ⟨exact, noFallback⟩
    exact elaborates_of_exact saturated noFallback exact

/-- On the fragment, a HOL-typed expression has exactly one HE candidate. -/
theorem exact_unique_of_holTyped {space : Space}
    {expression type : Atom} (saturated : SaturatedTerm space expression)
    (typed : HOLTyped space expression type) (static : StaticType type)
    {packages : List TypePackage}
    (derivation : RuntimeTypePackagesRel space expression packages) :
    observedTypes packages = [type] := by
  obtain ⟨found, foundStatic, holEq, _, unique⟩ :=
    exact_of_elaborates saturated typed
  rw [toTy_injective static foundStatic holEq]
  exact unique derivation

#print axioms hol_iff_exact
#print axioms exact_of_elaborates
#print axioms elaborates_of_exact
#print axioms exact_shape
#print axioms exact_unique_of_holTyped

end Mettapedia.Languages.MeTTa.HE.TypeGrounding
