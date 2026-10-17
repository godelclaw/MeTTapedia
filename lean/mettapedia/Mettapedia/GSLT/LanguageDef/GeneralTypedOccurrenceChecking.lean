import Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrence

/-!
# Checking a selected typed occurrence

The address and typing frames select one source occurrence and one sequence
of authored grammar declarations. Replay follows those choices directly. It
does not enumerate the other source sites or discard alternative typings.
Local typing is checked by the existing declaration-derived typing checker.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceChecking

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open GeneralTypedOccurrence WellSorted

/-- Check a selected path, reconstructing its original licensing derivation.
The proof component is erased when this procedure is executed. -/
def locate (language : LanguageDef) (free : FreeTypeContext)
    (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (address : List Nat)
    (frames : List TypingFrame) :
    Option {site : SiteData // Licensed language free permissions bound expected source site} :=
  match frames, address with
  | [], [] =>
      if h : permissions.enabled = true ∧ isObjectPattern source = true ∧
          checkHasType language free bound source expected = true then
        some ⟨SiteData.here bound expected source,
          .here h.1 h.2.1 (checkHasType_sound h.2.2)⟩
      else none
  | .application declaration index :: rest, actual :: path =>
    match source with
    | .apply constructor arguments =>
      match selectedRule : language.terms[declaration]? with
      | none => none
      | some rule =>
        match selectedArgument : arguments[index]?, selectedParameter : rule.params[index]? with
        | some argument, some parameter =>
          match parameterType : parameterType? parameter with
          | none => none
          | some typ =>
            if h : actual = index ∧ rule.label = constructor ∧ expected = .base rule.category ∧
                usesBareCollection? rule = false ∧
                checkArgumentsHaveTypes language free bound arguments rule.params = true ∧
                isObjectPatternList arguments = true ∧
                permissions.permitsArgument rule.label index = true then
              (locate language free permissions bound typ argument path rest).map fun inner =>
                ⟨inner.val.wrapApplication declaration constructor arguments index, by
                  have ordinary : ¬ UsesBareCollection rule := by
                    intro bare
                    have := (usesBareCollection?_eq_true_iff rule).mpr bare
                    simp [h.2.2.2.1] at this
                  have typed := checkArgumentsHaveTypes_sound_of
                    (fun _ _ _ checked => checkHasType_sound checked) h.2.2.2.2.1
                  have lic := Licensed.application
                    (List.mk_mem_zipIdx_iff_getElem?.mpr selectedRule) ordinary typed
                    h.2.2.2.2.2.1 selectedArgument selectedParameter parameterType
                    ((permitsArgument_spec _ _ _).mp h.2.2.2.2.2.2) inner.property
                  simpa only [h.2.1, h.2.2.1] using lic⟩
            else none
        | _, _ => none
    | _ => none
  | .lambda domain :: rest, actual :: path =>
    match source, expected with
    | .lambda binder body, .arrow actualDomain codomain =>
      if h : actual = 0 ∧ actualDomain = domain ∧ permissions.underLambda = true then
        (locate language free permissions (domain :: bound) codomain body path rest).map
          fun inner => ⟨inner.val.wrapLambda binder domain, by
            simpa only [h.2.1] using Licensed.lambda (binder := binder) h.2.2 inner.property⟩
      else none
    | _, _ => none
  | .multiLambda arity domain :: rest, actual :: path =>
    match source, expected with
    | .multiLambda actualArity binders body, .arrow (.multiBinder actualDomain) codomain =>
      if h : actual = 0 ∧ actualArity = arity ∧ actualDomain = domain ∧
          permissions.underMultiLambda = true then
        (locate language free permissions (List.replicate arity domain ++ bound)
          codomain body path rest).map fun inner =>
            ⟨inner.val.wrapMultiLambda arity binders domain, by
              simpa only [h.2.1, h.2.2.1] using
                Licensed.multiLambda (binders := binders) h.2.2.2 inner.property⟩
      else none
    | _, _ => none
  | .directCollection kind :: rest, index :: path =>
    match source, expected with
    | .collection actualKind elements none, .collection expectedKind elementType =>
      match selected : elements[index]? with
      | none => none
      | some element =>
        if h : actualKind = kind ∧ expectedKind = kind ∧ kind ∈ permissions.collectionKinds ∧
            checkElementsHaveType language free bound elements elementType = true ∧
            isObjectPatternList elements = true then
          (locate language free permissions bound elementType element path rest).map fun inner =>
            ⟨inner.val.wrapCollection (.directCollection kind) kind elements index, by
              simpa only [h.1, h.2.1] using
                Licensed.directCollection h.2.2.1
                  (checkElementsHaveType_sound h.2.2.2.1) h.2.2.2.2 selected inner.property⟩
        else none
    | _, _ => none
  | .authoredCollection declaration :: rest, index :: path =>
    match source with
    | .collection kind elements none =>
      match selectedRule : language.terms[declaration]? with
      | none => none
      | some rule =>
        match selectedType : bareCollectionElementType? rule kind expected with
        | none => none
        | some elementType =>
          match selected : elements[index]? with
          | none => none
          | some element =>
            if h : kind ∈ permissions.collectionKinds ∧
                checkElementsHaveType language free bound elements elementType = true ∧
                isObjectPatternList elements = true then
              (locate language free permissions bound elementType element path rest).map fun inner =>
                ⟨inner.val.wrapCollection (.authoredCollection declaration) kind elements index, by
                  obtain ⟨expectedEq, name, shape⟩ :=
                    (bareCollectionElementType?_eq_some_iff _ _ _ _).mp selectedType
                  have lic := Licensed.authoredCollection
                    (List.mk_mem_zipIdx_iff_getElem?.mpr selectedRule) shape h.1
                    (checkElementsHaveType_sound h.2.1) h.2.2 selected inner.property
                  simpa only [expectedEq] using lic⟩
            else none
    | _ => none
  | _, _ => none
termination_by frames.length

/-- Replay contains no proof search over addresses or grammar alternatives. -/
def replay (language : LanguageDef) (free : FreeTypeContext)
    (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (address : List Nat)
    (frames : List TypingFrame) : Option SiteData :=
  (locate language free permissions bound expected source address frames).map Subtype.val

theorem replay_sound {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {address : List Nat}
    {frames : List TypingFrame} {site : SiteData}
    (accepted : replay language free permissions bound expected source address frames = some site) :
    Licensed language free permissions bound expected source site := by
  obtain ⟨checked, _, equal⟩ := Option.map_eq_some_iff.mp accepted
  exact equal ▸ checked.property

theorem locate_complete {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site) :
    locate language free permissions bound expected source site.address site.typingFrames =
      some ⟨site, licensed⟩ := by
  induction licensed with
  | here enabled object typed =>
      simp [SiteData.here, locate, enabled, object,
        checkHasType_complete_of_object typed object]
  | @application bound rule declaration index arguments argument parameter typ inner
      declared ordinary typed objects selected selectedParameter parameterTyped permitted lic ih =>
      have notBare : usesBareCollection? rule = false := by
        apply Bool.eq_false_of_not_eq_true
        exact fun h => ordinary ((usesBareCollection?_eq_true_iff rule).mp h)
      have argumentTypes := checkArgumentsHaveTypes_complete_of_objects typed objects
      have permission := (permitsArgument_spec _ _ _).mpr permitted
      have declaredAt := List.mk_mem_zipIdx_iff_getElem?.mp declared
      change locate language free permissions bound (.base rule.category)
        (.apply rule.label arguments) (index :: inner.address)
        (.application declaration index :: inner.typingFrames) = some _
      rw [locate.eq_def]
      dsimp only
      split
      · next h => simp [declaredAt] at h
      · next actual actualSelected =>
        have eqRule : actual = rule := Option.some.inj (actualSelected.symm.trans declaredAt)
        subst actual
        split
        · next arg param argSelected paramSelected =>
          have eqArg : arg = argument := Option.some.inj (argSelected.symm.trans selected)
          have eqParam : param = parameter := Option.some.inj (paramSelected.symm.trans selectedParameter)
          subst arg param
          split
          · next h => simp [parameterTyped] at h
          · next actualType selectedType =>
            have eqType : actualType = typ := Option.some.inj (selectedType.symm.trans parameterTyped)
            subst actualType
            simp [notBare, argumentTypes, objects, permission, ih]
        · next h => simp [selected, selectedParameter] at h
  | @lambda bound binder body domain codomain inner permitted lic ih =>
      simp [SiteData.wrapLambda, locate, permitted, ih]
  | @multiLambda bound arity binders body domain codomain inner permitted lic ih =>
      simp [SiteData.wrapMultiLambda, locate, permitted, ih]
  | @directCollection bound kind elements index element typ inner permitted typed objects
      selected lic ih =>
      have elementTypes := checkElementsHaveType_complete_of_objects typed objects
      change locate language free permissions bound (.collection kind typ)
        (.collection kind elements none) (index :: inner.address)
        (.directCollection kind :: inner.typingFrames) = some _
      rw [locate.eq_def]
      dsimp only
      split
      · next h => simp [selected] at h
      · next actual selectedActual =>
        have eqElement : actual = element := Option.some.inj (selectedActual.symm.trans selected)
        subst actual
        simp [permitted, elementTypes, objects, ih]
  | @authoredCollection bound rule declaration name kind elements index element typ inner
      declared shape permitted typed objects selected lic ih =>
      have elementTypes := checkElementsHaveType_complete_of_objects typed objects
      have declaredAt := List.mk_mem_zipIdx_iff_getElem?.mp declared
      have selectedType := (bareCollectionElementType?_eq_some_iff rule kind
        (.base rule.category) typ).mpr ⟨rfl, name, shape⟩
      change locate language free permissions bound (.base rule.category)
        (.collection kind elements none) (index :: inner.address)
        (.authoredCollection declaration :: inner.typingFrames) = some _
      rw [locate.eq_def]
      dsimp only
      split
      · next h => simp [declaredAt] at h
      · next actual actualSelected =>
        have eqRule : actual = rule := Option.some.inj (actualSelected.symm.trans declaredAt)
        subst actual
        split
        · next h => simp [selectedType] at h
        · next actualType selectedActualType =>
          have eqType : actualType = typ := Option.some.inj (selectedActualType.symm.trans selectedType)
          subst actualType
          split
          · next h => simp [selected] at h
          · next actual selectedActual =>
            have eqElement : actual = element := Option.some.inj (selectedActual.symm.trans selected)
            subst actual
            simp [permitted, elementTypes, objects, ih]

theorem replay_complete {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr}
    {expected : TypeExpr} {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site) :
    replay language free permissions bound expected source site.address site.typingFrames =
      some site := by
  simp [replay, locate_complete licensed]

/-- Compare the reconstructed site with all supplied fields, including its
zipper, local context, local type and typing-declaration choices. -/
def check (language : LanguageDef) (free : FreeTypeContext)
    (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (site : SiteData) : Bool :=
  decide (replay language free permissions bound expected source site.address site.typingFrames =
    some site)

theorem check_exact (language : LanguageDef) (free : FreeTypeContext)
    (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (site : SiteData) :
    check language free permissions bound expected source site = true ↔
      Licensed language free permissions bound expected source site := by
  simp only [check, decide_eq_true_eq]
  exact ⟨replay_sound, replay_complete⟩

end Mettapedia.GSLT.LanguageDef.GeneralTypedOccurrenceChecking
