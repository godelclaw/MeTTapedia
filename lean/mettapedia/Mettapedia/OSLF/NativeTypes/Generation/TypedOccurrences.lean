import Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences.Completeness

open Mettapedia.OSLF.Framework

/-!
# Executable typed occurrence generation for authored source schemas

The original grammar determines the complete finite descent at a supplied
source type. Collection-tail metadata is retained in every zipper rather
than subjected to the concrete runtime object's admission check. All actual
authored declaration alternatives and binder sorts remain in the site data.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.DerivedContexts
open Mettapedia.OSLF.MeTTaIL.GeneralTypedSites
open Mettapedia.GSLT.LanguageDef.WellSorted

def generate (language : LanguageDef) (free : FreeTypeContext)
    (permissions : OperationalPermissions) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) : List SiteData :=
  if permissions.enabled = true ∧ substitutionFree source = true ∧
      schemaCheckHasType language free bound source expected = true then
    SiteData.here bound expected source ::
      match source with
      | .apply constructor arguments =>
          language.terms.zipIdx.flatMap fun (rule, declaration) =>
            if rule.label = constructor ∧ expected = .base rule.category ∧
                usesBareCollection? rule = false ∧
                schemaCheckArguments language free bound arguments rule.params = true then
              arguments.attach.zipIdx.flatMap fun (argument, index) =>
                if permissions.permitsArgument constructor index = true then
                  match rule.params[index]?.bind parameterType? with
                  | some parameterType =>
                      (generate language free permissions bound parameterType argument.1).map
                        (SiteData.wrapApplication declaration constructor arguments index)
                  | none => []
                else []
            else []
      | .lambda binder body =>
          match expected with
          | .arrow domain codomain =>
              if permissions.underLambda = true then
                (generate language free permissions (domain :: bound) codomain body).map
                  (SiteData.wrapLambda binder domain)
              else []
          | _ => []
      | .multiLambda arity binders body =>
          match expected with
          | .arrow (.multiBinder domain) codomain =>
              if permissions.underMultiLambda = true then
                (generate language free permissions (List.replicate arity domain ++ bound)
                  codomain body).map (SiteData.wrapMultiLambda arity binders domain)
              else []
          | _ => []
      | .collection kind elements rest =>
          if kind ∈ permissions.collectionKinds then
            (match expected with
              | .collection actual elementType =>
                  if actual = kind ∧
                      schemaCheckElements language free bound elements elementType = true then
                    elements.attach.zipIdx.flatMap fun (element, index) =>
                      (generate language free permissions bound elementType element.1).map
                        (SiteData.wrapSchemaCollection (.directCollection kind) kind elements index rest)
                  else []
              | _ => []) ++
              language.terms.zipIdx.flatMap fun (rule, declaration) =>
                match bareCollectionElementType? rule kind expected with
                | some elementType =>
                    if schemaCheckElements language free bound elements elementType = true then
                      elements.attach.zipIdx.flatMap fun (element, index) =>
                        (generate language free permissions bound elementType element.1).map
                          (SiteData.wrapSchemaCollection (.authoredCollection declaration) kind elements index rest)
                    else []
                | none => []
          else []
      | _ => []
  else []
termination_by sizeOf source
decreasing_by
  all_goals simp_wf
  all_goals first
    | (have smaller := List.sizeOf_lt_of_mem argument.property; omega)
    | (have smaller := List.sizeOf_lt_of_mem element.property; omega)

private theorem attached_position {α : Type} {elements : List α}
    {element : {item // item ∈ elements}} {index : Nat}
    (member : (element, index) ∈ elements.attach.zipIdx) :
    elements[index]? = some element.val := by
  have selected := List.mk_mem_zipIdx_iff_getElem?.mp member
  have mapped := congrArg (Option.map Subtype.val) selected
  simpa only [← List.getElem?_map, List.attach_map_subtype_val, Option.map_some] using mapped

private theorem attached_position_mem {α : Type} {elements : List α} {element : α}
    {index : Nat} (selected : elements[index]? = some element) :
    ((⟨element, List.mem_of_getElem? selected⟩ : {item // item ∈ elements}), index) ∈
      elements.attach.zipIdx := by
  apply List.mk_mem_zipIdx_iff_getElem?.mpr
  rw [List.getElem?_attach]
  simp [selected]

private theorem licensed_checked {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site) :
    permissions.enabled = true ∧ substitutionFree source = true ∧
      schemaCheckHasType language free bound source expected = true :=
  ⟨licensed.enabled, licensed.source_substitutionFree,
    schemaCheckHasType_complete licensed.source_typed licensed.source_substitutionFree⟩

theorem generate_sound (language : LanguageDef) (free : FreeTypeContext)
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (site : SiteData)
    (member : site ∈ generate language free permissions bound expected source) :
    Licensed language free permissions bound expected source site := by
  rw [generate.eq_def] at member
  split at member
  · rename_i accepted
    rcases List.mem_cons.mp member with same | nested
    · subst site
      exact .here accepted.1 accepted.2.1 (schemaCheckHasType_sound accepted.2.2)
    · cases source with
      | bvar _ => cases nested
      | fvar _ => cases nested
      | subst _ _ => cases nested
      | apply constructor arguments =>
        dsimp only at nested
        obtain ⟨⟨rule, declaration⟩, declared, branch⟩ := List.mem_flatMap.mp nested
        dsimp only at branch
        split at branch
        · rename_i checked
          obtain ⟨labelEq, typeEq, ordinary, argsChecked⟩ := checked
          subst constructor
          subst expected
          obtain ⟨⟨argument, index⟩, selected, descendants⟩ := List.mem_flatMap.mp branch
          dsimp only at descendants
          split at descendants
          · rename_i permitted
            cases parameterResult : rule.params[index]?.bind parameterType? with
            | none => simp [parameterResult] at descendants
            | some parameterType =>
              rw [parameterResult] at descendants
              obtain ⟨inner, innerMember, same⟩ := List.mem_map.mp descendants
              subst site
              obtain ⟨parameter, parameterSelected, parameterTyped⟩ :=
                Option.bind_eq_some_iff.mp parameterResult
              have notBare : ¬ UsesBareCollection rule := by
                intro bare
                have yes := (usesBareCollection?_eq_true_iff rule).mpr bare
                rw [ordinary] at yes
                contradiction
              exact .application declared notBare
                (schemaCheckArguments_sound_of (fun _ _ _ checked => schemaCheckHasType_sound checked) argsChecked)
                accepted.2.1 (attached_position selected) parameterSelected parameterTyped
                ((permitsArgument_spec permissions rule.label index).mp permitted)
                (generate_sound language free permissions bound parameterType argument.val inner innerMember)
          · cases descendants
        · cases branch
      | lambda binder body =>
        dsimp only at nested
        cases expected with
        | base _ => cases nested
        | multiBinder _ => cases nested
        | collection _ _ => cases nested
        | arrow domain codomain =>
          dsimp only at nested
          split at nested
          · rename_i permitted
            obtain ⟨inner, innerMember, same⟩ := List.mem_map.mp nested
            subst site
            exact .lambda permitted
              (generate_sound language free permissions (domain :: bound) codomain body inner innerMember)
          · cases nested
      | multiLambda arity binders body =>
        dsimp only at nested
        cases expected with
        | base _ => cases nested
        | multiBinder _ => cases nested
        | collection _ _ => cases nested
        | arrow domain codomain =>
          cases domain with
          | base _ => cases nested
          | arrow _ _ => cases nested
          | collection _ _ => cases nested
          | multiBinder domain =>
            dsimp only at nested
            split at nested
            · rename_i permitted
              obtain ⟨inner, innerMember, same⟩ := List.mem_map.mp nested
              subst site
              exact .multiLambda permitted
                (generate_sound language free permissions (List.replicate arity domain ++ bound)
                  codomain body inner innerMember)
            · cases nested
      | collection kind elements rest =>
        dsimp only at nested
        split at nested
        · rename_i permitted
          rcases List.mem_append.mp nested with direct | authored
          · cases expected with
            | base _ => cases direct
            | arrow _ _ => cases direct
            | multiBinder _ => cases direct
            | collection actual elementType =>
              dsimp only at direct
              split at direct
              · rename_i checked
                obtain ⟨kindEq, elementsChecked⟩ := checked
                subst actual
                obtain ⟨⟨element, index⟩, selected, descendants⟩ := List.mem_flatMap.mp direct
                obtain ⟨inner, innerMember, same⟩ := List.mem_map.mp descendants
                subst site
                exact .directCollection permitted (schemaCheckElements_sound elementsChecked)
                  accepted.2.1 (attached_position selected)
                  (generate_sound language free permissions bound elementType element.val inner innerMember)
              · cases direct
          · obtain ⟨⟨rule, declaration⟩, declared, branch⟩ := List.mem_flatMap.mp authored
            dsimp only at branch
            cases elementResult : bareCollectionElementType? rule kind expected with
            | none => simp [elementResult] at branch
            | some elementType =>
              rw [elementResult] at branch
              dsimp only at branch
              split at branch
              · rename_i checked
                obtain ⟨⟨element, index⟩, selected, descendants⟩ := List.mem_flatMap.mp branch
                obtain ⟨inner, innerMember, same⟩ := List.mem_map.mp descendants
                subst site
                obtain ⟨typeEq, parameterName, shape⟩ :=
                  (bareCollectionElementType?_eq_some_iff rule kind expected elementType).mp elementResult
                subst expected
                exact .authoredCollection declared shape permitted (schemaCheckElements_sound checked)
                  accepted.2.1 (attached_position selected)
                  (generate_sound language free permissions bound elementType element.val inner innerMember)
              · cases branch
        · cases nested
  · cases member
termination_by sizeOf source
decreasing_by
  all_goals subst source
  all_goals simp_wf
  all_goals first
    | omega
    | (have smaller := List.sizeOf_lt_of_mem argument.property; omega)
    | (have smaller := List.sizeOf_lt_of_mem element.property; omega)

theorem generate_stopped (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) :
    generate language free .stopped bound expected source = [] := by
  rw [generate.eq_def]
  simp [OperationalPermissions.stopped]

theorem generate_rootOnly (language : LanguageDef) (free : FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (source : Pattern) :
    generate language free .rootOnly bound expected source =
      if substitutionFree source = true ∧ schemaCheckHasType language free bound source expected = true
      then [SiteData.here bound expected source] else [] := by
  rw [generate.eq_def]
  simp only [OperationalPermissions.rootOnly, true_and]
  split
  · cases source with
    | apply _ _ => simp [OperationalPermissions.permitsArgument]
    | lambda _ _ => cases expected <;> simp
    | multiLambda _ _ _ =>
      cases expected with
      | arrow domain codomain => cases domain <;> simp
      | _ => simp
    | collection _ _ rest => cases rest <;> simp
    | _ => simp
  · rfl

/-- No typing determinism or caller-supplied completeness hypothesis is used.
Every independently licensed typing descent is emitted by the algorithm. -/
theorem generate_complete {language : LanguageDef} {free : FreeTypeContext}
    {permissions : OperationalPermissions} {bound : List TypeExpr} {expected : TypeExpr}
    {source : Pattern} {site : SiteData}
    (licensed : Licensed language free permissions bound expected source site) :
    site ∈ generate language free permissions bound expected source := by
  induction licensed with
  | here enabled object typed =>
    rw [generate.eq_def, if_pos ⟨enabled, object, schemaCheckHasType_complete typed object⟩]
    exact List.mem_cons_self
  | @application bound rule declaration index arguments argument parameter parameterType inner
      declared ordinary typed objects selected parameterSelected parameterTyped permitted innerLicensed ih =>
    have accepted := licensed_checked (Licensed.application declared ordinary typed objects
      selected parameterSelected parameterTyped permitted innerLicensed)
    have ordinaryChecked : usesBareCollection? rule = false := by
      cases checked : usesBareCollection? rule with
      | false => rfl
      | true => exact False.elim (ordinary ((usesBareCollection?_eq_true_iff rule).mp checked))
    have argsChecked := schemaCheckArguments_complete typed objects
    rw [generate.eq_def, if_pos accepted]
    apply List.mem_cons_of_mem
    dsimp only
    apply List.mem_flatMap.mpr
    refine ⟨(rule, declaration), declared, ?_⟩
    dsimp only
    rw [if_pos ⟨rfl, rfl, ordinaryChecked, argsChecked⟩]
    apply List.mem_flatMap.mpr
    refine ⟨((⟨argument, List.mem_of_getElem? selected⟩ : {item // item ∈ arguments}), index),
      attached_position_mem selected, ?_⟩
    dsimp only
    rw [if_pos ((permitsArgument_spec permissions rule.label index).mpr permitted)]
    rw [parameterSelected, Option.bind_some, parameterTyped]
    exact List.mem_map.mpr ⟨inner, ih, rfl⟩
  | @lambda bound binder body domain codomain inner permitted innerLicensed ih =>
    have accepted := licensed_checked (Licensed.lambda (binder := binder) permitted innerLicensed)
    rw [generate.eq_def, if_pos accepted]
    apply List.mem_cons_of_mem
    dsimp only
    rw [if_pos permitted]
    exact List.mem_map.mpr ⟨_, ih, rfl⟩
  | @multiLambda bound arity binders body domain codomain inner permitted innerLicensed ih =>
    have accepted := licensed_checked
      (Licensed.multiLambda (arity := arity) (binders := binders) permitted innerLicensed)
    rw [generate.eq_def, if_pos accepted]
    apply List.mem_cons_of_mem
    dsimp only
    rw [if_pos permitted]
    exact List.mem_map.mpr ⟨_, ih, rfl⟩
  | @directCollection bound kind elements rest index element elementType inner
      permitted typed objects selected innerLicensed ih =>
    have accepted := licensed_checked
      (Licensed.directCollection (rest := rest) permitted typed objects selected innerLicensed)
    have elementsChecked := schemaCheckElements_complete typed objects
    rw [generate.eq_def, if_pos accepted]
    apply List.mem_cons_of_mem
    dsimp only
    rw [if_pos permitted]
    apply List.mem_append_left
    rw [if_pos ⟨rfl, elementsChecked⟩]
    apply List.mem_flatMap.mpr
    exact ⟨((⟨element, List.mem_of_getElem? selected⟩ : {item // item ∈ elements}), index),
      attached_position_mem selected, List.mem_map.mpr ⟨inner, ih, rfl⟩⟩
  | @authoredCollection bound rule declaration parameterName kind elements rest index element elementType inner
      declared shape permitted typed objects selected innerLicensed ih =>
    have accepted := licensed_checked
      (Licensed.authoredCollection (rest := rest) declared shape permitted typed objects selected innerLicensed)
    have elementsChecked := schemaCheckElements_complete typed objects
    have elementResult : bareCollectionElementType? rule kind (.base rule.category) = some elementType :=
      (bareCollectionElementType?_eq_some_iff rule kind (.base rule.category) elementType).mpr
        ⟨rfl, parameterName, shape⟩
    rw [generate.eq_def, if_pos accepted]
    apply List.mem_cons_of_mem
    dsimp only
    rw [if_pos permitted]
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨(rule, declaration), declared, ?_⟩
    dsimp only
    rw [elementResult]
    dsimp only
    rw [if_pos elementsChecked]
    apply List.mem_flatMap.mpr
    exact ⟨((⟨element, List.mem_of_getElem? selected⟩ : {item // item ∈ elements}), index),
      attached_position_mem selected, List.mem_map.mpr ⟨inner, ih, rfl⟩⟩

/-- Exact grammar-driven occurrence coverage for arbitrary substitution-free schema size
and binder depth, including every retained typing alternative. -/
theorem generate_spec (language : LanguageDef) (free : FreeTypeContext)
    (permissions : OperationalPermissions) (bound : List TypeExpr) (expected : TypeExpr)
    (source : Pattern) (site : SiteData) :
    site ∈ generate language free permissions bound expected source ↔
      Licensed language free permissions bound expected source site :=
  ⟨generate_sound language free permissions bound expected source site, generate_complete⟩

/-- Coverage also holds against the previously defined typed zipper judgment,
with exact binder sorts and focus type. The existential preserves every
authored declaration alternative that justifies this typed occurrence. -/
theorem generate_typedAt_iff (language : LanguageDef) (free : FreeTypeContext)
    (permissions : OperationalPermissions) (bound focusBound : List TypeExpr)
    (expected focusType : TypeExpr) (focus : Pattern) (context : OneHoleContext) :
    (∃ site ∈ generate language free permissions bound expected (context.fill focus),
      site.context = context ∧ site.focus = focus ∧
      site.focusBound = focusBound ∧ site.focusType = focusType) ↔
    TypedAt language free focus context bound expected focusBound focusType ∧
      substitutionFree (context.fill focus) = true ∧ permitsContext permissions context = true := by
  constructor
  · rintro ⟨site, member, contextEq, focusEq, boundEq, typeEq⟩
    have licensed := generate_sound language free permissions bound expected
      (context.fill focus) site member
    exact ⟨by simpa only [contextEq, focusEq, boundEq, typeEq] using licensed.typedAt,
      licensed.source_substitutionFree, by simpa only [contextEq] using licensed.permitted⟩
  · rintro ⟨typed, object, permitted⟩
    obtain ⟨site, licensed, equalities⟩ := typedAt_licensed typed object permitted
    exact ⟨site, generate_complete licensed, equalities⟩

end Mettapedia.OSLF.NativeTypes.Generation.TypedOccurrences
