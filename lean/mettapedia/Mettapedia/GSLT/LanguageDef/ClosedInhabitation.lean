import Mettapedia.GSLT.LanguageDef.WellSorted
import Mettapedia.Logic.LP.HypotheticalPropositional

/-!
# Which sorts of a presentation have closed terms

A sort is inhabited when some closed object pattern has it, in the ordinary
well-sortedness judgment of the presentation (`WellSorted.HasType` with no free
variables, no pending substitution and no open collection tail).

Each constructor is read as a hypothetical Horn clause over sort names: a
simple argument of base sort asks for that sort; a collection argument asks for
nothing (the empty collection); a binding argument `D → C` asks for `C` under
a bound variable of sort `D`. `inhabited_iff` proves the reading exact for
every presentation whose argument types are of these shapes (`Supported`), so
inhabitation is decided by `HypotheticalPropositional.closure`.

Why it matters for generated type systems: the completion of a presentation
adjoins the sort constants `∗^X` and `□^X` to every carrier `X`. When `X` has no
closed term, these constants are its first closed elements. Every possibility
type over `X` is then empty in the term model and every universally quantified
claim over `X` holds vacuously.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ClosedInhabitation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.Logic.LP.HypotheticalPropositional

/-- What a closed term of a type asks for: `none` for an unsupported shape;
`some none` when the type always has a closed term; otherwise a base sort under
bound variables of the listed base sorts. -/
def typeGoal : TypeExpr → Option (Option (Finset String × String))
  | .base sort => some (some (∅, sort))
  | .collection _ _ => some none
  | .arrow (.base domain) codomain =>
      (typeGoal codomain).map (Option.map fun goal => (insert domain goal.1, goal.2))
  | .arrow (.multiBinder (.base domain)) codomain =>
      (typeGoal codomain).map (Option.map fun goal => (insert domain goal.1, goal.2))
  | _ => none

/-- The goal of a constructor parameter, respecting its representation. -/
def paramGoal : TermParam → Option (Option (Finset String × String))
  | .simple _ type => typeGoal type
  | .abstractionNamed _ _ (.arrow (.base domain) codomain) =>
      typeGoal (.arrow (.base domain) codomain)
  | .abstractionNamed _ _ (.base sort) => typeGoal (.arrow (.base sort) (.base sort))
  | .multiAbstractionNamed _ _ (.arrow (.multiBinder (.base domain)) codomain) =>
      typeGoal (.arrow (.multiBinder (.base domain)) codomain)
  | .multiAbstractionNamed _ _ (.base sort) =>
      typeGoal (.arrow (.multiBinder (.base sort)) (.base sort))
  | _ => none

/-- The clause of one constructor. -/
def ruleClause (rule : GrammarRule) : Clause String :=
  ⟨rule.params.filterMap fun param => (paramGoal param).bind id, rule.category⟩

/-- The clauses of a presentation. -/
def clauses (language : LanguageDef) : List (Clause String) := language.terms.map ruleClause

/-- Every parameter has a supported shape. -/
def Supported (language : LanguageDef) : Prop :=
  ∀ rule ∈ language.terms, ∀ param ∈ rule.params, (paramGoal param).isSome = true

instance (language : LanguageDef) : Decidable (Supported language) := by
  unfold Supported; infer_instance

/-- A closed object pattern of the sort exists. -/
def Inhabited (language : LanguageDef) (sort : String) : Prop :=
  ∃ pattern, isObjectPattern pattern = true ∧
    HasType language (fun _ => none) [] pattern (.base sort)

/-- Base sorts of the bound variables. -/
def baseSet (bound : List TypeExpr) : Finset String :=
  (bound.filterMap fun type => match type with
    | .base sort => some sort
    | _ => none).toFinset

theorem mem_baseSet {bound : List TypeExpr} {sort : String} :
    sort ∈ baseSet bound ↔ TypeExpr.base sort ∈ bound := by
  simp only [baseSet, List.mem_toFinset, List.mem_filterMap]
  constructor
  · rintro ⟨type, member, matched⟩
    cases type <;> simp at matched
    subst matched
    exact member
  · intro member
    exact ⟨_, member, rfl⟩

theorem baseSet_cons_base (sort : String) (bound : List TypeExpr) :
    baseSet (.base sort :: bound) = insert sort (baseSet bound) := by
  ext name
  simp [mem_baseSet, eq_comm]

theorem baseSet_subset_of_mem {bound larger : List TypeExpr}
    (subset : ∀ type ∈ bound, type ∈ larger) : baseSet bound ⊆ baseSet larger :=
  fun _ member => mem_baseSet.mpr (subset _ (mem_baseSet.mp member))

/-! ## Goals of types -/

theorem typeGoal_arrow_base {domain : String} {codomain : TypeExpr}
    {goal : Finset String × String}
    (shape : typeGoal (.arrow (.base domain) codomain) = some (some goal)) :
    ∃ inner, typeGoal codomain = some (some inner) ∧ goal = (insert domain inner.1, inner.2) := by
  simp only [typeGoal] at shape
  cases inner : typeGoal codomain with
  | none => simp [inner] at shape
  | some result =>
      cases result with
      | none => simp [inner] at shape
      | some inner' =>
          simp only [inner, Option.map_some, Option.some.injEq] at shape
          exact ⟨inner', rfl, shape.symm⟩

theorem typeGoal_arrow_multi {domain : String} {codomain : TypeExpr}
    {goal : Finset String × String}
    (shape : typeGoal (.arrow (.multiBinder (.base domain)) codomain) = some (some goal)) :
    ∃ inner, typeGoal codomain = some (some inner) ∧ goal = (insert domain inner.1, inner.2) := by
  simp only [typeGoal] at shape
  cases inner : typeGoal codomain with
  | none => simp [inner] at shape
  | some result =>
      cases result with
      | none => simp [inner] at shape
      | some inner' =>
          simp only [inner, Option.map_some, Option.some.injEq] at shape
          exact ⟨inner', rfl, shape.symm⟩

/-- A parameter's goal is the goal of its declared type. -/
theorem paramGoal_typeGoal {param : TermParam} {expected : TypeExpr}
    {result : Option (Finset String × String)}
    (declared : parameterType? param = some expected) (goal : paramGoal param = some result) :
    typeGoal expected = some result := by
  cases param with
  | simple name type =>
      simp only [parameterType?, Option.some.injEq] at declared
      subst declared
      exact goal
  | abstractionNamed binder name type =>
      cases type with
      | base sort =>
          simp only [parameterType?, Option.some.injEq] at declared
          subst declared
          exact goal
      | arrow domain codomain =>
          simp only [parameterType?, Option.some.injEq] at declared
          subst declared
          cases domain with
          | multiBinder inner => simp [paramGoal] at goal
          | _ => exact goal
      | multiBinder inner => simp [parameterType?] at declared
      | collection kind element => simp [parameterType?] at declared
  | multiAbstractionNamed binders name type =>
      cases type with
      | base sort =>
          simp only [parameterType?, Option.some.injEq] at declared
          subst declared
          exact goal
      | arrow domain codomain =>
          cases domain with
          | multiBinder inner =>
              simp only [parameterType?, Option.some.injEq] at declared
              subst declared
              cases inner <;> exact goal
          | _ => simp [parameterType?] at declared
      | _ => simp [parameterType?] at declared

/-! ## Completeness: a closed pattern yields a derivation -/

/-- Bound variables of base sort, or of a type that asks for nothing. -/
def BoundOK (bound : List TypeExpr) : Prop :=
  ∀ type ∈ bound, (∃ sort, type = .base sort) ∨ typeGoal type = none

theorem boundOK_nil : BoundOK [] := by simp [BoundOK]

theorem typeGoal_multiBinder (type : TypeExpr) : typeGoal (.multiBinder type) = none := rfl

variable {language : LanguageDef}

mutual
  theorem derives_of_hasType {bound : List TypeExpr} {pattern : Pattern} {type : TypeExpr}
      (typed : HasType language (fun _ => none) bound pattern type)
      (object : isObjectPattern pattern = true) (ok : BoundOK bound)
      {goal : Finset String × String} (shape : typeGoal type = some (some goal)) :
      Derives (clauses language) (goal.1 ∪ baseSet bound) goal.2 := by
    cases typed with
    | bvar lookup =>
        rcases ok _ (List.mem_of_getElem? lookup) with ⟨sort, rfl⟩ | unasked
        · simp only [typeGoal, Option.some.injEq] at shape
          subst shape
          exact .hyp (Finset.mem_union_right _ (mem_baseSet.mpr (List.mem_of_getElem? lookup)))
        · rw [unasked] at shape
          cases shape
    | fvar lookup => cases lookup
    | @constructor _ rule arguments member _ argumentsTyped =>
        simp only [typeGoal, Option.some.injEq] at shape
        subst shape
        refine .clause (List.mem_map.mpr ⟨rule, member, rfl⟩) fun premise premiseMember => ?_
        obtain ⟨param, paramMember, chosen⟩ := List.mem_filterMap.mp premiseMember
        have asked : paramGoal param = some (some premise) := by
          cases result : paramGoal param with
          | none => simp [result] at chosen
          | some inner => cases inner <;> simp_all
        simp only [isObjectPattern] at object
        have derived := derives_of_arguments argumentsTyped object ok param paramMember premise asked
        exact derived.mono (Finset.union_subset_union (subset_refl _) (by simp))
    | @lambda _ _ body domain codomain bodyTyped =>
        simp only [isObjectPattern] at object
        cases domain with
        | base sort =>
            obtain ⟨inner, innerShape, rfl⟩ := typeGoal_arrow_base shape
            have okInner : BoundOK (.base sort :: bound) := by
              intro type member
              rcases List.mem_cons.mp member with rfl | rest
              · exact Or.inl ⟨sort, rfl⟩
              · exact ok type rest
            have derived := derives_of_hasType bodyTyped object okInner innerShape
            rw [baseSet_cons_base] at derived
            refine derived.mono ?_
            intro name member
            simp only [Finset.mem_union, Finset.mem_insert] at member ⊢
            tauto
        | multiBinder inner =>
            cases inner with
            | base sort =>
                obtain ⟨inner, innerShape, rfl⟩ := typeGoal_arrow_multi shape
                have okInner : BoundOK (.multiBinder (.base sort) :: bound) := by
                  intro type member
                  rcases List.mem_cons.mp member with rfl | rest
                  · exact Or.inr rfl
                  · exact ok type rest
                have derived := derives_of_hasType bodyTyped object okInner innerShape
                refine derived.mono ?_
                intro name member
                simp only [Finset.mem_union, Finset.mem_insert, mem_baseSet,
                  List.mem_cons, reduceCtorEq, false_or] at member ⊢
                tauto
            | _ => simp [typeGoal] at shape
        | _ => simp [typeGoal] at shape
    | @multiLambda _ arity _ body domain codomain bodyTyped =>
        simp only [isObjectPattern] at object
        cases domain with
        | base sort =>
            obtain ⟨inner, innerShape, rfl⟩ := typeGoal_arrow_multi shape
            have okInner : BoundOK (List.replicate arity (.base sort) ++ bound) := by
              intro type member
              rcases List.mem_append.mp member with replicated | rest
              · exact Or.inl ⟨sort, (List.eq_of_mem_replicate replicated)⟩
              · exact ok type rest
            have derived := derives_of_hasType bodyTyped object okInner innerShape
            refine derived.mono ?_
            intro name member
            simp only [Finset.mem_union, Finset.mem_insert, mem_baseSet, List.mem_append,
              List.mem_replicate] at member ⊢
            rcases member with fromInner | ⟨_, equal⟩ | fromBound
            · exact Or.inl (Or.inr fromInner)
            · cases equal
              exact Or.inl (Or.inl rfl)
            · exact Or.inr fromBound
        | _ => simp [typeGoal] at shape
    | subst _ _ => simp [isObjectPattern] at object
    | collection _ => simp [typeGoal] at shape
    | @collectionConstructor _ rule parameterName collectionType elements rest elementType
        member parameters _ =>
        simp only [typeGoal, Option.some.injEq] at shape
        subst shape
        refine .clause (List.mem_map.mpr ⟨rule, member, rfl⟩) fun premise premiseMember => ?_
        have declaredParameters := ((GrammarRule.bareParams_cons_iff _ _ _).mp parameters).2
        simp [ruleClause, declaredParameters, paramGoal, typeGoal] at premiseMember

  theorem derives_of_arguments {bound : List TypeExpr} {arguments : List Pattern}
      {params : List TermParam}
      (typed : ArgumentsHaveTypes language (fun _ => none) bound arguments params)
      (objects : isObjectPatternList arguments = true) (ok : BoundOK bound) :
      ∀ param ∈ params, ∀ goal, paramGoal param = some (some goal) →
        Derives (clauses language) (goal.1 ∪ baseSet bound) goal.2 := by
    cases typed with
    | nil => intro param member; cases member
    | @cons _ argument arguments parameter parameters expected _ declared argumentTyped rest =>
        simp only [isObjectPatternList, Bool.and_eq_true] at objects
        intro param member goal asked
        rcases List.mem_cons.mp member with rfl | inRest
        · exact derives_of_hasType argumentTyped objects.1 ok
            (paramGoal_typeGoal declared asked)
        · exact derives_of_arguments rest objects.2 ok param inRest goal asked
end

/-! ## Soundness: a derivation yields a closed pattern -/

/-- A closed pattern of a supported type, given patterns for its goal. -/
theorem exists_typed (type : TypeExpr) :
    ∀ (result : Option (Finset String × String)), typeGoal type = some result →
    ∀ (hypotheses : Finset String),
      (∀ goal, result = some goal → ∀ larger : List TypeExpr,
        (∀ name ∈ goal.1 ∪ hypotheses, TypeExpr.base name ∈ larger) →
        ∃ pattern, isObjectPattern pattern = true ∧
          HasType language (fun _ => none) larger pattern (.base goal.2)) →
    ∀ bound : List TypeExpr, (∀ name ∈ hypotheses, TypeExpr.base name ∈ bound) →
      ∃ pattern, isObjectPattern pattern = true ∧
        HasType language (fun _ => none) bound pattern type ∧
        (∀ domain codomain, type = .arrow (.base domain) codomain →
          ∃ body, pattern = .lambda none body) ∧
        (∀ domain codomain, type = .arrow (.multiBinder (.base domain)) codomain →
          ∃ arity body, pattern = .multiLambda arity [] body) := by
  induction type with
  | base sort =>
      intro result shape hypotheses body bound covered
      simp only [typeGoal, Option.some.injEq] at shape
      subst shape
      obtain ⟨pattern, object, typed⟩ := body (∅, sort) rfl bound (by simpa using covered)
      exact ⟨pattern, object, typed, by simp, by simp⟩
  | collection kind element =>
      intro _ _ _ _ bound _
      exact ⟨.collection kind [] none, by simp [isObjectPattern, isObjectPatternList],
        .collection (.nil bound element), by simp, by simp⟩
  | multiBinder inner _ => intro result shape; simp [typeGoal] at shape
  | arrow domain codomain _ codomainIh =>
      intro result shape hypotheses body bound covered
      have arrowCase : ∀ sort, (typeGoal codomain).map
          (Option.map fun goal => (insert sort goal.1, goal.2)) = some result →
          ∃ inner, typeGoal codomain = some inner ∧
            result = inner.map fun goal => (insert sort goal.1, goal.2) := by
        intro sort mapped
        cases inner : typeGoal codomain with
        | none => simp [inner] at mapped
        | some inner' =>
            simp only [inner, Option.map_some, Option.some.injEq] at mapped
            exact ⟨inner', rfl, mapped.symm⟩
      have innerBody : ∀ sort (inner : Option (Finset String × String)),
          result = inner.map (fun goal => (insert sort goal.1, goal.2)) →
          ∀ goal, inner = some goal → ∀ larger : List TypeExpr,
            (∀ name ∈ goal.1 ∪ insert sort hypotheses, TypeExpr.base name ∈ larger) →
            ∃ pattern, isObjectPattern pattern = true ∧
              HasType language (fun _ => none) larger pattern (.base goal.2) := by
        intro sort inner resultEq goal innerEq larger covers
        subst innerEq
        apply body (insert sort goal.1, goal.2) (by simp [resultEq]) larger
        intro name member
        apply covers
        simp only [Finset.mem_union, Finset.mem_insert] at member ⊢
        tauto
      have coveredInner : ∀ sort, ∀ name ∈ insert sort hypotheses,
          TypeExpr.base name ∈ TypeExpr.base sort :: bound := by
        intro sort name member
        rcases Finset.mem_insert.mp member with rfl | old
        · exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (covered name old)
      cases domain with
      | base sort =>
          obtain ⟨inner, innerShape, resultEq⟩ := arrowCase sort shape
          obtain ⟨pattern, object, typed, _, _⟩ := codomainIh inner innerShape
            (insert sort hypotheses) (innerBody sort inner resultEq) (.base sort :: bound)
            (coveredInner sort)
          refine ⟨.lambda none pattern, by simpa [isObjectPattern] using object,
            .lambda typed, fun _ _ _ => ⟨pattern, rfl⟩, by simp⟩
      | multiBinder innerDomain =>
          cases innerDomain with
          | base sort =>
              obtain ⟨inner, innerShape, resultEq⟩ := arrowCase sort shape
              obtain ⟨pattern, object, typed, _, _⟩ := codomainIh inner innerShape
                (insert sort hypotheses) (innerBody sort inner resultEq)
                (List.replicate 1 (.base sort) ++ bound) (coveredInner sort)
              refine ⟨.multiLambda 1 [] pattern, by simpa [isObjectPattern] using object,
                .multiLambda typed, by simp, fun _ _ _ => ⟨1, pattern, rfl⟩⟩
          | _ => simp [typeGoal] at shape
      | _ => simp [typeGoal] at shape

/-- Arguments for every supported parameter list, given patterns for its goals. -/
theorem exists_arguments (params : List TermParam)
    (supported : ∀ param ∈ params, (paramGoal param).isSome = true)
    (hypotheses : Finset String)
    (body : ∀ param ∈ params, ∀ goal, paramGoal param = some (some goal) →
      ∀ larger : List TypeExpr, (∀ name ∈ goal.1 ∪ hypotheses, TypeExpr.base name ∈ larger) →
        ∃ pattern, isObjectPattern pattern = true ∧
          HasType language (fun _ => none) larger pattern (.base goal.2))
    (bound : List TypeExpr) (covered : ∀ name ∈ hypotheses, TypeExpr.base name ∈ bound) :
    ∃ arguments, isObjectPatternList arguments = true ∧
      ArgumentsHaveTypes language (fun _ => none) bound arguments params := by
  induction params with
  | nil => exact ⟨[], rfl, .nil⟩
  | cons param params ih =>
      obtain ⟨arguments, objects, typed⟩ := ih
        (fun param member => supported param (List.mem_cons_of_mem _ member))
        (fun param member => body param (List.mem_cons_of_mem _ member))
      obtain ⟨result, asked⟩ := Option.isSome_iff_exists.mp (supported param List.mem_cons_self)
      have paramBody := body param List.mem_cons_self
      have build : ∀ expected, parameterType? param = some expected →
          ∃ argument, isObjectPattern argument = true ∧
            HasType language (fun _ => none) bound argument expected ∧
            (∀ domain codomain, expected = .arrow (.base domain) codomain →
              ∃ body, argument = .lambda none body) ∧
            (∀ domain codomain, expected = .arrow (.multiBinder (.base domain)) codomain →
              ∃ arity body, argument = .multiLambda arity [] body) := by
        intro expected declared
        exact exists_typed expected result (paramGoal_typeGoal declared asked) hypotheses
          (fun goal resultEq => paramBody goal (resultEq ▸ asked)) bound covered
      cases param with
      | simple name type =>
          obtain ⟨argument, object, typed', _, _⟩ := build type rfl
          exact ⟨argument :: arguments, by simp [isObjectPatternList, object, objects],
            .cons trivial rfl typed' typed⟩
      | abstractionNamed binder name type =>
          cases type with
          | base sort =>
              obtain ⟨argument, object, typed', lambdaShape, _⟩ := build _ rfl
              obtain ⟨inner, rfl⟩ := lambdaShape sort (.base sort) rfl
              exact ⟨_ :: arguments, by simp [isObjectPatternList, objects]; simpa using object,
                .cons (by simp [MatchesParameterRepresentation]) rfl typed' typed⟩
          | arrow domain codomain =>
              cases domain with
              | base sort =>
                  obtain ⟨argument, object, typed', lambdaShape, _⟩ := build _ rfl
                  obtain ⟨inner, rfl⟩ := lambdaShape sort codomain rfl
                  exact ⟨_ :: arguments, by simp [isObjectPatternList, objects]; simpa using object,
                    .cons (by simp [MatchesParameterRepresentation]) rfl typed' typed⟩
              | _ => simp [paramGoal] at asked
          | _ => simp [paramGoal] at asked
      | multiAbstractionNamed binders name type =>
          cases type with
          | base sort =>
              obtain ⟨argument, object, typed', _, multiShape⟩ := build _ rfl
              obtain ⟨arity, inner, rfl⟩ := multiShape sort (.base sort) rfl
              exact ⟨_ :: arguments, by simp [isObjectPatternList, objects]; simpa using object,
                .cons (by simp [MatchesParameterRepresentation]) rfl typed' typed⟩
          | arrow domain codomain =>
              cases domain with
              | multiBinder innerDomain =>
                  cases innerDomain with
                  | base sort =>
                      obtain ⟨argument, object, typed', _, multiShape⟩ := build _ rfl
                      obtain ⟨arity, inner, rfl⟩ := multiShape sort codomain rfl
                      exact ⟨_ :: arguments, by simp [isObjectPatternList, objects]; simpa using object,
                        .cons (by simp [MatchesParameterRepresentation]) rfl typed' typed⟩
                  | _ => simp [paramGoal] at asked
              | _ => simp [paramGoal] at asked
          | _ => simp [paramGoal] at asked

theorem exists_pattern_of_derives (supported : Supported language) {hypotheses : Finset String}
    {sort : String} (derivation : Derives (clauses language) hypotheses sort) :
    ∀ bound : List TypeExpr, (∀ name ∈ hypotheses, TypeExpr.base name ∈ bound) →
      ∃ pattern, isObjectPattern pattern = true ∧
        HasType language (fun _ => none) bound pattern (.base sort) := by
  induction derivation with
  | hyp member =>
      intro bound covered
      obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp (covered _ member)
      exact ⟨.bvar index, rfl, .bvar lookup⟩
  | @clause hypotheses clause member _ ih =>
      intro bound covered
      obtain ⟨rule, ruleMember, rfl⟩ := List.mem_map.mp member
      have body : ∀ param ∈ rule.params, ∀ goal, paramGoal param = some (some goal) →
          ∀ larger : List TypeExpr, (∀ name ∈ goal.1 ∪ hypotheses, TypeExpr.base name ∈ larger) →
            ∃ pattern, isObjectPattern pattern = true ∧
              HasType language (fun _ => none) larger pattern (.base goal.2) := by
        intro param paramMember goal asked larger covers
        exact ih goal (List.mem_filterMap.mpr ⟨param, paramMember, by simp [asked]⟩) larger covers
      by_cases bare : UsesBareCollection rule
      · obtain ⟨name, kind, element, parameters⟩ := bare
        exact ⟨.collection kind [] none, by simp [isObjectPattern, isObjectPatternList],
          .collectionConstructor ruleMember parameters (.nil bound element)⟩
      · obtain ⟨arguments, objects, typed⟩ := exists_arguments rule.params
          (supported rule ruleMember) hypotheses body bound covered
        exact ⟨.apply rule.label arguments, by simpa [isObjectPattern] using objects,
          .constructor ruleMember bare typed⟩

/-- **Closed inhabitation is decided by the clause reading.** -/
theorem inhabited_iff (supported : Supported language) (sort : String) :
    Inhabited language sort ↔ Derives (clauses language) ∅ sort := by
  constructor
  · rintro ⟨pattern, object, typed⟩
    have derived := derives_of_hasType typed object boundOK_nil
      (goal := (∅, sort)) (by simp [typeGoal])
    simpa [baseSet] using derived
  · intro derivation
    exact exists_pattern_of_derives supported derivation [] (by simp)

theorem inhabited_iff_closure (supported : Supported language) (sort : String) :
    Inhabited language sort ↔
      sort ∈ closure (clauses language) (fuelFor (clauses language)) ∅ := by
  rw [inhabited_iff supported, derives_iff]

end Mettapedia.GSLT.LanguageDef.ClosedInhabitation
