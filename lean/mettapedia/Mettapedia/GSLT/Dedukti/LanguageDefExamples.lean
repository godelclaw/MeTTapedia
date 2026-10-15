import Mettapedia.GSLT.Dedukti.LanguageDefContextTheory
import Mettapedia.GSLT.Dedukti.TwoRoutes
import Mettapedia.GSLT.Dedukti.PureTypeSystem
import Mettapedia.GSLT.Dedukti.CousineauDowek

/-!
# The generated context theory on two theories

`holTheory` (the declared rule `term (arr a b) ⟶ term a → term b`) and the
embedding of the simply typed λ-calculus (`cdTheory simplyTyped`, the rules
`e kind (dot type) ⟶ U type` and `e type (dotpi X Y) ⟶ Π x : e type X. e type (Y x)`)
are presented by `dkLanguage`, with the names of their constants.  Both
language definitions pass validation, both theories are presented by their
rule lists, so the encoding is hosting for both at every scope
(`holTheory_encodeMap_hosting`, `simplyTyped_encodeMap_hosting`), and the
declared rules give transitions of the generated context theories
(`hol_transition`, `simplyTyped_code_transition`, `simplyTyped_product_transition`).
Beta, which the context theory of `lfLanguageDef` cannot perform, is a
transition here (`identityRedex_transition`).

The encoding covers part of the terms of `rewritingTheory` only: a variable
beyond the scope (`not_encodedAt_var`) and a constant that is not declared
(`not_encodedAt_undeclared`) have no encoding at the interface.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.Language

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFTyping (lookupBody lift)
open Mettapedia.GSLT.LanguageDef.WellSorted (parameterType? isObjectPattern isObjectPatternList)
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory)
open Mettapedia.OSLF.MeTTaIL.Syntax (Pattern GrammarRule LanguageDef)
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.Dedukti.TwoRoutes (holTheory holSig termArrow termOf arr bool)

variable {base : BasePremiseEvaluator} {names : List String} {rules : List RewriteRule}

/-! ## The constructors of every `dkLanguage` validate -/

theorem dkLanguage_typeNames : (dkLanguage names rules).typeNames = lfSorts := rfl

theorem metaName_zero : metaName 0 = "x" := by decide

theorem metaName_one : metaName 1 = "xx" := by decide

theorem dkLanguage_terms_valid :
    ∀ term ∈ (dkLanguage names rules).terms,
      LanguageDef.validateTerm (dkLanguage names rules) term = [] := by
  intro term member
  rcases List.mem_append.mp member with lf | named
  · rw [lfLanguageDef_terms] at lf
    exact lfTermRules_valid _ rfl term lf
  · obtain ⟨symbol, _, rfl⟩ := List.mem_map.mp named
    simp [nameRule, dkLanguage_typeNames, lfSorts]

/-- Discharge the side conditions of a congruence rule of a `dkLanguage`, given
the list of its constructor labels. -/
local macro "validate_congruence" rule:ident labels:ident source:str target:str : tactic =>
  `(tactic|
    (apply LanguageDef.validateRewrite_eq_nil_of_variableCongruence (source := $source)
       (target := $target)
     · rfl
     · simp [$rule:ident]
     · decide
     · decide
     · intro context
       simp [LanguageDef.validateRulePatterns, $labels:ident, Pattern.isWellScoped,
         Pattern.isWellScopedAt, Pattern.isWellScopedListAt, LanguageDef.patternFvarNames,
         Pattern.freeFvarNames, LanguageDef.patternBinderNames, LanguageDef.premiseLocallyScoped,
         LanguageDef.premiseFvarNames, LanguageDef.premisePatterns, LanguageDef.premiseForAllParams,
         LanguageDef.premiseProducedFvarNames, $rule:ident, appLeft, piLeft, lamLeft]))

/-- Discharge the side conditions of beta in a `dkLanguage`, given the list
of its constructor labels. -/
local macro "validate_beta" labels:ident : tactic =>
  `(tactic|
    (apply LanguageDef.validateRewrite_eq_nil_of_premiseFree
     · rfl
     · simp [betaRule]
     · decide
     · decide
     · intro context
       simp [LanguageDef.validateRulePatterns, $labels:ident, Pattern.isWellScoped,
         Pattern.isWellScopedAt, Pattern.isWellScopedListAt, LanguageDef.patternFvarNames,
         Pattern.freeFvarNames, LanguageDef.patternBinderNames, betaRule, betaLeft]))

/-! ## `holTheory` -/

/-- The constants of `holTheory`. -/
def holNames : List String := ["type", "bool", "arr", "term", "eq", "proof", "REFL", "ABS_THM"]

theorem holTheory_presents : Presents holTheory [termArrow] where
  undefined := fun symbol => by simp [holTheory, Theory.ofSig, holSig, lookupBody]
  rule_iff := fun _ => Iff.rfl
  leftAlgebraic := by decide
  rightDetermined := by decide

theorem holLanguage_labels : (dkLanguage holNames [termArrow]).terms.map (·.label) =
    ["SortType", "SortKind", "Srt", "Con", "Var", "Pi", "Lam", "App", "c:type", "c:bool", "c:arr",
      "c:term", "c:eq", "c:proof", "c:REFL", "c:ABS_THM"] := by decide

theorem holLanguage_validate : (dkLanguage holNames [termArrow]).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · decide
  · decide
  · decide
  · decide
  · exact dkLanguage_terms_valid
  · intro equation member
    rw [dkLanguage_equations] at member
    cases member
  · intro rewrite member
    simp only [dkLanguage, fixedRules, List.mapIdx_cons, List.mapIdx_nil, List.cons_append,
      List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · validate_beta holLanguage_labels
    · validate_congruence appFunctionRule holLanguage_labels "F" "G"
    · validate_congruence appArgumentRule holLanguage_labels "X" "Y"
    · validate_congruence piDomainRule holLanguage_labels "A" "C"
    · validate_congruence piBodyRule holLanguage_labels "B" "D"
    · validate_congruence lamDomainRule holLanguage_labels "A" "C"
    · validate_congruence lamBodyRule holLanguage_labels "B" "D"
    · apply LanguageDef.validateRewrite_eq_nil_of_premiseFree
      · rfl
      · simp [declaredRule]
      · decide
      · decide
      · intro context
        rw [holLanguage_labels]
        simp [LanguageDef.validateRulePatterns, Pattern.isWellScoped, Pattern.isWellScopedAt,
          Pattern.isWellScopedListAt, LanguageDef.patternFvarNames, Pattern.freeFvarNames,
          LanguageDef.patternBinderNames, declaredRule, toPattern, metaName_zero, metaName_one,
          termArrow, termOf, arr, encode, nameLabel]

/-- **`holTheory`, presented.** -/
def holPresentation : ValidatedLanguageDef := dkPresentation holNames [termArrow] holLanguage_validate

/-- **The encoding is hosting for `holTheory`, at every scope.** -/
theorem holTheory_encodeMap_hosting (depth : Nat) :
    (encodeMap (base := base) holTheory holLanguage_validate depth).Hosting :=
  encodeMap_hosting holTheory_presents holLanguage_validate depth

/-- The declared rule: `term (arr bool bool) ⟶ term bool → term bool`. -/
theorem hol_step : Dedukti.Step holTheory (termOf (arr bool bool)) (.pi (termOf bool) (termOf bool)) :=
  Step.root (RootStep.rule (rule := termArrow) (fun _ => bool) (List.mem_singleton.mpr rfl))

/-- **The declared rule is a transition of the generated context theory.** -/
theorem hol_transition :
    (contextTheory base holPresentation).rewrites (interface := termInterface 0)
      ⟨encode (termOf (arr bool bool)), encode_encodedAt (names := holNames) (rules := [termArrow])
        (wellScoped_of_test _ 0 rfl) (by decide)⟩
      ⟨encode (.pi (termOf bool) (termOf bool)), encode_encodedAt (names := holNames)
        (rules := [termArrow]) (wellScoped_of_test _ 0 rfl) (by decide)⟩ :=
  (dk_termStep_iff _ _).mpr ((step_encode_iff holTheory_presents).mpr ⟨_, rfl, hol_step⟩)

/-- **Beta is a transition of the generated context theory**: the redex that
the context theory of `lfLanguageDef` cannot contract
(`beta_not_in_lfPresentation`) is contracted here. -/
theorem identityRedex_transition :
    (contextTheory base holPresentation).rewrites (interface := termInterface 0)
      ⟨encode identityRedex, encode_encodedAt (names := holNames) (rules := [termArrow])
        (wellScoped_of_test _ 0 rfl) (by decide)⟩
      ⟨encode (.srt .type), encode_encodedAt (names := holNames) (rules := [termArrow])
        (wellScoped_of_test _ 0 rfl) (by decide)⟩ :=
  (dk_termStep_iff _ _).mpr ((step_encode_iff holTheory_presents).mpr
    ⟨_, rfl, Step.root (.beta (.srt .type) (.var 0) (.srt .type))⟩)

/-! ## Terms with no encoding -/

/-- **A variable beyond the scope has no encoding at the interface.** -/
theorem not_encodedAt_var (depth : Nat) :
    ¬ EncodedAt (dkLanguage names rules) depth (.var depth) := by
  intro encoded
  rcases hasType_base_inv encoded.1 encoded.2.2.1 with
    ⟨index, same, found⟩ | ⟨_, _, _, same, _, _⟩
  · simp only [encode, Pattern.bvar.injEq] at same
    subst same
    simp at found
  · simp [encode] at same

/-- **A constant that is not declared has no encoding at any interface.** -/
theorem not_encodedAt_undeclared (depth : Nat) :
    ¬ EncodedAt (dkLanguage holNames [termArrow]) depth (.con "undeclared") := by
  intro encoded
  rcases hasType_base_inv encoded.1 encoded.2.2.1 with
    ⟨_, impossible, _⟩ | ⟨rule, member, arguments, same, _, typedArguments⟩
  · simp [encode] at impossible
  · simp only [encode, Pattern.apply.injEq] at same
    obtain ⟨label, rfl⟩ := same
    rcases mem_dkLanguage_terms member with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | ⟨symbol, named, rfl⟩
    · simp [sortTypeRule] at label
    · simp [sortKindRule] at label
    · simp [srtRule] at label
    · simp only [conRule] at typedArguments
      cases typedArguments with
      | cons _ parameterType argumentTyped _ =>
          simp only [parameterType?, Option.some.injEq] at parameterType
          subst parameterType
          have object : isObjectPattern (.apply (nameLabel "undeclared") []) = true := by
            simp [isObjectPattern, isObjectPatternList]
          obtain ⟨symbol, named, same⟩ := name_inv argumentTyped object
          simp only [Pattern.apply.injEq, and_true] at same
          rw [← nameLabel_injective same] at named
          simp [holNames] at named
    · simp [varRule] at label
    · simp [piRule] at label
    · simp [lamRule] at label
    · simp [appRule] at label
    · simp only [holNames, List.mem_cons, List.not_mem_nil, or_false] at named
      rcases named with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [nameRule, nameLabel] at label

/-! ## The embedding of the simply typed λ-calculus -/

/-- The constants that `cdTheory simplyTyped` declares. -/
def simplyTypedSymbols : List Symbol :=
  [.univ .type, .univ .kind, .decode .type, .decode .kind, .code .type,
    .prod LFProfile.typeTypeType]

/-- Their names. -/
def simplyTypedNames : List String := simplyTypedSymbols.map Symbol.name

/-- **The names are those of the declared constants.** -/
theorem mem_simplyTypedNames (symbol : Symbol) :
    symbol.name ∈ simplyTypedNames ↔ (Symbol.declaredType simplyTyped symbol).isSome := by
  cases symbol with
  | univ level => cases level <;> decide
  | decode level => cases level <;> decide
  | code level => cases level <;> decide
  | prod rule =>
      obtain ⟨domain, codomain, result⟩ := rule
      cases domain <;> cases codomain <;> cases result <;> decide

/-- The rules of `cdTheory simplyTyped`. -/
def simplyTypedRules : List RewriteRule := [codeRule .type .kind, prodRule LFProfile.typeTypeType]

theorem simplyTyped_presents : Presents (cdTheory simplyTyped) simplyTypedRules where
  undefined := fun _ => rfl
  rule_iff := fun rule => by
    constructor
    · intro member
      cases member with
      | @code source target assigned =>
          cases source with
          | type =>
              cases (Option.some.inj assigned : Srt.kind = target)
              exact List.mem_cons_self
          | kind => cases assigned
      | @prod product member =>
          cases List.mem_singleton.mp member
          exact List.mem_cons_of_mem _ List.mem_cons_self
    · intro member
      simp only [simplyTypedRules, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact .code rfl
      · exact .prod (List.mem_singleton.mpr rfl)
  leftAlgebraic := by decide
  rightDetermined := by decide

theorem simplyTypedLanguage_labels :
    (dkLanguage simplyTypedNames simplyTypedRules).terms.map (·.label) =
      ["SortType", "SortKind", "Srt", "Con", "Var", "Pi", "Lam", "App", "c:Utype", "c:Ukind",
        "c:etype", "c:ekind", "c:dottype", "c:dotpi_type_type_type"] := by decide

theorem simplyTypedLanguage_validate :
    (dkLanguage simplyTypedNames simplyTypedRules).validate = [] := by
  apply LanguageDef.validate_eq_nil_of_rows
  · decide
  · decide
  · decide
  · decide
  · exact dkLanguage_terms_valid
  · intro equation member
    rw [dkLanguage_equations] at member
    cases member
  · intro rewrite member
    simp only [dkLanguage, fixedRules, simplyTypedRules, List.mapIdx_cons, List.mapIdx_nil,
      List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · validate_beta simplyTypedLanguage_labels
    · validate_congruence appFunctionRule simplyTypedLanguage_labels "F" "G"
    · validate_congruence appArgumentRule simplyTypedLanguage_labels "X" "Y"
    · validate_congruence piDomainRule simplyTypedLanguage_labels "A" "C"
    · validate_congruence piBodyRule simplyTypedLanguage_labels "B" "D"
    · validate_congruence lamDomainRule simplyTypedLanguage_labels "A" "C"
    · validate_congruence lamBodyRule simplyTypedLanguage_labels "B" "D"
    · apply LanguageDef.validateRewrite_eq_nil_of_premiseFree
      · rfl
      · simp [declaredRule]
      · decide
      · decide
      · intro context
        rw [simplyTypedLanguage_labels]
        simp [LanguageDef.validateRulePatterns, Pattern.isWellScoped, Pattern.isWellScopedAt,
          Pattern.isWellScopedListAt, LanguageDef.patternFvarNames, Pattern.freeFvarNames,
          LanguageDef.patternBinderNames, declaredRule, toPattern, codeRule, El, sortCode,
          codeType, encode, nameLabel, Symbol.name]
    · apply LanguageDef.validateRewrite_eq_nil_of_premiseFree
      · rfl
      · simp [declaredRule]
      · decide
      · decide
      · intro context
        rw [simplyTypedLanguage_labels]
        simp [LanguageDef.validateRulePatterns, Pattern.isWellScoped, Pattern.isWellScopedAt,
          Pattern.isWellScopedListAt, LanguageDef.patternFvarNames, Pattern.freeFvarNames,
          LanguageDef.patternBinderNames, declaredRule, toPattern, prodRule, El, prodCode,
          LFProfile.typeTypeType, metaName_zero, metaName_one, encode, nameLabel, Symbol.name]

/-- **The embedding of the simply typed λ-calculus, presented.** -/
def simplyTypedPresentation : ValidatedLanguageDef :=
  dkPresentation simplyTypedNames simplyTypedRules simplyTypedLanguage_validate

/-- **The encoding is hosting for the embedding of the simply typed
λ-calculus, at every scope.** -/
theorem simplyTyped_encodeMap_hosting (depth : Nat) :
    (encodeMap (base := base) (cdTheory simplyTyped) simplyTypedLanguage_validate depth).Hosting :=
  encodeMap_hosting simplyTyped_presents simplyTypedLanguage_validate depth

/-- The code rule: `e kind (dot type) ⟶ U type`. -/
theorem simplyTyped_code_step :
    Dedukti.Step (cdTheory simplyTyped) (El .kind (sortCode .type)) (codeType .type) :=
  Step.root (RootStep.rule (rule := codeRule .type .kind) (fun _ => .srt .type) (.code rfl))

/-- The product rule: `e type (dotpi X Y) ⟶ Π x : e type X. e type (Y x)`. -/
theorem simplyTyped_product_step (domain family : Term) :
    Dedukti.Step (cdTheory simplyTyped) (El .type (prodCode LFProfile.typeTypeType domain family))
      (.pi (El .type domain) (El .type (.app (lift 1 0 family) (.var 0)))) := by
  have root := RootStep.rule (theory := cdTheory simplyTyped) (rule := prodRule LFProfile.typeTypeType)
    (fun index => if index = 0 then family else domain) (.prod (List.mem_singleton.mpr rfl))
  rw [inst_prodRule_lhs, inst_prodRule_rhs] at root
  exact Step.root root

/-- **The code rule is a transition of the generated context theory.** -/
theorem simplyTyped_code_transition :
    (contextTheory base simplyTypedPresentation).rewrites (interface := termInterface 0)
      ⟨encode (El .kind (sortCode .type)), encode_encodedAt (names := simplyTypedNames)
        (rules := simplyTypedRules) (wellScoped_of_test _ 0 rfl) (by decide)⟩
      ⟨encode (codeType .type), encode_encodedAt (names := simplyTypedNames)
        (rules := simplyTypedRules) (wellScoped_of_test _ 0 rfl) (by decide)⟩ :=
  (dk_termStep_iff _ _).mpr ((step_encode_iff simplyTyped_presents).mpr
    ⟨_, rfl, simplyTyped_code_step⟩)

/-- The code of the constant family `λ x : e type X. X` over a type code `X`,
the variable of the scope. -/
def constantProduct : Term :=
  El .type (prodCode LFProfile.typeTypeType (.var 0) (.lam (El .type (.var 0)) (.var 1)))

/-- **The product rule is a transition of the generated context theory**, at
the scope of one variable. -/
theorem simplyTyped_product_transition :
    (contextTheory base simplyTypedPresentation).rewrites (interface := termInterface 1)
      ⟨encode constantProduct, encode_encodedAt (names := simplyTypedNames)
        (rules := simplyTypedRules) (wellScoped_of_test _ 1 rfl) (by decide)⟩
      ⟨encode (.pi (El .type (.var 0))
          (El .type (.app (lift 1 0 (.lam (El .type (.var 0)) (.var 1))) (.var 0)))),
        encode_encodedAt (names := simplyTypedNames) (rules := simplyTypedRules)
          (wellScoped_of_test _ 1 rfl) (by decide)⟩ :=
  (dk_termStep_iff _ _).mpr ((step_encode_iff simplyTyped_presents).mpr
    ⟨_, rfl, simplyTyped_product_step _ _⟩)

#print axioms holLanguage_validate
#print axioms holTheory_encodeMap_hosting
#print axioms hol_transition
#print axioms identityRedex_transition
#print axioms simplyTypedLanguage_validate
#print axioms simplyTyped_encodeMap_hosting
#print axioms simplyTyped_code_transition
#print axioms simplyTyped_product_transition
#print axioms mem_simplyTypedNames
#print axioms not_encodedAt_var
#print axioms not_encodedAt_undeclared

end Mettapedia.GSLT.Dedukti.Language
