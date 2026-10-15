import Mettapedia.GSLT.LanguageDef.WellSorted

/-!
# Typed equation and rewrite schemas

`LanguageDef.validate` checks names, arities, scope, and wildcard flow.  The
categorical presentation layer additionally needs the mathematical sorting
judgment for the two sides of every equation and rewrite.  This module states
that judgment over the exact authored declaration; it does not copy or
reinterpret the language definition.
-/

namespace Mettapedia.GSLT.LanguageDef

open Mettapedia.OSLF.MeTTaIL.Syntax
open StructuralMorphism
open WellSorted

namespace WellSorted.FreeTypeContext

/-- Interpret an authored schema context by first-match lookup. -/
def ofList : List (String × TypeExpr) → FreeTypeContext
  | [], _ => none
  | (name, type) :: context, sought =>
      if name = sought then some type else ofList context sought

@[simp]
theorem ofList_nil : ofList [] = empty := rfl

/-- Mapping schema annotations commutes with interpreting the schema
context. -/
theorem ofList_mapTypeContext (symbols : LanguageDefSymbolMap)
    (context : List (String × TypeExpr)) :
    ofList (mapTypeContext symbols context) = (ofList context).map symbols := by
  funext sought
  induction context with
  | nil => rfl
  | cons entry context inductionHypothesis =>
      rcases entry with ⟨name, type⟩
      by_cases equality : name = sought
      · subst sought
        simp [ofList, mapTypeContext, FreeTypeContext.map]
      · simp only [mapTypeContext, List.map_cons, ofList, equality, if_false,
          FreeTypeContext.map]
        exact inductionHypothesis

/-- Materialize exactly the supplied finite lookup footprint. Repeated names
retain their source order; every retained row comes from the same context. -/
def entriesOn (context : FreeTypeContext) (names : List String) : List (String × TypeExpr) :=
  names.filterMap fun name => (context name).map (name, ·)

/-- Finite materialization preserves precisely the requested lookups. -/
theorem ofList_entriesOn (context : FreeTypeContext) (names : List String) (name : String) :
    ofList (context.entriesOn names) name =
      if name ∈ names then context name else none := by
  induction names with
  | nil => rfl
  | cons first rest ih =>
      cases value : context first with
      | none =>
          have tail : context.entriesOn (first :: rest) = context.entriesOn rest := by
            simp [entriesOn, value]
          rw [tail, ih]
          by_cases equal : first = name
          · subst first
            simp [value]
          · simp only [List.mem_cons, Ne.symm equal, false_or]
      | some type =>
          have tail : context.entriesOn (first :: rest) =
              (first, type) :: context.entriesOn rest := by
            simp [entriesOn, value]
          rw [tail]
          by_cases equal : first = name
          · subst first
            simp [ofList, value]
          · simp only [ofList, equal, if_false, ih, List.mem_cons,
              Ne.symm equal, false_or]

/-- A finite view reads an existing context; it assigns no new types. -/
theorem entriesOn_mem_iff (context : FreeTypeContext) (names : List String)
    (name : String) (type : TypeExpr) :
    (name, type) ∈ context.entriesOn names ↔ name ∈ names ∧ context name = some type := by
  simp only [entriesOn, List.mem_filterMap]
  constructor
  · rintro ⟨other, member, encoded⟩
    cases value : context other with
    | none => simp [value] at encoded
    | some result =>
        simp only [value, Option.map_some, Option.some.injEq, Prod.mk.injEq] at encoded
        rcases encoded with ⟨rfl, rfl⟩
        exact ⟨member, value⟩
  · rintro ⟨member, value⟩
    exact ⟨name, member, by simp [value]⟩

#print axioms ofList_entriesOn
#print axioms entriesOn_mem_iff

end WellSorted.FreeTypeContext

namespace WellSorted

/-- Typing one pattern is unchanged by retaining only the free names that
occur in that pattern. This uses the existing free-context transport theorem. -/
theorem HasType.finiteFree_iff (language : LanguageDef)
    (free : FreeTypeContext) (bound : List TypeExpr)
    (pattern : Pattern) (expected : TypeExpr) :
    HasType language (FreeTypeContext.ofList (free.entriesOn pattern.freeFvarNames))
      bound pattern expected ↔ HasType language free bound pattern expected := by
  constructor
  · intro typed
    exact typed.recontextualizeFree fun member lookup => by
      simpa only [FreeTypeContext.ofList_entriesOn, if_pos member] using lookup
  · intro typed
    exact typed.recontextualizeFree fun member lookup => by
      simpa only [FreeTypeContext.ofList_entriesOn, if_pos member] using lookup

#print axioms HasType.finiteFree_iff

end WellSorted

/-- Two schema patterns inhabit one common type under the declaration's
authored metavariable context. -/
def SchemaSidesWellSorted (language : LanguageDef)
    (typeContext : List (String × TypeExpr))
    (left right : Pattern) : Prop :=
  ∃ type,
    HasType language (FreeTypeContext.ofList typeContext) [] left type ∧
    HasType language (FreeTypeContext.ofList typeContext) [] right type

/-- Sorting of one authored bidirectional equation. -/
def EquationWellSorted (language : LanguageDef) (equation : Equation) : Prop :=
  SchemaSidesWellSorted language equation.typeContext
    equation.left equation.right

/-- Sorting of one authored directional rewrite. -/
def RewriteWellSorted (language : LanguageDef) (rewrite : RewriteRule) : Prop :=
  SchemaSidesWellSorted language rewrite.typeContext rewrite.left rewrite.right

/-- Every equation in the exact declaration is sorted. -/
def EquationsWellSorted (presentation : ValidatedLanguageDef) : Prop :=
  ∀ equation ∈ presentation.language.equations,
    EquationWellSorted presentation.language equation

/-- Every rewrite in the exact declaration is sorted. -/
def RewritesWellSorted (presentation : ValidatedLanguageDef) : Prop :=
  ∀ rewrite ∈ presentation.language.rewrites,
    RewriteWellSorted presentation.language rewrite

/-! ## Validation consequences for authored equations -/

/-- Every equation selected from a validated language passes the exact
per-equation component of the language gate. -/
theorem validateEquation_eq_nil_of_validate_eq_nil
    (language : LanguageDef) (valid : language.validate = [])
    (equation : Equation) (membership : equation ∈ language.equations) :
    language.validateEquation equation = [] := by
  have equationErrors :
      language.equations.flatMap (language.validateEquation ·) = [] := by
    unfold LanguageDef.validate at valid
    simp only [List.append_eq_nil_iff] at valid
    aesop
  exact (List.flatMap_eq_nil_iff.mp equationErrors) equation membership

/-- Every type-context entry of an accepted equation mentions only sorts
declared by the same authored language. -/
theorem equationTypeContext_baseName_mem_of_validate_eq_nil
    (language : LanguageDef) (valid : language.validate = [])
    (equation : Equation) (equationMembership : equation ∈ language.equations)
    (entry : String × TypeExpr) (entryMembership : entry ∈ equation.typeContext)
    (name : String) (nameMembership : name ∈ entry.2.baseNames) :
    name ∈ language.typeNames := by
  have equationClean := validateEquation_eq_nil_of_validate_eq_nil
    language valid equation equationMembership
  unfold LanguageDef.validateEquation at equationClean
  simp only [List.append_eq_nil_iff] at equationClean
  apply LanguageDef.baseName_mem_of_validateTypeExpr_eq_nil
    language.typeNames s!"equation {equation.name}" entry.2 ?_ nameMembership
  aesop

namespace SchemaSidesWellSorted

/-- Strict structural theory maps preserve schema sorting. -/
theorem map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target)
    {typeContext : List (String × TypeExpr)} {left right : Pattern}
    (sorted : SchemaSidesWellSorted source.language typeContext left right) :
    SchemaSidesWellSorted target.language
      (mapTypeContext morphism.symbols typeContext)
      (mapPattern morphism.symbols left)
      (mapPattern morphism.symbols right) := by
  rcases sorted with ⟨type, leftTyped, rightTyped⟩
  refine ⟨mapTypeExpr morphism.symbols type, ?_, ?_⟩
  · simpa [FreeTypeContext.ofList_mapTypeContext] using leftTyped.map morphism
  · simpa [FreeTypeContext.ofList_mapTypeContext] using rightTyped.map morphism

end SchemaSidesWellSorted

namespace EquationWellSorted

/-- An authored equation remains sorted under a strict presentation map. -/
theorem map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) (equation : Equation)
    (sorted : EquationWellSorted source.language equation) :
    EquationWellSorted target.language
      (Mettapedia.GSLT.LanguageDef.mapEquation morphism.symbols equation) := by
  exact SchemaSidesWellSorted.map morphism sorted

end EquationWellSorted

namespace RewriteWellSorted

/-- An authored rewrite remains sorted under a strict presentation map. -/
theorem map {source target : ValidatedLanguageDef}
    (morphism : StructuralMorphism source target) (rewrite : RewriteRule)
    (sorted : RewriteWellSorted source.language rewrite) :
    RewriteWellSorted target.language
      (mapRewriteRule morphism.symbols rewrite) := by
  exact SchemaSidesWellSorted.map morphism sorted

end RewriteWellSorted

/-! ## Strict-core rho controls -/

/-- The equation authored by `rhoCalc` is genuinely sorted in its declared
name fiber.  This is stronger than the name/arity checks performed by
`LanguageDef.validate`. -/
theorem rhoCalc_equations_wellSorted :
    ∀ equation ∈ rhoCalc.equations, EquationWellSorted rhoCalc equation := by
  intro equation membership
  simp only [rhoCalc, List.mem_singleton] at membership
  subst equation
  refine ⟨TypeExpr.name, ?_, ?_⟩
  · change HasType rhoCalc (FreeTypeContext.ofList [("N", TypeExpr.name)]) []
      (.apply "NQuote" [.apply "PDrop" [.fvar "N"]]) TypeExpr.name
    apply HasType.constructor (rule := rhoCalc.terms[2])
    · simp [rhoCalc]
    · simp [rhoCalc, UsesBareCollection, TypeExpr.proc, TypeExpr.name,
        TypeExpr.baseType]
    · apply ArgumentsHaveTypes.cons
      · trivial
      · rfl
      · apply HasType.constructor (rule := rhoCalc.terms[1])
        · simp [rhoCalc]
        · simp [rhoCalc, UsesBareCollection, TypeExpr.proc, TypeExpr.name,
            TypeExpr.baseType]
        · apply ArgumentsHaveTypes.cons
          · trivial
          · rfl
          · apply HasType.fvar
            simp [FreeTypeContext.ofList]
          · exact ArgumentsHaveTypes.nil
      · exact ArgumentsHaveTypes.nil
  · change HasType rhoCalc (FreeTypeContext.ofList [("N", TypeExpr.name)]) []
      (.fvar "N") TypeExpr.name
    apply HasType.fvar
    simp [FreeTypeContext.ofList]

end Mettapedia.GSLT.LanguageDef
