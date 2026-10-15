import Mettapedia.OSLF.NativeTypes.Generation.BindingCarrierSemantics
import Mettapedia.OSLF.NativeTypes.Generation.NativeDeclarations

/-!
# An ordinary authored arrow need not be a native function carrier

This presentation has one base sort with variables and no operations that
produce it. Its higher-order source arrow has only a projection body.
The genuine presheaf function object additionally contains evaluation of a
contextual function. These points differ at a larger ambient context. Thus
native header formation alone cannot identify ordinary authored arrows with
native function objects.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingCarrierSemantics.ArrowCounterexample

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.GSLT.LanguageDef.WellSorted
open Mettapedia.OSLF.Binding
open _root_.CategoryTheory
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open BindingSubstitutionAlgebra IntrinsicScopedConditionalPresheaf MultiBinderPresheaf

def base : TypeExpr := .base "A"
def arrow : TypeExpr := .arrow base base
def higher : TypeExpr := .arrow arrow base

def consumer : GrammarRule where
  label := "Consume"
  category := "B"
  params := [.simple "function" higher]
  syntaxPattern := []

def language : LanguageDef where
  name := "OrdinaryArrowData"
  types := ["A", "B"]
  terms := [consumer]
  equations := []
  rewrites := []

theorem native_headers_admitted : (NativeSignature.install? language).isSome = true := by decide
theorem binder_profile_rejected : checkProfile language = false := by decide

private theorem source_body_unique {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language FreeTypeContext.empty [arrow, base] pattern type)
    (result : type = base) (object : isObjectPattern pattern = true) : pattern = .bvar 1 := by
  cases typed with
  | @bvar _ index _ lookup =>
      subst_vars
      cases index with
      | zero => simp [base, arrow] at lookup
      | succ index =>
          cases index with
          | zero => rfl
          | succ index => simp at lookup
  | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | constructor member _ _ =>
      simp only [language, List.mem_singleton] at member
      subst_vars
      simp [consumer, base] at result
  | lambda => simp [base] at result
  | multiLambda => simp [base] at result
  | subst => simp [isObjectPattern] at object
  | collection => simp [base] at result
  | collectionConstructor member shape _ =>
      simp only [language, List.mem_singleton] at member
      subst_vars
      simp [consumer, base] at result

abbrev Source :=
  {pattern : Pattern //
    HasType language FreeTypeContext.empty [base] pattern higher ∧
      pattern.hasCanonicalBinderMetadata = true ∧ isObjectPattern pattern = true}

private theorem arrow_source_unique {pattern : Pattern} {type : TypeExpr}
    (typed : HasType language FreeTypeContext.empty [base] pattern type)
    (result : type = higher) (canonical : pattern.hasCanonicalBinderMetadata = true)
    (object : isObjectPattern pattern = true) : pattern = .lambda none (.bvar 1) := by
  cases typed with
  | @bvar _ index _ lookup =>
      subst_vars
      cases index <;> simp [higher, base] at lookup
  | fvar lookup => simp [FreeTypeContext.empty] at lookup
  | constructor => simp [higher] at result
  | @lambda _ binder body domain codomain bodyTyped =>
      simp only [higher, TypeExpr.arrow.injEq] at result
      obtain ⟨rfl, rfl⟩ := result
      cases binder with
      | none => exact congrArg (Pattern.lambda none) (source_body_unique bodyTyped rfl object)
      | some name => simp [Pattern.hasCanonicalBinderMetadata] at canonical
  | multiLambda => simp [higher, arrow] at result
  | subst => simp [isObjectPattern] at object
  | collection => simp [higher] at result
  | collectionConstructor => simp [higher] at result

theorem source_unique (source : Source) : source.val = .lambda none (.bvar 1) :=
  arrow_source_unique source.2.1 rfl source.2.2.1 source.2.2.2

abbrev A := algebra language
abbrev P := programs A "A"
abbrev X := Opposite.op (ContextObject.ofList A.substitution.toClone ["A"])
abbrev Y := Opposite.op (ContextObject.ofList A.substitution.toClone ["A", "A"])

def x : P.obj X := by
  change (index : Fin 1) → Term (Mettapedia.GSLT.Poly.BindingLanguage.signature language)
    ["A"] (["A"].get index)
  exact fun index => Fin.cases (.var .zero) (fun later => Fin.elim0 later) index
def y : P.obj Y := by
  change (index : Fin 1) → Term (Mettapedia.GSLT.Poly.BindingLanguage.signature language)
    ["A", "A"] (["A"].get index)
  exact fun index => Fin.cases (.var (.succ .zero)) (fun later => Fin.elim0 later) index

def inclusion : X ⟶ Y :=
  Opposite.op (environmentArrow A (fun _ v => match v with | .zero => .var .zero))

/-- A contextual constant is reindexed with its actual ambient point. -/
def constantAt {C : Type} [Category C] (F G : C ⥤ Type)
    {context : C} (point : G.obj context) : (F.functorHom G).obj context where
  app target reindex := TypeCat.ofHom (fun _ => G.map reindex point)
  naturality step reindex := by
    ext argument
    change G.map (reindex ≫ step) point = G.map step (G.map reindex point)
    exact G.map_comp_apply reindex step point

/-- Evaluation of a genuine contextual function at a retained ambient point. -/
def evaluateAt {C : Type} [Category C] (F : C ⥤ Type)
    {context : C} (point : F.obj context) :
    ((F.functorHom F).functorHom F).obj context where
  app target reindex := TypeCat.ofHom (fun function =>
    (function.app target (𝟙 target)) (F.map reindex point))
  naturality step reindex := by
    ext function
    change (function.app _ (step ≫ 𝟙 _)) (F.map (reindex ≫ step) point) =
      F.map step ((function.app _ (𝟙 _)) (F.map reindex point))
    rw [Category.comp_id, F.map_comp_apply]
    have natural := ConcreteCategory.congr_hom
      (function.naturality step (𝟙 _)) (F.map reindex point)
    change (function.app _ (𝟙 _ ≫ step)) (F.map step (F.map reindex point)) =
      F.map step ((function.app _ (𝟙 _)) (F.map reindex point)) at natural
    simpa only [Category.id_comp] using natural

def constant : ((P.functorHom P).functorHom P).obj X := constantAt _ _ x
def evaluate : ((P.functorHom P).functorHom P).obj X := evaluateAt P x
def otherFunction : (P.functorHom P).obj Y := constantAt P P y

theorem native_functions_distinct : constant ≠ evaluate := by
  intro same
  have readout := congrArg (fun function =>
    ((function.app Y inclusion) otherFunction) (0 : Fin 1)) same
  change Term.var (S := Mettapedia.GSLT.Poly.BindingLanguage.signature language)
      (Γ := ["A", "A"]) (Var.zero) = Term.var (Var.succ Var.zero) at readout
  cases readout

/-- An adequate bijection is impossible for the ordinary authored arrow
accepted by declaration decoding, even using contextual presheaf Π. -/
theorem no_arrow_carrier_equivalence :
    ¬ Nonempty (Source ≃ ((P.functorHom P).functorHom P).obj X) := by
  rintro ⟨equivalence⟩
  have sourceEqual : equivalence.symm constant = equivalence.symm evaluate := by
    apply Subtype.ext
    rw [source_unique, source_unique]
  exact native_functions_distinct (equivalence.symm.injective sourceEqual)

end Mettapedia.OSLF.NativeTypes.Generation.BindingCarrierSemantics.ArrowCounterexample
