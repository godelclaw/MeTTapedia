import Mettapedia.GSLT.LanguageDef.BindingSignatureSameTerms
import Mettapedia.GSLT.Parsing.GrammarPresentationTransport
import Mettapedia.OSLF.Syntax.BindingCloneContextComparison

/-!
# Concrete notation changes preserve the generated binding syntax

The grammar transport changes actual terminal declarations. Its derived
operator map retains every parameter scope, including single and repeated
binders. Intrinsic terms and their typed substitutions are transported to the
new declaration-derived signature. No second constructor list is supplied.

The corresponding context functor preserves finite products. This is syntax
transport; preservation of an equation quotient or of operational firing must
add the relevant equation or rule-transport laws.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.BindingSyntax.Notation

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Binding
open Mettapedia.GSLT.Parsing.GrammarPresentationTransport
open Mettapedia.GSLT.LanguageDef.MultiSortedClone
open _root_.CategoryTheory

def mapOperator (tokens : String ≃ String) {language : LanguageDef} :
    {sort : TypeExpr} → Operator language sort → Operator (mapLanguage tokens language) sort
  | _, .constructor rule member ordinary scopes =>
      .constructor (mapRule tokens rule) (List.mem_map_of_mem member) ordinary scopes
  | _, .collectionConstructor rule member name kind element shape count =>
      .collectionConstructor (mapRule tokens rule) (List.mem_map_of_mem member)
        name kind element shape count
  | _, .lambda domain codomain => .lambda domain codomain
  | _, .multiLambda domain codomain count => .multiLambda domain codomain count
  | _, .subst domain codomain => .subst domain codomain
  | _, .collection kind element count => .collection kind element count

private theorem inverse_member (tokens : String ≃ String) {language : LanguageDef}
    {rule : GrammarRule} (member : rule ∈ (mapLanguage tokens language).terms) :
    mapRule tokens.symm rule ∈ language.terms := by
  obtain ⟨original, belongs, same⟩ := List.mem_map.mp member
  rw [← same, mapRule_inverse]
  exact belongs

/-- Pull a target declaration back through the terminal bijection. Membership
is recovered from its actual source declaration, not an invented rule. -/
def unmapOperator (tokens : String ≃ String) {language : LanguageDef} :
    {sort : TypeExpr} → Operator (mapLanguage tokens language) sort → Operator language sort
  | _, .constructor rule member ordinary scopes =>
      .constructor (mapRule tokens.symm rule) (inverse_member tokens member) ordinary scopes
  | _, .collectionConstructor rule member name kind element shape count =>
      .collectionConstructor (mapRule tokens.symm rule) (inverse_member tokens member)
        name kind element shape count
  | _, .lambda domain codomain => .lambda domain codomain
  | _, .multiLambda domain codomain count => .multiLambda domain codomain count
  | _, .subst domain codomain => .subst domain codomain
  | _, .collection kind element count => .collection kind element count

theorem unmap_map_operator (tokens : String ≃ String) {language : LanguageDef}
    {sort : TypeExpr} (operator : Operator language sort) :
    unmapOperator tokens (mapOperator tokens operator) = operator := by
  cases operator with
  | constructor rule =>
      cases rule
      simp only [mapOperator, unmapOperator, mapRule]
      congr 1 <;> first
        | exact proof_irrel_heq _ _
        | simp only [List.map_map, Function.comp_def, mapItem_inverse, List.map_id_fun', id_eq]
  | collectionConstructor rule =>
      cases rule
      simp only [mapOperator, unmapOperator, mapRule]
      congr 1 <;> first
        | exact proof_irrel_heq _ _
        | simp only [List.map_map, Function.comp_def, mapItem_inverse, List.map_id_fun', id_eq]
  | lambda => rfl
  | multiLambda => rfl
  | subst => rfl
  | collection => rfl

theorem map_unmap_operator (tokens : String ≃ String) {language : LanguageDef}
    {sort : TypeExpr} (operator : Operator (mapLanguage tokens language) sort) :
    mapOperator tokens (unmapOperator tokens operator) = operator := by
  have inverseItem (item : SyntaxItem) : mapItem tokens (mapItem tokens.symm item) = item := by
    simpa using mapItem_inverse tokens.symm item
  cases operator with
  | constructor rule =>
      cases rule
      simp only [mapOperator, unmapOperator, mapRule]
      congr 1 <;> first
        | exact proof_irrel_heq _ _
        | simp only [List.map_map, Function.comp_def, inverseItem, List.map_id_fun', id_eq]
  | collectionConstructor rule =>
      cases rule
      simp only [mapOperator, unmapOperator, mapRule]
      congr 1 <;> first
        | exact proof_irrel_heq _ _
        | simp only [List.map_map, Function.comp_def, inverseItem, List.map_id_fun', id_eq]
  | lambda => rfl
  | multiLambda => rfl
  | subst => rfl
  | collection => rfl

def forward (tokens : String ≃ String) (language : LanguageDef) :
    SigMor (signatureOf language) (signatureOf (mapLanguage tokens language)) where
  sortMap := id
  opMap := mapOperator tokens
  carriesArity := by
    intro sort operator
    change (signatureOf (mapLanguage tokens language)).arity (mapOperator tokens operator) =
      mapArities (fun sort => sort) ((signatureOf language).arity operator)
    rw [mapArities_id]
    cases operator <;> rfl

def backward (tokens : String ≃ String) (language : LanguageDef) :
    SigMor (signatureOf (mapLanguage tokens language)) (signatureOf language) where
  sortMap := id
  opMap := unmapOperator tokens
  carriesArity := by
    intro sort operator
    change (signatureOf language).arity (unmapOperator tokens operator) =
      mapArities (fun sort => sort) ((signatureOf (mapLanguage tokens language)).arity operator)
    rw [mapArities_id]
    cases operator <;> rfl

theorem forward_backward (tokens : String ≃ String) (language : LanguageDef) :
    (forward tokens language).comp (backward tokens language) =
      SigMor.ident (signatureOf language) := by
  unfold SigMor.comp forward backward SigMor.ident
  congr 1
  funext sort operator
  exact unmap_map_operator tokens operator

theorem backward_forward (tokens : String ≃ String) (language : LanguageDef) :
    (backward tokens language).comp (forward tokens language) =
      SigMor.ident (signatureOf (mapLanguage tokens language)) := by
  unfold SigMor.comp forward backward SigMor.ident
  congr 1
  funext sort operator
  exact map_unmap_operator tokens operator

def transport (tokens : String ≃ String) {language : LanguageDef}
    {context : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf language) context sort) :
    Term (signatureOf (mapLanguage tokens language)) context sort :=
  mapTerm (forward tokens language) (fun _ position => position) term

def untransport (tokens : String ≃ String) {language : LanguageDef}
    {context : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf (mapLanguage tokens language)) context sort) :
    Term (signatureOf language) context sort :=
  mapTerm (backward tokens language) (fun _ position => position) term

theorem untransport_transport (tokens : String ≃ String) {language : LanguageDef}
    {context : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf language) context sort) :
    untransport tokens (transport tokens term) = term := by
  unfold transport untransport
  have composed := mapTerm_comp (forward tokens language) (backward tokens language)
    (fun _ position => position) (fun _ position => position) term
  have asIdentity := mapTerm_heq_of_morphism_eq _ _ (forward_backward tokens language)
    (fun _ position => position) (fun _ position => position) (by rfl) term
  exact composed.trans (asIdentity.eq.trans
    ((mapTerm_ident (fun _ position => position) term).trans (rename_id term)))

theorem transport_untransport (tokens : String ≃ String) {language : LanguageDef}
    {context : List TypeExpr} {sort : TypeExpr}
    (term : Term (signatureOf (mapLanguage tokens language)) context sort) :
    transport tokens (untransport tokens term) = term := by
  unfold transport untransport
  have composed := mapTerm_comp (backward tokens language) (forward tokens language)
    (fun _ position => position) (fun _ position => position) term
  have asIdentity := mapTerm_heq_of_morphism_eq _ _ (backward_forward tokens language)
    (fun _ position => position) (fun _ position => position) (by rfl) term
  exact composed.trans (asIdentity.eq.trans
    ((mapTerm_ident (fun _ position => position) term).trans (rename_id term)))

theorem transport_bind (tokens : String ≃ String) {language : LanguageDef}
    {first second : List TypeExpr} {sort : TypeExpr}
    (environment : Sub (signatureOf language) first second)
    (term : Term (signatureOf language) first sort) :
    transport tokens (bind environment term) =
      bind (fun sort position => transport tokens (environment sort position))
        (transport tokens term) := by
  unfold transport
  exact mapTerm_bind (forward tokens language) (fun _ position => position)
    (fun _ position => position) environment
    (fun sort position => mapTerm (forward tokens language)
      (fun _ position => position) (environment sort position))
    (by intro sort position; rfl) term

theorem transport_substVar (tokens : String ≃ String) {language : LanguageDef} :
    ∀ (context : List TypeExpr) {target : List TypeExpr}
      (environment : (index : Fin context.length) →
        Term (signatureOf language) target (context.get index))
      {sort : TypeExpr} (position : Var context sort),
      transport tokens (substVar environment sort position) =
        substVar (fun index => transport tokens (environment index)) sort position
  | _ :: _, _, _, _, .zero => rfl
  | _ :: context, _, environment, _, .succ position =>
      transport_substVar tokens context (fun index => environment index.succ) position

private theorem positions_agree (tokens : String ≃ String) (language : LanguageDef)
    (context : List TypeExpr) (index : Fin context.length) :
    varOfIdx (S := signatureOf language) context index =
      varOfIdx (S := signatureOf (mapLanguage tokens language)) context index := by
  induction context with
  | nil => exact Fin.elim0 index
  | cons sort rest ih =>
      cases index using Fin.cases with
      | zero => rfl
      | succ index => exact congrArg Var.succ (ih index)

def cloneTranslation (tokens : String ≃ String) (language : LanguageDef) :
    CloneTranslation (termClone (signatureOf language))
      (termClone (signatureOf (mapLanguage tokens language))) where
  map := transport tokens
  map_project := by
    intro context index
    change Term.var (S := signatureOf (mapLanguage tokens language))
        (varOfIdx (S := signatureOf language) context index) =
      Term.var (S := signatureOf (mapLanguage tokens language))
        (varOfIdx (S := signatureOf (mapLanguage tokens language)) context index)
    exact congrArg (Term.var (S := signatureOf (mapLanguage tokens language)))
      (positions_agree tokens language context index)
  map_substitute := by
    intro first second sort term environment
    change Term (signatureOf language) first sort at term
    change (index : Fin first.length) →
      Term (signatureOf language) second (first.get index) at environment
    change transport tokens (bind (substVar environment) term) =
      bind (substVar (fun index => transport tokens (environment index))) (transport tokens term)
    rw [transport_bind]
    congr 1
    funext sort position
    exact transport_substVar tokens first environment position

def contextFunctor (tokens : String ≃ String) (language : LanguageDef) :=
  (cloneTranslation tokens language).contextFunctor

theorem contextFunctor_preservesFiniteProducts (tokens : String ≃ String)
    (language : LanguageDef) : Limits.PreservesFiniteProducts (contextFunctor tokens language) :=
  (cloneTranslation tokens language).preservesFiniteProducts

instance contextFunctor_faithful (tokens : String ≃ String) (language : LanguageDef) :
    (contextFunctor tokens language).Faithful where
  map_injective := by
    intro first second left right same
    change (index : Fin second.context.length) →
      Term (signatureOf language) first.context (second.context.get index) at left right
    funext index
    have component := congrFun same index
    change transport tokens (left index) = transport tokens (right index) at component
    have reflected := congrArg (untransport tokens) component
    exact (untransport_transport tokens (left index)).symm.trans
      (reflected.trans (untransport_transport tokens (right index)))

instance contextFunctor_full (tokens : String ≃ String) (language : LanguageDef) :
    (contextFunctor tokens language).Full where
  map_surjective := by
    intro first second environment
    refine ⟨fun index => untransport tokens (environment index), ?_⟩
    funext index
    exact transport_untransport tokens (environment index)

theorem contextFunctor_obj_surjective (tokens : String ≃ String) (language : LanguageDef) :
    Function.Surjective (contextFunctor tokens language).obj := by
  intro target
  cases target with
  | mk context marker =>
      refine ⟨ContextObject.ofList _ context, ?_⟩
      cases marker
      rfl

instance contextFunctor_essSurj (tokens : String ≃ String) (language : LanguageDef) :
    (contextFunctor tokens language).EssSurj :=
  Functor.essSurj_of_surj (contextFunctor_obj_surjective tokens language)

instance contextFunctor_isEquivalence (tokens : String ≃ String) (language : LanguageDef) :
    (contextFunctor tokens language).IsEquivalence where

/-- The equivalence is earned from the concrete bijective operator and term
maps. Its inverse recovers typed substitution arrows as well as objects. -/
noncomputable def contextEquivalence (tokens : String ≃ String) (language : LanguageDef) :=
  (contextFunctor tokens language).asEquivalence

end Mettapedia.GSLT.LanguageDef.BindingSyntax.Notation
