import Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalAdmission
import Mettapedia.OSLF.NativeTypes.Modal.NativeContextualSubstitution

/-!
# Fixed closed providers under ambient substitution

Every independently closed provider value is unchanged by simultaneous
ambient substitution, including values with nested binders. Ordered provider
rows and their original indices remain unchanged. These are forward data and
typing laws; they do not infer that unmatched queries stay unmatched.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeProviderSubstitution

open Mettapedia.OSLF.MeTTaIL Syntax GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

private theorem termScoped_member {depth : Nat} {patterns : List Pattern}
    (termScoped : Pattern.isWellScopedListAt depth patterns = true)
    {pattern : Pattern} (member : pattern ∈ patterns) : pattern.isWellScopedAt depth = true := by
  induction patterns with
  | nil => cases member
  | cons head tail ih =>
      simp only [Pattern.isWellScopedListAt, Bool.and_eq_true] at termScoped
      rcases List.mem_cons.mp member with same | member
      · subst pattern; exact termScoped.1
      · exact ih termScoped.2 member

private theorem lifted_fixed {depth : Nat} {substitution : ContextSubstitution.Assignment}
    (fixed : ∀ index, index < depth → substitution index = .bvar index) (arity : Nat) :
    ∀ index, index < depth + arity →
      ContextSubstitution.lift arity substitution index = .bvar index := by
  intro index within
  by_cases fresh : index < arity
  · simp only [ContextSubstitution.lift, fresh, ite_true]
  · have prior : index - arity < depth := by omega
    simp only [ContextSubstitution.lift, fresh, ite_false, fixed _ prior,
      Substitution.liftBVars, Nat.zero_le, ite_true]
    congr 1
    omega

/-- A scoped term only observes the substitution on its actual ambient
variables. All binders are traversed with their corresponding lifted action. -/
theorem substitute_fixed {depth : Nat} {substitution : ContextSubstitution.Assignment}
    {pattern : Pattern} (termScoped : pattern.isWellScopedAt depth = true)
    (fixed : ∀ index, index < depth → substitution index = .bvar index) :
    ContextSubstitution.substitute substitution pattern = pattern := by
  induction pattern using Pattern.inductionOn generalizing depth substitution with
  | hbvar index =>
      exact fixed index (of_decide_eq_true termScoped)
  | hfvar name => rfl
  | happly constructor arguments ih =>
      simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
      apply congrArg (Pattern.apply constructor)
      conv_rhs => rw [← List.map_id arguments]
      apply List.map_congr_left
      intro argument member
      exact ih argument member (termScoped_member termScoped member) fixed
  | hlambda binder body ih =>
      change Pattern.lambda binder (ContextSubstitution.substitute (ContextSubstitution.lift 1 substitution) body) =
        Pattern.lambda binder body
      exact congrArg (Pattern.lambda binder) (ih termScoped (lifted_fixed fixed 1))
  | hmultiLambda arity binders body ih =>
      change Pattern.multiLambda arity binders
          (ContextSubstitution.substitute (ContextSubstitution.lift arity substitution) body) =
        Pattern.multiLambda arity binders body
      exact congrArg (Pattern.multiLambda arity binders) (ih termScoped (lifted_fixed fixed arity))
  | hsubst body replacement ihBody ihReplacement =>
      simp only [Pattern.isWellScopedAt, Bool.and_eq_true] at termScoped
      simp only [ContextSubstitution.substitute]
      rw [ihBody termScoped.1 (lifted_fixed fixed 1), ihReplacement termScoped.2 fixed]
  | hcollection kind elements rest ih =>
      simp only [ContextSubstitution.substitute, ContextSubstitution.substituteList_eq_map]
      apply congrArg (fun elements => Pattern.collection kind elements rest)
      conv_rhs => rw [← List.map_id elements]
      apply List.map_congr_left
      intro element member
      exact ih element member (termScoped_member termScoped member) fixed

theorem substitute_closed {pattern : Pattern}
    (closed : pattern.isWellScopedAt 0 = true)
    (substitution : ContextSubstitution.Assignment) :
    ContextSubstitution.substitute substitution pattern = pattern :=
  substitute_fixed closed (fun _ impossible => by omega)

theorem closed_values_fixed {language : LanguageDef} {free : FreeTypeContext}
    {values : List Pattern} {types : List TypeExpr}
    (typed : ValuesTyped language free [] values types)
    (substitution : ContextSubstitution.Assignment) :
    values.map (ContextSubstitution.substitute substitution) = values := by
  induction typed with
  | nil => rfl
  | cons head rest ih =>
      simp only [List.map_cons]
      rw [substitute_closed head.2.2.2 substitution, ih]

def row (substitution : ContextSubstitution.Assignment) (original : ProviderRow) : ProviderRow where
  relation := original.relation
  values := original.values.map (ContextSubstitution.substitute substitution)

theorem closed_row_fixed {language : LanguageDef} {free : FreeTypeContext}
    {signature : Signature} {original : ProviderRow}
    (typed : RowTyped language free [] signature original)
    (substitution : ContextSubstitution.Assignment) : row substitution original = original := by
  cases original
  simp only [row]
  rw [closed_values_fixed typed.2 substitution]

def provider (substitution : ContextSubstitution.Assignment)
    (original : ProviderSnapshot) : ProviderSnapshot where
  signatures := original.signatures
  rows := original.rows.map (row substitution)
  dynamicRelations := original.dynamicRelations

theorem closed_provider_fixed {language : LanguageDef} {free : FreeTypeContext}
    {original : ProviderSnapshot}
    (closed : NativeOperationalAdmission.ClosedProvider language free original)
    (substitution : ContextSubstitution.Assignment) : provider substitution original = original := by
  have rowsFixed : original.rows.map (row substitution) = original.rows := by
    conv_rhs => rw [← List.map_id original.rows]
    apply List.map_congr_left
    intro originalRow member
    obtain ⟨signature, _, typed⟩ := closed.rows originalRow member
    exact closed_row_fixed typed substitution
  cases original
  simp only [provider] at rowsFixed ⊢
  rw [rowsFixed]

theorem actual_row_index_preserved {language : LanguageDef} {free : FreeTypeContext}
    {original : ProviderSnapshot} {index : Nat} {originalRow : ProviderRow}
    (closed : NativeOperationalAdmission.ClosedProvider language free original)
    (selected : original.rows[index]? = some originalRow)
    (substitution : ContextSubstitution.Assignment) :
    (provider substitution original).rows[index]? = some originalRow := by
  rw [closed_provider_fixed closed substitution]
  exact selected

theorem successful_input_preserved {language : LanguageDef} {free : FreeTypeContext}
    {value : Pattern} {type : TypeExpr}
    (typed : OpenPatternWellSorted language free [] type value)
    {actual : Pattern} (matched : actual = value)
    (substitution : ContextSubstitution.Assignment) :
    ContextSubstitution.substitute substitution actual = value := by
  rw [matched]
  exact substitute_closed typed.2.2.2 substitution

end Mettapedia.OSLF.NativeTypes.Modal.NativeProviderSubstitution
