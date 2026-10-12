import Mettapedia.OSLF.MeTTaIL.GeneralEquationSupport

/-!
# Sound alphabet bounds of the source-derived term universe

Every emitted syntax tree uses only the extracted alphabet. This complements
the universe's typing/scope filter and its independent completeness proof:
finite saturation can use closure for every carrier member, rather than only
for a manually selected set of already reached states.
-/

set_option autoImplicit false
namespace Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.GeneralEquationSupport

theorem rows_members (pool : List Pattern) (budget : Nat) (patterns : List Pattern)
    (member : patterns ∈ rows pool budget) : ∀ pattern ∈ patterns, pattern ∈ pool := by
  induction budget generalizing patterns with
  | zero =>
      have empty : patterns = [] := by simpa only [rows, List.mem_singleton] using member
      simp [empty]
  | succ budget ih =>
      simp only [rows, List.mem_cons, List.mem_flatMap, List.mem_map] at member
      rcases member with rfl | ⟨first, firstMember, rest, restMember, rfl⟩
      · simp
      · intro pattern occurs
        rcases List.mem_cons.mp occurs with rfl | later
        · exact firstMember
        · exact ih rest restMember pattern later

theorem terms_supported (alphabet : Alphabet) (indexBound budget : Nat) (pattern : Pattern)
    (member : pattern ∈ terms alphabet indexBound budget) : Supported alphabet pattern := by
  induction budget generalizing pattern with
  | zero => simp only [terms, List.not_mem_nil] at member
  | succ budget ih =>
      simp only [terms, List.mem_append, List.mem_flatMap, List.mem_map] at member
      rcases member with ((((bound | free) | constructor) | binder) | binders) | collection
      · obtain ⟨index, _, rfl⟩ := bound
        simp [Supported, constructors, Pattern.freeFvarNames, arities]
      · obtain ⟨name, declared, rfl⟩ := free
        refine ⟨by simp [constructors], ?_, by simp [arities]⟩
        intro actual occurs
        simp only [Pattern.freeFvarNames, List.mem_singleton] at occurs
        exact occurs ▸ declared
      · obtain ⟨label, declared, arguments, rowMember, rfl⟩ := constructor
        exact supported_apply alphabet label arguments declared
          (by intro child occurs; exact ih child (rows_members _ _ _ rowMember child occurs))
      · obtain ⟨body, bodyMember, rfl⟩ := binder
        simpa only [Supported, constructors, Pattern.freeFvarNames, arities] using ih body bodyMember
      · obtain ⟨arity, declared, body, bodyMember, rfl⟩ := binders
        have supported := ih body bodyMember
        refine ⟨by simpa only [constructors] using supported.1,
          by simpa only [Pattern.freeFvarNames] using supported.2.1, ?_⟩
        intro actual occurs
        simp only [arities, List.mem_cons] at occurs
        exact occurs.elim (fun same => same ▸ declared) (supported.2.2 actual)
      · obtain ⟨kind, _, elements, rowMember, rfl⟩ := collection
        exact supported_collection alphabet kind elements
          (by intro child occurs; exact ih child (rows_members _ _ _ rowMember child occurs))

theorem typedUniverse_supported (alphabet : Alphabet) (indexBound budget : Nat)
    (language : LanguageDef) (free : Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext)
    (bound : List TypeExpr) (expected : TypeExpr) (pattern : Pattern)
    (member : pattern ∈ typedUniverse alphabet indexBound budget language free bound expected) :
    Supported alphabet pattern := terms_supported alphabet indexBound budget pattern (List.mem_filter.mp member).1

theorem sourceUniverse_supported (language : LanguageDef)
    (free : Mettapedia.GSLT.LanguageDef.WellSorted.FreeTypeContext) (bound : List TypeExpr)
    (expected : TypeExpr) (source : Pattern) (providerTerms : List Pattern) (pattern : Pattern)
    (member : pattern ∈ sourceUniverse language free bound expected source providerTerms) :
    Supported (alphabet language source providerTerms) pattern := typedUniverse_supported _ _ _ _ _ _ _ _ member

end Mettapedia.OSLF.Framework.GeneralFiniteTermUniverse
