import Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

/-!
# Resolved-wildcard provenance counterexample

Recursive R2 matching treats a literal `%Undefined%` in the compared source
types as a gradual wildcard.  It must not grant wildcard status to an ordinary
type variable merely because an incoming substitution presents that variable
as `%Undefined%`: the raw new equation may conflict with the incoming one.

The legacy presentation relation substituted first and then inspected the
result for `%Undefined%`. The source counterexamples below separate that
rule from raw wildcard provenance. Runtime comparisons consume these
independent facts downstream.
-/

namespace Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.WildcardProvenanceCounterexample

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation

def legacyIncoming : TypeSubst :=
  [("x", Atom.undefinedType)]

/-- The legacy decision rule: substitution-produced `%Undefined%` was
mistaken for a literal wildcard. -/
def LegacyResolvedWildcardAccepts
    (substitution : TypeSubst) (left right : Atom) : Prop :=
  substitution.apply left = Atom.undefinedType ∨
    substitution.apply right = Atom.undefinedType

theorem legacy_resolved_wildcard_accepts :
    LegacyResolvedWildcardAccepts legacyIncoming
      (.var "x") (.symbol "A") := by
  left
  simp [legacyIncoming, TypeSubst.apply, TypeSubst.lookup,
    Atom.undefinedType]

/-- Before the provenance correction, the presentation relation admits the
same false-positive branch. -/
theorem legacy_presentation_relation_accepts :
    LegacyResolvedWildcardAccepts legacyIncoming
      (.var "x") (.symbol "A") :=
  legacy_resolved_wildcard_accepts

/-- The corrected spec relation keeps wildcard provenance at the raw layer
and therefore rejects the substitution-produced false positive. -/
theorem corrected_spec_relation_rejects_resolved_wildcard_conflict :
    ¬∃ output,
      ReducedTypePresentationMatchRel legacyIncoming
        (.var "x") (.symbol "A") output := by
  rintro ⟨output, derivation⟩
  obtain ⟨resolvedLeft, resolvedRight, leftApply, rightApply, applied⟩ :=
    derivation.ordinary_of_nonUndefined
      (by simp [Atom.undefinedType]) (by simp [Atom.undefinedType])
      (by simp [ReducedTypeLeafShape])
  simp [legacyIncoming, TypeSubst.apply, TypeSubst.lookup,
    Atom.undefinedType] at leftApply
  simp [legacyIncoming, TypeSubst.apply] at rightApply
  rw [← leftApply, ← rightApply] at applied
  exact AppliedReducedTypeMatchRel.no_distinct_symbols
    (by decide) applied

/-! ## Recursive provenance canary -/

/-- The second legacy decision rule substituted an entire expression before
recursing into its children.  It therefore exposed substitution-produced
`%Undefined%` as though it had occurred literally in the raw child. -/
def LegacyResolvedChildrenAccepts
    (substitution : TypeSubst) (left right : List Atom) : Prop :=
  ∃ resolvedLeft resolvedRight output,
    substitution.apply (.expression left) = .expression resolvedLeft ∧
      substitution.apply (.expression right) = .expression resolvedRight ∧
      ReducedTypePresentationListMatchRel substitution
        resolvedLeft resolvedRight output

/-- Legacy acceptance persists one level below an expression unless raw
wildcard provenance is threaded structurally. -/
theorem legacy_nested_resolved_wildcard_accepts :
    LegacyResolvedChildrenAccepts legacyIncoming
      [.var "x"] [.symbol "A"] := by
  refine ⟨[.symbol "%Undefined%"], [.symbol "A"], legacyIncoming,
    ?_, ?_, ?_⟩
  · simp [legacyIncoming, TypeSubst.apply, TypeSubst.lookup,
      Atom.undefinedType]
  · simp [legacyIncoming, TypeSubst.apply]
  · exact ReducedTypePresentationListMatchRel.cons
      (ReducedTypePresentationMatchRel.undefinedLeft _ _)
      (ReducedTypePresentationListMatchRel.nil _)

/-- The corrected relation recurses on the raw expression children and
therefore rejects the same nested false positive. -/
theorem corrected_spec_relation_rejects_nested_resolved_wildcard_conflict :
    ¬∃ output,
      ReducedTypePresentationMatchRel legacyIncoming
        (.expression [.var "x"]) (.expression [.symbol "A"]) output := by
  rintro ⟨output, derivation⟩
  cases derivation with
  | expression children =>
      cases children with
      | cons head tail =>
          exact corrected_spec_relation_rejects_resolved_wildcard_conflict
            ⟨_, head⟩
  | ordinary _ _ leafShape _ _ _ => exact leafShape.elim

/-! ## Ordinary `%Undefined%` remains bindable -/

private def consistentUndefinedIncoming : TypeSubst :=
  [("y", Atom.undefinedType)]

/-- Positive boundary: after provenance is checked on the raw atoms, an
already-presented `%Undefined%` is an ordinary symbol.  A fresh variable may
therefore be equated with it; the correction rejects conflicts without
turning ordinary `%Undefined%` into an unmatchable constant. -/
theorem substitution_produced_undefined_is_ordinary_and_bindable :
    ReducedTypePresentationMatchRel consistentUndefinedIncoming
      (.var "x") (.var "y")
      (consistentUndefinedIncoming.bind "x" Atom.undefinedType) := by
  apply ReducedTypePresentationMatchRel.ordinary
      (resolvedLeft := .var "x")
      (resolvedRight := Atom.undefinedType)
  · simp [Atom.undefinedType]
  · simp [Atom.undefinedType]
  · simp [ReducedTypeLeafShape]
  · simp [consistentUndefinedIncoming, TypeSubst.apply,
      TypeSubst.lookup]
  · simp [consistentUndefinedIncoming, TypeSubst.apply,
      TypeSubst.lookup, Atom.undefinedType]
  · exact AppliedReducedTypeMatchRel.bindLeft
      (by simp [TypeSubst.typeVars, Atom.undefinedType])

end Mettapedia.Languages.MeTTa.HE.Spec.Type.Presentation.WildcardProvenanceCounterexample
