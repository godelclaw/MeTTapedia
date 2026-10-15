import Mettapedia.OSLF.NativeTypes.Modal.NativeTracedMatchSubstitution

/-!
# Local scope of decoded authored occurrence arguments

Scope is obtained from the language's actual binding admission and its exact
occurrence-depth lookup. No separate caller-supplied list of legal sites or
dependency arguments is used.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeRuleOccurrenceScope

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding

theorem row_scopes {rule : RewriteRule} {spec : RuleBindingSpec}
    (admitted : admittedFor rule spec = true) {row : MetavariableOccurrence}
    (member : row ∈ spec.occurrences) {depth : Nat}
    (located : occurrenceDepthAtSite? rule row.site row.path = some depth) :
    ∀ argument ∈ row.arguments, argument.isWellScopedAt depth = true := by
  simp only [admittedFor, Bool.and_eq_true] at admitted
  have checked := List.all_eq_true.mp admitted.2 row member
  cases declared : dependencies? spec row.name with
  | none => simp only [declared, Bool.and_false] at checked; cases checked
  | some dependencies =>
      simp only [declared, located, Bool.and_eq_true] at checked
      intro argument present
      exact Substitution.isWellScopedAt_of_isGroundAt
        (List.all_eq_true.mp checked.2.2 argument present)

theorem decoded_scopes {rule : RewriteRule} {spec : RuleBindingSpec}
    (admitted : admittedFor rule spec = true) {name : String} {site : RulePatternSite}
    {path : List Nat} {depth : Nat} {arguments : List Pattern}
    (located : occurrenceDepthAtSite? rule site path = some depth)
    (decoded : arguments? rule spec name site path = some arguments) :
    ∀ argument ∈ arguments, argument.isWellScopedAt depth = true := by
  unfold arguments? at decoded
  cases declaration : dependencies? spec name with
  | none => simp [declaration] at decoded
  | some dependencies =>
      simp only [declaration, Option.bind_eq_bind, Option.bind_some] at decoded
      cases occurrence : occurrenceDeclared rule {name, site, path, arguments := []} with
      | false => simp [occurrence] at decoded
      | true =>
          simp only [occurrence, guard, ↓reduceIte] at decoded
          cases rows : spec.occurrences.filter
              (fun candidate => candidate.name == name && candidate.site == site && candidate.path == path) with
          | nil =>
              simp only [rows] at decoded
              split at decoded <;> try contradiction
              have empty : arguments = [] := (Option.some.inj decoded).symm
              rw [empty]
              simp
          | cons row tail =>
              cases tail with
              | nil =>
                  simp only [rows] at decoded
                  split at decoded <;> try contradiction
                  have same := Option.some.inj decoded
                  rw [← same]
                  have selected : row ∈ spec.occurrences.filter
                      (fun candidate => candidate.name == name && candidate.site == site && candidate.path == path) := by
                    rw [rows]
                    exact List.mem_cons_self
                  have member := (List.mem_filter.mp selected).1
                  have matching : row.name = name ∧ row.site = site ∧ row.path = path := by
                    have condition := (List.mem_filter.mp selected).2
                    simpa only [Bool.and_eq_true, beq_iff_eq, and_assoc] using condition
                  apply row_scopes admitted member
                  simpa only [matching.2.1, matching.2.2] using located
              | cons next remaining => simp only [rows] at decoded; contradiction

end Mettapedia.OSLF.NativeTypes.Modal.NativeRuleOccurrenceScope
