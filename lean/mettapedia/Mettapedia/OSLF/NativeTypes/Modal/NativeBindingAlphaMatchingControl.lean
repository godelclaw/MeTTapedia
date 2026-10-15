import Mettapedia.OSLF.NativeTypes.Modal.NativeBindingMatchInstantiation

/-!
# Raw repeated captures distinguish alpha-equivalent display labels

The raw matcher compares stored contextual bodies structurally. Two
alpha-equivalent binders with different display labels therefore need not
match a repeated metavariable. Canonical semantic carrier comparisons do
not supply reflection for arbitrary unnormalized raw matching.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeBindingAlphaMatchingControl

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching

private def term : TypeExpr := .base "Term"

def spec : RuleBindingSpec := { dependencies := [("X", [])], occurrences := [] }
def rule : RewriteRule := {
  name := "Repeated", typeContext := [("X", .arrow term term)], premises := [],
  left := .apply "Pair" [.fvar "X", .fvar "X"], right := .fvar "X", bindings := some spec }
def source : Pattern := .apply "Pair"
  [.lambda (some "first") (.bvar 0), .lambda (some "second") (.bvar 0)]
def canonicalSource : Pattern := source.eraseBinderMetadata

theorem binding_admitted : admittedFor rule spec = true := by decide +kernel

theorem source_alpha : Pattern.AlphaEquiv source canonicalSource := by
  exact (Pattern.eraseBinderMetadata_idempotent source).symm

theorem raw_repeated_match_rejected : matchRuleAt rule spec 0 source = [] := by decide +kernel

theorem canonical_repeated_match_found : matchRuleAt rule spec 0 canonicalSource ≠ [] := by decide +kernel

theorem raw_matching_not_alpha_invariant :
    ¬ (∀ left right, Pattern.AlphaEquiv left right →
      (matchRuleAt rule spec 0 left = [] ↔ matchRuleAt rule spec 0 right = [])) := by
  intro invariant
  exact canonical_repeated_match_found ((invariant source canonicalSource source_alpha).mp raw_repeated_match_rejected)

end Mettapedia.OSLF.NativeTypes.Modal.NativeBindingAlphaMatchingControl
