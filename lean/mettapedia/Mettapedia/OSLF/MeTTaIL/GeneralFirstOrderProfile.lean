import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderScopedInstance
import Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderSubstitution

/-!
# Checked first-order rule profiles

The finite syntax check recognizes precisely metavariables and ordered
constructor applications. Profile evidence is derived from authored rows,
not supplied as a per-language matching or reduction oracle.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch Match MatchSpec
open Mettapedia.GSLT.LanguageDef.WellSorted

mutual
 def checkFirstOrder : Pattern → Bool
  | .fvar _ => true
  | .apply _ arguments => checkFirstOrderArguments arguments
  | _ => false
 termination_by pattern => sizeOf pattern

 def checkFirstOrderArguments : List Pattern → Bool
  | [] => true
  | argument :: arguments => checkFirstOrder argument && checkFirstOrderArguments arguments
 termination_by arguments => sizeOf arguments
end

mutual
 theorem checkFirstOrder_sound {schema : Pattern} (checked : checkFirstOrder schema = true) : FirstOrder schema := by
  cases schema with
  | fvar name => exact .metavariable name
  | apply label arguments =>
    exact .constructor label arguments (checkFirstOrderArguments_sound (by
      simpa only [checkFirstOrder] using checked))
  | bvar | lambda | multiLambda | subst | collection => simp only [checkFirstOrder, Bool.false_eq_true] at checked
 termination_by sizeOf schema

 theorem checkFirstOrderArguments_sound {schemas : List Pattern}
    (checked : checkFirstOrderArguments schemas = true) : ∀ schema ∈ schemas, FirstOrder schema := by
  cases schemas with
  | nil => intro _ member; cases member
  | cons schema schemas =>
    simp only [checkFirstOrderArguments, Bool.and_eq_true] at checked
    have first := checkFirstOrder_sound checked.1
    have remaining := checkFirstOrderArguments_sound checked.2
    intro child member
    rcases List.mem_cons.mp member with rfl | member
    · exact first
    · exact remaining child member
 termination_by sizeOf schemas
end

 theorem FirstOrder.isMatchCorrect {schema : Pattern} (shape : FirstOrder schema) :
    Match.Pattern.isMatchCorrect schema = true := by
  induction schema using Pattern.inductionOn with
  | hfvar => rfl
  | happly label arguments ih =>
    cases shape with
    | constructor _ _ children =>
      simpa only [Match.Pattern.isMatchCorrect, isMatchCorrectAux] using
        (isMatchCorrectListAux_iff_forall arguments).mpr (fun argument member => ih argument member (children argument member))
  | hbvar | hlambda | hmultiLambda | hsubst | hcollection => cases shape

 def checkRuleShape (rule : RewriteRule) : Bool :=
  checkFirstOrder rule.left && checkFirstOrder rule.right && rule.premises.isEmpty &&
    decide (rule.typeContext.map Prod.fst).Nodup &&
    rule.right.freeFvarNames.all (fun name => decide (name ∈ rule.left.freeFvarNames))

 theorem checkRuleShape_sound {rule : RewriteRule} (checked : checkRuleShape rule = true) :
    FirstOrder rule.left ∧ FirstOrder rule.right ∧ rule.premises = [] ∧
      (rule.typeContext.map Prod.fst).Nodup ∧
      ∀ name ∈ rule.right.freeFvarNames, name ∈ rule.left.freeFvarNames := by
  simp only [checkRuleShape, Bool.and_eq_true, List.isEmpty_iff, decide_eq_true_eq] at checked
  exact ⟨checkFirstOrder_sound checked.1.1.1.1, checkFirstOrder_sound checked.1.1.1.2,
    checked.1.1.2, checked.1.2, fun name member =>
      of_decide_eq_true (List.all_eq_true.mp checked.2 name member)⟩

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
