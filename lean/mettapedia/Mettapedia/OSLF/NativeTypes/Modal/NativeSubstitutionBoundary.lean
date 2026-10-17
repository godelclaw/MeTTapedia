import Mettapedia.OSLF.NativeTypes.Modal.NativeRootEvent
import Mettapedia.OSLF.MeTTaIL.StructuralDescentAuthoredPlans

/-!
# Syntactic freshness bounds operational substitution transport

An independently sorted ambient substitution can introduce a free atom into
an actual instantiated freshness subject. The original authored scoped rule
fires before substitution and has no firing after it, although its finite
provider is closed and unchanged. Event presheaves for this profile therefore
require a freshness-preserving action or an explicitly relative context base.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeSubstitutionBoundary

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

private def term : TypeExpr := .base "Term"

def binding : RuleBindingSpec := { dependencies := [("X", [])], occurrences := [] }
def condition : FreshnessCondition := ⟨"a", .fvar "X"⟩
def rule : RewriteRule := {
  «name» := "FreshLoop", typeContext := [("X", term)], premises := [.freshness condition],
  left := .fvar "X", right := .fvar "X", bindings := some binding }
def language : LanguageDef := {
  «name» := "FreshnessBoundary", types := [{«name» := "Term"}], terms := [], equations := [], rewrites := [rule] }
def free : FreeTypeContext := fun name => if name = "a" then some term else none

def environment : Environment := {
  language := language, free := free, provider := {signatures := [], rows := []}, specifications := [(0, binding)] }

def before : Assignment := [("X", ⟨[], 1, .bvar 0⟩)]
def after : Assignment := [("X", ⟨[], 0, .fvar "a"⟩)]
def beforeContext : Context := ⟨0, rule, binding, [term], 0, 0⟩

/-- The substitution is sorted independently in the original object grammar. -/
theorem substitution_sorted : HasType language free [] (.fvar "a") term :=
  .fvar (by simp [free])

theorem original_sorted : HasType language free [term] (.bvar 0) term := .bvar rfl

theorem providers_closed : checkProviderClosed language free environment.provider = true := rfl

theorem source_scope : OpenPatternWellSorted language free [term] term (.bvar 0) :=
  checkOpenPatternWellSorted_sound (by decide +kernel)

theorem captured_sorted : TypedAssignment environment beforeContext before :=
  checkTypedAssignment_sound (by decide +kernel)

theorem captured_exact :
    capture? rule binding 1 0 .left [] [] "X" (.bvar 0) = some before := by
  decide +kernel

theorem subject_before : freshnessSubject? rule binding [term] 0 0 before condition =
    some ("a", .bvar 0) := by decide +kernel

theorem freshness_before : SyntacticallyFresh "a" (.bvar 0) := by
  simp [SyntacticallyFresh, Substitution.freeVars]

/-- This is an actual independent scoped firing, retaining its original
capture and the instantiated premise event, not an endpoint-only witness. -/
theorem original_firing : RootFiring environment [term] term (.bvar 0) 0 [] before before
    [.freshness 0 0 "a" (.bvar 0)] (.bvar 0) := by
  refine .fire rfl rfl (by decide +kernel) source_scope (.capture captured_exact)
    captured_sorted (.cons (.freshness subject_before freshness_before) .nil) ?_ source_scope
  decide +kernel

theorem substituted_subject : Substitution.instantiateBVar (.fvar "a") (.bvar 0) = .fvar "a" := by
  simp [Substitution.instantiateBVar, Substitution.instantiateBVarAt, Substitution.liftBVars]

theorem subject_after : freshnessSubject? rule binding [] 0 0 after condition =
    some ("a", .fvar "a") := by decide +kernel

theorem freshness_after_fails : ¬ SyntacticallyFresh "a" (.fvar "a") := by
  simp [SyntacticallyFresh, Substitution.freeVars]

/-- Any firing of the original singleton rule would have to discharge the
same failed freshness premise after this sorted ambient substitution. -/
theorem no_substituted_firing {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event} {target : Pattern} :
    ¬ RootFiring environment [] term (.fvar "a") index trace captured completed history target := by
  intro fired
  cases fired with
  | @fire _ _ _ _ _ selectedRule selectedBinding _ _ _ _ declared specified _ _ matched _ premises _ _ =>
      have selected : selectedRule = rule := by
        have member := List.mem_of_getElem? declared
        simpa only [environment, language, List.mem_singleton] using member
      subst selectedRule
      have selectedIndex : index = 0 := by
        cases index with
        | zero => rfl
        | succ index => simp [environment, language] at declared
      subst index
      have selectedSpec : selectedBinding = binding := by
        have exactSpec : specification? environment 0 = some binding := by rfl
        exact Option.some.inj (specified.symm.trans exactSpec)
      subst selectedBinding
      have capturedSame : captured = after := by
        cases matched with
        | capture read =>
            have actual : capture? rule binding 0 0 .left [] [] "X" (.fvar "a") = some after := by
              decide +kernel
            exact Option.some.inj (read.symm.trans actual)
      subst captured
      change PremisesHold environment ⟨0, rule, binding, [], 0, 0⟩ [.freshness condition]
        after completed history at premises
      cases premises with
      | cons head tail =>
          cases head with
          | freshness read fresh =>
              have recovered := Option.some.inj (subject_after.symm.trans read)
              cases recovered
              exact freshness_after_fails fresh

#guard checkOpenPatternWellSorted language free [] term (.fvar "a")
#guard checkOpenPatternWellSorted language free [term] term (.bvar 0)
#guard checkProviderClosed language free environment.provider
#guard Substitution.isFresh "a" (.bvar 0)
#guard !(Substitution.isFresh "a" (Substitution.instantiateBVar (.fvar "a") (.bvar 0)))

end Mettapedia.OSLF.NativeTypes.Modal.NativeSubstitutionBoundary
