import Mettapedia.OSLF.NativeTypes.Modal.NativeOperationalAdmission
import Mettapedia.OSLF.NativeTypes.Modal.NativeContextualSubstitution

/-!
# A closed positive provider does not give substitution reflection

A positive input query compares its actual scoped argument to an unchanged,
closed provider row. Substitution can turn an unmatched ambient variable into
that row. The original firing is absent, the substituted firing exists, and
both scopes are independently sorted. Positive admission therefore cannot be
used as a two-sided semantic comparison or as a pullback assertion.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Modal.NativeQuerySubstitutionBoundary

open Mettapedia.OSLF.MeTTaIL Syntax RuleBinding ScopedRuleMatching GeneralPremise
open Mettapedia.GSLT.LanguageDef.WellSorted

def term : TypeExpr := .base "Term"
def binding : RuleBindingSpec := {dependencies := [("X", [])], occurrences := []}
def rule : RewriteRule := {
  «name» := "PositiveQueryLoop", typeContext := [("X", term)],
  premises := [.relationQuery "known" [.fvar "X"]], left := .fvar "X", right := .fvar "X",
  bindings := some binding }
def language : LanguageDef := {
  «name» := "PositiveQuerySubstitutionBoundary", types := [{«name» := "Term"}],
  terms := [], equations := [], rewrites := [rule] }
def free : FreeTypeContext := fun name => if name = "a" then some term else none
def signature : Signature := ⟨"known", [term], [.input]⟩
def row : ProviderRow := ⟨"known", [.fvar "a"]⟩
def provider : ProviderSnapshot := ⟨[signature], [row]⟩
def environment : Environment := {
  language := language, free := free, provider := provider, specifications := [(0, binding)] }
def before : Assignment := [("X", ⟨[], 1, .bvar 0⟩)]
def after : Assignment := [("X", ⟨[], 0, .fvar "a"⟩)]
def beforeContext : Context := ⟨0, rule, binding, [term], 0, 0⟩
def afterContext : Context := ⟨0, rule, binding, [], 0, 0⟩

theorem provider_closed : checkProviderClosed language free provider = true := by decide +kernel

theorem prerequisites_admitted : NativeOperationalAdmission.checkPrerequisites environment = true := by
  decide +kernel

theorem before_sorted : OpenPatternWellSorted language free [term] term (.bvar 0) :=
  checkOpenPatternWellSorted_sound (by decide +kernel)

theorem after_sorted : OpenPatternWellSorted language free [] term (.fvar "a") :=
  checkOpenPatternWellSorted_sound (by decide +kernel)

theorem bound_substitution_sorted : HasType language free [] (.fvar "a") term := .fvar (by simp [free])

theorem after_assignment_exact :
    NativeContextualSubstitution.assignment 0 (ContextSubstitution.single (.fvar "a")) before = after := by
  decide +kernel

theorem input_before : instantiateAt? rule binding 1 (.premise 0 0 0) [] 0 before (.fvar "X") =
    some (.bvar 0) := by decide +kernel

theorem input_after : instantiateAt? rule binding 0 (.premise 0 0 0) [] 0 after (.fvar "X") =
    some (.fvar "a") := by decide +kernel

theorem after_capture : capture? rule binding 0 0 .left [] [] "X" (.fvar "a") = some after := by
  decide +kernel

theorem after_typed : TypedAssignment environment afterContext after :=
  checkTypedAssignment_sound (by decide +kernel)

/-- The changed answer includes its actual provider row position and ordered
argument origin, rather than only a substituted endpoint. -/
theorem substituted_firing : RootFiring environment [] term (.fvar "a") 0 [] after after
    [.query 0 0 0 [(0, [])]] (.fvar "a") := by
  refine .fire rfl rfl (by decide +kernel) after_sorted (.capture after_capture) after_typed
    (.cons (.query ?_) .nil) (by decide +kernel) after_sorted
  refine .row (row := row) (signature := signature) rfl (by decide +kernel) ?_
    (.input input_after .nil) after_typed
  exact checkRow_sound (by decide +kernel)

/-- Every firing of this actual authored language would need the failed
original input comparison; no alternate matcher or premise history repairs it. -/
theorem no_original_firing {index : Nat} {trace : List GeneralScopedMatchMachine.BagChoice}
    {captured completed : Assignment} {history : List Event} {target : Pattern} :
    ¬ RootFiring environment [term] term (.bvar 0) index trace captured completed history target := by
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
        have actual : specification? environment 0 = some binding := rfl
        exact Option.some.inj (specified.symm.trans actual)
      subst selectedBinding
      have capturedSame : captured = before := by
        cases matched with
        | capture read =>
            have actual : capture? rule binding 1 0 .left [] [] "X" (.bvar 0) = some before := by
              decide +kernel
            exact Option.some.inj (read.symm.trans actual)
      subst captured
      change PremisesHold environment beforeContext [.relationQuery "known" [.fvar "X"]]
        before completed history at premises
      cases premises with
      | cons head tail =>
          cases head with
          | query query =>
              cases query with
              | row rowSelected signatureSelected _ arguments _ =>
                  have rowSame := List.mem_of_getElem? rowSelected
                  simp only [environment, provider, List.mem_singleton] at rowSame
                  have actual : signature? provider "known" 1 = some signature := by decide +kernel
                  have signatureSame := Option.some.inj (signatureSelected.symm.trans actual)
                  rw [rowSame, signatureSame] at arguments
                  cases arguments with
                  | input read tail =>
                      have impossible := Option.some.inj (input_before.symm.trans read)
                      cases impossible

#guard NativeOperationalAdmission.checkPrerequisites environment
#guard NativeOperationalAdmission.checkPremise provider (.relationQuery "known" [.fvar "X"])
#guard !(NativeOperationalAdmission.checkPremise provider (.relationQuery "missing" [.fvar "X"]))
#guard !(NativeOperationalAdmission.checkPremise provider (.freshness ⟨"a", .fvar "X"⟩))
#guard checkOpenPatternWellSorted language free [term] term (.bvar 0)
#guard checkOpenPatternWellSorted language free [] term (.fvar "a")

end Mettapedia.OSLF.NativeTypes.Modal.NativeQuerySubstitutionBoundary
