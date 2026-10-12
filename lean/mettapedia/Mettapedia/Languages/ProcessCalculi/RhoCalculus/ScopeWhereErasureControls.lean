import Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWhereExecutionControls

/-!
# Erasing complementary where clauses admits additional communications

These concrete unguarded programs retain each channel, continuation and
payload. Only their receiver tags are erased. Ordinary scoped COMM can
then select either answer, even though the guarded interpreter will admit
only the branch earned by the supplied payload test. This is a control
on concrete programs, not an unproved syntax-wide erasure functor.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWhereErasureControls

open Mettapedia.OSLF.MeTTaIL
open Syntax ScopedRuleExecution
open Mettapedia.GSLT.Examples.ScopedRhoBinding
open Mettapedia.GSLT.Causality.ComplementaryAssay (Verdict)
open ScopeWhereExecutionControls

def erasedProbe (branch : Verdict) : Pattern :=
  .apply "PInput" [channel, .lambda none (continuation branch)]

def erasedSource (sample : Verdict) : Pattern :=
  .collection .hashBag
    [erasedProbe .confirm, erasedProbe .refute, .apply "POutput" [channel, payload sample]] none

def erasedTarget (sample branch : Verdict) : Pattern :=
  .collection .hashBag
    [.apply "POutput" [answerChannel branch, .apply "PDrop" [.apply "NQuote" [payload sample]]],
     erasedProbe (opposite branch)] none

theorem ordinary_COMM_admits_both (sample : Verdict) :
    applyRuleAt Engine.RelationEnv.empty rhoCalcWithScopedSchemas 0 scopedCommRewrite
      (erasedSource sample) = [erasedTarget sample .confirm, erasedTarget sample .refute] := by
  cases sample <;> decide +kernel

theorem erased_answers_are_distinct (sample : Verdict) :
    erasedTarget sample .confirm ≠ erasedTarget sample .refute := by
  cases sample <;> decide +kernel

theorem either_erased_answer_reachable (sample branch : Verdict) :
    erasedTarget sample branch ∈ rewriteStepAt Engine.RelationEnv.empty
      rhoCalcWithScopedSchemas 0 (erasedSource sample) := by
  cases sample <;> cases branch <;> decide +kernel

end Mettapedia.Languages.ProcessCalculi.RhoCalculus.ScopeWhereErasureControls
