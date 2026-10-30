import Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog
import Mettapedia.OSLF.MeTTaIL.ReferenceStepExecution

/-! The operational rules below are read from the authored Core.module.
Grounding, source admission and the saturation driver are separate layers. -/

set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

namespace Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.Kernel

open Mettapedia.OSLF.MeTTaIL Syntax

def language : LanguageDef := GroundKernel.language.toOption.get (by decide +kernel)

def factStore (facts : List Pattern) : Pattern :=
  .apply "FactStore" [.collection .hashSet facts none]

def tuple (values : List Pattern) : Pattern :=
  .apply "GroundTuple" [.collection .vec values none]

def fact (relation : String) (values : List Pattern) : Pattern :=
  .apply "AtomData" [.apply "Relation" [.fvar relation],tuple values]

def body (facts : List Pattern) : Pattern :=
  .apply "GroundBody" [.collection .vec facts none]

def rule (identifier : String) (grounding : List Pattern) (head : Pattern) (premises : List Pattern) : Pattern :=
  .apply "GroundRule" [.fvar identifier,tuple grounding,head,body premises]

def applyInstance (identifier : String) (grounding : List Pattern) (head : Pattern)
    (premises known : List Pattern) : Pattern :=
  .apply "ApplyGround" [rule identifier grounding head premises,factStore known]

def result (identifier : String) (grounding : List Pattern) (head : Pattern)
    (premises known : List Pattern) : Pattern :=
  .apply "GroundApplied"
    [.apply "GroundKey" [.fvar identifier,tuple grounding,body premises],factStore (head :: known)]

def targets (depth : Nat) (source : Pattern) : List Pattern :=
  (ReferenceStep.stepsAt Engine.RelationEnv.empty language depth source).map Prod.snd

private def a : Pattern := fact "A" [.fvar "value"]
private def b : Pattern := fact "B" [.fvar "value"]
private def c : Pattern := fact "C" [.fvar "value"]
private def d : Pattern := fact "D" [.fvar "value"]

theorem authored_kernel_nonempty : language.rewrites.length = 2 := by decide +kernel

theorem actual_membership :
    targets 1 (.apply "HasFact" [factStore [a,b],a]) = [.apply "FactPresent" []] := by
  decide +kernel

theorem absent_membership : targets 1 (.apply "HasFact" [factStore [a,b],c]) = [] := by
  decide +kernel

theorem repeated_premise_is_kept :
    result "rule-0" [] d [a,a] [a] ∈ targets 2 (applyInstance "rule-0" [] d [a,a] [a]) := by
  decide +kernel

theorem missing_premise_blocks : targets 2 (applyInstance "rule-0" [] d [a,b] [a]) = [] := by
  decide +kernel

theorem empty_body_applies : result "rule-0" [] d [] [] ∈ targets 2 (applyInstance "rule-0" [] d [] []) := by
  decide +kernel

theorem two_groundings_one_fact :
    result "rule-0" [.fvar "via-B"] d [a,b] [a,b,c] ∈
        targets 2 (applyInstance "rule-0" [.fvar "via-B"] d [a,b] [a,b,c]) ∧
    result "rule-0" [.fvar "via-C"] d [a,c] [a,b,c] ∈
        targets 2 (applyInstance "rule-0" [.fvar "via-C"] d [a,c] [a,b,c]) ∧
    result "rule-0" [.fvar "via-B"] d [a,b] [a,b,c] ≠
      result "rule-0" [.fvar "via-C"] d [a,c] [a,b,c] := by
  decide +kernel

#print axioms authored_kernel_nonempty
#print axioms actual_membership
#print axioms absent_membership
#print axioms repeated_premise_is_kept
#print axioms missing_premise_blocks
#print axioms empty_body_applies
#print axioms two_groundings_one_fact

end Mettapedia.GSLT.LanguageDef.ModuleFormat.SouffleDatalog.Kernel
