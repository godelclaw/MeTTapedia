import Mettapedia.OSLF.NativeTypes.Certificates.RefinementChecking
import Mettapedia.TypeTheory.Calculi.NativeDependent.Examples.RefinementJudgmentControls

/-!
# Native certificate execution and rejecting controls

The independent dependent-language examples supply primitive declarations and
derivation witnesses. Raw certificates are checked computationally, including
conditional refinements and higher-order quantified predicates. Damaged premise
trees and incorrect requested judgments are rejected without semantic oracles.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Certificates.Controls

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement.Controls

deriving instance DecidableEq for TypeSymbol, PredicateSymbol

instance : DecidableEq symbols.TypeSymbol := inferInstanceAs (DecidableEq TypeSymbol)
instance : DecidableEq symbols.TermSymbol := inferInstanceAs (DecidableEq Empty)
instance : DecidableEq symbols.PredicateSymbol := inferInstanceAs (DecidableEq PredicateSymbol)

def empty : Refinement.Certificate signature := Refinement.erase emptyContext

def conditional : Refinement.Certificate signature := Refinement.erase conditionalRefinement

def quantified : Refinement.Certificate signature := Refinement.erase quantifiedPredicateFunction

def reification : Refinement.Certificate signature := Refinement.erase firstClassPredicateQuote

def newest : Refinement.Certificate signature := Refinement.erase newestAssumption

def older : Refinement.Certificate signature := Refinement.erase olderAssumption

def damagedFamily : Refinement.Certificate signature :=
  .node (.typeFamily .nil .scalar Fin.elim0) (fun _ => empty)

theorem conditional_checked : Refinement.check conditional
    (.term conditionalContext (.refine (scalar 1) (positive 1) (.var 0))
      (.comprehension (scalar 1) (positive 1))) = true := by
  exact Refinement.check_erase conditionalRefinement

theorem duplicate_origin_certificates_distinct : newest ≠ older := by
  intro same
  apply assumption_trees_retain_positions
  exact Tree.erase_injective (P := Refinement.presentation signature) same

theorem damaged_family_rejected : Refinement.check damagedFamily
    (.type .nil (scalar 0)) = false := by decide

theorem wrong_context_rejected : Refinement.check empty
    (.context (.snoc .nil (scalar 0))) = false := by decide

theorem wrong_conclusion_rejected : Refinement.check conditional
    (.entails conditionalContext .falsehood) = false := by decide

#guard Refinement.check empty (.context .nil)
#guard Refinement.check conditional
  (.term conditionalContext (.refine (scalar 1) (positive 1) (.var 0))
    (.comprehension (scalar 1) (positive 1)))
#guard Refinement.check quantified
  (.entails .nil (.all (predicateFunctionAt 0)
    (.all (scalar 1) (.implies appliedPredicate appliedPredicate))))
#guard Refinement.check reification
  (.term (.snoc .nil (scalar 0)) (.quote (positive 0)) .propositions)
#guard Refinement.check newest (.entails duplicateContext (positive 0))
#guard Refinement.check older (.entails duplicateContext (positive 0))
#guard !(Refinement.check damagedFamily (.type .nil (scalar 0)))
#guard !(Refinement.check empty (.context (.snoc .nil (scalar 0))))
#guard !(Refinement.check conditional (.entails conditionalContext .falsehood))

end Mettapedia.OSLF.NativeTypes.Certificates.Controls
