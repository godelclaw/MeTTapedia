import Mettapedia.GSLT.LanguageDef.MeTTaILSubtermMatchAutomata
import Mettapedia.OSLF.Framework.TypeSynthesis

/-!
# Subterm match observations and authored root execution

The two automata supply exact occurrence-indexed bindings. Only root matches
are passed to the existing premise evaluator and rule instantiator. A match
at a child position does not grant contextual reduction. Recursive premises
use the canonical contextual executor at their declared fuel; equations stay
with the canonical GSLT's equivalence, rather than becoming directed rules.

The complete reduct list is preserved, including premise branching, rule
order and duplicate occurrences. This is the semantic composition layer;
execution of its MeTTa lowering is a separate correspondence obligation.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.MeTTaILMatchAutomataExecution

open Mettapedia.OSLF.MeTTaIL.Syntax Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.OSLF.MeTTaIL.ContextualStep
open Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep
open Mettapedia.OSLF.MeTTaIL.Engine
open MeTTaILFirstOrderRuleCompilation MeTTaILSubtermMatchAutomata

def atRoot (observations : List BoundMatch) : List BoundMatch :=
  observations.filter (fun matched => matched.location.position.isEmpty)

private theorem root_filter_entries (patterns : List Pattern)
    (entries : List (SubtermMatching.Position × PatternPlan)) :
    atRoot (entries.flatMap fun entry => patterns.zipIdx.flatMap fun row =>
      (matchPattern row.1 entry.2.erase).map fun bindings =>
        (⟨⟨entry.1, row.2⟩, bindings⟩ : BoundMatch)) =
    (entries.filter (fun entry => entry.1.isEmpty)).flatMap fun entry =>
      patterns.zipIdx.flatMap fun row =>
        (matchPattern row.1 entry.2.erase).map fun bindings =>
          (⟨⟨entry.1, row.2⟩, bindings⟩ : BoundMatch) := by
  induction entries with
  | nil => rfl
  | cons entry rest ih =>
      simp only [List.flatMap_cons, atRoot, List.filter_append] at ih ⊢
      rw [ih]
      cases empty : entry.1.isEmpty <;>
        simp [List.filter_flatMap, List.filter_map, Function.comp_def, empty]

private theorem subtermsList_no_root (next : Nat) (subjects : List PatternPlan) :
    (subtermsList next subjects).filter (fun entry => entry.1.isEmpty) = [] := by
  induction subjects generalizing next with
  | nil => rfl
  | cons subject subjects ih =>
      simp [subtermsList, List.filter_append, List.filter_map, ih]

theorem subterms_root (subject : PatternPlan) :
    (subterms subject).filter (fun entry => entry.1.isEmpty) = [([], subject)] := by
  cases subject <;> simp [subterms, subtermsList_no_root]

theorem atRoot_reference (patterns : List Pattern) (subject : PatternPlan) :
    atRoot (reference patterns subject) =
      patterns.zipIdx.flatMap fun row =>
        (matchPattern row.1 subject.erase).map fun bindings =>
          (⟨⟨[], row.2⟩, bindings⟩ : BoundMatch) := by
  rw [reference, root_filter_entries, subterms_root]
  simp

/-- Resolve the retained occurrence in the actual authored rule list. A bad
index cannot create a rule application. Premises and binder-depth-aware
instantiation remain the canonical operations. -/
def dispatchMatch (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveStep : Pattern → List Pattern) (matched : BoundMatch) : List Pattern :=
  match language.rewrites[matched.location.occurrence]? with
  | none => []
  | some rule =>
      (premisesUsing base language recursiveStep rule.premises matched.bindings).map
        (RuleInterpretation.syntactic.instantiateRule language rule)

def dispatchRoot (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveStep : Pattern → List Pattern) (observations : List BoundMatch) : List Pattern :=
  (atRoot observations).flatMap (dispatchMatch base language recursiveStep)

theorem dispatch_reference (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveStep : Pattern → List Pattern) (subject : PatternPlan) :
    dispatchRoot base language recursiveStep (reference (languagePatterns language) subject) =
      language.rewrites.flatMap
        (applyRuleUsing .syntactic base language recursiveStep · subject.erase) := by
  unfold dispatchRoot
  rw [atRoot_reference]
  simp only [languagePatterns, List.zipIdx_map, List.flatMap_map, Prod.map, id_eq]
  rw [List.flatMap_assoc]
  simp only [List.flatMap_map]
  have each :
      language.rewrites.zipIdx.flatMap (fun row =>
        (matchPattern row.1.left subject.erase).flatMap fun bindings =>
          dispatchMatch base language recursiveStep ⟨⟨[], row.2⟩, bindings⟩) =
      language.rewrites.zipIdx.flatMap (fun row =>
        applyRuleUsing .syntactic base language recursiveStep row.1 subject.erase) := by
    apply List.flatMap_congr
    intro row member
    have found := List.mem_zipIdx_iff_getElem?.mp member
    simp [dispatchMatch, found, Mettapedia.OSLF.MeTTaIL.InterpretedContextualStep.applyRuleUsing,
      RuleInterpretation.syntactic]
  rw [each]
  simpa only [List.flatMap_map, Function.comp_def] using
    congrArg (List.flatMap (applyRuleUsing .syntactic base language recursiveStep · subject.erase))
      (List.zipIdx_map_fst 0 language.rewrites)

/-- Dispatch depends on the exact ordered matcher contract, not a particular
control schedule. The physical row lookup, canonical premise fold and rule
instantiation are unchanged. -/
theorem dispatch_matcher_exact (implementation : OrderedMatcher)
    (exactMatches : MatchingExact implementation)
    (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveStep : Pattern → List Pattern) (subject : PatternPlan) :
    dispatchRoot base language recursiveStep
      (implementation (languagePatterns language) subject) =
      language.rewrites.flatMap
        (applyRuleUsing .syntactic base language recursiveStep · subject.erase) := by
  rw [exactMatches, dispatch_reference]

theorem normalizedTopDown_dispatch_exact (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveStep : Pattern → List Pattern) (subject : PatternPlan) :
    dispatchRoot base language recursiveStep (normalizedTopDown (languagePatterns language) subject) =
      language.rewrites.flatMap
        (applyRuleUsing .syntactic base language recursiveStep · subject.erase) :=
  dispatch_matcher_exact normalizedTopDown normalizedTopDown_matching_exact
    base language recursiveStep subject

theorem bottomUp_dispatch_exact (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveStep : Pattern → List Pattern) (subject : PatternPlan) :
    dispatchRoot base language recursiveStep (bottomUp (languagePatterns language) subject) =
      language.rewrites.flatMap
        (applyRuleUsing .syntactic base language recursiveStep · subject.erase) := by
  exact dispatch_matcher_exact bottomUp bottomUp_matching_exact base language recursiveStep subject

theorem topDown_dispatch_exact (base : BasePremiseEvaluator) (language : LanguageDef)
    (recursiveStep : Pattern → List Pattern) (subject : PatternPlan) :
    dispatchRoot base language recursiveStep (topDown (languagePatterns language) subject) =
      language.rewrites.flatMap
        (applyRuleUsing .syntactic base language recursiveStep · subject.erase) := by
  exact dispatch_matcher_exact topDown topDown_matching_exact base language recursiveStep subject

inductive Strategy where | bottomUp | topDown

def runAt (strategy : Strategy) (base : BasePremiseEvaluator) (language : LanguageDef) :
    Nat → PatternPlan → List Pattern
  | 0, _ => []
  | fuel + 1, subject =>
      let observations := match strategy with
        | .bottomUp => bottomUp (languagePatterns language) subject
        | .topDown => topDown (languagePatterns language) subject
      dispatchRoot base language (rewriteAt .syntactic base language fuel) observations

theorem runAt_exact (strategy : Strategy) (base : BasePremiseEvaluator) (language : LanguageDef)
    (fuel : Nat) (subject : PatternPlan) :
    runAt strategy base language fuel subject = rewriteAt .syntactic base language fuel subject.erase := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      cases strategy <;> unfold runAt <;>
        first | exact bottomUp_dispatch_exact _ _ _ _ | exact topDown_dispatch_exact _ _ _ _

/-- Preservation and reflection to the canonical GSLT, for every finite
contextual derivation depth. Equational representatives require the GSLT's
own closure; the executable root result list does not orient equations. -/
theorem runAt_iff_gslt_step (strategy : Strategy) (relations : RelationEnv)
    (language : LanguageDef) (equationFree : language.isEquationFree = true)
    (subject : PatternPlan) (target : Pattern) :
    (∃ fuel, target ∈ runAt strategy (engineBasePremises relations) language fuel subject) ↔
      (Mettapedia.OSLF.Framework.TypeSynthesis.langGSLTUsing relations language).Step
        subject.erase target := by
  simp only [runAt_exact, rewriteAt_syntactic_eq_contextual]
  exact (Mettapedia.OSLF.MeTTaIL.ContextualStep.exists_mem_rewriteAt_iff_step).trans
    (Mettapedia.OSLF.Framework.TypeSynthesis.langSemanticReducesUsing_iff_langReducesUsing_of_equation_free
      relations equationFree subject.erase target).symm

#print axioms runAt_exact
#print axioms runAt_iff_gslt_step

#print axioms dispatch_matcher_exact
#print axioms normalizedTopDown_dispatch_exact

end Mettapedia.GSLT.LanguageDef.MeTTaILMatchAutomataExecution
