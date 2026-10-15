import Mettapedia.OSLF.MeTTaIL.GeneralRuleBindingInference
import Mettapedia.OSLF.MeTTaIL.GeneralPremiseProjectionTotality

/-!
# Ordinary readback of first-order scoped assignments

First-order rule patterns have constructor and metavariable nodes. At the
rule's root context, dependency-free captures read back as their original
bodies. The reconstruction law concerns the independent scoped matching
judgment and ordinary substitution, independently of either enumerator.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection

open Syntax RuleBinding ScopedRuleMatching GeneralScopedMatch
open Mettapedia.OSLF.MeTTaIL.Match (Bindings applyBindings)

inductive FirstOrder : Pattern → Prop where
  | metavariable (name : String) : FirstOrder (.fvar name)
  | constructor (label : String) (arguments : List Pattern)
      (children : ∀ argument ∈ arguments, FirstOrder argument) : FirstOrder (.apply label arguments)

def ordinary (assignment : ScopedRuleMatching.Assignment) : Bindings :=
  assignment.map fun entry => (entry.1, entry.2.body)

theorem ordinary_lookup (assignment : ScopedRuleMatching.Assignment) (name : String) :
    (ordinary assignment).lookup name = (lookup assignment name).map ContextualValue.body := by
  induction assignment with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨key, value⟩
    simp only [ordinary, List.map_cons, Match.Bindings.lookup, lookup, List.find?_cons]
    cases test : key == name with
    | false => exact ih
    | true => rfl

theorem ordinary_variable {assignment : ScopedRuleMatching.Assignment} {name : String}
    {value : ContextualValue} (found : lookup assignment name = some value) :
    applyBindings (ordinary assignment) (.fvar name) = value.body := by
  have read := ordinary_lookup assignment name
  rw [found] at read
  unfold Match.Bindings.lookup at read
  cases selected : (ordinary assignment).find? (fun entry => entry.1 == name) with
  | none => simp [selected] at read
  | some pair =>
    simp only [selected, Option.map_some] at read
    simpa only [Match.applyBindings, selected] using Option.some.inj read

theorem root_value_readout {ambient : Nat} {value : ContextualValue}
    (root : GeneralPremise.RootValue ambient value) :
    instantiateValue? value ambient 0 [] = some value.body := by
  have occurrence : occurrenceAssignment 0 0 [] = Pattern.bvar := by
    funext index
    simp only [occurrenceAssignment, Nat.not_lt_zero, if_false, Nat.sub_zero, Nat.zero_add]
  rcases root with ⟨dependencies, caller, scopeProof⟩
  simp [instantiateValue?, dependencies, caller, occurrence, scopeProof]

mutual
  theorem matching_reconstructs {rule : RewriteRule} {ambient : Nat}
      {site : RulePatternSite} {path : List Nat} {initial final chosen : ScopedRuleMatching.Assignment}
      {schema target : Pattern} (shape : FirstOrder schema)
      (matched : GeneralScopedMatch.Matches rule (GeneralRuleBindingInference.inferredSpec rule)
        ambient site path 0 initial schema target final)
      (extension : Extends final chosen) (roots : GeneralPremise.RootValues ambient chosen) :
      applyBindings (ordinary chosen) schema = target := by
    cases shape with
    | metavariable name =>
      cases matched with
      | capture captured =>
        obtain ⟨value, _, _, found, projected⟩ :=
          GeneralRuleBindingInference.inferred_capture_interpretation captured
        have retained  := extension _ _ found
        have same := Option.some.inj ((root_value_readout (roots name value retained)).symm.trans projected)
        exact (ordinary_variable retained).trans same
    | constructor label arguments shapes =>
      cases matched with
      | constructor matchedArguments =>
        have same := arguments_reconstruct shapes matchedArguments extension roots
        simpa only [Match.applyBindings] using congrArg (Pattern.apply label) same
  termination_by sizeOf schema

  theorem arguments_reconstruct {rule : RewriteRule} {ambient index : Nat}
      {site : RulePatternSite} {path : List Nat} {initial final chosen : ScopedRuleMatching.Assignment}
      {schemas targets : List Pattern} (shapes : ∀ schema ∈ schemas, FirstOrder schema)
      (matched : GeneralScopedMatch.Arguments rule (GeneralRuleBindingInference.inferredSpec rule)
        ambient site path 0 initial index schemas targets final)
      (extension : Extends final chosen) (roots : GeneralPremise.RootValues ambient chosen) :
      schemas.map (applyBindings (ordinary chosen)) = targets := by
    cases schemas with
    | nil => cases matched; rfl
    | cons schema schemas =>
      cases matched with
      | cons first rest =>
        have head := matching_reconstructs (shapes schema (by simp)) first (rest.extends.trans extension) roots
        have tail := arguments_reconstruct (fun child member => shapes child (by simp [member])) rest extension roots
        simp only [List.map_cons, head, tail]
  termination_by sizeOf schemas
end

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
