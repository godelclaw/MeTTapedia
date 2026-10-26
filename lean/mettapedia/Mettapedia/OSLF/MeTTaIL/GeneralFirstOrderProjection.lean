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


/-- An actual successful projection of a dependency-free value has an empty
argument spine, including when authored occurrence rows are present. -/
theorem root_value_arguments_empty {ambient depth : Nat} {value : ContextualValue}
    {arguments : List Pattern} {target : Pattern} (root : GeneralPremise.RootValue ambient value)
    (read : instantiateValue? value ambient depth arguments = some target) : arguments = [] := by
  have sameLength : arguments.length = value.dependencies.length := by
    unfold instantiateValue? at read
    split at read
    · cases read
    · split at read
      · cases read
      · rename_i accepted
        by_contra different
        exact accepted (bne_iff_ne.mpr different)
  rw [root.1] at sameLength
  exact List.length_eq_zero_iff.mp sameLength

#print axioms root_value_arguments_empty

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


 theorem inferred_success_arguments_empty {rule : RewriteRule} {name : String}
    {site : RulePatternSite} {path : List Nat} {arguments : List Pattern}
    (read : arguments? rule (GeneralRuleBindingInference.inferredSpec rule) name site path = some arguments) :
    arguments = [] := by
  have original := read
  unfold arguments? at read
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at read
  obtain ⟨dependencies, declared, _⟩ := read
  have empty := GeneralRuleBindingInference.inferred_dependencies_empty declared
  exact GeneralRuleBindingInference.inferred_arguments_empty (empty ▸ declared) original

open Syntax RuleBinding ScopedRuleMatching Match

mutual
theorem FirstOrder.binderFree {schema : Pattern} (shape : FirstOrder schema) :
    Match.binderFree schema = true := by
  cases shape with
  | metavariable => rfl
  | constructor _ _ children => exact firstOrder_arguments_binderFree children
termination_by sizeOf schema

theorem firstOrder_arguments_binderFree {schemas : List Pattern}
    (shapes : ∀ schema ∈ schemas, FirstOrder schema) : binderFreeList schemas = true := by
  cases schemas with
  | nil => rfl
  | cons first rest =>
    exact Bool.and_eq_true_iff.mpr ⟨(shapes first (List.mem_cons_self ..)).binderFree,
      firstOrder_arguments_binderFree (fun child member => shapes child (List.mem_cons_of_mem _ member))⟩
termination_by sizeOf schemas
end

mutual
/-- Successful dependency-free instantiation reads the actual collection
rest and concatenates it in the same order as ordinary substitution. -/
theorem binderFree_instantiation_readout {rule : RewriteRule} {spec : RuleBindingSpec}
    {operation : Pattern → Pattern → Pattern} {ambient : Nat}
    {site : RulePatternSite} {path : List Nat} {assignment : Assignment}
    {schema target : Pattern} (shape : binderFree schema = true)
    (roots : GeneralPremise.RootValues ambient assignment)
    (read : instantiateWith? operation rule spec
      ambient site path 0 assignment schema = some target) :
    applyBindings (ordinary assignment) schema = target := by
  cases schema with
  | fvar name =>
    simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨value, found, arguments, occurrence, projected⟩ := read
    have empty := root_value_arguments_empty (roots name value found) projected
    subst arguments
    have same := Option.some.inj ((root_value_readout (roots name value found)).symm.trans projected)
    exact (ordinary_variable found).trans same
  | bvar index =>
    simp only [instantiateWith?, Option.some.injEq] at read
    simpa only [applyBindings] using read
  | apply label schemas =>
    simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨results, read, same⟩ := read
    cases Option.some.inj same
    have children := binderFree_instantiation_arguments_readout shape roots read
    simpa only [applyBindings] using congrArg (Pattern.apply label) children
  | lambda | multiLambda | subst => simp only [binderFree, Bool.false_eq_true] at shape
  | collection kind schemas rest =>
    simp only [instantiateWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨explicit, explicitRead, read⟩ := read
    have children := binderFree_instantiation_arguments_readout shape roots explicitRead
    cases rest with
    | none =>
      cases Option.some.inj read
      simp only [applyBindings, children, List.append_nil]
    | some name =>
      simp only [Option.bind_eq_some_iff] at read
      obtain ⟨value, found, arguments, occurrence, actual, projected, read⟩ := read
      have empty := root_value_arguments_empty (roots name value found) projected
      subst arguments
      have actualBody : actual = value.body :=
        Option.some.inj (projected.symm.trans (root_value_readout (roots name value found)))
      subst actual
      have stored : (ordinary assignment).lookup name = some value.body := by
        rw [ordinary_lookup, found]
        rfl
      cases body : value.body with
      | collection actualKind residual tail =>
        cases tail with
        | some _ => simp only [body] at read; cases read
        | none =>
          simp only [body] at read stored
          split at read
          · rename_i sameKind
            have sameKind : actualKind = kind := beq_iff_eq.mp sameKind
            subst actualKind
            cases Option.some.inj read
            simp only [Bindings.lookup, Option.map_eq_some_iff] at stored
            obtain ⟨entry, selected, entryBody⟩ := stored
            rcases entry with ⟨key, entryValue⟩
            change entryValue = .collection kind residual none at entryBody
            subst entryValue
            simp only [applyBindings, children, selected, beq_self_eq_true, ite_true]
          · cases read
      | _ => simp only [body] at read; cases read
termination_by sizeOf schema

theorem binderFree_instantiation_arguments_readout {rule : RewriteRule} {spec : RuleBindingSpec}
    {operation : Pattern → Pattern → Pattern} {ambient index : Nat}
    {site : RulePatternSite} {path : List Nat} {assignment : Assignment}
    {schemas targets : List Pattern} (shapes : binderFreeList schemas = true)
    (roots : GeneralPremise.RootValues ambient assignment)
    (read : instantiateArgsWith? operation rule spec
      ambient site path 0 assignment index schemas = some targets) :
    schemas.map (applyBindings (ordinary assignment)) = targets := by
  cases schemas with
  | nil =>
    simp only [instantiateArgsWith?, Option.some.injEq] at read
    simpa only [List.map_nil] using read
  | cons schema schemas =>
    obtain ⟨firstShape, restShapes⟩ := Bool.and_eq_true_iff.mp shapes
    simp only [instantiateArgsWith?, Option.bind_eq_bind, Option.bind_eq_some_iff] at read
    obtain ⟨target, first, targets, rest, same⟩ := read
    cases Option.some.inj same
    have head := binderFree_instantiation_readout firstShape roots first
    have tail := binderFree_instantiation_arguments_readout restShapes roots rest
    simp only [List.map_cons, head, tail]
termination_by sizeOf schemas
end

#print axioms binderFree_instantiation_readout
#print axioms binderFree_instantiation_arguments_readout
#print axioms FirstOrder.binderFree
#print axioms firstOrder_arguments_binderFree

end Mettapedia.OSLF.MeTTaIL.GeneralFirstOrderProjection
