import Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge
import Mettapedia.OSLF.MeTTaIL.PatternTokens

/-!
# First-order rule packages for the generic inference checker

A rule has depth-zero metavariables and schemas in `BindingSchemaFragment`:
applications, depth-zero metavariables, bound-variable indices and fixed
collections. Object binders, substitution nodes and collection rests are
excluded. For such a package, generic checker derivations coincide with an
inductive relation whose rule instances substitute an argument vector for
metavariables. This bridge concerns structural instantiation;
`argumentValidAt 0` checks ground binding structure, not a many-sorted signature.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.FirstOrderRules

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.Match
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.InferenceChecker
open Mettapedia.GSLT.LanguageDef.InferenceInstantiationBridge

/-- A first-order inference rule: identifier, metavariable names (all at
depth zero), ordered premise schemas, and conclusion schema. -/
structure FORule where
  id : String
  vars : List String
  premises : List Pattern
  conclusion : Pattern
  deriving Repr, DecidableEq

namespace FORule

def formals (r : FORule) : List (String × Nat) := r.vars.map fun x => (x, 0)

def toSchema (r : FORule) : RuleSchema :=
  { id := ⟨r.id⟩, metavariables := r.formals, premises := r.premises,
    conclusion := r.conclusion }

/-- The substitution of an argument vector for the metavariables. -/
def bindings (r : FORule) (args : List Pattern) : Bindings := r.vars.zip args

def instPremises (r : FORule) (args : List Pattern) : List Pattern :=
  r.premises.map (applyBindings (r.bindings args))

def instConclusion (r : FORule) (args : List Pattern) : Pattern :=
  applyBindings (r.bindings args) r.conclusion

end FORule

/-- Derivability in a first-order package. -/
inductive FODerivable (rules : List FORule) : Pattern → Prop where
  | rule (r : FORule) (member : r ∈ rules) (args : List Pattern)
      (length : args.length = r.vars.length)
      (valid : ∀ a ∈ args, argumentValidAt 0 a = true)
      (premises : ∀ p ∈ r.instPremises args, FODerivable rules p) :
      FODerivable rules (r.instConclusion args)

/-- Structural admissibility of a first-order package: metavariable names are
distinct and every schema lies in the first-order fragment. -/
structure FOPackage (rules : List FORule) : Prop where
  nodup : ∀ r ∈ rules, r.vars.Nodup
  premisesFragment : ∀ r ∈ rules, BindingSchemasFragment r.formals r.premises
  conclusionFragment : ∀ r ∈ rules, BindingSchemaFragment r.formals r.conclusion

theorem FORule.formals_names (r : FORule) : r.formals.map Prod.fst = r.vars := by
  simp [FORule.formals, List.map_map, Function.comp_def]

theorem bindingsOfArguments?_formals :
    ∀ (vars : List String) (args : List Pattern), args.length = vars.length →
      bindingsOfArguments? (vars.map fun x => (x, 0)) args = some (vars.zip args)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, a :: as, h => by
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp [bindingsOfArguments?, bindingsOfArguments?_formals xs as h]

theorem argumentsOfBindings?_formals (r : FORule) (args : List Pattern)
    (nodup : r.vars.Nodup) (length : args.length = r.vars.length) :
    argumentsOfBindings? r.formals (r.bindings args) = some args := by
  apply argumentsOfBindings?_of_bindingsOfArguments
  · rw [FORule.formals_names]; exact nodup
  · intro formal member
    simp only [FORule.formals, List.mem_map] at member
    obtain ⟨_, _, rfl⟩ := member
    rfl
  · exact bindingsOfArguments?_formals r.vars args length

theorem argumentsValidAt_formals :
    ∀ (vars : List String) (args : List Pattern),
      argumentsValidAt (vars.map fun x => (x, 0)) args = true ↔
        args.length = vars.length ∧ ∀ a ∈ args, argumentValidAt 0 a = true
  | [], [] => by simp [argumentsValidAt]
  | [], _ :: _ => by simp [argumentsValidAt]
  | _ :: _, [] => by simp [argumentsValidAt]
  | x :: xs, a :: as => by
      simp only [List.map_cons, argumentsValidAt, Bool.and_eq_true,
        argumentsValidAt_formals xs as, List.length_cons, Nat.add_right_cancel_iff,
        List.mem_cons, forall_eq_or_imp]
      tauto

/-- A rule of a first-order package applies exactly to substitution
instances of its schemas. -/
theorem ruleApplication_iff (definition : ValidatedCalculusLanguageDef)
    (rules : List FORule) (package : FOPackage rules)
    (r : FORule) (member : r ∈ rules)
    (lookup : definition.1.lookupRule? ⟨r.id⟩ = some r.toSchema)
    (args premises : List Pattern) (conclusion : Pattern) :
    RuleApplication definition ⟨⟨r.id⟩, args⟩ premises conclusion ↔
      args.length = r.vars.length ∧ (∀ a ∈ args, argumentValidAt 0 a = true) ∧
        premises = r.instPremises args ∧ conclusion = r.instConclusion args := by
  constructor
  · rintro ⟨rule, hlookup, hargs, _hside, hprem, hconc⟩
    have hrule : rule = r.toSchema := by
      rw [lookup] at hlookup; exact (Option.some.inj hlookup).symm
    subst hrule
    have hvalid := (argumentsValidAt_formals r.vars args).mp hargs
    have hbind := argumentsOfBindings?_formals r args (package.nodup r member) hvalid.1
    have hp := instantiateSchemasAt?_eq_applyBindings
      (package.premisesFragment r member) hbind
    have hc := instantiateSchemaAt?_eq_applyBindings
      (package.conclusionFragment r member) hbind
    have hp' := instantiateSchemasAt?_complete hprem
    have hc' := instantiateSchemaAt?_complete hconc
    refine ⟨hvalid.1, hvalid.2, ?_, ?_⟩
    · have := hp'.symm.trans hp
      exact Option.some.inj this
    · have := hc'.symm.trans hc
      exact Option.some.inj this
  · rintro ⟨hlen, hvalid, rfl, rfl⟩
    have hbind := argumentsOfBindings?_formals r args (package.nodup r member) hlen
    refine ⟨r.toSchema, lookup, ?_, ?_, ?_, ?_⟩
    · exact (argumentsValidAt_formals r.vars args).mpr ⟨hlen, hvalid⟩
    · simp [RuleSchema.sideConditionsHold, FORule.toSchema]
    · exact instantiateSchemasAt?_sound
        (instantiateSchemasAt?_eq_applyBindings (package.premisesFragment r member) hbind)
    · exact instantiateSchemaAt?_sound
        (instantiateSchemaAt?_eq_applyBindings (package.conclusionFragment r member) hbind)

/-- The validated definition presents exactly the first-order rules. -/
structure Presents (definition : ValidatedCalculusLanguageDef)
    (rules : List FORule) : Prop where
  package : FOPackage rules
  rules_eq : definition.1.rules = rules.map FORule.toSchema

theorem Presents.lookup {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules)
    {r : FORule} (member : r ∈ rules) :
    definition.1.lookupRule? ⟨r.id⟩ = some r.toSchema := by
  have hmem : r.toSchema ∈ definition.1.rules := by
    rw [presents.rules_eq]; exact List.mem_map_of_mem member
  exact lookupRule?_eq_some_of_mem definition hmem

theorem Presents.rule_of_lookup {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules)
    {id : RuleId} {rule : RuleSchema}
    (lookup : definition.1.lookupRule? id = some rule) :
    ∃ r ∈ rules, rule = r.toSchema ∧ id = ⟨r.id⟩ := by
  have hfind : definition.1.rules.find? (fun candidate => decide (candidate.id = id)) =
      some rule := lookup
  have hmem := List.mem_of_find?_eq_some hfind
  have hid : rule.id = id := by simpa using List.find?_some hfind
  rw [presents.rules_eq] at hmem
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hmem
  exact ⟨r, hr, rfl, hid.symm⟩

/-- Every rule application of the presented definition is a first-order
rule instance, so first-order derivability is closed under it. -/
theorem foDerivable_ruleSound {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules)
    (ruleInstance : RuleInstance) (premises : List Pattern) (conclusion : Pattern)
    (application : RuleApplication definition ruleInstance premises conclusion)
    (children : ∀ p ∈ premises, FODerivable rules p) :
    FODerivable rules conclusion := by
  have application' := application
  obtain ⟨rule, lookup, _, _, _, _⟩ := application'
  obtain ⟨r, hr, rfl, hid⟩ := presents.rule_of_lookup lookup
  rcases ruleInstance with ⟨id, args⟩
  simp only at hid
  subst hid
  obtain ⟨hlen, hvalid, hprem, hconc⟩ :=
    (ruleApplication_iff definition rules presents.package r hr
      (presents.lookup hr) args _ _).mp application
  subst hprem
  subst hconc
  exact .rule r hr args hlen hvalid children

theorem foDerivable_of_derivation {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules) {goal : Pattern}
    (derivation : Derivation definition goal) : FODerivable rules goal :=
  Derivation.sound_of_ruleApplications (FODerivable rules)
    (foDerivable_ruleSound presents) derivation

theorem derivationList_of_forall {definition : ValidatedCalculusLanguageDef} :
    ∀ (premises : List Pattern), (∀ p ∈ premises, Nonempty (Derivation definition p)) →
      Nonempty (DerivationList definition premises)
  | [], _ => ⟨.nil⟩
  | p :: ps, h => by
      obtain ⟨d⟩ := h p (by simp)
      obtain ⟨ds⟩ := derivationList_of_forall ps (fun q hq => h q (by simp [hq]))
      exact ⟨.cons d ds⟩

theorem derivation_of_foDerivable {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules) {goal : Pattern}
    (derivable : FODerivable rules goal) : Nonempty (Derivation definition goal) := by
  induction derivable with
  | rule r hr args hlen hvalid _ ih =>
      obtain ⟨children⟩ := derivationList_of_forall _ ih
      have application :=
        (ruleApplication_iff definition rules presents.package r hr
          (presents.lookup hr) args (r.instPremises args) (r.instConclusion args)).mpr
          ⟨hlen, hvalid, rfl, rfl⟩
      exact ⟨.byRule ⟨⟨r.id⟩, args⟩ application children⟩

/-- Generic checker derivations of a first-order package are exactly its
first-order derivations. -/
theorem derivation_iff_foDerivable {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules) (goal : Pattern) :
    Nonempty (Derivation definition goal) ↔ FODerivable rules goal :=
  ⟨fun ⟨d⟩ => foDerivable_of_derivation presents d, derivation_of_foDerivable presents⟩

/-- Raw proof checking of a first-order package accepts some article for a
goal exactly when the goal is first-order derivable. -/
theorem checkRaw_exists_iff_foDerivable {definition : ValidatedCalculusLanguageDef}
    {rules : List FORule} (presents : Presents definition rules) (goal : Pattern) :
    (∃ proof, checkRaw definition goal proof = true) ↔ FODerivable rules goal := by
  rw [← derivation_iff_foDerivable presents goal]
  constructor
  · rintro ⟨proof, hproof⟩
    obtain ⟨derivation, -⟩ :=
      (G2_checkRaw_iff_exists_derivation_erases_to (definition := definition)
        (goal := goal) (proof := proof)).mp hproof
    exact ⟨derivation⟩
  · rintro ⟨derivation⟩
    exact ⟨derivation.erase,
      (G2_checkRaw_iff_exists_derivation_erases_to (definition := definition)
        (goal := goal) (proof := derivation.erase)).mpr ⟨derivation, rfl⟩⟩

/-- Packages combine. -/
theorem FOPackage.append {first second : List FORule}
    (hf : FOPackage first) (hs : FOPackage second) : FOPackage (first ++ second) := by
  constructor
  · intro r hr
    exact (List.mem_append.mp hr).elim (hf.nodup r) (hs.nodup r)
  · intro r hr
    exact (List.mem_append.mp hr).elim (hf.premisesFragment r) (hs.premisesFragment r)
  · intro r hr
    exact (List.mem_append.mp hr).elim (hf.conclusionFragment r) (hs.conclusionFragment r)

/-- Derivations remain valid when their real rule list is extended. -/
theorem FODerivable.mono {R S : List FORule} (hRS : R ⊆ S) {goal : Pattern}
    (derivation : FODerivable R goal) : FODerivable S goal := by
  induction derivation with
  | rule r hr args hlen hvalid _ ih => exact .rule r (hRS hr) args hlen hvalid ih

/-! ## Full storage under first-order instantiation -/

open Mettapedia.OSLF.MeTTaIL

/-- Each argument's complete structural payload is paid for by the ordered
argument vector, including names, binder metadata and binary indices. -/
theorem argument_weight_le {argument : Pattern} {arguments : List Pattern}
    (member : argument ∈ arguments) :
    PatternTokens.weight argument ≤ PatternTokens.listWeight arguments := by
  induction arguments with
  | nil => simp at member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with same | later
      · subst argument
        simp only [PatternTokens.listWeight]
        omega
      · have bound := ih later
        simp only [PatternTokens.listWeight]
        omega

mutual
  /-- Actual source binding application grows a binder-free schema by at
  most the product of its fixed payload and the supplied value budget. No
  substitution or collection-rest operation is included in this fragment. -/
  theorem applyBindings_weight (bindings : Bindings) (bound : Nat)
      (bounded : ∀ entry ∈ bindings, PatternTokens.weight entry.2 ≤ bound)
      {formals : List (String × Nat)} (schema : Pattern)
      (fragment : BindingSchemaFragment formals schema) :
      PatternTokens.weight (applyBindings bindings schema) ≤
        PatternTokens.weight schema * (bound + 1) := by
    cases schema with
    | bvar index =>
        simp only [applyBindings, PatternTokens.weight]
        nlinarith
    | fvar name =>
        cases found : bindings.find? (fun entry => entry.1 == name) with
        | none =>
            simp only [applyBindings, found, PatternTokens.weight]
            nlinarith
        | some entry =>
            have value := bounded entry (List.mem_of_find?_eq_some found)
            simp only [applyBindings, found]
            simp only [PatternTokens.weight]
            nlinarith
    | apply constructor arguments =>
        cases fragment with
        | apply items =>
            have values := applyBindings_listWeight bindings bound bounded arguments items
            simp only [applyBindings, PatternTokens.weight]
            nlinarith
    | collection collectionType elements rest =>
        cases fragment with
        | collection items =>
            have values := applyBindings_listWeight bindings bound bounded elements items
            simp only [applyBindings, List.append_nil, PatternTokens.weight, PatternTokens.optionWeight]
            nlinarith
    | lambda _ _ => cases fragment
    | multiLambda _ _ _ => cases fragment
    | subst _ _ => cases fragment
  termination_by sizeOf schema
  decreasing_by all_goals sizeOf_pattern_dec

  /-- The ordered premise vector retains every substituted occurrence. -/
  theorem applyBindings_listWeight (bindings : Bindings) (bound : Nat)
      (bounded : ∀ entry ∈ bindings, PatternTokens.weight entry.2 ≤ bound)
      {formals : List (String × Nat)} (schemas : List Pattern)
      (fragment : BindingSchemasFragment formals schemas) :
      PatternTokens.listWeight (schemas.map (applyBindings bindings)) ≤
        PatternTokens.listWeight schemas * (bound + 1) := by
    cases schemas with
    | nil => simp [PatternTokens.listWeight]
    | cons schema schemas =>
        cases fragment with
        | cons head tail =>
            have first := applyBindings_weight bindings bound bounded schema head
            have later := applyBindings_listWeight bindings bound bounded schemas tail
            simp only [List.map_cons, PatternTokens.listWeight]
            nlinarith
  termination_by sizeOf schemas
  decreasing_by all_goals sizeOf_pattern_dec
end

private theorem bindings_argument_weight (names : List String) (arguments : List Pattern) :
    ∀ entry ∈ names.zip arguments,
      PatternTokens.weight entry.2 ≤ PatternTokens.listWeight arguments := by
  induction names generalizing arguments with
  | nil => simp
  | cons name names ih =>
      cases arguments with
      | nil => simp
      | cons argument arguments =>
          intro entry member
          rcases List.mem_cons.mp member with same | later
          · subst entry
            simp only [PatternTokens.listWeight]
            omega
          · have bound := ih arguments entry later
            simp only [PatternTokens.listWeight]
            omega

/-- An instantiated source conclusion has linear full-payload growth for
each fixed first-order schema; repeated metavariables retain their copies. -/
theorem FORule.instConclusion_weight (rule : FORule) (arguments : List Pattern)
    (fragment : BindingSchemaFragment rule.formals rule.conclusion) :
    PatternTokens.weight (rule.instConclusion arguments) ≤
      PatternTokens.weight rule.conclusion * (PatternTokens.listWeight arguments + 1) :=
  applyBindings_weight (rule.bindings arguments) (PatternTokens.listWeight arguments)
    (bindings_argument_weight rule.vars arguments) rule.conclusion fragment

theorem FORule.instPremises_weight (rule : FORule) (arguments : List Pattern)
    (fragment : BindingSchemasFragment rule.formals rule.premises) :
    PatternTokens.listWeight (rule.instPremises arguments) ≤
      PatternTokens.listWeight rule.premises * (PatternTokens.listWeight arguments + 1) :=
  applyBindings_listWeight (rule.bindings arguments) (PatternTokens.listWeight arguments)
    (bindings_argument_weight rule.vars arguments) rule.premises fragment

namespace StorageControls

def repeated : FORule := ⟨"repeat", ["x"], [], .apply "Pair" [.fvar "x", .fvar "x"]⟩

/-- The source operation really copies both occurrences of its argument. -/
theorem repeated_argument (argument : Pattern) :
    repeated.instConclusion [argument] = .apply "Pair" [argument, argument] := by
  simp [repeated, FORule.instConclusion, FORule.bindings, applyBindings]

theorem repeated_argument_storage (argument : Pattern) :
    PatternTokens.weight (repeated.instConclusion [argument]) =
      8 + 2 * PatternTokens.weight argument := by
  rw [repeated_argument]
  have name : ("Pair" : String).utf8ByteSize = 4 := by decide +kernel
  simp only [PatternTokens.weight, PatternTokens.listWeight, name]
  omega

/-- A substitution node runs a different operation and cannot use the
first-order structural-instantiation bound. -/
theorem substitution_excluded (formals : List (String × Nat)) (body replacement : Pattern) :
    ¬ BindingSchemaFragment formals (.subst body replacement) := by
  intro fragment
  cases fragment

theorem residual_collection_excluded (formals : List (String × Nat))
    (kind : CollType) (elements : List Pattern) (rest : String) :
    ¬ BindingSchemaFragment formals (.collection kind elements (some rest)) := by
  intro fragment
  cases fragment

end StorageControls

end Mettapedia.GSLT.LanguageDef.FirstOrderRules
