import Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

/-!
# Premise agreement between the general and canonical semantics

The general semantics evaluates a rule's premises over scoped assignments; the
canonical engine evaluates them over ordinary bindings. For first-order rules
whose captured values sit at the root, the ordinary projection of an assignment
is the binding list the canonical engine sees. This module proves, premise form
by premise form, that both evaluate the same premise the same way.

Freshness: the general check names the atom through the assignment and tests it
against the instantiated subject; the canonical check resolves the same atom
through the bindings and tests the same subject.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.GeneralCanonicalAgreement

open Mettapedia.OSLF.MeTTaIL
open MeTTaIL.Syntax MeTTaIL.Match MeTTaIL.RuleBinding MeTTaIL.ScopedRuleMatching
open MeTTaIL.GeneralFirstOrderProjection
open private resolveFreshVarName from Mettapedia.OSLF.MeTTaIL.Engine

/-- A premise's own schema is coherent with its site in the rule. -/
theorem nameCoherent_premise {rule : RewriteRule} {index argument : Nat} {schema : Pattern}
    (located : sitePattern? rule (.premise index 0 argument) = some schema) :
    NameCoherent rule (.premise index 0 argument) [] schema := by
  intro suffix
  simp only [List.nil_append, located, Option.bind_some]

theorem sitePattern_freshness {rule : RewriteRule} {index : Nat} {condition : FreshnessCondition}
    (declared : rule.premises[index]? = some (.freshness condition)) :
    sitePattern? rule (.premise index 0 0) = some condition.term := by
  simp [sitePattern?, declared, quantifiedBody?]

/-- On root values, the general and canonical fresh-name resolutions agree. -/
theorem freshnessName_eq_resolve {ambient : Nat} {assignment : Assignment}
    (roots : GeneralPremise.RootValues ambient assignment) (name : String) :
    GeneralPremise.freshnessName? ambient assignment name =
      resolveFreshVarName (ordinary assignment) name := by
  unfold GeneralPremise.freshnessName? resolveFreshVarName
  rw [ordinary_lookup]
  cases found : lookup assignment name with
  | none => rfl
  | some value =>
    simp only [Option.map_some, root_value_readout (roots name value found)]
    cases value.body <;> rfl

/-- **Freshness.** For a first-order freshness premise whose subject names are
bound to root values, the general check succeeds exactly when the canonical
check keeps the ordinary bindings. -/
theorem freshness_iff {rule : RewriteRule} {bound : List TypeExpr} {index : Nat}
    {assignment : Assignment} {condition : FreshnessCondition}
    (relEnv : Engine.RelationEnv) (language : LanguageDef)
    (declared : rule.premises[index]? = some (.freshness condition))
    (roots : GeneralPremise.RootValues bound.length assignment)
    (shape : FirstOrder condition.term)
    (defined : GeneralPremise.BoundNames assignment condition.term.freeFvarNames)
    (dependencies : ∀ name ∈ condition.term.freeFvarNames,
      dependencies? (GeneralRuleBindingInference.inferredSpec rule) name = some []) :
    (∃ atom subject, GeneralPremise.freshnessSubject? rule
        (GeneralRuleBindingInference.inferredSpec rule) bound index 0 assignment condition =
          some (atom, subject) ∧ GeneralPremise.SyntacticallyFresh atom subject) ↔
      ordinary assignment ∈
        Engine.premiseStepWithEnv relEnv language (ordinary assignment) (.freshness condition) := by
  have coherent := nameCoherent_premise (sitePattern_freshness declared)
  obtain ⟨subject, instantiated⟩ := instantiation_total (operation := Substitution.instantiateBVar) shape
    coherent defined roots dependencies
  have readout : applyBindings (ordinary assignment) condition.term = subject :=
    instantiation_readout shape roots instantiated
  have subjectOf : instantiateAt? rule (GeneralRuleBindingInference.inferredSpec rule) bound.length
      (.premise index 0 0) [] 0 assignment condition.term = some subject := instantiated
  simp only [GeneralPremise.freshnessSubject?, freshnessName_eq_resolve roots, subjectOf,
    Option.bind_eq_bind]
  simp only [Engine.premiseStepWithEnv, readout]
  cases resolved : resolveFreshVarName (ordinary assignment) condition.varName with
  | none => simp
  | some atom =>
    simp only [Option.bind_some, Option.some.injEq, Prod.mk.injEq]
    by_cases fresh : Substitution.checkFreshness ⟨atom, subject⟩ = true
    · have holds : GeneralPremise.SyntacticallyFresh atom subject :=
        (GeneralPremise.syntactic_freshness_iff atom subject).mp fresh
      rw [if_pos fresh]
      exact ⟨fun _ => List.mem_singleton_self _, fun _ => ⟨atom, subject, ⟨rfl, rfl⟩, holds⟩⟩
    · have fails : ¬ GeneralPremise.SyntacticallyFresh atom subject :=
        fun holds => fresh ((GeneralPremise.syntactic_freshness_iff atom subject).mpr holds)
      rw [if_neg fresh]
      constructor
      · rintro ⟨_, _, ⟨rfl, rfl⟩, holds⟩
        exact absurd holds fails
      · intro member
        cases member

end Mettapedia.OSLF.Framework.GeneralCanonicalAgreement
