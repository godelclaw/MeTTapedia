import Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceSearch

/-!
# Admission for nested collection occurrences with checked input guards

The profile discharges collection decomposition and the unnecessary structural
child-depth obligation through the retained occurrence search. Every other
general obligation remains explicit. Provider relations are finite; premises
are nullary or mixed queries with checked object input templates and canonical
provider rows. Ordinary output schemas may contain nested collections and rest
variables;
quantified and child-step premises, extra equations, wrapper laws and extrusion laws require
separate profiles. This certificate grants successor-class coverage, without
selecting a logical derivation identity or an aggregation policy.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceAdmission

open _root_.Mettapedia.OSLF.MeTTaIL.Syntax GeneralExecutionAdmission

def pending (plan : Plan) : List Obligation :=
  plan.obligations.filter fun issue => issue != .setDecomposition && issue != .childStratification

def check (plan : Plan) : Bool :=
  (pending plan).isEmpty &&
    CollectionOccurrenceMachine.checkGuardFragment plan &&
    plan.rules.all (fun declaration => RuleBinding.admittedFor declaration.rule declaration.binding.spec) &&
    plan.equations.isEmpty && (Complete.Normalized.laws plan).isEmpty &&
    (Complete.Normalized.extrusions plan).isEmpty && plan.snapshot.provider.dynamicRelations.isEmpty

structure Requirements (plan : Plan) : Prop where
  pending : pending plan = []
  fragment : CollectionOccurrenceMachine.checkGuardFragment plan = true
  admitted : ∀ declaration ∈ plan.rules,
    RuleBinding.admittedFor declaration.rule declaration.binding.spec = true
  noEquations : plan.equations = []
  noLaws : Complete.Normalized.laws plan = []
  noExtrusions : Complete.Normalized.extrusions plan = []
  finiteProvider : plan.snapshot.provider.dynamicRelations = []

theorem check_iff (plan : Plan) : check plan = true ↔ Requirements plan := by
  simp only [check, Bool.and_eq_true, List.isEmpty_iff, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨pending, fragment⟩, admitted⟩, equations⟩, laws⟩, extrusions⟩, finite⟩
    exact ⟨pending, fragment, admitted, equations, laws, extrusions, finite⟩
  · intro ready
    exact ⟨⟨⟨⟨⟨⟨ready.pending, ready.fragment⟩, ready.admitted⟩, ready.noEquations⟩,
      ready.noLaws⟩, ready.noExtrusions⟩, ready.finiteProvider⟩

structure Certificate (plan : Plan) : Type where
  checked : check plan = true

def admit? (plan : Plan) : Option (Certificate plan) :=
  if checked : check plan = true then some ⟨checked⟩ else none

theorem Certificate.requirements {plan : Plan} (certificate : Certificate plan) : Requirements plan :=
  (check_iff plan).mp certificate.checked

/-- Admission establishes exactly the hypotheses of the existing source
comparison for the actual retained Search publication. -/
theorem source_exact {plan : Plan} (certificate : Certificate plan)
    (bound : List TypeExpr) (expected : TypeExpr) (depth : Nat) (source target : Pattern) :
    (Complete.Presented.gslt plan bound expected).Step source target ↔
      ∃ work receipt, receipt ∈
          (CollectionOccurrenceSearch.search plan bound expected depth).publication
            ((CollectionOccurrenceSearch.search plan bound expected depth).run source work) ∧
        CanonicalBags.Same target receipt.target := by
  have ready := certificate.requirements
  exact CollectionOccurrenceSearch.presented_iff_published ready.fragment ready.noEquations
    ready.noLaws ready.noExtrusions depth

/-- A certificate settles the original source's outgoing steps over the
explored reachable universe. Incoming and spatial-decomposition coverage
are additional obligations. -/
theorem settled_edges_cover_steps {plan : Plan} (certificate : Certificate plan)
    (bound : List TypeExpr) (expected : TypeExpr) (depth : Nat) (source : Pattern) (work : Nat)
    (done : Complete.Settled.settled (CollectionOccurrenceSearch.search plan bound expected depth)
      (Complete.Explore.explore (CollectionOccurrenceSearch.search plan bound expected depth) source work) = true) :
    ∀ node ∈ (Complete.Explore.explore (CollectionOccurrenceSearch.search plan bound expected depth) source work).nodes,
      ∀ target, (Complete.Presented.gslt plan bound expected).Step node.state target →
        ∃ receipt target', (node.state, receipt, target') ∈ Complete.Graph.edges
            (CollectionOccurrenceSearch.search plan bound expected depth)
            (Complete.Explore.explore (CollectionOccurrenceSearch.search plan bound expected depth) source work) ∧
          CanonicalBags.Same target target' := by
  have ready := certificate.requirements
  exact CollectionOccurrenceSearch.settled_edges_cover_steps ready.fragment ready.noEquations
    ready.noLaws ready.noExtrusions depth source work done

end Mettapedia.OSLF.MeTTaIL.CollectionOccurrenceAdmission
