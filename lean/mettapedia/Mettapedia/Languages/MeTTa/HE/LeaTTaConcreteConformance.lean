import Mettapedia.Languages.MeTTa.HE.LeaTTaQueryObservationalAnchor
import Mettapedia.Languages.MeTTa.HE.EvalSpec
import Mettapedia.Languages.MeTTa.HE.Conformance
open Mettapedia.Languages.MeTTa.HE.Spec.Match.SolutionTheory
open Mettapedia.Languages.MeTTa.HE.BindingComposition
open Mettapedia.Languages.MeTTa.HE.MatchSizeTheory
open Mettapedia.Languages.MeTTa.HE.Spec.Bindings.ScopeObservation.ModelTransport

/-!
# Concrete repaired-LeaTTa conformance fixtures

This downstream module keeps executable boundary fixtures and regression
readouts separate from the reusable LeaTTa bridge and the universal
specification soundness/completeness seal.  The exact counter-sensitive
canaries remain explicit because they pin runtime behavior that a semantic
solution-theory theorem intentionally abstracts away.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

open Mettapedia.Languages.MeTTa.OSLFCore
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

mutual
private theorem atomDepth_le_scan : (atom : Atom) → atomDepth atom ≤ Bindings.atomScanFuel atom
  | .symbol _ => by simp [atomDepth,Bindings.atomScanFuel]
  | .var _ => by simp [atomDepth,Bindings.atomScanFuel]
  | .grounded _ => by simp [atomDepth,Bindings.atomScanFuel]
  | .expression atoms => Nat.add_le_add_right (listDepth_le_scan atoms) 1
private theorem listDepth_le_scan : (atoms : List Atom) → listDepth atoms ≤ Bindings.atomScanFuel.atomListScanFuel atoms
  | [] => Nat.le_refl 0
  | atom :: atoms => max_le_max (atomDepth_le_scan atom) (listDepth_le_scan atoms)
end
private theorem structural_application_depth (bindings : Bindings) (atom : Atom) :
    atomDepth atom + 2 ≤ bindings.resolutionFuel atom := by
  have bound := atomDepth_le_scan atom
  simp only [Bindings.resolutionFuel]
  omega

/-- Conformance-facing observation predicate for the repaired visible-avoid
equation interface: an HE equation step is paired with the concrete LeaTTa
`queryOp` item that observes the same successor up to α-equivalence. -/
def LeaTTaVisibleEquationStepObservation
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (src dst : Atom) (gt : Metta.GroundingTable)
    (prev : Metta.Minimal.Stack) (counter : Nat) : Prop :=
  HEEquationStepAgainstVisible space d fuel src dst ∧
  LeaTTaEquationQueryOpHit space fuel src dst gt prev counter

/-- Executable LeaTTa no-match observation: `queryOp` emits its
`NotReducible` final item for the translated query under the translated input
bindings. This is only the executable half of HE's no-match branch; the
official `queryEquations = []` premise stays separate. -/
def LeaTTaNoMatchQueryOpHit
    (space : Space) (src : Atom) (inputBindings : Bindings)
    (gt : Metta.GroundingTable) (prev : Metta.Minimal.Stack)
    (counter : Nat) : Prop :=
  Metta.Minimal.finItem prev Metta.Minimal.notReducibleA
      (toLeaTTaMatchBindings inputBindings) ∈
    (Metta.Minimal.queryOp
      (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms space.atoms) gt)
      { counter := counter, world := Metta.Minimal.World.empty }
      prev (encodeModelAtom src) (toLeaTTaMatchBindings inputBindings)).1

/-- If a non-variable-headed LeaTTa query has no executable candidates, the
real `queryOp` no-match branch emits `NotReducible`. -/
theorem queryOp_contains_notReducible_of_no_candidates
    (env : Metta.Minimal.MinEnv) (st : Metta.Minimal.St)
    (prev : Metta.Minimal.Stack) (toEval : Metta.Atom)
    (b : Metta.Bindings)
    (hNotVarHead : Metta.Minimal.isVariableHeaded toEval = false)
    (hnone : Metta.Minimal.candidatesW env st.world toEval = []) :
    Metta.Minimal.finItem prev Metta.Minimal.notReducibleA b ∈
      (Metta.Minimal.queryOp env st prev toEval b).1 := by
  unfold Metta.Minimal.queryOp
  rw [hNotVarHead]
  rw [hnone]
  simp

/-- Concrete no-match executable witness: an empty HE space has no equation
candidates for a symbol-headed expression, so LeaTTa's query layer reports
`NotReducible`. -/
theorem emptySpace_foo_noMatchQueryOpHit_counter0
    (gt : Metta.GroundingTable) :
    LeaTTaNoMatchQueryOpHit
      Space.empty (.expression [.symbol "foo"]) Bindings.empty gt [] 0 := by
  unfold LeaTTaNoMatchQueryOpHit
  apply queryOp_contains_notReducible_of_no_candidates
  · simp [encodeModelAtom, encodeModelAtoms, Metta.Minimal.isVariableHeaded]
  · simp [Space.empty, Metta.Minimal.candidatesW, Metta.Minimal.World.empty,
      Metta.Minimal.MinEnv.candidates, Metta.Minimal.MinEnv.ofAtomsGT,
      Metta.Minimal.extractRules, heHeadKey]

/-- Raw executable-hit constructor for the repaired visible-avoid equation
interface. The HE visible query premise provides the declarative companion step;
the LeaTTa premise is the actual `queryOp` hit rather than the stronger raw
candidate-transport certificate. -/
theorem equation_match_againstVisible_observation_of_queryOp_hit
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs : Atom} {qb : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (hhit :
      LeaTTaEquationQueryOpHit
        space fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter) :
    LeaTTaVisibleEquationStepObservation
      space d fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter := by
  exact
    ⟨HEEquationStepAgainstVisible.equation_match
        h_not_special h_not_grounded h_query
        (queryEquationsAgainstVisible_hasLoop_false h_query),
      hhit⟩

/-- The repaired `queryEquationsAgainstVisible` path produces a complete
LeaTTa observation once the avoid-aware raw-rule transport obligation is
available. -/
theorem equation_match_againstVisible_observation_of_transport
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs : Atom} {qb : Bindings}
    {gt : Metta.GroundingTable} {k : String}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey (encodeModelAtom (.expression es)) = some k)
    (h_query : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (htransport : EquationMatchVisibleItemTransportAgainst
      space (.expression es) rhs qb fuel gt prev counter) :
    LeaTTaVisibleEquationStepObservation
      space d fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter := by
  exact
    equation_match_againstVisible_observation_of_queryOp_hit
      (space := space) (d := d) (fuel := fuel) (es := es)
      (rhs := rhs) (qb := qb) (gt := gt) (prev := prev)
      (counter := counter)
      h_not_special h_not_grounded h_query
      (leattaEquationQueryOpHit_of_transport_againstVisible
        (space := space) (src := .expression es) (rhs := rhs)
        (qb := qb) (fuel := fuel) (gt := gt) (prev := prev)
        (counter := counter) (k := k)
        hk h_query htransport)

/-- Observation wrapper for the local freshened-item transport obligation on
the repaired visible-query interface. -/
theorem equation_match_againstVisible_observation_of_freshened_item_transport
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs : Atom} {qb : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey (encodeModelAtom (.expression es)) = some k)
    (h_query : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (hitemTransport : FreshenedQueryOpItemTransportAgainstVisible
      space (.expression es) rhs qb fuel gt prev counter) :
    LeaTTaVisibleEquationStepObservation
      space d fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter := by
  exact
    equation_match_againstVisible_observation_of_queryOp_hit
      (space := space) (d := d) (fuel := fuel) (es := es)
      (rhs := rhs) (qb := qb) (gt := gt) (prev := prev)
      (counter := counter)
      h_not_special h_not_grounded h_query
      (leattaEquationQueryOpHit_of_freshened_item_transport_againstVisible
        (space := space) (src := .expression es) (rhs := rhs)
        (qb := qb) (fuel := fuel) (gt := gt) (prev := prev)
        (counter := counter) (k := k)
        hk h_query hitemTransport)

/-- Observation wrapper for the variable-successor specialization of the
freshened-item visible-query transport. -/
theorem equation_match_againstVisible_observation_of_freshened_variable_item_transport
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs : Atom} {qb : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey (encodeModelAtom (.expression es)) = some k)
    (h_query : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (hvarTransport : FreshenedVariableQueryOpItemTransportAgainstVisible
      space (.expression es) rhs qb fuel gt prev counter) :
    LeaTTaVisibleEquationStepObservation
      space d fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter := by
  exact
    equation_match_againstVisible_observation_of_queryOp_hit
      (space := space) (d := d) (fuel := fuel) (es := es)
      (rhs := rhs) (qb := qb) (gt := gt) (prev := prev)
      (counter := counter)
      h_not_special h_not_grounded h_query
      (leattaEquationQueryOpHit_of_freshened_variable_item_transport_againstVisible
        (space := space) (src := .expression es) (rhs := rhs)
        (qb := qb) (fuel := fuel) (gt := gt) (prev := prev)
        (counter := counter) (k := k)
        hk h_query hvarTransport)

/-- Observation-level wrapper for the instantiated-item seam on the repaired
visible-avoid query interface.  For the non-ground fragment where HE recursive
application agrees with LeaTTa instantiation, it is enough to prove that the
instantiated RHS item is present in `queryOp`; this theorem packages that item
with the corresponding HE equation step. -/
theorem equation_match_againstVisible_observation_of_instantiated_item
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs : Atom} {qb : Bindings}
    {gt : Metta.GroundingTable}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    (heq : qb.equalities = [])
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings qb))
    (hdepth : atomDepth rhs + 2 ≤ fuel)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb) (encodeModelAtom rhs))
          (toLeaTTaMatchBindings qb) ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (encodeModelAtom (.expression es)) Metta.Bindings.empty).1) :
    LeaTTaVisibleEquationStepObservation
      space d fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter := by
  refine ⟨?_, ?_⟩
  · exact HEEquationStepAgainstVisible.equation_match
      h_not_special h_not_grounded h_query
      (queryEquationsAgainstVisible_hasLoop_false h_query)
  · exact
      queryOp_contains_equation_match_visible_successor_of_instantiated_item_againstVisible
        (space := space) (src := .expression es) (rhs := rhs) (qb := qb)
        (fuel := fuel) (gt := gt)
        prev counter h_query heq hfresh hdepth hitem

/-- Conditional HE-side equation-step simulation: once the single remaining
specialized transport lemma is supplied, an HE `equation_match` successor is
already visible on LeaTTa's executable `queryOp` interface up to α-renaming.
This packages the positive P1 bridge at the actual
`HESmallStep.equation_match` boundary while keeping the one honest proof debt
explicit. -/
theorem equation_match_queryOp_visible_successor_of_transport
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs : Atom} {qb : Bindings}
    {gt : Metta.GroundingTable} {k : String}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (_h_not_special : ¬ SpecialFormHead (.expression es))
    (_h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey (encodeModelAtom (.expression es)) = some k)
    (h_query : (rhs, qb) ∈ queryEquations space (.expression es) fuel)
    (_h_no_loop : qb.hasLoop = false)
    (htransport : EquationMatchVisibleItemTransport
      space (.expression es) rhs qb fuel gt prev counter) :
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (encodeModelAtom (.expression es)) Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (encodeModelAtom (qb.applyFull rhs fuel)) := by
  exact
    queryOp_contains_equation_match_visible_successor_of_transport
      (space := space) (src := .expression es) (rhs := rhs) (qb := qb)
      (fuel := fuel) (gt := gt) (k := k) prev counter hk h_query htransport

/-- Small packaged interface theorem for the HE `equation_match` frontier:
under the honest alpha-level transport hypothesis, we can exhibit both the
actual HE small-step and the corresponding executable LeaTTa `queryOp` witness
at once. This is a more semantic entry point for downstream consumers than the
raw premise bundle alone. -/
theorem equation_match_queryOp_visible_successor_package_of_transport
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs : Atom} {qb : Bindings}
    {gt : Metta.GroundingTable} {k : String}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey (encodeModelAtom (.expression es)) = some k)
    (h_query : (rhs, qb) ∈ queryEquations space (.expression es) fuel)
    (h_scoped : (rhs, qb) ∈ queryEquationsAvoiding
      (equationScope [] (.expression es) Atom.undefinedType Bindings.empty) space (.expression es) fuel)
    (h_no_loop : qb.hasLoop = false)
    (htransport : EquationMatchVisibleItemTransport
      space (.expression es) rhs qb fuel gt prev counter) :
    HESmallStep space d fuel (.expression es) (qb.applyFull rhs fuel) ∧
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (encodeModelAtom (.expression es)) Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (encodeModelAtom (qb.applyFull rhs fuel)) := by
  refine ⟨HESmallStep.equation_match h_not_special h_not_grounded h_scoped h_no_loop, ?_⟩
  exact
    equation_match_queryOp_visible_successor_of_transport
      (space := space) (d := d) (fuel := fuel) (es := es) (rhs := rhs)
      (qb := qb) (gt := gt) (k := k) prev counter
      h_not_special h_not_grounded hk h_query h_no_loop htransport

/-- The actual scoped-query witness derives loop freedom at the visible
transport boundary. No restriction to non-variable assignment payloads is
needed. -/
theorem equation_match_queryOp_visible_successor_package_of_scoped_transport
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs : Atom} {qb : Bindings}
    {gt : Metta.GroundingTable} {k : String}
    (prev : Metta.Minimal.Stack) (counter : Nat)
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey (encodeModelAtom (.expression es)) = some k)
    (h_query : (rhs, qb) ∈ queryEquations space (.expression es) fuel)
    (h_scoped : (rhs, qb) ∈ queryEquationsAvoiding
      (equationScope [] (.expression es) Atom.undefinedType Bindings.empty) space (.expression es) fuel)
    (htransport : EquationMatchVisibleItemTransport
      space (.expression es) rhs qb fuel gt prev counter) :
    HESmallStep space d fuel (.expression es) (qb.applyFull rhs fuel) ∧
    ∃ emitted m,
      Metta.Minimal.evalResult prev emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (encodeModelAtom (.expression es)) Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (encodeModelAtom (qb.applyFull rhs fuel)) := by
  exact
    equation_match_queryOp_visible_successor_package_of_transport
      (space := space) (d := d) (fuel := fuel) (es := es) (rhs := rhs)
      (qb := qb) (gt := gt) (k := k) prev counter
      h_not_special h_not_grounded hk h_query h_scoped
      (queryEquationsAvoiding_hasLoop_false h_scoped) htransport

/-!
The previous theorem closes the final MOPS membership step once an exact raw
rule/match witness has already been transported. The converse direction is not
available for arbitrary HE `equation_match` steps: HE freshens every equation
locally before matching, while raw `equalityReductions` ranges over the
unfreshened space rules. If the RHS contains a variable that is not grounded by
the match, HE can legitimately step to a freshened variable name that never
appears in the raw MOPS reduct set. We pin that boundary down with a concrete
counterexample rather than silently pretending the exact simulation theorem is
already within reach.
-/

private def freshRhsBoundarySpace : Space :=
  Space.ofList [.expression [.symbol "=", .expression [.symbol "q"], .var "z"]]

private theorem queryEquations_freshRhsBoundary :
    queryEquations freshRhsBoundarySpace (.expression [.symbol "q"]) 10 =
      [(.var "z#0", Bindings.empty)] := by
  rfl

private theorem queryEquationsAvoiding_freshRhsBoundary :
    queryEquationsAvoiding [] freshRhsBoundarySpace (.expression [.symbol "q"]) 10 =
      [(.var "z#0", Bindings.empty)] := by
  rfl

private theorem freshRhsBoundary_cover :
    CoversEvaluation [] [] (.expression [.symbol "q"]) Atom.undefinedType Bindings.empty := by
  intro name h
  simp [equationScope, Atom.undefinedType, atomVariables, atomListVariables, Bindings.names, Bindings.empty] at h

private theorem queryEquationsAgainstVisible_freshRhsBoundary :
    queryEquationsAgainstVisible freshRhsBoundarySpace (.expression [.symbol "q"]) 10 =
      [(.var "z#0", Bindings.empty)] := by
  rfl

private theorem freshRhsBoundary_empty_applyFull_z0 :
    Bindings.empty.applyFull (.var "z#0") 10 = .var "z#0" := by
  rw [Bindings.applyFull_no_equalities (b := Bindings.empty) rfl]
  rfl

private def freshRhsBoundaryQueryAtom : Metta.Atom :=
  encodeModelAtom (.expression [.symbol "q"])

private def freshRhsBoundaryQueryRule : Metta.Atom × Metta.Atom :=
  (encodeModelAtom (.expression [.symbol "q"]), encodeModelAtom (.var "z"))

/-- At the exact counter-sensitive work-item layer targeted by
`QueryOpWitnessTransport`, the boundary example produces HE's `z#0` name when
LeaTTa processes the rule at counter `0`. -/
private theorem queryOpItemsOfRule_freshRhsBoundary_counter0 :
    queryOpItemsOfRule [] freshRhsBoundaryQueryAtom Metta.Bindings.empty 0
      freshRhsBoundaryQueryRule =
        [Metta.Minimal.evalResult [] (Metta.Atom.var "z#0") Metta.Bindings.empty] := by
  have hfresh :
      Metta.Minimal.freshenRule 0 freshRhsBoundaryQueryRule.1 freshRhsBoundaryQueryRule.2 =
        (freshRhsBoundaryQueryRule.1, Metta.Atom.var "z#0") := by
    simp [freshRhsBoundaryQueryRule, encodeModelAtom,
      Metta.Minimal.freshenRule, Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup]
    decide
  have hmatch :
      Metta.matchAtoms freshRhsBoundaryQueryRule.1 freshRhsBoundaryQueryAtom =
        [Metta.Bindings.empty] := by
    simp [freshRhsBoundaryQueryRule, freshRhsBoundaryQueryAtom, encodeModelAtom,
      Metta.matchAtoms, Metta.matchAtomsWith, Metta.matchAll, merge_empty_right]
    rfl
  have hcompat := freshenRuleAvoiding_eq_legacy_empty_of_target_vars_nil
    0 freshRhsBoundaryQueryAtom freshRhsBoundaryQueryRule.1 freshRhsBoundaryQueryRule.2
    (by simp [freshRhsBoundaryQueryAtom, encodeModelAtom, Metta.Atom.vars])
  unfold queryOpItemsOfRule Metta.Minimal.queryOpItemsOfRule
  rw [hcompat, hfresh]
  simp [hmatch, Metta.Bindings.empty, merge_empty_right, Metta.Bindings.hasLoop,
    Metta.Bindings.vars, Metta.Minimal.evalResult, Metta.instantiate_nil]

/-- The same raw rule/redex pair produces a different freshened work item once
LeaTTa's runtime counter has advanced. This is the exact counter-alignment debt
the positive non-ground bridge must account for. -/
private theorem queryOpItemsOfRule_freshRhsBoundary_counter5 :
    queryOpItemsOfRule [] freshRhsBoundaryQueryAtom Metta.Bindings.empty 5
      freshRhsBoundaryQueryRule =
        [Metta.Minimal.evalResult [] (Metta.Atom.var "z#5") Metta.Bindings.empty] := by
  have hfresh :
      Metta.Minimal.freshenRule 5 freshRhsBoundaryQueryRule.1 freshRhsBoundaryQueryRule.2 =
        (freshRhsBoundaryQueryRule.1, Metta.Atom.var "z#5") := by
    simp [freshRhsBoundaryQueryRule, encodeModelAtom,
      Metta.Minimal.freshenRule, Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup]
    decide
  have hmatch :
      Metta.matchAtoms freshRhsBoundaryQueryRule.1 freshRhsBoundaryQueryAtom =
        [Metta.Bindings.empty] := by
    simp [freshRhsBoundaryQueryRule, freshRhsBoundaryQueryAtom, encodeModelAtom,
      Metta.matchAtoms, Metta.matchAtomsWith, Metta.matchAll, merge_empty_right]
    rfl
  have hcompat := freshenRuleAvoiding_eq_legacy_empty_of_target_vars_nil
    5 freshRhsBoundaryQueryAtom freshRhsBoundaryQueryRule.1 freshRhsBoundaryQueryRule.2
    (by simp [freshRhsBoundaryQueryAtom, encodeModelAtom, Metta.Atom.vars])
  unfold queryOpItemsOfRule Metta.Minimal.queryOpItemsOfRule
  rw [hcompat, hfresh]
  simp [hmatch, Metta.Bindings.empty, merge_empty_right, Metta.Bindings.hasLoop,
    Metta.Bindings.vars, Metta.Minimal.evalResult, Metta.instantiate_nil]

/-- Concrete counter boundary at the exact work-item layer used by the bridge:
the boundary rule contributes different freshened items at counters `0` and
`5`, so any literal positive transport theorem must align those counters (or
work modulo alpha-renaming). -/
theorem queryOpItemsOfRule_freshRhsBoundary_counter_mismatch :
    queryOpItemsOfRule [] freshRhsBoundaryQueryAtom Metta.Bindings.empty 0
        freshRhsBoundaryQueryRule ≠
      queryOpItemsOfRule [] freshRhsBoundaryQueryAtom Metta.Bindings.empty 5
        freshRhsBoundaryQueryRule := by
  rw [queryOpItemsOfRule_freshRhsBoundary_counter0,
    queryOpItemsOfRule_freshRhsBoundary_counter5]
  simp [Metta.Minimal.evalResult, Metta.Minimal.finItem]

/-- The old literal target really is false at arbitrary runtime counters: on
the boundary example, HE's visible successor is the freshened atom `z#0`, but
LeaTTa's `queryOp` work-item at counter `5` is necessarily `z#5`. This is why
the corrected positive bridge above lives modulo `Metta.AlphaEq` rather than
literal atom equality. -/
theorem freshRhsBoundary_no_literal_visible_successor_counter5
    (gt : Metta.GroundingTable) :
    ¬ ∃ pre post m,
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms freshRhsBoundarySpace.atoms) gt)
          Metta.Minimal.World.empty freshRhsBoundaryQueryAtom =
        pre ++ freshRhsBoundaryQueryRule :: post ∧
      Metta.Minimal.evalResult [] (Metta.Atom.var "z#0") m ∈
        queryOpItemsOfRule [] freshRhsBoundaryQueryAtom Metta.Bindings.empty 5
          freshRhsBoundaryQueryRule := by
  intro hlit
  obtain ⟨pre, post, m, hsplit, hitem⟩ := hlit
  have hsingle :
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms freshRhsBoundarySpace.atoms) gt)
          Metta.Minimal.World.empty freshRhsBoundaryQueryAtom =
        [freshRhsBoundaryQueryRule] := by
    simp [freshRhsBoundarySpace, Space.ofList, freshRhsBoundaryQueryAtom,
      freshRhsBoundaryQueryRule, Metta.Minimal.candidatesW, Metta.Minimal.World.empty,
      Metta.Minimal.MinEnv.candidates, Metta.Minimal.headKey,
      Metta.Minimal.MinEnv.ofAtomsGT, Metta.Minimal.extractRules, encodeModelAtoms,
      encodeModelAtom]
  rw [hsingle] at hsplit
  have hpre_nil : pre = [] := by
    cases pre with
    | nil =>
      rfl
    | cons hd tl =>
      simp at hsplit
  subst hpre_nil
  have hitem5 :
      Metta.Minimal.evalResult [] (Metta.Atom.var "z#0") m ∈
        queryOpItemsOfRule [] freshRhsBoundaryQueryAtom Metta.Bindings.empty 5
          freshRhsBoundaryQueryRule := by
    simpa using hitem
  rw [queryOpItemsOfRule_freshRhsBoundary_counter5] at hitem5
  simp [Metta.Minimal.evalResult, Metta.Minimal.finItem] at hitem5

/-- The original exact counter-sensitive transport hypothesis is not merely
undischarged; it is false once LeaTTa's runtime freshening counter has
advanced past the HE witness index. The fresh-RHS boundary exhibits that
failure already at counter `5`. -/
theorem not_QueryOpWitnessTransport_freshRhsBoundary_counter5
    (gt : Metta.GroundingTable) :
    ¬ QueryOpWitnessTransport
        freshRhsBoundarySpace (.expression [.symbol "q"]) (.var "z#0")
        Bindings.empty 10 gt [] 5 := by
  intro htransport
  have hk : Metta.Minimal.headKey freshRhsBoundaryQueryAtom = some "q" := by
    simp [freshRhsBoundaryQueryAtom, encodeModelAtom, Metta.Minimal.headKey]
  have hzip :
      (Atom.expression [Atom.symbol "=", .expression [.symbol "q"], .var "z"], 0) ∈
        freshRhsBoundarySpace.atoms.zipIdx := by
    simp [freshRhsBoundarySpace, Space.ofList]
  have hmatch :
      FaithfulQueryWitness (.expression [.symbol "q"])
        (freshenEquation 0 (.expression [.symbol "q"]) (.var "z") 10).1
        Bindings.empty 10 := by
    unfold FaithfulQueryWitness
    refine ⟨Bindings.empty, ?_⟩
    constructor
    · decide
    constructor
    · simp [mergeBindings, Bindings.empty]
    · rfl
  obtain ⟨pre, post, hsplit, hitem⟩ := htransport hk hzip hmatch
  have hsingle :
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms freshRhsBoundarySpace.atoms) gt)
          Metta.Minimal.World.empty freshRhsBoundaryQueryAtom =
        [freshRhsBoundaryQueryRule] := by
    simp [freshRhsBoundarySpace, Space.ofList, freshRhsBoundaryQueryAtom,
      freshRhsBoundaryQueryRule, Metta.Minimal.candidatesW, Metta.Minimal.World.empty,
      Metta.Minimal.MinEnv.candidates, Metta.Minimal.headKey,
      Metta.Minimal.MinEnv.ofAtomsGT, Metta.Minimal.extractRules, encodeModelAtoms,
      encodeModelAtom]
  have hsplit' :
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms freshRhsBoundarySpace.atoms) gt)
          Metta.Minimal.World.empty freshRhsBoundaryQueryAtom =
        pre ++ freshRhsBoundaryQueryRule :: post := by
    simpa [freshRhsBoundaryQueryAtom, freshRhsBoundaryQueryRule] using hsplit
  have hshape :
      [freshRhsBoundaryQueryRule] = pre ++ freshRhsBoundaryQueryRule :: post := by
    calc
      [freshRhsBoundaryQueryRule] =
          Metta.Minimal.candidatesW
            (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms freshRhsBoundarySpace.atoms) gt)
            Metta.Minimal.World.empty freshRhsBoundaryQueryAtom := hsingle.symm
      _ = pre ++ freshRhsBoundaryQueryRule :: post := hsplit'
  have hpre_nil : pre = [] := by
    cases pre with
    | nil =>
        rfl
    | cons hd tl =>
        simp at hshape
  subst hpre_nil
  have hsplit0 :
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms freshRhsBoundarySpace.atoms) gt)
          Metta.Minimal.World.empty freshRhsBoundaryQueryAtom =
        [] ++ freshRhsBoundaryQueryRule :: post := by
    simpa [freshRhsBoundaryQueryAtom, freshRhsBoundaryQueryRule] using hsplit
  refine freshRhsBoundary_no_literal_visible_successor_counter5 gt ?_
  refine ⟨[], post, Metta.Bindings.empty, hsplit0, ?_⟩
  simpa [freshRhsBoundaryQueryAtom, freshRhsBoundaryQueryRule,
    encodeModelAtom, toLeaTTaMatchBindings_empty, Metta.Bindings.empty] using hitem

/-- The abbreviation `EquationMatchQueryOpTransport` inherits the same concrete
counterexample. -/
theorem not_EquationMatchQueryOpTransport_freshRhsBoundary_counter5
    (gt : Metta.GroundingTable) :
    ¬ EquationMatchQueryOpTransport
        (space := freshRhsBoundarySpace) (src := .expression [.symbol "q"])
        (rhs := .var "z#0") (qb := Bindings.empty) (fuel := 10) (gt := gt) [] 5 := by
  simpa [EquationMatchQueryOpTransport] using
    not_QueryOpWitnessTransport_freshRhsBoundary_counter5 gt

/-- The same boundary example succeeds once we ask for the honest notion of
agreement: the runtime item `z#5` is alpha-equivalent to HE's visible
successor `z#0`. -/
theorem freshRhsBoundary_alpha_visible_successor_counter5
    (gt : Metta.GroundingTable) :
    ∃ pre post emitted m,
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms freshRhsBoundarySpace.atoms) gt)
          Metta.Minimal.World.empty freshRhsBoundaryQueryAtom =
        pre ++ freshRhsBoundaryQueryRule :: post ∧
      Metta.Minimal.evalResult [] emitted m ∈
        queryOpItemsOfRule [] freshRhsBoundaryQueryAtom Metta.Bindings.empty 5
          freshRhsBoundaryQueryRule ∧
      Metta.AlphaEq emitted (Metta.Atom.var "z#0") := by
  refine ⟨[], [], Metta.Atom.var "z#5", Metta.Bindings.empty, ?_, ?_, ?_⟩
  · simp [freshRhsBoundarySpace, Space.ofList, freshRhsBoundaryQueryAtom,
      freshRhsBoundaryQueryRule, Metta.Minimal.candidatesW, Metta.Minimal.World.empty,
      Metta.Minimal.MinEnv.candidates, Metta.Minimal.headKey,
      Metta.Minimal.MinEnv.ofAtomsGT, Metta.Minimal.extractRules, encodeModelAtoms,
      encodeModelAtom]
  · simpa [freshRhsBoundaryQueryAtom, freshRhsBoundaryQueryRule, encodeModelAtom] using
      (show Metta.Minimal.evalResult [] (Metta.Atom.var "z#5") Metta.Bindings.empty ∈
          queryOpItemsOfRule [] freshRhsBoundaryQueryAtom Metta.Bindings.empty 5
            freshRhsBoundaryQueryRule from by
          rw [queryOpItemsOfRule_freshRhsBoundary_counter5]
          simp [Metta.Minimal.evalResult, Metta.Minimal.finItem])
  · exact alphaEq_var_var "z#5" "z#0"

/-- The corrected alpha-level transport obligation is genuinely inhabitable on
the fresh-RHS boundary at runtime counter `5`: although the old literal
transport fails there, the executable `queryOp` item still lands in the honest
alpha-equivalence class of HE's visible successor. -/
theorem freshRhsBoundary_EquationMatchVisibleItemTransport_counter5
    (gt : Metta.GroundingTable) :
    EquationMatchVisibleItemTransport
        freshRhsBoundarySpace (.expression [.symbol "q"]) (.var "z#0")
        Bindings.empty 10 gt [] 5 := by
  intro idx lhs rawRhs k hk hzip _hmatch
  have hshape :
      (lhs = .expression [.symbol "q"] ∧ rawRhs = .var "z") ∧ idx = 0 := by
    simpa [freshRhsBoundarySpace, Space.ofList] using hzip
  rcases hshape with ⟨⟨hlhs, hrhs⟩, hidx⟩
  subst hidx
  subst hlhs
  subst hrhs
  have hkq : k = "q" := by
    simpa [freshRhsBoundaryQueryAtom, encodeModelAtom, Metta.Minimal.headKey] using hk.symm
  subst hkq
  refine ⟨[], [], Metta.Atom.var "z#5", Metta.Bindings.empty, ?_, ?_, ?_⟩
  · simp [freshRhsBoundarySpace, Space.ofList, Metta.Minimal.candidatesW, Metta.Minimal.World.empty,
      Metta.Minimal.MinEnv.candidates, Metta.Minimal.headKey,
      Metta.Minimal.MinEnv.ofAtomsGT, Metta.Minimal.extractRules, encodeModelAtoms,
      encodeModelAtom]
  · change Metta.Minimal.evalResult [] (Metta.Atom.var "z#5") Metta.Bindings.empty ∈
        queryOpItemsOfRule [] freshRhsBoundaryQueryAtom Metta.Bindings.empty 5
          freshRhsBoundaryQueryRule
    rw [queryOpItemsOfRule_freshRhsBoundary_counter5]
    simp [Metta.Minimal.evalResult, Metta.Minimal.finItem]
  · rw [freshRhsBoundary_empty_applyFull_z0]
    exact alphaEq_var_var "z#5" "z#0"

/-- The avoid-aware transport target is also inhabited on the fresh-RHS
boundary. Here the query atom has no visible variables, so the avoid-aware
freshening interface agrees extensionally with the ordinary freshening interface,
while still exercising the repaired theorem interface. -/
theorem freshRhsBoundary_FreshenedQueryOpItemTransportAgainstVisible_counter5
    (gt : Metta.GroundingTable) :
    FreshenedQueryOpItemTransportAgainstVisible
        freshRhsBoundarySpace (.expression [.symbol "q"]) (.var "z#0")
        Bindings.empty 10 gt [] 5 := by
  intro idx lhs rawRhs pre post k hk hzip _hmatch hsplit
  have hshape :
      (lhs = .expression [.symbol "q"] ∧ rawRhs = .var "z") ∧ idx = 0 := by
    simpa [freshRhsBoundarySpace, Space.ofList] using hzip
  rcases hshape with ⟨⟨hlhs, hrhs⟩, hidx⟩
  subst hidx
  subst hlhs
  subst hrhs
  have hkq : k = "q" := by
    simpa [freshRhsBoundaryQueryAtom, encodeModelAtom, Metta.Minimal.headKey] using hk.symm
  subst hkq
  have hsingle :
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms freshRhsBoundarySpace.atoms) gt)
          Metta.Minimal.World.empty (encodeModelAtom (.expression [.symbol "q"])) =
        [(encodeModelAtom (.expression [.symbol "q"]), encodeModelAtom (.var "z"))] := by
    simp [freshRhsBoundarySpace, Space.ofList, Metta.Minimal.candidatesW, Metta.Minimal.World.empty,
      Metta.Minimal.MinEnv.candidates, Metta.Minimal.headKey,
      Metta.Minimal.MinEnv.ofAtomsGT, Metta.Minimal.extractRules, encodeModelAtoms,
      encodeModelAtom]
  rw [hsingle] at hsplit
  have hpre_nil : pre = [] := by
    cases pre with
    | nil => rfl
    | cons hd tl => simp at hsplit
  subst hpre_nil
  have hpost_nil : post = [] := by
    simpa using hsplit
  subst hpost_nil
  have hcompat := freshenRuleAvoiding_eq_legacy_empty_of_target_vars_nil
    5 (encodeModelAtom (.expression [.symbol "q"]))
      (encodeModelAtom (.expression [.symbol "q"])) (encodeModelAtom (.var "z"))
      (by simp [encodeModelAtom, Metta.Atom.vars])
  refine
    ⟨encodeModelAtom (.expression [.symbol "q"]), Metta.Atom.var "z#5",
      [], [], Metta.Atom.var "z#5",
      ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_nil, Nat.add_zero]
    rw [hcompat]
    simp [encodeModelAtom, Metta.Minimal.freshenRule, Metta.Atom.vars,
      Metta.Subst.apply, Metta.Subst.lookup]
    decide
  · simp [encodeModelAtom, Metta.matchAtoms, Metta.matchAtomsWith,
      Metta.matchAll, merge_empty_right, Metta.Bindings.hasLoop,
      Metta.Bindings.vars]
  · rw [merge_empty_right]
    simp [Metta.Bindings.empty]
  · simp [Metta.Bindings.hasLoop, Metta.Bindings.vars]
  · simp [Metta.instantiate_nil]
  · rw [freshRhsBoundary_empty_applyFull_z0]
    exact alphaEq_var_var "z#5" "z#0"

theorem freshRhsBoundary_EquationMatchVisibleItemTransportAgainst_counter5
    (gt : Metta.GroundingTable) :
    EquationMatchVisibleItemTransportAgainst
        freshRhsBoundarySpace (.expression [.symbol "q"]) (.var "z#0")
        Bindings.empty 10 gt [] 5 := by
  exact
    equationMatchVisibleItemTransportAgainst_of_freshened_item_transport
      (freshRhsBoundary_FreshenedQueryOpItemTransportAgainstVisible_counter5 gt)

/-- The corrected visible-successor bridge is already enough to recover a real
`queryOp` witness on the fresh-RHS boundary. This is the smallest positive
regression check showing the repaired alpha-level target is not only weaker
than the false literal one, but actually usable by the generic bridge. -/
theorem queryOp_contains_equation_match_visible_successor_freshRhsBoundary_counter5
    (gt : Metta.GroundingTable) :
    ∃ emitted m,
      Metta.Minimal.evalResult [] emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms freshRhsBoundarySpace.atoms) gt)
          { counter := 5, world := Metta.Minimal.World.empty }
          [] freshRhsBoundaryQueryAtom Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (Metta.Atom.var "z#0") := by
  have hk : Metta.Minimal.headKey freshRhsBoundaryQueryAtom = some "q" := by
    simp [freshRhsBoundaryQueryAtom, encodeModelAtom, Metta.Minimal.headKey]
  have hquery : (.var "z#0", Bindings.empty) ∈
      queryEquations freshRhsBoundarySpace (.expression [.symbol "q"]) 10 := by
    simp [queryEquations_freshRhsBoundary]
  exact
    queryOp_contains_equation_match_visible_successor_of_transport
      (space := freshRhsBoundarySpace)
      (src := .expression [.symbol "q"])
      (rhs := .var "z#0")
      (qb := Bindings.empty)
      (fuel := 10)
      (gt := gt)
      (k := "q")
      (prev := [])
      (counter := 5)
      hk
      hquery
      (freshRhsBoundary_EquationMatchVisibleItemTransport_counter5 gt)

/-- The repaired visible-avoid query interface also recovers the fresh-RHS
boundary witness through the new avoid-aware transport theorem. This pins the
`queryEquationsAgainstVisible` path to the same alpha-level executable
`queryOp` target. -/
theorem queryOp_contains_equation_match_visible_successor_againstVisible_freshRhsBoundary_counter5
    (gt : Metta.GroundingTable) :
    ∃ emitted m,
      Metta.Minimal.evalResult [] emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms freshRhsBoundarySpace.atoms) gt)
          { counter := 5, world := Metta.Minimal.World.empty }
          [] freshRhsBoundaryQueryAtom Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (Metta.Atom.var "z#0") := by
  have hk : Metta.Minimal.headKey freshRhsBoundaryQueryAtom = some "q" := by
    simp [freshRhsBoundaryQueryAtom, encodeModelAtom, Metta.Minimal.headKey]
  have hquery : (.var "z#0", Bindings.empty) ∈
      queryEquationsAgainstVisible freshRhsBoundarySpace (.expression [.symbol "q"]) 10 := by
    simp [queryEquationsAgainstVisible_freshRhsBoundary]
  exact
    queryOp_contains_equation_match_visible_successor_againstVisible_of_transport
      (space := freshRhsBoundarySpace)
      (src := .expression [.symbol "q"])
      (rhs := .var "z#0")
      (qb := Bindings.empty)
      (fuel := 10)
      (gt := gt)
      (k := "q")
      (prev := [])
      (counter := 5)
      hk
      hquery
      (freshRhsBoundary_EquationMatchVisibleItemTransportAgainst_counter5 gt)

/-- End-to-end repaired equation-step package on the fresh-RHS boundary: the
visible-avoid HE equation-step interface and the LeaTTa executable `queryOp`
witness agree up to alpha-equivalence at the counter where literal fresh-name
transport fails. -/
theorem equation_match_againstVisible_freshRhsBoundary_queryOp_visible_successor_counter5
    (gt : Metta.GroundingTable) :
    HEEquationStepAgainstVisible freshRhsBoundarySpace GroundedDispatch.none 10
      (.expression [.symbol "q"]) (.var "z#0") ∧
    ∃ emitted m,
      Metta.Minimal.evalResult [] emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms freshRhsBoundarySpace.atoms) gt)
          { counter := 5, world := Metta.Minimal.World.empty }
          [] freshRhsBoundaryQueryAtom Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (Metta.Atom.var "z#0") := by
  have hNotSpecial : ¬ SpecialFormHead (.expression [.symbol "q"]) := by
    simp [SpecialFormHead]
  have hNotGrounded : HeadNotExecutable GroundedDispatch.none (.expression [.symbol "q"]) := by
    simp [HeadNotExecutable, GroundedDispatch.none]
  have hk : Metta.Minimal.headKey freshRhsBoundaryQueryAtom = some "q" := by
    simp [freshRhsBoundaryQueryAtom, encodeModelAtom, Metta.Minimal.headKey]
  have hquery : (.var "z#0", Bindings.empty) ∈
      queryEquationsAgainstVisible freshRhsBoundarySpace (.expression [.symbol "q"]) 10 := by
    simp [queryEquationsAgainstVisible_freshRhsBoundary]
  simpa [freshRhsBoundary_empty_applyFull_z0, freshRhsBoundaryQueryAtom,
      encodeModelAtom] using
    (equation_match_againstVisible_queryOp_visible_successor_package_of_transport
      (space := freshRhsBoundarySpace)
      (d := GroundedDispatch.none)
      (fuel := 10)
      (es := [.symbol "q"])
      (rhs := .var "z#0")
      (qb := Bindings.empty)
      (gt := gt)
      (k := "q")
      (prev := [])
      (counter := 5)
      hNotSpecial
      hNotGrounded
      hk
      hquery
      (freshRhsBoundary_EquationMatchVisibleItemTransportAgainst_counter5 gt))

/-- Named observation witness for the repaired visible-avoid path at the
fresh-RHS boundary. This is the conformance-facing form of the same regression:
the HE step and concrete LeaTTa `queryOp` item live in one proof object. -/
theorem freshRhsBoundary_againstVisible_observation_counter5
    (gt : Metta.GroundingTable) :
    LeaTTaVisibleEquationStepObservation
      freshRhsBoundarySpace GroundedDispatch.none 10
      (.expression [.symbol "q"]) (.var "z#0") gt [] 5 := by
  have hNotSpecial : ¬ SpecialFormHead (.expression [.symbol "q"]) := by
    simp [SpecialFormHead]
  have hNotGrounded : HeadNotExecutable GroundedDispatch.none (.expression [.symbol "q"]) := by
    simp [HeadNotExecutable, GroundedDispatch.none]
  have hk : Metta.Minimal.headKey freshRhsBoundaryQueryAtom = some "q" := by
    simp [freshRhsBoundaryQueryAtom, encodeModelAtom, Metta.Minimal.headKey]
  have hquery : (.var "z#0", Bindings.empty) ∈
      queryEquationsAgainstVisible freshRhsBoundarySpace (.expression [.symbol "q"]) 10 := by
    simp [queryEquationsAgainstVisible_freshRhsBoundary]
  simpa [freshRhsBoundary_empty_applyFull_z0, freshRhsBoundaryQueryAtom,
      encodeModelAtom] using
    (equation_match_againstVisible_observation_of_freshened_item_transport
      (space := freshRhsBoundarySpace)
      (d := GroundedDispatch.none)
      (fuel := 10)
      (es := [.symbol "q"])
      (rhs := .var "z#0")
      (qb := Bindings.empty)
      (gt := gt)
      (k := "q")
      (prev := [])
      (counter := 5)
      hNotSpecial
      hNotGrounded
      hk
      hquery
      (freshRhsBoundary_FreshenedQueryOpItemTransportAgainstVisible_counter5 gt))

/-- A concrete conformance-facing package: a LeaTTa executable observation is
paired with the corresponding declarative HE `MettaCall` result. -/
def LeaTTaObservedMettaCall
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (src dst type_ : Atom) (inputBindings outputBindings : Bindings)
    (gt : Metta.GroundingTable) (prev : Metta.Minimal.Stack)
    (counter : Nat) : Prop :=
  LeaTTaVisibleEquationStepObservation space d fuel src dst gt prev counter ∧
  MettaCall space d src type_ inputBindings (dst, outputBindings)

/-- Engine-step-shaped equation-call fragment for LeaTTa observations.

This is intentionally narrower than a full LeaTTa engine instance: it packages a
visible executable observation together with the exact HE equation-query,
merge, loop, and ordinary-call return premises needed to build the official
declarative `MettaCall` constructor. -/
def LeaTTaEquationMettaCallStep
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (src type_ : Atom) (inputBindings : Bindings) (result : ResultPair) : Prop :=
  ∃ rhs queryBindings merged visibleDst gt prev counter,
    LeaTTaVisibleEquationStepObservation space d fuel src visibleDst gt prev counter ∧
    isErrorAtom src = false ∧
    HeadNotExecutable d src ∧
    (∃ avoid, CoversEvaluation avoid [] src type_ inputBindings ∧
      (rhs, queryBindings) ∈ queryEquationsAvoiding avoid space src fuel) ∧
    merged ∈ mergeBindings queryBindings inputBindings fuel ∧
    merged.hasLoop = false ∧
    OrdinaryCallReturnRel space d src (merged.applyFull rhs fuel) type_ merged result

/-- Generic equation-match constructor for the observed-call package.  It
keeps the executable LeaTTa observation separate from the HE declarative
premises, then builds the `MettaCall` side with the official HE rule. -/
theorem observedMettaCall_of_equation_match
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src dst type_ rhs : Atom}
    {queryBindings inputBindings merged outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat}
    (hobs : LeaTTaVisibleEquationStepObservation space d fuel src dst gt prev counter)
    (h_not_error : isErrorAtom src = false)
    (h_not_grounded : HeadNotExecutable d src)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] src type_ inputBindings)
    (h_query : (rhs, queryBindings) ∈ queryEquationsAvoiding avoid space src fuel)
    (h_merge : merged ∈ mergeBindings queryBindings inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d src (merged.applyFull rhs fuel) type_ merged
        (dst, outputBindings)) :
    LeaTTaObservedMettaCall
      space d fuel src dst type_ inputBindings outputBindings gt prev counter := by
  refine ⟨hobs, ?_⟩
  apply MettaCall.equation_match (fuel := fuel)
    (rhs := rhs) (queryBindings := queryBindings) (merged := merged)
    (h_not_error := h_not_error) (h_cover := h_cover)
  · cases src with
    | symbol s =>
        trivial
    | var v =>
        trivial
    | grounded g =>
        trivial
    | expression es =>
        cases es with
        | nil =>
            trivial
        | cons op rest =>
            simpa [HeadNotExecutable] using h_not_grounded
  · exact h_query
  · exact h_merge
  · exact h_no_loop
  · exact h_recurse

/-- The step-shaped LeaTTa equation-call fragment is sound for the official HE
`MettaCall` relation.  This is the hook needed by the engine-parametric
conformance boundary before a complete LeaTTa engine instance exists. -/
theorem leattaEquationMettaCallStep_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src type_ : Atom} {inputBindings : Bindings} {result : ResultPair} :
    LeaTTaEquationMettaCallStep space d fuel src type_ inputBindings result →
      MettaCall space d src type_ inputBindings result := by
  rintro ⟨rhs, queryBindings, merged, _visibleDst, _gt, _prev, _counter,
    _hobs, h_not_error, h_not_grounded, ⟨avoid, h_cover, h_query⟩, h_merge, h_no_loop,
    h_recurse⟩
  apply MettaCall.equation_match (fuel := fuel)
    (rhs := rhs) (queryBindings := queryBindings) (merged := merged)
    (h_not_error := h_not_error) (h_cover := h_cover)
  · cases src with
    | symbol s =>
        trivial
    | var v =>
        trivial
    | grounded g =>
        trivial
    | expression es =>
        cases es with
        | nil =>
            trivial
        | cons op rest =>
            simpa [HeadNotExecutable] using h_not_grounded
  · exact h_query
  · exact h_merge
  · exact h_no_loop
  · exact h_recurse

/-- Step-shaped no-match fragment: executable LeaTTa `queryOp` observes
`NotReducible`, and the official HE query path is empty, so the public
`MettaCall.no_match` branch returns the original atom and bindings. -/
def LeaTTaNoMatchMettaCallStep
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (src _type : Atom) (inputBindings : Bindings) (result : ResultPair) :
    Prop :=
  result = (src, inputBindings) ∧
  ∃ gt prev counter,
    LeaTTaNoMatchQueryOpHit space src inputBindings gt prev counter ∧
    isErrorAtom src = false ∧
    HeadNotExecutable d src ∧
    queryEquationsAvoiding (equationScope [] src _type inputBindings) space src fuel = []

theorem leattaNoMatchMettaCallStep_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src type_ : Atom} {inputBindings : Bindings} {result : ResultPair} :
    LeaTTaNoMatchMettaCallStep space d fuel src type_ inputBindings result →
      MettaCall space d src type_ inputBindings result := by
  rintro ⟨hresult, _gt, _prev, _counter, _hobs, h_not_error,
    h_not_grounded, h_no_eqs⟩
  subst result
  cases src with
  | symbol s =>
      exact MettaCall.no_match
        (space := space) (dispatch := d)
        (atom := .symbol s) (type_ := type_) (b := inputBindings)
        (fuel := fuel) h_not_error trivial
        (equationScope_coversEvaluation [] _ type_ inputBindings) h_no_eqs
  | var v =>
      exact MettaCall.no_match
        (space := space) (dispatch := d)
        (atom := .var v) (type_ := type_) (b := inputBindings)
        (fuel := fuel) h_not_error trivial
        (equationScope_coversEvaluation [] _ type_ inputBindings) h_no_eqs
  | grounded g =>
      exact MettaCall.no_match
        (space := space) (dispatch := d)
        (atom := .grounded g) (type_ := type_) (b := inputBindings)
        (fuel := fuel) h_not_error trivial
        (equationScope_coversEvaluation [] _ type_ inputBindings) h_no_eqs
  | expression es =>
      cases es with
      | nil =>
          exact MettaCall.no_match
            (space := space) (dispatch := d)
            (atom := .expression []) (type_ := type_) (b := inputBindings)
            (fuel := fuel) h_not_error trivial
            (equationScope_coversEvaluation [] _ type_ inputBindings) h_no_eqs
      | cons op rest =>
          have h_not_grounded_spec :
              d.isExecutable op = false ∧
              op ≠ .symbol "unify" ∧
              op ≠ .symbol "switch-minimal" := by
            simpa [HeadNotExecutable] using h_not_grounded
          exact MettaCall.no_match
            (space := space) (dispatch := d)
            (atom := .expression (op :: rest)) (type_ := type_)
            (b := inputBindings) (fuel := fuel)
            h_not_error h_not_grounded_spec (equationScope_coversEvaluation [] _ type_ inputBindings) h_no_eqs

/-- The currently proved non-ground LeaTTa call fragment: equation hits and
no-match observations. This is still not a complete LeaTTa call relation; it
only packages the two non-ground query branches already paired with explicit
official HE premises. -/
def LeaTTaEquationNoMatchMettaCallStep
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (src type_ : Atom) (inputBindings : Bindings) (result : ResultPair) :
    Prop :=
  LeaTTaEquationMettaCallStep space d fuel src type_ inputBindings result ∨
  LeaTTaNoMatchMettaCallStep space d fuel src type_ inputBindings result

theorem leattaEquationNoMatchMettaCallStep_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src type_ : Atom} {inputBindings : Bindings} {result : ResultPair} :
    LeaTTaEquationNoMatchMettaCallStep
      space d fuel src type_ inputBindings result →
      MettaCall space d src type_ inputBindings result := by
  intro hstep
  cases hstep with
  | inl heq =>
      exact leattaEquationMettaCallStep_sound heq
  | inr hno =>
      exact leattaNoMatchMettaCallStep_sound hno

theorem emptySpace_foo_noMatchMettaCallStep_counter0 :
    LeaTTaNoMatchMettaCallStep
      Space.empty GroundedDispatch.none 10
      (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty
      (.expression [.symbol "foo"], Bindings.empty) := by
  refine ⟨rfl, (default : Metta.GroundingTable), [], 0,
    emptySpace_foo_noMatchQueryOpHit_counter0 (default : Metta.GroundingTable),
    ?_, ?_, ?_⟩
  · rfl
  · simp [HeadNotExecutable, GroundedDispatch.none]
  · rfl

theorem emptySpace_foo_equationNoMatchMettaCallStep_counter0 :
    LeaTTaEquationNoMatchMettaCallStep
      Space.empty GroundedDispatch.none 10
      (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty
      (.expression [.symbol "foo"], Bindings.empty) :=
  Or.inr emptySpace_foo_noMatchMettaCallStep_counter0

/-! ### Primitive `unify` fragment

The LeaTTa executable side is `unifyOp`; the HE reference side remains
`unifySuccessResults` and the official raw `MettaCall` constructors. -/

/-- Executable LeaTTa observation for the primitive `unify` helper. -/
def LeaTTaUnifyOpHit
    (target pattern thenBranch elseBranch : Atom)
    (inputBindings : Bindings) (result : ResultPair)
    (prev : Metta.Minimal.Stack) : Prop :=
  Metta.Minimal.finItem prev
      (encodeModelAtom result.1) (toLeaTTaMatchBindings result.2) ∈
    Metta.Minimal.unifyOp prev
      (encodeModelAtom target) (encodeModelAtom pattern)
      (encodeModelAtom thenBranch) (encodeModelAtom elseBranch)
      (toLeaTTaMatchBindings inputBindings)

/-- If LeaTTa's matcher has no local `unifyOp` matches, the executable helper
emits the else branch under the incoming bindings. -/
theorem leattaUnifyOpHit_fallback_of_matchAtoms_nil
    (target pattern thenBranch elseBranch : Atom)
    (inputBindings : Bindings) (prev : Metta.Minimal.Stack)
    (hmatch :
      Metta.matchAtoms (encodeModelAtom target) (encodeModelAtom pattern) = []) :
    LeaTTaUnifyOpHit target pattern thenBranch elseBranch inputBindings
      (elseBranch, inputBindings) prev := by
  unfold LeaTTaUnifyOpHit
  exact
    Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness.mem_unifyOp_fallback_of_matchAtoms_nil
      prev (encodeModelAtom target) (encodeModelAtom pattern)
      (encodeModelAtom thenBranch) (encodeModelAtom elseBranch)
      (toLeaTTaMatchBindings inputBindings) hmatch

/-- Successful LeaTTa matcher/merge evidence produces the executable `unifyOp`
success item.  The HE side is not inferred here; callers must still supply the
official `unifySuccessResults` witness at the call layer. -/
theorem leattaUnifyOpHit_success_of_match_merge_noLoop
    {target pattern thenBranch elseBranch resultAtom : Atom}
    {inputBindings resultBindings : Bindings}
    {prev : Metta.Minimal.Stack} {matchBindings merged : Metta.Bindings}
    (hmatch :
      matchBindings ∈
        Metta.matchAtoms (encodeModelAtom target) (encodeModelAtom pattern))
    (hmerge :
      merged ∈
        Metta.Bindings.merge (toLeaTTaMatchBindings inputBindings) matchBindings)
    (hloop : Metta.Bindings.hasLoop merged = false)
    (hresultAtom :
      encodeModelAtom resultAtom =
        Metta.instantiate merged (encodeModelAtom thenBranch))
    (hresultBindings : toLeaTTaMatchBindings resultBindings = merged) :
    LeaTTaUnifyOpHit target pattern thenBranch elseBranch inputBindings
      (resultAtom, resultBindings) prev := by
  unfold LeaTTaUnifyOpHit
  rw [hresultAtom, hresultBindings]
  exact
    Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness.mem_unifyOp_success_of_match_merge_noLoop
      prev (encodeModelAtom target) (encodeModelAtom pattern)
      (encodeModelAtom thenBranch) (encodeModelAtom elseBranch)
      (toLeaTTaMatchBindings inputBindings) matchBindings merged
      hmatch hmerge hloop

/-- Extensional executable LeaTTa observation for primitive `unify`.  The
runtime item may carry any binding list whose direct value lookups agree with
the official HE result binding translation. -/
def LeaTTaUnifyOpHitExt
    (target pattern thenBranch elseBranch : Atom)
    (inputBindings : Bindings) (result : ResultPair)
    (prev : Metta.Minimal.Stack) : Prop :=
  ∃ emittedBindings : Metta.Bindings,
    Metta.Minimal.finItem prev
        (encodeModelAtom result.1) emittedBindings ∈
      Metta.Minimal.unifyOp prev
        (encodeModelAtom target) (encodeModelAtom pattern)
        (encodeModelAtom thenBranch) (encodeModelAtom elseBranch)
        (toLeaTTaMatchBindings inputBindings) ∧
    LeaBindingsLookupEq emittedBindings (toLeaTTaMatchBindings result.2)

/-- Successful LeaTTa matcher/merge evidence produces an extensional `unifyOp`
success item.  This is the binding-order tolerant sibling of
`leattaUnifyOpHit_success_of_match_merge_noLoop`. -/
theorem leattaUnifyOpHitExt_success_of_match_merge_noLoop
    {target pattern thenBranch elseBranch resultAtom : Atom}
    {inputBindings resultBindings : Bindings}
    {prev : Metta.Minimal.Stack} {matchBindings emittedMerged : Metta.Bindings}
    (hmatch :
      matchBindings ∈
        Metta.matchAtoms (encodeModelAtom target) (encodeModelAtom pattern))
    (hmerge :
      emittedMerged ∈
        Metta.Bindings.merge (toLeaTTaMatchBindings inputBindings) matchBindings)
    (hloop : Metta.Bindings.hasLoop emittedMerged = false)
    (hresultAtom :
      encodeModelAtom resultAtom =
        Metta.instantiate emittedMerged (encodeModelAtom thenBranch))
    (hresultBindings :
      LeaBindingsLookupEq emittedMerged (toLeaTTaMatchBindings resultBindings)) :
    LeaTTaUnifyOpHitExt target pattern thenBranch elseBranch inputBindings
      (resultAtom, resultBindings) prev := by
  unfold LeaTTaUnifyOpHitExt
  refine ⟨emittedMerged, ?_, hresultBindings⟩
  rw [hresultAtom]
  exact
    Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness.mem_unifyOp_success_of_match_merge_noLoop
      prev (encodeModelAtom target) (encodeModelAtom pattern)
      (encodeModelAtom thenBranch) (encodeModelAtom elseBranch)
      (toLeaTTaMatchBindings inputBindings) matchBindings emittedMerged
      hmatch hmerge hloop

/-- Step-shaped primitive `unify` fragment.  The executable LeaTTa `unifyOp`
hit is paired with the official HE raw-success or raw-fallback premise. -/
def LeaTTaUnifyMettaCallStep
    (_space : Space) (_d : GroundedDispatch) (fuel : Nat)
    (src _type : Atom) (inputBindings : Bindings) (result : ResultPair) :
    Prop :=
  ∃ target pattern thenBranch elseBranch prev,
    src = .expression [.symbol "unify", target, pattern, thenBranch, elseBranch] ∧
    isErrorAtom src = false ∧
    LeaTTaUnifyOpHit target pattern thenBranch elseBranch
      inputBindings result prev ∧
    (result ∈ unifySuccessResults target pattern thenBranch inputBindings fuel ∨
      result = (elseBranch, inputBindings) ∧
        unifySuccessResults target pattern thenBranch inputBindings fuel = [])

/-- Step-shaped primitive `unify` fragment with a lookup-extensional executable
binding observation.  The HE reference result remains exact. -/
def LeaTTaUnifyMettaCallStepExt
    (_space : Space) (_d : GroundedDispatch) (fuel : Nat)
    (src _type : Atom) (inputBindings : Bindings) (result : ResultPair) :
    Prop :=
  ∃ target pattern thenBranch elseBranch prev,
    src = .expression [.symbol "unify", target, pattern, thenBranch, elseBranch] ∧
    isErrorAtom src = false ∧
    LeaTTaUnifyOpHitExt target pattern thenBranch elseBranch
      inputBindings result prev ∧
    (result ∈ unifySuccessResults target pattern thenBranch inputBindings fuel ∨
      result = (elseBranch, inputBindings) ∧
        unifySuccessResults target pattern thenBranch inputBindings fuel = [])

/-- Transported success constructor for primitive `unify`: HE supplies the
official raw success result, while the executable side supplies a corresponding
LeaTTa matcher/merge item. The reached HE record has no equality entries, so its
assignment readout agrees with equality-aware application. -/
theorem leattaUnifyMettaCallStep_success_of_transported_match_merge
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {target pattern thenBranch elseBranch type_ : Atom}
    {inputBindings matchBindings merged : Bindings}
    {prev : Metta.Minimal.Stack}
    (hmatchHE : matchBindings ∈ matchAtoms target pattern fuel)
    (hmergeHE : merged ∈ mergeBindings matchBindings
      (Spec.Type.Presentation.BindingTheory.aliasConstraints inputBindings) fuel)
    (hloopHE : merged.hasLoop = false)
    (hmatchLea :
      toLeaTTaMatchBindings matchBindings ∈
        Metta.matchAtoms (encodeModelAtom target) (encodeModelAtom pattern))
    (hmergeLea :
      toLeaTTaMatchBindings merged ∈
        Metta.Bindings.merge (toLeaTTaMatchBindings inputBindings)
          (toLeaTTaMatchBindings matchBindings))
    (hloopLea : Metta.Bindings.hasLoop (toLeaTTaMatchBindings merged) = false)
    (hno : NoVarAssignmentValues merged)
    (hkeys : AssignmentsNodup merged)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings merged))
    (heq : merged.equalities = []) :
    LeaTTaUnifyMettaCallStep space d fuel
      (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
      type_ inputBindings
      (merged.applyDefault thenBranch, merged) := by
  have hinst :
      encodeModelAtom (merged.applyDefault thenBranch) =
        Metta.instantiate (toLeaTTaMatchBindings merged)
          (encodeModelAtom thenBranch) := by
    simpa [Bindings.applyDefault] using
      encodeModelAtom_apply_eq_instantiate_matchBindings_of_noVarAssignmentValues
        hno hkeys hfresh (merged.resolutionFuel thenBranch) thenBranch
          (structural_application_depth merged thenBranch)
  have hhit :
      LeaTTaUnifyOpHit target pattern thenBranch elseBranch inputBindings
        (merged.applyDefault thenBranch, merged) prev := by
    exact
      leattaUnifyOpHit_success_of_match_merge_noLoop
        (target := target) (pattern := pattern) (thenBranch := thenBranch)
        (elseBranch := elseBranch) (inputBindings := inputBindings)
        (resultAtom := merged.applyDefault thenBranch)
        (resultBindings := merged) (prev := prev)
        (matchBindings := toLeaTTaMatchBindings matchBindings)
        (merged := toLeaTTaMatchBindings merged)
        hmatchLea hmergeLea hloopLea hinst rfl
  have href :
      (merged.applyDefault thenBranch, merged) ∈
        unifySuccessResults target pattern thenBranch inputBindings fuel := by
    unfold unifySuccessResults
    refine List.mem_flatMap.mpr ?_
    refine ⟨matchBindings, hmatchHE, ?_⟩
    exact List.mem_filterMap.mpr ⟨merged, hmergeHE, by simp [hloopHE, Bindings.applyFull_no_equalities heq, Bindings.applyDefault]⟩
  exact ⟨target, pattern, thenBranch, elseBranch, prev,
    rfl, rfl, hhit, Or.inl href⟩

/-- Transported success constructor for primitive `unify` using the
lookup-extensional executable observation.  This keeps the official HE result
binding exact while allowing LeaTTa's runtime merge list to use an equivalent
order. The equality-free reached HE record justifies the assignment readout. -/
theorem leattaUnifyMettaCallStepExt_success_of_transported_match_merge
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {target pattern thenBranch elseBranch type_ : Atom}
    {inputBindings matchBindings merged : Bindings}
    {prev : Metta.Minimal.Stack}
    {runtimeMatchBindings emittedMerged : Metta.Bindings}
    (hmatchHE : matchBindings ∈ matchAtoms target pattern fuel)
    (hmergeHE : merged ∈ mergeBindings matchBindings
      (Spec.Type.Presentation.BindingTheory.aliasConstraints inputBindings) fuel)
    (hloopHE : merged.hasLoop = false)
    (hmatchLea :
      runtimeMatchBindings ∈
        Metta.matchAtoms (encodeModelAtom target) (encodeModelAtom pattern))
    (hmergeLea :
      emittedMerged ∈
        Metta.Bindings.merge (toLeaTTaMatchBindings inputBindings)
          runtimeMatchBindings)
    (hloopLea : Metta.Bindings.hasLoop emittedMerged = false)
    (hbindingsEq : LeaBindingsLookupEq emittedMerged (toLeaTTaMatchBindings merged))
    (hno : NoVarAssignmentValues merged)
    (hkeys : AssignmentsNodup merged)
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings merged))
    (heq : merged.equalities = []) :
    LeaTTaUnifyMettaCallStepExt space d fuel
      (.expression [.symbol "unify", target, pattern, thenBranch, elseBranch])
      type_ inputBindings
      (merged.applyDefault thenBranch, merged) := by
  have hinstExact :
      encodeModelAtom (merged.applyDefault thenBranch) =
        Metta.instantiate (toLeaTTaMatchBindings merged)
          (encodeModelAtom thenBranch) := by
    simpa [Bindings.applyDefault] using
      encodeModelAtom_apply_eq_instantiate_matchBindings_of_noVarAssignmentValues
        hno hkeys hfresh (merged.resolutionFuel thenBranch) thenBranch
          (structural_application_depth merged thenBranch)
  have hinstRuntime :
      Metta.instantiate emittedMerged (encodeModelAtom thenBranch) =
        Metta.instantiate (toLeaTTaMatchBindings merged)
          (encodeModelAtom thenBranch) :=
    LeaBindingsLookupEq.instantiate hbindingsEq (encodeModelAtom thenBranch)
  have hinst :
      encodeModelAtom (merged.applyDefault thenBranch) =
        Metta.instantiate emittedMerged (encodeModelAtom thenBranch) :=
    hinstExact.trans hinstRuntime.symm
  have hhit :
      LeaTTaUnifyOpHitExt target pattern thenBranch elseBranch inputBindings
        (merged.applyDefault thenBranch, merged) prev := by
    exact
      leattaUnifyOpHitExt_success_of_match_merge_noLoop
        (target := target) (pattern := pattern) (thenBranch := thenBranch)
        (elseBranch := elseBranch) (inputBindings := inputBindings)
        (resultAtom := merged.applyDefault thenBranch)
        (resultBindings := merged) (prev := prev)
        (matchBindings := runtimeMatchBindings)
        (emittedMerged := emittedMerged)
        hmatchLea hmergeLea hloopLea hinst hbindingsEq
  have href :
      (merged.applyDefault thenBranch, merged) ∈
        unifySuccessResults target pattern thenBranch inputBindings fuel := by
    unfold unifySuccessResults
    refine List.mem_flatMap.mpr ?_
    refine ⟨matchBindings, hmatchHE, ?_⟩
    exact List.mem_filterMap.mpr ⟨merged, hmergeHE, by simp [hloopHE, Bindings.applyFull_no_equalities heq, Bindings.applyDefault]⟩
  exact ⟨target, pattern, thenBranch, elseBranch, prev,
    rfl, rfl, hhit, Or.inl href⟩

/-- LeaTTa's two-sided matcher agrees with HE's official singleton result when
the target is ground and the pattern is a variable. -/
theorem leattaMatchAtoms_ground_var_exact
    {target : Atom} (v : String) (hground : GroundAtom target) :
    Metta.matchAtoms (encodeModelAtom target) (encodeModelAtom (.var v)) =
      [[Metta.BindingRel.val v (encodeModelAtom target)]] := by
  have hclosed : (encodeModelAtom target).vars = [] :=
    encodeModelAtom_vars_nil_of_ground hground
  have hoccurs : Metta.Subst.occurs v (encodeModelAtom target) = false :=
    occurs_eq_false_of_not_mem_vars v (encodeModelAtom target) (by
      rw [hclosed]
      simp)
  have hloop : Metta.Bindings.hasLoop
      [Metta.BindingRel.val v (encodeModelAtom target)] = false :=
    hasLoop_singleton_val_closed_false v (encodeModelAtom target) hclosed
  cases target with
  | var w =>
      exact (GroundAtom.not_var hground).elim
  | symbol s =>
      have hloop' : Metta.Bindings.hasLoop
          [Metta.BindingRel.val v (Metta.Atom.sym s)] = false := by
        simpa [encodeModelAtom] using hloop
      simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hloop']
  | grounded g =>
      have hloop' : Metta.Bindings.hasLoop
          [Metta.BindingRel.val v (Metta.Atom.gnd (encodeModelGround g))] = false := by
        simpa [encodeModelAtom] using hloop
      simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom, hloop']
  | expression es =>
      have hoccursExpr :
          Metta.Subst.occurs v (Metta.Atom.expr (es.map encodeModelAtom)) = false := by
        simpa only [encodeModelAtom, Spec.Match.SolutionTheory.encodeModelAtoms_eq_map] using hoccurs
      have hloop' : Metta.Bindings.hasLoop
          [Metta.BindingRel.val v (Metta.Atom.expr (es.map encodeModelAtom))] = false := by
        simpa only [encodeModelAtom, Spec.Match.SolutionTheory.encodeModelAtoms_eq_map] using hloop
      simp [Metta.matchAtoms, Metta.matchAtomsWith, encodeModelAtom,
        Spec.Match.SolutionTheory.encodeModelAtoms_eq_map, hoccursExpr, hloop']

/-- Primitive `unify` success on the ground-target/variable-pattern fragment:
all HE and LeaTTa matcher/merge witnesses are derived from the official
groundness premise, rather than supplied as side conditions. -/
theorem leattaUnifyMettaCallStep_success_ground_var_empty_seed
    {space : Space} {d : GroundedDispatch} {n : Nat}
    {target thenBranch elseBranch type_ : Atom} {v : String}
    (hground : GroundAtom target) :
    LeaTTaUnifyMettaCallStep space d (n + 1)
      (.expression [.symbol "unify", target, .var v, thenBranch, elseBranch])
      type_ Bindings.empty
      ((Bindings.empty.assign v target).applyDefault thenBranch,
        Bindings.empty.assign v target) := by
  let merged : Bindings := Bindings.empty.assign v target
  have hgroundMerged : GroundBindings merged :=
    GroundBindings.assign GroundBindings.empty hground
  have hno : NoVarAssignmentValues merged :=
    noVarAssignmentValues_of_groundBindings hgroundMerged
  have hkeys : AssignmentsNodup merged := by
    simp [merged, AssignmentsNodup, Bindings.empty, Bindings.assign,
      Bindings.isBound, Bindings.lookup]
  have hloopHE : merged.hasLoop = false :=
    GroundBindings.hasLoop_false hgroundMerged
  have hmatchHE : merged ∈ matchAtoms target (.var v) (n + 1) := by
    rw [matchAtoms_ground_var_exact target v n hground]
    simp [merged]
  have hmergeHE : merged ∈ mergeBindings merged Bindings.empty (n + 1) := by
    rw [mergeBindings_empty_right merged n]
    simp
  have hmergedLea :
      toLeaTTaMatchBindings merged =
        [Metta.BindingRel.val v (encodeModelAtom target)] := by
    cases target with
    | var w =>
        exact (GroundAtom.not_var hground).elim
    | symbol s =>
        simp [merged, toLeaTTaMatchBindings, toLeaTTaMatchSubst,
          Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup,
          Metta.Bindings.ofSubst, encodeModelAtom]
    | grounded g =>
        simp [merged, toLeaTTaMatchBindings, toLeaTTaMatchSubst,
          Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup,
          Metta.Bindings.ofSubst, encodeModelAtom]
    | expression es =>
        simp [merged, toLeaTTaMatchBindings, toLeaTTaMatchSubst,
          Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup,
          Metta.Bindings.ofSubst, encodeModelAtom]
  have hmatchLea :
      toLeaTTaMatchBindings merged ∈
        Metta.matchAtoms (encodeModelAtom target) (encodeModelAtom (.var v)) := by
    rw [leattaMatchAtoms_ground_var_exact v hground]
    simp [hmergedLea]
  have hmergeLea :
      toLeaTTaMatchBindings merged ∈
        Metta.Bindings.merge (toLeaTTaMatchBindings Bindings.empty)
          (toLeaTTaMatchBindings merged) := by
    rw [hmergedLea]
    cases target with
    | var w =>
        exact (GroundAtom.not_var hground).elim
    | symbol s =>
        simp [toLeaTTaMatchBindings_empty, Metta.Bindings.merge,
          Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
          Metta.Bindings.addValRaw,
          Metta.Bindings.removeVal,
          encodeModelAtom]
    | grounded g =>
        simp [toLeaTTaMatchBindings_empty, Metta.Bindings.merge,
          Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
          Metta.Bindings.addValRaw,
          Metta.Bindings.removeVal,
          encodeModelAtom]
    | expression es =>
        simp [toLeaTTaMatchBindings_empty, Metta.Bindings.merge,
          Metta.Bindings.mergeOne, Metta.Bindings.addVarBinding,
          Metta.Bindings.addValRaw,
          Metta.Bindings.removeVal,
          encodeModelAtom]
  have hloopLea :
      Metta.Bindings.hasLoop (toLeaTTaMatchBindings merged) = false := by
    rw [hmergedLea]
    exact Metta.Bindings.hasLoop_singleton_val_of_not_mem
      v (encodeModelAtom target) (by
        rw [encodeModelAtom_vars_nil_of_ground_core hground]
        simp)
  have hfresh :
      ValueKeysFreshForValues (toLeaTTaMatchBindings merged) := by
    rw [hmergedLea]
    simp [ValueKeysFreshForValues, bindingValueKeys,
      encodeModelAtom_vars_nil_of_ground_core hground]
  simpa [merged] using
    leattaUnifyMettaCallStep_success_of_transported_match_merge
      (space := space) (d := d) (fuel := n + 1)
      (target := target) (pattern := .var v)
      (thenBranch := thenBranch) (elseBranch := elseBranch)
      (type_ := type_) (inputBindings := Bindings.empty)
      (matchBindings := merged) (merged := merged) (prev := [])
      hmatchHE hmergeHE hloopHE hmatchLea hmergeLea hloopLea hno hkeys hfresh
      (by simp [merged, Bindings.empty, Bindings.assign])

/-- Concrete non-empty seed used to expose the binding-order boundary between
HE raw `unify` results and LeaTTa's runtime merge list. -/
def seededUnifyOrderSeed : Bindings :=
  Bindings.empty.assign "y" (.symbol "b")

/-- Concrete singleton match binding for the non-empty seed order boundary. -/
def seededUnifyOrderMatch : Bindings :=
  Bindings.empty.assign "x" (.symbol "a")

/-- Exact HE raw merge result: primitive `unify` merges the incoming seed into
the singleton match binding, so the match binding stays at the front. -/
def seededUnifyOrderHEMerged : Bindings :=
  { assignments := [("x", .symbol "a"), ("y", .symbol "b")]
  , equalities := [] }

/-- Exact LeaTTa runtime merge result: LeaTTa folds the singleton match binding
into the translated seed, so the fresh match binding is prepended to the
seed's matcher-oriented bindings. -/
def seededUnifyOrderLeaMerged : Metta.Bindings :=
  [ Metta.BindingRel.val "x" (Metta.Atom.sym "a")
  , Metta.BindingRel.val "y" (Metta.Atom.sym "b") ]

theorem seededUnifyOrder_he_merge_mem :
    seededUnifyOrderHEMerged ∈
      mergeBindings seededUnifyOrderMatch seededUnifyOrderSeed 10 := by
  have hlookup : seededUnifyOrderMatch.lookup "y" = none := by
    simp [seededUnifyOrderMatch, Bindings.empty, Bindings.assign,
      Bindings.isBound, Bindings.lookup]
  rw [show (10 : Nat) = 8 + 2 by rfl]
  change seededUnifyOrderHEMerged ∈
    mergeBindings seededUnifyOrderMatch
      (Bindings.empty.assign "y" (.symbol "b")) (8 + 2)
  rw [mergeBindings_single_assign_fresh hlookup
    (by simp [seededUnifyOrderMatch, Bindings.empty, Bindings.assign]) 8]
  simp [seededUnifyOrderHEMerged, seededUnifyOrderMatch,
    Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup]

theorem seededUnifyOrder_unifySuccessResults_mem :
    (.symbol "a", seededUnifyOrderHEMerged) ∈
      unifySuccessResults (.symbol "a") (.var "x") (.var "x")
        seededUnifyOrderSeed 10 := by
  unfold unifySuccessResults
  refine List.mem_flatMap.mpr ?_
  refine ⟨seededUnifyOrderMatch, ?_, ?_⟩
  · rw [matchAtoms_ground_var_exact (.symbol "a") "x" 9 (GroundAtom.symbol "a")]
    simp [seededUnifyOrderMatch]
  · refine List.mem_filterMap.mpr ?_
    refine ⟨seededUnifyOrderHEMerged, seededUnifyOrder_he_merge_mem, ?_⟩
    have hloop : seededUnifyOrderHEMerged.hasLoop = false := by
      rfl
    have happly :
        seededUnifyOrderHEMerged.applyDefault (.var "x") = .symbol "a" := by
      rfl
    decide +kernel

theorem seededUnifyOrder_toLeaTTaMatchBindings_he_merged :
    toLeaTTaMatchBindings seededUnifyOrderHEMerged =
      [ Metta.BindingRel.val "y" (Metta.Atom.sym "b")
      , Metta.BindingRel.val "x" (Metta.Atom.sym "a") ] := by
  simp [seededUnifyOrderHEMerged, toLeaTTaMatchBindings,
    toLeaTTaMatchSubst, encodeModelAtom, Metta.Bindings.ofSubst]

theorem seededUnifyOrder_leatta_runtime_merge_eq :
    Metta.Bindings.merge (toLeaTTaMatchBindings seededUnifyOrderSeed)
        (toLeaTTaMatchBindings seededUnifyOrderMatch) =
      [seededUnifyOrderLeaMerged] := by
  simp [seededUnifyOrderSeed, seededUnifyOrderMatch,
    seededUnifyOrderLeaMerged, toLeaTTaMatchBindings, toLeaTTaMatchSubst,
    Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup,
    Metta.Bindings.ofSubst, Metta.Bindings.merge, Metta.Bindings.mergeOne,
    Metta.Bindings.addVarBinding,
    Metta.Bindings.addValRaw, Metta.Bindings.removeVal]
  rfl

/-- The current literal bridge cannot simply generalize from empty seeds to
non-empty seeds: HE's exact raw binding list and LeaTTa's exact runtime binding
list are lookup-equivalent here, but not literally the same list. -/
theorem seededUnifyOrder_literal_transport_fails :
    toLeaTTaMatchBindings seededUnifyOrderHEMerged ∉
      Metta.Bindings.merge (toLeaTTaMatchBindings seededUnifyOrderSeed)
        (toLeaTTaMatchBindings seededUnifyOrderMatch) := by
  rw [seededUnifyOrder_leatta_runtime_merge_eq,
    seededUnifyOrder_toLeaTTaMatchBindings_he_merged]
  simp [seededUnifyOrderLeaMerged]

/-- The same boundary is only about concrete list order, not binding meaning:
direct value lookup agrees between the HE raw result translation and the
LeaTTa runtime merge result. -/
theorem seededUnifyOrder_lookupVal_extensional_agreement (z : String) :
    Metta.Bindings.lookupVal (toLeaTTaMatchBindings seededUnifyOrderHEMerged) z =
      Metta.Bindings.lookupVal seededUnifyOrderLeaMerged z := by
  rw [seededUnifyOrder_toLeaTTaMatchBindings_he_merged]
  by_cases hx : z = "x"
  · subst z
    simp [seededUnifyOrderLeaMerged, Metta.Bindings.lookupVal]
  · by_cases hy : z = "y"
    · subst z
      simp [seededUnifyOrderLeaMerged, Metta.Bindings.lookupVal]
    · simp [seededUnifyOrderLeaMerged, Metta.Bindings.lookupVal, hx, hy]

/-- The two list orders also agree at the equality-class-aware observable used
by the v1.0.8 bridge. -/
theorem seededUnifyOrder_resolve_extensional_agreement (z : String) :
    (Metta.Bindings.resolve
        (toLeaTTaMatchBindings seededUnifyOrderHEMerged) z).getD (.var z) =
      (Metta.Bindings.resolve seededUnifyOrderLeaMerged z).getD (.var z) := by
  rw [seededUnifyOrder_toLeaTTaMatchBindings_he_merged]
  have hleft : ClosedValueBindings
      [ Metta.BindingRel.val "y" (Metta.Atom.sym "b")
      , Metta.BindingRel.val "x" (Metta.Atom.sym "a") ] := by
    exact .val (by simp [Metta.Atom.vars]) (.val (by simp [Metta.Atom.vars]) .nil)
  have hright : ClosedValueBindings seededUnifyOrderLeaMerged := by
    exact .val (by simp [Metta.Atom.vars]) (.val (by simp [Metta.Atom.vars]) .nil)
  rw [ClosedValueBindings.resolve_eq_lookupVal hleft z,
    ClosedValueBindings.resolve_eq_lookupVal hright z]
  congr 1
  simpa [seededUnifyOrder_toLeaTTaMatchBindings_he_merged] using
    seededUnifyOrder_lookupVal_extensional_agreement z

/-- The non-empty seed boundary is a positive executable/declarative success
once the executable binding observation is compared by full resolution rather
than concrete list order.  The HE result is still the exact raw
`unifySuccessResults` pair. -/
theorem seededUnifyOrder_leattaUnifyMettaCallStepExt_counter0 :
    LeaTTaUnifyMettaCallStepExt
      Space.empty GroundedDispatch.none 10
      (.expression [.symbol "unify", .symbol "a", .var "x",
        .var "x", .symbol "else"])
      Atom.undefinedType seededUnifyOrderSeed
      (.symbol "a", seededUnifyOrderHEMerged) := by
  have hmatchHE :
      seededUnifyOrderMatch ∈ matchAtoms (.symbol "a") (.var "x") 10 := by
    rw [matchAtoms_ground_var_exact (.symbol "a") "x" 9 (GroundAtom.symbol "a")]
    simp [seededUnifyOrderMatch]
  have hmergeHE :
      seededUnifyOrderHEMerged ∈
        mergeBindings seededUnifyOrderMatch seededUnifyOrderSeed 10 :=
    seededUnifyOrder_he_merge_mem
  have hloopHE : seededUnifyOrderHEMerged.hasLoop = false := by
    rfl
  have hmatchLea :
      toLeaTTaMatchBindings seededUnifyOrderMatch ∈
        Metta.matchAtoms (encodeModelAtom (.symbol "a")) (encodeModelAtom (.var "x")) := by
    rw [leattaMatchAtoms_ground_var_exact "x" (GroundAtom.symbol "a")]
    simp [seededUnifyOrderMatch, toLeaTTaMatchBindings, toLeaTTaMatchSubst,
      Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup,
      Metta.Bindings.ofSubst, encodeModelAtom]
  have hmergeLea :
      seededUnifyOrderLeaMerged ∈
        Metta.Bindings.merge (toLeaTTaMatchBindings seededUnifyOrderSeed)
          (toLeaTTaMatchBindings seededUnifyOrderMatch) := by
    rw [seededUnifyOrder_leatta_runtime_merge_eq]
    simp
  have hloopLea :
      Metta.Bindings.hasLoop seededUnifyOrderLeaMerged = false := by
    apply ClosedValueBindings.hasLoop_false
    exact .val (by simp [Metta.Atom.vars])
      (.val (by simp [Metta.Atom.vars]) .nil)
  have hbindingsEq :
      LeaBindingsLookupEq seededUnifyOrderLeaMerged
        (toLeaTTaMatchBindings seededUnifyOrderHEMerged) :=
    LeaBindingsLookupEq.symm
      (fun z => seededUnifyOrder_resolve_extensional_agreement z)
  have hno : NoVarAssignmentValues seededUnifyOrderHEMerged := by
    intro v x hlookup
    change List.lookup v [("x", Atom.symbol "a"), ("y", Atom.symbol "b")] =
      some (Atom.var x) at hlookup
    cases hxv : (v == "x") with
    | true =>
        rw [List.lookup_cons, hxv] at hlookup
        simp at hlookup
    | false =>
        cases hyv : (v == "y") with
        | true =>
            rw [List.lookup_cons, hxv, List.lookup_cons, hyv] at hlookup
            simp at hlookup
        | false =>
            rw [List.lookup_cons, hxv, List.lookup_cons, hyv, List.lookup_nil] at hlookup
            simp at hlookup
  have hkeys : AssignmentsNodup seededUnifyOrderHEMerged := by
    simp [AssignmentsNodup, seededUnifyOrderHEMerged]
  have hfresh :
      ValueKeysFreshForValues
        (toLeaTTaMatchBindings seededUnifyOrderHEMerged) := by
    rw [seededUnifyOrder_toLeaTTaMatchBindings_he_merged]
    exact ClosedValueBindings.valueKeysFreshForValues
      (ClosedValueBindings.val (by simp [Metta.Atom.vars])
        (ClosedValueBindings.val (by simp [Metta.Atom.vars])
          ClosedValueBindings.nil))
  have hstep :
      LeaTTaUnifyMettaCallStepExt
        Space.empty GroundedDispatch.none 10
        (.expression [.symbol "unify", .symbol "a", .var "x",
          .var "x", .symbol "else"])
        Atom.undefinedType seededUnifyOrderSeed
        (seededUnifyOrderHEMerged.applyDefault (.var "x"),
          seededUnifyOrderHEMerged) :=
    leattaUnifyMettaCallStepExt_success_of_transported_match_merge
      (space := Space.empty) (d := GroundedDispatch.none) (fuel := 10)
      (target := .symbol "a") (pattern := .var "x")
      (thenBranch := .var "x") (elseBranch := .symbol "else")
      (type_ := Atom.undefinedType) (inputBindings := seededUnifyOrderSeed)
      (matchBindings := seededUnifyOrderMatch)
      (merged := seededUnifyOrderHEMerged) (prev := [])
      (runtimeMatchBindings := toLeaTTaMatchBindings seededUnifyOrderMatch)
      (emittedMerged := seededUnifyOrderLeaMerged)
      hmatchHE hmergeHE hloopHE hmatchLea hmergeLea hloopLea hbindingsEq
      hno hkeys hfresh rfl
  have applied : seededUnifyOrderHEMerged.applyDefault (.var "x") = .symbol "a" := by
    decide +kernel
  simpa only [applied] using hstep

theorem leattaUnifyMettaCallStep_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src type_ : Atom} {inputBindings : Bindings} {result : ResultPair} :
    LeaTTaUnifyMettaCallStep space d fuel src type_ inputBindings result →
      MettaCall space d src type_ inputBindings result := by
  rintro ⟨target, pattern, thenBranch, elseBranch, _prev,
    h_shape, h_not_error, _hhit, h_reference⟩
  cases h_reference with
  | inl h_raw =>
      exact MettaCall.unify_success_raw
        src type_ inputBindings target pattern thenBranch elseBranch
        result fuel h_shape h_not_error h_raw
  | inr h_fallback =>
      rcases h_fallback with ⟨h_result, h_empty⟩
      rw [h_result]
      exact MettaCall.unify_no_match_raw
        src type_ inputBindings target pattern thenBranch elseBranch
        fuel h_shape h_not_error h_empty

theorem leattaUnifyMettaCallStepExt_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src type_ : Atom} {inputBindings : Bindings} {result : ResultPair} :
    LeaTTaUnifyMettaCallStepExt space d fuel src type_ inputBindings result →
      MettaCall space d src type_ inputBindings result := by
  rintro ⟨target, pattern, thenBranch, elseBranch, _prev,
    h_shape, h_not_error, _hhit, h_reference⟩
  cases h_reference with
  | inl h_raw =>
      exact MettaCall.unify_success_raw
        src type_ inputBindings target pattern thenBranch elseBranch
        result fuel h_shape h_not_error h_raw
  | inr h_fallback =>
      rcases h_fallback with ⟨h_result, h_empty⟩
      rw [h_result]
      exact MettaCall.unify_no_match_raw
        src type_ inputBindings target pattern thenBranch elseBranch
        fuel h_shape h_not_error h_empty

theorem emptySpace_unifySymbolMismatch_leattaUnifyMettaCallStep_counter0 :
    LeaTTaUnifyMettaCallStep
      Space.empty GroundedDispatch.none 10
      (.expression [.symbol "unify", .symbol "a", .symbol "b",
        .symbol "then", .symbol "else"])
      Atom.undefinedType Bindings.empty
      (.symbol "else", Bindings.empty) := by
  refine ⟨.symbol "a", .symbol "b", .symbol "then", .symbol "else", [],
    rfl, rfl, ?_, ?_⟩
  · exact leattaUnifyOpHit_fallback_of_matchAtoms_nil
      (.symbol "a") (.symbol "b") (.symbol "then") (.symbol "else")
      Bindings.empty [] rfl
  · exact Or.inr ⟨rfl, rfl⟩

/-- Concrete positive success witness for primitive `unify`: matching `a`
against `$x` instantiates the success branch `$x` to `a`, rather than taking
the else branch. -/
theorem emptySpace_unifyVarSymbol_leattaUnifyMettaCallStep_counter0 :
    LeaTTaUnifyMettaCallStep
      Space.empty GroundedDispatch.none 10
      (.expression [.symbol "unify", .symbol "a", .var "x",
        .var "x", .symbol "else"])
      Atom.undefinedType Bindings.empty
      (.symbol "a", Bindings.empty.assign "x" (.symbol "a")) := by
  simpa [Bindings.applyDefault, Bindings.resolutionFuel, Bindings.resolutionValueDepth,
    Bindings.atomScanFuel, Bindings.boundVars, Bindings.apply, Bindings.resolve,
    Bindings.resolveAtomAux, Bindings.hasAssignedVar, Bindings.hasAssignedVarAux,
    Bindings.empty, Bindings.assign, Bindings.isBound, Bindings.lookup] using
    leattaUnifyMettaCallStep_success_ground_var_empty_seed
      (space := Space.empty) (d := GroundedDispatch.none) (n := 9)
      (target := .symbol "a") (v := "x") (thenBranch := .var "x")
      (elseBranch := .symbol "else") (type_ := Atom.undefinedType)
      (GroundAtom.symbol "a")

/-- The currently proved call fragment: equation hits, no-match observations,
and primitive `unify` raw result/fallback observations. -/
def LeaTTaQueryUnifyMettaCallStep
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (src type_ : Atom) (inputBindings : Bindings) (result : ResultPair) :
    Prop :=
  LeaTTaEquationNoMatchMettaCallStep
    space d fuel src type_ inputBindings result ∨
  LeaTTaUnifyMettaCallStep space d fuel src type_ inputBindings result

/-- Lookup-extensional primitive-`unify` variant of the query/unify fragment.
The query lanes are unchanged; only the executable binding comparison for
primitive `unify` is widened from list equality to direct-lookup equality. -/
def LeaTTaQueryUnifyMettaCallStepExt
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (src type_ : Atom) (inputBindings : Bindings) (result : ResultPair) :
    Prop :=
  LeaTTaEquationNoMatchMettaCallStep
    space d fuel src type_ inputBindings result ∨
  LeaTTaUnifyMettaCallStepExt space d fuel src type_ inputBindings result

theorem leattaQueryUnifyMettaCallStep_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src type_ : Atom} {inputBindings : Bindings} {result : ResultPair} :
    LeaTTaQueryUnifyMettaCallStep
      space d fuel src type_ inputBindings result →
      MettaCall space d src type_ inputBindings result := by
  intro hstep
  cases hstep with
  | inl hquery =>
      exact leattaEquationNoMatchMettaCallStep_sound hquery
  | inr hunify =>
      exact leattaUnifyMettaCallStep_sound hunify

theorem leattaQueryUnifyMettaCallStepExt_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src type_ : Atom} {inputBindings : Bindings} {result : ResultPair} :
    LeaTTaQueryUnifyMettaCallStepExt
      space d fuel src type_ inputBindings result →
      MettaCall space d src type_ inputBindings result := by
  intro hstep
  cases hstep with
  | inl hquery =>
      exact leattaEquationNoMatchMettaCallStep_sound hquery
  | inr hunify =>
      exact leattaUnifyMettaCallStepExt_sound hunify

theorem emptySpace_unifySymbolMismatch_queryUnifyMettaCallStep_counter0 :
    LeaTTaQueryUnifyMettaCallStep
      Space.empty GroundedDispatch.none 10
      (.expression [.symbol "unify", .symbol "a", .symbol "b",
        .symbol "then", .symbol "else"])
      Atom.undefinedType Bindings.empty
      (.symbol "else", Bindings.empty) :=
  Or.inr emptySpace_unifySymbolMismatch_leattaUnifyMettaCallStep_counter0

theorem emptySpace_unifyVarSymbol_queryUnifyMettaCallStep_counter0 :
    LeaTTaQueryUnifyMettaCallStep
      Space.empty GroundedDispatch.none 10
      (.expression [.symbol "unify", .symbol "a", .var "x",
        .var "x", .symbol "else"])
      Atom.undefinedType Bindings.empty
      (.symbol "a", Bindings.empty.assign "x" (.symbol "a")) :=
  Or.inr emptySpace_unifyVarSymbol_leattaUnifyMettaCallStep_counter0

theorem seededUnifyOrder_queryUnifyMettaCallStepExt_counter0 :
    LeaTTaQueryUnifyMettaCallStepExt
      Space.empty GroundedDispatch.none 10
      (.expression [.symbol "unify", .symbol "a", .var "x",
        .var "x", .symbol "else"])
      Atom.undefinedType seededUnifyOrderSeed
      (.symbol "a", seededUnifyOrderHEMerged) :=
  Or.inr seededUnifyOrder_leattaUnifyMettaCallStepExt_counter0

/-- Empty-input bridge from a visible LeaTTa observation to an independently
computed HE equation result. The observed runtime atom may be an equality-class
representative while recursive HE evaluation returns the class value. -/
theorem leattaEquationMettaCallStep_of_visible_observation_empty_input_result
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src visibleDst type_ rhs : Atom} {qb : Bindings} {result : ResultPair}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat}
    (hobs :
      LeaTTaVisibleEquationStepObservation space d fuel src visibleDst gt prev counter)
    (h_not_error : isErrorAtom src = false)
    (h_not_grounded : HeadNotExecutable d src)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] src type_ Bindings.empty)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space src fuel)
    (h_no_loop : qb.hasLoop = false)
    (h_recurse : OrdinaryCallReturnRel space d src (qb.applyFull rhs fuel) type_ qb result) :
    LeaTTaEquationMettaCallStep
      space d fuel src type_ Bindings.empty result := by
  cases fuel with
  | zero =>
      simp [queryEquationsAvoiding] at h_query_public
  | succ n =>
      have h_merge : qb ∈ mergeBindings qb Bindings.empty (n + 1) := by
        rw [mergeBindings_empty_right qb n]
        simp
      exact
        ⟨rhs, qb, qb, visibleDst, gt, prev, counter, hobs, h_not_error,
          h_not_grounded, ⟨avoid, h_cover, h_query_public⟩, h_merge, h_no_loop, h_recurse⟩

/-- Step-shaped bridge from an already equality-aware visible LeaTTa
observation to the engine-call fragment. This is the non-shortcut constructor:
it consumes the repaired visible observation directly, and keeps the official
HE `queryEquations` witness and `OrdinaryCallReturnRel` premise explicit. -/
theorem leattaEquationMettaCallStep_of_visible_observation_empty_input
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src dst type_ rhs : Atom} {qb outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat}
    (hobs : LeaTTaVisibleEquationStepObservation space d fuel src dst gt prev counter)
    (h_not_error : isErrorAtom src = false)
    (h_not_grounded : HeadNotExecutable d src)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] src type_ Bindings.empty)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space src fuel)
    (h_no_loop : qb.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d src (qb.applyFull rhs fuel) type_ qb (dst, outputBindings)) :
    LeaTTaEquationMettaCallStep
      space d fuel src type_ Bindings.empty (dst, outputBindings) := by
  exact
    leattaEquationMettaCallStep_of_visible_observation_empty_input_result
      hobs h_not_error h_not_grounded h_cover h_query_public h_no_loop h_recurse

/-- Merge-parametric bridge from an equality-aware visible LeaTTa observation to
the engine-call fragment. This is the binding-threaded version of
`leattaEquationMettaCallStep_of_visible_observation_empty_input`: the caller
provides the official HE merge result and ordinary-call return premise rather
than assuming the input bindings are empty. -/
theorem leattaEquationMettaCallStep_of_visible_observation_with_merge
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src dst type_ rhs : Atom}
    {queryBindings inputBindings merged outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat}
    (hobs : LeaTTaVisibleEquationStepObservation space d fuel src dst gt prev counter)
    (h_not_error : isErrorAtom src = false)
    (h_not_grounded : HeadNotExecutable d src)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] src type_ inputBindings)
    (h_query_public : (rhs, queryBindings) ∈
      queryEquationsAvoiding avoid space src fuel)
    (h_merge : merged ∈ mergeBindings queryBindings inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d src (merged.applyFull rhs fuel) type_ merged
        (dst, outputBindings)) :
    LeaTTaEquationMettaCallStep
      space d fuel src type_ inputBindings (dst, outputBindings) := by
  exact
    ⟨rhs, queryBindings, merged, dst, gt, prev, counter,
      hobs, h_not_error, h_not_grounded, ⟨avoid, h_cover, h_query_public⟩, h_merge,
      h_no_loop, h_recurse⟩

/-- Parametric equality-aware equation-call bridge for the repaired visible
query interface. Unlike the instantiated-RHS shortcut below, this theorem consumes
the avoid-aware transport witness directly, so equality-bearing HE matches can
enter the step-shaped LeaTTa call fragment without dropping their equality
constraints. -/
theorem leattaEquationMettaCallStep_of_transport_againstVisible_empty_input
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom} {qb outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey (encodeModelAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ Bindings.empty)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (htransport : EquationMatchVisibleItemTransportAgainst
      space (.expression es) rhs qb fuel gt prev counter)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (qb.applyFull rhs fuel) type_ qb
        (qb.applyFull rhs fuel, outputBindings)) :
    LeaTTaEquationMettaCallStep
      space d fuel (.expression es) type_ Bindings.empty
      (qb.applyFull rhs fuel, outputBindings) := by
  have hobs :
      LeaTTaVisibleEquationStepObservation
        space d fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter :=
    equation_match_againstVisible_observation_of_transport
      (space := space) (d := d) (fuel := fuel) (es := es)
      (rhs := rhs) (qb := qb) (gt := gt) (k := k)
      (prev := prev) (counter := counter)
      h_not_special h_not_grounded hk h_query_visible htransport
  exact
    leattaEquationMettaCallStep_of_visible_observation_empty_input
      (space := space)
      (d := d)
      (fuel := fuel)
      (src := .expression es)
      (dst := qb.applyFull rhs fuel)
      (type_ := type_)
      (rhs := rhs)
      (qb := qb)
      (outputBindings := outputBindings)
      (gt := gt)
      (prev := prev)
      (counter := counter)
      hobs h_not_error h_not_grounded h_cover h_query_public
      (queryEquationsAvoiding_hasLoop_false h_query_public)
      h_recurse

/-- Binding-threaded equality-aware equation-call bridge for the repaired
visible query interface, specialized to ordinary returns whose final atom is
the visible HE equation successor. -/
theorem leattaEquationMettaCallStep_of_transport_againstVisible_with_merge
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey (encodeModelAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ inputBindings)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (htransport : EquationMatchVisibleItemTransportAgainst
      space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (merged.applyFull rhs fuel) type_ merged
        (qb.applyFull rhs fuel, outputBindings)) :
    LeaTTaEquationMettaCallStep
      space d fuel (.expression es) type_ inputBindings
      (qb.applyFull rhs fuel, outputBindings) := by
  have hobs :
      LeaTTaVisibleEquationStepObservation
        space d fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter :=
    equation_match_againstVisible_observation_of_transport
      (space := space) (d := d) (fuel := fuel) (es := es)
      (rhs := rhs) (qb := qb) (gt := gt) (k := k)
      (prev := prev) (counter := counter)
      h_not_special h_not_grounded hk h_query_visible htransport
  exact
    leattaEquationMettaCallStep_of_visible_observation_with_merge
      (space := space)
      (d := d)
      (fuel := fuel)
      (src := .expression es)
      (dst := qb.applyFull rhs fuel)
      (type_ := type_)
      (rhs := rhs)
      (queryBindings := qb)
      (inputBindings := inputBindings)
      (merged := merged)
      (outputBindings := outputBindings)
      (gt := gt)
      (prev := prev)
      (counter := counter)
      hobs h_not_error h_not_grounded h_cover h_query_public h_merge h_no_loop
      h_recurse

/-- Continuation-aware bridge from an equality-aware visible LeaTTa observation
to the engine-call fragment. The executable observation records the immediate
equation successor `visibleDst`, while the official HE `OrdinaryCallReturnRel`
premise may produce any final result pair. -/
theorem leattaEquationMettaCallStep_of_visible_observation_with_merge_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src visibleDst type_ rhs : Atom}
    {queryBindings inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {finalResult : ResultPair}
    (hobs :
      LeaTTaVisibleEquationStepObservation
        space d fuel src visibleDst gt prev counter)
    (h_not_error : isErrorAtom src = false)
    (h_not_grounded : HeadNotExecutable d src)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] src type_ inputBindings)
    (h_query_public :
      (rhs, queryBindings) ∈ queryEquationsAvoiding avoid space src fuel)
    (h_merge : merged ∈ mergeBindings queryBindings inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d src (merged.applyFull rhs fuel) type_ merged finalResult) :
    LeaTTaEquationMettaCallStep
      space d fuel src type_ inputBindings finalResult := by
  exact
    ⟨rhs, queryBindings, merged, visibleDst, gt, prev, counter,
      hobs, h_not_error, h_not_grounded, ⟨avoid, h_cover, h_query_public⟩, h_merge,
      h_no_loop, h_recurse⟩

/-- Continuation-aware equality bridge for the repaired visible query interface.
The LeaTTa `queryOp` observation witnesses the immediate visible equation
successor `qb.applyFull rhs fuel`; the final `MettaCall` result is supplied by the
ordinary HE call-return premise. -/
theorem leattaEquationMettaCallStep_of_transport_againstVisible_with_merge_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey (encodeModelAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ inputBindings)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (htransport : EquationMatchVisibleItemTransportAgainst
      space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (merged.applyFull rhs fuel) type_ merged finalResult) :
    LeaTTaEquationMettaCallStep
      space d fuel (.expression es) type_ inputBindings finalResult := by
  have hobs :
      LeaTTaVisibleEquationStepObservation
        space d fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter :=
    equation_match_againstVisible_observation_of_transport
      (space := space) (d := d) (fuel := fuel) (es := es)
      (rhs := rhs) (qb := qb) (gt := gt) (k := k)
      (prev := prev) (counter := counter)
      h_not_special h_not_grounded hk h_query_visible htransport
  exact
    leattaEquationMettaCallStep_of_visible_observation_with_merge_final
      (space := space)
      (d := d)
      (fuel := fuel)
      (src := .expression es)
      (visibleDst := qb.applyFull rhs fuel)
      (type_ := type_)
      (rhs := rhs)
      (queryBindings := qb)
      (inputBindings := inputBindings)
      (merged := merged)
      (gt := gt)
      (prev := prev)
      (counter := counter)
      (finalResult := finalResult)
      hobs h_not_error h_not_grounded h_cover h_query_public h_merge h_no_loop
      h_recurse

/-- Continuation-aware bridge from a concrete LeaTTa `queryOp` hit on the
repaired visible query interface. This is the executable-trace boundary: the
caller supplies the actual emitted item up to alpha-equivalence, while the HE
premises supply query, merge, loop, and ordinary-call return evidence. -/
theorem leattaEquationMettaCallStep_of_queryOp_hit_againstVisible_with_merge_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ inputBindings)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (hhit :
      LeaTTaEquationQueryOpHit
        space fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (merged.applyFull rhs fuel) type_ merged finalResult) :
    LeaTTaEquationMettaCallStep
      space d fuel (.expression es) type_ inputBindings finalResult := by
  have hobs :
      LeaTTaVisibleEquationStepObservation
        space d fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter :=
    equation_match_againstVisible_observation_of_queryOp_hit
      (space := space) (d := d) (fuel := fuel) (es := es)
      (rhs := rhs) (qb := qb) (gt := gt) (prev := prev)
      (counter := counter)
      h_not_special h_not_grounded h_query_visible hhit
  exact
    leattaEquationMettaCallStep_of_visible_observation_with_merge_final
      (space := space)
      (d := d)
      (fuel := fuel)
      (src := .expression es)
      (visibleDst := qb.applyFull rhs fuel)
      (type_ := type_)
      (rhs := rhs)
      (queryBindings := qb)
      (inputBindings := inputBindings)
      (merged := merged)
      (gt := gt)
      (prev := prev)
      (counter := counter)
      (finalResult := finalResult)
      hobs h_not_error h_not_grounded h_cover h_query_public h_merge h_no_loop
      h_recurse

/-- Continuation-aware bridge from the local freshened-item transport obligation
on the repaired visible query interface. -/
theorem leattaEquationMettaCallStep_of_freshened_item_transport_againstVisible_with_merge_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey (encodeModelAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ inputBindings)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (hitemTransport : FreshenedQueryOpItemTransportAgainstVisible
      space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (merged.applyFull rhs fuel) type_ merged finalResult) :
    LeaTTaEquationMettaCallStep
      space d fuel (.expression es) type_ inputBindings finalResult := by
  exact
    leattaEquationMettaCallStep_of_queryOp_hit_againstVisible_with_merge_final
      (space := space)
      (d := d)
      (fuel := fuel)
      (es := es)
      (rhs := rhs)
      (type_ := type_)
      (qb := qb)
      (inputBindings := inputBindings)
      (merged := merged)
      (gt := gt)
      (prev := prev)
      (counter := counter)
      (finalResult := finalResult)
      h_not_special h_not_error h_not_grounded h_query_visible
      h_cover h_query_public
      (leattaEquationQueryOpHit_of_freshened_item_transport_againstVisible
        (space := space) (src := .expression es) (rhs := rhs)
        (qb := qb) (fuel := fuel) (gt := gt) (prev := prev)
        (counter := counter) (k := k)
        hk h_query_visible hitemTransport)
      h_merge h_no_loop h_recurse

/-- Continuation-aware bridge for the variable-successor specialization of the
local freshened-item transport obligation. -/
theorem leattaEquationMettaCallStep_of_freshened_variable_item_transport_againstVisible_with_merge_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey (encodeModelAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ inputBindings)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (hvarTransport : FreshenedVariableQueryOpItemTransportAgainstVisible
      space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (merged.applyFull rhs fuel) type_ merged finalResult) :
    LeaTTaEquationMettaCallStep
      space d fuel (.expression es) type_ inputBindings finalResult := by
  exact
    leattaEquationMettaCallStep_of_queryOp_hit_againstVisible_with_merge_final
      (space := space)
      (d := d)
      (fuel := fuel)
      (es := es)
      (rhs := rhs)
      (type_ := type_)
      (qb := qb)
      (inputBindings := inputBindings)
      (merged := merged)
      (gt := gt)
      (prev := prev)
      (counter := counter)
      (finalResult := finalResult)
      h_not_special h_not_error h_not_grounded h_query_visible
      h_cover h_query_public
      (leattaEquationQueryOpHit_of_freshened_variable_item_transport_againstVisible
        (space := space) (src := .expression es) (rhs := rhs)
        (qb := qb) (fuel := fuel) (gt := gt) (prev := prev)
        (counter := counter) (k := k)
        hk h_query_visible hvarTransport)
      h_merge h_no_loop h_recurse

/-- Step-shaped counterpart of
`observedMettaCall_of_instantiated_item_againstVisible_empty_input`: for the
non-ground instantiated-RHS fragment, a visible LeaTTa `queryOp` item plus the
HE query premises gives an engine-style `mettaCallStep` witness. -/
theorem leattaEquationMettaCallStep_of_instantiated_item_againstVisible_empty_input
    {space : Space} {d : GroundedDispatch} {n : Nat}
    {es : List Atom} {rhs type_ : Atom} {qb outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) (n + 1))
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ Bindings.empty)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) (n + 1))
    (heq : qb.equalities = [])
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings qb))
    (hdepth : atomDepth rhs + 2 ≤ n + 1)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb) (encodeModelAtom rhs))
          (toLeaTTaMatchBindings qb) ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (encodeModelAtom (.expression es)) Metta.Bindings.empty).1)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (qb.applyFull rhs (n + 1)) type_ qb
        (qb.applyFull rhs (n + 1), outputBindings)) :
    LeaTTaEquationMettaCallStep
      space d (n + 1) (.expression es) type_ Bindings.empty
      (qb.applyFull rhs (n + 1), outputBindings) := by
  have hobs :
      LeaTTaVisibleEquationStepObservation
        space d (n + 1) (.expression es) (qb.applyFull rhs (n + 1))
        gt prev counter :=
    equation_match_againstVisible_observation_of_instantiated_item
      (space := space) (d := d) (fuel := n + 1) (es := es)
      (rhs := rhs) (qb := qb) (gt := gt)
      (prev := prev) (counter := counter)
      h_not_special h_not_grounded h_query_visible heq
      hfresh hdepth hitem
  have h_merge : qb ∈ mergeBindings qb Bindings.empty (n + 1) := by
    rw [mergeBindings_empty_right qb n]
    simp
  exact
    ⟨rhs, qb, qb, qb.applyFull rhs (n + 1), gt, prev, counter, hobs, h_not_error, h_not_grounded,
      ⟨avoid, h_cover, h_query_public⟩, h_merge,
      queryEquationsAgainstVisible_hasLoop_false h_query_visible,
      h_recurse⟩

/-- Empty-input observed-call wrapper for the repaired visible-avoid equation
interface.  The visible query premise builds the LeaTTa executable observation;
the public query premise is kept separate because the official HE `MettaCall`
constructor consumes `queryEquations`.  This is the reusable bridge shape for
non-ground matches whose RHS instantiation agrees with HE substitution. -/
theorem observedMettaCall_of_instantiated_item_againstVisible_empty_input
    {space : Space} {d : GroundedDispatch} {n : Nat}
    {es : List Atom} {rhs type_ : Atom} {qb outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) (n + 1))
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ Bindings.empty)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) (n + 1))
    (heq : qb.equalities = [])
    (hfresh : ValueKeysFreshForValues (toLeaTTaMatchBindings qb))
    (hdepth : atomDepth rhs + 2 ≤ n + 1)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (toLeaTTaMatchBindings qb) (encodeModelAtom rhs))
          (toLeaTTaMatchBindings qb) ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (encodeModelAtom (.expression es)) Metta.Bindings.empty).1)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (qb.applyFull rhs (n + 1)) type_ qb
        (qb.applyFull rhs (n + 1), outputBindings)) :
    LeaTTaObservedMettaCall
      space d (n + 1) (.expression es) (qb.applyFull rhs (n + 1))
      type_ Bindings.empty outputBindings gt prev counter := by
  have hobs :
      LeaTTaVisibleEquationStepObservation
        space d (n + 1) (.expression es) (qb.applyFull rhs (n + 1))
        gt prev counter :=
    equation_match_againstVisible_observation_of_instantiated_item
      (space := space) (d := d) (fuel := n + 1) (es := es)
      (rhs := rhs) (qb := qb) (gt := gt)
      (prev := prev) (counter := counter)
      h_not_special h_not_grounded h_query_visible heq
      hfresh hdepth hitem
  have h_merge : qb ∈ mergeBindings qb Bindings.empty (n + 1) := by
    rw [mergeBindings_empty_right qb n]
    simp
  exact
    observedMettaCall_of_equation_match
      (space := space) (d := d) (fuel := n + 1)
      (src := .expression es)
      (dst := qb.applyFull rhs (n + 1))
      (type_ := type_)
      (rhs := rhs)
      (queryBindings := qb)
      (inputBindings := Bindings.empty)
      (merged := qb)
      (outputBindings := outputBindings)
      (gt := gt) (prev := prev) (counter := counter)
      hobs h_not_error h_not_grounded h_cover h_query_public h_merge
      (queryEquationsAgainstVisible_hasLoop_false h_query_visible)
      h_recurse

/-- Declarative HE call for the fresh-RHS boundary used by the repaired
visible-avoid LeaTTa observation theorem. -/
theorem freshRhsBoundary_mettaCall_fresh_rhs :
    MettaCall freshRhsBoundarySpace GroundedDispatch.none
      (.expression [.symbol "q"]) Atom.undefinedType Bindings.empty
      (.var "z#0", Bindings.empty) := by
  apply MettaCall.equation_match (fuel := 10)
    (rhs := .var "z#0")
    (queryBindings := Bindings.empty)
    (merged := Bindings.empty)
    (avoid := [])
  case h_not_error => rfl
  case h_not_grounded =>
    simp [GroundedDispatch.none]
  case h_cover =>
    intro name h
    simp [equationScope, Atom.undefinedType, atomVariables, atomListVariables, Bindings.names, Bindings.empty] at h
  case h_query =>
    decide
  case h_merge =>
    decide
  case h_no_loop =>
    rfl
  case h_recurse =>
    apply OrdinaryCallReturnRel.of_eval (by decide +kernel)
    change EvalAtom _ _ (.var "z#0") _ _ _
    exact EvalAtom.type_pass (.var "z#0") Atom.undefinedType Bindings.empty
      rfl (Or.inr (Or.inr rfl))

/-- Fresh-RHS boundary package: the repaired LeaTTa `queryOp` observation and
the declarative HE `MettaCall` result agree on the same visible successor. -/
theorem freshRhsBoundary_observed_mettaCall_counter5
    (gt : Metta.GroundingTable) :
    LeaTTaObservedMettaCall
      freshRhsBoundarySpace GroundedDispatch.none 10
      (.expression [.symbol "q"]) (.var "z#0") Atom.undefinedType
      Bindings.empty Bindings.empty gt [] 5 := by
  exact
    observedMettaCall_of_equation_match
      (space := freshRhsBoundarySpace)
      (d := GroundedDispatch.none)
      (fuel := 10)
      (src := .expression [.symbol "q"])
      (dst := .var "z#0")
      (type_ := Atom.undefinedType)
      (rhs := .var "z#0")
      (queryBindings := Bindings.empty)
      (inputBindings := Bindings.empty)
      (merged := Bindings.empty)
      (outputBindings := Bindings.empty)
      (gt := gt)
      (prev := [])
      (counter := 5)
      (freshRhsBoundary_againstVisible_observation_counter5 gt)
      rfl
      (by simp [HeadNotExecutable, GroundedDispatch.none])
      freshRhsBoundary_cover (by simp [queryEquationsAvoiding_freshRhsBoundary])
      (by decide)
      rfl
      (by
        apply OrdinaryCallReturnRel.of_eval (by decide +kernel)
        change EvalAtom _ _ (.var "z#0") _ _ _
        exact EvalAtom.type_pass (.var "z#0") Atom.undefinedType Bindings.empty
          rfl (Or.inr (Or.inr rfl)))

/-- Engine-step-shaped fresh-RHS boundary package through the repaired
freshened-item transport path. -/
theorem freshRhsBoundary_leattaEquationMettaCallStep_counter5
    (gt : Metta.GroundingTable) :
    LeaTTaEquationMettaCallStep
      freshRhsBoundarySpace GroundedDispatch.none 10
      (.expression [.symbol "q"]) Atom.undefinedType Bindings.empty
      (.var "z#0", Bindings.empty) := by
  exact
    leattaEquationMettaCallStep_of_freshened_item_transport_againstVisible_with_merge_final
      (space := freshRhsBoundarySpace)
      (d := GroundedDispatch.none)
      (fuel := 10)
      (es := [.symbol "q"])
      (rhs := .var "z#0")
      (type_ := Atom.undefinedType)
      (qb := Bindings.empty)
      (inputBindings := Bindings.empty)
      (merged := Bindings.empty)
      (gt := gt)
      (prev := [])
      (counter := 5)
      (k := "q")
      (finalResult := (.var "z#0", Bindings.empty))
      (by simp [SpecialFormHead])
      rfl
      (by simp [HeadNotExecutable, GroundedDispatch.none])
      (by simp [encodeModelAtom, Metta.Minimal.headKey])
      (by simp [queryEquationsAgainstVisible_freshRhsBoundary])
      freshRhsBoundary_cover (by simp [queryEquationsAvoiding_freshRhsBoundary])
      (freshRhsBoundary_FreshenedQueryOpItemTransportAgainstVisible_counter5 gt)
      (by decide)
      rfl
      (by
        apply OrdinaryCallReturnRel.of_eval (by decide +kernel)
        change EvalAtom _ _ (.var "z#0") _ _ _
        exact EvalAtom.type_pass (.var "z#0") Atom.undefinedType Bindings.empty
          rfl (Or.inr (Or.inr rfl)))

private def groundObservedCallSpace : Space :=
  Space.ofList
    [.expression
      [.symbol "=", .expression [.symbol "foo"], .symbol "bar"]]

private theorem groundObservedCall_lhs_ground :
    GroundAtom (.expression [.symbol "foo"]) := by
  refine GroundAtom.expression ?_
  intro e he
  simp at he
  subst he
  exact GroundAtom.symbol "foo"

private theorem queryEquationsAgainstVisible_groundObservedCall :
    queryEquationsAgainstVisible groundObservedCallSpace
        (.expression [.symbol "foo"]) 10 =
      [(.symbol "bar", Bindings.empty)] := by
  rfl

private theorem queryEquations_groundObservedCall :
    queryEquations groundObservedCallSpace
        (.expression [.symbol "foo"]) 10 =
      [(.symbol "bar", Bindings.empty)] := by
  rfl

private theorem groundObservedCall_queryOp_visible_successor_counter5
    (gt : Metta.GroundingTable) :
    LeaTTaVisibleEquationStepObservation
      groundObservedCallSpace GroundedDispatch.none 10
      (.expression [.symbol "foo"]) (.symbol "bar") gt [] 5 := by
  have hNotSpecial : ¬ SpecialFormHead (.expression [.symbol "foo"]) := by
    simp [SpecialFormHead]
  have hNotGrounded :
      HeadNotExecutable GroundedDispatch.none (.expression [.symbol "foo"]) := by
    simp [HeadNotExecutable, GroundedDispatch.none]
  have hquery : (.symbol "bar", Bindings.empty) ∈
      queryEquationsAgainstVisible groundObservedCallSpace
        (.expression [.symbol "foo"]) 10 := by
    simp [queryEquationsAgainstVisible_groundObservedCall]
  refine ⟨?_, ?_⟩
  · exact HEEquationStepAgainstVisible.equation_match
      hNotSpecial hNotGrounded hquery
      (queryEquationsAgainstVisible_hasLoop_false hquery)
  · refine ⟨encodeModelAtom (.symbol "bar"), ?_⟩
    refine ⟨Metta.Bindings.empty, ?_, ?_⟩
    · exact
        queryOp_contains_ground_rule_result
          (space := groundObservedCallSpace)
          (src := .expression [.symbol "foo"])
          (lhs := .expression [.symbol "foo"])
          (rawRhs := .symbol "bar")
          (qb := Bindings.empty)
          (fuel := 10)
          (idx := 0)
          (gt := gt)
          (k := "foo")
          []
          5
          (by
            simp [encodeModelAtom, Metta.Minimal.headKey])
          (by
            simp [groundObservedCallSpace, Space.ofList])
          groundObservedCall_lhs_ground
          (GroundAtom.symbol "bar")
          (by rfl)
    · unfold Metta.AlphaEq Metta.canonicalizeVars encodeModelAtom
      simp [Metta.Atom.vars, Metta.distinctVarsAux, Metta.renameVars]

/-- Closed ground-rule package: the repaired LeaTTa executable observation and
the declarative HE `MettaCall` result agree for a singleton ground equation. -/
theorem groundObservedCall_observed_mettaCall_counter5
    (gt : Metta.GroundingTable) :
    LeaTTaObservedMettaCall
      groundObservedCallSpace GroundedDispatch.none 10
      (.expression [.symbol "foo"]) (.symbol "bar") Atom.undefinedType
      Bindings.empty Bindings.empty gt [] 5 := by
  exact
    observedMettaCall_of_equation_match
      (space := groundObservedCallSpace)
      (d := GroundedDispatch.none)
      (fuel := 10)
      (src := .expression [.symbol "foo"])
      (dst := .symbol "bar")
      (type_ := Atom.undefinedType)
      (rhs := .symbol "bar")
      (queryBindings := Bindings.empty)
      (inputBindings := Bindings.empty)
      (merged := Bindings.empty)
      (outputBindings := Bindings.empty)
      (gt := gt)
      (prev := [])
      (counter := 5)
      (avoid := [])
      (groundObservedCall_queryOp_visible_successor_counter5 gt)
      rfl
      (by simp [HeadNotExecutable, GroundedDispatch.none])
      (by
        intro name h
        simp [equationScope, Atom.undefinedType, atomVariables, atomListVariables, Bindings.names, Bindings.empty] at h)
      (by decide)
      (by decide)
      rfl
      (by
        apply OrdinaryCallReturnRel.of_eval (by decide +kernel)
        change EvalAtom _ _ (.symbol "bar") _ _ _
        apply EvalAtom.type_cast (fuel := 10)
        · rfl
        · decide
        · left
          rfl
        · decide)

/-- The counter-0 fresh name used by the singleton unary-identity equation
fragment. This is public because several conformance-facing theorem statements
name the resulting HE binding explicitly. -/
def unaryIdentityFresh0 (v : String) : String :=
  v ++ "#" ++ toString 0

/-- Singleton HE equation space for the unary-identity fragment:
`(= (<head> $var) $var)`. -/
def unaryIdentitySpace (head var : String) : Space :=
  Space.ofList
    [.expression
      [.symbol "=", .expression [.symbol head, .var var], .var var]]

/-- Faithful HE binding result for querying `unaryIdentitySpace head var` with
`(<head> value)` at counter 0. -/
def unaryIdentityBindings (var value : String) : Bindings :=
  Bindings.empty.assign (unaryIdentityFresh0 var) (.symbol value)

private def unaryIdentityQueryAtom (head value : String) : Metta.Atom :=
  encodeModelAtom (.expression [.symbol head, .symbol value])

private def unaryIdentityQueryRule (head var : String) : Metta.Atom × Metta.Atom :=
  (encodeModelAtom (.expression [.symbol head, .var var]),
    encodeModelAtom (.var var))

private def unaryIdentityLeaBindings (var value : String) : Metta.Bindings :=
  [Metta.BindingRel.val (unaryIdentityFresh0 var) (Metta.Atom.sym value)]

@[simp] private theorem toString_string_self (s : String) :
    toString s = s := rfl

/-- Parametric LeaTTa item calculation for the singleton unary-identity rule at
runtime counter `0`.  This is the executable side of the assignment fragment:
freshening, matching, merging, and instantiating the RHS produce exactly the
symbol carried by the query. -/
theorem queryOpItemsOfRule_unaryIdentity_counter0
    (head var value : String) :
    queryOpItemsOfRule [] (unaryIdentityQueryAtom head value)
      Metta.Bindings.empty 0 (unaryIdentityQueryRule head var) =
        [Metta.Minimal.evalResult []
          (Metta.Atom.sym value) (unaryIdentityLeaBindings var value)] := by
  have hfresh :
      Metta.Minimal.freshenRule 0
          (unaryIdentityQueryRule head var).1
          (unaryIdentityQueryRule head var).2 =
        ( Metta.Atom.expr
            [Metta.Atom.sym head, Metta.Atom.var (unaryIdentityFresh0 var)]
        , Metta.Atom.var (unaryIdentityFresh0 var)) := by
    simp [unaryIdentityQueryRule, unaryIdentityFresh0, encodeModelAtom,
      Metta.Minimal.freshenRule, Metta.Atom.vars, Metta.Subst.apply,
      Metta.Subst.lookup]
  have hmatchLoop :
      Metta.Bindings.hasLoop
          [Metta.BindingRel.val (unaryIdentityFresh0 var) (Metta.Atom.sym value)] =
        false := by
    exact hasLoop_singleton_val_closed_false _ _ (by simp [Metta.Atom.vars])
  have hmatchLoop' : Metta.Bindings.hasLoop
      [Metta.BindingRel.val (var ++ "#" ++ Nat.repr 0) (Metta.Atom.sym value)] =
        false := by
    simpa [unaryIdentityFresh0] using hmatchLoop
  have hmatch :
      Metta.matchAtoms
          (Metta.Atom.expr
            [Metta.Atom.sym head, Metta.Atom.var (unaryIdentityFresh0 var)])
          (unaryIdentityQueryAtom head value) =
        [[Metta.BindingRel.val (unaryIdentityFresh0 var) (Metta.Atom.sym value)]] := by
    simp [unaryIdentityQueryAtom, unaryIdentityFresh0, encodeModelAtom,
      Metta.matchAtoms, Metta.matchAtomsWith, Metta.matchAll,
      Metta.Bindings.merge, Metta.Bindings.mergeOne,
      Metta.Bindings.addVarBinding,
      Metta.Bindings.addValRaw, Metta.Bindings.removeVal, hmatchLoop']
  have hmerge :
      Metta.Bindings.merge Metta.Bindings.empty
          [Metta.BindingRel.val (unaryIdentityFresh0 var) (Metta.Atom.sym value)] =
        [[Metta.BindingRel.val (unaryIdentityFresh0 var) (Metta.Atom.sym value)]] := by
    exact singleton_val_merge_empty_eq _ _ (by intro w; simp)
  have hloop :
      Metta.Bindings.hasLoop
          [Metta.BindingRel.val (unaryIdentityFresh0 var) (Metta.Atom.sym value)] =
        false := by
    exact hmatchLoop
  have hinst :
      Metta.instantiate
          [Metta.BindingRel.val (unaryIdentityFresh0 var) (Metta.Atom.sym value)]
          (Metta.Atom.var (unaryIdentityFresh0 var)) =
        Metta.Atom.sym value := by
    exact Metta.instantiate_singleton_val_var_of_not_mem _ _
      (by simp [Metta.Atom.vars])
  have hcompat := freshenRuleAvoiding_eq_legacy_empty_of_target_vars_nil
    0 (unaryIdentityQueryAtom head value) (unaryIdentityQueryRule head var).1
      (unaryIdentityQueryRule head var).2
      (by simp [unaryIdentityQueryAtom, encodeModelAtom, Metta.Atom.vars])
  unfold queryOpItemsOfRule Metta.Minimal.queryOpItemsOfRule
  rw [hcompat, hfresh]
  simp only
  rw [hmatch]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hmerge]
  simp [hloop, hinst, unaryIdentityLeaBindings,
    Metta.Minimal.evalResult, Metta.Minimal.finItem]

private theorem toLeaTTaMatchBindings_unaryIdentity
    (var value : String) :
    toLeaTTaMatchBindings (unaryIdentityBindings var value) =
      unaryIdentityLeaBindings var value := by
  simp [toLeaTTaMatchBindings, toLeaTTaMatchSubst, unaryIdentityBindings,
    unaryIdentityLeaBindings, unaryIdentityFresh0, Bindings.assign,
    Bindings.isBound, Bindings.lookup, Bindings.empty, encodeModelAtom,
    Metta.Bindings.ofSubst]

/-- Parametric LeaTTa `queryOp` membership for the singleton unary-identity
rule at counter `0`.  This lifts the reusable work-item calculation through
the public `queryOp` fold/candidate layer, leaving the HE query premises to
the declarative side. -/
theorem unaryIdentity_instantiated_queryOp_item_counter0
    (head var value : String) (gt : Metta.GroundingTable) :
    Metta.Minimal.evalResult []
        (Metta.instantiate (toLeaTTaMatchBindings (unaryIdentityBindings var value))
          (encodeModelAtom (.var (unaryIdentityFresh0 var))))
        (toLeaTTaMatchBindings (unaryIdentityBindings var value)) ∈
      (Metta.Minimal.queryOp
        (Metta.Minimal.MinEnv.ofAtomsGT
          (encodeModelAtoms (unaryIdentitySpace head var).atoms) gt)
        { counter := 0, world := Metta.Minimal.World.empty }
        [] (unaryIdentityQueryAtom head value) Metta.Bindings.empty).1 := by
  let env :=
    Metta.Minimal.MinEnv.ofAtomsGT
      (encodeModelAtoms (unaryIdentitySpace head var).atoms) gt
  let st0 : Metta.Minimal.St :=
    { counter := 0, world := Metta.Minimal.World.empty }
  have hsplit :
      Metta.Minimal.candidatesW env Metta.Minimal.World.empty
          (unaryIdentityQueryAtom head value) =
        [] ++ unaryIdentityQueryRule head var :: [] := by
    simp [env, unaryIdentitySpace, Space.ofList, unaryIdentityQueryAtom,
      unaryIdentityQueryRule, Metta.Minimal.candidatesW,
      Metta.Minimal.World.empty, Metta.Minimal.MinEnv.candidates,
      Metta.Minimal.headKey, Metta.Minimal.MinEnv.ofAtomsGT,
      Metta.Minimal.extractRules, encodeModelAtoms, encodeModelAtom]
  have hinst :
      Metta.instantiate
          (toLeaTTaMatchBindings (unaryIdentityBindings var value))
          (encodeModelAtom (.var (unaryIdentityFresh0 var))) =
        Metta.Atom.sym value := by
    rw [toLeaTTaMatchBindings_unaryIdentity]
    simpa [unaryIdentityLeaBindings, encodeModelAtom] using
      (Metta.instantiate_singleton_val_var_of_not_mem
        (unaryIdentityFresh0 var) (Metta.Atom.sym value)
        (by simp [Metta.Atom.vars]))
  have hitem :
      Metta.Minimal.evalResult []
          (Metta.instantiate (toLeaTTaMatchBindings (unaryIdentityBindings var value))
            (encodeModelAtom (.var (unaryIdentityFresh0 var))))
          (toLeaTTaMatchBindings (unaryIdentityBindings var value)) ∈
        queryOpItemsOfRule [] (unaryIdentityQueryAtom head value)
          Metta.Bindings.empty 0 (unaryIdentityQueryRule head var) := by
    rw [queryOpItemsOfRule_unaryIdentity_counter0]
    simp only [List.mem_singleton]
    rw [hinst, toLeaTTaMatchBindings_unaryIdentity]
  have hNotVarHead :
      Metta.Minimal.isVariableHeaded (unaryIdentityQueryAtom head value) = false := by
    simp [unaryIdentityQueryAtom, encodeModelAtom,
      Metta.Minimal.isVariableHeaded]
  simpa [env, st0] using
    (queryOp_contains_item_of_splitCandidate env st0 []
      (unaryIdentityQueryAtom head value) Metta.Bindings.empty
      hNotVarHead hsplit hitem)

/-- The unary-identity witness binds its fresh variable to a value atom, never
to another variable.  This public fact is a semantic premise used by the
instantiated-RHS conformance schema. -/
theorem noVarAssignmentValues_unaryIdentity
    (var value : String) :
    NoVarAssignmentValues (unaryIdentityBindings var value) := by
  intro v x hlookup
  have hlist :
      List.lookup v (unaryIdentityBindings var value).assignments =
        some (.var x) := by
    simpa [Bindings.lookup] using hlookup
  have hmem : (v, Atom.var x) ∈ (unaryIdentityBindings var value).assignments :=
    lookup_some_mem_assignments hlist
  simp [unaryIdentityBindings, unaryIdentityFresh0, Bindings.assign,
    Bindings.isBound, Bindings.lookup, Bindings.empty] at hmem

/-- The singleton unary-identity witness has no duplicate assignment keys. -/
theorem assignmentsNodup_unaryIdentity
    (var value : String) :
    AssignmentsNodup (unaryIdentityBindings var value) := by
  simp [AssignmentsNodup, unaryIdentityBindings, unaryIdentityFresh0,
    Bindings.assign, Bindings.isBound, Bindings.lookup, Bindings.empty]

private theorem freshenEquation_unaryIdentity_counter0_atFuel
    (head var : String) (extraFuel : Nat) :
    freshenEquation 0
        (.expression [.symbol head, .var var]) (.var var) (extraFuel + 5) =
      (.expression [.symbol head, .var (unaryIdentityFresh0 var)],
        .var (unaryIdentityFresh0 var)) := by
  have herase : ([var, var] : List String).eraseDups = [var] := by
    rw [List.eraseDups_cons]
    simp
  simp [freshenEquation, collectVars, collectVars.collectVarsList,
    freshMapping, renameVars, renameVars.renameVarsList, herase,
    unaryIdentityFresh0]

private theorem freshenEquation_unaryIdentity_counter0
    (head var : String) :
    freshenEquation 0
        (.expression [.symbol head, .var var]) (.var var) 10 =
      (.expression [.symbol head, .var (unaryIdentityFresh0 var)],
        .var (unaryIdentityFresh0 var)) := by
  simpa using freshenEquation_unaryIdentity_counter0_atFuel head var 5

private theorem freshenEquationAgainst_unaryIdentity_counter0_atFuel
    (head var : String) (extraFuel : Nat) :
    freshenEquationAgainst [] 0
        (.expression [.symbol head, .var var]) (.var var) (extraFuel + 5) =
      (.expression [.symbol head, .var (unaryIdentityFresh0 var)],
        .var (unaryIdentityFresh0 var)) := by
  have herase : ([var, var] : List String).eraseDups = [var] := by
    rw [List.eraseDups_cons]
    simp
  simp [freshenEquationAgainst, collectVars, collectVars.collectVarsList,
    freshMappingAgainst, Mettapedia.Languages.MeTTa.HE.chooseFreshName_nil,
    renameVars, renameVars.renameVarsList,
    herase, unaryIdentityFresh0]

private theorem freshenEquationAgainst_unaryIdentity_counter0
    (head var : String) :
    freshenEquationAgainst [] 0
        (.expression [.symbol head, .var var]) (.var var) 10 =
      (.expression [.symbol head, .var (unaryIdentityFresh0 var)],
        .var (unaryIdentityFresh0 var)) := by
  simpa using freshenEquationAgainst_unaryIdentity_counter0_atFuel head var 5

/-- HE query-interface membership for the singleton unary-identity equation on
the repaired visible-avoid path.  This is reference-side evidence only: it uses
HE's `queryEquationsAgainstVisible`/`matchAtoms` definitions, not LeaTTa. -/
theorem queryEquationsAgainstVisible_unaryIdentity_counter0_mem_atFuel
    (head var value : String) (extraFuel : Nat) :
    (.var (unaryIdentityFresh0 var), unaryIdentityBindings var value) ∈
      queryEquationsAgainstVisible (unaryIdentitySpace head var)
        (.expression [.symbol head, .symbol value]) (extraFuel + 5) := by
  have havoid :
      (collectVars (.expression [.symbol head, .symbol value])
        (extraFuel + 5)).eraseDups = [] := by
    simp [collectVars, collectVars.collectVarsList]
  have hfresh :=
    freshenEquationAgainst_unaryIdentity_counter0_atFuel head var extraFuel
  have hloopRaw :
      ({ assignments := [(var ++ "#" ++ Nat.repr 0, Atom.symbol value)]
        , equalities := [] } : Bindings).hasLoop = false := by
    apply Bindings.hasLoop_false_of_assignment_vars_nil
    intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    rfl
  simp [queryEquationsAgainstVisible, unaryIdentitySpace, Space.ofList,
    havoid, hfresh, matchAtoms, matchAtomsList, mergeBindings, getMetaType,
    Atom.expressionType, Atom.symbolType, Atom.variableType,
    unaryIdentityBindings, unaryIdentityFresh0, Bindings.assign,
    Bindings.isBound, Bindings.lookup, Bindings.empty, hloopRaw]
  have member :
      Bindings.empty.assign (var ++ "#" ++ Nat.repr 0) (.symbol value) ∈
        addVarBinding Bindings.empty (var ++ "#" ++ Nat.repr 0)
          (.symbol value) (extraFuel + 1) := by
    rw [addVarBinding_fresh
      (by simp [Bindings.empty, Bindings.lookup]) rfl extraFuel]
    simp
  exact ⟨by simpa only [Bindings.empty] using Bindings.hasLoop_empty, member⟩

/-- Fuel-10 specialization of
`queryEquationsAgainstVisible_unaryIdentity_counter0_mem_atFuel`, preserved for
the executable `queryOp` bridge at counter 0. -/
theorem queryEquationsAgainstVisible_unaryIdentity_counter0_mem
    (head var value : String) :
    (.var (unaryIdentityFresh0 var), unaryIdentityBindings var value) ∈
      queryEquationsAgainstVisible (unaryIdentitySpace head var)
        (.expression [.symbol head, .symbol value]) 10 := by
  simpa using
      queryEquationsAgainstVisible_unaryIdentity_counter0_mem_atFuel
      head var value 5

/-- HE public query-interface membership for the singleton unary-identity
equation.  This is the premise consumed by the official `MettaCall` rule. -/
theorem queryEquations_unaryIdentity_counter0_mem_atFuel
    (head var value : String) (extraFuel : Nat) :
    (.var (unaryIdentityFresh0 var), unaryIdentityBindings var value) ∈
      queryEquations (unaryIdentitySpace head var)
        (.expression [.symbol head, .symbol value]) (extraFuel + 5) := by
  have hfresh := freshenEquation_unaryIdentity_counter0_atFuel head var extraFuel
  have hloopRaw :
      ({ assignments := [(var ++ "#" ++ Nat.repr 0, Atom.symbol value)]
        , equalities := [] } : Bindings).hasLoop = false := by
    apply Bindings.hasLoop_false_of_assignment_vars_nil
    intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    rfl
  simp [queryEquations, unaryIdentitySpace, Space.ofList, hfresh,
    matchAtoms, matchAtomsList, mergeBindings, getMetaType,
    Atom.expressionType, Atom.symbolType, Atom.variableType,
    unaryIdentityBindings, unaryIdentityFresh0, Bindings.assign,
    Bindings.isBound, Bindings.lookup, Bindings.empty, hloopRaw]
  have member :
      Bindings.empty.assign (var ++ "#" ++ Nat.repr 0) (.symbol value) ∈
        addVarBinding Bindings.empty (var ++ "#" ++ Nat.repr 0)
          (.symbol value) (extraFuel + 1) := by
    rw [addVarBinding_fresh
      (by simp [Bindings.empty, Bindings.lookup]) rfl extraFuel]
    simp
  exact ⟨by simpa only [Bindings.empty] using Bindings.hasLoop_empty, member⟩

/-- Scoped query membership for the singleton unary-identity equation.  This is the premise consumed by the official `MettaCall` rule. -/
theorem queryEquationsAvoiding_unaryIdentity_counter0_mem_atFuel
    (head var value : String) (extraFuel : Nat) :
    (.var (unaryIdentityFresh0 var), unaryIdentityBindings var value) ∈
      queryEquationsAvoiding [] (unaryIdentitySpace head var)
        (.expression [.symbol head, .symbol value]) (extraFuel + 5) := by
  have hfresh : freshenEquationAvoiding [] 0
        (.expression [.symbol head, .var var]) (.var var) =
      (.expression [.symbol head, .var (unaryIdentityFresh0 var)],
        .var (unaryIdentityFresh0 var)) := by
    have herase : ([var, var] : List String).eraseDups = [var] := by
      rw [List.eraseDups_cons]
      simp
    simp [freshenEquationAvoiding, atomVariables, atomListVariables, herase, renameAtom,
      renameAtomList, instanceName, freeSuffix, suffixName, unaryIdentityFresh0]
  have hloopRaw :
      ({ assignments := [(var ++ "#" ++ Nat.repr 0, Atom.symbol value)]
        , equalities := [] } : Bindings).hasLoop = false := by
    apply Bindings.hasLoop_false_of_assignment_vars_nil
    intro entry member
    have same := List.mem_singleton.mp member
    subst entry
    rfl
  simp [queryEquationsAvoiding, unaryIdentitySpace, Space.ofList, hfresh,
    matchAtoms, matchAtomsList, mergeBindings, getMetaType,
    Atom.expressionType, Atom.symbolType, Atom.variableType,
    unaryIdentityBindings, unaryIdentityFresh0, Bindings.assign,
    Bindings.isBound, Bindings.lookup, Bindings.empty, hloopRaw]
  have member :
      Bindings.empty.assign (var ++ "#" ++ Nat.repr 0) (.symbol value) ∈
        addVarBinding Bindings.empty (var ++ "#" ++ Nat.repr 0)
          (.symbol value) (extraFuel + 1) := by
    rw [addVarBinding_fresh
      (by simp [Bindings.empty, Bindings.lookup]) rfl extraFuel]
    simp
  exact ⟨by simpa only [Bindings.empty] using Bindings.hasLoop_empty, member⟩

theorem queryEquationsAvoiding_unaryIdentity_counter0_mem
    (head var value : String) :
    (.var (unaryIdentityFresh0 var), unaryIdentityBindings var value) ∈
      queryEquationsAvoiding [] (unaryIdentitySpace head var)
        (.expression [.symbol head, .symbol value]) 10 := by
  simpa using queryEquationsAvoiding_unaryIdentity_counter0_mem_atFuel head var value 5

/-- A ground call with empty bindings is covered by the empty avoidance list. -/
theorem unaryIdentity_cover (head value : String) :
    CoversEvaluation [] [] (.expression [.symbol head, .symbol value]) Atom.undefinedType Bindings.empty := by
  intro name h
  simp [equationScope, Atom.undefinedType, atomVariables, atomListVariables, Bindings.names, Bindings.empty] at h

/-- Fuel-10 specialization of `queryEquations_unaryIdentity_counter0_mem_atFuel`,
preserved for the official `MettaCall` wrapper at counter 0. -/
theorem queryEquations_unaryIdentity_counter0_mem
    (head var value : String) :
    (.var (unaryIdentityFresh0 var), unaryIdentityBindings var value) ∈
      queryEquations (unaryIdentitySpace head var)
        (.expression [.symbol head, .symbol value]) 10 := by
  simpa using queryEquations_unaryIdentity_counter0_mem_atFuel head var value 5

/-- Parameterized observed-call package for the singleton unary-identity rule.
The theorem deliberately keeps the official HE query premises explicit; its
contribution is deriving the LeaTTa executable item generically and packaging
the result through the declarative `MettaCall` constructor. -/
theorem unaryIdentity_observed_mettaCall_of_queries_counter0
    (head var value : String) (gt : Metta.GroundingTable)
    (h_not_special :
      ¬ SpecialFormHead (.expression [.symbol head, .symbol value]))
    (h_not_error :
      isErrorAtom (.expression [.symbol head, .symbol value]) = false)
    (h_query_visible :
      (.var (unaryIdentityFresh0 var), unaryIdentityBindings var value) ∈
        queryEquationsAgainstVisible (unaryIdentitySpace head var)
          (.expression [.symbol head, .symbol value]) 10)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression [.symbol head, .symbol value]) Atom.undefinedType Bindings.empty)
    (h_query_public :
      (.var (unaryIdentityFresh0 var), unaryIdentityBindings var value) ∈
        queryEquationsAvoiding avoid (unaryIdentitySpace head var)
          (.expression [.symbol head, .symbol value]) 10)
    (h_recurse :
      OrdinaryCallReturnRel (unaryIdentitySpace head var) GroundedDispatch.none
        (.expression [.symbol head, .symbol value]) (.symbol value) Atom.undefinedType (unaryIdentityBindings var value)
        (.symbol value, unaryIdentityBindings var value)) :
    LeaTTaObservedMettaCall
      (unaryIdentitySpace head var) GroundedDispatch.none 10
      (.expression [.symbol head, .symbol value]) (.symbol value)
      Atom.undefinedType Bindings.empty (unaryIdentityBindings var value)
      gt [] 0 := by
  have heq : (unaryIdentityBindings var value).equalities = [] := by
    simp [unaryIdentityBindings, Bindings.assign, Bindings.empty]
  have hfull :
      (unaryIdentityBindings var value).applyFull
          (.var (unaryIdentityFresh0 var)) 10 =
        .symbol value := by
    rw [Bindings.applyFull_no_equalities heq]
    simp [Bindings.apply, Bindings.resolve, unaryIdentityBindings,
      Bindings.resolveAtomAux, Bindings.hasAssignedVar,
      unaryIdentityFresh0, Bindings.assign, Bindings.isBound, Bindings.empty,
      Bindings.lookup]
  simpa [hfull] using
    (observedMettaCall_of_instantiated_item_againstVisible_empty_input
      (space := unaryIdentitySpace head var)
      (d := GroundedDispatch.none)
      (n := 9)
      (es := [.symbol head, .symbol value])
      (rhs := .var (unaryIdentityFresh0 var))
      (qb := unaryIdentityBindings var value)
      (type_ := Atom.undefinedType)
      (outputBindings := unaryIdentityBindings var value)
      (gt := gt)
      (prev := [])
      (counter := 0)
      h_not_special
      h_not_error
      (by
        simp [HeadNotExecutable, GroundedDispatch.none]
        constructor
        · intro hunify
          apply h_not_special
          simp [SpecialFormHead, hunify]
        · intro hswitch
          apply h_not_special
          simp [SpecialFormHead, hswitch])
      h_query_visible
      h_cover
      h_query_public
      heq
      (by
        rw [toLeaTTaMatchBindings_unaryIdentity]
        exact ClosedValueBindings.valueKeysFreshForValues
          (ClosedValueBindings.val (by simp [Metta.Atom.vars])
            ClosedValueBindings.nil))
      (by simp [atomDepth])
      (unaryIdentity_instantiated_queryOp_item_counter0 head var value gt)
      (by
        simpa [hfull] using h_recurse))

/-- Parameterized unary-identity observed-call package with the official HE
query premises discharged from `matchAtoms` on the singleton equation space. -/
theorem unaryIdentity_observed_mettaCall_counter0
    (head var value : String) (gt : Metta.GroundingTable)
    (h_not_special :
      ¬ SpecialFormHead (.expression [.symbol head, .symbol value]))
    (h_not_error :
      isErrorAtom (.expression [.symbol head, .symbol value]) = false)
    (h_recurse :
      OrdinaryCallReturnRel (unaryIdentitySpace head var) GroundedDispatch.none
        (.expression [.symbol head, .symbol value]) (.symbol value) Atom.undefinedType (unaryIdentityBindings var value)
        (.symbol value, unaryIdentityBindings var value)) :
    LeaTTaObservedMettaCall
      (unaryIdentitySpace head var) GroundedDispatch.none 10
      (.expression [.symbol head, .symbol value]) (.symbol value)
      Atom.undefinedType Bindings.empty (unaryIdentityBindings var value)
      gt [] 0 := by
  exact
    unaryIdentity_observed_mettaCall_of_queries_counter0
      head var value gt h_not_special h_not_error
      (queryEquationsAgainstVisible_unaryIdentity_counter0_mem head var value)
      (unaryIdentity_cover head value)
      (queryEquationsAvoiding_unaryIdentity_counter0_mem head var value)
      h_recurse

/-- Engine-step-shaped unary-identity package: the same non-ground assignment
fragment as `unaryIdentity_observed_mettaCall_counter0`, but exposed through the
`mettaCallStep`-shaped relation used by the engine-parametric boundary. -/
theorem unaryIdentity_leattaEquationMettaCallStep_counter0
    (head var value : String)
    (h_not_special :
      ¬ SpecialFormHead (.expression [.symbol head, .symbol value]))
    (h_not_error :
      isErrorAtom (.expression [.symbol head, .symbol value]) = false)
    (h_recurse :
      OrdinaryCallReturnRel (unaryIdentitySpace head var) GroundedDispatch.none
        (.expression [.symbol head, .symbol value]) (.symbol value) Atom.undefinedType (unaryIdentityBindings var value)
        (.symbol value, unaryIdentityBindings var value)) :
    LeaTTaEquationMettaCallStep
      (unaryIdentitySpace head var) GroundedDispatch.none 10
      (.expression [.symbol head, .symbol value]) Atom.undefinedType
      Bindings.empty (.symbol value, unaryIdentityBindings var value) := by
  have heq : (unaryIdentityBindings var value).equalities = [] := by
    simp [unaryIdentityBindings, Bindings.assign, Bindings.empty]
  have hfull :
      (unaryIdentityBindings var value).applyFull
          (.var (unaryIdentityFresh0 var)) 10 =
        .symbol value := by
    rw [Bindings.applyFull_no_equalities heq]
    simp [Bindings.apply, Bindings.resolve, unaryIdentityBindings,
      Bindings.resolveAtomAux, Bindings.hasAssignedVar,
      unaryIdentityFresh0, Bindings.assign, Bindings.isBound, Bindings.empty,
      Bindings.lookup]
  simpa [hfull] using
    (leattaEquationMettaCallStep_of_instantiated_item_againstVisible_empty_input
      (space := unaryIdentitySpace head var)
      (d := GroundedDispatch.none)
      (n := 9)
      (es := [.symbol head, .symbol value])
      (rhs := .var (unaryIdentityFresh0 var))
      (type_ := Atom.undefinedType)
      (qb := unaryIdentityBindings var value)
      (outputBindings := unaryIdentityBindings var value)
      (gt := (default : Metta.GroundingTable))
      (prev := [])
      (counter := 0)
      h_not_special
      h_not_error
      (by
        simp [HeadNotExecutable, GroundedDispatch.none]
        constructor
        · intro hunify
          apply h_not_special
          simp [SpecialFormHead, hunify]
        · intro hswitch
          apply h_not_special
          simp [SpecialFormHead, hswitch])
      (queryEquationsAgainstVisible_unaryIdentity_counter0_mem head var value)
      (unaryIdentity_cover head value)
      (queryEquationsAvoiding_unaryIdentity_counter0_mem head var value)
      heq
      (by
        rw [toLeaTTaMatchBindings_unaryIdentity]
        exact ClosedValueBindings.valueKeysFreshForValues
          (ClosedValueBindings.val (by simp [Metta.Atom.vars])
            ClosedValueBindings.nil))
      (by simp [atomDepth])
      (unaryIdentity_instantiated_queryOp_item_counter0
        head var value (default : Metta.GroundingTable))
      (by
        simpa [hfull] using h_recurse))

/-- The unary-identity step-shaped package feeds the generic soundness hook and
therefore models the official declarative HE `MettaCall` rule. -/
theorem unaryIdentity_leattaEquationMettaCallStep_counter0_sound
    (head var value : String)
    (h_not_special :
      ¬ SpecialFormHead (.expression [.symbol head, .symbol value]))
    (h_not_error :
      isErrorAtom (.expression [.symbol head, .symbol value]) = false)
    (h_recurse :
      OrdinaryCallReturnRel (unaryIdentitySpace head var) GroundedDispatch.none
        (.expression [.symbol head, .symbol value]) (.symbol value) Atom.undefinedType (unaryIdentityBindings var value)
        (.symbol value, unaryIdentityBindings var value)) :
    MettaCall (unaryIdentitySpace head var) GroundedDispatch.none
      (.expression [.symbol head, .symbol value]) Atom.undefinedType
      Bindings.empty (.symbol value, unaryIdentityBindings var value) := by
  exact
    leattaEquationMettaCallStep_sound
      (unaryIdentity_leattaEquationMettaCallStep_counter0
        head var value h_not_special h_not_error h_recurse)

private def nonGroundAssignmentSpace : Space :=
  Space.ofList
    [.expression
      [.symbol "=", .expression [.symbol "id", .var "x"], .var "x"]]

private def nonGroundAssignmentBindings : Bindings :=
  Bindings.empty.assign "x#0" (.symbol "a")

private def nonGroundAssignmentQueryAtom : Metta.Atom :=
  encodeModelAtom (.expression [.symbol "id", .symbol "a"])

private def nonGroundAssignmentQueryRule : Metta.Atom × Metta.Atom :=
  (encodeModelAtom (.expression [.symbol "id", .var "x"]),
    encodeModelAtom (.var "x"))

private def nonGroundAssignmentLeaBindings : Metta.Bindings :=
  [Metta.BindingRel.val "x#0" (Metta.Atom.sym "a")]

private theorem queryEquationsAgainstVisible_nonGroundAssignment :
    queryEquationsAgainstVisible nonGroundAssignmentSpace
        (.expression [.symbol "id", .symbol "a"]) 10 =
      [(.var "x#0", nonGroundAssignmentBindings)] := by
  rfl

private theorem queryEquations_nonGroundAssignment :
    queryEquations nonGroundAssignmentSpace
        (.expression [.symbol "id", .symbol "a"]) 10 =
      [(.var "x#0", nonGroundAssignmentBindings)] := by
  rfl

private theorem queryOpItemsOfRule_nonGroundAssignment_counter0 :
    queryOpItemsOfRule [] nonGroundAssignmentQueryAtom Metta.Bindings.empty 0
      nonGroundAssignmentQueryRule =
        [Metta.Minimal.evalResult []
          (Metta.Atom.sym "a") nonGroundAssignmentLeaBindings] := by
  have hx0 : "x#" ++ Nat.repr 0 = "x#0" := by
    decide
  simpa [nonGroundAssignmentQueryAtom, nonGroundAssignmentQueryRule,
    nonGroundAssignmentLeaBindings, unaryIdentityQueryAtom,
    unaryIdentityQueryRule, unaryIdentityLeaBindings, unaryIdentityFresh0,
    encodeModelAtom, hx0] using
      (queryOpItemsOfRule_unaryIdentity_counter0 "id" "x" "a")

private theorem toLeaTTaMatchBindings_nonGroundAssignment :
    toLeaTTaMatchBindings nonGroundAssignmentBindings =
      nonGroundAssignmentLeaBindings := by
  rfl

private theorem noVarAssignmentValues_nonGroundAssignment :
    NoVarAssignmentValues nonGroundAssignmentBindings := by
  intro v x hlookup
  have hlist :
      List.lookup v nonGroundAssignmentBindings.assignments =
        some (.var x) := by
    simpa [Bindings.lookup] using hlookup
  have hmem : (v, Atom.var x) ∈ nonGroundAssignmentBindings.assignments :=
    lookup_some_mem_assignments hlist
  simp [nonGroundAssignmentBindings, Bindings.assign, Bindings.isBound,
    Bindings.lookup, Bindings.empty] at hmem

private theorem assignmentsNodup_nonGroundAssignment :
    AssignmentsNodup nonGroundAssignmentBindings := by
  simp [AssignmentsNodup, nonGroundAssignmentBindings, Bindings.assign,
    Bindings.isBound, Bindings.lookup, Bindings.empty]

private theorem nonGroundAssignment_applyFull_x0 :
    nonGroundAssignmentBindings.applyFull (.var "x#0") 10 = .symbol "a" := by
  rw [Bindings.applyFull_no_equalities (b := nonGroundAssignmentBindings) rfl]
  simp [nonGroundAssignmentBindings, Bindings.apply, Bindings.resolve,
    Bindings.resolveAtomAux, Bindings.assign, Bindings.isBound, Bindings.empty,
    Bindings.lookup]

private theorem nonGroundAssignment_instantiated_queryOp_item_counter0
    (gt : Metta.GroundingTable) :
    Metta.Minimal.evalResult []
        (Metta.instantiate (toLeaTTaMatchBindings nonGroundAssignmentBindings)
          (encodeModelAtom (.var "x#0")))
        (toLeaTTaMatchBindings nonGroundAssignmentBindings) ∈
      (Metta.Minimal.queryOp
        (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms nonGroundAssignmentSpace.atoms) gt)
        { counter := 0, world := Metta.Minimal.World.empty }
        [] nonGroundAssignmentQueryAtom Metta.Bindings.empty).1 := by
  have hx0 : "x#" ++ Nat.repr 0 = "x#0" := by decide
  simpa [nonGroundAssignmentSpace, nonGroundAssignmentBindings,
    nonGroundAssignmentQueryAtom, unaryIdentitySpace, unaryIdentityBindings,
    unaryIdentityQueryAtom, unaryIdentityFresh0, Bindings.assign,
    Bindings.isBound, Bindings.lookup, Bindings.empty, hx0] using
    (unaryIdentity_instantiated_queryOp_item_counter0 "id" "x" "a" gt)

/-- Concrete non-ground assignment transport for the repaired query interface:
`(= (id $x) $x)` queried at `(id a)` emits `a` on LeaTTa's `queryOp` layer. -/
theorem nonGroundAssignment_FreshenedQueryOpItemTransportAgainstVisible_counter0
    (gt : Metta.GroundingTable) :
    FreshenedQueryOpItemTransportAgainstVisible
      nonGroundAssignmentSpace (.expression [.symbol "id", .symbol "a"])
      (.var "x#0") nonGroundAssignmentBindings 10 gt [] 0 := by
  intro idx lhs rawRhs pre post k hk hzip _hmatch hsplit
  have hshape :
      (lhs = .expression [.symbol "id", .var "x"] ∧ rawRhs = .var "x") ∧
        idx = 0 := by
    simpa [nonGroundAssignmentSpace, Space.ofList] using hzip
  rcases hshape with ⟨⟨hlhs, hrhs⟩, hidx⟩
  subst hidx
  subst hlhs
  subst hrhs
  have hkid : k = "id" := by
    simpa [nonGroundAssignmentQueryAtom, encodeModelAtom,
      Metta.Minimal.headKey] using hk.symm
  subst hkid
  have hsingle :
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms nonGroundAssignmentSpace.atoms) gt)
          Metta.Minimal.World.empty
          (encodeModelAtom (.expression [.symbol "id", .symbol "a"])) =
        [(encodeModelAtom (.expression [.symbol "id", .var "x"]),
          encodeModelAtom (.var "x"))] := by
    simp [nonGroundAssignmentSpace, Space.ofList, Metta.Minimal.candidatesW,
      Metta.Minimal.World.empty, Metta.Minimal.MinEnv.candidates,
      Metta.Minimal.headKey, Metta.Minimal.MinEnv.ofAtomsGT,
      Metta.Minimal.extractRules, encodeModelAtoms, encodeModelAtom]
  rw [hsingle] at hsplit
  have hpre_nil : pre = [] := by
    cases pre with
    | nil => rfl
    | cons hd tl => simp at hsplit
  subst hpre_nil
  have hpost_nil : post = [] := by
    simpa using hsplit
  subst hpost_nil
  have hmatchLoop : Metta.Bindings.hasLoop
      [Metta.BindingRel.val "x#0" (Metta.Atom.sym "a")] = false :=
    hasLoop_singleton_val_closed_false "x#0" (Metta.Atom.sym "a")
      (by simp [Metta.Atom.vars])
  have hcompat := freshenRuleAvoiding_eq_legacy_empty_of_target_vars_nil
    0 (encodeModelAtom (.expression [.symbol "id", .symbol "a"]))
      (encodeModelAtom (.expression [.symbol "id", .var "x"])) (encodeModelAtom (.var "x"))
      (by simp [encodeModelAtom, Metta.Atom.vars])
  refine
    ⟨Metta.Atom.expr [Metta.Atom.sym "id", Metta.Atom.var "x#0"],
      Metta.Atom.var "x#0",
      [Metta.BindingRel.val "x#0" (Metta.Atom.sym "a")],
      nonGroundAssignmentLeaBindings, Metta.Atom.sym "a",
      ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_nil, Nat.add_zero]
    rw [hcompat]
    simp [encodeModelAtom, Metta.Minimal.freshenRule, Metta.Atom.vars,
      Metta.Subst.apply, Metta.Subst.lookup]
    decide
  · simp [encodeModelAtom, Metta.matchAtoms, Metta.matchAtomsWith,
      Metta.matchAll, Metta.Bindings.merge, Metta.Bindings.mergeOne,
      Metta.Bindings.addVarBinding, Metta.Bindings.addValRaw,
      Metta.Bindings.removeVal, hmatchLoop]
  · change [Metta.BindingRel.val "x#0" (Metta.Atom.sym "a")] ∈
      Metta.Bindings.merge []
        [Metta.BindingRel.val "x#0" (Metta.Atom.sym "a")]
    exact singleton_val_mem_merge_empty_left "x#0" (Metta.Atom.sym "a")
      (by intro w; simp)
  · simpa [nonGroundAssignmentLeaBindings] using
      (hasLoop_singleton_val_closed_false "x#0" (Metta.Atom.sym "a")
        (by simp [Metta.Atom.vars]))
  · simpa [nonGroundAssignmentLeaBindings] using
      (Metta.instantiate_singleton_val_var_of_not_mem
        "x#0" (Metta.Atom.sym "a") (by simp [Metta.Atom.vars])).symm
  · unfold Metta.AlphaEq Metta.canonicalizeVars encodeModelAtom
    simp [nonGroundAssignment_applyFull_x0,
      Metta.Atom.vars, Metta.distinctVarsAux, Metta.renameVars]

theorem nonGroundAssignment_EquationMatchVisibleItemTransportAgainst_counter0
    (gt : Metta.GroundingTable) :
    EquationMatchVisibleItemTransportAgainst
      nonGroundAssignmentSpace (.expression [.symbol "id", .symbol "a"])
      (.var "x#0") nonGroundAssignmentBindings 10 gt [] 0 := by
  exact
    equationMatchVisibleItemTransportAgainst_of_freshened_item_transport
      (nonGroundAssignment_FreshenedQueryOpItemTransportAgainstVisible_counter0 gt)

private theorem nonGroundAssignment_queryOp_visible_successor_counter0
    (gt : Metta.GroundingTable) :
    LeaTTaVisibleEquationStepObservation
      nonGroundAssignmentSpace GroundedDispatch.none 10
      (.expression [.symbol "id", .symbol "a"]) (.symbol "a") gt [] 0 := by
  have hNotSpecial :
      ¬ SpecialFormHead (.expression [.symbol "id", .symbol "a"]) := by
    simp [SpecialFormHead]
  have hNotGrounded :
      HeadNotExecutable GroundedDispatch.none
        (.expression [.symbol "id", .symbol "a"]) := by
    simp [HeadNotExecutable, GroundedDispatch.none]
  have hk : Metta.Minimal.headKey
      (encodeModelAtom (.expression [.symbol "id", .symbol "a"])) = some "id" := by
    simp [encodeModelAtom, Metta.Minimal.headKey]
  have hquery : (.var "x#0", nonGroundAssignmentBindings) ∈
      queryEquationsAgainstVisible nonGroundAssignmentSpace
        (.expression [.symbol "id", .symbol "a"]) 10 := by
    simp [queryEquationsAgainstVisible_nonGroundAssignment]
  simpa [nonGroundAssignment_applyFull_x0] using
    (equation_match_againstVisible_observation_of_freshened_item_transport
      (space := nonGroundAssignmentSpace)
      (d := GroundedDispatch.none)
      (fuel := 10)
      (es := [.symbol "id", .symbol "a"])
      (rhs := .var "x#0")
      (qb := nonGroundAssignmentBindings)
      (gt := gt)
      (prev := [])
      (counter := 0)
      hNotSpecial
      hNotGrounded
      hk
      hquery
      (nonGroundAssignment_FreshenedQueryOpItemTransportAgainstVisible_counter0 gt))

/-- First non-ground observed-call package: faithful HE assignment matching and
LeaTTa's executable `queryOp` agree on the visible successor for `(id a)`. -/
theorem nonGroundAssignment_observed_mettaCall_counter0
    (gt : Metta.GroundingTable) :
    LeaTTaObservedMettaCall
      nonGroundAssignmentSpace GroundedDispatch.none 10
      (.expression [.symbol "id", .symbol "a"]) (.symbol "a")
      Atom.undefinedType Bindings.empty nonGroundAssignmentBindings gt [] 0 := by
  have hx0 : unaryIdentityFresh0 "x" = "x#0" := by
    decide
  have h_recurse :
      EvalAtom (unaryIdentitySpace "id" "x") GroundedDispatch.none
        (.symbol "a") Atom.undefinedType (unaryIdentityBindings "x" "a")
        (.symbol "a", unaryIdentityBindings "x" "a") := by
    apply EvalAtom.type_cast (fuel := 10)
    · rfl
    · decide
    · left
      rfl
    · decide
  simpa [nonGroundAssignmentSpace, nonGroundAssignmentBindings,
      unaryIdentitySpace, unaryIdentityBindings, hx0] using
    (unaryIdentity_observed_mettaCall_counter0
      "id" "x" "a" gt
      (by simp [SpecialFormHead])
      rfl
      (OrdinaryCallReturnRel.of_eval (by decide) h_recurse))

/-- Engine-step-shaped non-ground assignment package through the repaired
freshened-item transport path. -/
theorem nonGroundAssignment_leattaEquationMettaCallStep_counter0
    (gt : Metta.GroundingTable) :
    LeaTTaEquationMettaCallStep
      nonGroundAssignmentSpace GroundedDispatch.none 10
      (.expression [.symbol "id", .symbol "a"]) Atom.undefinedType
      Bindings.empty (.symbol "a", nonGroundAssignmentBindings) := by
  have h_recurse :
      EvalAtom nonGroundAssignmentSpace GroundedDispatch.none
        (.symbol "a") Atom.undefinedType nonGroundAssignmentBindings
        (.symbol "a", nonGroundAssignmentBindings) := by
    apply EvalAtom.type_cast (fuel := 10)
    · rfl
    · decide
    · left
      rfl
    · decide
  exact
    leattaEquationMettaCallStep_of_freshened_item_transport_againstVisible_with_merge_final
      (space := nonGroundAssignmentSpace)
      (d := GroundedDispatch.none)
      (fuel := 10)
      (es := [.symbol "id", .symbol "a"])
      (rhs := .var "x#0")
      (type_ := Atom.undefinedType)
      (qb := nonGroundAssignmentBindings)
      (inputBindings := Bindings.empty)
      (merged := nonGroundAssignmentBindings)
      (gt := gt)
      (prev := [])
      (counter := 0)
      (k := "id")
      (finalResult := (.symbol "a", nonGroundAssignmentBindings))
      (by simp [SpecialFormHead])
      rfl
      (by simp [HeadNotExecutable, GroundedDispatch.none])
      (by simp [encodeModelAtom, Metta.Minimal.headKey])
      (by simp [queryEquationsAgainstVisible_nonGroundAssignment])
      (avoid := [])
      (by
        intro name h
        simp [equationScope, Atom.undefinedType, atomVariables, atomListVariables, Bindings.names, Bindings.empty] at h)
      (by decide)
      (nonGroundAssignment_FreshenedQueryOpItemTransportAgainstVisible_counter0 gt)
      (by
        rw [show 10 = 9 + 1 by decide]
        rw [mergeBindings_empty_right nonGroundAssignmentBindings 9]
        simp)
      (queryEquationsAgainstVisible_hasLoop_false
        (space := nonGroundAssignmentSpace)
        (atom := .expression [.symbol "id", .symbol "a"])
        (rhs := .var "x#0")
        (qb := nonGroundAssignmentBindings)
        (fuel := 10)
        (by simp [queryEquationsAgainstVisible_nonGroundAssignment]))
      (by
        apply OrdinaryCallReturnRel.of_eval
          (by rw [nonGroundAssignment_applyFull_x0]; decide)
        simpa [nonGroundAssignment_applyFull_x0] using h_recurse)

/-- HE's small-step equation rule can step to a freshened RHS variable name. -/
theorem equation_match_freshRhsBoundary_step :
    HESmallStep freshRhsBoundarySpace GroundedDispatch.none 10
      (.expression [.symbol "q"]) (.var "z#0") := by
  have hstep :
      HESmallStep freshRhsBoundarySpace GroundedDispatch.none 10
        (.expression [.symbol "q"])
        (Bindings.empty.applyFull (.var "z#0") 10) := by
    apply HESmallStep.equation_match
    · simp [SpecialFormHead]
    · simp [HeadNotExecutable, GroundedDispatch.none]
    · decide
    · rfl
  simpa [freshRhsBoundary_empty_applyFull_z0] using hstep

/-- The actual HE `equation_match` step at the fresh-RHS boundary already has a
visible LeaTTa `queryOp` successor once we target the honest alpha-level
runtime notion. This is the smallest end-to-end positive witness for the
corrected interface theorem at the real small-step boundary. -/
theorem equation_match_freshRhsBoundary_queryOp_visible_successor_counter5
    (gt : Metta.GroundingTable) :
    HESmallStep freshRhsBoundarySpace GroundedDispatch.none 10
      (.expression [.symbol "q"]) (.var "z#0") ∧
    ∃ emitted m,
      Metta.Minimal.evalResult [] emitted m ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms freshRhsBoundarySpace.atoms) gt)
          { counter := 5, world := Metta.Minimal.World.empty }
          [] freshRhsBoundaryQueryAtom Metta.Bindings.empty).1 ∧
      Metta.AlphaEq emitted (Metta.Atom.var "z#0") := by
  refine ⟨equation_match_freshRhsBoundary_step, ?_⟩
  have hNotSpecial : ¬ SpecialFormHead (.expression [.symbol "q"]) := by
    simp [SpecialFormHead]
  have hNotGrounded : HeadNotExecutable GroundedDispatch.none (.expression [.symbol "q"]) := by
    simp [HeadNotExecutable, GroundedDispatch.none]
  have hk : Metta.Minimal.headKey freshRhsBoundaryQueryAtom = some "q" := by
    simp [freshRhsBoundaryQueryAtom, encodeModelAtom, Metta.Minimal.headKey]
  have hquery : (.var "z#0", Bindings.empty) ∈
      queryEquations freshRhsBoundarySpace (.expression [.symbol "q"]) 10 := by
    simp [queryEquations_freshRhsBoundary]
  have hNoLoop : Bindings.empty.hasLoop = false := Bindings.hasLoop_empty
  simpa [freshRhsBoundary_empty_applyFull_z0, freshRhsBoundaryQueryAtom,
      encodeModelAtom] using
    (equation_match_queryOp_visible_successor_package_of_transport
      (space := freshRhsBoundarySpace)
      (d := GroundedDispatch.none)
      (fuel := 10)
      (es := [.symbol "q"])
      (rhs := .var "z#0")
      (qb := Bindings.empty)
      (gt := gt)
      (k := "q")
      (prev := [])
      (counter := 5)
      hNotSpecial
      hNotGrounded
      hk
      hquery
      (by decide)
      hNoLoop
      (freshRhsBoundary_EquationMatchVisibleItemTransport_counter5 gt)).2

/-- Raw LeaTTa/MOPS equality firing does not contain the freshened HE RHS from
`equation_match_freshRhsBoundary_step`; it fires the unfreshened rule instead.
This is the concrete alpha/freshening boundary the later bridge must quotient
or target via the executable `queryOp` layer rather than raw
`equalityReductions` alone. -/
theorem freshRhsBoundary_not_mem_equalityReductions :
    encodeModelAtom (.var "z#0") ∉
      Metta.equalityReductions (toLeaTTaSpace freshRhsBoundarySpace)
        (encodeModelAtom (.expression [.symbol "q"])) := by
  simp [freshRhsBoundarySpace, Space.ofList, toLeaTTaSpace, Metta.equalityReductions,
    Metta.Space.equalityRules, encodeModelAtoms, encodeModelAtom, Metta.matchAtoms,
    Metta.matchAtomsWith, Metta.matchAll, Metta.instantiate,
    Metta.Bindings.hasLoop, Metta.Bindings.vars]

/-- Honest global boundary: an exact theorem sending every HE
`HESmallStep.equation_match` successor directly into raw LeaTTa/MOPS
`equalityReductions` is false. The missing theorem therefore reflects a real
semantic boundary, not mere unfinished proof plumbing. -/
theorem equation_match_not_simulated_by_equalityReductions :
    ∃ (space : Space) (fuel : Nat) (src dst : Atom),
      HESmallStep space GroundedDispatch.none fuel src dst ∧
      encodeModelAtom dst ∉
        Metta.equalityReductions (toLeaTTaSpace space) (encodeModelAtom src) := by
  refine ⟨freshRhsBoundarySpace, 10, .expression [.symbol "q"], .var "z#0", ?_, ?_⟩
  · exact equation_match_freshRhsBoundary_step
  · exact freshRhsBoundary_not_mem_equalityReductions

/-!
The previous boundary only rules out exact simulation into raw
`equalityReductions`. A stronger mismatch remains even on the executable
`queryOp` layer: after the faithful HE matcher migration, variable-variable
relationships stay as equality constraints, while the current
`toLeaTTaMatchBindings` projection only carries value assignments. If a query
atom already contains a name that collides with a later freshened rule variable,
the repaired visible-avoid HE query interface preserves the equality information,
but the instantiated-item shortcut below cannot transport it on its own.
-/

private def chainResolveBoundarySpace : Space :=
  Space.ofList
    [.expression
      [.symbol "=",
        .expression [.symbol "f", .var "x", .var "y"],
        .var "x"]]

private def chainResolveBoundaryQueryBindings : Bindings :=
  { assignments := [("y#1", .symbol "a")]
  , equalities := [("y#1", "x#0")] }

private def chainResolveBoundaryVisibleQueryBindings : Bindings :=
  { assignments := [("y#2", .symbol "a")]
  , equalities := [("y#1", "x#0")] }

private theorem queryEquations_chainResolveBoundary :
    queryEquations chainResolveBoundarySpace
        (.expression [.symbol "f", .var "y#1", .symbol "a"]) 10 =
      [(.var "x#0", chainResolveBoundaryQueryBindings)] := by
  rfl

/-- The visible-avoid query interface repairs the generated-name collision in the
boundary example: the freshened rule variable corresponding to the raw `y`
parameter is renamed to `y#2`, avoiding the query's already-visible `y#1`.
After G3's faithful matcher migration, the `x`/`y#1` relationship is an
equality, not the old oriented assignment chain. -/
private theorem queryEquationsAgainstVisible_chainResolveBoundary :
    queryEquationsAgainstVisible chainResolveBoundarySpace
        (.expression [.symbol "f", .var "y#1", .symbol "a"]) 10 =
      [(.var "x#0", chainResolveBoundaryVisibleQueryBindings)] := by
  rfl

/-- On the repaired visible-avoid query interface, the chain boundary no longer
reuses the query-visible name `y#1` for the freshened rule parameter `y`; the
freshened binding key is `y#2` instead. The equality relation `y#1 = x#0`
remains explicit, which is the G3b equality-threading seam. -/
theorem chainResolveBoundary_queryEquationsAgainstVisible_avoids_query_name :
    queryEquationsAgainstVisible chainResolveBoundarySpace
        (.expression [.symbol "f", .var "y#1", .symbol "a"]) 10 =
      [(.var "x#0", chainResolveBoundaryVisibleQueryBindings)] ∧
    chainResolveBoundaryVisibleQueryBindings.lookup "y#1" = none ∧
    chainResolveBoundaryVisibleQueryBindings.lookup "y#2" = some (.symbol "a") ∧
    ("y#1", "x#0") ∈ chainResolveBoundaryVisibleQueryBindings.equalities := by
  exact ⟨queryEquationsAgainstVisible_chainResolveBoundary, rfl, rfl, by simp [chainResolveBoundaryVisibleQueryBindings]⟩

private theorem chainResolveBoundary_queryBindings_no_loop :
    chainResolveBoundaryQueryBindings.hasLoop = false := by
  rfl

private theorem chainResolveBoundary_he_successor_unresolved :
    chainResolveBoundaryQueryBindings.apply (.var "x#0") 10 = .var "x#0" := by
  rfl

private theorem chainResolveBoundary_he_successor_full :
    chainResolveBoundaryQueryBindings.applyFull (.var "x#0") 10 = .symbol "a" := by
  decide

theorem equation_match_chainResolveBoundary_step :
    HESmallStep chainResolveBoundarySpace GroundedDispatch.none 10
      (.expression [.symbol "f", .var "y#1", .symbol "a"]) (.var "y#1") := by
  have hstep :
      HESmallStep chainResolveBoundarySpace GroundedDispatch.none 10
        (.expression [.symbol "f", .var "y#1", .symbol "a"])
        (chainResolveBoundaryVisibleQueryBindings.applyFull (.var "x#0") 10) := by
    apply HESmallStep.equation_match
    · simp [SpecialFormHead]
    · simp [HeadNotExecutable, GroundedDispatch.none]
    · decide
    · decide
  have preserved : chainResolveBoundaryVisibleQueryBindings.applyFull (.var "x#0") 10 =
      .var "y#1" := by decide
  simpa only [preserved] using hstep

private def chainResolveBoundaryQueryAtom : Metta.Atom :=
  encodeModelAtom (.expression [.symbol "f", .var "y#1", .symbol "a"])

private def chainResolveBoundaryQueryRule : Metta.Atom × Metta.Atom :=
  (encodeModelAtom (.expression [.symbol "f", .var "x", .var "y"]),
    encodeModelAtom (.var "x"))

private def chainResolveBoundaryQueryItemBindings : Metta.Bindings :=
  [ Metta.BindingRel.eq "x#0" "y#1"
  , Metta.BindingRel.val "y#0" (Metta.Atom.sym "a") ]

private theorem merge_empty_chainResolveBoundary_counter0 :
    Metta.Bindings.merge Metta.Bindings.empty
        [ Metta.BindingRel.val "y#0" (Metta.Atom.sym "a")
        , Metta.BindingRel.eq "x#0" "y#1" ] =
      [chainResolveBoundaryQueryItemBindings] := by
  rfl

private theorem chainResolveBoundary_resolve_x0 :
    Metta.Bindings.resolve chainResolveBoundaryQueryItemBindings "x#0" =
      some (Metta.Atom.var "y#1") := by
  apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolve_eq_representative_of_valueless_class
      (cls := ["y#1", "x#0"])
  · rfl
  · decide
  · rfl
  · rfl

private theorem chainResolveBoundary_resolve_y1 :
    Metta.Bindings.resolve chainResolveBoundaryQueryItemBindings "y#1" =
      some (Metta.Atom.var "y#1") := by
  apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolve_eq_representative_of_valueless_class
      (cls := ["y#1", "x#0"])
  · rfl
  · decide
  · rfl
  · rfl

private theorem chainResolveBoundary_resolve_y0 :
    Metta.Bindings.resolve chainResolveBoundaryQueryItemBindings "y#0" =
      some (Metta.Atom.sym "a") := by
  apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolve_eq_closed_class_value
    (cls := ["y#0"])
  · rfl
  · rfl
  · simp [Metta.Atom.vars]
  · simp [chainResolveBoundaryQueryItemBindings,
      Metta.Bindings.resolutionFuel, Metta.Bindings.relationResolutionFuel,
      Metta.Atom.size]

private theorem chainResolveBoundaryQueryItemBindings_hasLoop_false :
    Metta.Bindings.hasLoop chainResolveBoundaryQueryItemBindings = false := by
  apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.hasLoop_false_of_resolveAtomAux_some
  · rfl
  · intro x hx
    have hvars :
        Metta.Bindings.vars chainResolveBoundaryQueryItemBindings =
          ["x#0", "y#1", "y#0"] := by
      simp [Metta.Bindings.vars, chainResolveBoundaryQueryItemBindings,
        Metta.Atom.vars]
      decide
    rw [hvars] at hx
    simp at hx
    rcases hx with rfl | rfl | rfl
    · exact Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolveAtomAux_some_of_resolve_some
        chainResolveBoundary_resolve_x0
    · exact Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolveAtomAux_some_of_resolve_some
        chainResolveBoundary_resolve_y1
    · exact Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.resolveAtomAux_some_of_resolve_some
        chainResolveBoundary_resolve_y0

private theorem matchAtoms_chainResolveBoundary_counter0 :
    Metta.matchAtoms
        (Metta.Atom.expr
          [Metta.Atom.sym "f", Metta.Atom.var "x#0", Metta.Atom.var "y#0"])
        chainResolveBoundaryQueryAtom =
      [[ Metta.BindingRel.val "y#0" (Metta.Atom.sym "a")
       , Metta.BindingRel.eq "x#0" "y#1" ]] := by
  have heq :
      Metta.Bindings.merge []
          [Metta.BindingRel.eq "x#0" "y#1"] =
        [[Metta.BindingRel.eq "x#0" "y#1"]] := by
    exact merge_singleton_eq_eq_of_valueless_class
      (by decide)
      (Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.classValues_one_eq_eq_nil
        "x#0" "y#1" "x#0")
      (by simp)
  have hval :
      Metta.Bindings.merge
          [Metta.BindingRel.eq "x#0" "y#1"]
          [Metta.BindingRel.val "y#0" (Metta.Atom.sym "a")] =
        [[ Metta.BindingRel.val "y#0" (Metta.Atom.sym "a")
         , Metta.BindingRel.eq "x#0" "y#1" ]] := by
    exact merge_singleton_val_eq_of_fresh_class
      (Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.classValues_one_eq_eq_nil
        "x#0" "y#1" "y#0")
      (by intro y; simp)
      (by simp [bindingValueKeys])
  have hloop : Metta.Bindings.hasLoop
      [ Metta.BindingRel.val "y#0" (Metta.Atom.sym "a")
      , Metta.BindingRel.eq "x#0" "y#1" ] = false := by
    apply Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge.Bindings.hasLoop_false_of_resolveAtomAux_some
    · rfl
    · intro x hx
      have hvars : Metta.Bindings.vars
          [ Metta.BindingRel.val "y#0" (Metta.Atom.sym "a")
          , Metta.BindingRel.eq "x#0" "y#1" ] =
          ["y#0", "x#0", "y#1"] := by
        simp [Metta.Bindings.vars, Metta.Atom.vars, List.eraseDups_cons]
      rw [hvars] at hx
      simp at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨Metta.Atom.sym "a", by rfl⟩
      · exact ⟨Metta.Atom.var "y#1", by rfl⟩
      · exact ⟨Metta.Atom.var "y#1", by rfl⟩
  have heqLoop : Metta.Bindings.hasLoop
      [Metta.BindingRel.eq "x#0" "y#1"] = false :=
    Metta.Bindings.hasLoop_singleton_eq_of_ne _ _ (by decide)
  have hvalLoop : Metta.Bindings.hasLoop
      [Metta.BindingRel.val "y#0" (Metta.Atom.sym "a")] = false :=
    Metta.Bindings.hasLoop_singleton_val_of_not_mem _ _ (by simp [Metta.Atom.vars])
  simp [chainResolveBoundaryQueryAtom, encodeModelAtom, Metta.matchAtoms,
    Metta.matchAtomsWith, Metta.matchAll, heq, hval, hloop, heqLoop, hvalLoop]

private theorem instantiate_chainResolveBoundaryQueryItemBindings_x0 :
    Metta.instantiate chainResolveBoundaryQueryItemBindings
        (Metta.Atom.var "x#0") =
      Metta.Atom.var "y#1" := by
  simp [Metta.instantiate, Metta.Bindings.resolveAtom,
    chainResolveBoundary_resolve_x0]

private theorem queryOpItemsOfRule_chainResolveBoundary_counter0 :
    queryOpItemsOfRule [] chainResolveBoundaryQueryAtom Metta.Bindings.empty 0
      chainResolveBoundaryQueryRule =
        [Metta.Minimal.evalResult []
          (Metta.Atom.var "y#1") chainResolveBoundaryQueryItemBindings] := by
  have hfresh :
      Metta.Minimal.freshenRule 0
          chainResolveBoundaryQueryRule.1 chainResolveBoundaryQueryRule.2 =
        ( Metta.Atom.expr [Metta.Atom.sym "f", Metta.Atom.var "x#0", Metta.Atom.var "y#0"]
        , Metta.Atom.var "x#0") := by
    simp [chainResolveBoundaryQueryRule, encodeModelAtom, Metta.Minimal.freshenRule,
      Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup]
    decide
  have hmatch :
      Metta.matchAtoms
          (Metta.Atom.expr [Metta.Atom.sym "f", Metta.Atom.var "x#0", Metta.Atom.var "y#0"])
          chainResolveBoundaryQueryAtom =
        [[ Metta.BindingRel.val "y#0" (Metta.Atom.sym "a")
         , Metta.BindingRel.eq "x#0" "y#1" ]] := by
    exact matchAtoms_chainResolveBoundary_counter0
  have hmerge :
      Metta.Bindings.empty.merge
        [ Metta.BindingRel.val "y#0" (Metta.Atom.sym "a")
        , Metta.BindingRel.eq "x#0" "y#1" ] =
      [chainResolveBoundaryQueryItemBindings] := by
    exact merge_empty_chainResolveBoundary_counter0
  have hloop :
      Metta.Bindings.hasLoop chainResolveBoundaryQueryItemBindings = false := by
    exact chainResolveBoundaryQueryItemBindings_hasLoop_false
  have hcompat :
      Metta.Minimal.freshenRuleAvoiding 0
          (Metta.Minimal.queryOpAvoid [] chainResolveBoundaryQueryAtom Metta.Bindings.empty)
          chainResolveBoundaryQueryRule.1 chainResolveBoundaryQueryRule.2 =
        (Metta.Minimal.freshenRule 0 chainResolveBoundaryQueryRule.1
          chainResolveBoundaryQueryRule.2, 1) := by
    apply Metta.Minimal.freshenRuleAvoiding_eq_legacy
    rw [hfresh]
    simp [Metta.Minimal.queryOpAvoid, Metta.Bindings.empty, Metta.Bindings.vars,
      Metta.Minimal.liveStackVars, chainResolveBoundaryQueryAtom, encodeModelAtom,
      Metta.Atom.vars]
  unfold queryOpItemsOfRule Metta.Minimal.queryOpItemsOfRule
  rw [hcompat, hfresh]
  change
    List.flatMap
        (fun mb =>
          List.filterMap
            (fun m =>
              if m.hasLoop = true then none
              else some (Metta.Minimal.evalResult []
                (Metta.instantiate m (Metta.Atom.var "x#0")) m))
            (Metta.Bindings.empty.merge mb))
        (Metta.matchAtoms
          (Metta.Atom.expr
            [Metta.Atom.sym "f", Metta.Atom.var "x#0", Metta.Atom.var "y#0"])
          chainResolveBoundaryQueryAtom) =
      [Metta.Minimal.evalResult []
        (Metta.Atom.var "y#1") chainResolveBoundaryQueryItemBindings]
  rw [hmatch]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [hmerge]
  simp [hloop, instantiate_chainResolveBoundaryQueryItemBindings_x0,
    Metta.Minimal.evalResult, Metta.Minimal.finItem]

theorem chainResolveBoundary_no_visible_successor_counter0
    (gt : Metta.GroundingTable) :
    ¬ ∃ pre post emitted m,
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms chainResolveBoundarySpace.atoms) gt)
          Metta.Minimal.World.empty chainResolveBoundaryQueryAtom =
        pre ++ chainResolveBoundaryQueryRule :: post ∧
      Metta.Minimal.evalResult [] emitted m ∈
        queryOpItemsOfRule [] chainResolveBoundaryQueryAtom Metta.Bindings.empty
          (0 + pre.length) chainResolveBoundaryQueryRule ∧
      Metta.AlphaEq emitted (Metta.Atom.sym "a") := by
  intro hvis
  obtain ⟨pre, post, emitted, m, hsplit, hitem, halpha⟩ := hvis
  have hsingle :
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms chainResolveBoundarySpace.atoms) gt)
          Metta.Minimal.World.empty chainResolveBoundaryQueryAtom =
        [chainResolveBoundaryQueryRule] := by
    simp [chainResolveBoundarySpace, Space.ofList, chainResolveBoundaryQueryAtom,
      chainResolveBoundaryQueryRule, Metta.Minimal.candidatesW, Metta.Minimal.World.empty,
      Metta.Minimal.MinEnv.candidates, Metta.Minimal.headKey,
      Metta.Minimal.MinEnv.ofAtomsGT, Metta.Minimal.extractRules, encodeModelAtoms,
      encodeModelAtom]
  rw [hsingle] at hsplit
  have hpre_nil : pre = [] := by
    cases pre with
    | nil =>
        rfl
    | cons hd tl =>
        simp at hsplit
  subst hpre_nil
  have hpost_nil : post = [] := by
    simpa using hsplit
  subst hpost_nil
  have hitem0 :
      Metta.Minimal.evalResult [] emitted m ∈
        queryOpItemsOfRule [] chainResolveBoundaryQueryAtom Metta.Bindings.empty 0
          chainResolveBoundaryQueryRule := by
    simpa using hitem
  cases emitted with
  | sym s =>
      unfold Metta.AlphaEq Metta.canonicalizeVars at halpha
      simp [Metta.Atom.vars, Metta.distinctVarsAux, Metta.renameVars] at halpha
      subst halpha
      rw [queryOpItemsOfRule_chainResolveBoundary_counter0] at hitem0
      simp [Metta.Minimal.evalResult, Metta.Minimal.finItem,
        chainResolveBoundaryQueryItemBindings] at hitem0
  | var v =>
      unfold Metta.AlphaEq Metta.canonicalizeVars at halpha
      simp [Metta.Atom.vars, Metta.distinctVarsAux, Metta.renameVars] at halpha
  | gnd g =>
      unfold Metta.AlphaEq Metta.canonicalizeVars at halpha
      simp [Metta.Atom.vars, Metta.distinctVarsAux, Metta.renameVars] at halpha
  | expr xs =>
      unfold Metta.AlphaEq Metta.canonicalizeVars at halpha
      simp [Metta.Atom.vars, Metta.distinctVarsAux, Metta.renameVars] at halpha

private theorem noVarAssignmentValues_chainResolveBoundaryVisible :
    NoVarAssignmentValues chainResolveBoundaryVisibleQueryBindings := by
  intro v x hlookup
  have hlist :
      List.lookup v chainResolveBoundaryVisibleQueryBindings.assignments =
        some (.var x) := by
    simpa [Bindings.lookup] using hlookup
  have hmem : (v, Atom.var x) ∈
      chainResolveBoundaryVisibleQueryBindings.assignments :=
    lookup_some_mem_assignments hlist
  simp [chainResolveBoundaryVisibleQueryBindings] at hmem

private theorem assignmentsNodup_chainResolveBoundaryVisible :
    AssignmentsNodup chainResolveBoundaryVisibleQueryBindings := by
  simp [AssignmentsNodup, chainResolveBoundaryVisibleQueryBindings]

private theorem chainResolveBoundaryVisible_apply_x0 :
    chainResolveBoundaryVisibleQueryBindings.apply (.var "x#0") 10 = .var "x#0" := by
  rfl

private theorem chainResolveBoundaryVisible_applyFull_x0 :
    chainResolveBoundaryVisibleQueryBindings.applyFull (.var "x#0") 10 =
      .var "y#1" := by
  decide

private theorem queryOp_chainResolveBoundary_counter0_eq
    (gt : Metta.GroundingTable) :
    (Metta.Minimal.queryOp
        (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms chainResolveBoundarySpace.atoms) gt)
        { counter := 0, world := Metta.Minimal.World.empty }
        [] chainResolveBoundaryQueryAtom Metta.Bindings.empty).1 =
      [Metta.Minimal.evalResult []
        (Metta.Atom.var "y#1") chainResolveBoundaryQueryItemBindings] := by
  have hsingle :
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT
            (encodeModelAtoms chainResolveBoundarySpace.atoms) gt)
          Metta.Minimal.World.empty chainResolveBoundaryQueryAtom =
        [chainResolveBoundaryQueryRule] := by
    simp [chainResolveBoundarySpace, Space.ofList, chainResolveBoundaryQueryAtom,
      chainResolveBoundaryQueryRule, Metta.Minimal.candidatesW,
      Metta.Minimal.World.empty, Metta.Minimal.MinEnv.candidates,
      Metta.Minimal.headKey, Metta.Minimal.MinEnv.ofAtomsGT,
      Metta.Minimal.extractRules, encodeModelAtoms, encodeModelAtom]
  unfold Metta.Minimal.queryOp
  rw [show Metta.Minimal.isVariableHeaded chainResolveBoundaryQueryAtom = false by
    decide]
  rw [hsingle]
  simp only [List.foldl_cons, List.foldl_nil]
  simp only [Bool.false_eq_true]
  dsimp only [Metta.Minimal.queryOpFoldStep]
  have hitems :
      Metta.Minimal.queryOpItemsOfRule [] chainResolveBoundaryQueryAtom
          Metta.Bindings.empty 0 chainResolveBoundaryQueryRule =
        [Metta.Minimal.evalResult []
          (Metta.Atom.var "y#1") chainResolveBoundaryQueryItemBindings] := by
    exact queryOpItemsOfRule_chainResolveBoundary_counter0
  simp only [hitems, List.nil_append, List.isEmpty_cons, Bool.false_eq_true,
    if_false]

/-- The repaired visible-avoid equality-bearing boundary satisfies the
variable-successor local transport obligation: the candidate split is supplied
externally, and the proof discharges exactly LeaTTa's single-candidate
freshening, matching, merge, loop-filter, variable instantiation, and HE
variable successor. -/
theorem chainResolveBoundary_FreshenedVariableQueryOpItemTransportAgainstVisible_counter0
    (gt : Metta.GroundingTable) :
    FreshenedVariableQueryOpItemTransportAgainstVisible
      chainResolveBoundarySpace
      (.expression [.symbol "f", .var "y#1", .symbol "a"])
      (.var "x#0")
      chainResolveBoundaryVisibleQueryBindings 10 gt [] 0 := by
  intro idx lhs rawRhs pre post k _hk hzip _hmatch hsplit
  have hcase :
      (lhs = .expression [.symbol "f", .var "x", .var "y"] ∧
        rawRhs = .var "x") ∧
      idx = 0 := by
    simpa [chainResolveBoundarySpace, Space.ofList] using hzip
  rcases hcase with ⟨⟨rfl, rfl⟩, rfl⟩
  have hsingle :
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT
            (encodeModelAtoms chainResolveBoundarySpace.atoms) gt)
          Metta.Minimal.World.empty chainResolveBoundaryQueryAtom =
        [chainResolveBoundaryQueryRule] := by
    simp [chainResolveBoundarySpace, Space.ofList, chainResolveBoundaryQueryAtom,
      chainResolveBoundaryQueryRule, Metta.Minimal.candidatesW,
      Metta.Minimal.World.empty, Metta.Minimal.MinEnv.candidates,
      Metta.Minimal.headKey, Metta.Minimal.MinEnv.ofAtomsGT,
      Metta.Minimal.extractRules, encodeModelAtoms, encodeModelAtom]
  have hsingle' :
      Metta.Minimal.candidatesW
          (Metta.Minimal.MinEnv.ofAtomsGT
            (encodeModelAtoms chainResolveBoundarySpace.atoms) gt)
          Metta.Minimal.World.empty
          (encodeModelAtom
            (Atom.expression [Atom.symbol "f", Atom.var "y#1", Atom.symbol "a"])) =
        [(encodeModelAtom
            (Atom.expression [Atom.symbol "f", Atom.var "x", Atom.var "y"]),
          encodeModelAtom (Atom.var "x"))] := by
    simpa [chainResolveBoundaryQueryAtom, chainResolveBoundaryQueryRule] using hsingle
  rw [hsingle'] at hsplit
  have hpre_nil : pre = [] := by
    cases pre with
    | nil => rfl
    | cons hd tl => simp at hsplit
  subst hpre_nil
  have hpost_nil : post = [] := by
    simpa using hsplit
  subst hpost_nil
  have hcompat :
      Metta.Minimal.freshenRuleAvoiding 0
          (Metta.Minimal.queryOpAvoid [] chainResolveBoundaryQueryAtom Metta.Bindings.empty)
          chainResolveBoundaryQueryRule.1 chainResolveBoundaryQueryRule.2 =
        (Metta.Minimal.freshenRule 0 chainResolveBoundaryQueryRule.1
          chainResolveBoundaryQueryRule.2, 1) := by
    apply Metta.Minimal.freshenRuleAvoiding_eq_legacy
    have hfresh : Metta.Minimal.freshenRule 0 chainResolveBoundaryQueryRule.1
        chainResolveBoundaryQueryRule.2 =
        (Metta.Atom.expr [Metta.Atom.sym "f", Metta.Atom.var "x#0", Metta.Atom.var "y#0"],
          Metta.Atom.var "x#0") := by
      simp [chainResolveBoundaryQueryRule, encodeModelAtom, Metta.Minimal.freshenRule,
        Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup]
      decide
    rw [hfresh]
    simp [Metta.Minimal.queryOpAvoid, Metta.Bindings.empty, Metta.Bindings.vars,
      Metta.Minimal.liveStackVars, chainResolveBoundaryQueryAtom, encodeModelAtom,
      Metta.Atom.vars]
  refine
    ⟨Metta.Atom.expr
        [Metta.Atom.sym "f", Metta.Atom.var "x#0", Metta.Atom.var "y#0"],
      Metta.Atom.var "x#0",
      [ Metta.BindingRel.val "y#0" (Metta.Atom.sym "a")
      , Metta.BindingRel.eq "x#0" "y#1" ],
      chainResolveBoundaryQueryItemBindings,
      "y#1", "y#1", ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [List.length_nil, Nat.add_zero]
    have hfirst :
        (Metta.Minimal.freshenRuleAvoiding 0
          (Metta.Minimal.queryOpAvoid []
            (encodeModelAtom
              (Atom.expression [Atom.symbol "f", Atom.var "y#1", Atom.symbol "a"]))
            Metta.Bindings.empty)
          (encodeModelAtom
            (Atom.expression [Atom.symbol "f", Atom.var "x", Atom.var "y"]))
          (encodeModelAtom (Atom.var "x"))).1 =
        Metta.Minimal.freshenRule 0
          (encodeModelAtom
            (Atom.expression [Atom.symbol "f", Atom.var "x", Atom.var "y"]))
          (encodeModelAtom (Atom.var "x")) := by
      simpa only [chainResolveBoundaryQueryAtom, chainResolveBoundaryQueryRule] using
        congrArg Prod.fst hcompat
    rw [hfirst]
    simp [encodeModelAtom, Metta.Minimal.freshenRule,
      Metta.Atom.vars, Metta.Subst.apply, Metta.Subst.lookup]
    decide
  · change
      [ Metta.BindingRel.val "y#0" (Metta.Atom.sym "a")
      , Metta.BindingRel.eq "x#0" "y#1" ] ∈
        Metta.matchAtoms
          (Metta.Atom.expr
            [Metta.Atom.sym "f", Metta.Atom.var "x#0", Metta.Atom.var "y#0"])
          chainResolveBoundaryQueryAtom
    rw [matchAtoms_chainResolveBoundary_counter0]
    simp
  · rw [merge_empty_chainResolveBoundary_counter0]
    simp
  · exact chainResolveBoundaryQueryItemBindings_hasLoop_false
  · exact instantiate_chainResolveBoundaryQueryItemBindings_x0
  · exact chainResolveBoundaryVisible_applyFull_x0

/-- The repaired visible-avoid equality-bearing boundary satisfies the smaller
local freshened-item transport obligation by the variable-successor transport
specialization. -/
theorem chainResolveBoundary_FreshenedQueryOpItemTransportAgainstVisible_counter0
    (gt : Metta.GroundingTable) :
    FreshenedQueryOpItemTransportAgainstVisible
      chainResolveBoundarySpace
      (.expression [.symbol "f", .var "y#1", .symbol "a"])
      (.var "x#0")
      chainResolveBoundaryVisibleQueryBindings 10 gt [] 0 := by
  exact
    freshenedQueryOpItemTransportAgainstVisible_of_variable_item
      (chainResolveBoundary_FreshenedVariableQueryOpItemTransportAgainstVisible_counter0 gt)

/-- The repaired visible-avoid equality-bearing boundary is transportable at the
honest executable level: LeaTTa's matcher orients the HE equality as the emitted
variable `y#1`, and HE's equality-aware substitution selects the same class
representative. This is the positive counterpart to the assignment-only shortcut
failure below. -/
theorem chainResolveBoundary_EquationMatchVisibleItemTransportAgainst_counter0
    (gt : Metta.GroundingTable) :
    EquationMatchVisibleItemTransportAgainst
      chainResolveBoundarySpace
      (.expression [.symbol "f", .var "y#1", .symbol "a"])
      (.var "x#0")
      chainResolveBoundaryVisibleQueryBindings 10 gt [] 0 := by
  exact
    equationMatchVisibleItemTransportAgainst_of_freshened_item_transport
      (chainResolveBoundary_FreshenedQueryOpItemTransportAgainstVisible_counter0 gt)

/-- Complete observation package for the equality-bearing boundary on the repaired
visible query path. The old instantiated-item shortcut fails below, but the
alpha-visible executable transport path already observes the correct HE successor
for this concrete case. -/
theorem equation_match_chainResolveBoundary_againstVisible_queryOp_visible_successor_counter0
    (gt : Metta.GroundingTable) :
    LeaTTaVisibleEquationStepObservation
      chainResolveBoundarySpace GroundedDispatch.none 10
      (.expression [.symbol "f", .var "y#1", .symbol "a"]) (.var "y#1")
      gt [] 0 := by
  have hNotSpecial :
      ¬ SpecialFormHead (.expression [.symbol "f", .var "y#1", .symbol "a"]) := by
    simp [SpecialFormHead]
  have hNotGrounded :
      HeadNotExecutable GroundedDispatch.none
        (.expression [.symbol "f", .var "y#1", .symbol "a"]) := by
    simp [HeadNotExecutable, GroundedDispatch.none]
  have hk :
      Metta.Minimal.headKey
          (encodeModelAtom (.expression [.symbol "f", .var "y#1", .symbol "a"])) =
        some "f" := by
    simp [encodeModelAtom, Metta.Minimal.headKey]
  have hquery : (.var "x#0", chainResolveBoundaryVisibleQueryBindings) ∈
      queryEquationsAgainstVisible chainResolveBoundarySpace
        (.expression [.symbol "f", .var "y#1", .symbol "a"]) 10 := by
    simp [queryEquationsAgainstVisible_chainResolveBoundary]
  have hobs :
      LeaTTaVisibleEquationStepObservation
        chainResolveBoundarySpace GroundedDispatch.none 10
        (.expression [.symbol "f", .var "y#1", .symbol "a"])
        (chainResolveBoundaryVisibleQueryBindings.applyFull (.var "x#0") 10)
        gt [] 0 :=
    equation_match_againstVisible_observation_of_freshened_variable_item_transport
      (space := chainResolveBoundarySpace)
      (d := GroundedDispatch.none)
      (fuel := 10)
      (es := [.symbol "f", .var "y#1", .symbol "a"])
      (rhs := .var "x#0")
      (qb := chainResolveBoundaryVisibleQueryBindings)
      (gt := gt)
      (k := "f")
      (prev := [])
      (counter := 0)
      hNotSpecial
      hNotGrounded
      hk
      hquery
      (chainResolveBoundary_FreshenedVariableQueryOpItemTransportAgainstVisible_counter0 gt)
  simpa [chainResolveBoundaryVisible_applyFull_x0] using hobs

private theorem chainResolveBoundary_scoped_query :
    (.var "x#0", chainResolveBoundaryVisibleQueryBindings) ∈
      queryEquationsAvoiding ["y#1"] chainResolveBoundarySpace
        (.expression [.symbol "f", .var "y#1", .symbol "a"]) 10 := by
  decide

private theorem chainResolveBoundary_cover :
    CoversEvaluation ["y#1"] [] (.expression [.symbol "f", .var "y#1", .symbol "a"]) Atom.undefinedType Bindings.empty := by
  intro name h
  simp [equationScope, Atom.undefinedType, atomVariables, atomListVariables, Bindings.names, Bindings.empty] at h
  simp [h]

private theorem chainResolveBoundaryVisible_no_loop :
    chainResolveBoundaryVisibleQueryBindings.hasLoop = false := by
  rfl

/-- The equality-bearing chain boundary also reaches the official HE
`MettaCall` relation through the repaired visible-observation bridge. The
official rule renames the rule parameter `y` apart from the query's `y#1`, so the
call returns the caller's variable `y#1` with the visible binding record. The
equation-indexed spelling, which reused `y#1` and returned `a`, captured the
caller's variable and is not an official instance. -/
theorem chainResolveBoundary_visible_observation_models_mettaCall_counter0
    (gt : Metta.GroundingTable) :
    MettaCall chainResolveBoundarySpace GroundedDispatch.none
      (.expression [.symbol "f", .var "y#1", .symbol "a"])
      Atom.undefinedType Bindings.empty
      (.var "y#1", chainResolveBoundaryVisibleQueryBindings) := by
  have hobs :
      LeaTTaVisibleEquationStepObservation
        chainResolveBoundarySpace GroundedDispatch.none 10
        (.expression [.symbol "f", .var "y#1", .symbol "a"])
        (.var "y#1") gt [] 0 :=
    equation_match_chainResolveBoundary_againstVisible_queryOp_visible_successor_counter0 gt
  have hrecurse :
      EvalAtom chainResolveBoundarySpace GroundedDispatch.none
        (chainResolveBoundaryVisibleQueryBindings.applyFull (.var "x#0") 10)
        Atom.undefinedType chainResolveBoundaryVisibleQueryBindings
        (.var "y#1", chainResolveBoundaryVisibleQueryBindings) := by
    rw [chainResolveBoundaryVisible_applyFull_x0]
    exact EvalAtom.type_pass _ _ _ rfl (Or.inr (Or.inr rfl))
  exact
    leattaEquationMettaCallStep_sound
      (leattaEquationMettaCallStep_of_visible_observation_empty_input_result
        (space := chainResolveBoundarySpace)
        (d := GroundedDispatch.none)
        (fuel := 10)
        (src := .expression [.symbol "f", .var "y#1", .symbol "a"])
        (visibleDst := .var "y#1")
        (type_ := Atom.undefinedType)
        (rhs := .var "x#0")
        (qb := chainResolveBoundaryVisibleQueryBindings)
        (gt := gt)
        (prev := [])
        (counter := 0)
        hobs rfl (by simp [HeadNotExecutable, GroundedDispatch.none])
        chainResolveBoundary_cover chainResolveBoundary_scoped_query
        chainResolveBoundaryVisible_no_loop
        (OrdinaryCallReturnRel.of_eval
          (by rw [chainResolveBoundaryVisible_applyFull_x0]; decide) hrecurse))

/-- Step-shaped public package for the equality-bearing chain boundary.  The
statement expands the private fixture definitions so downstream conformance
readouts can use the artifact without depending on private names. -/
theorem chainResolveBoundary_leattaEquationMettaCallStep_counter0 :
    LeaTTaEquationMettaCallStep
      (Space.ofList
        [.expression
          [.symbol "=",
            .expression [.symbol "f", .var "x", .var "y"],
            .var "x"]])
      GroundedDispatch.none 10
      (.expression [.symbol "f", .var "y#1", .symbol "a"])
      Atom.undefinedType Bindings.empty
      (.var "y#1",
        ({ assignments := [("y#2", .symbol "a")]
         , equalities := [("y#1", "x#0")] } : Bindings)) := by
  have hobs :
      LeaTTaVisibleEquationStepObservation
        chainResolveBoundarySpace GroundedDispatch.none 10
        (.expression [.symbol "f", .var "y#1", .symbol "a"])
        (.var "y#1") (default : Metta.GroundingTable) [] 0 :=
    equation_match_chainResolveBoundary_againstVisible_queryOp_visible_successor_counter0
      (default : Metta.GroundingTable)
  have hrecurse :
      EvalAtom chainResolveBoundarySpace GroundedDispatch.none
        (chainResolveBoundaryVisibleQueryBindings.applyFull (.var "x#0") 10)
        Atom.undefinedType chainResolveBoundaryVisibleQueryBindings
        (.var "y#1", chainResolveBoundaryVisibleQueryBindings) := by
    rw [chainResolveBoundaryVisible_applyFull_x0]
    exact EvalAtom.type_pass _ _ _ rfl (Or.inr (Or.inr rfl))
  have hstep :
      LeaTTaEquationMettaCallStep
        chainResolveBoundarySpace GroundedDispatch.none 10
        (.expression [.symbol "f", .var "y#1", .symbol "a"])
        Atom.undefinedType Bindings.empty
        (.var "y#1", chainResolveBoundaryVisibleQueryBindings) :=
    leattaEquationMettaCallStep_of_visible_observation_empty_input_result
      (space := chainResolveBoundarySpace)
      (d := GroundedDispatch.none)
      (fuel := 10)
      (src := .expression [.symbol "f", .var "y#1", .symbol "a"])
      (visibleDst := .var "y#1")
      (type_ := Atom.undefinedType)
      (rhs := .var "x#0")
      (qb := chainResolveBoundaryVisibleQueryBindings)
      (gt := (default : Metta.GroundingTable))
      (prev := [])
      (counter := 0)
      hobs rfl (by simp [HeadNotExecutable, GroundedDispatch.none])
      chainResolveBoundary_cover chainResolveBoundary_scoped_query
      chainResolveBoundaryVisible_no_loop
        (OrdinaryCallReturnRel.of_eval
          (by rw [chainResolveBoundaryVisible_applyFull_x0]; decide) hrecurse)
  simpa [chainResolveBoundarySpace, chainResolveBoundaryVisibleQueryBindings] using hstep

private theorem chainResolveBoundary_expected_instantiated_item_not_queryOp_counter0
    (gt : Metta.GroundingTable) :
    Metta.Minimal.evalResult []
        (Metta.instantiate
          (toLeaTTaMatchBindings chainResolveBoundaryVisibleQueryBindings)
          (encodeModelAtom (.var "x#0")))
        (toLeaTTaMatchBindings chainResolveBoundaryVisibleQueryBindings) ∉
      (Metta.Minimal.queryOp
        (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms chainResolveBoundarySpace.atoms) gt)
        { counter := 0, world := Metta.Minimal.World.empty }
        [] chainResolveBoundaryQueryAtom Metta.Bindings.empty).1 := by
  have htranslated :
      toLeaTTaMatchBindings chainResolveBoundaryVisibleQueryBindings =
        [Metta.BindingRel.val "y#2" (Metta.Atom.sym "a")] := by
    rfl
  have hinst :
      Metta.instantiate
          (toLeaTTaMatchBindings chainResolveBoundaryVisibleQueryBindings)
          (encodeModelAtom (.var "x#0")) =
        Metta.Atom.var "x#0" := by
    rw [htranslated]
    simpa [encodeModelAtom] using
      (Metta.instantiate_singleton_val_inert
        "y#2" (Metta.Atom.sym "a") (Metta.Atom.var "x#0")
        (by simp [Metta.Atom.vars]))
  rw [queryOp_chainResolveBoundary_counter0_eq gt]
  simp only [List.mem_singleton]
  rw [hinst, htranslated]
  simp [chainResolveBoundaryQueryItemBindings, Metta.Minimal.evalResult,
    Metta.Minimal.finItem]

/-- The instantiated-RHS shortcut used by
`leattaEquationMettaCallStep_of_instantiated_item_againstVisible_empty_input`
is not enough for every repaired HE visible-query hit.  There is a concrete
query whose HE match is loop-free, assignment-key unique, and has no
variable-valued assignments, but whose equality constraint is lost by the
current assignment-only projection into LeaTTa match bindings; the expected
instantiated item is therefore absent from `queryOp`.

This theorem is a limitation boundary, not a conformance result.  It marks the
next bridge obligation: either transport equality constraints explicitly or
state the exact fragment where they are unnecessary. -/
theorem exists_visible_query_hit_not_carried_by_instantiated_item_shortcut :
    ∃ (space : Space) (src rhs : Atom) (qb : Bindings)
      (fuel counter : Nat) (gt : Metta.GroundingTable),
      (rhs, qb) ∈ queryEquationsAgainstVisible space src fuel ∧
      NoVarAssignmentValues qb ∧
      AssignmentsNodup qb ∧
      atomDepth rhs + 2 ≤ fuel ∧
      Metta.Minimal.evalResult []
          (Metta.instantiate (toLeaTTaMatchBindings qb) (encodeModelAtom rhs))
          (toLeaTTaMatchBindings qb) ∉
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT (encodeModelAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          [] (encodeModelAtom src) Metta.Bindings.empty).1 := by
  refine
    ⟨chainResolveBoundarySpace,
      .expression [.symbol "f", .var "y#1", .symbol "a"],
      .var "x#0",
      chainResolveBoundaryVisibleQueryBindings,
      10, 0, (default : Metta.GroundingTable), ?_, ?_, ?_, ?_, ?_⟩
  · simp [queryEquationsAgainstVisible_chainResolveBoundary]
  · exact noVarAssignmentValues_chainResolveBoundaryVisible
  · exact assignmentsNodup_chainResolveBoundaryVisible
  · decide
  · simpa [chainResolveBoundaryQueryAtom] using
      chainResolveBoundary_expected_instantiated_item_not_queryOp_counter0
        (default : Metta.GroundingTable)

end Mettapedia.Languages.MeTTa.HE.LeaTTaBridge

/-! # HE conformance consumers of the step bridges above

The engine fragments and observation theorems below instantiate the
engine-parametric boundary of `Conformance` with the step relations of this
module. -/

namespace Mettapedia.Languages.MeTTa.HE.Conformance

open Mettapedia.Languages.MeTTa.OSLFCore (Atom GroundedValue)
open Mettapedia.Languages.MeTTa.HE
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.RuntimeCorrectness
open Mettapedia.Languages.MeTTa.LeaTTa.EvaluatorCorrectness.QueryOpBridge

/-! ### LeaTTa equation-call fragment hook

This is not a complete LeaTTa engine instance.  It exposes the exact local
`mettaCall_sound` obligation discharged by the equation-call bridge in
`LeaTTaBridge`: any future engine whose call-step relation refines that
step-shaped fragment already satisfies the corresponding declarative HE
`MettaCall` obligation. -/

theorem leattaEquationFragment_mettaCall_sound
    (engine : HEOperationalEngine)
    (h_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaBridge.LeaTTaEquationMettaCallStep
            space dispatch fuel atom type_ b r) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r := by
  intro space dispatch atom type_ b fuel r hstep
  exact LeaTTaBridge.leattaEquationMettaCallStep_sound
    (h_refines space dispatch atom type_ b fuel r hstep)

/-- Assemble a full `HEEngineBridge` from explicit non-LeaTTa obligations plus
the proven LeaTTa equation-call fragment for `mettaCallStep`.

This theorem is deliberately obligation-preserving: it does not manufacture a
LeaTTa engine, and it does not claim the equation fragment covers all possible
runtimes unless the caller proves that their engine's `mettaCallStep` relation
really refines `LeaTTaEquationMettaCallStep`. -/
theorem engine_bridge_of_leattaEquationFragment_mettaCall
    (engine : HEOperationalEngine)
    (h_eval :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.evalAtomStep space dispatch atom type_ b fuel r →
          EvalAtom space dispatch atom type_ b r)
    (h_metta_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaBridge.LeaTTaEquationMettaCallStep
            space dispatch fuel atom type_ b r) :
    HEEngineBridge engine where
  evalAtom_sound := h_eval
  mettaCall_sound := leattaEquationFragment_mettaCall_sound engine h_metta_refines

/-- Engine-parametric declarative HE model theorem for any engine whose
`mettaCallStep` interface is proven to refine the LeaTTa equation-call fragment,
with the remaining engine obligations supplied explicitly. -/
theorem engine_models_declarative_he_of_leattaEquationFragment_mettaCall
    (engine : HEOperationalEngine)
    (h_eval :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.evalAtomStep space dispatch atom type_ b fuel r →
          EvalAtom space dispatch atom type_ b r)
    (h_metta_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaBridge.LeaTTaEquationMettaCallStep
            space dispatch fuel atom type_ b r) :
    HEEngineModelsDeclarativeSpec engine :=
  engine_parametric_he_refinement engine
    (engine_bridge_of_leattaEquationFragment_mettaCall
      engine h_eval h_metta_refines)

/-- The currently proved LeaTTa-backed HE engine instance for the equation-call
fragment.  It is intentionally not named as a complete LeaTTa runtime: the
`mettaCallStep` field is exactly the observed equation-call fragment from
`LeaTTaBridge`, while the `evalAtomStep` field exposes the already-declarative
HE eval interface needed by the shared refinement theorem. -/
def leattaEquationFragmentEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b _fuel r =>
    EvalAtom space dispatch atom type_ b r
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    LeaTTaBridge.LeaTTaEquationMettaCallStep
      space dispatch fuel atom type_ b r

theorem leattaEquationFragmentEngine_bridge :
    HEEngineBridge leattaEquationFragmentEngine :=
  engine_bridge_of_leattaEquationFragment_mettaCall
    leattaEquationFragmentEngine
    (by
      intro space dispatch atom type_ b fuel r hstep
      simpa [leattaEquationFragmentEngine] using hstep)
    (by
      intro space dispatch atom type_ b fuel r hstep
      simpa [leattaEquationFragmentEngine] using hstep)

theorem leattaEquationFragmentEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec leattaEquationFragmentEngine :=
  engine_parametric_he_refinement
    leattaEquationFragmentEngine leattaEquationFragmentEngine_bridge

/-! ### LeaTTa equation/no-match fragment hook

The next honest widening adds the non-ground no-match branch.  It is still a
fragment instance, not a full LeaTTa engine: the executable side contributes
LeaTTa `queryOp` observations for equation hits or `NotReducible`, while the
official HE query premises remain explicit. -/

theorem leattaEquationNoMatchFragment_mettaCall_sound
    (engine : HEOperationalEngine)
    (h_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaBridge.LeaTTaEquationNoMatchMettaCallStep
            space dispatch fuel atom type_ b r) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r := by
  intro space dispatch atom type_ b fuel r hstep
  exact LeaTTaBridge.leattaEquationNoMatchMettaCallStep_sound
    (h_refines space dispatch atom type_ b fuel r hstep)

def leattaEquationNoMatchFragmentEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b _fuel r =>
    EvalAtom space dispatch atom type_ b r
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    LeaTTaBridge.LeaTTaEquationNoMatchMettaCallStep
      space dispatch fuel atom type_ b r

theorem leattaEquationNoMatchFragmentEngine_bridge :
    HEEngineBridge leattaEquationNoMatchFragmentEngine where
  evalAtom_sound := by
    intro space dispatch atom type_ b fuel r hstep
    simpa [leattaEquationNoMatchFragmentEngine] using hstep
  mettaCall_sound := by
    intro space dispatch atom type_ b fuel r hstep
    exact LeaTTaBridge.leattaEquationNoMatchMettaCallStep_sound hstep

theorem leattaEquationNoMatchFragmentEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec leattaEquationNoMatchFragmentEngine :=
  engine_parametric_he_refinement
    leattaEquationNoMatchFragmentEngine
    leattaEquationNoMatchFragmentEngine_bridge

/-- Concrete positive readout for the widened fragment: the empty-space
symbol-headed no-match executable observation satisfies official HE
`MettaCall.no_match` through the engine-parametric call interface. -/
theorem emptySpace_foo_equationNoMatchFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty
      (.expression [.symbol "foo"], Bindings.empty) :=
  leattaEquationNoMatchFragmentEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty 10
    (.expression [.symbol "foo"], Bindings.empty)
    LeaTTaBridge.emptySpace_foo_equationNoMatchMettaCallStep_counter0

/-! ### LeaTTa query/unify fragment hook

This widening adds the primitive `unify` raw success/fallback lane to the
already-proved equation/no-match query fragment. -/

theorem leattaQueryUnifyFragment_mettaCall_sound
    (engine : HEOperationalEngine)
    (h_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaBridge.LeaTTaQueryUnifyMettaCallStep
            space dispatch fuel atom type_ b r) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r := by
  intro space dispatch atom type_ b fuel r hstep
  exact LeaTTaBridge.leattaQueryUnifyMettaCallStep_sound
    (h_refines space dispatch atom type_ b fuel r hstep)

def leattaQueryUnifyFragmentEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b _fuel r =>
    EvalAtom space dispatch atom type_ b r
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    LeaTTaBridge.LeaTTaQueryUnifyMettaCallStep
      space dispatch fuel atom type_ b r

theorem leattaQueryUnifyFragmentEngine_bridge :
    HEEngineBridge leattaQueryUnifyFragmentEngine where
  evalAtom_sound := by
    intro space dispatch atom type_ b fuel r hstep
    simpa [leattaQueryUnifyFragmentEngine] using hstep
  mettaCall_sound := by
    intro space dispatch atom type_ b fuel r hstep
    exact LeaTTaBridge.leattaQueryUnifyMettaCallStep_sound hstep

theorem leattaQueryUnifyFragmentEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec leattaQueryUnifyFragmentEngine :=
  engine_parametric_he_refinement
    leattaQueryUnifyFragmentEngine
    leattaQueryUnifyFragmentEngine_bridge

/-- Concrete positive readout for the primitive `unify` fallback lane: a
symbol mismatch in LeaTTa `unifyOp` and the official HE raw fallback premise
produce the declarative HE `MettaCall.unify_no_match_raw` result. -/
theorem emptySpace_unifySymbolMismatch_queryUnifyFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "unify", .symbol "a", .symbol "b",
        .symbol "then", .symbol "else"])
      Atom.undefinedType Bindings.empty
      (.symbol "else", Bindings.empty) :=
  leattaQueryUnifyFragmentEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "unify", .symbol "a", .symbol "b",
      .symbol "then", .symbol "else"])
    Atom.undefinedType Bindings.empty 10
    (.symbol "else", Bindings.empty)
    LeaTTaBridge.emptySpace_unifySymbolMismatch_queryUnifyMettaCallStep_counter0

/-- General positive readout for the primitive `unify` success lane on the
ground-target/variable-pattern fragment. The executable LeaTTa singleton
match/merge evidence is derived by `LeaTTaBridge` from `GroundAtom target`; the
declarative conclusion is the official HE `MettaCall` result. -/
theorem groundTarget_unifyVar_queryUnifyFragment_models_mettaCall
    {space : Space} {d : GroundedDispatch}
    {target thenBranch elseBranch type_ : Atom} {v : String}
    (hground : GroundAtom target) :
    MettaCall space d
      (.expression [.symbol "unify", target, .var v, thenBranch, elseBranch])
      type_ Bindings.empty
      ((Bindings.empty.assign v target).applyDefault thenBranch,
        Bindings.empty.assign v target) :=
  leattaQueryUnifyFragmentEngine_models_declarative_he.mettaCall_models
    space d
    (.expression [.symbol "unify", target, .var v, thenBranch, elseBranch])
    type_ Bindings.empty 10
    ((Bindings.empty.assign v target).applyDefault thenBranch,
      Bindings.empty.assign v target)
    (Or.inr <|
      LeaTTaBridge.leattaUnifyMettaCallStep_success_ground_var_empty_seed
        (space := space) (d := d) (n := 9)
        (target := target) (v := v) (thenBranch := thenBranch)
        (elseBranch := elseBranch) (type_ := type_)
        hground)

/-- Concrete positive readout for the primitive `unify` success lane: matching
`a` against `$x` returns the success branch `$x` instantiated to `a`, with the
official HE match binding carried through the query/unify fragment engine. -/
theorem emptySpace_unifyVarSymbol_queryUnifyFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "unify", .symbol "a", .var "x",
        .var "x", .symbol "else"])
      Atom.undefinedType Bindings.empty
      (.symbol "a", Bindings.empty.assign "x" (.symbol "a")) :=
  groundTarget_unifyVar_queryUnifyFragment_models_mettaCall
      (space := Space.empty) (d := GroundedDispatch.none)
      (target := .symbol "a") (v := "x") (thenBranch := .var "x")
      (elseBranch := .symbol "else") (type_ := Atom.undefinedType)
      (GroundAtom.symbol "a")

/-! ### LeaTTa query/unify fragment with extensional primitive bindings

This sibling fragment keeps the same engine-parametric refinement interface, but
uses the lookup-extensional executable observation for primitive `unify`. -/

theorem leattaQueryUnifyFragmentExt_mettaCall_sound
    (engine : HEOperationalEngine)
    (h_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaBridge.LeaTTaQueryUnifyMettaCallStepExt
            space dispatch fuel atom type_ b r) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r := by
  intro space dispatch atom type_ b fuel r hstep
  exact LeaTTaBridge.leattaQueryUnifyMettaCallStepExt_sound
    (h_refines space dispatch atom type_ b fuel r hstep)

def leattaQueryUnifyFragmentExtEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b _fuel r =>
    EvalAtom space dispatch atom type_ b r
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    LeaTTaBridge.LeaTTaQueryUnifyMettaCallStepExt
      space dispatch fuel atom type_ b r

theorem leattaQueryUnifyFragmentExtEngine_bridge :
    HEEngineBridge leattaQueryUnifyFragmentExtEngine where
  evalAtom_sound := by
    intro space dispatch atom type_ b fuel r hstep
    simpa [leattaQueryUnifyFragmentExtEngine] using hstep
  mettaCall_sound := by
    intro space dispatch atom type_ b fuel r hstep
    exact LeaTTaBridge.leattaQueryUnifyMettaCallStepExt_sound hstep

theorem leattaQueryUnifyFragmentExtEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec leattaQueryUnifyFragmentExtEngine :=
  engine_parametric_he_refinement
    leattaQueryUnifyFragmentExtEngine
    leattaQueryUnifyFragmentExtEngine_bridge

/-- Concrete positive readout for the non-empty-seed primitive `unify` lane:
LeaTTa's runtime merge order differs from the official HE raw result order,
but the emitted binding set is direct-lookup equivalent, so the shared
engine-parametric refinement still yields the exact HE `MettaCall`. -/
theorem seededUnifyOrder_queryUnifyFragmentExt_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "unify", .symbol "a", .var "x",
        .var "x", .symbol "else"])
      Atom.undefinedType LeaTTaBridge.seededUnifyOrderSeed
      (.symbol "a", LeaTTaBridge.seededUnifyOrderHEMerged) :=
  leattaQueryUnifyFragmentExtEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "unify", .symbol "a", .var "x",
      .var "x", .symbol "else"])
    Atom.undefinedType LeaTTaBridge.seededUnifyOrderSeed 10
    (.symbol "a", LeaTTaBridge.seededUnifyOrderHEMerged)
    LeaTTaBridge.seededUnifyOrder_queryUnifyMettaCallStepExt_counter0

/-- Conformance-facing schema for the equality-aware visible equation bridge.
The executable side supplies a repaired LeaTTa visible observation; the
declarative side remains the official HE `queryEquations`/`mergeBindings`/
ordinary-call return premise bundle. This is the bridge shape needed for
equality-bearing matches that cannot pass through the assignment-only
instantiated-RHS shortcut. -/
theorem leattaVisibleEquationObservation_models_mettaCall
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src dst type_ rhs : Atom}
    {queryBindings inputBindings merged outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat}
    (hobs :
      LeaTTaBridge.LeaTTaVisibleEquationStepObservation
        space d fuel src dst gt prev counter)
    (h_not_error : isErrorAtom src = false)
    (h_not_grounded : HeadNotExecutable d src)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] src type_ inputBindings)
    (h_query_public : (rhs, queryBindings) ∈
      queryEquationsAvoiding avoid space src fuel)
    (h_merge : merged ∈ mergeBindings queryBindings inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d src (merged.applyFull rhs fuel) type_ merged
        (dst, outputBindings)) :
    MettaCall space d src type_ inputBindings (dst, outputBindings) := by
  exact
    (LeaTTaBridge.observedMettaCall_of_equation_match
      (space := space)
      (d := d)
      (fuel := fuel)
      (src := src)
      (dst := dst)
      (type_ := type_)
      (rhs := rhs)
      (queryBindings := queryBindings)
      (inputBindings := inputBindings)
      (merged := merged)
      (outputBindings := outputBindings)
      (gt := gt)
      (prev := prev)
      (counter := counter)
      hobs h_not_error h_not_grounded h_cover h_query_public h_merge
      h_no_loop h_recurse).2

/-- Conformance-facing schema for the repaired visible-avoid transport path.
This is the equality-aware counterpart of the instantiated-RHS fragment below:
once the public HE query witness, visible HE query witness, avoid-aware LeaTTa
transport, and `OrdinaryCallReturnRel` premise are supplied, the official
declarative HE `MettaCall` result follows. -/
theorem leattaTransportAgainstVisible_models_mettaCall
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom} {qb outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey
      (Spec.Match.SolutionTheory.encodeModelAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ Bindings.empty)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (htransport : LeaTTaBridge.EquationMatchVisibleItemTransportAgainst
      space (.expression es) rhs qb fuel gt prev counter)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (qb.applyFull rhs fuel) type_ qb
        (qb.applyFull rhs fuel, outputBindings)) :
  MettaCall space d (.expression es) type_ Bindings.empty
      (qb.applyFull rhs fuel, outputBindings) := by
  exact
    LeaTTaBridge.leattaEquationMettaCallStep_sound
      (LeaTTaBridge.leattaEquationMettaCallStep_of_transport_againstVisible_empty_input
        (space := space)
        (d := d)
        (fuel := fuel)
        (es := es)
        (rhs := rhs)
        (type_ := type_)
        (qb := qb)
        (outputBindings := outputBindings)
        (gt := gt)
        (prev := prev)
        (counter := counter)
        (k := k)
        h_not_special h_not_error h_not_grounded hk h_query_visible
        h_cover h_query_public htransport h_recurse)

/-- Binding-threaded conformance schema for the repaired visible-avoid
transport path. This removes the empty-input restriction from
`leattaTransportAgainstVisible_models_mettaCall` while keeping the exact HE
merge, loop, and ordinary-call return premises visible. The result atom is
still the visible equation successor observed by LeaTTa. -/
theorem leattaTransportAgainstVisibleWithMerge_models_mettaCall
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey
      (Spec.Match.SolutionTheory.encodeModelAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ inputBindings)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (htransport : LeaTTaBridge.EquationMatchVisibleItemTransportAgainst
      space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (merged.applyFull rhs fuel) type_ merged
        (qb.applyFull rhs fuel, outputBindings)) :
  MettaCall space d (.expression es) type_ inputBindings
      (qb.applyFull rhs fuel, outputBindings) := by
  exact
    LeaTTaBridge.leattaEquationMettaCallStep_sound
      (LeaTTaBridge.leattaEquationMettaCallStep_of_transport_againstVisible_with_merge
        (space := space)
        (d := d)
        (fuel := fuel)
        (es := es)
        (rhs := rhs)
        (type_ := type_)
        (qb := qb)
        (inputBindings := inputBindings)
        (merged := merged)
        (outputBindings := outputBindings)
        (gt := gt)
        (prev := prev)
        (counter := counter)
        (k := k)
        h_not_special h_not_error h_not_grounded hk h_query_visible
        h_cover h_query_public htransport h_merge h_no_loop h_recurse)

/-- Continuation-aware conformance schema for an equality-aware visible LeaTTa
observation.  The executable observation records the immediate equation
successor, while the official HE `MettaCall` result is exactly the result of
the `OrdinaryCallReturnRel` premise. -/
theorem leattaVisibleEquationObservation_models_mettaCall_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {src visibleDst type_ rhs : Atom}
    {queryBindings inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {finalResult : ResultPair}
    (hobs :
      LeaTTaBridge.LeaTTaVisibleEquationStepObservation
        space d fuel src visibleDst gt prev counter)
    (h_not_error : isErrorAtom src = false)
    (h_not_grounded : HeadNotExecutable d src)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] src type_ inputBindings)
    (h_query_public : (rhs, queryBindings) ∈
      queryEquationsAvoiding avoid space src fuel)
    (h_merge : merged ∈ mergeBindings queryBindings inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d src (merged.applyFull rhs fuel) type_ merged finalResult) :
  MettaCall space d src type_ inputBindings finalResult := by
  exact
    LeaTTaBridge.leattaEquationMettaCallStep_sound
      (LeaTTaBridge.leattaEquationMettaCallStep_of_visible_observation_with_merge_final
        (space := space)
        (d := d)
        (fuel := fuel)
        (src := src)
        (visibleDst := visibleDst)
        (type_ := type_)
        (rhs := rhs)
        (queryBindings := queryBindings)
        (inputBindings := inputBindings)
        (merged := merged)
        (gt := gt)
        (prev := prev)
        (counter := counter)
        (finalResult := finalResult)
        hobs h_not_error h_not_grounded h_cover h_query_public h_merge
        h_no_loop h_recurse)

/-- Continuation-aware conformance schema for the repaired visible-avoid
transport path. This is the version needed by the full equation-call rule: the
visible LeaTTa `queryOp` item only has to agree with the immediate HE equation
successor, not with the recursive final result. -/
theorem leattaTransportAgainstVisibleWithMerge_models_mettaCall_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey
      (Spec.Match.SolutionTheory.encodeModelAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ inputBindings)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (htransport : LeaTTaBridge.EquationMatchVisibleItemTransportAgainst
      space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (merged.applyFull rhs fuel) type_ merged finalResult) :
  MettaCall space d (.expression es) type_ inputBindings finalResult := by
  exact
    LeaTTaBridge.leattaEquationMettaCallStep_sound
      (LeaTTaBridge.leattaEquationMettaCallStep_of_transport_againstVisible_with_merge_final
        (space := space)
        (d := d)
        (fuel := fuel)
        (es := es)
        (rhs := rhs)
        (type_ := type_)
        (qb := qb)
        (inputBindings := inputBindings)
        (merged := merged)
        (gt := gt)
        (prev := prev)
        (counter := counter)
        (k := k)
        (finalResult := finalResult)
        h_not_special h_not_error h_not_grounded hk h_query_visible
        h_cover h_query_public htransport h_merge h_no_loop h_recurse)

/-- Conformance schema for the concrete executable `queryOp` hit boundary.
Unlike the transport-based schema, this theorem consumes the runtime evidence
directly: a LeaTTa `queryOp` item alpha-equivalent to the immediate HE visible
equation successor. -/
theorem leattaQueryOpHitAgainstVisibleWithMerge_models_mettaCall_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ inputBindings)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (hhit :
      LeaTTaBridge.LeaTTaEquationQueryOpHit
        space fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (merged.applyFull rhs fuel) type_ merged finalResult) :
  MettaCall space d (.expression es) type_ inputBindings finalResult := by
  exact
    LeaTTaBridge.leattaEquationMettaCallStep_sound
      (LeaTTaBridge.leattaEquationMettaCallStep_of_queryOp_hit_againstVisible_with_merge_final
        (space := space)
        (d := d)
        (fuel := fuel)
        (es := es)
        (rhs := rhs)
        (type_ := type_)
        (qb := qb)
        (inputBindings := inputBindings)
        (merged := merged)
        (gt := gt)
        (prev := prev)
        (counter := counter)
        (finalResult := finalResult)
        h_not_special h_not_error h_not_grounded h_query_visible
        h_cover h_query_public hhit h_merge h_no_loop h_recurse)

/-- Query-match-aware version of the concrete executable `queryOp` boundary.
In addition to the official HE `MettaCall`, this packages the public and
visible query hits with their dedicated HE `MatchRel` witnesses.  The result
keeps the executable observation and the declarative query evidence together,
which is the shape the engine-parametric conformance theorem needs. -/
theorem leattaQueryOpHitAgainstVisibleWithMerge_models_mettaCall_final_with_queryMatchRel
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ inputBindings)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (hhit :
      LeaTTaBridge.LeaTTaEquationQueryOpHit
        space fuel (.expression es) (qb.applyFull rhs fuel) gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (merged.applyFull rhs fuel) type_ merged finalResult) :
    MettaCall space d (.expression es) type_ inputBindings finalResult ∧
    (∃ lhs rhs0 idx,
      (.expression [.symbol "=", lhs, rhs0], idx) ∈ space.atoms.zipIdx ∧
      rhs = (freshenEquationAvoiding avoid idx lhs rhs0).2 ∧
      DeclMatchSpec.MatchRel
        (.expression es) (freshenEquationAvoiding avoid idx lhs rhs0).1 qb) ∧
    (∃ lhs rhs0 idx,
      (.expression [.symbol "=", lhs, rhs0], idx) ∈ space.atoms.zipIdx ∧
      rhs =
        (freshenEquationAgainst
          (collectVars (.expression es) fuel).eraseDups idx lhs rhs0 fuel).2 ∧
      DeclMatchSpec.MatchRel
        (.expression es)
        (freshenEquationAgainst
          (collectVars (.expression es) fuel).eraseDups idx lhs rhs0 fuel).1
        qb) := by
  refine ⟨?_, ?_, ?_⟩
  · exact
      leattaQueryOpHitAgainstVisibleWithMerge_models_mettaCall_final
        (space := space)
        (d := d)
        (fuel := fuel)
        (es := es)
        (rhs := rhs)
        (type_ := type_)
        (qb := qb)
        (inputBindings := inputBindings)
        (merged := merged)
        (gt := gt)
        (prev := prev)
        (counter := counter)
        (finalResult := finalResult)
        h_not_special h_not_error h_not_grounded h_query_visible
        h_cover h_query_public hhit h_merge h_no_loop h_recurse
  · exact queryEquationsAvoiding_hits_are_declarative_matches h_query_public
  · exact queryEquationsAgainstVisible_hits_are_declarative_matches h_query_visible

/-! ### LeaTTa repaired query/extensional-unify fragment

This is the widest currently proved call fragment that keeps the repaired
equation-query path explicit: `Error` passthrough is carried by the HE
source rule and checked against LeaTTa's executable translation above,
equation hits must come through the visible `matchAtoms`-backed query evidence
above, no-match stays the official empty public-query branch, and primitive
`unify` uses the lookup-extensional executable binding observation from
`LeaTTaBridge`. -/

def LeaTTaRepairedQueryUnifyExtMettaCallStep
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (atom type_ : Atom) (inputBindings : Bindings)
    (result : ResultPair) : Prop :=
  LeaTTaErrorPassthroughMettaCallStep
      space d fuel atom type_ inputBindings result ∨
  LeaTTaVisibleEquationQueryOpMettaCallStep
      space d fuel atom type_ inputBindings result ∨
  LeaTTaBridge.LeaTTaNoMatchMettaCallStep
      space d fuel atom type_ inputBindings result ∨
  LeaTTaBridge.LeaTTaUnifyMettaCallStepExt
      space d fuel atom type_ inputBindings result

theorem leattaRepairedQueryUnifyExtMettaCallStep_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {atom type_ : Atom} {inputBindings : Bindings}
    {result : ResultPair}
    (hstep :
      LeaTTaRepairedQueryUnifyExtMettaCallStep
        space d fuel atom type_ inputBindings result) :
    MettaCall space d atom type_ inputBindings result := by
  rcases hstep with herr | hrest
  · exact leattaErrorPassthroughMettaCallStep_sound herr
  rcases hrest with hvisible | hrest
  · exact leattaVisibleEquationQueryOpMettaCallStep_sound hvisible
  rcases hrest with hno | hunify
  · exact LeaTTaBridge.leattaNoMatchMettaCallStep_sound hno
  · exact LeaTTaBridge.leattaUnifyMettaCallStepExt_sound hunify

/-- Any engine whose call interface refines the repaired LeaTTa-backed
error/query/no-match/extensional-`unify` fragment satisfies the corresponding
declarative HE `MettaCall` obligation. -/
theorem leattaRepairedQueryUnifyExtFragment_mettaCall_sound
    (engine : HEOperationalEngine)
    (h_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaRepairedQueryUnifyExtMettaCallStep
            space dispatch fuel atom type_ b r) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r := by
  intro space dispatch atom type_ b fuel r hstep
  exact leattaRepairedQueryUnifyExtMettaCallStep_sound
    (h_refines space dispatch atom type_ b fuel r hstep)

/-- Assemble a full engine bridge from explicit non-call obligations plus a
proof that the engine's call interface refines the repaired LeaTTa-backed
error/query/no-match/extensional-`unify` fragment. -/
theorem engine_bridge_of_leattaRepairedQueryUnifyExtFragment_mettaCall
    (engine : HEOperationalEngine)
    (h_eval :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.evalAtomStep space dispatch atom type_ b fuel r →
          EvalAtom space dispatch atom type_ b r)
    (h_metta_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaRepairedQueryUnifyExtMettaCallStep
            space dispatch fuel atom type_ b r) :
    HEEngineBridge engine where
  evalAtom_sound := h_eval
  mettaCall_sound :=
    leattaRepairedQueryUnifyExtFragment_mettaCall_sound engine h_metta_refines

/-- Engine-parametric declarative HE model theorem for any engine whose
`mettaCallStep` interface is proven to refine the repaired LeaTTa-backed
error/query/no-match/extensional-`unify` fragment. -/
theorem engine_models_declarative_he_of_leattaRepairedQueryUnifyExtFragment_mettaCall
    (engine : HEOperationalEngine)
    (h_eval :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.evalAtomStep space dispatch atom type_ b fuel r →
          EvalAtom space dispatch atom type_ b r)
    (h_metta_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaRepairedQueryUnifyExtMettaCallStep
            space dispatch fuel atom type_ b r) :
    HEEngineModelsDeclarativeSpec engine :=
  engine_parametric_he_refinement engine
    (engine_bridge_of_leattaRepairedQueryUnifyExtFragment_mettaCall
      engine h_eval h_metta_refines)

def leattaRepairedQueryUnifyExtFragmentEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b _fuel r =>
    EvalAtom space dispatch atom type_ b r
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    LeaTTaRepairedQueryUnifyExtMettaCallStep
      space dispatch fuel atom type_ b r

theorem leattaRepairedQueryUnifyExtFragmentEngine_bridge :
    HEEngineBridge leattaRepairedQueryUnifyExtFragmentEngine where
  evalAtom_sound := by
    intro space dispatch atom type_ b fuel r hstep
    simpa [leattaRepairedQueryUnifyExtFragmentEngine] using hstep
  mettaCall_sound := by
    intro space dispatch atom type_ b fuel r hstep
    exact leattaRepairedQueryUnifyExtMettaCallStep_sound hstep

theorem leattaRepairedQueryUnifyExtFragmentEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec leattaRepairedQueryUnifyExtFragmentEngine :=
  engine_parametric_he_refinement
    leattaRepairedQueryUnifyExtFragmentEngine
    leattaRepairedQueryUnifyExtFragmentEngine_bridge

/-- Concrete no-match readout through the repaired query/extensional-unify
fragment. -/
theorem emptySpace_foo_repairedQueryUnifyExtFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty
      (.expression [.symbol "foo"], Bindings.empty) :=
  leattaRepairedQueryUnifyExtFragmentEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty 10
    (.expression [.symbol "foo"], Bindings.empty)
    (Or.inr (Or.inr
      (Or.inl LeaTTaBridge.emptySpace_foo_noMatchMettaCallStep_counter0)))

/-- Concrete extensional-`unify` readout through the repaired
query/extensional-unify fragment. -/
theorem seededUnifyOrder_repairedQueryUnifyExtFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "unify", .symbol "a", .var "x",
        .var "x", .symbol "else"])
      Atom.undefinedType LeaTTaBridge.seededUnifyOrderSeed
      (.symbol "a", LeaTTaBridge.seededUnifyOrderHEMerged) :=
  leattaRepairedQueryUnifyExtFragmentEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "unify", .symbol "a", .var "x",
      .var "x", .symbol "else"])
    Atom.undefinedType LeaTTaBridge.seededUnifyOrderSeed 10
    (.symbol "a", LeaTTaBridge.seededUnifyOrderHEMerged)
    (Or.inr (Or.inr (Or.inr
      LeaTTaBridge.seededUnifyOrder_leattaUnifyMettaCallStepExt_counter0)))

/-- Concrete `Error` passthrough through the repaired query/extensional-unify
fragment, paired with the executable LeaTTa minimal readout for the translated
atom. -/
theorem leatta_minimal_error_passthrough_repairedQueryUnifyExtFragment_models_mettaCall :
    Metta.Minimal.mettaEval (Metta.Minimal.MinEnv.ofAtomsGT [] []) 4
      Metta.Minimal.St.init [] leattaErrorPassthroughAtom =
        ([(leattaErrorPassthroughAtom, [])], Metta.Minimal.St.init) ∧
    MettaCall Space.empty GroundedDispatch.none
      (Atom.error (.symbol "x") (.symbol "e")) Atom.undefinedType Bindings.empty
      (Atom.error (.symbol "x") (.symbol "e"), Bindings.empty) := by
  constructor
  · exact leatta_minimal_error_passthrough_mettaEval
  · exact
      leattaRepairedQueryUnifyExtFragmentEngine_models_declarative_he.mettaCall_models
        Space.empty GroundedDispatch.none
        (Atom.error (.symbol "x") (.symbol "e")) Atom.undefinedType Bindings.empty 10
        (Atom.error (.symbol "x") (.symbol "e"), Bindings.empty)
        (Or.inl
          ⟨.symbol "x", .symbol "e", rfl, rfl,
            leatta_error_passthrough_atom_is_HE_error_translation⟩)

/-! ### Repaired query/unify fragment plus malformed-`unify` interface

This super-fragment keeps the repaired query/extensional-`unify` bridge intact
and adds the subject-side malformed-`unify` observation repaired above. -/

def LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
    (space : Space) (d : GroundedDispatch) (fuel : Nat)
    (atom type_ : Atom) (inputBindings : Bindings)
    (result : ResultPair) : Prop :=
  LeaTTaRepairedQueryUnifyExtMettaCallStep
    space d fuel atom type_ inputBindings result ∨
  LeaTTaUnifyBadArityMettaCallStep
    space d fuel atom type_ inputBindings result ∨
  LeaTTaBridge.LeaTTaEquationMettaCallStep
    space d fuel atom type_ inputBindings result

theorem leattaRepairedQueryUnifyExtBadArityMettaCallStep_sound
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {atom type_ : Atom} {inputBindings : Bindings}
    {result : ResultPair}
    (hstep :
      LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
        space d fuel atom type_ inputBindings result) :
    MettaCall space d atom type_ inputBindings result := by
  rcases hstep with hbase | hrest
  · exact leattaRepairedQueryUnifyExtMettaCallStep_sound hbase
  rcases hrest with hbad | heq
  · exact leattaUnifyBadArityMettaCallStep_sound hbad
  · exact LeaTTaBridge.leattaEquationMettaCallStep_sound heq

/-- Any engine whose call interface refines the repaired query/extensional-`unify`
fragment plus the malformed-`unify` executable observation satisfies the
corresponding declarative HE `MettaCall` obligation. -/
theorem leattaRepairedQueryUnifyExtBadArityFragment_mettaCall_sound
    (engine : HEOperationalEngine)
    (h_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
            space dispatch fuel atom type_ b r) :
    ∀ (space : Space) (dispatch : GroundedDispatch)
      (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
      engine.mettaCallStep space dispatch atom type_ b fuel r →
        MettaCall space dispatch atom type_ b r := by
  intro space dispatch atom type_ b fuel r hstep
  exact leattaRepairedQueryUnifyExtBadArityMettaCallStep_sound
    (h_refines space dispatch atom type_ b fuel r hstep)

theorem engine_bridge_of_leattaRepairedQueryUnifyExtBadArityFragment_mettaCall
    (engine : HEOperationalEngine)
    (h_eval :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.evalAtomStep space dispatch atom type_ b fuel r →
          EvalAtom space dispatch atom type_ b r)
    (h_metta_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
            space dispatch fuel atom type_ b r) :
    HEEngineBridge engine where
  evalAtom_sound := h_eval
  mettaCall_sound :=
    leattaRepairedQueryUnifyExtBadArityFragment_mettaCall_sound
      engine h_metta_refines

theorem engine_models_declarative_he_of_leattaRepairedQueryUnifyExtBadArityFragment_mettaCall
    (engine : HEOperationalEngine)
    (h_eval :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.evalAtomStep space dispatch atom type_ b fuel r →
          EvalAtom space dispatch atom type_ b r)
    (h_metta_refines :
      ∀ (space : Space) (dispatch : GroundedDispatch)
        (atom type_ : Atom) (b : Bindings) (fuel : Nat) (r : ResultPair),
        engine.mettaCallStep space dispatch atom type_ b fuel r →
          LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
            space dispatch fuel atom type_ b r) :
    HEEngineModelsDeclarativeSpec engine :=
  engine_parametric_he_refinement engine
    (engine_bridge_of_leattaRepairedQueryUnifyExtBadArityFragment_mettaCall
      engine h_eval h_metta_refines)

def leattaRepairedQueryUnifyExtBadArityFragmentEngine : HEOperationalEngine where
  evalAtomStep := fun space dispatch atom type_ b _fuel r =>
    EvalAtom space dispatch atom type_ b r
  mettaCallStep := fun space dispatch atom type_ b fuel r =>
    LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
      space dispatch fuel atom type_ b r

theorem leattaRepairedQueryUnifyExtBadArityFragmentEngine_bridge :
    HEEngineBridge leattaRepairedQueryUnifyExtBadArityFragmentEngine where
  evalAtom_sound := by
    intro space dispatch atom type_ b fuel r hstep
    simpa [leattaRepairedQueryUnifyExtBadArityFragmentEngine] using hstep
  mettaCall_sound := by
    intro space dispatch atom type_ b fuel r hstep
    exact leattaRepairedQueryUnifyExtBadArityMettaCallStep_sound hstep

theorem leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he :
    HEEngineModelsDeclarativeSpec
      leattaRepairedQueryUnifyExtBadArityFragmentEngine :=
  engine_parametric_he_refinement
    leattaRepairedQueryUnifyExtBadArityFragmentEngine
    leattaRepairedQueryUnifyExtBadArityFragmentEngine_bridge

/-- The bad-arity-inclusive repaired fragment subsumes the previous repaired
query/extensional-`unify` fragment. -/
theorem leattaRepairedQueryUnifyExt_step_subsumed_by_badArityFragment
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {atom type_ : Atom} {inputBindings : Bindings}
    {result : ResultPair}
    (hstep :
      LeaTTaRepairedQueryUnifyExtMettaCallStep
        space d fuel atom type_ inputBindings result) :
    LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
        space d fuel atom type_ inputBindings result :=
  Or.inl hstep

/-- The bad-arity-inclusive repaired fragment also subsumes the general
LeaTTa equation-call step.  This is the migration path away from the separate
equation fragment engine. -/
theorem leattaEquationStep_subsumed_by_badArityFragment
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {atom type_ : Atom} {inputBindings : Bindings}
    {result : ResultPair}
    (hstep :
      LeaTTaBridge.LeaTTaEquationMettaCallStep
        space d fuel atom type_ inputBindings result) :
    LeaTTaRepairedQueryUnifyExtBadArityMettaCallStep
        space d fuel atom type_ inputBindings result :=
  Or.inr (Or.inr hstep)

/-- The older repaired fragment engine is justified through the stronger
bad-arity-inclusive bridge, giving a migration path for downstream readouts
while fragment engines are consolidated. -/
theorem leattaRepairedQueryUnifyExtFragmentEngine_models_declarative_he_via_badArityFragment :
    HEEngineModelsDeclarativeSpec leattaRepairedQueryUnifyExtFragmentEngine :=
  engine_models_declarative_he_of_leattaRepairedQueryUnifyExtBadArityFragment_mettaCall
    leattaRepairedQueryUnifyExtFragmentEngine
    (by
      intro space dispatch atom type_ b fuel r hstep
      simpa [leattaRepairedQueryUnifyExtFragmentEngine] using hstep)
    (by
      intro space dispatch atom type_ b fuel r hstep
      exact
        leattaRepairedQueryUnifyExt_step_subsumed_by_badArityFragment
          (by
            simpa [leattaRepairedQueryUnifyExtFragmentEngine] using hstep))

/-- The older equation fragment engine is justified through the stronger
bad-arity-inclusive bridge. -/
theorem leattaEquationFragmentEngine_models_declarative_he_via_badArityFragment :
    HEEngineModelsDeclarativeSpec leattaEquationFragmentEngine :=
  engine_models_declarative_he_of_leattaRepairedQueryUnifyExtBadArityFragment_mettaCall
    leattaEquationFragmentEngine
    (by
      intro space dispatch atom type_ b fuel r hstep
      simpa [leattaEquationFragmentEngine] using hstep)
    (by
      intro space dispatch atom type_ b fuel r hstep
      exact
        leattaEquationStep_subsumed_by_badArityFragment
          (by
            simpa [leattaEquationFragmentEngine] using hstep))

/-- Concrete no-match readout through the bad-arity-inclusive repaired
fragment. -/
theorem emptySpace_foo_repairedQueryUnifyExtBadArityFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty
      (.expression [.symbol "foo"], Bindings.empty) :=
  leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "foo"]) Atom.undefinedType Bindings.empty 10
    (.expression [.symbol "foo"], Bindings.empty)
    (Or.inl (Or.inr (Or.inr
      (Or.inl LeaTTaBridge.emptySpace_foo_noMatchMettaCallStep_counter0))))

/-- Concrete extensional-`unify` readout through the bad-arity-inclusive
repaired fragment. -/
theorem seededUnifyOrder_repairedQueryUnifyExtBadArityFragment_models_mettaCall :
    MettaCall Space.empty GroundedDispatch.none
      (.expression [.symbol "unify", .symbol "a", .var "x",
        .var "x", .symbol "else"])
      Atom.undefinedType LeaTTaBridge.seededUnifyOrderSeed
      (.symbol "a", LeaTTaBridge.seededUnifyOrderHEMerged) :=
  leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
    Space.empty GroundedDispatch.none
    (.expression [.symbol "unify", .symbol "a", .var "x",
      .var "x", .symbol "else"])
    Atom.undefinedType LeaTTaBridge.seededUnifyOrderSeed 10
    (.symbol "a", LeaTTaBridge.seededUnifyOrderHEMerged)
    (Or.inl (Or.inr (Or.inr (Or.inr
      LeaTTaBridge.seededUnifyOrder_leattaUnifyMettaCallStepExt_counter0))))

/-- Concrete `Error` passthrough through the bad-arity-inclusive repaired
fragment, paired with the executable LeaTTa minimal readout for the translated
atom. -/
theorem leatta_minimal_error_passthrough_repairedQueryUnifyExtBadArityFragment_models_mettaCall :
    Metta.Minimal.mettaEval (Metta.Minimal.MinEnv.ofAtomsGT [] []) 4
      Metta.Minimal.St.init [] leattaErrorPassthroughAtom =
        ([(leattaErrorPassthroughAtom, [])], Metta.Minimal.St.init) ∧
    MettaCall Space.empty GroundedDispatch.none
      (Atom.error (.symbol "x") (.symbol "e")) Atom.undefinedType Bindings.empty
      (Atom.error (.symbol "x") (.symbol "e"), Bindings.empty) := by
  constructor
  · exact leatta_minimal_error_passthrough_mettaEval
  · exact
      leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
        Space.empty GroundedDispatch.none
        (Atom.error (.symbol "x") (.symbol "e")) Atom.undefinedType Bindings.empty 10
        (Atom.error (.symbol "x") (.symbol "e"), Bindings.empty)
        (Or.inl (Or.inl
          ⟨.symbol "x", .symbol "e", rfl, rfl,
            leatta_error_passthrough_atom_is_HE_error_translation⟩))

/-- Concrete equality-bearing chain-resolution readout through the
bad-arity-inclusive repaired fragment, subsuming the older equation-fragment
readout. -/
theorem chainResolveBoundary_badArityFragment_models_mettaCall_counter0 :
    MettaCall
      (Space.ofList
        [.expression
          [.symbol "=",
            .expression [.symbol "f", .var "x", .var "y"],
            .var "x"]])
      GroundedDispatch.none
      (.expression [.symbol "f", .var "y#1", .symbol "a"])
      Atom.undefinedType Bindings.empty
      (.var "y#1",
        ({ assignments := [("y#2", .symbol "a")]
         , equalities := [("y#1", "x#0")] } : Bindings)) :=
  leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
    (Space.ofList
      [.expression
        [.symbol "=",
          .expression [.symbol "f", .var "x", .var "y"],
          .var "x"]])
    GroundedDispatch.none
    (.expression [.symbol "f", .var "y#1", .symbol "a"])
    Atom.undefinedType Bindings.empty 10
    (.var "y#1",
      ({ assignments := [("y#2", .symbol "a")]
       , equalities := [("y#1", "x#0")] } : Bindings))
    (leattaEquationStep_subsumed_by_badArityFragment
      LeaTTaBridge.chainResolveBoundary_leattaEquationMettaCallStep_counter0)

/-- Concrete malformed-`unify` readout through the repaired fragment extended
with the bad-arity subject observation. -/
theorem leatta_minimal_unify_bad_arity_repairedQueryUnifyExtBadArityFragment_models_mettaCall :
    Metta.Minimal.evalAtomMin
        (Metta.Minimal.MinEnv.ofAtomsGT [] []) 4
        leattaBadUnifyThreeArgs =
      [Spec.Match.SolutionTheory.encodeModelAtom
        (mkUnifyBadArityError heBadUnifyThreeArgs)] ∧
    MettaCall Space.empty GroundedDispatch.none
      heBadUnifyThreeArgs Atom.undefinedType Bindings.empty
      (mkUnifyBadArityError heBadUnifyThreeArgs, Bindings.empty) := by
  constructor
  · exact leatta_minimal_unify_bad_arity_matches_HE_bad_arity_interface.1
  · exact
      leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
        Space.empty GroundedDispatch.none
        heBadUnifyThreeArgs Atom.undefinedType Bindings.empty 4
        (mkUnifyBadArityError heBadUnifyThreeArgs, Bindings.empty)
        (Or.inr
          (Or.inl
            leattaBadUnifyThreeArgs_unifyBadArityMettaCallStep_counter4))

/-- Transport-backed conformance through the concrete `queryOp` hit boundary.
This theorem makes explicit that the older avoid-aware transport certificate is
now only one way to produce the executable hit consumed by the smaller bridge. -/
theorem leattaTransportAgainstVisibleWithMerge_models_mettaCall_final_via_queryOpHit
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey
      (Spec.Match.SolutionTheory.encodeModelAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ inputBindings)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (htransport : LeaTTaBridge.EquationMatchVisibleItemTransportAgainst
      space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (merged.applyFull rhs fuel) type_ merged finalResult) :
    MettaCall space d (.expression es) type_ inputBindings finalResult := by
  exact
    leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
      space d (.expression es) type_ inputBindings fuel finalResult
      (leattaEquationStep_subsumed_by_badArityFragment
        (LeaTTaBridge.leattaEquationMettaCallStep_of_transport_againstVisible_with_merge_final
          (space := space)
          (d := d)
          (fuel := fuel)
          (es := es)
          (rhs := rhs)
          (type_ := type_)
          (qb := qb)
          (inputBindings := inputBindings)
          (merged := merged)
          (gt := gt)
          (prev := prev)
          (counter := counter)
          (k := k)
          (finalResult := finalResult)
          h_not_special h_not_error h_not_grounded hk h_query_visible
          h_cover h_query_public htransport h_merge h_no_loop h_recurse))

/-- Conformance schema through the smaller local freshened-item transport
boundary. Candidate selection is discharged from the HE visible query witness;
the supplied obligation is only the single-candidate LeaTTa freshening,
matching, merge, loop-filter, instantiation, and alpha-agreement step. -/
theorem leattaFreshenedItemTransportAgainstVisibleWithMerge_models_mettaCall_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey
      (Spec.Match.SolutionTheory.encodeModelAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ inputBindings)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (hitemTransport :
      LeaTTaBridge.FreshenedQueryOpItemTransportAgainstVisible
        space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (merged.applyFull rhs fuel) type_ merged finalResult) :
    MettaCall space d (.expression es) type_ inputBindings finalResult := by
  exact
    leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
      space d (.expression es) type_ inputBindings fuel finalResult
      (leattaEquationStep_subsumed_by_badArityFragment
        (LeaTTaBridge.leattaEquationMettaCallStep_of_freshened_item_transport_againstVisible_with_merge_final
          (space := space)
          (d := d)
          (fuel := fuel)
          (es := es)
          (rhs := rhs)
          (type_ := type_)
          (qb := qb)
          (inputBindings := inputBindings)
          (merged := merged)
          (gt := gt)
          (prev := prev)
          (counter := counter)
          (k := k)
          (finalResult := finalResult)
          h_not_special h_not_error h_not_grounded hk h_query_visible
          h_cover h_query_public hitemTransport h_merge h_no_loop h_recurse))

/-- Variable-successor specialization of the freshened-item conformance schema.
The caller proves only that the executable local item emits a variable and the
HE visible successor is a variable; the bridge supplies the alpha-equivalence
needed by the official `MettaCall` conclusion. -/
theorem leattaFreshenedVariableItemTransportAgainstVisibleWithMerge_models_mettaCall_final
    {space : Space} {d : GroundedDispatch} {fuel : Nat}
    {es : List Atom} {rhs type_ : Atom}
    {qb inputBindings merged : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat} {k : String} {finalResult : ResultPair}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (hk : Metta.Minimal.headKey
      (Spec.Match.SolutionTheory.encodeModelAtom (.expression es)) = some k)
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) fuel)
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ inputBindings)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) fuel)
    (hvarTransport :
      LeaTTaBridge.FreshenedVariableQueryOpItemTransportAgainstVisible
        space (.expression es) rhs qb fuel gt prev counter)
    (h_merge : merged ∈ mergeBindings qb inputBindings fuel)
    (h_no_loop : merged.hasLoop = false)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (merged.applyFull rhs fuel) type_ merged finalResult) :
    MettaCall space d (.expression es) type_ inputBindings finalResult := by
  exact
    leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
      space d (.expression es) type_ inputBindings fuel finalResult
      (leattaEquationStep_subsumed_by_badArityFragment
        (LeaTTaBridge.leattaEquationMettaCallStep_of_freshened_variable_item_transport_againstVisible_with_merge_final
          (space := space)
          (d := d)
          (fuel := fuel)
          (es := es)
          (rhs := rhs)
          (type_ := type_)
          (qb := qb)
          (inputBindings := inputBindings)
          (merged := merged)
          (gt := gt)
          (prev := prev)
          (counter := counter)
          (k := k)
          (finalResult := finalResult)
          h_not_special h_not_error h_not_grounded hk h_query_visible
          h_cover h_query_public hvarTransport h_merge h_no_loop h_recurse))

/-- Concrete equality-bearing query readout through the engine-parametric
LeaTTa equation fragment.  This is the repaired path for the chain-resolution
boundary where HE's visible query interface preserves an equality relation that
the assignment-only instantiated-item shortcut cannot carry. -/
theorem chainResolveBoundary_equationFragment_models_mettaCall_counter0 :
    MettaCall
      (Space.ofList
        [.expression
          [.symbol "=",
            .expression [.symbol "f", .var "x", .var "y"],
            .var "x"]])
      GroundedDispatch.none
      (.expression [.symbol "f", .var "y#1", .symbol "a"])
      Atom.undefinedType Bindings.empty
      (.var "y#1",
        ({ assignments := [("y#2", .symbol "a")]
         , equalities := [("y#1", "x#0")] } : Bindings)) :=
  chainResolveBoundary_badArityFragment_models_mettaCall_counter0

/-- Negative companion for the equality-bearing query boundary: there is a
faithful visible-query hit whose expected instantiated item is absent from the
assignment-only shortcut's `queryOp` target. -/
theorem equalityBearing_query_hit_not_carried_by_instantiated_item_shortcut :
    ∃ (space : Space) (src rhs : Atom) (qb : Bindings)
      (fuel counter : Nat) (gt : Metta.GroundingTable),
      (rhs, qb) ∈ queryEquationsAgainstVisible space src fuel ∧
      Spec.Match.SolutionTheory.NoVarAssignmentValues qb ∧
      Spec.Match.SolutionTheory.AssignmentsNodup qb ∧
      BindingComposition.atomDepth rhs + 2 ≤ fuel ∧
      Metta.Minimal.evalResult []
          (Metta.instantiate (LeaTTaBridge.toLeaTTaMatchBindings qb)
            (Spec.Match.SolutionTheory.encodeModelAtom rhs))
          (LeaTTaBridge.toLeaTTaMatchBindings qb) ∉
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT
            (Spec.Match.SolutionTheory.encodeModelAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          [] (Spec.Match.SolutionTheory.encodeModelAtom src) Metta.Bindings.empty).1 :=
  LeaTTaBridge.exists_visible_query_hit_not_carried_by_instantiated_item_shortcut

/-- Generic conformance schema for the no-variable-values instantiated-RHS
equation fragment.  It exposes the reusable bridge behind the unary-identity
fixture: once the repaired visible query, public HE query, LeaTTa `queryOp` item,
and `OrdinaryCallReturnRel` premise are supplied, the official declarative HE
`MettaCall` result follows. -/
theorem leattaInstantiatedEquationFragment_models_mettaCall
    {space : Space} {d : GroundedDispatch} {n : Nat}
    {es : List Atom} {rhs type_ : Atom} {qb outputBindings : Bindings}
    {gt : Metta.GroundingTable} {prev : Metta.Minimal.Stack}
    {counter : Nat}
    (h_not_special : ¬ SpecialFormHead (.expression es))
    (h_not_error : isErrorAtom (.expression es) = false)
    (h_not_grounded : HeadNotExecutable d (.expression es))
    (h_query_visible : (rhs, qb) ∈
      queryEquationsAgainstVisible space (.expression es) (n + 1))
    {avoid : List String}
    (h_cover : CoversEvaluation avoid [] (.expression es) type_ Bindings.empty)
    (h_query_public : (rhs, qb) ∈
      queryEquationsAvoiding avoid space (.expression es) (n + 1))
    (heq : qb.equalities = [])
    (hfresh : ValueKeysFreshForValues (LeaTTaBridge.toLeaTTaMatchBindings qb))
    (hdepth : BindingComposition.atomDepth rhs + 2 ≤ n + 1)
    (hitem :
      Metta.Minimal.evalResult prev
          (Metta.instantiate (LeaTTaBridge.toLeaTTaMatchBindings qb)
            (Spec.Match.SolutionTheory.encodeModelAtom rhs))
          (LeaTTaBridge.toLeaTTaMatchBindings qb) ∈
        (Metta.Minimal.queryOp
          (Metta.Minimal.MinEnv.ofAtomsGT
            (Spec.Match.SolutionTheory.encodeModelAtoms space.atoms) gt)
          { counter := counter, world := Metta.Minimal.World.empty }
          prev (Spec.Match.SolutionTheory.encodeModelAtom (.expression es))
          Metta.Bindings.empty).1)
    (h_recurse :
      OrdinaryCallReturnRel space d (.expression es) (qb.applyFull rhs (n + 1)) type_ qb
        (qb.applyFull rhs (n + 1), outputBindings)) :
    MettaCall space d (.expression es) type_ Bindings.empty
      (qb.applyFull rhs (n + 1), outputBindings) := by
  exact
    leattaRepairedQueryUnifyExtBadArityFragmentEngine_models_declarative_he.mettaCall_models
      space d (.expression es) type_ Bindings.empty (n + 1)
      (qb.applyFull rhs (n + 1), outputBindings)
      (leattaEquationStep_subsumed_by_badArityFragment
        (LeaTTaBridge.leattaEquationMettaCallStep_of_instantiated_item_againstVisible_empty_input
          (space := space) (d := d) (n := n) (es := es)
          (rhs := rhs) (type_ := type_) (qb := qb)
          (outputBindings := outputBindings) (gt := gt) (prev := prev)
          (counter := counter)
          h_not_special h_not_error h_not_grounded h_query_visible
          h_cover h_query_public heq hfresh
          hdepth hitem h_recurse))

/-- Conformance-facing positive fixture for the LeaTTa equation-call fragment:
the arbitrary unary-identity non-ground assignment witness satisfies the
official HE `MettaCall` rule through the step-shaped bridge hook. -/
theorem leattaUnaryIdentityFragment_models_mettaCall
    (head var value : String)
    (h_not_special :
      ¬ SpecialFormHead (.expression [.symbol head, .symbol value]))
    (h_not_error :
      isErrorAtom (.expression [.symbol head, .symbol value]) = false)
    (h_recurse :
      OrdinaryCallReturnRel (LeaTTaBridge.unaryIdentitySpace head var) GroundedDispatch.none
        (.expression [.symbol head, .symbol value]) (.symbol value) Atom.undefinedType
        (LeaTTaBridge.unaryIdentityBindings var value)
        (.symbol value, LeaTTaBridge.unaryIdentityBindings var value)) :
    MettaCall (LeaTTaBridge.unaryIdentitySpace head var) GroundedDispatch.none
      (.expression [.symbol head, .symbol value]) Atom.undefinedType
      Bindings.empty (.symbol value, LeaTTaBridge.unaryIdentityBindings var value) := by
  have heq :
      (LeaTTaBridge.unaryIdentityBindings var value).equalities = [] := by
    simp [LeaTTaBridge.unaryIdentityBindings, Bindings.assign, Bindings.empty]
  have hfull :
      (LeaTTaBridge.unaryIdentityBindings var value).applyFull
          (.var (LeaTTaBridge.unaryIdentityFresh0 var)) 10 =
        .symbol value := by
    rw [Bindings.applyFull_no_equalities heq]
    simp [Bindings.apply, Bindings.resolve, Bindings.resolveAtomAux,
      Bindings.hasAssignedVar, LeaTTaBridge.unaryIdentityBindings,
      LeaTTaBridge.unaryIdentityFresh0, Bindings.assign, Bindings.isBound,
      Bindings.empty, Bindings.lookup]
  simpa [hfull] using
    (leattaInstantiatedEquationFragment_models_mettaCall
      (space := LeaTTaBridge.unaryIdentitySpace head var)
      (d := GroundedDispatch.none)
      (n := 9)
      (es := [.symbol head, .symbol value])
      (rhs := .var (LeaTTaBridge.unaryIdentityFresh0 var))
      (type_ := Atom.undefinedType)
      (qb := LeaTTaBridge.unaryIdentityBindings var value)
      (outputBindings := LeaTTaBridge.unaryIdentityBindings var value)
      (gt := (default : Metta.GroundingTable))
      (prev := [])
      (counter := 0)
      h_not_special
      h_not_error
      (by
        simp [HeadNotExecutable, GroundedDispatch.none]
        constructor
        · intro hunify
          apply h_not_special
          simp [SpecialFormHead, hunify]
        · intro hswitch
          apply h_not_special
          simp [SpecialFormHead, hswitch])
      (LeaTTaBridge.queryEquationsAgainstVisible_unaryIdentity_counter0_mem
        head var value)
      (LeaTTaBridge.unaryIdentity_cover head value)
      (LeaTTaBridge.queryEquationsAvoiding_unaryIdentity_counter0_mem
        head var value)
      heq
      (by
        have htranslated :
            LeaTTaBridge.toLeaTTaMatchBindings
                (LeaTTaBridge.unaryIdentityBindings var value) =
              [Metta.BindingRel.val
                (LeaTTaBridge.unaryIdentityFresh0 var) (Metta.Atom.sym value)] := by
          simp [LeaTTaBridge.toLeaTTaMatchBindings,
            LeaTTaBridge.toLeaTTaMatchSubst,
            LeaTTaBridge.unaryIdentityBindings,
            LeaTTaBridge.unaryIdentityFresh0, Bindings.assign,
            Bindings.isBound, Bindings.lookup, Bindings.empty,
            Spec.Match.SolutionTheory.encodeModelAtom, Metta.Bindings.ofSubst]
        rw [htranslated]
        exact ClosedValueBindings.valueKeysFreshForValues
          (ClosedValueBindings.val (by simp [Metta.Atom.vars])
            ClosedValueBindings.nil))
      (by simp [BindingComposition.atomDepth])
      (LeaTTaBridge.unaryIdentity_instantiated_queryOp_item_counter0
        head var value (default : Metta.GroundingTable))
      (by
        simpa [hfull] using h_recurse))

/-- The actual invocation protocol refutes a universal bridge from the old
raw fuel evaluator to the current declarative call relation. -/
theorem heFuelEvaluatorEngine_has_no_historical_bridge :
    ¬ HEEngineBridge heFuelEvaluatorEngine := by
  intro bridge
  let value : Atom := .grounded (.int 7)
  let invocation : Atom :=
    .expression [.symbol "function", .expression [.symbol "return", value]]
  have executed : (value, Bindings.empty) ∈
      mettaCall Space.empty GroundedDispatch.none invocation Atom.atomType Bindings.empty 30 := by
    dsimp [invocation, value]
    decide +kernel
  have derived := bridge.mettaCall_sound Space.empty GroundedDispatch.none
    invocation Atom.atomType Bindings.empty 30 (value, Bindings.empty) executed
  have queryEmpty (avoid : List String) (fuel : Nat) :
      queryEquationsAvoiding avoid Space.empty invocation fuel = [] := by
    cases fuel <;> simp [queryEquationsAvoiding, Space.empty]
  dsimp [invocation, value] at derived
  cases derived
  all_goals simp_all [invocation, value, Space.empty, GroundedDispatch.none, isErrorAtom]

end Mettapedia.Languages.MeTTa.HE.Conformance
