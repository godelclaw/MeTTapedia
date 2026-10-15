import Mettapedia.GSLT.Causality.DoCalculus.ReviseRule
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder.BranchLocalCount
import Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Policies

/-!
# Which coordinate a publication may revise

`QueryCounts` is the module of `QueryState` and `poolObservational`.
`AdjustCounts` is the module of `frontDoorCounts`, `backDoorCounts`, and the
two query states. Neither name is a definition.

An observation of the actual run revises the observational coordinate.
A count from a region run under an intervention revises the interventional
coordinate. `crossingPolicy` is the publication that crosses: each direction
returns the observation only when `identificationDischarged` is true. The front
door and the back door admit both directions, and `revise_rule_sound_front`
and `revise_rule_sound_back` check the publication into the interventional
coordinate. The bow is the refusal, by `revise_rule_misses_bow`.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder

open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions
open Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.Regions.Controls
open Mettapedia.GSLT.Causality.DoCalculus
open Mettapedia.Logic.EvidenceStateInsufficiency
open Mettapedia.ProbabilityTheory.BayesianNetworks

/-- The two coordinates of a query. -/
inductive EvidenceCoordinate where
  | observational
  | interventional
deriving DecidableEq, Repr

theorem EvidenceCoordinate.same_not_cross :
    EvidenceCoordinate.observational ≠ EvidenceCoordinate.interventional := by
  decide

theorem EvidenceCoordinate.not_same (coordinate : EvidenceCoordinate) :
    coordinate = coordinate := rfl

/-- Publish the branch-local observations when `source` is `target`. A crossing
is not this policy. The store publication is `publish` of no steps. -/
def evidencePolicy (source target : EvidenceCoordinate) : Policy Unit Flag Bool where
  returned outcomes :=
    if source = target then outcomes.map Prod.fst else []
  change _ world := publish ([] : List (Step Unit Flag)) world

theorem evidencePolicy_same_returns (observation : Bool) :
    (evidencePolicy .observational .observational).returned
      ((pureObservation observation).branchLocal emptyFlag) = [observation] := by
  simp [evidencePolicy, pureObservation, Region.branchLocal, Readout.const]

theorem evidencePolicy_crossing_returns_nothing (observation : Bool) :
    (evidencePolicy .observational .interventional).returned
      ((pureObservation observation).branchLocal emptyFlag) = [] := by
  simp [evidencePolicy, pureObservation, Region.branchLocal, Readout.const,
    EvidenceCoordinate.same_not_cross]

/-- A crossing from `source` into `target`. The two arms are the two directions.
Each publishes the branch-local observations only when `source ≠ target` is the
arm and `identificationDischarged` is true. The same coordinate publishes
nothing. The store publication is `publish` of no steps. -/
def crossingPolicy {V : Type} [Fintype V] [DecidableEq V]
    (graph : DirectedGraph V) [DecidableRel graph.edges]
    (fuel : Nat) (enum : List V) (L outcome intervention conditioning : Finset V)
    (source target : EvidenceCoordinate) : Policy Unit Flag Bool where
  returned outcomes :=
    match source, target with
    | .observational, .interventional =>
      if identificationDischarged graph fuel enum L outcome intervention conditioning then
        outcomes.map Prod.fst
      else
        []
    | .interventional, .observational =>
      if identificationDischarged graph fuel enum L outcome intervention conditioning then
        outcomes.map Prod.fst
      else
        []
    | .observational, .observational => []
    | .interventional, .interventional => []
  change _ world := publish ([] : List (Step Unit Flag)) world

theorem front_identification_discharged :
    identificationDischarged smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS
      (∅ : Finset Smoke) = true := by
  rw [identificationDischarged, front_door_separates_id.2.1]

theorem back_identification_discharged :
    identificationDischarged doorGraph 2 doorEnum (∅ : Finset Door) doorY doorX
      (∅ : Finset Door) = true := by
  rw [identificationDischarged, (back_door_identify_count_licence true).1]

theorem crossingPolicy_returns (observation : Bool) :
    (crossingPolicy smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS (∅ : Finset Smoke)
        .observational .interventional).returned
      ((pureObservation observation).branchLocal emptyFlag) = [observation] := by
  simp [crossingPolicy, front_identification_discharged, pureObservation, Region.branchLocal,
    Readout.const]

theorem crossingPolicy_same_returns_nothing (observation : Bool) :
    (crossingPolicy smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS (∅ : Finset Smoke)
        .observational .observational).returned
      ((pureObservation observation).branchLocal emptyFlag) = [] := by
  simp [crossingPolicy, pureObservation, Region.branchLocal, Readout.const]

/-- Revise one coordinate by the observations a policy returns. -/
def publishCounts (policy : Policy Unit Flag Bool) (region : Region Unit Flag Bool)
    (world : Unit → Flag) (state : QueryState) (coordinate : EvidenceCoordinate) :
    QueryState :=
  (policy.returned (region.branchLocal world)).foldl
    (fun state observation =>
      match coordinate with
      | .observational => poolObservational state observation
      | .interventional => poolInterventional state observation)
    state

theorem publishCounts_actual (state : QueryState) (observation : Bool) :
    publishCounts (evidencePolicy .observational .observational)
      (pureObservation observation) emptyFlag state .observational =
        poolObservational state observation := by
  simp [publishCounts, evidencePolicy, pureObservation, Region.branchLocal, Readout.const,
    poolObservational]

theorem publishCounts_refused_crossing (state : QueryState) (observation : Bool) :
    publishCounts (evidencePolicy .observational .interventional)
      (pureObservation observation) emptyFlag state .interventional = state ∧
      poolInterventional state observation ≠ state := by
  refine ⟨?same, ?diff⟩
  · simp [publishCounts, evidencePolicy, pureObservation, Region.branchLocal, Readout.const,
      EvidenceCoordinate.same_not_cross]
  · intro same
    have changed := congrArg QueryState.interventional same
    cases observation with
    | true =>
      have posEq := congrArg Counts.pos changed
      simp [poolInterventional, Counts.revise] at posEq
    | false =>
      have negEq := congrArg Counts.neg changed
      simp [poolInterventional, Counts.revise] at negEq

/-- An observation of the actual run revises the observational coordinate. -/
theorem actual_revises_observational (state : QueryState) (observation : Bool) :
    publishCounts (evidencePolicy .observational .observational)
      (pureObservation observation) emptyFlag state .observational =
        poolObservational state observation ∧
      (poolObservational state observation).observational =
        state.observational.revise observation ∧
      (poolObservational state observation).interventional = state.interventional := by
  refine ⟨publishCounts_actual state observation, ?_, rfl⟩
  rfl

/-- A count returned by a region run as an intervention revises the
interventional coordinate and leaves the observational coordinate. -/
theorem intervention_revises_interventional (state : QueryState) (observation : Bool) :
    publishCounts (evidencePolicy .interventional .interventional)
      (pureObservation observation) emptyFlag state .interventional =
        poolInterventional state observation ∧
      (poolInterventional state observation).interventional =
        state.interventional.revise observation ∧
      (poolInterventional state observation).observational = state.observational := by
  refine ⟨?policy, rfl, rfl⟩
  simp [publishCounts, evidencePolicy, pureObservation, Region.branchLocal, Readout.const,
    poolInterventional]

/-- Both crossings, on `crossingPolicy`. The discharge bit is
`identificationDischarged` of the graph. Where it is false the target state is
unchanged. Where it is true the publication is one `poolObservational` or one
`poolInterventional` of the target coordinate. -/
theorem crossings_need_identification {V : Type} [Fintype V] [DecidableEq V]
    (graph : DirectedGraph V) [DecidableRel graph.edges]
    (fuel : Nat) (enum : List V) (L outcome intervention conditioning : Finset V)
    (source target : EvidenceCoordinate) (different : source ≠ target)
    (observation : Bool) (state : QueryState) :
    (identificationDischarged graph fuel enum L outcome intervention conditioning = false →
        publishCounts
          (crossingPolicy graph fuel enum L outcome intervention conditioning source target)
          (pureObservation observation) emptyFlag state target = state) ∧
      (identificationDischarged graph fuel enum L outcome intervention conditioning = true →
        publishCounts
          (crossingPolicy graph fuel enum L outcome intervention conditioning source target)
          (pureObservation observation) emptyFlag state target =
          match target with
          | .observational => poolObservational state observation
          | .interventional => poolInterventional state observation) := by
  refine ⟨?refused, ?admitted⟩
  · intro refused
    cases source <;> cases target <;> first | exact absurd rfl different | simp [
      publishCounts, crossingPolicy, refused, pureObservation, Region.branchLocal, Readout.const]
  · intro admitted
    cases source <;> cases target <;> first | exact absurd rfl different | simp [
      publishCounts, crossingPolicy, admitted, pureObservation, Region.branchLocal, Readout.const,
      poolObservational, poolInterventional]

/-- The front door admits both crossings. `source ≠ target`, and the gate is
`identificationDischarged` of the smoke graph. `revise_rule_sound_front` says
the publication into the interventional coordinate revises `frontDoorCounts`
and leaves the observational coordinate at the actual counts. -/
theorem front_door_admitted (experiment : Bool) :
    identificationDischarged smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS
        (∅ : Finset Smoke) = true ∧
      publishCounts
          (crossingPolicy smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS (∅ : Finset Smoke)
            .observational .interventional)
          (pureObservation experiment) emptyFlag frontDoorState .interventional =
        poolInterventional frontDoorState experiment ∧
      (poolInterventional frontDoorState experiment).interventional =
        frontDoorCounts.revise experiment ∧
      (poolInterventional frontDoorState experiment).observational = smokeObsCounts ∧
      publishCounts
          (crossingPolicy smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS (∅ : Finset Smoke)
            .interventional .observational)
          (pureObservation experiment) emptyFlag frontDoorState .observational =
        poolObservational frontDoorState experiment := by
  refine ⟨front_identification_discharged,
    (crossings_need_identification smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS
      (∅ : Finset Smoke) .observational .interventional EvidenceCoordinate.same_not_cross
      experiment frontDoorState).2 front_identification_discharged,
    (revise_rule_sound_front experiment front_identification_discharged).1,
    (revise_rule_sound_front experiment front_identification_discharged).2,
    (crossings_need_identification smokeGraph 2 smokeEnum {Smoke.u} {Smoke.c} smokeS
      (∅ : Finset Smoke) .interventional .observational EvidenceCoordinate.same_not_cross.symm
      experiment frontDoorState).2 front_identification_discharged⟩

/-- The back door admits both crossings, by `revise_rule_sound_back`. -/
theorem back_door_admitted (experiment : Bool) :
    identificationDischarged doorGraph 2 doorEnum (∅ : Finset Door) doorY doorX
        (∅ : Finset Door) = true ∧
      publishCounts
          (crossingPolicy doorGraph 2 doorEnum (∅ : Finset Door) doorY doorX (∅ : Finset Door)
            .observational .interventional)
          (pureObservation experiment) emptyFlag backDoorState .interventional =
        poolInterventional backDoorState experiment ∧
      (poolInterventional backDoorState experiment).interventional =
        backDoorCounts.revise experiment ∧
      (poolInterventional backDoorState experiment).observational = doorObsCounts ∧
      publishCounts
          (crossingPolicy doorGraph 2 doorEnum (∅ : Finset Door) doorY doorX (∅ : Finset Door)
            .interventional .observational)
          (pureObservation experiment) emptyFlag backDoorState .observational =
        poolObservational backDoorState experiment := by
  refine ⟨back_identification_discharged,
    (crossings_need_identification doorGraph 2 doorEnum (∅ : Finset Door) doorY doorX
      (∅ : Finset Door) .observational .interventional EvidenceCoordinate.same_not_cross
      experiment backDoorState).2 back_identification_discharged,
    (revise_rule_sound_back experiment back_identification_discharged).1,
    (revise_rule_sound_back experiment back_identification_discharged).2,
    (crossings_need_identification doorGraph 2 doorEnum (∅ : Finset Door) doorY doorX
      (∅ : Finset Door) .interventional .observational EvidenceCoordinate.same_not_cross.symm
      experiment backDoorState).2 back_identification_discharged⟩

/-- The bow refuses both crossings. `revise_rule_misses_bow` discharges nothing,
so `crossingPolicy` leaves each target coordinate unchanged. -/
theorem bow_crossing_refused (observation : Bool) (state : QueryState) :
    identificationDischarged bowGraph 2 bowEnum {Bow.u} {Bow.y} {Bow.x}
        (∅ : Finset Bow) = false ∧
      publishCounts
          (crossingPolicy bowGraph 2 bowEnum {Bow.u} {Bow.y} {Bow.x} (∅ : Finset Bow)
            .observational .interventional)
          (pureObservation observation) emptyFlag state .interventional = state ∧
      publishCounts
          (crossingPolicy bowGraph 2 bowEnum {Bow.u} {Bow.y} {Bow.x} (∅ : Finset Bow)
            .interventional .observational)
          (pureObservation observation) emptyFlag state .observational = state := by
  refine ⟨revise_rule_misses_bow,
    (crossings_need_identification bowGraph 2 bowEnum {Bow.u} {Bow.y} {Bow.x} (∅ : Finset Bow)
      .observational .interventional EvidenceCoordinate.same_not_cross observation state).1
      revise_rule_misses_bow,
    (crossings_need_identification bowGraph 2 bowEnum {Bow.u} {Bow.y} {Bow.x} (∅ : Finset Bow)
      .interventional .observational EvidenceCoordinate.same_not_cross.symm observation state).1
      revise_rule_misses_bow⟩

end Mettapedia.Languages.ProcessCalculi.MeTTaCalculus.EvidenceBorder
