import Mettapedia.GSLT.Distinction.OptionGraph
import Mettapedia.SetTheory.OpenTower.Hosting
import Mettapedia.SetTheory.OpenTower.Stability
import Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion
import Mettapedia.SetTheory.OpenTower.ConsistencyTower
import Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels
import Mettapedia.SetTheory.OpenTower.Strength.Shapes
import Mettapedia.SetTheory.OpenTower.Strength.Completions
import Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories
import Mettapedia.TypeTheory.IndexedUniverseAdequacy
import Mettapedia.GSLT.Logic.ObserverPresheafControls
import Mettapedia.Logic.TheoryModel.Basic
import Mettapedia.Logic.FinitaryRuleSystem.DirectedUnion
import Mettapedia.Logic.Metaphysics.UltrainfinitismCore
import Mettapedia.Logic.StoneGunkDuality
import Mettapedia.SetTheory.CarveOuts.WellFoundedBubble

/-!
# Open towers of set stages, placed in the option graph

Seven questions, with their options, arrows, contracts and witnesses.

* **What an open tower is** (`open-tower-kind`): an internal tower of closed sets in one level
  under a named supply of inaccessibles; the external schema of embeddings between universe
  levels; a generated enclosure tower; a proof-theoretic progression. The first two are built,
  and so are the finite levels of the progression of consistency extensions; the generated
  enclosure tower is recorded without facts from this module.
* **Limits** (`open-tower-limit`): the union of the ω-tower against its closure.
* **Hosting** (`open-tower-hosting`): a stage as a model of an exactly named derivation
  system, componentwise enclosure of its model codes in a later stage, and a first-order set
  model. The coded interpretation agrees through each type's decoding bijection; a single
  internal code for the whole interpretation and internal consistency remain separate.
* **Stability** (`open-tower-stability`): what survives the inclusion of an earlier stage into
  a later one.
* **The strength of the top** (`open-tower-top`): a greatest stage, a strongest completion
  reachable by one sentence, a cofinal extensible family, one fixed model, a linear open tower, or
  a plural family of admitted theories. The review digest proposed this question separately as
  the strength of the top; it is the same question and is merged here. Its "greatest consistent
  theory" is recorded in the one form refuted, a completion isolated by one sentence. Every pair
  of its options is separated by a witness. Its four undecided options are ordered by arrows:
  restrictions from the plural family down to one model, the reading of the plural family at
  one model, interpretations back up, and the passages one level up.
* **Perspectives** (`open-tower-perspectives`): three statements of openness, kept as separate
  options, with the one equivalence that holds between two of them: for Boolean algebras, no
  terminal refinement stage and no principal perspective are the same property.
* **The hosted system** (`open-tower-hosted-system`): the higher-order derivation system of the
  seven set laws, which every stage hosts. Hosting is an interpretation of that system in a stage:
  a stage exists, so the system is consistent relative to the host. No arithmetized consistency
  statement and no conservativity are claimed.

Boundaries are recorded as unknowns, not as preservation claims: whether the union of the
ω-tower satisfies Replacement is open, and the eventual theory is consistent but not shown
complete.

`graph` is the local graph; `graph_wellFormed`, `witnesses_kernelChecked`, `contracts_cited`,
`quotients_honest`, `contracts_consistent`, `lossy_counterexampled` and `rejected_witnessed`
check it, and `identifications` lists the two pairs it proves to be the same. Host choice
enters through the replacement operation of the set model and through
Mathlib's cardinal arithmetic; the choice-free tower is recorded as a fact of the internal
option.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeOptions.OpenTower

open Lean (Name)
open Mettapedia.GSLT.Distinction.OptionGraph

/-- The report that records the arguments. -/
def report : Document where
  key := "open-tower-of-stages-report-20261006"
  title := "Open towers of set stages: what they are, hosting, stability and the top"
  date := "2026-10-06"

/-- The named supply of inaccessibles that the internal tower is conditional on. -/
def cofinalInaccessibles : NamedHypothesis where
  name := ``Mettapedia.Logic.HOL.Embedding.ZFSetUniverseClosure.CofinalInaccessibles
  conditions := "Every theorem of the internal tower: cofinally many inaccessible cardinals at \
    the level of the sets"

/-! ## Questions -/

def questions : List Question := [
  { id := "open-tower-kind"
    title := "What an open tower of set stages is"
    summary := "Four constructions share the name: an internal tower of closed sets in one level \
      under a named supply of inaccessibles, the external schema of embeddings between universe \
      levels, a generated enclosure tower of declared codes, and a proof-theoretic progression \
      of consistency or reflection extensions. None is renamed as another." },
  { id := "open-tower-limit"
    title := "The limit of the ω-tower"
    summary := "Whether the union of the ω-tower is itself a stage, and what it models." },
  { id := "open-tower-hosting"
    title := "How a later stage hosts an earlier one"
    summary := "A stage as a model of an exactly named derivation system with closed falsity \
      empty; its type codes, operation codes and individual truth fibres enclosed in a later \
      stage, with external decoding agreement; a first-order set model of ZFC." },
  { id := "open-tower-stability"
    title := "What survives growth from one stage to a later one"
    summary := "Truth of formulas along the inclusion of an earlier stage into a later one, and \
      the eventual theory of the tower: deductively closed, consistent and containing ZFC; \
      whether it is complete is open."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.Stability.eventualTheory_closed,
      ``Mettapedia.SetTheory.OpenTower.Stability.eventualTheory_consistent,
      ``Mettapedia.SetTheory.OpenTower.Stability.mem_eventualTheory_iff_free,
      ``Mettapedia.SetTheory.OpenTower.Stability.zfc_subset_eventualTheory,
      ``Mettapedia.SetTheory.OpenTower.Stability.infinity_eventual_not_initial]] },
  { id := "open-tower-top"
    title := "Strength of the top"
    summary := "Whether the top is a greatest stage, a strongest theory reached from the base by \
      one sentence, one fixed model, a linear open tower, a plural family of admitted theories \
      with interpretation arrows, or a cofinal, directed, extensible family of stages that no \
      set exhausts. 'Strongest' names an order: constructor capability, interpretability, \
      proof-theoretic strength or model strength. Among the four undecided options, at one \
      level: one model is a part of a tower, a tower is a part of the cofinal family, and every \
      stage of the cofinal family is admitted under one of the two maximal theories of the \
      plural family; nothing goes back as a part. The closed sets of a level form a chain. A \
      tower lies inside one model beyond it; the cofinal family lies inside no model of its \
      level, and one level up it is the family of stages inside one model. A model of a theory \
      is one of its completions: its verdict on a sentence is a function of the class of the \
      sentence, and the class is not a function of the verdict when a sentence is left open."
    facts := [cites [``Mettapedia.TypeTheory.IndexedUniverseAdequacy.no_final_stage,
      ``Mettapedia.TypeTheory.IndexedUniverseAdequacy.finite_support_has_strict_host,
      ``Mettapedia.GSLT.AdmissibleContextCongruence.ObserverPresheafControls.OracleTower.oracleTower_strict,
      ``Mettapedia.Logic.TheoryModel.subset_theoryOf_iff],
      cites [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsFixedModel.exists_isLinearTower,
        ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsLinearTower.subset_closedSets,
        ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsLinearTower.not_subset_of_isFixedModel,
        ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsCofinalFamily.not_subset_of_collected,
        ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsCofinalFamily.subset_total,
        ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsLinearTower.exists_isFixedModel_hosting,
        ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsCofinalFamily.not_hostedBy_of_collected,
        ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.mem_image_closed_iff],
      cites [``Mettapedia.SetTheory.OpenTower.Strength.Completions.exists_completion_of_model,
        ``Mettapedia.SetTheory.OpenTower.Strength.Completions.model_verdict_factors_through_class,
        ``Mettapedia.SetTheory.OpenTower.Strength.Completions.class_not_factors_through_model_verdict],
      .«theorem» [
        { declaration := ``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.not_collected_of_cofinal, choiceFree := true },
        { declaration := ``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.not_injective_of_subsets_mem, choiceFree := true },
        { declaration := ``Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels.em_of_closedRel_trichotomy, choiceFree := true },
        { declaration := ``Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels.exists_incomparable_transitive, choiceFree := true },
        { declaration := ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.bubble_wellFounded, choiceFree := true },
        { declaration := ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.no_common_admitted_extension,
          choiceFree := true },
        { declaration := ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.hypersets_no_memHom_into_members,
          choiceFree := true }]] },
  { id := "open-tower-hosted-system"
    title := "The system a stage hosts"
    summary := "The higher-order derivation system of the seven set laws, with its proofs \
      retained." },
  { id := "open-tower-perspectives"
    title := "Three statements of openness"
    summary := "No terminal stage of a tower of sets, no isolated completion of a theory, and no \
      principal point of a space of perspectives. Only the last two are joined by a theorem, for \
      Boolean algebras." }
]

/-! ## Options -/

def nodes : List Node := [
  { id := "internal-set-tower", question := "open-tower-kind"
    title := "Internal tower of closed sets"
    summary := "Closed sets in one level of ZFSet: least closed sets around each stage, an \
      ordinal-indexed continuation, directed, cofinal, without a greatest stage. The tower is \
      choice-free when enclosures are supplied as data and replacement is stated relationally."
    hypotheses := [cofinalInaccessibles]
    facts := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.stage_ssubset_of_lt,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.no_terminal_stage,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.stages_directed,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.no_small_cofinal_family,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.ordinalStage_unbounded,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.closed_empty],
      .«theorem» [
        { declaration :=
          ``Mettapedia.SetTheory.OpenTower.InternalTower.Enclosures.relStage_mem_of_lt,
          choiceFree := true },
        { declaration :=
            ``Mettapedia.SetTheory.OpenTower.InternalTower.Enclosures.relStage_independent,
          choiceFree := true },
        { declaration := ``Mettapedia.SetTheory.OpenTower.InternalTower.hullRel_closedRel,
          choiceFree := true },
        { declaration := ``Mettapedia.SetTheory.OpenTower.Stability.bounded_absolute,
          choiceFree := true }]] },
  { id := "external-level-schema", question := "open-tower-kind"
    title := "External schema across universe levels"
    summary := "The membership-preserving embedding of each level into the next, whose image is \
      a closed set containing ω and elementarily equivalent to the lower level. Each statement \
      sees finitely many levels; the levels are not terms."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.ExternalTower.liftEmbedding_mem_iff,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.image_is_set,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.image_closed,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.not_seen_whole_at_same_level,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.exists_closed_omega_succ,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.exists_nested_closed_omega]] },
  { id := "generated-enclosure-tower", question := "open-tower-kind"
    title := "Generated enclosure tower"
    summary := "The closure of declared codes under declared operations, decoded coherently. \
      Weaker than closure under every small family of the ambient level." },
  { id := "proof-theoretic-progression", question := "open-tower-kind"
    title := "Proof-theoretic progression"
    summary := "Extensions of a theory by consistency or reflection principles along presented \
      well-orders. A separate track from enlarging set carriers. The finite levels of the \
      consistency progression over a Δ₁ extension of IΣ₁ true in the standard model are built: \
      each stage proves the consistency of the one below and not its own, the stages increase \
      strictly without a terminal stage, and no stage proves every truth of the standard model. \
      They are instantiated at PA, whose Δ₁ presentation is constructed, not postulated; true \
      arithmetic, which proves every truth, has no Δ₁ presentation. Transfinite levels are not \
      built."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.ConsistencyTower.SoundStage.next_proves_consistency,
      ``Mettapedia.SetTheory.OpenTower.ConsistencyTower.SoundStage.not_proves_own_consistency,
      ``Mettapedia.SetTheory.OpenTower.ConsistencyTower.SoundStage.tower_strictMono,
      ``Mettapedia.SetTheory.OpenTower.ConsistencyTower.SoundStage.not_next_le,
      ``Mettapedia.SetTheory.OpenTower.ConsistencyTower.noTerminalStage,
      ``Mettapedia.SetTheory.OpenTower.ConsistencyTower.truth_not_reached,
      ``Mettapedia.Logic.Diagonal.Arithmetic.stage_diagonalizable,
      ``Mettapedia.Logic.Diagonal.InductionSchemeDelta1.peanoDelta1,
      ``Mettapedia.SetTheory.OpenTower.ConsistencyTower.peano_tower_strictMono,
      ``Mettapedia.SetTheory.OpenTower.ConsistencyTower.peano_tower_certified,
      ``Mettapedia.SetTheory.OpenTower.ConsistencyTower.peano_tower_not_self_certified,
      ``Mettapedia.SetTheory.OpenTower.ConsistencyTower.trueArith_not_delta1]] },
  { id := "union-of-tower", question := "open-tower-limit"
    title := "The union of the ω-tower"
    summary := "The set of members of all stages of the ω-tower. It models Zermelo set theory with \
      choice; whether it satisfies Replacement is open."
    hypotheses := [cofinalInaccessibles]
    facts := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.towerUnion_not_closed,
      ``Mettapedia.SetTheory.OpenTower.ZFCStages.towerUnion_zclosed,
      ``Mettapedia.SetTheory.OpenTower.ZFCStages.towerUnion_models_zc]] },
  { id := "closure-of-union", question := "open-tower-limit"
    title := "The ω-th stage"
    summary := "The least closed set around the union of the ω-tower."
    hypotheses := [cofinalInaccessibles]
    facts := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.limitStage_closed,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.stage_mem_limitStage,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.towerUnion_ne_limitStage]] },
  { id := "stage-model", question := "open-tower-hosting"
    title := "A stage as a model of the seven set laws"
    summary := "The standard higher-order model over the members of a closed set containing ∅. \
      Every retained proof from the seven set laws is interpreted, and closed falsity is empty."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.theory_valid,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.theoremSection,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.falsity_empty,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.consistent]] },
  { id := "internal-copy", question := "open-tower-hosting"
    title := "Model component codes in a later stage"
    summary := "Type codes, coded operations and truth fibres of the stage model are members of \
      every later closed set containing the stage; terms are interpreted by graph lambda and \
      application. Whole-interpretation coding and internal consistency are separate obligations."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.internal_copy,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.consistent_from_internal_copy,
      ``Mettapedia.SetTheory.OpenTower.Hosting.tower_hosting,
      ``Mettapedia.SetTheory.OpenTower.Hosting.external_hosting]] },
  { id := "first-order-set-model", question := "open-tower-hosting"
    title := "A first-order set model of ZFC"
    summary := "The members of a closed set containing ω, as a structure for the first-order \
      language of set theory, with consistency in the Foundation library's calculus."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.ZFCStages.closed_models_zfc,
      ``Mettapedia.SetTheory.OpenTower.ZFCStages.stage_models_zfc,
      ``Mettapedia.SetTheory.OpenTower.ZFCStages.zfc_consistent_of_stage,
      ``Mettapedia.SetTheory.OpenTower.ZFCStages.image_models_zfc,
      ``Mettapedia.SetTheory.OpenTower.ZFCStages.zfc_consistent_of_image]] },
  { id := "earlier-stage", question := "open-tower-stability"
    title := "Truth at an earlier stage"
    summary := "Formulas read among the members of an earlier stage." },
  { id := "later-stage", question := "open-tower-stability"
    title := "Truth at a later stage"
    summary := "Formulas read among the members of a later stage, which includes the earlier \
      one transitively." },
  { id := "greatest-stage", question := "open-tower-top"
    title := "A greatest stage"
    summary := "A closed set including every closed set. It fails to exist exactly when every \
      closed set is a member of another."
    standings := [{
      standing := .rejected,
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.not_exists_greatest_stage]]
    }]
    hypotheses := [cofinalInaccessibles]
    facts := [cites [``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.not_exists_greatest_iff]] },
  { id := "strongest-completion", question := "open-tower-top"
    title := "A strongest theory reached by one sentence"
    summary := "A completion of a base theory isolated by a single sentence over it: the form in \
      which a greatest consistent theory above the base is refuted. The refutation is for \
      consistent Δ₁ extensions of IΣ₁; over a complete theory, such as the theory of a set model, \
      the one completion is isolated."
    standings := [{
      standing := .rejected,
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.no_isolated_completion,
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.lindenbaum_noTerminalStage]]
    }]
    facts := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Completions.isOpen_singleton_of_complete,
      ``Mettapedia.SetTheory.OpenTower.Strength.Completions.structure_theory_complete]] },
  { id := "cofinal-extensible-family", question := "open-tower-top"
    title := "A cofinal, directed, extensible family of stages"
    summary := "The class of stages: every set lies in a stage, any two sets lie in one stage, \
      every set-indexed family lies in one stage, and no set-indexed family is cofinal. The \
      stages are the levels of the von Neumann hierarchy at the inaccessible cardinals, with the \
      empty set and the hereditarily finite sets; they are well-ordered by membership, and the \
      named hypothesis says exactly that they are cofinal."
    hypotheses := [cofinalInaccessibles]
    facts := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.exists_stage_containing,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.stages_directed,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.small_family_bounded,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.no_small_cofinal_family],
      cites [``Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels.closed_eq_vonNeumann,
        ``Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels.closed_subset_total,
        ``Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels.closedSets_isWellOrder,
        ``Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels.closed_iff,
        ``Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels.cofinalInaccessibles_iff_cofinal,
        ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.isCofinalFamily_ordinalStage,
        ``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.closedSets_not_collected]] },
  { id := "one-fixed-model", question := "open-tower-top"
    title := "One fixed model"
    summary := "A single model, for example HOTG with ambient hypersets, as the top. A model is \
      one perspective: a point of the space of completions. As a set model it is one closed set \
      holding the empty set; the law that every set lies in a closed set fails inside it exactly \
      when it is the least closed set around one of its members."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.isFixedModel_hereditarilyFinite,
      ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.isFixedModel_image,
      ``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.not_universeLawInside_iff,
      ``Mettapedia.SetTheory.OpenTower.Strength.InaccessibleLevels.universeLawInside_vonNeumann_iff,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.image_members_in_closed_members,
      ``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.not_injective_members_into_member,
      ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.stage_holds_iff,
      ``Mettapedia.SetTheory.OpenTower.Strength.Completions.exists_completion_of_model,
      ``Mettapedia.SetTheory.OpenTower.Strength.Completions.affirms_neg_iff,
      ``Mettapedia.SetTheory.OpenTower.Strength.Completions.structure_theory_complete]] },
  { id := "linear-open-tower", question := "open-tower-top"
    title := "A linear open tower"
    summary := "Stages U0 < U1 < …, each modelling the last, with no final stage. As a tower \
      of closed sets it is the beginning of the tower indexed by the ordinals of the level; its \
      union is not closed."
    hypotheses := [cofinalInaccessibles]
    facts := [cites [``Mettapedia.TypeTheory.IndexedUniverseAdequacy.no_final_stage],
      cites [``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.stageChain_stage,
        ``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.StageChain.iUnion_not_closed,
        ``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.not_cofinal_range,
        ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.ordinalStage_natCast]] },
  { id := "plural-admitted-family", question := "open-tower-top"
    title := "A plural family of admitted theories"
    summary := "Stages related by interpretation arrows with contracts: directed within a \
      compatible family, joined across incompatible families only by interpretations into a host \
      that keeps their memberships apart; no terminal stage. Among theories of membership \
      principles, the admitted ones are exactly the parts of the well-founded theory and the \
      parts of the anti-founded theory: two maximal members with no common admitted extension."
    facts := [cites [``Mettapedia.Logic.FinitaryRuleSystem.directedUnion_noBottom,
      ``Mettapedia.Logic.FinitaryRuleSystem.Canary.splitUnion_not_noBottom,
      ``Mettapedia.SetTheory.CarveOuts.not_acc_of_quine],
      cites [``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.admitted_wellFounded,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.admitted_antiFounded,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.admitted_iff,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.hypersets_holds_iff,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.no_common_admitted_extension,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.no_greatest_admitted,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.bubble_wellFounded,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.bubble_decorates,
        ``Mettapedia.SetTheory.OpenTower.Strength.Completions.forall_affirms_iff_provable,
        ``Mettapedia.SetTheory.OpenTower.Strength.Completions.arithmetic_completions_disagree]] },
  { id := "seven-law-hol-system", question := "open-tower-hosted-system"
    title := "The derivation system of the seven set laws"
    summary := "Higher-order derivations from the seven HOTG set laws, retained as proof terms." },
  { id := "no-terminal-set-stage", question := "open-tower-perspectives"
    title := "No terminal stage of the tower of sets"
    summary := "Every closed set is a member of a later closed set."
    hypotheses := [cofinalInaccessibles]
    facts := [cites [
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.closedSets_noTerminalStage]] },
  { id := "no-terminal-refinement-stage", question := "open-tower-perspectives"
    title := "No terminal refinement stage"
    summary := "In a Boolean algebra, every nonzero element strictly refines to another nonzero \
      element; for Δ₁ extensions of IΣ₁, every consistent sentence over the theory is strictly \
      implied by another consistent one."
    facts := [cites [
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.lindenbaum_noTerminalStage,
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.bool_has_terminalStage]] },
  { id := "no-principal-perspective", question := "open-tower-perspectives"
    title := "No principal perspective"
    summary := "The space of perspectives has no isolated point: the Stone space of an atomless \
      algebra, the completions of an arithmetic theory, the free ultrafilters on the stage \
      indices."
    facts := [cites [``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.no_isolated_completion,
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.completions_nonempty,
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.free_ultrafilter_not_isolated]] }
]

/-! ## Arrows -/

def arrows : List Arrow := [
  { id := "level-image-as-stage", source := "external-level-schema"
    target := "internal-set-tower"
    kind := .interpretation
    grades := [.preserved]
    summary := "One level read as the set of its lifts one level up: a closed set containing ω, \
      bounding every lifted stage of the lower internal tower."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.ExternalTower.image_closed,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.lift_stage_mem_image,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.image_members_in_closed_members]]
    contract := {
      entries := [
        .keeps (.formulas .firstOrder)
          [``Mettapedia.SetTheory.OpenTower.ExternalTower.image_elementarilyEquivalent]
          "first-order sentences of membership and equality; the lift is an isomorphism onto \
          the members of the image",
        .keeps .laws [``Mettapedia.Logic.HOL.Embedding.ZFSetLiftedUniverseClosure.closed_lift_iff,
          ``Mettapedia.SetTheory.OpenTower.ExternalTower.lift_stage]
          "closedness is preserved and reflected; least closed sets commute with the lift under \
          the inaccessibility hypothesis at both levels",
        .unknownAt (.commitment .choice) "a choice-free code for the image set"] } },
  { id := "union-closes-to-limit", source := "union-of-tower"
    target := "closure-of-union"
    kind := .interpretation
    grades := [.preserved]
    summary := "The union of the ω-tower is a member of the ω-th stage, which contains every \
      stage."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.stage_mem_limitStage,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.limitStage_closed]]
    contract := {
      entries := [
        .keeps .distinctions [
          ``Mettapedia.SetTheory.OpenTower.InternalTower.towerUnion_ne_limitStage]
          "the union and the ω-th stage are different sets",
        .unknownAt (.formulas .firstOrder)
          "first-order replacement instances in the union of the ω-tower"] } },
  { id := "internal-copy-decodes", source := "internal-copy"
    target := "stage-model"
    kind := .interpretation
    grades := [.preserved]
    summary := "The coded interpretation of a term in the later stage decodes to its denotation \
      in the stage model."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.decode_interpret,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.decode_interpret_stage]]
    contract := {
      entries := [
        .keeps (.formulas .higherOrder)
          [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.decode_interpret_stage]
          "every term and formula of the seven-law signature, at every coded valuation",
        .keeps .verdicts [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.theorem_fibre,
          ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.falsity_fibre]
          "theorems have the inhabited fibre and closed falsity the empty fibre",
        .unknownAt .distinctions
          "one set coding satisfaction for all formulas at once, which needs a coding of the \
          syntax"] } },
  { id := "internal-copy-is-stage-model", source := "stage-model"
    target := "internal-copy"
    kind := .equivalence
    grades := [.exactKernel .extension]
    summary := "The componentwise coded interpretation agrees with the stage model through each \
      type: on every term and coded valuation, the coded interpretation decodes to the model's \
      denotation."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.decode_interpret_stage,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.decode_codedConstants]]
    contract := {
      entries := [
        .keeps (.formulas .higherOrder)
          [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.decode_interpret_stage]
          "every term and formula of the seven-law signature, at every coded valuation; decoding \
          is a bijection at each type, so every valuation of the model is reached",
        .unknownAt .distinctions
          "one set coding satisfaction for all formulas at once, which needs a coding of the \
          syntax"] } },
  { id := "earlier-into-later", source := "later-stage"
    target := "earlier-stage"
    kind := .restriction
    grades := [.preserved]
    summary := "The earlier stage is a transitive subset of the later one; truth is read on the \
      smaller carrier."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.stage_subset_of_le,
      ``Mettapedia.SetTheory.OpenTower.Stability.membershipEmbedding]]
    contract := {
      entries := [
        .keeps (.formulas .bounded)
          [``Mettapedia.SetTheory.OpenTower.Stability.bounded_absolute,
          ``Mettapedia.SetTheory.OpenTower.Stability.stage_bounded_absolute]
          "bounded formulas with parameters in the earlier stage, preserved and reflected",
        .loses (.formulas .firstOrder)
          [``Mettapedia.SetTheory.OpenTower.Stability.weakInfinity_changes,
          ``Mettapedia.SetTheory.OpenTower.Stability.infinity_changes]
          "an unbounded sentence false at the first stage over ∅ and true at the next"] } },
  { id := "stage-hosts-hol-system", source := "seven-law-hol-system"
    target := "stage-model"
    kind := .interpretation
    grades := [.ungraded]
    summary := "The derivation system interpreted in a stage, a closed set containing ∅: if the \
      stage exists, every derivation is interpreted and closed falsity has none, so the system \
      is consistent relative to the host. Along the tower and across levels its type codes, \
      operation codes and individual truth fibres belong to the next stage."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.consistent,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.internal_copy,
      ``Mettapedia.SetTheory.OpenTower.Hosting.tower_hosting,
      ``Mettapedia.SetTheory.OpenTower.Hosting.external_hosting]]
    contract := {
      entries := [
        .keeps .laws [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.theory_valid]
          "the seven set laws hold in the stage",
        .keeps .verdicts [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.consistent,
          ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.falsity_empty]
          "no derivation of closed falsity, given the stage",
        .keeps (.evidence .witnesses) [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.internal_copy,
          ``Mettapedia.SetTheory.OpenTower.Hosting.tower_hosting,
          ``Mettapedia.SetTheory.OpenTower.Hosting.external_hosting]
          "each type code, operation code and individual truth fibre belongs to the next stage",
        .unknownAt .distinctions
          "a single internal code for the whole model, syntax and proof interpretation",
        .unknownAt .verdicts
          "no arithmetized consistency statement Con(T) is stated or proved: consistency is \
          relative to the host and the stage",
        .unknownAt .distinctions
          "no conservativity: nothing true in the stage is shown derivable in the system"] } },
  { id := "plural-family-to-fixed-model", source := "plural-admitted-family"
    target := "one-fixed-model"
    kind := .observationalQuotient
    grades := [.factors, .lossy]
    summary := "Choosing one model is choosing a point of the space of perspectives: a model of a \
      theory is one of its completions. The verdict of the model on a sentence is a function of \
      the class of the sentence, so what holds at every perspective holds at the chosen one. \
      The class is not a function of the verdict when the theory leaves a sentence open: which \
      verdict the open sentence gets depends on the point."
    evidence := [cites [``Mettapedia.Logic.Metaphysics.ultraTrue_all_iff,
      ``Mettapedia.Logic.Metaphysics.ultraTrue_exists_iff,
      ``Mettapedia.Logic.Metaphysics.openFamily_iff_not_precise,
      ``Mettapedia.Foundations.Gunk.isGunky_iff_perfect_stoneSpace,
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.completions_perfect,
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.no_isolated_completion,
      ``Mettapedia.SetTheory.OpenTower.Strength.Completions.forall_affirms_iff_provable,
      ``Mettapedia.SetTheory.OpenTower.Strength.Completions.affirms_neg_iff],
      cites [``Mettapedia.SetTheory.OpenTower.Strength.Completions.exists_completion_of_model,
        ``Mettapedia.SetTheory.OpenTower.Strength.Completions.model_verdict_factors_through_class,
        ``Mettapedia.SetTheory.OpenTower.Strength.Completions.class_not_factors_through_verdict]]
    contract := {
      entries := [
        .keeps .verdicts [``Mettapedia.Logic.Metaphysics.ultraTrue_all_iff,
          ``Mettapedia.SetTheory.OpenTower.Strength.Completions.forall_affirms_iff_provable,
          ``Mettapedia.SetTheory.OpenTower.Strength.Completions.model_verdict_factors_through_class]
          "what holds at every perspective holds at the chosen one; for the completions of a \
          theory, what every completion affirms is what the theory proves, and the verdict of a \
          model on a sentence is a function of the class of the sentence",
        .loses .distinctions [``Mettapedia.SetTheory.OpenTower.Strength.Completions.arithmetic_completions_disagree,
          ``Mettapedia.SetTheory.OpenTower.Strength.Completions.stage_theories_leave_infinity_open,
          ``Mettapedia.SetTheory.OpenTower.Strength.Completions.class_not_factors_through_model_verdict]
          "the open sentences: a sentence the theory neither proves nor refutes is affirmed at \
          one completion and refuted at another, and the class of a sentence is not a function \
          of the verdict of one model, so one point does not show that a sentence is open"] } },
  { id := "plural-family-to-cofinal-family", source := "plural-admitted-family"
    target := "cofinal-extensible-family"
    kind := .restriction
    grades := [.preserved]
    summary := "The stages admitted under the set-forming principles with membership induction, \
      on the membership of one level of sets. They share one theory and one membership, and any \
      two of them are comparable. The accessible part of any stage admitted under the \
      set-forming principles is admitted under that theory too."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.stage_wellFounded,
      ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.bubble_wellFounded,
      ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.bubble_decorates,
      ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.admitted_wellFounded]]
    contract := {
      entries := [
        .keeps .laws [``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.stage_wellFounded,
          ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.bubble_wellFounded]
          "one admitted theory: every stage of the part satisfies the set-forming principles \
          and membership induction, and so does the accessible part of every stage admitted \
          under the set-forming principles",
        .keeps .verdicts [``Mettapedia.SetTheory.OpenTower.InternalTower.stages_directed,
          ``Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels.closed_subset_total]
          "compatible and directed: any two sets lie in one stage, and any two stages are \
          comparable by inclusion",
        .loses .distinctions [``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.no_quineAtom_among_members,
          ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.hypersets_no_memHom_into_members,
          ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.no_common_admitted_extension]
          "the anti-founded theory: no set has a Quine atom among its members, the hypersets \
          have no membership-preserving map into the members of a set, and no admitted theory \
          includes both theories"]
      hypotheses := [cofinalInaccessibles.name] } },
  { id := "cofinal-family-to-linear-tower", source := "cofinal-extensible-family"
    target := "linear-open-tower"
    kind := .restriction
    grades := [.preserved]
    summary := "The stages of a linear tower are closed sets of the level: the tower is a \
      subfamily of the cofinal family, with membership and inclusion as in the family."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsLinearTower.subset_closedSets,
      ``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.stageChain_stage,
      ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.isCofinalFamily_closedSets]]
    contract := {
      entries := [
        .keeps .laws [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsLinearTower.subset_closedSets,
          ``Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels.closed_subset_total]
          "every stage of the tower is a stage of the family, and the order of the family is \
          linear, as the order of the tower is",
        .loses .verdicts [``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.not_cofinal_range,
          ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsCofinalFamily.not_subset_of_collected]
          "cofinality: no family indexed by the natural numbers has every set of the level in \
          one of its members, so the cofinal family is a part of no tower"] } },
  { id := "linear-tower-to-fixed-model", source := "linear-open-tower"
    target := "one-fixed-model"
    kind := .restriction
    grades := [.preserved]
    summary := "One stage of the tower, kept alone as the model: every fixed model is the first \
      stage of a tower."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsFixedModel.exists_isLinearTower,
      ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.stage_wellFounded]]
    contract := {
      entries := [
        .keeps (.formulas .bounded) [``Mettapedia.SetTheory.OpenTower.Stability.stage_bounded_absolute]
          "bounded formulas with parameters in the stage have the same truth value at the stage \
          and at every later stage of the tower",
        .keeps .laws [``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.stage_wellFounded]
          "the stage satisfies the set-forming principles and membership induction",
        .loses (.formulas .firstOrder) [``Mettapedia.SetTheory.OpenTower.Stability.infinity_changes]
          "the axiom of infinity is false at the first stage over ∅ and true at every later stage",
        .loses .verdicts [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsFixedModel.not_hostedBy_self,
          ``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.not_injective_members_into_member,
          ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsLinearTower.not_subset_of_isFixedModel]
          "hosting: each stage of the tower is a member of the next, while the one stage is not \
          a member of itself and its members do not inject into the members of any of its \
          members; the tower is a part of no fixed model"]
      hypotheses := [cofinalInaccessibles.name] } },
  { id := "fixed-model-heads-linear-tower", source := "one-fixed-model"
    target := "linear-open-tower"
    kind := .interpretation
    grades := [.preserved]
    summary := "Every fixed model is the first stage of the tower over it; the type codes, \
      operation codes and truth fibres of its model are members of the next stage."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.stageChain_chainFrom,
      ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsFixedModel.exists_isLinearTower,
      ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.internal_copy]]
    contract := {
      entries := [
        .keeps (.evidence .witnesses) [``Mettapedia.SetTheory.OpenTower.Hosting.Stage.internal_copy]
          "each type code, operation code and individual truth fibre of the model belongs to \
          every later stage",
        .keeps (.formulas .bounded) [``Mettapedia.SetTheory.OpenTower.Stability.bounded_absolute]
          "bounded formulas with parameters in the model, preserved and reflected",
        .loses (.formulas .firstOrder) [``Mettapedia.SetTheory.OpenTower.Stability.infinity_changes]
          "the axiom of infinity is false at the first stage over ∅ and true at the later \
          stages of the tower over it"]
      hypotheses := [cofinalInaccessibles.name] } },
  { id := "linear-tower-in-cofinal-family", source := "linear-open-tower"
    target := "cofinal-extensible-family"
    kind := .interpretation
    grades := [.preserved]
    summary := "The stages of a linear tower are stages of the cofinal family, and the family \
      continues the tower: indexed by the ordinals of the level, the tower of least closed sets \
      reaches every set."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsLinearTower.subset_closedSets,
      ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.ordinalStage_natCast,
      ``Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels.ordinalStage_cofinal]]
    contract := {
      entries := [
        .keeps .laws [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsLinearTower.subset_closedSets,
          ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.ordinalStage_natCast]
          "every stage of the tower is a stage of the family; the tower of least closed sets is \
          the beginning of the tower indexed by the ordinals",
        .keeps .verdicts [``Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels.closed_trichotomy,
          ``Mettapedia.SetTheory.OpenTower.Strength.ClosedLevels.closedSets_isWellOrder]
          "the shape of the order: the stages of the family are well-ordered by membership, as \
          the stages of the tower are"]
      hypotheses := [cofinalInaccessibles.name] } },
  { id := "cofinal-family-in-plural-family", source := "cofinal-extensible-family"
    target := "plural-admitted-family"
    kind := .interpretation
    grades := [.preserved]
    summary := "Every stage of the family is admitted under one theory of the plural family, and \
      is a transitive part of the stage of the other theory: the map sending a set to its \
      hyperset is injective and preserves and reflects membership."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.stage_wellFounded,
      ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.members_decorate_hypersets,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.ofZFSet_injective]]
    contract := {
      entries := [
        .keeps .laws [``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.stage_wellFounded]
          "the set-forming principles and membership induction hold at every stage",
        .keeps (.formulas .atomic) [``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.members_decorate_hypersets,
          ``Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.ofZFSet_mem_ofZFSet_iff]
          "membership, into the hypersets: preserved and reflected, with a transitive image",
        .loses .verdicts [``Mettapedia.SetTheory.Profiles.hset_refutes_memInduction,
          ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.no_common_admitted_extension]
          "membership induction: a law of every stage of the family, refuted at the hypersets; \
          no admitted theory has it together with the Quine atom"] } },
  { id := "linear-tower-in-limit-model", source := "linear-open-tower"
    target := "one-fixed-model"
    kind := .interpretation
    grades := [.ungraded]
    summary := "Every linear tower lies inside one fixed model: a closed set that has every \
      stage of the tower as a member. That model is not the union of the tower, which is not \
      closed."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsLinearTower.exists_isFixedModel_hosting,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.small_family_bounded,
      ``Mettapedia.SetTheory.OpenTower.InternalTower.stage_mem_limitStage]]
    contract := {
      entries := [
        .keeps (.evidence .witnesses) [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsLinearTower.exists_isFixedModel_hosting,
          ``Mettapedia.SetTheory.OpenTower.Hosting.Stage.internal_copy]
          "every stage of the tower is a member of the model, which then holds the type codes, \
          operation codes and truth fibres of the model of each stage",
        .loses .verdicts [``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.StageChain.iUnion_not_closed,
          ``Mettapedia.SetTheory.OpenTower.InternalTower.towerUnion_ne_limitStage]
          "the tower as one model: the union of the stages is not closed, so the hosting model \
          is strictly beyond the tower"]
      hypotheses := [cofinalInaccessibles.name] } },
  { id := "cofinal-family-in-model-one-level-up", source := "cofinal-extensible-family"
    target := "one-fixed-model"
    kind := .interpretation
    grades := [.preserved]
    summary := "The closed sets of one level, lifted, are exactly the closed members of the \
      image of the level, which is one fixed model of the next level and satisfies the same \
      first-order sentences as the level. At one level there is no such model: a model with \
      every closed set as a member or a part would be a greatest stage."
    evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.mem_image_closed_iff,
      ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.isFixedModel_image,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.image_elementarilyEquivalent,
      ``Mettapedia.SetTheory.OpenTower.ExternalTower.image_members_in_closed_members,
      ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsCofinalFamily.not_hostedBy_of_collected]]
    contract := {
      entries := [
        .keeps (.formulas .firstOrder) [``Mettapedia.SetTheory.OpenTower.ExternalTower.image_elementarilyEquivalent]
          "first-order sentences of membership and equality: the level and its image satisfy \
          the same",
        .keeps .laws [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.mem_image_closed_iff,
          ``Mettapedia.SetTheory.OpenTower.ExternalTower.image_members_in_closed_members]
          "the stages: the closed members of the image are the lifts of the closed sets, and \
          every member of the image lies in one of them",
        .loses .verdicts [``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.closedSets_not_collected,
          ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsFixedModel.collected]
          "collection at its own level: no set of the level has every closed set as a member, \
          while one level up the image is one set"]
      hypotheses := [cofinalInaccessibles.name] } },
  { id := "plural-family-coded-one-level-up", source := "plural-admitted-family"
    target := "one-fixed-model"
    kind := .interpretation
    grades := [.ungraded]
    summary := "The stage with a Quine atom, hosted with its membership kept apart: every \
      hyperset of one level is a set of the next level, the codes form one set, and every \
      closed set that has the image of the level as a member has that set as a member. \
      Membership of hypersets is a relation on the codes, not their membership."
    evidence := [cites [``Mettapedia.TypeTheory.MaterialSets.Hypersets.code_injective,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.codeMem_code,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.mem_hsetCode,
      ``Mettapedia.TypeTheory.MaterialSets.Hypersets.hsetCode_mem_of_carrierCode_mem]]
    contract := {
      entries := [
        .keeps .distinctions [``Mettapedia.TypeTheory.MaterialSets.Hypersets.code_injective]
          "distinct hypersets have distinct codes",
        .keeps .verdicts [``Mettapedia.TypeTheory.MaterialSets.Hypersets.codeMem_code]
          "membership of hypersets, read as the interpreted relation on the codes",
        .loses (.formulas .atomic) [``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.codeMem_quineAtom_self,
          ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.hypersets_no_memHom_into_members]
          "membership as the host's membership: the code of the Quine atom is related to itself \
          and is not a member of itself, and no map of the hypersets into the members of a set \
          preserves membership"] } },
  { id := "refinement-is-perspective", source := "no-terminal-refinement-stage"
    target := "no-principal-perspective"
    kind := .equivalence
    grades := [.exactKernel .extension]
    summary := "For a Boolean algebra, a refinement tower of nonzero elements without a terminal \
      stage is exactly a Stone space without an isolated point."
    evidence := [cites [
      ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.noTerminalStage_iff_perfect]]
    contract := {
      entries := [
        .keeps .verdicts
          [``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.noTerminalStage_iff_perfect]
          "for every Boolean algebra, its perspectives the points of its Stone space",
        .unknownAt .distinctions
          "a comparison with the tower of sets, which is a different order, and with the free \
          ultrafilters on the stage indices, which are not given as the Stone space of an \
          algebra"] } }
]

/-! ## Observers and witnesses -/

def observers : List Observer := [
  { id := "limit-is-stage", title := "The limit is a stage"
    reads := "Whether the set is closed under union, power set and replacement."
    kind := .«theorem» },
  { id := "unbounded-sentence-preserved", title := "An unbounded sentence keeps its truth value"
    reads := "Whether the sentence `some nonempty set has no member-maximal element` has the \
      same truth value at the two stages."
    kind := .«theorem» },
  { id := "common-upper-stage", title := "A common upper stage"
    reads := "Whether two stages, one with Foundation and one with a Quine atom, need a \
      consistent stage above both on one membership relation."
    kind := .«theorem» },
  { id := "level-bounded", title := "One set bounds the stages of a level"
    reads := "Whether a single set has every stage of a level as a member."
    kind := .«theorem» },
  { id := "first-stage-model", title := "A model at the first stage"
    reads := "Whether the option's model of its theory exists at the first stage of the ω-tower \
      over ∅, where every set is hereditarily finite."
    kind := .«theorem» },
  { id := "realized-at-arithmetic", title := "Realized over arithmetic"
    reads := "Whether the option exists for a consistent Δ₁ extension of IΣ₁."
    kind := .«theorem» },
  { id := "greatest-element", title := "A greatest element"
    reads := "Whether the option has a top: a stage including every stage, a strongest theory \
      reached by one sentence, or an admitted theory including every admitted theory."
    kind := .«theorem» },
  { id := "stages-collected", title := "One set has every stage"
    reads := "Whether one set of the level has every stage of the option as a member."
    kind := .«theorem» },
  { id := "hosts-its-stages", title := "Hosts its own stages"
    reads := "Whether every stage of the option is a member of a stage of the option, which \
      then holds a model of it."
    kind := .«theorem» },
  { id := "independent-sentence", title := "One verdict on an open sentence"
    reads := "Whether the option gives one verdict to a sentence that the base theory neither \
      proves nor refutes."
    kind := .«theorem» },
  { id := "quine-atom-stage", title := "A stage with a Quine atom"
    reads := "Whether the option has a stage in which some set is its own only member."
    kind := .«theorem» },
  { id := "realized-at-a-stage", title := "Realized at a stage"
    reads := "Whether the option exists at a stage of the tower: among the closed sets of its \
      level, or as a completion of its first-order theory reached by one sentence."
    kind := .«theorem» }
]

def witnesses : List Witness := [
  { id := "union-not-a-stage", observer := "limit-is-stage"
    left := "union-of-tower", right := "closure-of-union"
    case := "The ω-tower over any set, under the inaccessibility hypothesis."
    leftVerdict := {
      reading := "Refuted: replacement along the finite ordinals collects every stage into one \
        member of the union."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.towerUnion_not_closed]] }
    rightVerdict := {
      reading := "Holds: the least closed set around the union."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.limitStage_closed]] } },
  { id := "weak-infinity-changes", observer := "unbounded-sentence-preserved"
    left := "earlier-stage", right := "later-stage"
    case := "The first two stages of the ω-tower over ∅."
    leftVerdict := {
      reading := "False: the first stage consists of hereditarily finite sets."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.Stability.weakInfinity_false_at_stage_zero,
        ``Mettapedia.SetTheory.OpenTower.Stability.stage_zero_hereditarilyFinite]] }
    rightVerdict := {
      reading := "True: the first stage is a member without a member-maximal element."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.Stability.weakInfinity_true_at_later_stage]] } },
  { id := "no-top-stage", observer := "greatest-element"
    left := "greatest-stage", right := "cofinal-extensible-family"
    case := "Closed sets of one level, under the inaccessibility hypothesis."
    leftVerdict := {
      reading := "Refuted: the least closed set around a greatest one would contain it."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.InternalTower.not_exists_greatest_stage]] }
    rightVerdict := {
      reading := "Holds without a top: directed, every set-indexed family bounded, no set-indexed \
        family cofinal."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.stages_directed,
        ``Mettapedia.SetTheory.OpenTower.InternalTower.no_small_cofinal_family]] } },
  { id := "no-strongest-completion", observer := "greatest-element"
    left := "strongest-completion", right := "cofinal-extensible-family"
    case := "A consistent Δ₁ extension of IΣ₁, and the closed sets of one level."
    leftVerdict := {
      reading := "Refuted: every consistent sentence over the theory is strictly implied by \
        another consistent one, so no completion is isolated."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.lindenbaum_noTerminalStage,
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.no_isolated_completion]] }
    rightVerdict := {
      reading := "Holds without a top: every closed set is a member of a later one."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.closedSets_noTerminalStage]] } },
  { id := "lower-level-bounded-above", observer := "level-bounded"
    left := "internal-set-tower", right := "external-level-schema"
    case := "The ordinal-indexed tower of closed sets of one level, under the inaccessibility \
      hypothesis."
    leftVerdict := {
      reading := "Not bounded: no set of the level contains every stage."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.ordinalStage_unbounded]] }
    rightVerdict := {
      reading := "Bounded one level up: the lift of every stage is a member of the image of the \
        level, which is a set there."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.ExternalTower.lift_ordinalStage_mem_image,
        ``Mettapedia.SetTheory.OpenTower.ExternalTower.image_is_set]] } },
  { id := "first-stage-not-zfc", observer := "first-stage-model"
    left := "stage-model", right := "first-order-set-model"
    case := "The first stage of the ω-tower over ∅, under the inaccessibility hypothesis."
    leftVerdict := {
      reading := "A model: the stage models the seven set laws, with closed falsity empty."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.tower_hosting]] }
    rightVerdict := {
      reading := "Not a model of ZFC: the axiom of infinity fails at the first stage and holds \
        from the next on."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Stability.infinity_changes,
        ``Mettapedia.SetTheory.OpenTower.Stability.stage_zero_hereditarilyFinite]] } },
  { id := "first-stage-copy-not-zfc", observer := "first-stage-model"
    left := "internal-copy", right := "first-order-set-model"
    case := "The first stage of the ω-tower over ∅, under the inaccessibility hypothesis."
    leftVerdict := {
      reading := "Present: the codes, operations and truth fibres of its model are members of the \
        next stage."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Hosting.tower_hosting]] }
    rightVerdict := {
      reading := "Not a model of ZFC: the axiom of infinity fails at the first stage."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Stability.infinity_changes]] } },
  { id := "no-top-linear-stage", observer := "greatest-element"
    left := "greatest-stage", right := "linear-open-tower"
    case := "Closed sets of one level, and a linear tower of universe stages."
    leftVerdict := {
      reading := "Refuted: the least closed set around a greatest one would contain it."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.InternalTower.not_exists_greatest_stage]] }
    rightVerdict := {
      reading := "Holds without a top: no stage is final, and every finite set of stages has a \
        strictly larger host."
      evidence := [cites [``Mettapedia.TypeTheory.IndexedUniverseAdequacy.no_final_stage,
        ``Mettapedia.TypeTheory.IndexedUniverseAdequacy.finite_support_has_strict_host]] } },
  { id := "no-strongest-linear-stage", observer := "greatest-element"
    left := "strongest-completion", right := "linear-open-tower"
    case := "A consistent Δ₁ extension of IΣ₁, and a linear tower of universe stages."
    leftVerdict := {
      reading := "Refuted: no completion is isolated."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.no_isolated_completion]] }
    rightVerdict := {
      reading := "Holds without a top: no stage is final."
      evidence := [cites [``Mettapedia.TypeTheory.IndexedUniverseAdequacy.no_final_stage]] } },
  { id := "a-completion-exists", observer := "realized-at-arithmetic"
    left := "strongest-completion", right := "one-fixed-model"
    case := "A consistent Δ₁ extension of IΣ₁."
    leftVerdict := {
      reading := "Not realized: no completion is reached by one sentence over the theory."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.no_isolated_completion]] }
    rightVerdict := {
      reading := "Realized: the space of completions is nonempty, and each completion is one \
        fixed perspective."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.completions_nonempty]] } },
  { id := "foundation-vs-quine", observer := "common-upper-stage"
    left := "plural-admitted-family", right := "linear-open-tower"
    case := "A stage with Foundation and a stage with a Quine atom, on one membership relation."
    leftVerdict := {
      reading := "Not needed: a Quine atom is not accessible, so the well-founded part and the \
        hypersets stay apart and are joined by interpretation."
      evidence := [cites [``Mettapedia.SetTheory.CarveOuts.not_acc_of_quine]] }
    rightVerdict := {
      reading := "Needed: a linear tower puts both on one membership, and in the canary rule \
        system a union that is not directed derives falsity."
      evidence := [cites [``Mettapedia.Logic.FinitaryRuleSystem.Canary.splitUnion_not_noBottom]] } },
  { id := "no-set-has-every-stage", observer := "stages-collected"
    left := "cofinal-extensible-family", right := "one-fixed-model"
    case := "The closed sets of one level, under the inaccessibility hypothesis, and one closed \
      set of that level. The law that every set lies in a closed set does not separate the two: \
      it holds inside the image of a level one level up, and inside the level at an inaccessible \
      cardinal exactly when the inaccessibles below it are unbounded. No first-order sentence \
      separates them for every model either: the image of a level satisfies the same sentences \
      as the level."
    leftVerdict := {
      reading := "No: every set of the level lies in a closed set, and no set has every member \
        of such a family as a member."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.closedSets_not_collected,
        ``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.not_collected_of_cofinal]] }
    rightVerdict := {
      reading := "Yes: one model is one set, a member of its singleton and, under the \
        hypothesis, of a later closed set."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsFixedModel.collected,
        ``Mettapedia.SetTheory.OpenTower.InternalTower.no_terminal_stage]] } },
  { id := "tower-is-collected", observer := "stages-collected"
    left := "cofinal-extensible-family", right := "linear-open-tower"
    case := "The closed sets of one level, under the inaccessibility hypothesis, and a tower of \
      closed sets indexed by the natural numbers. On the shape of the order the two agree: the \
      closed sets of a level are linearly ordered by inclusion."
    leftVerdict := {
      reading := "No: a cofinal family is collected by no set, so it is a part of no tower."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.closedSets_not_collected,
        ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsCofinalFamily.not_subset_of_collected]] }
    rightVerdict := {
      reading := "Yes: the stages of a tower are the members of one set, and one closed set has \
        them all as members."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsLinearTower.collected,
        ``Mettapedia.SetTheory.OpenTower.InternalTower.small_family_bounded]] } },
  { id := "open-sentence-left-open", observer := "independent-sentence"
    left := "one-fixed-model", right := "plural-admitted-family"
    case := "A consistent Δ₁ extension of IΣ₁ with a sentence it neither proves nor refutes; the \
      first two stages of the tower over ∅ with the axiom of infinity; the six set-forming \
      principles with membership induction against a Quine atom."
    leftVerdict := {
      reading := "One verdict: a model of a theory is one of its completions, a completion \
        affirms the negation of a sentence exactly when it does not affirm the sentence, and the \
        theory of a set model is complete."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Completions.exists_completion_of_model,
        ``Mettapedia.SetTheory.OpenTower.Strength.Completions.affirms_neg_iff,
        ``Mettapedia.SetTheory.OpenTower.Strength.Completions.structure_theory_complete]] }
    rightVerdict := {
      reading := "Left open: one completion affirms the sentence and another its negation; the \
        common theory of the two stages neither proves nor refutes infinity; membership \
        induction and a Quine atom are each admitted with the set-forming principles, and not \
        together."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Completions.arithmetic_completions_disagree,
        ``Mettapedia.SetTheory.OpenTower.Strength.Completions.stage_theories_leave_infinity_open,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.no_common_admitted_extension,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.admitted_wellFounded,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.admitted_antiFounded]] } },
  { id := "quine-atom-stage-admitted", observer := "quine-atom-stage"
    left := "cofinal-extensible-family", right := "plural-admitted-family"
    case := "The members of a set of any level, and the hypersets."
    leftVerdict := {
      reading := "None: no set has a Quine atom among its members, and every stage satisfies \
        membership induction."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.no_quineAtom_among_members,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.stage_wellFounded]] }
    rightVerdict := {
      reading := "One: the hypersets satisfy the set-forming principles with a Quine atom. They \
        are joined to the well-founded stages by interpretation: every transitive set is a \
        transitive part of them, their accessible part satisfies the well-founded theory, and \
        one level up they are coded as sets under their own membership. They have no \
        membership-preserving map into the members of a set."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.admitted_antiFounded,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.members_decorate_hypersets,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.bubble_wellFounded,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.hypersets_no_memHom_into_members,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.codeMem_quineAtom_self]] } },
  { id := "fixed-model-not-self-hosted", observer := "hosts-its-stages"
    left := "one-fixed-model", right := "linear-open-tower"
    case := "One closed set holding the empty set, and a tower of closed sets indexed by the \
      natural numbers."
    leftVerdict := {
      reading := "No: the model is not a member of itself, and its members do not inject into \
        the members of any of its members."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsFixedModel.not_hostedBy_self,
        ``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.not_injective_members_into_member]] }
    rightVerdict := {
      reading := "Yes: each stage is a member of the next, which holds the type codes, \
        operation codes and truth fibres of its model."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.IsLinearTower.hostedBy_self,
        ``Mettapedia.SetTheory.OpenTower.Hosting.tower_hosting]] } },
  { id := "stage-theory-isolates-its-completion", observer := "realized-at-a-stage"
    left := "greatest-stage", right := "strongest-completion"
    case := "A stage of the tower: the closed sets of its level, under the inaccessibility \
      hypothesis, and its first-order theory."
    leftVerdict := {
      reading := "Not realized: no closed set of the level includes every closed set; \
        equivalently, every closed set is a member of another."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.not_exists_greatest_stage,
        ``Mettapedia.SetTheory.OpenTower.Strength.StageFamilies.not_exists_greatest_iff]] }
    rightVerdict := {
      reading := "Realized: the theory of a set model is complete and consistent, so it has a \
        completion, and that completion is isolated. The refutation of an isolated completion \
        is for effectively axiomatized bases."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Completions.structureTheory_completion_isolated,
        ``Mettapedia.SetTheory.OpenTower.Strength.Completions.structureTheory_completions_nonempty]] } },
  { id := "a-fixed-model-exists", observer := "realized-at-a-stage"
    left := "greatest-stage", right := "one-fixed-model"
    case := "The closed sets of one level, under the inaccessibility hypothesis."
    leftVerdict := {
      reading := "Not realized: no closed set of the level includes every closed set."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.not_exists_greatest_stage]] }
    rightVerdict := {
      reading := "Realized: the hereditarily finite sets are a fixed model at every level, \
        every stage of the tower after the first is a set model of ZFC, and one level up the \
        image of the level is a fixed model with no hypothesis. None of them is greatest: each \
        is a member of a later closed set. In another order the first stage over ∅ is maximal: \
        no closed set that has it as a member is elementarily equivalent to it, so it has no \
        elementary extension among the stages."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.Shapes.isFixedModel_hereditarilyFinite,
        ``Mettapedia.SetTheory.OpenTower.ZFCStages.stage_models_zfc,
        ``Mettapedia.SetTheory.OpenTower.Strength.Shapes.isFixedModel_image,
        ``Mettapedia.SetTheory.OpenTower.InternalTower.no_terminal_stage,
        ``Mettapedia.SetTheory.OpenTower.Strength.Completions.stage_zero_not_elementaryEquiv]] } },
  { id := "no-top-admitted-theory", observer := "greatest-element"
    left := "greatest-stage", right := "plural-admitted-family"
    case := "The closed sets of one level, under the inaccessibility hypothesis, and the \
      theories of membership principles admitted at a level."
    leftVerdict := {
      reading := "Refuted: the least closed set around a greatest one would contain it."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.InternalTower.not_exists_greatest_stage]] }
    rightVerdict := {
      reading := "Holds without a top: no admitted theory includes every admitted theory, \
        since the well-founded and the anti-founded theory have no common admitted extension; \
        directed unions of bottom-free rule systems stay bottom-free."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.no_greatest_admitted,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.no_common_admitted_extension,
        ``Mettapedia.Logic.FinitaryRuleSystem.directedUnion_noBottom]] } },
  { id := "no-strongest-admitted-theory", observer := "greatest-element"
    left := "strongest-completion", right := "plural-admitted-family"
    case := "A consistent Δ₁ extension of IΣ₁, and the theories of membership principles \
      admitted at a level."
    leftVerdict := {
      reading := "Refuted: no completion is isolated."
      evidence := [cites [
        ``Mettapedia.SetTheory.OpenTower.NoIsolatedCompletion.no_isolated_completion]] }
    rightVerdict := {
      reading := "Holds without a top: no admitted theory includes every admitted theory, \
        since the well-founded and the anti-founded theory have no common admitted extension."
      evidence := [cites [``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.no_greatest_admitted,
        ``Mettapedia.SetTheory.OpenTower.Strength.AdmittedTheories.no_common_admitted_extension]] } }
]

/-- The local graph of this module. -/
def graph : Graph where
  documents := [report]
  questions := questions
  nodes := nodes
  arrows := arrows
  observers := observers
  witnesses := witnesses

theorem graph_wellFormed : graph.wellFormed = true := by
  decide +kernel

/-- Every witness rests on theorems only. -/
theorem witnesses_kernelChecked : witnesses.all Witness.kernelChecked = true := by
  decide +kernel

theorem contracts_cited : graph.contractsCited = true := by
  decide +kernel

theorem quotients_honest : graph.quotientsHonest = true := by
  decide +kernel

theorem contracts_consistent : graph.contractsConsistent = true := by
  decide +kernel

theorem lossy_counterexampled : graph.lossyCounterexampled = true := by
  decide +kernel

/-- Every rejected option carries a witness. -/
theorem rejected_witnessed : graph.rejectedWitnessed = true := by
  decide +kernel

/-- **The two comparisons**: the componentwise coded interpretation agrees with the stage model,
and for Boolean algebras
no terminal refinement stage is no principal perspective. -/
theorem identifications : graph.equivalences = [
    ("stage-model", "internal-copy"),
    ("no-terminal-refinement-stage", "no-principal-perspective")] := by
  decide +kernel

end Mettapedia.Languages.MeTTa.PrimeOptions.OpenTower
