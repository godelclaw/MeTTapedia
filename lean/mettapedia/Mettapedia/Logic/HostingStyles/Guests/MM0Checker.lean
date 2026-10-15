import Mettapedia.Languages.MM0.Presentation.ObligationGSLT
import Mettapedia.GSLT.Meredith.GSLT
import Mettapedia.Logic.HostingStyles.Guests.CheckerContexts
import Mettapedia.Logic.HostingStyles.Guests.CheckerSimulation
import Mettapedia.Logic.HostingStyles.Guests.MM0Derivations

/-!
# The checker of an MM0 theory as it runs, and what a host of it has

`mm0Checker T` is the check of the certificates of the MM0 calculus over a
theory `T`, as the shared checker runs it (`certificateChecker`).  A state is
the list of the judgments that remain, each with the certificate submitted
for it; a step checks one node; the accepting state is the empty list.  A
computed leaf runs one of the three kernel operations of `T` in one step.

## Certificates that take long to check

**In every MM0 theory there are certificates whose check takes any number of
steps** (`mm0Checker_steps`, `mm0Checker_steps_unbounded`): the certificate
that proves a local hypothesis found after `count` others has `count + 2`
nodes, and no theorem of the theory is used.  The checker terminates
(`certificateCheckerRank`), so the argument from a cyclic reduction does not
apply to it; what applies is a bound on the runs of the host.

## The candidate presentation does not host it

* **A theory whose rank is bounded hosts the checker of no MM0 theory**
  (`mm0Checker_not_hostedBy_of_bounded`).
* The rank of the candidate presentation is at most three, under every
  evaluator of its premises and under each of its readings.  So for every
  theory the checker is not hosted under the linear reading, the reading with
  regions or the cartesian reading (`mm0Checker_not_hostedBy_row`), and no map
  into any of them preserves its steps (`mm0Checker_not_preserves_row`).  The
  witness is the certificate that proves the fourth of four local hypotheses:
  every theory accepts it and its check takes five steps (`witness_steps`).
* The same holds of the kernel over a query-first model
  (`mm0Checker_not_hostedBy_queryFirstKernel`).

The checker is given by its terms alone, so hosting it with all contexts and
hosting it on terms are one demand (`hostOf_mm0Checker_contexts_iff_terms`).

**With its contexts** (`mm0CheckerWithContexts T`, the states with named
places) the candidate receives no map from it under the linear reading, no map
that preserves its steps under the reading with regions and no hosting map
under the cartesian reading (`mm0CheckerWithContexts_row`); and so does the
candidate with a run constructor under every evaluator of its premises
(`mm0CheckerWithContexts_run_row`).  These three cells do not depend on the
length of the runs of the candidate.

## Two sentences for a candidate that computes

`MM0Checker` is the class of the checkers, one for each theory.

1. `HostOf candidate MM0Checker .terms .hosting`: one step of the candidate
   for each step of the check.
2. `RunsMM0Checkers candidate`: for each theory a reading of the states of the
   check with a nonempty reduction of the candidate for each step of the
   check, images of states without step that have no step, unique terms
   without step among the reducts of an image, and an accepting image that
   only the accepting state has (`RunsCheck`).  The first sentence implies
   the second (`runsMM0Checkers_of_hostOf`).

**What each buys.**  For a judgment `context ⊢ expression` of a theory, the
image of the state that submits some certificate reaches the image of the
accepting state exactly when the MM0 kernel derives the judgment
(`derives_iff_reaches_of_hostOf`, `mm0_runsCheck_reaches_iff_derives`; for
one hosting map, `mm0Checker_reaches_image_iff_derives`).  For one
certificate, its image reaches the accepting image exactly when the shared
checker accepts it.  A candidate that meets the first sentence has runs of
every length (`steps_unbounded_of_hostOf_mm0Checker`).

**Both can be met**: the checkers of all theories side by side meet them
(`sideBySide_hostOf_mm0Checker`, `sideBySide_runsMM0Checkers`); that theory
is the guests themselves.  The kernel of a model that carries the checkers beside its base
meets the first (`guestKernel_hostOf_mm0Checker`); there the hosting power is
in the model.  **The candidate presentation meets neither**
(`mm0Checker_class_row`, `not_runsMM0Checkers_row`).

## The obligations of the kernel, without a certificate

MM0 has a second theory with steps: `obligationGSLT T context hypotheses`,
whose states are lists of expressions still to be derived and whose steps
resolve the first one by one kernel rule, the step choosing what a certificate
would supply.  As soon as there is a local hypothesis it has runs of every
length (`obligations_steps`), so it is not hosted either
(`obligations_not_hostedBy_row`).  As soon as an expression has a sort it
converts that goal to itself (`obligations_cycle`): it does not terminate, and
no theory with a rank hosts it (`obligations_not_hostedBy_of_rank`).  Without
declarations, context and hypotheses it has no step
(`obligations_static_empty`).  Under a hosting map
the image of a goal reaches the image of the empty list exactly when the
kernel derives the goal (`obligations_reaches_image_iff_derives`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.Guests

open Mettapedia.GSLT
open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.MeTTaIL.ContextualStep (BasePremiseEvaluator)
open Mettapedia.GSLT.LanguageDef.InferenceChecker (RuleInstance RuleApplication argumentValidAt)
open Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves (CompactProof check checkChildren)
open Mettapedia.GSLT.LanguageDef.Authored
open Mettapedia.GSLT.LanguageDef.FirstOrderRules
open Mettapedia.Languages.MM0
open Mettapedia.Languages.MM0.Presentation (encode)
open Mettapedia.Languages.MM0.Presentation.Calculus
open Mettapedia.Languages.MM0.Presentation.ComputationalObligations
  (obligationGSLT Resolves hypothesis_query_exact theorem_query_exact conversion_query_exact
    singleton_discharge_iff)
open Mettapedia.Logic.HostingStyles.PrimeCandidate
open Mettapedia.Logic.HostingStyles.ContextReadings
open Mettapedia.Languages.MeTTa.PrimeCandidates.Language (Model QueryFirstModel kernelGSLT)
open Mettapedia.GSLT.LanguageDef.Contexts (contextTheory)

/-! ## The checker and the class -/

/-- **The checker of an MM0 theory, as it runs**: the check of the
certificates of the MM0 calculus over the theory, given by its states and
steps. -/
abbrev mm0Checker (T : Kernel.Theory) : ContextTheory.{0} := checkerTheory (mm0 T)

/-- **The class of the MM0 checkers**: one for each theory. -/
def MM0Checker (source : ContextTheory.{0}) : Prop :=
  ∃ T : Kernel.Theory, source = mm0Checker T

/-- **Positive**: the checker of each theory. -/
theorem mm0Checker_member (T : Kernel.Theory) : MM0Checker (mm0Checker T) := ⟨T, rfl⟩

/-! ## Certificates that take long to check -/

/-- A rule of the MM0 kernel applies at every list of valid arguments of its
length. -/
theorem kernelRule_application {r : FORule} (member : r ∈ rules) (args : List Pattern)
    (length : args.length = r.vars.length) (valid : ∀ a ∈ args, argumentValidAt 0 a = true) :
    RuleApplication kernelCalculus ⟨⟨r.id⟩, args⟩ (r.instPremises args)
      (r.instConclusion args) :=
  (ruleApplication_iff kernelCalculus rules presents.package r member (presents.lookup member) args
    _ _).mpr ⟨length, valid, rfl, rfl⟩

/-- **The certificate that an expression is among the local hypotheses**: one
node for each hypothesis passed over, and one for the hypothesis found. -/
def memberCertificate (T : Kernel.Theory) (expression : Kernel.Preterm) :
    List Kernel.Preterm → List Kernel.Preterm → Certificate (mm0 T)
  | [], rest =>
      .node ⟨⟨rHypothesisHere.id⟩,
        [expressionPattern expression, itemsPattern (rest.map encode)]⟩ []
  | passed :: skipped, rest =>
      .node ⟨⟨rHypothesisThere.id⟩, [expressionPattern expression, expressionPattern passed,
          itemsPattern ((skipped ++ expression :: rest).map encode)]⟩
        [memberCertificate T expression skipped rest]

/-- The shared checker accepts it. -/
theorem memberCertificate_accepted (T : Kernel.Theory) (expression : Kernel.Preterm) :
    ∀ skipped rest : List Kernel.Preterm,
      check (mm0 T).definition (mm0 T).family.evaluate
        (hypothesisJ expression (skipped ++ expression :: rest))
        (memberCertificate T expression skipped rest) = true
  | [], rest => by
      have applied := kernelRule_application (r := rHypothesisHere) (by simp [rules])
        [expressionPattern expression, itemsPattern (rest.map encode)] rfl
        (by simp [expressionPattern, termPattern_argumentValid, itemsPattern_argumentValid])
      rw [(inst_rHypothesisHere _ _).1, (inst_rHypothesisHere _ _).2] at applied
      exact (check_node_iff _ _ _ _ _).mpr ⟨[], applied, by simp [checkChildren]⟩
  | passed :: skipped, rest => by
      have applied := kernelRule_application (r := rHypothesisThere) (by simp [rules])
        [expressionPattern expression, expressionPattern passed,
          itemsPattern ((skipped ++ expression :: rest).map encode)] rfl
        (by simp [expressionPattern, termPattern_argumentValid, itemsPattern_argumentValid])
      rw [(inst_rHypothesisThere _ _ _).1, (inst_rHypothesisThere _ _ _).2] at applied
      refine (check_node_iff _ _ _ _ _).mpr
        ⟨[hypothesisJ expression (skipped ++ expression :: rest)], applied, ?_⟩
      simp only [checkChildren, Bool.and_true]
      exact memberCertificate_accepted T expression skipped rest

/-- It has one node for each hypothesis passed over and one more. -/
theorem memberCertificate_nodes (T : Kernel.Theory) (expression : Kernel.Preterm) :
    ∀ skipped rest : List Kernel.Preterm,
      certificateNodes (memberCertificate T expression skipped rest) = skipped.length + 1
  | [], _ => rfl
  | _ :: skipped, rest => by
      rw [memberCertificate, certificateNodes, certificateNodesList, certificateNodesList,
        memberCertificate_nodes T expression skipped rest]
      rfl

/-- **The certificate of `context ⊢ expression` by a local hypothesis.** -/
def localCertificate (T : Kernel.Theory) (context : Kernel.Context) (expression : Kernel.Preterm)
    (skipped rest : List Kernel.Preterm) : Certificate (mm0 T) :=
  .node ⟨⟨rHypothesis.id⟩, [contextPattern context,
      expressionsPattern (skipped ++ expression :: rest), expressionPattern expression]⟩
    [memberCertificate T expression skipped rest]

/-- The shared checker accepts it. -/
theorem localCertificate_accepted (T : Kernel.Theory) (context : Kernel.Context)
    (expression : Kernel.Preterm) (skipped rest : List Kernel.Preterm) :
    check (mm0 T).definition (mm0 T).family.evaluate
      (derivesJ context (skipped ++ expression :: rest) expression)
      (localCertificate T context expression skipped rest) = true := by
  have applied := kernelRule_application (r := rHypothesis) (by simp [rules])
    [contextPattern context, expressionsPattern (skipped ++ expression :: rest),
      expressionPattern expression] rfl
    (by simp [contextPattern, expressionsPattern, expressionPattern, termPattern_argumentValid])
  rw [(inst_rHypothesis _ _ _).1, (inst_rHypothesis _ _ _).2] at applied
  refine (check_node_iff _ _ _ _ _).mpr
    ⟨[hypothesisJ expression (skipped ++ expression :: rest)], applied, ?_⟩
  simp only [checkChildren, Bool.and_true]
  exact memberCertificate_accepted T expression skipped rest

/-- It has two nodes more than hypotheses passed over. -/
theorem localCertificate_nodes (T : Kernel.Theory) (context : Kernel.Context)
    (expression : Kernel.Preterm) (skipped rest : List Kernel.Preterm) :
    certificateNodes (localCertificate T context expression skipped rest) = skipped.length + 2 := by
  rw [localCertificate, certificateNodes, certificateNodesList, certificateNodesList,
    memberCertificate_nodes]

/-- **In every MM0 theory, the check of the certificate that proves a local
hypothesis found after others takes two steps more than hypotheses are passed
over.** -/
theorem mm0Checker_steps (T : Kernel.Theory) (context : Kernel.Context)
    (expression : Kernel.Preterm) (skipped rest : List Kernel.Preterm) :
    (mm0Checker T).Steps (interface := PUnit.unit) (skipped.length + 2)
      [(derivesJ context (skipped ++ expression :: rest) expression,
        localCertificate T context expression skipped rest)] [] :=
  (steps_singleton_iff _ _ _).mpr
    ⟨localCertificate_accepted T context expression skipped rest,
      (localCertificate_nodes T context expression skipped rest).symm⟩

/-- **The checker of every MM0 theory has runs of every length.** -/
theorem mm0Checker_steps_unbounded (T : Kernel.Theory) (bound : Nat) :
    ∃ (count : Nat) (start : Checking (mm0 T)), bound < count ∧
      (mm0Checker T).Steps (interface := PUnit.unit) count start [] := by
  have steps := mm0Checker_steps T [] (.var 0) (List.replicate bound (.var 0)) []
  rw [List.length_replicate] at steps
  exact ⟨bound + 2, _, by omega, steps⟩

/-! ## The witness against the candidate presentation -/

/-- Four local hypotheses. -/
def witnessHypotheses : List Kernel.Preterm := [.var 0, .var 1, .var 2, .var 3]

/-- **The witness**: the certificate that proves the fourth of four local
hypotheses. -/
def witnessCertificate (T : Kernel.Theory) : Certificate (mm0 T) :=
  localCertificate T [] (.var 3) [.var 0, .var 1, .var 2] []

/-- The shared checker accepts the witness, in every theory. -/
theorem witnessCertificate_accepted (T : Kernel.Theory) :
    check (mm0 T).definition (mm0 T).family.evaluate (derivesJ [] witnessHypotheses (.var 3))
      (witnessCertificate T) = true :=
  localCertificate_accepted T [] (.var 3) [.var 0, .var 1, .var 2] []

/-- The witness has five nodes. -/
theorem witnessCertificate_nodes (T : Kernel.Theory) :
    certificateNodes (witnessCertificate T) = 5 :=
  localCertificate_nodes T [] (.var 3) [.var 0, .var 1, .var 2] []

/-- **The check of the witness takes five steps**: two more than the
candidate presentation has. -/
theorem witness_steps (T : Kernel.Theory) :
    (mm0Checker T).Steps (interface := PUnit.unit) 5
      [(derivesJ [] witnessHypotheses (.var 3), witnessCertificate T)] [] :=
  mm0Checker_steps T [] (.var 3) [.var 0, .var 1, .var 2] []

/-- **Negative**, for the witness: submitted for the first hypothesis it is
rejected, and its check never accepts.  That judgment is derivable; this
certificate is no certificate of it. -/
theorem witness_rejected_for_other (T : Kernel.Theory) :
    ¬ (mm0Checker T).Reaches (interface := PUnit.unit)
      [(derivesJ [] witnessHypotheses (.var 0), witnessCertificate T)] [] := by
  intro reaches
  have accepted := (reaches_accepting_singleton_iff _ _).mp reaches
  obtain ⟨premises, applied, -⟩ := (check_node_iff _ _ _ _ _).mp accepted
  have expected := kernelRule_application (r := rHypothesis) (by simp [rules])
    [contextPattern [], expressionsPattern ([.var 0, .var 1, .var 2] ++ Kernel.Preterm.var 3 :: []),
      expressionPattern (.var 3)] rfl
    (by simp [contextPattern, expressionsPattern, expressionPattern, termPattern_argumentValid])
  rw [(inst_rHypothesis _ _ _).1, (inst_rHypothesis _ _ _).2] at expected
  have conclusions := (applied.outputs_unique expected).2
  have expressions := (derivesJ_injective (context := [])
    (hypotheses := witnessHypotheses) (expression := .var 0) (other := [])
    (otherHypotheses := witnessHypotheses) (otherExpression := .var 3) conclusions).2.2
  cases expressions

/-! ## The candidate presentation does not host the checker -/

/-- **A theory whose rank is bounded hosts the checker of no MM0 theory**: no
map into it even preserves the steps of the checker. -/
theorem mm0Checker_not_preserves_of_bounded {candidate : ContextTheory.{0}}
    (ranked : candidate.Rank) (bound : Nat)
    (bounded : ∀ {interface : candidate.Interface} (term : candidate.Term interface),
      ranked.rank term ≤ bound)
    (T : Kernel.Theory) (map : ContextMap (mm0Checker T) candidate) :
    ¬ map.PreservesTransitions := by
  obtain ⟨count, start, long, steps⟩ := mm0Checker_steps_unbounded T bound
  exact map.not_preserves_of_steps ranked bounded steps long

/-- **A theory whose rank is bounded hosts the checker of no MM0 theory.** -/
theorem mm0Checker_not_hostedBy_of_bounded {candidate : ContextTheory.{0}}
    (ranked : candidate.Rank) (bound : Nat)
    (bounded : ∀ {interface : candidate.Interface} (term : candidate.Term interface),
      ranked.rank term ≤ bound)
    (T : Kernel.Theory) : ¬ HostedBy (mm0Checker T) candidate :=
  fun ⟨map, hosting⟩ =>
    mm0Checker_not_preserves_of_bounded ranked bound bounded T map hosting.preserves

/-- **No map from the checker of an MM0 theory into the candidate preserves
its steps**, under the linear reading, the reading with regions or the
cartesian reading, for any evaluator of the premises of the candidate.  The
witness is the certificate of five nodes. -/
theorem mm0Checker_not_preserves_row (base : BasePremiseEvaluator) (T : Kernel.Theory) :
    (∀ map : ContextMap (mm0Checker T) (presentedReading base), ¬ map.PreservesTransitions) ∧
      (∀ map : ContextMap (mm0Checker T) (regionProbe base), ¬ map.PreservesTransitions) ∧
        ∀ map : ContextMap (mm0Checker T) (cartesianProbe base), ¬ map.PreservesTransitions :=
  ⟨fun map => presented_not_preserves_of_steps base map (witness_steps T) (by decide),
    fun map => reading_not_preserves_of_steps base probeData map (witness_steps T) (by decide),
    fun map => reading_not_preserves_of_steps base (fun _ => True) map (witness_steps T)
      (by decide)⟩

/-- **The candidate hosts the checker of no MM0 theory**, under the linear
reading, the reading with regions or the cartesian reading. -/
theorem mm0Checker_not_hostedBy_row (base : BasePremiseEvaluator) (T : Kernel.Theory) :
    ¬ HostedBy (mm0Checker T) (presentedReading base) ∧
      ¬ HostedBy (mm0Checker T) (regionProbe base) ∧
        ¬ HostedBy (mm0Checker T) (cartesianProbe base) :=
  ⟨not_hostedBy_presented_of_check base (witnessCertificate_accepted T)
      (by rw [witnessCertificate_nodes]; decide),
    not_hostedBy_reading_of_check base probeData (witnessCertificate_accepted T)
      (by rw [witnessCertificate_nodes]; decide),
    not_hostedBy_reading_of_check base (fun _ => True) (witnessCertificate_accepted T)
      (by rw [witnessCertificate_nodes]; decide)⟩

/-! ## The sentence -/

/-- A candidate that is a host of the class on terms hosts the checker of
each theory. -/
theorem hostedBy_of_hostOf_mm0Checker {candidate : ContextTheory.{0}}
    (hosts : HostOf candidate MM0Checker .terms .hosting) (T : Kernel.Theory) :
    HostedBy (mm0Checker T) candidate :=
  hosts _ ⟨mm0Checker T, ⟨T, rfl⟩, PUnit.unit, rfl⟩

/-- **For the class of the MM0 checkers, hosting with all contexts and
hosting on terms are one demand**: a checker is given by its terms alone. -/
theorem hostOf_mm0Checker_contexts_iff_terms {candidate : ContextTheory.{0}} :
    HostOf candidate MM0Checker .contexts .hosting ↔
      HostOf candidate MM0Checker .terms .hosting := by
  constructor
  · exact HostOf.terms
  · rintro hosts reading ⟨T, rfl⟩
    exact hostedBy_of_hostOf_mm0Checker hosts T

/-- **The candidate presentation is no host of the class**, under any of its
three readings. -/
theorem mm0Checker_class_row (base : BasePremiseEvaluator) :
    ¬ HostOf (presentedReading base) MM0Checker .terms .hosting ∧
      ¬ HostOf (regionProbe base) MM0Checker .terms .hosting ∧
        ¬ HostOf (cartesianProbe base) MM0Checker .terms .hosting :=
  ⟨fun hosts =>
      (mm0Checker_not_hostedBy_row base {}).1 (hostedBy_of_hostOf_mm0Checker hosts {}),
    fun hosts =>
      (mm0Checker_not_hostedBy_row base {}).2.1 (hostedBy_of_hostOf_mm0Checker hosts {}),
    fun hosts =>
      (mm0Checker_not_hostedBy_row base {}).2.2 (hostedBy_of_hostOf_mm0Checker hosts {})⟩

/-! ## What hosting the checker buys -/

/-- **The transfer**: under a hosting map from the checker of a theory, the
image of the state that submits some certificate for `context ⊢ expression`
reaches the image of the accepting state exactly when the MM0 kernel derives
the judgment.  Reaching is up to the static equivalence of the host. -/
theorem mm0Checker_reaches_image_iff_derives {candidate : ContextTheory.{0}} {T : Kernel.Theory}
    (map : ContextMap (mm0Checker T) candidate) (hosting : map.Hosting) (context : Kernel.Context)
    (hypotheses : List Kernel.Preterm) (expression : Kernel.Preterm) :
    (∃ (certificate : Certificate (mm0 T)) (final : candidate.Term (map.interface PUnit.unit)),
        candidate.Reaches
            (map.term (origin := PUnit.unit)
              [(derivesJ context hypotheses expression, certificate)])
            final ∧
          (candidate.equations (map.interface PUnit.unit)).r final
            (map.term (origin := PUnit.unit) [])) ↔
      Kernel.Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses
        expression :=
  (exists_reaches_image_iff_derivable map hosting _).trans
    (factDerivation_iff context hypotheses expression)

/-- **What a candidate that meets the sentence has**, for every theory: an
interface and images of the states of the check such that the image of a
submitted certificate reaches the image of the accepting state exactly when
the shared checker accepts the certificate, and some certificate's image does
for `context ⊢ expression` exactly when the MM0 kernel derives it. -/
theorem derives_iff_reaches_of_hostOf {candidate : ContextTheory.{0}}
    (hosts : HostOf candidate MM0Checker .terms .hosting) (T : Kernel.Theory) :
    ∃ (point : candidate.Interface) (image : Checking (mm0 T) → candidate.Term point),
      (∀ (goal : Pattern) (certificate : Certificate (mm0 T)),
        (∃ final, candidate.Reaches (image [(goal, certificate)]) final ∧
            (candidate.equations point).r final (image [])) ↔
          check (mm0 T).definition (mm0 T).family.evaluate goal certificate = true) ∧
        ∀ (context : Kernel.Context) (hypotheses : List Kernel.Preterm)
          (expression : Kernel.Preterm),
          (∃ (certificate : Certificate (mm0 T)) (final : candidate.Term point),
              candidate.Reaches (image [(derivesJ context hypotheses expression, certificate)])
                final ∧ (candidate.equations point).r final (image [])) ↔
            Kernel.Derives T.termSignature T.definitionSignature T.theoremSignature context
              hypotheses expression := by
  obtain ⟨map, hosting⟩ := hostedBy_of_hostOf_mm0Checker hosts T
  exact ⟨map.interface PUnit.unit, fun state => map.term (origin := PUnit.unit) state,
    fun goal certificate => reaches_image_iff_check map hosting goal certificate,
    fun context hypotheses expression =>
      mm0Checker_reaches_image_iff_derives map hosting context hypotheses expression⟩

/-- **A candidate that meets the sentence has runs of every length.** -/
theorem steps_unbounded_of_hostOf_mm0Checker {candidate : ContextTheory.{0}}
    (hosts : HostOf candidate MM0Checker .terms .hosting) (bound : Nat) :
    ∃ (interface : candidate.Interface) (count : Nat) (term final : candidate.Term interface),
      bound < count ∧ candidate.Steps count term final := by
  obtain ⟨map, hosting⟩ := hostedBy_of_hostOf_mm0Checker hosts {}
  obtain ⟨count, start, long, steps⟩ := mm0Checker_steps_unbounded {} bound
  exact ⟨_, count, _, _, long, map.steps_of_preserves hosting.preserves steps⟩

/-! ## The sentence can be met: the checkers side by side -/

/-- A step of the checkers of all theories side by side: a step of one of
them. -/
inductive SideBySideStep :
    (Σ T : Kernel.Theory, Checking (mm0 T)) → (Σ T : Kernel.Theory, Checking (mm0 T)) →
      Prop where
  | member {T : Kernel.Theory} {state next : Checking (mm0 T)}
      (step : CheckStep (mm0 T) state next) : SideBySideStep ⟨T, state⟩ ⟨T, next⟩

/-- **The checkers of all MM0 theories, side by side.**  A state names its
theory. -/
def sideBySideCheckers : GSLT.{0} where
  Term := Σ T : Kernel.Theory, Checking (mm0 T)
  equations := ⟨Eq, eq_equivalence⟩
  rewrites := SideBySideStep
  rewrites_resp_left := by
    intro state other next same step
    cases same
    exact ⟨next, step, rfl⟩
  rewrites_resp_right := by
    intro state next other step same
    cases same
    exact step

/-- The checker of one theory, among all of them. -/
def sideBySideMap (T : Kernel.Theory) :
    ContextMap (mm0Checker T) sideBySideCheckers.termsAlone :=
  ContextMap.ofTerms (source := certificateChecker (mm0 T))
    (target := sideBySideCheckers.termsAlone) PUnit.unit
    (fun state => (⟨T, state⟩ : Σ T : Kernel.Theory, Checking (mm0 T)))
    (fun {first second} same => congrArg (Sigma.mk T) (same : first = second))

/-- It is hosting. -/
theorem sideBySideMap_hosting (T : Kernel.Theory) : (sideBySideMap T).Hosting :=
  (ContextMap.ofTerms_hosting_iff (source := certificateChecker (mm0 T))
    (target := sideBySideCheckers.termsAlone) PUnit.unit
    (fun state => (⟨T, state⟩ : Σ T : Kernel.Theory, Checking (mm0 T)))
    (fun {first second} same => congrArg (Sigma.mk T) (same : first = second))).mpr
    ⟨fun _ _ same => eq_of_heq (Sigma.mk.inj same).2,
      fun _ _ step => SideBySideStep.member step,
      fun _ _ step => by
        cases step with
        | member inner => exact ⟨_, inner, rfl⟩⟩

/-- **Positive**, for the sentence: the checkers of all theories side by side
host each of them.  This theory is the guests themselves. -/
theorem sideBySide_hostOf_mm0Checker :
    HostOf sideBySideCheckers.termsAlone MM0Checker .terms .hosting := by
  rintro reading ⟨source, ⟨T, rfl⟩, interface, rfl⟩
  exact ⟨sideBySideMap T, sideBySideMap_hosting T⟩

/-! ## The controls of the MM0 calculus, carried through the check -/

/-- **Positive**: in the theory with one axiom, some certificate of the
constant that the axiom asserts is checked to acceptance. -/
theorem withAxiom_constant_checked :
    ∃ certificate : Certificate (mm0 Controls.withAxiom),
      (mm0Checker Controls.withAxiom).Reaches (interface := PUnit.unit)
        [(derivesJ [] [] Controls.constant, certificate)] [] :=
  (exists_reaches_accepting_iff_derivable (mm0 Controls.withAxiom) _).mpr
    ((mm0 Controls.withAxiom).accepts_iff _ |>.mp Controls.axiom_certified)

/-- **Negative**: in the same theory no certificate of another term symbol
is. -/
theorem withAxiom_other_never_checked :
    ¬ ∃ certificate : Certificate (mm0 Controls.withAxiom),
      (mm0Checker Controls.withAxiom).Reaches (interface := PUnit.unit)
        [(derivesJ [] [] (.term 1), certificate)] [] := fun checked =>
  withAxiom_accepts_constant_only.2
    (((mm0 Controls.withAxiom).accepts_iff _).mpr
      ((exists_reaches_accepting_iff_derivable (mm0 Controls.withAxiom) _).mp checked))

/-- **Negative**: in the theory without the axiom, the check of a computed
leaf that claims the axiom never accepts, whatever fuel the leaf names. -/
theorem missingAxiom_never_checked (fuel : Nat) :
    ¬ (mm0Checker Controls.withoutAxiom).Reaches (interface := PUnit.unit)
      [(theoremJ 0 Controls.axiomDecl,
        .computed ⟨Operation.lookup, ⟨(0 : Nat), Controls.axiomDecl, fuel⟩⟩)] [] :=
  not_reaches_accepting_of_rejected (Controls.missing_axiom_leaf_rejected fuel)

/-- **Negative**, for `MM0Checker`: the proof system of an MM0 theory is no
checker.  A checker has a step, a proof system has none. -/
theorem mm0ProofSystem_not_mm0Checker (T : Kernel.Theory) : ¬ MM0Checker (mm0ProofSystem T) := by
  intro member
  have stepping : ∀ source : ContextTheory.{0}, MM0Checker source →
      ∃ (interface : source.Interface) (term next : source.Term interface),
        source.rewrites term next := by
    rintro _ ⟨other, rfl⟩
    obtain ⟨next, step⟩ := exists_step_of_accepted
      ((accepted_singleton_iff _ _).mpr (witnessCertificate_accepted other))
    exact ⟨PUnit.unit, _, next, step⟩
  obtain ⟨_, _, _, step⟩ := stepping _ member
  exact step

/-! ## The checker with its contexts -/

/-- **The checker of an MM0 theory with its contexts**: the states with named
places. -/
abbrev mm0CheckerWithContexts (T : Kernel.Theory) : ContextTheory.{0} := checkerWithContexts (mm0 T)

/-- The checker of every MM0 theory has a step: the first step of the check
of the witness. -/
theorem mm0Checker_has_step (T : Kernel.Theory) :
    ∃ state next : Checking (mm0 T), CheckStep (mm0 T) state next := by
  obtain ⟨next, step⟩ := exists_step_of_accepted
    ((accepted_singleton_iff _ _).mpr (witnessCertificate_accepted T))
  exact ⟨_, next, step⟩

/-- **The candidate presentation and the checker with its contexts**, for
every theory and every evaluator: no map at all under the linear reading; no
map that preserves steps under the reading with regions; no hosting map under
the cartesian reading. -/
theorem mm0CheckerWithContexts_row (base : BasePremiseEvaluator) (T : Kernel.Theory) :
    IsEmpty (ContextMap (mm0CheckerWithContexts T) (presentedReading base)) ∧
      (∀ map : ContextMap (mm0CheckerWithContexts T) (regionProbe base),
        ¬ map.PreservesTransitions) ∧
      ∀ map : ContextMap (mm0CheckerWithContexts T) (cartesianProbe base), ¬ map.Hosting := by
  obtain ⟨state, next, step⟩ := mm0Checker_has_step T
  have row := probe_checkerWithContexts_row base step
  exact ⟨row.1, row.2.1, fun map => row.2.2 (fun _ => True) map⟩

/-- **The candidate with a run constructor and the checker with its
contexts**, for every theory and under every evaluator of its premises: the
same three cells, the last for every reading.  The reasons are the shape of
its contexts and the sort in which it reduces, not the length of its runs. -/
theorem mm0CheckerWithContexts_run_row (base : BasePremiseEvaluator) (T : Kernel.Theory) :
    IsEmpty (ContextMap (mm0CheckerWithContexts T) (contextTheory base runPresentation)) ∧
      (∀ map : ContextMap (mm0CheckerWithContexts T) (regionRun base),
        ¬ map.PreservesTransitions) ∧
      ∀ (declared : LanguageDef.Contexts.Interface → Prop)
        (map : ContextMap (mm0CheckerWithContexts T)
          ((contextTheory base runPresentation).regionReading declared)), ¬ map.Hosting := by
  obtain ⟨state, next, step⟩ := mm0Checker_has_step T
  exact run_checkerWithContexts_row base step

/-- With its contexts the checker is hosted by none of the three readings
either: a host of it would host the checker on terms. -/
theorem mm0CheckerWithContexts_not_hostedBy_row (base : BasePremiseEvaluator) (T : Kernel.Theory) :
    ¬ HostedBy (mm0CheckerWithContexts T) (presentedReading base) ∧
      ¬ HostedBy (mm0CheckerWithContexts T) (regionProbe base) ∧
        ¬ HostedBy (mm0CheckerWithContexts T) (cartesianProbe base) :=
  ⟨fun hosted => (mm0Checker_not_hostedBy_row base T).1
      (hostedBy_checkerTheory_of_withContexts (mm0 T) hosted),
    fun hosted => (mm0Checker_not_hostedBy_row base T).2.1
      (hostedBy_checkerTheory_of_withContexts (mm0 T) hosted),
    fun hosted => (mm0Checker_not_hostedBy_row base T).2.2
      (hostedBy_checkerTheory_of_withContexts (mm0 T) hosted)⟩

/-- **The transfer, from the checker with its contexts**: a hosting map from
it buys the same. -/
theorem mm0CheckerWithContexts_reaches_image_iff_derives {candidate : ContextTheory.{0}}
    {T : Kernel.Theory} (map : ContextMap (mm0CheckerWithContexts T) candidate)
    (hosting : map.Hosting) (context : Kernel.Context) (hypotheses : List Kernel.Preterm)
    (expression : Kernel.Preterm) :
    (∃ (certificate : Certificate (mm0 T)) (final : candidate.Term (map.interface ())),
        candidate.Reaches
            (map.term (origin := ()) [(derivesJ context hypotheses expression, certificate)])
            final ∧
          (candidate.equations (map.interface ())).r final (map.term (origin := ()) [])) ↔
      Kernel.Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses
        expression :=
  mm0Checker_reaches_image_iff_derives (map.comp (termsInclusion (mm0 T)))
    (hosting.comp (termsInclusion_hosting (mm0 T))) context hypotheses expression

/-! ## The sentence for a candidate with smaller steps -/

/-- **A candidate runs the MM0 checkers**: it runs the check of every theory,
with a nonempty reduction of its own for each step of the check. -/
def RunsMM0Checkers (candidate : ContextTheory.{0}) : Prop :=
  ∀ T : Kernel.Theory, Nonempty (RunsCheck candidate (mm0 T))

/-- A host of the class of the checkers runs them: the sentence with smaller
steps is the weaker one. -/
theorem runsMM0Checkers_of_hostOf {candidate : ContextTheory.{0}}
    (hosts : HostOf candidate MM0Checker .terms .hosting) : RunsMM0Checkers candidate := by
  intro T
  obtain ⟨map, hosting⟩ := hostedBy_of_hostOf_mm0Checker hosts T
  exact ⟨RunsCheck.ofHosting map hosting⟩

/-- **What running the checker of a theory buys**: the image of some
certificate of `context ⊢ expression` reaches the image of the accepting
state exactly when the MM0 kernel derives the judgment. -/
theorem mm0_runsCheck_reaches_iff_derives {candidate : ContextTheory.{0}} {T : Kernel.Theory}
    (runs : RunsCheck candidate (mm0 T)) (context : Kernel.Context)
    (hypotheses : List Kernel.Preterm) (expression : Kernel.Preterm) :
    (∃ (certificate : Certificate (mm0 T)) (final : candidate.Term runs.point),
        candidate.Reaches (runs.image [(derivesJ context hypotheses expression, certificate)])
          final ∧ (candidate.equations runs.point).r final (runs.image [])) ↔
      Kernel.Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses
        expression :=
  (runs.exists_reaches_iff_derivable _).trans (factDerivation_iff context hypotheses expression)

/-- **The candidate presentation runs the checker of no MM0 theory**, under
any of its three readings: the check of the witness asks for five nonempty
reductions in a row, and the candidate has three steps in a row at most. -/
theorem mm0_runsCheck_row (base : BasePremiseEvaluator) (T : Kernel.Theory) :
    IsEmpty (RunsCheck (presentedReading base) (mm0 T)) ∧
      IsEmpty (RunsCheck (regionProbe base) (mm0 T)) ∧
        IsEmpty (RunsCheck (cartesianProbe base) (mm0 T)) :=
  ⟨isEmpty_runsCheck_of_bounded (probeRank base) 3 (fun term => probeRank_le base term)
      (witness_steps T) (by decide),
    isEmpty_runsCheck_of_bounded ((probeRank base).regionReading probeData) 3
      (fun term => probeRank_le base term) (witness_steps T) (by decide),
    isEmpty_runsCheck_of_bounded ((probeRank base).regionReading fun _ => True) 3
      (fun term => probeRank_le base term) (witness_steps T) (by decide)⟩

/-- So it does not run the MM0 checkers. -/
theorem not_runsMM0Checkers_row (base : BasePremiseEvaluator) :
    ¬ RunsMM0Checkers (presentedReading base) ∧ ¬ RunsMM0Checkers (regionProbe base) ∧
      ¬ RunsMM0Checkers (cartesianProbe base) :=
  ⟨fun runs => (runs {}).elim (mm0_runsCheck_row base {}).1.false,
    fun runs => (runs {}).elim (mm0_runsCheck_row base {}).2.1.false,
    fun runs => (runs {}).elim (mm0_runsCheck_row base {}).2.2.false⟩

/-- **Positive**: the checkers side by side run the MM0 checkers. -/
theorem sideBySide_runsMM0Checkers : RunsMM0Checkers sideBySideCheckers.termsAlone :=
  runsMM0Checkers_of_hostOf sideBySide_hostOf_mm0Checker

/-! ## The kernel reading of the candidate -/

/-- **The kernel over a query-first model hosts the checker of no MM0
theory**: its rank is at most three. -/
theorem mm0Checker_not_hostedBy_queryFirstKernel (model : QueryFirstModel) (T : Kernel.Theory) :
    ¬ HostedBy (mm0Checker T) (kernelReading model.toAssemblyModel) :=
  mm0Checker_not_hostedBy_of_bounded (queryFirstKernelRank model) 3
    (fun term => queryFirstKernelRank_le model term) T

/-- **The kernel of a model that carries the checkers beside its base meets
the sentence.**  The hosting power is in the model, which is a parameter of
this reading: the checkers are placed in the base and run there.  It shows
that the sentence has to be asked of a candidate whose model is fixed. -/
theorem guestKernel_hostOf_mm0Checker (model : Model) :
    HostOf (kernelReading (withGuest model sideBySideCheckers)) MM0Checker .terms .hosting := by
  rintro reading ⟨source, ⟨T, rfl⟩, interface, rfl⟩
  exact ⟨(guestMap model sideBySideCheckers).comp (sideBySideMap T),
    (guestMap_hosting model sideBySideCheckers).comp (sideBySideMap_hosting T)⟩

/-! ## The obligations of the kernel, without a certificate -/

/-- **With a local hypothesis, the obligation theory of the kernel has runs
of every length**: as many copies of the hypothesis are resolved one by
one. -/
theorem obligations_steps (T : Kernel.Theory) (context : Kernel.Context)
    {hypotheses : List Kernel.Preterm} {expression : Kernel.Preterm}
    (member : expression ∈ hypotheses) :
    ∀ count : Nat,
      (obligationGSLT T context hypotheses).termsAlone.Steps (interface := PUnit.unit) count
        (List.replicate count expression) []
  | 0 => .zero _
  | count + 1 => by
      obtain ⟨index, lookup⟩ := List.mem_iff_getElem?.mp member
      exact .succ (Resolves.hypothesis ((hypothesis_query_exact _ _ _).mpr lookup))
        (obligations_steps T context member count)

/-- **So the candidate hosts it under none of its three readings**, as soon
as there is a local hypothesis. -/
theorem obligations_not_hostedBy_row (base : BasePremiseEvaluator) (T : Kernel.Theory)
    (context : Kernel.Context) {hypotheses : List Kernel.Preterm} {expression : Kernel.Preterm}
    (member : expression ∈ hypotheses) :
    ¬ HostedBy (obligationGSLT T context hypotheses).termsAlone (presentedReading base) ∧
      ¬ HostedBy (obligationGSLT T context hypotheses).termsAlone (regionProbe base) ∧
        ¬ HostedBy (obligationGSLT T context hypotheses).termsAlone (cartesianProbe base) :=
  ⟨not_hostedBy_presented_of_steps base (interface := PUnit.unit)
      (obligations_steps T context member 4) (by decide),
    not_hostedBy_reading_of_steps base probeData (interface := PUnit.unit)
      (obligations_steps T context member 4) (by decide),
    not_hostedBy_reading_of_steps base (fun _ => True) (interface := PUnit.unit)
      (obligations_steps T context member 4) (by decide)⟩

/-- **The obligation theory converts a goal that has a sort to itself**: the
reflexive conversion is a step.  So it has a cyclic reduction; unlike the
checker of certificates it does not terminate. -/
theorem obligations_cycle (T : Kernel.Theory) (context : Kernel.Context)
    (hypotheses : List Kernel.Preterm) {expression : Kernel.Preterm} {sort : Nat}
    (typed : Kernel.Preterm.HasType T.termSignature context expression [] sort)
    (rest : List Kernel.Preterm) :
    Resolves T context hypotheses (expression :: rest) (expression :: rest) :=
  Resolves.conversion (witness := .refl expression)
    ((conversion_query_exact T context (.refl expression) expression expression sort).mpr
      (.refl typed))

/-- **No theory with a rank hosts the obligation theory of a theory in which
an expression has a sort**, whatever the bound of the rank. -/
theorem obligations_not_hostedBy_of_rank {candidate : ContextTheory.{0}} (ranked : candidate.Rank)
    (T : Kernel.Theory) (context : Kernel.Context) (hypotheses : List Kernel.Preterm)
    {expression : Kernel.Preterm} {sort : Nat}
    (typed : Kernel.Preterm.HasType T.termSignature context expression [] sort) :
    ¬ HostedBy (obligationGSLT T context hypotheses).termsAlone candidate :=
  fun ⟨map, hosting⟩ =>
    map.not_preserves_of_cycle_of_rank ranked (interface := PUnit.unit) (term := [expression])
      (.single (obligations_cycle T context hypotheses typed [])) hosting.preserves

/-- **Positive**, for the cycle: in the theory with one axiom the obligation
of the constant is converted to itself. -/
theorem withAxiom_obligations_cycle :
    Resolves Controls.withAxiom [] [] [Controls.constant] [Controls.constant] :=
  obligations_cycle Controls.withAxiom [] [] (sort := 0)
    (Kernel.Preterm.HasType.term (index := 0) (declaration := ⟨[], 0, ∅⟩) rfl) []

/-- Without declarations and in the empty context no expression has a
sort. -/
theorem not_hasType_empty {expression : Kernel.Preterm} {remaining : Kernel.Context} {sort : Nat} :
    ¬ Kernel.Preterm.HasType (fun _ => none) [] expression remaining sort := by
  intro typed
  induction typed with
  | var found => simp at found
  | term lookup => cases lookup
  | bound _ found _ => simp at found
  | regular _ _ ih _ => exact ih

/-- **Negative**, for the local hypothesis: in the theory without
declarations, in the empty context and without local hypotheses, the
obligation theory has no step at all. -/
theorem obligations_static_empty (state next : List Kernel.Preterm) :
    ¬ Resolves {} [] [] state next := by
  intro step
  cases step with
  | hypothesis computed =>
      have lookup := (hypothesis_query_exact _ _ _).mp computed
      simp at lookup
  | theoremApp lookup _ =>
      have found := (theorem_query_exact _ _ _).mp lookup
      cases found
  | conversion computed =>
      exact not_hasType_empty
        ((conversion_query_exact _ _ _ _ _ _).mp computed).derives.typed.2

/-- **Under a hosting map from the obligation theory, the image of a goal
reaches the image of the empty list exactly when the MM0 kernel derives the
goal.** -/
theorem obligations_reaches_image_iff_derives {candidate : ContextTheory.{0}} (T : Kernel.Theory)
    (context : Kernel.Context) (hypotheses : List Kernel.Preterm)
    (map : ContextMap (obligationGSLT T context hypotheses).termsAlone candidate)
    (hosting : map.Hosting) (goal : Kernel.Preterm) :
    (∃ final, candidate.Reaches (map.term (origin := PUnit.unit) [goal]) final ∧
        (candidate.equations (map.interface PUnit.unit)).r final
          (map.term (origin := PUnit.unit) [])) ↔
      Kernel.Derives T.termSignature T.definitionSignature T.theoremSignature context hypotheses
        goal := by
  refine (hosting.reaches_image_iff (interface := PUnit.unit) [goal] []).trans ?_
  refine Iff.trans ?_ (singleton_discharge_iff T context hypotheses goal)
  refine Iff.trans ?_ (Meredith.multiStep_iff_reflTransGen _ _ _).symm
  constructor
  · rintro ⟨final, reaches, same⟩
    obtain rfl : final = [] := same
    exact reaches
  · intro reaches
    exact ⟨[], reaches, rfl⟩

#print axioms kernelRule_application
#print axioms memberCertificate_accepted
#print axioms localCertificate_accepted
#print axioms localCertificate_nodes
#print axioms mm0Checker_steps
#print axioms mm0Checker_steps_unbounded
#print axioms witness_steps
#print axioms witness_rejected_for_other
#print axioms mm0Checker_not_preserves_of_bounded
#print axioms mm0Checker_not_hostedBy_of_bounded
#print axioms mm0Checker_not_preserves_row
#print axioms mm0Checker_not_hostedBy_row
#print axioms hostOf_mm0Checker_contexts_iff_terms
#print axioms mm0Checker_class_row
#print axioms mm0Checker_reaches_image_iff_derives
#print axioms derives_iff_reaches_of_hostOf
#print axioms steps_unbounded_of_hostOf_mm0Checker
#print axioms sideBySideMap_hosting
#print axioms sideBySide_hostOf_mm0Checker
#print axioms withAxiom_constant_checked
#print axioms withAxiom_other_never_checked
#print axioms missingAxiom_never_checked
#print axioms mm0ProofSystem_not_mm0Checker
#print axioms mm0Checker_has_step
#print axioms mm0CheckerWithContexts_row
#print axioms mm0CheckerWithContexts_run_row
#print axioms mm0CheckerWithContexts_not_hostedBy_row
#print axioms mm0CheckerWithContexts_reaches_image_iff_derives
#print axioms runsMM0Checkers_of_hostOf
#print axioms mm0_runsCheck_reaches_iff_derives
#print axioms mm0_runsCheck_row
#print axioms not_runsMM0Checkers_row
#print axioms sideBySide_runsMM0Checkers
#print axioms mm0Checker_not_hostedBy_queryFirstKernel
#print axioms guestKernel_hostOf_mm0Checker
#print axioms obligations_steps
#print axioms obligations_not_hostedBy_row
#print axioms obligations_cycle
#print axioms obligations_not_hostedBy_of_rank
#print axioms withAxiom_obligations_cycle
#print axioms obligations_static_empty
#print axioms obligations_reaches_image_iff_derives

end Mettapedia.Logic.HostingStyles.Guests
