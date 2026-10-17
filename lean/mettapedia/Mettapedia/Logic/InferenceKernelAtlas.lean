import Mettapedia.Logic.InferenceBasisControls
import Mettapedia.Logic.InferenceBasisCompilerControls
import Mettapedia.GSLT.LanguageDef.InferenceBasisBoundary
import Mettapedia.GSLT.LanguageDef.KernelCheckingClasses
import Mettapedia.GSLT.LanguageDef.CertificateGSLTClassifyingCategory
import Mettapedia.GSLT.LanguageDef.HeuristicEvidence
import Mettapedia.Computability.FuelledConversionEvidence
import Mettapedia.Languages.Metamath.CheckingDiscipline
import Mettapedia.Languages.MM0.CheckingDiscipline
import Mettapedia.Languages.HOLLight.KernelAtlas
import Mettapedia.Languages.Megalodon.FuelledConversionProfile
import Mettapedia.Languages.Megalodon.FuelledConversionWitness
import Mettapedia.GSLT.LanguageDef.StandardSemanticAuthorityProfiles
import Mettapedia.Logic.HOL.ConversionTiers
import Mettapedia.Logic.HOL.CheckableFragment
import Mettapedia.Languages.HOLLight.RetainedElaboration
import Mettapedia.Languages.MM0.Kernel.SubstitutionStability
import Mettapedia.GSLT.Dedukti.ConstructionsConsistency
import Mettapedia.OSLF.MeTTaIL.GeneralRewriteRecipeExecution
import Mettapedia.Languages.ProcessCalculi.RhoCalculus.NativeExecution
import Mettapedia.Languages.MeTTa.EquationKernel.Execution
import Mettapedia.Languages.MM0.Formats.MMB.MachineCost
import Mettapedia.Languages.Lean.HintedHeadConversion
import Mettapedia.GSLT.Logic.PropositionalLRAT
import Mettapedia.Logic.ProofSharingBounds
import Mettapedia.Logic.PropositionalHilbertChecking
import Mettapedia.Logic.PropositionalExtension
import Mettapedia.Logic.IntuitionisticDecision
import Mettapedia.Logic.EqualityRecipe
import Mettapedia.Languages.Lean.Lean4LessCheckerBoundary
import Mettapedia.Languages.VibeITP.CheckingMachine
import Mettapedia.Languages.Metamath.CheckingMachine
import Mettapedia.Languages.GuardedAtomRule.CheckingMachine
import Mettapedia.Logic.RuleMulticategoryKernels
import Mettapedia.Logic.MultiPremiseSteps
import Mettapedia.GSLT.LanguageDef.CertificateGSLTFreeMulticategory
import Mettapedia.GSLT.Logic.PropositionalLRATActions
import Mettapedia.GSLT.Logic.KripkeTruthChecking
import Mettapedia.Languages.HOLLight.FirstOrder.PortableKernel

/-!
# Inference kernels: primitive bases, evidence and resources

`KripkeTruth.Checking` is a separate partial-truth profile, not a change of
every object logic. Its ten local codes present the existing strong Kleene
evidence constructors exactly. Grounded signed judgments coincide with closed
proofs and accepted certificates. For finite judgment domains, the original
least-fixed-point decision agrees with that certificate authority; completed
ungroundedness is kept distinct from an unfinished checking frontier.

This entry point joins the independently checked coordinates of the kernel
atlas. Rule generation compares consequences under open hypotheses; explicit
templates construct certificates; executed translations compare machine costs.
The concrete Metamath, MM0 and HOL Light observers describe their actual
interfaces without turning an operation inventory into a complexity theorem.

Finite-budget checking separates acceptance, refusal and exhaustion. Explicit
conversion paths compose even when a fixed search budget is insufficient to
rediscover the composite. Arbitrary proposed proofs retain the same checking
authority and model soundness.

The logical core precedes any checking machine: `Logic.Derivation` gives
judgments, finitary rule instances and exact finite witnesses, while the
open-derivation owners retain hypotheses and compose evidence into premise
slots. Multiple-premise composition is multicategorical; unary rewrites give
paths. Exchange, weakening, contraction and equations between proofs belong
to the selected presentation, rather than being silently imposed by replay.
`CertificateGSLT` gives an authored finite presentation of this structure.
Its existing classifying category identifies closed source proof terms with
arrows from the empty premise context to a singleton goal via the executable
`ClassifyingContext.closedDerivationEquiv`, preserving the proof in both
directions. VibeITP and Metamath expose their source comparisons at this
proof-category level as well as through graph and machine realizations.

Multiple-premise composition is now a theorem rather than a reading. Open
derivations over a proof-relevant rule signature form the free cartesian
multicategory on it (`RuleSignature.universal`); kernel derivability is closed
derivability there (`RuleWitness.derivable_iff_derives`); accepted certificate
trees are exactly its closed morphisms (`RuleWitness.closedEquiv`); every node of
an accepted shared graph unfolds to one (`RuleWitness.unfold_root`). Authored
calculi present the same structure on their rule applications
(`CertificateGSLT.OpenDerivation.termEquiv`, `toTerm_bind`). Holes may be
discarded or reused, so the structure is cartesian; closed derivations are
linear (`Term.closed_linear`). Graph checking and unfolding are invariant under
every order that keeps premises before consumers
(`DerivationGraph.replayWith_permute_iff`, `RuleWitness.unfold_permute`), and
reuse across a theory change revalidates exactly the used instances
(`DerivationGraph.revalidate_iff`). Translations are multifunctors: the
intuitionistic-to-classical and classical-to-extended inclusions are faithful,
the second conservative and the first not reflecting
(`Hilbert.inclusion_not_reflecting`, `Extension.inclusion_conservative`); HOL
Light's rule multicategory maps into its first-order calculus, preserving and
reflecting derivability (`HOLLight.FirstOrder.translation`,
`translation_reflects`). Logical work adds over substitution
(`Term.size_subst`); affine rule images are linear on trees
(`RuleSignature.lift_size_le`), while one contracting image is exponential on
trees and linear on graphs (`Contraction.contraction_gap`). Atomic
multi-pattern steps without consumption are graph replay
(`MultiPremiseSteps.run_monotone`); consumed occurrences cannot be reused, and
the split/join process cannot be represented by the tree-shaped single-wire-cut
grammar while preserving generator and wire counts
(`MultiPremiseSteps.consumed_not_cited`, `process_not_polycategorical`). This
does not exclude other categorical presentations. LRAT's RUP actions are retained as multi-premise
rule instances (`PropositionalLRATActions.check_sound`), and RAT additions are
extensions rather than instances (`rat_not_rule_instance`).

The native execution objects use the existing `ObservedMachine` category,
with their own occurrence and verdict types. The authored GSLT recipe and
MeTTa equation workers each inspect one original DAG node and retain refusal
with its suffix. Their verdicts agree with their original checkers. Actual
terminated authored checking is equivalent to the existing reaching native
type (`GeneralRewriteRecipeExecution.exists_finished_iff_reachingNativeType`),
including the original equations and an equation-respecting target predicate. The rho
worker inspects its original inference trees, with formation checked at the
request boundary. MM0 exposes its original command/unification microsteps;
HOL Light exposes its original registered-event receiver. The Lean4Lean
instance is the executable beta/delta/head profile, with explicit normalizing
strategy hints. It is not the full Lean kernel. These are objects at their
declared observation interfaces; morphisms between different interfaces
still require explicit observation maps and resource simulations.

Storage navigation is a further realization. The borrowed cursor preserves
source addresses and a checked prefix; it is neither a primitive proof rule
nor a required representation of every native checker. A stack, stream,
tree focus or dependency schedule may realize the same evidence structure.
Focus becomes a semantic observation only when explicitly selected and
preserved by a comparison. The cursor adapters below depend on their source
theories, while those theories remain independent of cursor machinery.

VibeITP's existing authored kernel also uses the common retained source-address
checker (`VibeITP.CheckingMachine.kernelCheckingObject`). Its graph coverage and retained
roots agree with its independent static judgment under `Hosted`; its auxiliary
term-operation judgments are preserved as well. `kernelModule_read` recovers
the exact theory-extended package through the verified portable module reader
and the original validator. This data surface is distinct from the upstream
theory-builder grammar; neither native C refinement nor binary protocol
correspondence follows merely from reading a module.
Metamath's projected snapshot also instantiates that cursor. Its accepted graph
judgments coincide with successful original `DB.stepNormal` label folds under
the established prefix-projection and empty-stack conditions. Portable loading
revalidates the complete snapshot, and target-facing export checks freshness;
parser provenance and compressed-proof execution retain their separate laws.
The guarded atom-rule calculus uses its original `Evidence.Source.presentation`
on the same cursor, with graph coverage and retained-root soundness against
its original conditional-atom meaning. This preserves the calculus's accurate
name and makes no claim about HE or PeTTa evaluation.

Algorithmic Lean-style judgment and ideal typing/equality are separate
scopes (`Lean4LessCheckerBoundary.IdealBoundary`). Reproducible budgets
enumerating a fixed algorithm do not fill gaps in its ideal interpretation.
Explicit equality recipes are exact for the generated equivalence relation;
ideal completeness requires a further generation theorem. Typed reflexivity
uses a formed-expression fibre rather than arbitrary raw syntax.

Checked reconstruction accepts a partial producer's result only after the
destination checks it (`Checker.reconstruct_eq_some`). This yields an
elaboration edge without assuming heuristic completeness. Reproducible fuel,
checkpoints and full traces are connected by exact endpoint and tick-count
laws in `Machines.ExecutionHints`; replay always continues
its computed internal state. Such checkpoints do not by themselves accelerate
the computation between them.

`ProofSharingBounds` supplies a fixed calculus with a genuine obstruction to
every polynomial-size DAG-to-tree translation: every accepted tree has
`2^(n+1)-1` nodes, while a checked DAG has `n+1` rows and quadratic size even
with unary indices. This is a representation separation for that calculus,
not a Frege/extended-Frege separation. `PropositionalLRAT` reuses the verified
standard-library RUP/RAT/deletion checker, preserving the native clause
semantics. Accepted refutations entail native resolution derivations; that
completeness argument supplies no polynomial LRAT-to-resolution compiler.
`PropositionalHilbertChecking` supplies native finite rule codes and tree/DAG
coverage for Foundation's standard intuitionistic and classical Hilbert
calculi, with a computable elaborator into the existing retained `PropDeriv`
terms. Excluded middle is admitted only in the classical rule profile.
`PropositionalExtension` adds fresh literal definitions, proves conservative
classical authority and tree/DAG coverage, and embeds Frege DAGs without
changing their replay verdict or expanding references. Its literal-unfolding
family has polynomial encoded source size and exactly exponential output
tree size. This is not an unrestricted Frege lower bound.
`IntuitionisticDecision` validates finite persistent Kripke countermodels,
proves coverage of non-theorems, and supplies an executable terminating
decision procedure by enumerating proof and countermodel certificates.
This exhaustive search is separate from native proof checking and has no
practical or polynomial-time claim. Executed Cook--Reckhow bounds remain
separate obligations.

Larger kernels elaborate into what smaller ones check. Accepted HOL Light proof
graphs elaborate, by a computable function, into retained natural-deduction
proofs (`HOLLight.RetainedElaboration.elaborateProved_correct`). For simply
typed beta, fuelled and explicit conversion evidence elaborate into each other
(`HOL.ConversionTiers.fuelledAboveExplicit`, `explicitAboveFuelled`, which rests
on strong normalization and confluence); retaining the explicit evidence costs
at most, and in the worst case exactly, an exponential in the fuelled
certificate's bit size (`fuelledElaboration_size`, `Controls.compression_gap`).
Binder hints make membership in the normalizing fragment decidable by one pass,
and a certificate outside it is refused before any conversion is run
(`HOL.CheckableFragment.check_outside`, `Controls.omega_outside`). MM0
derivability is stable under admissible substitution, which composes, so it is
a presheaf on contexts (`MM0.Kernel.Contextual.derivableFace`); checked proof
witnesses move along the same substitutions and form a presheaf over it
(`MM0.Kernel.Contextual.witnessFace`), onto which forgetting the witness is
surjective at every context (`MM0.Kernel.Contextual.forgetWitness_surjective`).
The calculus of constructions, the top of the lambda cube, is consistent
(`GSLT.Dedukti.ConstructionsModel.constructions_consistent`, by a
proof-irrelevant model), while a universal sort `∗ : ∗` is not.

The standard-semantics examples have precise scopes: universal affine
inequalities over natural numbers, and recurrence from a selected root under
a fixed controller on a finite state space. They do not supply general
Presburger, S1S or S2S decision procedures. The atlas likewise does not assert
a universal weakest kernel, universal polynomial equivalence, full Lean
refinement, or completion of the physical calculus-to-HOL compiler.
-/
