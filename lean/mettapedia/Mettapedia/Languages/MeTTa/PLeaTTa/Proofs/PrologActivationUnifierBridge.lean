-- SPDX-License-Identifier: Apache-2.0

/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologActivationUnifierBridge
Purpose: Rule out executable head-unification failure for one independently
  resolved, supported local clause occurrence.
Trusted boundary: none
Main exports:
  ActivatedTaskAgrees,
  SupportedPreparedCandidateAgrees.unifyB_direct_of_headResolution,
  SupportedPreparedCandidateAgrees.unifyB_residual_variant_of_headResolution,
  SupportedPreparedCandidateAgrees.unifyB_body_residual_variant_of_headResolution,
  SupportedPreparedCandidateAgrees.unifyB_body_cumulative_trimmed_of_headResolution,
  SupportedPreparedCandidateAgrees.unifyB_body_continuation_support_of_headResolution,
  SupportedPreparedCandidateAgrees.unifyB_complete_of_headResolution,
  matched_clause_eq_ok_task_correspondence
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologCallPayloadBridge
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologMguComposition

namespace Mettapedia.Languages.MeTTa.PLeaTTa.PrologActivationUnifierBridge

open Mettapedia.Languages.MeTTa.PLeaTTa.Source (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.OpenSubstitution
open PeTTaSpec.PrologCore.Canonical
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.GoalSemantics
open CompilerAdequacy
open CompilerSubstitutionAdequacy
open OpenBindingAgreement
open PrologStateBridge
open PrologCallEntryBridge
open PrologPrefilterBridge
open PrologCallPayloadBridge
open PrologMguBridge
open PrologMguOpenAgreement
open PrologMguTopology
open PrologMguVariant
open PrologGoalAlpha
open PrologGoalMguVariant
open PrologMguComposition

/-! ## One semantically matched prepared occurrence -/

/-- Exact payload relation for the left task installed by a matched local
clause.

The independent task carries its cumulative binding separately from its raw
body.  The executable task carries the corresponding trimmed runtime
substitution beside the freshened body.  Keeping both components explicit
avoids an idempotence assumption and gives the eventual Search/OpenConf
simulation a relation over the actual successor payloads. -/
def ActivatedTaskAgrees
    (alpha support : List (LogicVar × String)) (barrier : Nat)
    (canonical : TreeSubstitution) (referenceBase : Substitution)
    (runtime : Subst) (entered : EnteredClause)
    (executableGoals : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal) : Prop :=
  SharedRuntimeAlpha alpha ∧
    canonical.WellFormed ∧
    entered.bindings =
        TreeSubstitution.reify canonical ++ referenceBase ∧
    AlphaGoalsCumulativeResidualVariantAgreesOn
      alpha support barrier canonical referenceBase runtime
      entered.rawBody executableGoals

/-- A semantic head resolution at one real prepared clause occurrence
constructs the actual executable MGU and exposes the complete
cross-representation witness.  The returned flattened MGU may orient residual
aliases differently from the independently ordered source MGU, so the theorem
proves an acyclic open valuation plus mutual semantic factorization rather
than false association-list equality.  The exact installed `unifyB` state
remains visible; `trimFor` is deliberately outside this theorem. -/
theorem SupportedPreparedCandidateAgrees.unifyB_direct_of_headResolution
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution}
    (query :
      NormalizedCallAgrees queryAlpha cursor
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding result))
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (resolved : HeadResolution branch independentResult) :
    ∃ alpha canonical flattened generated installed,
      SharedRuntimeAlpha alpha ∧
      AlphaGoalsAgree alpha barrier branch.body
        (freshenResolutionClause
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body ∧
      SharedAlphaEquationsAgree alpha branch.normalizedHeadEquations
          ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
          (((freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).params ++
            [(freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).result]).map
            (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) ∧
      independentResult =
        TreeSubstitution.reify canonical ++ branch.bindings ∧
      OrderedTreeMgu
        (denoteEquations branch.normalizedHeadEquations) canonical ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)))
          (.expr
            (((freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]).map
              (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))) =
        some generated ∧
      AlphaTreeSubstitutionAgrees alpha flattened generated ∧
      TreeSubstitutionTopological flattened ∧
      Nonempty (Mettapedia.Languages.MeTTa.PLeaTTa.SubstTopological generated) ∧
      AlphaValuationAgrees alpha flattened generated ∧
      TreeIsMgu flattened
        (denoteEquations branch.normalizedHeadEquations) ∧
      TreeFactorsThrough flattened canonical ∧
      TreeFactorsThrough canonical flattened ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result])) =
        some installed ∧
      installed =
        match generated with
        | [] => binding
        | _ :: _ => Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.compose generated binding := by
  cases agreement with
  | intro reference freshSeed executable base encoding bodySupported =>
      have startsAbove :
          cursor.reservationStart ≤
            (reference.clause.freshCopy freshSeed).firstFresh := by
        have starts := wellFormed.1.start_le_member_first member
        simpa [preparedBranchOf] using starts
      have queryBelowFresh :
          GeneratedBelow
            (reference.clause.freshCopy freshSeed).firstFresh
            (queryAlpha.map Prod.fst) :=
        queryReferenceBelow.mono startsAbove
      have bindingBelowStart :
          GeneratedBelow cursor.reservationStart
            (substitutionVariables cursor.bindings) := by
        intro index indexMember
        exact wellFormed.2.1 index
          (List.mem_append_right _ indexMember)
      have bindingBelowFresh :
          GeneratedBelow
            (reference.clause.freshCopy freshSeed).firstFresh
            (substitutionVariables cursor.bindings) :=
        bindingBelowStart.mono startsAbove
      have domains :
          Substitution.DomainsBelow
            (reference.clause.freshCopy freshSeed).firstFresh
            cursor.bindings :=
        Substitution.domainsBelow_of_generatedBelow bindingBelowFresh
      have headAgreement :=
        freshCopy_prefilter_head_alpha_agrees base freshSeed
      rcases headAgreement.outputLast with
        ⟨referenceParameters, referenceResult, referenceArguments,
          parameterAgreement, resultAgreement⟩
      have fullClauseAgreement :
          AlphaTermsAgree
            (prefilterAlpha reference.clause freshSeed)
            (reference.clause.freshCopy freshSeed).clause.arguments
            (clause.params ++ [clause.result]) := by
        rw [referenceArguments]
        exact AlphaTermsAgree.append_singleton
          parameterAgreement resultAgreement
      have generated :
          Terms.GeneratedAtLeast
            (reference.clause.freshCopy freshSeed).firstFresh
            (reference.clause.freshCopy freshSeed).clause.arguments :=
        AlphaTermsAgree.generatedAtLeast_of_graph
          fullClauseAgreement (prefilterAlpha_generated_range encoding)
      have stable :
          cursor.bindings.applyTerms
              (reference.clause.freshCopy freshSeed).clause.arguments =
            (reference.clause.freshCopy freshSeed).clause.arguments :=
        Substitution.applyTerms_eq_self_of_generatedAtLeast domains generated
      have normalizedLengths :
          (cursor.bindings.applyTerms cursor.arguments).length =
            (reference.clause.freshCopy freshSeed).clause.arguments.length := by
        have queryLength := AlphaTermsAgree.length_eq query.arguments
        have clauseLength := AlphaTermsAgree.length_eq fullClauseAgreement
        simp only [List.length_append, List.length_singleton,
          List.length_map] at queryLength clauseLength
        omega
      have rawLengths :
          cursor.arguments.length =
            (reference.clause.freshCopy freshSeed).clause.arguments.length := by
        simpa only [Substitution.applyTerms_length] using normalizedLengths
      have normalizedEquations :
          (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).normalizedHeadEquations =
            argumentEquations
              (cursor.bindings.applyTerms cursor.arguments)
              (cursor.bindings.applyTerms
                (reference.clause.freshCopy freshSeed).clause.arguments) :=
        preparedBranchOf_normalizedHeadEquations_eq
          cursor.callGeneration cursor.arguments cursor.bindings freshSeed
          reference rawLengths
      rcases resolved with
        ⟨extension, ⟨canonical, derivation, extensionShape⟩, resultShape⟩
      have freshened :=
        freshenClause_actual_alpha_agrees
          base encoding freshSeed
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding qterm
          seed barrier
      have normalized :=
        Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.FreshenedClauseAlphaAgrees.normalizedSharedHeadEquations
          freshened rfl queryShared query.arguments queryBelowFresh
          queryExecutableLive highWater normalizedLengths
      have branchAgreement :
          SharedAlphaEquationsAgree
            (queryAlpha ++
              RuntimeAlpha.graph
                (referenceFreshTargets
                  (reference.clause.freshCopy freshSeed).firstFresh
                  reference.clause.variables)
                (executableFreshTargets
                  (resolutionFreshSuffix
                    (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding
                    qterm seed)
                  reference.clause.variables))
            (preparedBranchOf cursor.callGeneration cursor.arguments
              cursor.bindings freshSeed reference).normalizedHeadEquations
            ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
            (((freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]).map
              (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) := by
        rw [normalizedEquations, stable]
        exact normalized.2
      obtain
        ⟨flattened, generatedRuntime, installed, generatedExact,
          generatedAgreement, flattenedTopological, generatedTopological,
          generatedValuation, flattenedMgu, flattenedFactors,
          canonicalFactors, installedExact, installedShape⟩ :=
        Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguDirectSimulation.OrderedTreeMgu.unifyB_exists_alpha_mgu
          binding normalized.1 branchAgreement derivation
      refine
        ⟨_, canonical, flattened, generatedRuntime, installed,
          normalized.1, ?_, branchAgreement, ?_, derivation, generatedExact,
          generatedAgreement, flattenedTopological, generatedTopological,
          generatedValuation, flattenedMgu, flattenedFactors,
          canonicalFactors, installedExact, installedShape⟩
      ·
        have bodyAgreement :=
          freshenClause_body_alpha_agrees
            base bodySupported freshSeed
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier
        have enlarged :=
          Mettapedia.Languages.MeTTa.PLeaTTa.PrologGoalMguVariant.AlphaGoalsAgree.mono
            (fun pair pairMember =>
              List.mem_append_right queryAlpha pairMember)
            bodyAgreement
        simpa [preparedBranchOf] using enlarged
      simpa [extensionShape] using resultShape

/-- The direct activation witness, quotiented only by semantic residual
variation.  This is the form consumed by body simulation: it keeps the exact
generated and installed executable substitutions, while hiding the
irrelevant orientation of the independently ordered MGU behind mutual
instantiation.  Ground observations remain exact by
`AlphaResidualVariantAgrees.apply_of_canonical_ground`. -/
theorem
    SupportedPreparedCandidateAgrees.unifyB_residual_variant_of_headResolution
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution}
    (query :
      NormalizedCallAgrees queryAlpha cursor
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding result))
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (resolved : HeadResolution branch independentResult) :
    ∃ alpha canonical generated installed,
      SharedRuntimeAlpha alpha ∧
      AlphaGoalsAgree alpha barrier branch.body
        (freshenResolutionClause
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body ∧
      SharedAlphaEquationsAgree alpha branch.normalizedHeadEquations
          ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
          (((freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).params ++
            [(freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).result]).map
            (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) ∧
      independentResult =
        TreeSubstitution.reify canonical ++ branch.bindings ∧
      OrderedTreeMgu
        (denoteEquations branch.normalizedHeadEquations) canonical ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)))
          (.expr
            (((freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]).map
              (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))) =
        some generated ∧
      AlphaResidualVariantAgrees alpha canonical generated ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result])) =
        some installed ∧
      installed =
        match generated with
        | [] => binding
        | _ :: _ => Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.compose generated binding := by
  obtain
    ⟨alpha, canonical, flattened, generated, installed, shared,
      bodyControl, equationsAgreement, independentShape, ordered, generatedExact,
      generatedAgreement, flattenedTopological, generatedTopological,
      generatedValuation, _flattenedMgu, flattenedFactors,
      canonicalFactors, installedExact, installedShape⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologActivationUnifierBridge.SupportedPreparedCandidateAgrees.unifyB_direct_of_headResolution
      query wellFormed member agreement arity queryShared
      queryReferenceBelow queryExecutableLive highWater resolved
  have canonicalTopological :
      TreeSubstitutionTopological canonical :=
    PrologMguTopology.OrderedTreeMgu.binding_topological ordered
  have variantAgreement :
      AlphaResidualVariantAgrees alpha canonical generated :=
    ⟨flattened, ⟨canonicalFactors, flattenedFactors⟩,
      canonicalTopological, flattenedTopological,
      generatedAgreement.variablesSatisfy,
      generatedTopological, generatedValuation⟩
  exact
    ⟨alpha, canonical, generated, installed, shared,
      bodyControl, equationsAgreement, independentShape, ordered, generatedExact,
      variantAgreement, installedExact, installedShape⟩

/-- A supported body certificate closes the first source-to-runtime
activation payload: the exact freshened body control structure and every
alpha-linked term leaf share one residual-MGU representative.

The result is deliberately about the generated head MGU.  Relating the
installed `compose generated binding` state and its later `trimFor` projection
to the cumulative independent binding remains a separate obligation. -/
theorem
    SupportedPreparedCandidateAgrees.unifyB_body_residual_variant_of_headResolution
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution}
    (query :
      NormalizedCallAgrees queryAlpha cursor
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding result))
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (resolved : HeadResolution branch independentResult) :
    ∃ alpha canonical generated installed,
      SharedRuntimeAlpha alpha ∧
      SharedAlphaEquationsAgree alpha branch.normalizedHeadEquations
          ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
          (((freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).params ++
            [(freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).result]).map
            (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) ∧
      independentResult =
        TreeSubstitution.reify canonical ++ branch.bindings ∧
      OrderedTreeMgu
        (denoteEquations branch.normalizedHeadEquations) canonical ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)))
          (.expr
            (((freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]).map
              (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))) =
        some generated ∧
      AlphaResidualVariantAgrees alpha canonical generated ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result])) =
        some installed ∧
      installed =
        (match generated with
        | [] => binding
        | _ :: _ => Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.compose generated binding) ∧
      AlphaGoalsResidualVariantAgrees alpha barrier canonical generated
        branch.body
        (freshenResolutionClause
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body := by
  obtain
    ⟨alpha, canonical, generated, installed, shared, bodyControl,
      equationsAgreement, independentShape, ordered, generatedExact,
      generatedAgreement, installedExact, installedShape⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologActivationUnifierBridge.SupportedPreparedCandidateAgrees.unifyB_residual_variant_of_headResolution
      query wellFormed member agreement arity queryShared
      queryReferenceBelow queryExecutableLive highWater resolved
  exact
    ⟨alpha, canonical, generated, installed, shared,
      equationsAgreement, independentShape, ordered, generatedExact,
      generatedAgreement, installedExact, installedShape,
      Mettapedia.Languages.MeTTa.PLeaTTa.PrologGoalMguVariant.AlphaResidualVariantAgrees.goals
        generatedAgreement bodyControl⟩

/-- The first cumulative local-clause activation theorem.

The executable head MGU is composed with the incoming runtime binding and
then trimmed exactly as `Step.eq_ok` trims it.  The independent side retains
the source ordering `canonical ++ branch.bindings`.  Because the two MGU
implementations may orient a residual alias differently, agreement is stated
through one shared residual representative on an explicit observable
support.

The final support conditions are intentionally exposed.  A later
Search-to-machine correspondence must prove that its live continuation
selects only source identities fixed by `branch.bindings`, runtime names
outside `binding`, and runtime names retained by `trimFor`; this theorem does
not manufacture those facts from an arbitrary support. -/
theorem
    SupportedPreparedCandidateAgrees.unifyB_body_cumulative_trimmed_of_headResolution
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution}
    (query :
      NormalizedCallAgrees queryAlpha cursor
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding result))
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (bindingTopological : Mettapedia.Languages.MeTTa.PLeaTTa.SubstTopological binding)
    (resolved : HeadResolution branch independentResult) :
    ∃ alpha canonical generated installed,
      SharedRuntimeAlpha alpha ∧
      independentResult =
        TreeSubstitution.reify canonical ++ branch.bindings ∧
      OrderedTreeMgu
        (denoteEquations branch.normalizedHeadEquations) canonical ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)))
          (.expr
            (((freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]).map
              (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))) =
        some generated ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result])) =
        some installed ∧
      ∀ support,
        (∀ pair, pair ∈ support → pair ∈ alpha) →
        AlphaReferenceIdentitiesFixed support branch.bindings →
        AlphaRuntimeNamesAvoid support binding →
        AlphaRuntimeNamesLive support
          ((freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm →
        AlphaGoalsCumulativeResidualVariantAgreesOn
          alpha support barrier canonical branch.bindings
          (Mettapedia.Languages.MeTTa.PLeaTTa.trimFor
            ((freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).body ++ rest)
            qterm installed)
          branch.body
          (freshenResolutionClause
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).body := by
  obtain
    ⟨alpha, canonical, generated, installed, shared, bodyControl,
      _equationsAgreement, independentShape, ordered, generatedExact,
      generatedAgreement, installedExact, installedShape⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologActivationUnifierBridge.SupportedPreparedCandidateAgrees.unifyB_residual_variant_of_headResolution
      query wellFormed member agreement arity queryShared
      queryReferenceBelow queryExecutableLive highWater resolved
  have resolvedAvoids (atom : Atom) :
      Mettapedia.Languages.MeTTa.PLeaTTa.AtomAvoids binding (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding atom) := by
    intro name nameMember
    exact bindingTopological.subst_resolvesDomain
      binding atom name nameMember
  have leftAvoids :
      Mettapedia.Languages.MeTTa.PLeaTTa.AtomAvoids binding
        (.expr ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))) := by
    simpa only [Mettapedia.Languages.MeTTa.PLeaTTa.subst_expr] using
      resolvedAvoids (.expr (args ++ [result]))
  have rightAvoids :
      Mettapedia.Languages.MeTTa.PLeaTTa.AtomAvoids binding
        (.expr
          (((freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).params ++
            [(freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).result]).map
            (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))) := by
    simpa only [Mettapedia.Languages.MeTTa.PLeaTTa.subst_expr] using
      resolvedAvoids
        (.expr
          ((freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).params ++
            [(freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).result]))
  have generatedAvoidsBinding :
      Mettapedia.Languages.MeTTa.PLeaTTa.SubstEntriesAvoid binding generated :=
    Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact_avoidsExternal
      binding
      (.expr ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)))
      (.expr
        (((freshenResolutionClause
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).params ++
          [(freshenResolutionClause
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
            qterm seed barrier clause).result]).map
          (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)))
      generated leftAvoids rightAvoids generatedExact
  refine
    ⟨alpha, canonical, generated, installed, shared, independentShape,
      ordered, generatedExact, installedExact, ?_⟩
  intro support included referenceFixed runtimeAvoids live
  have supportedResidual :
      AlphaResidualVariantAgreesOn alpha support canonical generated :=
    generatedAgreement.on included
  have cumulative :
      AlphaCumulativeResidualVariantAgreesOn
        alpha support canonical branch.bindings installed :=
    have installedShape' :
        installed =
          Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguComposition.installGenerated generated binding := by
      exact installedShape
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguComposition.AlphaResidualVariantAgreesOn.carry
      (canonical := canonical) (generated := generated)
      (base := binding) (installed := installed)
      (referenceBase := branch.bindings)
      supportedResidual bindingTopological generatedAvoidsBinding
      referenceFixed runtimeAvoids installedShape'
  exact
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguComposition.AlphaGoalsCumulativeResidualVariantAgreesOn.trimFor
      ⟨bodyControl, cumulative⟩ live

/-- Clause activation with all carried-state *safety* conditions discharged
by the continuation itself.

The selected support contains precisely the alpha links whose source
identities are absent from the carried source keys, whose runtime names are
absent from the carried executable substitution, and whose runtime names are
live roots of the body-plus-tail continuation.  It discharges the preceding
theorem's safety premises for that particular support, but intentionally does
not claim that the conservative support contains every future observable.
That completeness property belongs to the caller/compiler invariant. -/
theorem
    SupportedPreparedCandidateAgrees.unifyB_body_continuation_support_of_headResolution
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution}
    (query :
      NormalizedCallAgrees queryAlpha cursor
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding result))
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (bindingTopological : Mettapedia.Languages.MeTTa.PLeaTTa.SubstTopological binding)
    (resolved : HeadResolution branch independentResult) :
    ∃ alpha canonical generated installed,
      SharedRuntimeAlpha alpha ∧
      independentResult =
        TreeSubstitution.reify canonical ++ branch.bindings ∧
      OrderedTreeMgu
        (denoteEquations branch.normalizedHeadEquations) canonical ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)))
          (.expr
            (((freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result]).map
              (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))) =
        some generated ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result])) =
        some installed ∧
      AlphaGoalsCumulativeResidualVariantAgreesOn
        alpha
        (continuationAlphaSupport
          alpha branch.bindings binding
          ((freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm)
        barrier canonical branch.bindings
        (Mettapedia.Languages.MeTTa.PLeaTTa.trimFor
          ((freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm installed)
        branch.body
        (freshenResolutionClause
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body := by
  obtain
    ⟨alpha, canonical, generated, installed, shared, independentShape,
      ordered, generatedExact, installedExact, close⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologActivationUnifierBridge.SupportedPreparedCandidateAgrees.unifyB_body_cumulative_trimmed_of_headResolution
      query wellFormed member agreement arity queryShared
      queryReferenceBelow queryExecutableLive highWater bindingTopological
      resolved
  refine
    ⟨alpha, canonical, generated, installed, shared, independentShape,
      ordered, generatedExact, installedExact, ?_⟩
  exact close
    (continuationAlphaSupport
      alpha branch.bindings binding
      ((freshenResolutionClause
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body ++ rest)
      qterm)
    (continuationAlphaSupport.included
      alpha branch.bindings binding
      ((freshenResolutionClause
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body ++ rest)
      qterm)
    (continuationAlphaSupport.referenceFixed
      alpha branch.bindings binding
      ((freshenResolutionClause
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body ++ rest)
      qterm)
    (continuationAlphaSupport.runtimeAvoids
      alpha branch.bindings binding
      ((freshenResolutionClause
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body ++ rest)
      qterm)
    (continuationAlphaSupport.live
      alpha branch.bindings binding
      ((freshenResolutionClause
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body ++ rest)
      qterm)

/-- Compatibility projection of the direct witness: every independently
resolved supported occurrence rules out executable head-unification
failure. -/
theorem SupportedPreparedCandidateAgrees.unifyB_complete_of_headResolution
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution}
    (query :
      NormalizedCallAgrees queryAlpha cursor
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding result))
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (resolved : HeadResolution branch independentResult) :
    ∃ executableResult,
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).params ++
              [(freshenResolutionClause
                (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
                qterm seed barrier clause).result])) =
        some executableResult := by
  obtain
    ⟨alpha, canonical, flattened, generated, installed, shared,
      bodyControl, equationsAgreement, independentShape, ordered, generatedExact,
      generatedAgreement, flattenedTopological, generatedTopological,
      generatedValuation, flattenedMgu, flattenedFactors,
      canonicalFactors, installedExact, installedShape⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologActivationUnifierBridge.SupportedPreparedCandidateAgrees.unifyB_direct_of_headResolution
      query wellFormed member agreement arity queryShared
      queryReferenceBelow queryExecutableLive highWater resolved
  exact ⟨installed, installedExact⟩

/-- Equivalent negative formulation used when excluding the executable
`eq_fail` constructor in a step correspondence proof. -/
theorem SupportedPreparedCandidateAgrees.unifyB_ne_none_of_headResolution
    {queryAlpha : List (LogicVar × String)}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution}
    (query :
      NormalizedCallAgrees queryAlpha cursor
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding result))
    (wellFormed : cursor.WellFormed)
    (member : branch ∈ cursor.remaining)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (resolved : HeadResolution branch independentResult) :
    Mettapedia.Languages.MeTTa.PLeaTTa.unifyB binding (.expr (args ++ [result]))
        (.expr
          ((freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).params ++
            [(freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).result])) ≠
      none := by
  obtain ⟨executableResult, success⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologActivationUnifierBridge.SupportedPreparedCandidateAgrees.unifyB_complete_of_headResolution
        query wellFormed member agreement arity queryShared
        queryReferenceBelow queryExecutableLive highWater resolved
  rw [success]
  simp

/-! ## Paired activation step -/

/-- A matched independent cursor pull and the corresponding executable
full-head equality both advance successfully.

The theorem pins the actual `RawStep.clausesPull` splice and actual
`Mettapedia.Languages.MeTTa.PLeaTTa.Step.eq_ok` constructor.  This compatibility projection records only
simultaneous step existence; `matched_clause_eq_ok_task_correspondence` below
strengthens it with the successor payload relation. -/
theorem matched_clause_eq_ok_correspondence
    {prog : Mettapedia.Languages.MeTTa.PLeaTTa.Prog} {gt : Mettapedia.Languages.MeTTa.PLeaTTa.Source.GroundingTable}
    {queryAlpha : List (LogicVar × String)}
    {session : Session} {scope : CutScopeId}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {branches : List ClauseBranch} {clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution} {conf : Mettapedia.Languages.MeTTa.PLeaTTa.Conf}
    (query :
      NormalizedCallAgrees queryAlpha cursor
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding result))
    (wellFormed : cursor.WellFormed)
    (remaining : cursor.remaining = branch :: branches)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (resolved : HeadResolution branch independentResult)
    (current :
      conf.cur =
        some
          (Mettapedia.Languages.MeTTa.PLeaTTa.Goal.eq (.expr (args ++ [result]))
              (.expr
                ((freshenResolutionClause
                    (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest
                    binding qterm seed barrier clause).params ++
                  [(freshenResolutionClause
                    (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest
                    binding qterm seed barrier clause).result])) ::
            (freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest,
            binding)) :
    ∃ executableResult,
      RawStep session (.clauses scope cursor) [] .none session
          (.running
            (.choice scope
              (.task scope (branch.enter independentResult).rawBody
                (branch.enter independentResult).bindings)
              (.clauses scope (cursor.advance branch branches)))) ∧
        Mettapedia.Languages.MeTTa.PLeaTTa.Step prog gt conf
          { conf with
            cur :=
              some
                ((freshenResolutionClause
                    (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest
                    binding qterm seed barrier clause).body ++ rest,
                  Mettapedia.Languages.MeTTa.PLeaTTa.trimFor
                    ((freshenResolutionClause
                      (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest
                      binding qterm seed barrier clause).body ++ rest)
                    conf.qterm executableResult) } := by
  have member : branch ∈ cursor.remaining := by
    rw [remaining]
    simp
  obtain ⟨executableResult, success⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologActivationUnifierBridge.SupportedPreparedCandidateAgrees.unifyB_complete_of_headResolution
      query wellFormed member agreement arity queryShared
      queryReferenceBelow queryExecutableLive highWater resolved
  refine ⟨executableResult, ?_, ?_⟩
  · exact matched_clause_splices_body_first scope session
      (.matched cursor branch branches independentResult remaining resolved)
  · exact .eq_ok conf
      (.expr (args ++ [result]))
      (.expr
        ((freshenResolutionClause
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding qterm
            seed barrier clause).params ++
          [(freshenResolutionClause
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding qterm
            seed barrier clause).result]))
      ((freshenResolutionClause
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding qterm seed
        barrier clause).body ++ rest)
      binding executableResult current success

/-- The paired activation step with its successor payload relation.

Unlike `matched_clause_eq_ok_correspondence`, this strengthening does not
stop at simultaneous step existence.  It relates the exact independent left
task installed by `clausesPull` to the exact freshened executable body and
trimmed binding installed by `eq_ok`, on the structurally extracted safe
continuation support.  Completeness of that conservative support for all
future observations remains a separate caller/compiler obligation. -/
theorem matched_clause_eq_ok_task_correspondence
    {prog : Mettapedia.Languages.MeTTa.PLeaTTa.Prog} {gt : Mettapedia.Languages.MeTTa.PLeaTTa.Source.GroundingTable}
    {queryAlpha : List (LogicVar × String)}
    {session : Session} {scope : CutScopeId}
    {cursor : PreparedCursor} {branch : ClauseBranch}
    {branches : List ClauseBranch} {clause : Mettapedia.Languages.MeTTa.PLeaTTa.Clause}
    {args : List Atom} {result : Atom} {rest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal}
    {binding : Subst} {qterm : Atom} {seed barrier : Nat}
    {independentResult : Substitution} {conf : Mettapedia.Languages.MeTTa.PLeaTTa.Conf}
    (query :
      NormalizedCallAgrees queryAlpha cursor
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
        (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding result))
    (wellFormed : cursor.WellFormed)
    (remaining : cursor.remaining = branch :: branches)
    (agreement :
      SupportedPreparedCandidateAgrees cursor.callGeneration
        cursor.predicate cursor.arguments cursor.bindings branch clause)
    (arity : clause.params.length = args.length)
    (queryShared : SharedRuntimeAlpha queryAlpha)
    (queryReferenceBelow :
      GeneratedBelow cursor.reservationStart (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈
          resolutionOccupiedVars
            (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) result rest binding qterm) ≤
        seed)
    (bindingTopological : Mettapedia.Languages.MeTTa.PLeaTTa.SubstTopological binding)
    (resolved : HeadResolution branch independentResult)
    (queryTerm : conf.qterm = qterm)
    (current :
      conf.cur =
        some
          (Mettapedia.Languages.MeTTa.PLeaTTa.Goal.eq (.expr (args ++ [result]))
              (.expr
                ((freshenResolutionClause
                    (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest
                    binding qterm seed barrier clause).params ++
                  [(freshenResolutionClause
                    (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest
                    binding qterm seed barrier clause).result])) ::
            (freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest,
            binding)) :
    ∃ alpha canonical installed,
      SharedRuntimeAlpha alpha ∧
      OrderedTreeMgu
        (denoteEquations branch.normalizedHeadEquations) canonical ∧
      RawStep session (.clauses scope cursor) [] .none session
          (.running
            (.choice scope
              (.task scope (branch.enter independentResult).rawBody
                (branch.enter independentResult).bindings)
              (.clauses scope (cursor.advance branch branches)))) ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.Step prog gt conf
        { conf with
          cur :=
            some
              ((freshenResolutionClause
                  (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest
                  binding qterm seed barrier clause).body ++ rest,
                Mettapedia.Languages.MeTTa.PLeaTTa.trimFor
                  ((freshenResolutionClause
                    (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest
                    binding qterm seed barrier clause).body ++ rest)
                  qterm installed) } ∧
      ActivatedTaskAgrees
        alpha
        (continuationAlphaSupport
          alpha branch.bindings binding
          ((freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm)
        barrier canonical branch.bindings
        (Mettapedia.Languages.MeTTa.PLeaTTa.trimFor
          ((freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).body ++ rest)
          qterm installed)
        (branch.enter independentResult)
        (freshenResolutionClause
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
          qterm seed barrier clause).body := by
  have member : branch ∈ cursor.remaining := by
    rw [remaining]
    simp
  obtain
    ⟨alpha, canonical, _generated, installed, shared, independentShape,
      ordered, _generatedExact, installedExact, bodyAgreement⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologActivationUnifierBridge.SupportedPreparedCandidateAgrees.unifyB_body_continuation_support_of_headResolution
      query wellFormed member agreement arity queryShared
      queryReferenceBelow queryExecutableLive highWater bindingTopological
      resolved
  have sourceStep :
      RawStep session (.clauses scope cursor) [] .none session
        (.running
          (.choice scope
            (.task scope (branch.enter independentResult).rawBody
              (branch.enter independentResult).bindings)
            (.clauses scope (cursor.advance branch branches)))) :=
    matched_clause_splices_body_first scope session
      (.matched cursor branch branches independentResult remaining resolved)
  have executableStep :
      Mettapedia.Languages.MeTTa.PLeaTTa.Step prog gt conf
        { conf with
          cur :=
            some
              ((freshenResolutionClause
                  (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest
                  binding qterm seed barrier clause).body ++ rest,
                Mettapedia.Languages.MeTTa.PLeaTTa.trimFor
                  ((freshenResolutionClause
                    (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest
                    binding qterm seed barrier clause).body ++ rest)
                  qterm installed) } := by
    simpa only [queryTerm] using
      Mettapedia.Languages.MeTTa.PLeaTTa.Step.eq_ok conf
        (.expr (args ++ [result]))
        (.expr
          ((freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).params ++
            [(freshenResolutionClause
              (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding
              qterm seed barrier clause).result]))
        ((freshenResolutionClause
          (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)) args result rest binding qterm
          seed barrier clause).body ++ rest)
        binding installed current installedExact
  refine
    ⟨alpha, canonical, installed, shared, ordered, sourceStep,
      executableStep, ?_⟩
  refine
    ⟨shared,
      ordered.binding_wellFormed
        (denoteEquations_wellFormed branch.normalizedHeadEquations),
      ?_, ?_⟩
  · simpa [ClauseBranch.enter] using independentShape
  · simpa [ClauseBranch.enter] using bodyAgreement

end Mettapedia.Languages.MeTTa.PLeaTTa.PrologActivationUnifierBridge
