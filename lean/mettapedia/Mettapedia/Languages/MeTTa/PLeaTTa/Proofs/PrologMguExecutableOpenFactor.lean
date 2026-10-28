-- SPDX-License-Identifier: Apache-2.0

/-
Module: Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologMguExecutableOpenFactor
Purpose: Factor the independently constructed open canonical MGU
  representative through every actual executable MGU result.
Trusted boundary: none
Main exports:
  OpenAlphaResultFactors,
  RuntimeAlphaCovers,
  RuntimeAtomAlphaCovered,
  unifyTopExact_result_runtimeAlphaCovered,
  unifyTopExact_open_factor_of_ordered_shared_alpha,
  unifyB_result_has_open_factor_of_ordered_shared_alpha
-/
import Mettapedia.Languages.MeTTa.PLeaTTa.Proofs.PrologMguTopology

namespace Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguExecutableOpenFactor

open Mettapedia.Languages.MeTTa.PLeaTTa.Source (Atom Subst)
open PeTTaSpec.PrologCore
open PeTTaSpec.PrologCore.Resolver
open PeTTaSpec.PrologCore.Canonical
open PrologStateBridge
open PrologMguBridge
open PrologMguOpenAgreement
open PrologMguTopology
open PrologPrefilterBridge

/-- The actual executable result is at least as general as one open runtime
representative of the independent ordered canonical MGU.  The representative
retains its raw alpha spelling, exact deep denotation, and acyclicity
certificate; factorization is semantic rather than association-list equality.
-/
def OpenAlphaResultFactors
    (alpha : List (LogicVar × String))
    (canonical : TreeSubstitution) (result : Subst) : Prop :=
  ∃ representative,
    AlphaTreeSubstitutionAgrees alpha canonical representative ∧
      AlphaValuationAgrees alpha canonical representative ∧
      Nonempty (Mettapedia.Languages.MeTTa.PLeaTTa.SubstTopological representative) ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.SubstFactorsThroughWith
        Mettapedia.Languages.MeTTa.PLeaTTa.prologGroundIdentical representative result

/-! ## Actual-result support in the shared alpha graph -/

/-- One executable variable name is covered by the finite shared alpha graph
when the graph gives it some independent canonical identity. -/
def RuntimeAlphaCovers
    (alpha : List (LogicVar × String)) (name : String) : Prop :=
  ∃ identity, (identity, name) ∈ alpha

/-- Every executable variable occurring in one runtime atom is covered by
the finite shared alpha graph. -/
def RuntimeAtomAlphaCovered
    (alpha : List (LogicVar × String)) (atom : Atom) : Prop :=
  ∀ {name}, name ∈ atom.vars → RuntimeAlphaCovers alpha name

/-- Complete alpha coverage of an executable substitution includes both its
keys and every variable nested inside every replacement value. -/
def RuntimeSubstitutionAlphaCovered
    (alpha : List (LogicVar × String)) (binding : Subst) : Prop :=
  Mettapedia.Languages.MeTTa.PLeaTTa.RuntimeSubstitutionVariablesSatisfy
    (RuntimeAlphaCovers alpha) binding

/-- Structural canonical/runtime agreement covers every executable variable
occurring in the runtime atom. -/
theorem CanonicalRuntimeAgrees.runtimeAlphaCovers
    {alpha : List (LogicVar × String)}
    {tree : Tree} {atom : Atom}
    (agreement : CanonicalRuntimeAgrees alpha tree atom) :
    ∀ {name}, name ∈ atom.vars → RuntimeAlphaCovers alpha name := by
  intro name member
  obtain ⟨identity, linked, _⟩ :=
    CanonicalRuntimeAgrees.runtime_variable_supported
      agreement (treeVariablesSatisfy_true tree) member
  exact ⟨identity, linked⟩

/-- Both executable sides of a shared-alpha equation family have complete
runtime-variable coverage. -/
theorem SharedAlphaEquationsAgree.runtimeAlphaCovers
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms) :
    (∀ {name},
      name ∈ (leftAtoms.map Atom.vars).flatten →
        RuntimeAlphaCovers alpha name) ∧
      ∀ {name},
        name ∈ (rightAtoms.map Atom.vars).flatten →
          RuntimeAlphaCovers alpha name := by
  induction agreement with
  | nil =>
      constructor <;> intro name member <;> simp at member
  | cons left right tail inductionHypothesis =>
      constructor
      · intro name member
        simp only [List.map_cons, List.flatten_cons,
          List.mem_append] at member
        rcases member with headMember | tailMember
        · exact
            CanonicalRuntimeAgrees.runtimeAlphaCovers
              (AlphaTermAgrees.canonicalRuntimeAgrees left) headMember
        · exact inductionHypothesis.1 tailMember
      · intro name member
        simp only [List.map_cons, List.flatten_cons,
          List.mem_append] at member
        rcases member with headMember | tailMember
        · exact
            CanonicalRuntimeAgrees.runtimeAlphaCovers
              (AlphaTermAgrees.canonicalRuntimeAgrees right) headMember
        · exact inductionHypothesis.2 tailMember

/-- Expression wrapping preserves the complete two-sided coverage statement
in exactly the support shape used by `unifyTopExact`. -/
theorem SharedAlphaEquationsAgree.expression_runtimeAlphaCovers
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms) :
    ∀ {name},
      name ∈ (.expr leftAtoms : Atom).vars ++
          (.expr rightAtoms : Atom).vars →
        RuntimeAlphaCovers alpha name := by
  intro name member
  simp only [Atom.vars, List.mem_append] at member
  rcases member with leftMember | rightMember
  · exact
      (Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguExecutableOpenFactor.SharedAlphaEquationsAgree.runtimeAlphaCovers
        agreement).1 leftMember
  · exact
      (Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguExecutableOpenFactor.SharedAlphaEquationsAgree.runtimeAlphaCovers
        agreement).2 rightMember

/-- Every key and every residual replacement variable in an actual
`unifyTopExact` result has an alpha partner in the original equation graph.
This is stronger than key-domain coverage and is independent of any chosen
canonical MGU orientation. -/
theorem unifyTopExact_result_runtimeAlphaCovered
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {result : Subst}
    (returned :
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact (.expr leftAtoms) (.expr rightAtoms) =
        some result) :
    RuntimeSubstitutionAlphaCovered alpha result := by
  have supported :=
    Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact_result_variablesSatisfy
      (.expr leftAtoms) (.expr rightAtoms) result returned
  intro entry member
  have entrySupported := supported entry member
  exact
    ⟨Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguExecutableOpenFactor.SharedAlphaEquationsAgree.expression_runtimeAlphaCovers
        agreement entrySupported.1,
      fun name nameMember =>
        Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguExecutableOpenFactor.SharedAlphaEquationsAgree.expression_runtimeAlphaCovers
          agreement (entrySupported.2 name nameMember)⟩

/-- Inverse functionality upgrades runtime alpha coverage to a unique
canonical identity.  This is the finite inverse map consumed by residual
alpha-renaming; no choice of rigid-term interpretation is made here. -/
theorem SharedRuntimeAlpha.uniqueCanonical_of_runtimeAlphaCovers
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {name : String}
    (covered : RuntimeAlphaCovers alpha name) :
    ∃! identity, (identity, name) ∈ alpha := by
  obtain ⟨identity, linked⟩ := covered
  refine ⟨identity, linked, ?_⟩
  intro candidate candidateLinked
  exact shared.backward candidateLinked linked

/-- Deep executable substitution preserves alpha coverage when both the
input atom and the complete key-and-value support of the substitution are
covered.  This is the closure fact needed before residual output variables
can be renamed back to independent identities. -/
theorem RuntimeSubstitutionAlphaCovered.subst
    {alpha : List (LogicVar × String)}
    {binding : Subst}
    (bindingCovered :
      RuntimeSubstitutionAlphaCovered alpha binding)
    {atom : Atom}
    (atomCovered : RuntimeAtomAlphaCovered alpha atom) :
    RuntimeAtomAlphaCovered alpha (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding atom) := by
  intro name member
  rcases Mettapedia.Languages.MeTTa.PLeaTTa.subst_vars_origin binding atom name member with
    inputMember | replacementMember
  · exact atomCovered inputMember
  · simp only [List.mem_flatMap] at replacementMember
    obtain ⟨entry, entryMember, nameMember⟩ := replacementMember
    exact bindingCovered.replacement entryMember nameMember

/-- An actual executable MGU therefore preserves alpha coverage on every
alpha-covered runtime atom. -/
theorem unifyTopExact_result_subst_runtimeAlphaCovered
    {alpha : List (LogicVar × String)}
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {result : Subst}
    (returned :
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact (.expr leftAtoms) (.expr rightAtoms) =
        some result)
    {atom : Atom}
    (atomCovered : RuntimeAtomAlphaCovered alpha atom) :
    RuntimeAtomAlphaCovered alpha (Mettapedia.Languages.MeTTa.PLeaTTa.subst result atom) := by
  exact
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguExecutableOpenFactor.RuntimeSubstitutionAlphaCovered.subst
      (unifyTopExact_result_runtimeAlphaCovered agreement returned)
      atomCovered

/-- Variable support cannot by itself choose between PeTTa's two accepted
boolean source spellings.  Pinned PeTTa normalizes `True` and `true` to the
same Prolog atom, so the remaining theorem must obtain this normalization
from the supported source producer rather than inventing a runtime
distinction. -/
theorem boolean_runtime_inverse_is_not_functional :
    CanonicalRuntimeAgrees []
        (.node (.atom "True") []) (.sym "True") ∧
      CanonicalRuntimeAgrees []
        (.node (.atom "true") []) (.sym "True") ∧
      (.node (.atom "True") [] : Tree) ≠
        .node (.atom "true") [] := by
  exact ⟨.atom (by decide) (by decide), .trueAtom, by simp⟩

/-- In contrast, the forgeable source atom `#nil` and the internal empty-list
sentinel now have different runtime constructors. -/
theorem nil_runtime_encoding_is_distinct :
    CanonicalRuntimeAgrees []
        (.node (.atom "#nil") []) (.sym "#nil") ∧
      CanonicalRuntimeAgrees [] (.node .nil []) nilA ∧
      (Atom.sym "#nil" : Atom) ≠ nilA := by
  exact ⟨.atom (by decide) (by decide), .nil, nilA_ne_source_nil.symm⟩

/-- A tree-level canonical unifier and its open alpha valuation make every
runtime equation pair comparator-equivalent.  This avoids reifying the
canonical substitution merely to reuse the source-substitution theorem. -/
theorem SharedAlphaEquationsAgree.atomsEquivalent_of_tree_unifier
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgrees alpha canonical runtime)
    (unifies :
      TreeUnifiesEquations canonical (denoteEquations equations)) :
    AtomsEquivalentWith Mettapedia.Languages.MeTTa.PLeaTTa.prologGroundIdentical
      (leftAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime))
      (rightAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst runtime)) := by
  induction agreement with
  | nil =>
      exact .nil
  | @cons leftTerm rightTerm leftAtom rightAtom equations leftAtoms
      rightAtoms left right tail inductionHypothesis =>
      have leftApplied :=
        canonicalRuntimeAgrees_apply
          (AlphaTermAgrees.canonicalRuntimeAgrees left) valuation
      have rightApplied :=
        canonicalRuntimeAgrees_apply
          (AlphaTermAgrees.canonicalRuntimeAgrees right) valuation
      have headEquality :
          TreeSubstitution.apply canonical (Term.denote leftTerm) =
            TreeSubstitution.apply canonical (Term.denote rightTerm) := by
        apply unifies
          (Term.denote leftTerm, Term.denote rightTerm)
        simp [denoteEquations]
      rw [headEquality] at leftApplied
      exact .cons
        (CanonicalRuntimeAgrees.equivalent_of_same
          functional leftApplied rightApplied)
        (inductionHypothesis (by
          intro denoted member
          exact unifies denoted (by
            simp only [denoteEquations, List.mem_map] at member ⊢
            obtain ⟨equation, equationMember, rfl⟩ := member
            exact
              ⟨equation, List.mem_cons_of_mem _ equationMember, rfl⟩)))

/-- Expression wrapper around
`atomsEquivalent_of_tree_unifier`, in the exact runtime worklist shape
consumed by `unifyTopExact`. -/
theorem SharedAlphaEquationsAgree.deepEquivalentUnifies_of_tree_unifier
    {alpha : List (LogicVar × String)}
    (functional : AlphaForwardFunctional alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution} {runtime : Subst}
    (valuation :
      AlphaValuationAgrees alpha canonical runtime)
    (unifies :
      TreeUnifiesEquations canonical (denoteEquations equations)) :
    Mettapedia.Languages.MeTTa.PLeaTTa.DeepEquivalentUnifies Mettapedia.Languages.MeTTa.PLeaTTa.prologGroundIdentical runtime
      [(.expr leftAtoms, .expr rightAtoms)] := by
  intro equation member
  simp only [List.mem_singleton] at member
  subst equation
  simp only [Mettapedia.Languages.MeTTa.PLeaTTa.subst_expr]
  exact .expression
    (Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguExecutableOpenFactor.SharedAlphaEquationsAgree.atomsEquivalent_of_tree_unifier
      functional agreement valuation unifies)

/-- The open representative constructed from an ordered canonical MGU is a
runtime unifier, while retaining its raw spelling and topology witnesses. -/
theorem SharedAlphaEquationsAgree.open_runtime_unifier_exists
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical) :
    ∃ representative,
      AlphaTreeSubstitutionAgrees alpha canonical representative ∧
        AlphaValuationAgrees alpha canonical representative ∧
        Nonempty (Mettapedia.Languages.MeTTa.PLeaTTa.SubstTopological representative) ∧
        Mettapedia.Languages.MeTTa.PLeaTTa.DeepEquivalentUnifies
          Mettapedia.Languages.MeTTa.PLeaTTa.prologGroundIdentical representative
          [(.expr leftAtoms, .expr rightAtoms)] := by
  obtain
    ⟨representative, spelling, valuation, topological⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguTopology.SharedAlphaEquationsAgree.orderedMgu_open_valuation_exists
      shared agreement derivation
  exact
    ⟨representative, spelling, valuation, topological,
      Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguExecutableOpenFactor.SharedAlphaEquationsAgree.deepEquivalentUnifies_of_tree_unifier
        shared.forward agreement valuation derivation.isMostGeneral.1⟩

/-- Every actual `unifyTopExact` result admits the independent canonical
MGU's open runtime representative as a semantic instance.  Unlike the older
ground-factor theorem, this result preserves residual variables. -/
theorem unifyTopExact_open_factor_of_ordered_shared_alpha
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations leftAtoms rightAtoms)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical)
    {result : Subst}
    (returned :
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact (.expr leftAtoms) (.expr rightAtoms) =
        some result) :
    OpenAlphaResultFactors alpha canonical result := by
  obtain
    ⟨representative, spelling, valuation, topological,
      representativeUnifies⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguExecutableOpenFactor.SharedAlphaEquationsAgree.open_runtime_unifier_exists
      shared agreement derivation
  have runtimeMgu :=
    Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact_isMgu
      (.expr leftAtoms) (.expr rightAtoms) result returned
  exact
    ⟨representative, spelling, valuation, topological,
      runtimeMgu.2 representative representativeUnifies⟩

/-- The current-binding executable call exposes its generated open MGU and
the exact installation equation, with the canonical open representative
factoring through that generated result before composition with `base`. -/
theorem unifyB_result_has_open_factor_of_ordered_shared_alpha
    (base : Subst)
    {alpha : List (LogicVar × String)}
    (shared : SharedRuntimeAlpha alpha)
    {equations : List (Term × Term)}
    {leftAtoms rightAtoms : List Atom}
    (agreement :
      SharedAlphaEquationsAgree alpha equations
        (leftAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base))
        (rightAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base)))
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu (denoteEquations equations) canonical)
    {result : Subst}
    (returned :
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyB base (.expr leftAtoms) (.expr rightAtoms) =
        some result) :
    ∃ generated,
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr (leftAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base)))
          (.expr (rightAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base))) =
          some generated ∧
        OpenAlphaResultFactors alpha canonical generated ∧
        result =
          match generated with
          | [] => base
          | _ :: _ => Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.compose generated base := by
  obtain ⟨generated, generatedEq, _, installed⟩ :=
    Mettapedia.Languages.MeTTa.PLeaTTa.unifyB_result_has_generated_mgu
      base (.expr leftAtoms) (.expr rightAtoms) result returned
  have normalizedEq :
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr (leftAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base)))
          (.expr (rightAtoms.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst base))) =
          some generated := by
    simpa only [Mettapedia.Languages.MeTTa.PLeaTTa.subst_expr] using generatedEq
  have factors :=
    unifyTopExact_open_factor_of_ordered_shared_alpha
      shared agreement derivation normalizedEq
  exact ⟨generated, normalizedEq, factors, installed⟩

/-! ## Actual freshened retained-clause head -/

/-- Returned-substitution open factorization at the actual retained-clause
activation.  The graph contains both the normalized query payload and the
real suffix-freshened executable clause occurrence; it is constructed once
by `normalizedSharedHeadEquations` and consumed unchanged by the general
open-factor theorem. -/
theorem FreshenedClauseAlphaAgrees.unifyB_result_has_open_factor
    {queryAlpha : List (LogicVar × String)}
    {reference : LocalClause} {executablePredicate : String}
    {executable : Mettapedia.Languages.MeTTa.PLeaTTa.Clause} {freshSeed : Nat}
    {argsv args : List Atom} {result : Atom}
    {rest : List Mettapedia.Languages.MeTTa.PLeaTTa.Goal} {binding : Subst}
    {query : Atom} {seed barrier : Nat}
    (freshened :
      FreshenedClauseAlphaAgrees reference executablePredicate executable
        freshSeed argsv args result rest binding query seed barrier)
    (argsvEq : argsv = args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))
    (queryShared : SharedRuntimeAlpha queryAlpha)
    {queryTerms : List Term}
    (queryPayload :
      AlphaTermsAgree queryAlpha queryTerms
        (args.map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding) ++
          [Mettapedia.Languages.MeTTa.PLeaTTa.subst binding result]))
    (queryReferenceBelow :
      GeneratedBelow (reference.freshCopy freshSeed).firstFresh
        (queryAlpha.map Prod.fst))
    (queryExecutableLive :
      ∀ name, name ∈ queryAlpha.map Prod.snd →
        name ∈ resolutionOccupiedVars argsv result rest binding query)
    (highWater :
      resolutionSeedHighWaterNames
        (resolutionOccupiedVars argsv result rest binding query) ≤ seed)
    (lengths :
      queryTerms.length =
        (reference.freshCopy freshSeed).clause.arguments.length)
    {canonical : TreeSubstitution}
    (derivation :
      OrderedTreeMgu
        (denoteEquations
          (argumentEquations queryTerms
            (reference.freshCopy freshSeed).clause.arguments))
        canonical)
    {executableResult : Subst}
    (returned :
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyB binding (.expr (args ++ [result]))
          (.expr
            ((freshenResolutionClause argsv args result rest binding query
                seed barrier executable).params ++
              [(freshenResolutionClause argsv args result rest binding query
                seed barrier executable).result])) =
        some executableResult) :
    ∃ generated,
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr ((args ++ [result]).map (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding)))
          (.expr
            (((freshenResolutionClause argsv args result rest binding query
                seed barrier executable).params ++
              [(freshenResolutionClause argsv args result rest binding query
                seed barrier executable).result]).map
              (Mettapedia.Languages.MeTTa.PLeaTTa.subst binding))) =
          some generated ∧
        OpenAlphaResultFactors
          (queryAlpha ++
            RuntimeAlpha.graph
              (referenceFreshTargets
                (reference.freshCopy freshSeed).firstFresh
                reference.variables)
              (executableFreshTargets
                (resolutionFreshSuffix argsv result rest binding query seed)
                reference.variables))
          canonical generated ∧
        executableResult =
          match generated with
          | [] => binding
          | _ :: _ => Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.compose generated binding := by
  have normalized :=
    Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguValuation.FreshenedClauseAlphaAgrees.normalizedSharedHeadEquations
      freshened argsvEq queryShared queryPayload queryReferenceBelow
      queryExecutableLive highWater lengths
  exact unifyB_result_has_open_factor_of_ordered_shared_alpha
    binding normalized.1 normalized.2 derivation returned

/-! ### Anti-vacuity: the factor remains open -/

private def openWitnessX : LogicVar := .source "X"

private def openWitnessY : LogicVar := .source "Y"

private def openWitnessAlpha : List (LogicVar × String) :=
  [(openWitnessX, "X"), (openWitnessY, "Y")]

private def openWitnessEquations : List (Term × Term) :=
  [(.variable openWitnessX, .variable openWitnessY)]

private def openWitnessCanonical : TreeSubstitution :=
  [(openWitnessX, .variable openWitnessY)]

private theorem openWitnessShared :
    SharedRuntimeAlpha openWitnessAlpha := by
  constructor
  · intro identity left right leftMember rightMember
    simp [openWitnessAlpha, openWitnessX, openWitnessY]
      at leftMember rightMember
    rcases leftMember with leftMember | leftMember <;>
      rcases rightMember with rightMember | rightMember <;>
      simp_all
  · intro left right name leftMember rightMember
    simp [openWitnessAlpha, openWitnessX, openWitnessY]
      at leftMember rightMember
    rcases leftMember with leftMember | leftMember <;>
      rcases rightMember with rightMember | rightMember <;>
      simp_all

/-- On the smallest residual-alias problem, the factor theorem applies to
the concrete open executable result and that result leaves `Y` unresolved.
This distinguishes the new theorem from the older grounded-instance factor.
-/
theorem residual_alias_open_factor_retains_residual :
    ∃ result,
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr [.var "X"]) (.expr [.var "Y"]) =
        some result ∧
      OpenAlphaResultFactors
        openWitnessAlpha openWitnessCanonical result ∧
      Mettapedia.Languages.MeTTa.PLeaTTa.subst result (.var "Y") = .var "Y" := by
  have derivation :
      OrderedTreeMgu
        (denoteEquations openWitnessEquations)
        openWitnessCanonical := by
    apply OrderedTreeMgu.cons
      (.variable openWitnessX) (.variable openWitnessY) []
      openWitnessCanonical []
    · exact .bindLeft openWitnessX (.variable openWitnessY)
        (by simp [openWitnessX, openWitnessY])
        (by simp [Tree.occurs, openWitnessX, openWitnessY])
    · exact .nil
  have agreement :
      SharedAlphaEquationsAgree openWitnessAlpha
        openWitnessEquations [.var "X"] [.var "Y"] :=
    .cons
      (.variable (by simp [openWitnessAlpha]))
      (.variable (by simp [openWitnessAlpha]))
      .nil
  have returned :
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr [.var "X"]) (.expr [.var "Y"]) =
        some [("X", .var "Y")] := by
    unfold Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
    simp [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.unifyTopWith, Atom.size,
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.unifyRoundsWith, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.decomposeAllWith,
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.decomposeEqWith, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.decomposeListWith,
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.occurs, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.extend, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.erase]
  refine ⟨[("X", .var "Y")], returned, ?_, ?_⟩
  · exact unifyTopExact_open_factor_of_ordered_shared_alpha
      openWitnessShared agreement derivation returned
  · simp [Mettapedia.Languages.MeTTa.PLeaTTa.subst, Mettapedia.Languages.MeTTa.PLeaTTa.substN, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.lookup]

/-- The actual residual-alias result exercises both halves of alpha support:
its key and its still-open replacement variable are covered uniquely, while
an otherwise identical substitution carrying a foreign residual is rejected.
-/
theorem residual_alias_result_alpha_support_exact :
    ∃ result,
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr [.var "X"]) (.expr [.var "Y"]) =
        some result ∧
      RuntimeSubstitutionAlphaCovered openWitnessAlpha result ∧
      (∃! identity, (identity, "X") ∈ openWitnessAlpha) ∧
      (∃! identity, (identity, "Y") ∈ openWitnessAlpha) ∧
      ¬ RuntimeSubstitutionAlphaCovered openWitnessAlpha
          [("X", .var "Z")] := by
  have agreement :
      SharedAlphaEquationsAgree openWitnessAlpha
        openWitnessEquations [.var "X"] [.var "Y"] :=
    .cons
      (.variable (by simp [openWitnessAlpha]))
      (.variable (by simp [openWitnessAlpha]))
      .nil
  have returned :
      Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
          (.expr [.var "X"]) (.expr [.var "Y"]) =
        some [("X", .var "Y")] := by
    unfold Mettapedia.Languages.MeTTa.PLeaTTa.unifyTopExact
    simp [Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.unifyTopWith, Atom.size,
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.unifyRoundsWith, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.decomposeAllWith,
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.decomposeEqWith, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Unify.decomposeListWith,
      Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.occurs, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.extend, Mettapedia.Languages.MeTTa.PLeaTTa.Source.Subst.erase]
  have covered :=
    unifyTopExact_result_runtimeAlphaCovered agreement returned
  have keyCovered :
      RuntimeAlphaCovers openWitnessAlpha "X" :=
    covered.key (entry := ("X", .var "Y")) (by simp)
  have replacementCovered :
      RuntimeAlphaCovers openWitnessAlpha "Y" :=
    covered.replacement (entry := ("X", .var "Y")) (by simp)
      (by simp [Atom.vars])
  refine
    ⟨[("X", .var "Y")], returned, covered,
      Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguExecutableOpenFactor.SharedRuntimeAlpha.uniqueCanonical_of_runtimeAlphaCovers
        openWitnessShared keyCovered,
      Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguExecutableOpenFactor.SharedRuntimeAlpha.uniqueCanonical_of_runtimeAlphaCovers
        openWitnessShared replacementCovered, ?_⟩
  intro foreignCovered
  have foreign :
      RuntimeAlphaCovers openWitnessAlpha "Z" :=
    foreignCovered.replacement (entry := ("X", .var "Z")) (by simp)
      (by simp [Atom.vars])
  rcases foreign with ⟨identity, linked⟩
  simp [openWitnessAlpha, openWitnessX, openWitnessY] at linked

end Mettapedia.Languages.MeTTa.PLeaTTa.PrologMguExecutableOpenFactor
