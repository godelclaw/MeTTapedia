import Mettapedia.QuantumTheory.YangMills.ExtendedExtractionTransfer
import Mettapedia.QuantumTheory.YangMills.ExtractionMajorant
import Mettapedia.QuantumTheory.YangMills.WilsonBlockMajorant
import Mettapedia.QuantumTheory.YangMills.WilsonExtractionRecombinationConstant

/-!
# V14 dimension-sixteen Wilson extraction: source certificate

This module records the outcome of attempting to construct the actual
dimension-`16` action-sector extraction coordinates requested by the v14
Yang--Mills route.

The positive Wilson object is already concrete: `WilsonBlockMajorant` supplies
finite `SU(N)` Wilson observables, their local gauge action, and a norm-one
coefficient-majorant truncation.  The transfer theorem
`coefficientL1_basisJetProjection_le` also proves exactly how certified basis
and dual-jet column bounds would produce an extraction constant.

What v14 does not supply is the coordinate certificate needed to instantiate
that theorem for its action-sector projection `P_ext`:

* F.4.3 uses equations of motion to identify operators, while O.9.2 says that
  the action-sector census uses the off-shell basis and retains EOM operators;
* the dimension-`16` lists are schematic counts, not lattice Wilson
  representatives or a quotient basis modulo Bianchi, integration-by-parts,
  cyclic, orientation, and `SU(N)` trace relations;
* Appendix I gives explicit dual jets only for the distinct observable-sector
  projection of canonical dimension at most `4`;
* no dimension-`16` biorthogonality or conditioning matrix is given; and
* the displayed analytic-radius estimate for the extraction factor does not
  imply the advertised bound `2`, under either its literal or sign-corrected
  binomial reading (`ExtractionMajorant`).

Accordingly the verdict here is a precise source underdetermination, not a
claim that no dimension-`16` Wilson basis can exist.  A future completion must
choose one relation policy, give actual lattice representatives and all
relations, construct the dual jets, and certify their matrices.  Until then
`C_extract`, and therefore `C_true`, are not derived for the v14 Wilson RG map.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills

/-! ## The relation-policy mismatch -/

/-- Whether equations-of-motion operators are removed from the local
action-sector coordinate space or retained as off-shell coordinates. -/
inductive V14ActionSectorRelationPolicy where
  | onShell
  | offShell
deriving DecidableEq, Repr

/-- F.4.3 says that equations of motion are used to identify independent
operators and labels the divergence-square operator as vanishing on shell. -/
def v14F4RelationPolicy : V14ActionSectorRelationPolicy := .onShell

/-- O.9.2 explicitly says that the operator census uses the off-shell basis
and retains EOM-related operators. -/
def v14O9RelationPolicy : V14ActionSectorRelationPolicy := .offShell

/-- The two source sections do not select the same action-sector quotient. -/
theorem v14F4RelationPolicy_ne_v14O9RelationPolicy :
    v14F4RelationPolicy ≠ v14O9RelationPolicy := by
  decide

/-- Named operator templates that v14 itself uses when describing the low
canonical-dimension action sector.  These are source-level continuum
templates, not a fabricated lattice basis. -/
inductive V14ActionOperatorTemplate where
  | identity
  | actionDensity
  | topologicalDensity
  | cubicFieldStrength
  | divergenceSquare
deriving DecidableEq, Fintype, Repr

/-- Canonical dimensions assigned to the five source-level templates. -/
def V14ActionOperatorTemplate.canonicalDimension :
    V14ActionOperatorTemplate → ℕ
  | .identity => 0
  | .actionDensity => 4
  | .topologicalDensity => 4
  | .cubicFieldStrength => 6
  | .divergenceSquare => 6

/-- Membership of the displayed templates under the two relation policies.
The only policy-sensitive template in this finite audit is the EOM
divergence-square term singled out by both F.4.3 and O.9.2. -/
def V14ActionSectorRelationPolicy.retains
    (policy : V14ActionSectorRelationPolicy)
    (operator : V14ActionOperatorTemplate) : Bool :=
  match policy, operator with
  | .onShell, .divergenceSquare => false
  | _, _ => true

theorem v14F4_omits_divergenceSquare :
    v14F4RelationPolicy.retains .divergenceSquare = false := by
  rfl

theorem v14O9_retains_divergenceSquare :
    v14O9RelationPolicy.retains .divergenceSquare = true := by
  rfl

theorem divergenceSquare_dimension_le_sixteen :
    V14ActionOperatorTemplate.divergenceSquare.canonicalDimension ≤ 16 := by
  decide

/-- **Concrete relation-policy obstruction.**  The source's two stated
policies disagree on a named dimension-six operator inside the requested
dimension-sixteen sector. -/
theorem v14_relationPolicies_disagree_inside_dimensionSixteen :
    v14F4RelationPolicy.retains .divergenceSquare ≠
      v14O9RelationPolicy.retains .divergenceSquare ∧
    V14ActionOperatorTemplate.divergenceSquare.canonicalDimension ≤ 16 := by
  exact ⟨by decide, divergenceSquare_dimension_le_sixteen⟩

/-! ## Certificate fields and the source transfer table -/

/-- Fields required to turn the source's range description into the actual
dimension-`16` Wilson-coordinate certificate requested by the transfer
theorem. -/
inductive V14Dimension16CertificateField where
  | wilsonGaugeObject
  | exactBlockBoundaryConvention
  | actionSectorRelationQuotient
  | latticeWilsonRepresentatives
  | finiteQuotientBasis
  | dimensionSixteenDualJets
  | basisJetBiorthogonality
  | conditioningBound
  | extractionConstant
  | wilsonRecursionConstant
deriving DecidableEq, Fintype, Repr

/-- Status vocabulary for the source-to-certificate transfer. -/
inductive V14Dimension16CertificateStatus where
  | constructed
  | sourceConflict
  | notSupplied
  | displayedBoundRefuted
  | notDerived
deriving DecidableEq, Repr

/-- A field is construction-cleared only when the actual object or certificate
data have been supplied. -/
def V14Dimension16CertificateStatus.clears :
    V14Dimension16CertificateStatus → Bool
  | .constructed => true
  | _ => false

/-- Source-audited transfer status.  `wilsonGaugeObject` is the one positive
row: v14 fixes `SU(N)` on a hypercubic Wilson lattice, and the imported Wilson
module realizes that finite object.  The boundary row concerns the precise
block-local convention needed by the dimension-`16` coordinate quotient, not
the existence of boundary conditions elsewhere in the manuscript. -/
def v14Dimension16CertificateStatus :
    V14Dimension16CertificateField → V14Dimension16CertificateStatus
  | .wilsonGaugeObject => .constructed
  | .exactBlockBoundaryConvention => .notSupplied
  | .actionSectorRelationQuotient => .sourceConflict
  | .latticeWilsonRepresentatives => .notSupplied
  | .finiteQuotientBasis => .notSupplied
  | .dimensionSixteenDualJets => .notSupplied
  | .basisJetBiorthogonality => .notSupplied
  | .conditioningBound => .displayedBoundRefuted
  | .extractionConstant => .notDerived
  | .wilsonRecursionConstant => .notDerived

/-- The complete transfer table, emitted as checked data for documentation and
regression use. -/
def v14Dimension16TransferTable :
    List (V14Dimension16CertificateField × V14Dimension16CertificateStatus) :=
  [ (.wilsonGaugeObject, .constructed)
  , (.exactBlockBoundaryConvention, .notSupplied)
  , (.actionSectorRelationQuotient, .sourceConflict)
  , (.latticeWilsonRepresentatives, .notSupplied)
  , (.finiteQuotientBasis, .notSupplied)
  , (.dimensionSixteenDualJets, .notSupplied)
  , (.basisJetBiorthogonality, .notSupplied)
  , (.conditioningBound, .displayedBoundRefuted)
  , (.extractionConstant, .notDerived)
  , (.wilsonRecursionConstant, .notDerived)
  ]

/-- The source would determine a complete coordinate certificate only if
every required row were construction-cleared. -/
def V14Dimension16SourceCertificateComplete : Prop :=
  ∀ field : V14Dimension16CertificateField,
    (v14Dimension16CertificateStatus field).clears = true

/-- The action-sector relation quotient is not coherently fixed by the source. -/
theorem v14Dimension16_relationQuotient_sourceConflict :
    v14Dimension16CertificateStatus .actionSectorRelationQuotient =
      .sourceConflict := by
  rfl

/-- Appendix I's dimension-four observable jets do not fill the distinct
dimension-sixteen action-sector dual-jet row. -/
theorem v14Dimension16_dualJets_notSupplied :
    v14Dimension16CertificateStatus .dimensionSixteenDualJets =
      .notSupplied := by
  rfl

/-- The source does not provide a finite quotient basis for the actual lattice
Wilson representatives modulo all its stated identities. -/
theorem v14Dimension16_finiteQuotientBasis_notSupplied :
    v14Dimension16CertificateStatus .finiteQuotientBasis = .notSupplied := by
  rfl

/-- The displayed projection estimate cannot serve as the missing
conditioning certificate. -/
theorem v14Dimension16_conditioning_displayedBoundRefuted :
    v14Dimension16CertificateStatus .conditioningBound =
      .displayedBoundRefuted := by
  rfl

/-- The transfer table is not complete: the named dimension-sixteen dual jets
alone already witness a non-cleared row. -/
theorem not_v14Dimension16SourceCertificateComplete :
    ¬ V14Dimension16SourceCertificateComplete := by
  intro h
  have hdual := h .dimensionSixteenDualJets
  simp [v14Dimension16CertificateStatus,
    V14Dimension16CertificateStatus.clears] at hdual

/-! ## The analytic bound and final verdict -/

/-- The literal v14 extraction-factor claim specialized to any positive number
of plaquette-log indices. -/
def V14LiteralDimension16ExtractionBound : Prop :=
  ∀ n : ℕ, 1 ≤ n → literalExtractionOperatorSum n ≤ 2

/-- The displayed dimension-sixteen sum fails already for one index. -/
theorem not_v14LiteralDimension16ExtractionBound :
    ¬ V14LiteralDimension16ExtractionBound := by
  intro h
  exact
    (not_literalExtractionOperatorSum_le_two (n := 1) (by decide))
      (h 1 (by decide))

/-- The factorization that remains after the extraction-coordinate audit.
This is bookkeeping only: the four arguments are actual-map constants only
when separately proved on the same Wilson RG map. -/
def v14WilsonRecursionConstantBudget
    (Cfluct Ccumulant Crecomb Cextract : ℝ) : ℝ :=
  Cfluct * Ccumulant * Crecomb * Cextract

theorem v14WilsonRecursionConstantBudget_eq
    (Cfluct Ccumulant Crecomb Cextract : ℝ) :
    v14WilsonRecursionConstantBudget Cfluct Ccumulant Crecomb Cextract =
      Cfluct * Ccumulant * Crecomb * Cextract := by
  rfl

/-- **YM MOVE 2 verdict (obstructed).**  The as-written source neither fixes a
coherent dimension-sixteen coordinate certificate nor proves its advertised
extraction bound.  This does not rule out a future explicitly chosen Wilson
basis and dual-jet construction; it rules out deriving `C_extract`, and hence
`C_true`, from the data presently supplied by v14. -/
theorem v14Dimension16WilsonExtraction_asWritten_obstructed :
    (¬ V14Dimension16SourceCertificateComplete) ∧
      v14F4RelationPolicy ≠ v14O9RelationPolicy ∧
      (¬ V14LiteralDimension16ExtractionBound) ∧
      v14Dimension16CertificateStatus .extractionConstant = .notDerived ∧
      v14Dimension16CertificateStatus .wilsonRecursionConstant = .notDerived := by
  exact
    ⟨not_v14Dimension16SourceCertificateComplete,
      v14F4RelationPolicy_ne_v14O9RelationPolicy,
      not_v14LiteralDimension16ExtractionBound,
      rfl,
      rfl⟩

end YangMills
end QuantumTheory
end Mettapedia
