import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16ContextualQuotient
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16SU2TraceRelations

/-!
# The equivariant physical relation operator at dimension sixteen

The standard sparse relation families are assembled into one linear operator.
The off-shell policy omits the equation of motion; the on-shell policy includes
it.  In both policies the generator action and the signed carrier action
intertwine exactly.  The same statement is then transported through the exact
field-antisymmetry and derivative-localization quotient.

The two `SU(2)` trace families are the traceless anticommutator consequence
and the fundamental three-cut trace identity for traceless `2 x 2` matrices.
They are the finite trace reductions implied by the ordinary degree-two
Cayley--Hamilton identity, rather than an independently chosen truncation.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16PhysicalRelationOperator

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicRawFDCharacterCensus
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance
open HypercubicDimension16DifferentialRelations
open HypercubicDimension16IBPTraceRelations
open HypercubicDimension16CovariantCommutator
open HypercubicDimension16SU2TraceRelations
open HypercubicDimension16ContextualQuotient

/-! ## Policies and generators -/

inductive PhysicalRelationPolicy where
  | offShell
  | onShell
deriving DecidableEq

/-- Sites of all standard relation families which remain after derivative
label alpha reduction.  The EOM constructor is inhabited only on shell. -/
inductive PhysicalRelationGenerator
    (policy : PhysicalRelationPolicy) where
  | antisymmetry (carrier : RelationCarrier)
      (slot : Fin carrier.1.1)
  | bianchi (carrier : RelationCarrier)
      (field : Fin carrier.1.1)
      (position : Fin (dimension16DerivativeCount carrier.1))
      (innermost : IsInnermostDerivative carrier field position)
  | eom (enabled : policy = .onShell)
      (carrier : RelationCarrier)
      (field : Fin carrier.1.1)
      (position : Fin (dimension16DerivativeCount carrier.1))
      (innermost : IsInnermostDerivative carrier field position)
  | integrationByParts (carrier : RelationCarrier)
      (position : Fin (dimension16DerivativeCount carrier.1))
      (outermost : IsGloballyOutermostDerivative carrier position)
  | traceless (carrier : RelationCarrier)
      (field : Fin carrier.1.1)
      (singleton : IsSingletonTrace carrier field)
  | covariantCommutator (carrier : RelationCarrier)
      (site : CovariantCommutatorSite carrier)
  | traceAnticommutator (carrier : RelationCarrier)
      (site : TraceAnticommutatorSite carrier)
  | fundamentalTrace (carrier : RelationCarrier)
      (site : FundamentalTraceSite carrier)

abbrev PhysicalRelationGeneratorSpace
    (policy : PhysicalRelationPolicy) :=
  PhysicalRelationGenerator policy →₀ ℚ

def physicalRelationRow {policy : PhysicalRelationPolicy} :
    PhysicalRelationGenerator policy → RelationSpace
  | .antisymmetry carrier slot =>
      fieldAntisymmetryRow carrier slot
  | .bianchi carrier field position _ =>
      bianchiRow carrier field position
  | .eom _ carrier field position _ =>
      eomRow carrier field position
  | .integrationByParts carrier position _ =>
      integrationByPartsRow carrier position
  | .traceless carrier field _ =>
      tracelessLetterRow carrier field
  | .covariantCommutator _ site =>
      covariantCommutatorRow site
  | .traceAnticommutator _ site =>
      traceAnticommutatorRow site
  | .fundamentalTrace _ site =>
      fundamentalTraceRow site

/-- Linear map whose range is the joint standard-relation span. -/
def physicalRelationOperator (policy : PhysicalRelationPolicy) :
    PhysicalRelationGeneratorSpace policy →ₗ[ℚ] RelationSpace :=
  Finsupp.linearCombination ℚ physicalRelationRow

@[simp] theorem physicalRelationOperator_single
    {policy : PhysicalRelationPolicy}
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ) :
    physicalRelationOperator policy
        (Finsupp.single generator coefficient) =
      coefficient • physicalRelationRow generator := by
  simp [physicalRelationOperator]

/-! ## Signed action on generator sites -/

def PhysicalRelationGenerator.act
    {policy : PhysicalRelationPolicy} (h : Hypercubic4) :
    PhysicalRelationGenerator policy → PhysicalRelationGenerator policy
  | .antisymmetry carrier slot =>
      .antisymmetry
        (exactDimension16DerivativeAlphaReducedAct h carrier) slot
  | .bianchi carrier field position innermost =>
      .bianchi
        (exactDimension16DerivativeAlphaReducedAct h carrier)
        field position
        ((isInnermostDerivative_act_iff h carrier field position).mpr
          innermost)
  | .eom enabled carrier field position innermost =>
      .eom enabled
        (exactDimension16DerivativeAlphaReducedAct h carrier)
        field position
        ((isInnermostDerivative_act_iff h carrier field position).mpr
          innermost)
  | .integrationByParts carrier position outermost =>
      .integrationByParts
        (exactDimension16DerivativeAlphaReducedAct h carrier)
        position
        ((isGloballyOutermostDerivative_act_iff h carrier position).mpr
          outermost)
  | .traceless carrier field singleton =>
      .traceless
        (exactDimension16DerivativeAlphaReducedAct h carrier)
        field
        ((isSingletonTrace_act_iff h carrier field).mpr singleton)
  | .covariantCommutator _ site =>
      .covariantCommutator
        (exactDimension16DerivativeAlphaReducedAct h _) (site.act h)
  | .traceAnticommutator _ site =>
      .traceAnticommutator
        (exactDimension16DerivativeAlphaReducedAct h _) (site.act h)
  | .fundamentalTrace _ site =>
      .fundamentalTrace
        (exactDimension16DerivativeAlphaReducedAct h _) (site.act h)

@[simp] theorem PhysicalRelationGenerator.act_one
    {policy : PhysicalRelationPolicy}
    (generator : PhysicalRelationGenerator policy) :
    generator.act 1 = generator := by
  cases generator with
  | antisymmetry carrier slot =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_one carrier
      rfl
  | bianchi carrier field position innermost =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_one carrier
      rfl
  | eom enabled carrier field position innermost =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_one carrier
      rfl
  | integrationByParts carrier position outermost =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_one carrier
      rfl
  | traceless carrier field singleton =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_one carrier
      rfl
  | covariantCommutator carrier site =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_one carrier
      rfl
  | traceAnticommutator carrier site =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_one carrier
      rfl
  | fundamentalTrace carrier site =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_one carrier
      rfl

theorem PhysicalRelationGenerator.act_mul
    {policy : PhysicalRelationPolicy} (left right : Hypercubic4)
    (generator : PhysicalRelationGenerator policy) :
    generator.act (left * right) = (generator.act right).act left := by
  cases generator with
  | antisymmetry carrier slot =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_mul left right carrier
      rfl
  | bianchi carrier field position innermost =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_mul left right carrier
      rfl
  | eom enabled carrier field position innermost =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_mul left right carrier
      rfl
  | integrationByParts carrier position outermost =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_mul left right carrier
      rfl
  | traceless carrier field singleton =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_mul left right carrier
      rfl
  | covariantCommutator carrier site =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_mul left right carrier
      rfl
  | traceAnticommutator carrier site =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_mul left right carrier
      rfl
  | fundamentalTrace carrier site =>
      simp only [PhysicalRelationGenerator.act]
      cases exactDimension16DerivativeAlphaReducedAct_mul left right carrier
      rfl

/-- Coefficient needed on a generator when the corresponding tensor row is
transported by a signed hypercubic element. -/
def physicalRelationGeneratorSign
    {policy : PhysicalRelationPolicy} (h : Hypercubic4) :
    PhysicalRelationGenerator policy → ℚ
  | .antisymmetry carrier _ =>
      exactDimension16DerivativeAlphaReducedTensorSign h carrier
  | .bianchi carrier _ _ _ =>
      exactDimension16DerivativeAlphaReducedTensorSign h carrier
  | .eom _ carrier field position _ =>
      eomContextSign h carrier field position
  | .integrationByParts carrier _ _ =>
      exactDimension16DerivativeAlphaReducedTensorSign h carrier
  | .traceless carrier _ _ =>
      exactDimension16DerivativeAlphaReducedTensorSign h carrier
  | .covariantCommutator carrier _ =>
      exactDimension16DerivativeAlphaReducedTensorSign h carrier
  | .traceAnticommutator carrier _ =>
      exactDimension16DerivativeAlphaReducedTensorSign h carrier
  | .fundamentalTrace carrier _ =>
      exactDimension16DerivativeAlphaReducedTensorSign h carrier

@[simp] theorem eomContextSign_one
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    eomContextSign 1 carrier field position = 1 := by
  simp [eomContextSign, fieldDerivativeContextSign]

theorem eomContextSign_mul
    (left right : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    eomContextSign (left * right) carrier field position =
      eomContextSign right carrier field position *
        eomContextSign left
          (exactDimension16DerivativeAlphaReducedAct right carrier)
          field position := by
  rcases carrier with ⟨fieldCount, sector⟩
  simp only [eomContextSign, fieldDerivativeContextSign,
    hypercubic_mul_def, Hypercubic4.axisSign_compose,
    Finset.prod_mul_distrib,
    exactDimension16DerivativeAlphaReducedAct,
    derivativeAlphaReducedSectorAct, orderedDerivativeWordAct]
  ac_rfl

@[simp] theorem physicalRelationGeneratorSign_one
    {policy : PhysicalRelationPolicy}
    (generator : PhysicalRelationGenerator policy) :
    physicalRelationGeneratorSign 1 generator = 1 := by
  cases generator <;>
    simp only [physicalRelationGeneratorSign,
      exactDimension16DerivativeAlphaReducedTensorSign_one,
      eomContextSign_one]

theorem physicalRelationGeneratorSign_mul
    {policy : PhysicalRelationPolicy} (left right : Hypercubic4)
    (generator : PhysicalRelationGenerator policy) :
    physicalRelationGeneratorSign (left * right) generator =
      physicalRelationGeneratorSign right generator *
        physicalRelationGeneratorSign left (generator.act right) := by
  cases generator <;>
    simp only [physicalRelationGeneratorSign, PhysicalRelationGenerator.act,
      exactDimension16DerivativeAlphaReducedTensorSign_mul,
      eomContextSign_mul]

def signedPhysicalRelationGeneratorActionBasis
    {policy : PhysicalRelationPolicy} (h : Hypercubic4)
    (generator : PhysicalRelationGenerator policy) :
    PhysicalRelationGeneratorSpace policy :=
  physicalRelationGeneratorSign h generator •
    Finsupp.single (generator.act h) 1

def signedPhysicalRelationGeneratorAction
    (policy : PhysicalRelationPolicy) (h : Hypercubic4) :
    PhysicalRelationGeneratorSpace policy →ₗ[ℚ]
      PhysicalRelationGeneratorSpace policy :=
  Finsupp.linearCombination ℚ
    (signedPhysicalRelationGeneratorActionBasis h)

@[simp] theorem signedPhysicalRelationGeneratorAction_single
    {policy : PhysicalRelationPolicy} (h : Hypercubic4)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ) :
    signedPhysicalRelationGeneratorAction policy h
        (Finsupp.single generator coefficient) =
      coefficient • signedPhysicalRelationGeneratorActionBasis h generator := by
  simp [signedPhysicalRelationGeneratorAction]

theorem signedPhysicalRelationGeneratorAction_single_explicit
    {policy : PhysicalRelationPolicy} (h : Hypercubic4)
    (generator : PhysicalRelationGenerator policy) (coefficient : ℚ) :
    signedPhysicalRelationGeneratorAction policy h
        (Finsupp.single generator coefficient) =
      Finsupp.single (generator.act h)
        (coefficient * physicalRelationGeneratorSign h generator) := by
  rw [signedPhysicalRelationGeneratorAction_single]
  simp [signedPhysicalRelationGeneratorActionBasis]

@[simp] theorem signedPhysicalRelationGeneratorAction_one
    (policy : PhysicalRelationPolicy)
    (value : PhysicalRelationGeneratorSpace policy) :
    signedPhysicalRelationGeneratorAction policy 1 value = value := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright =>
      rw [(signedPhysicalRelationGeneratorAction policy 1).map_add,
        hleft, hright]
  | single generator coefficient =>
      rw [signedPhysicalRelationGeneratorAction_single_explicit,
        PhysicalRelationGenerator.act_one,
        physicalRelationGeneratorSign_one]
      simp

theorem signedPhysicalRelationGeneratorAction_mul
    (policy : PhysicalRelationPolicy) (left right : Hypercubic4)
    (value : PhysicalRelationGeneratorSpace policy) :
    signedPhysicalRelationGeneratorAction policy (left * right) value =
      signedPhysicalRelationGeneratorAction policy left
        (signedPhysicalRelationGeneratorAction policy right value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add first second hfirst hsecond =>
      rw [map_add, map_add, map_add, hfirst, hsecond]
  | single generator coefficient =>
      rw [signedPhysicalRelationGeneratorAction_single_explicit,
        signedPhysicalRelationGeneratorAction_single_explicit,
        signedPhysicalRelationGeneratorAction_single_explicit,
        PhysicalRelationGenerator.act_mul,
        physicalRelationGeneratorSign_mul]
      congr 1
      ring

/-- The signed action on standard relation generators is a rational
representation of the literal hypercubic group. -/
def signedPhysicalRelationGeneratorRepresentation
    (policy : PhysicalRelationPolicy) :
    Representation ℚ Hypercubic4 (PhysicalRelationGeneratorSpace policy) where
  toFun := signedPhysicalRelationGeneratorAction policy
  map_one' := by
    apply LinearMap.ext
    exact signedPhysicalRelationGeneratorAction_one policy
  map_mul' left right := by
    apply LinearMap.ext
    exact signedPhysicalRelationGeneratorAction_mul policy left right

/-! ## Equivariance before rank -/

theorem physicalRelationRow_equivariant
    {policy : PhysicalRelationPolicy} (h : Hypercubic4)
    (generator : PhysicalRelationGenerator policy) :
    signedRelationAction h (physicalRelationRow generator) =
      physicalRelationGeneratorSign h generator •
        physicalRelationRow (generator.act h) := by
  cases generator with
  | antisymmetry carrier slot =>
      exact fieldAntisymmetryRow_equivariant h carrier slot
  | bianchi carrier field position innermost =>
      exact bianchiRow_equivariant h carrier field position innermost
  | eom enabled carrier field position innermost =>
      exact eomRow_equivariant h carrier field position innermost
  | integrationByParts carrier position outermost =>
      exact integrationByPartsRow_equivariant h carrier position outermost
  | traceless carrier field singleton =>
      exact tracelessLetterRow_equivariant h carrier field singleton
  | covariantCommutator carrier site =>
      exact covariantCommutatorRow_equivariant h site
  | traceAnticommutator carrier site =>
      exact traceAnticommutatorRow_equivariant h site
  | fundamentalTrace carrier site =>
      exact fundamentalTraceRow_equivariant h site

/-- The standard relation operator intertwines the signed action exactly. -/
theorem physicalRelationOperator_equivariant
    (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : PhysicalRelationGeneratorSpace policy) :
    physicalRelationOperator policy
        (signedPhysicalRelationGeneratorAction policy h value) =
      signedRelationAction h (physicalRelationOperator policy value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single generator coefficient =>
      simp [signedPhysicalRelationGeneratorActionBasis,
        physicalRelationRow_equivariant h generator, smul_smul]

def physicalRelationSubmodule (policy : PhysicalRelationPolicy) :
    Submodule ℚ RelationSpace :=
  LinearMap.range (physicalRelationOperator policy)

theorem physicalRelationSubmodule_signed_invariant
    (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : RelationSpace)
    (membership : value ∈ physicalRelationSubmodule policy) :
    signedRelationAction h value ∈ physicalRelationSubmodule policy := by
  rcases membership with ⟨source, rfl⟩
  exact ⟨signedPhysicalRelationGeneratorAction policy h source,
    physicalRelationOperator_equivariant policy h source⟩

/-! ## Transport through the exact contextual quotient -/

/-- Remaining standard relations after exact field-antisymmetry and
different-owner derivative localization.  Antisymmetry generators map to
zero here, as required by the proved contextual kernel theorem. -/
def normalizedPhysicalRelationOperator
    (policy : PhysicalRelationPolicy) :
    PhysicalRelationGeneratorSpace policy →ₗ[ℚ]
      ExactOrientedLocalSpace :=
  normalizeExactContextual.comp (physicalRelationOperator policy)

theorem normalizedPhysicalRelationOperator_equivariant
    (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : PhysicalRelationGeneratorSpace policy) :
    normalizedPhysicalRelationOperator policy
        (signedPhysicalRelationGeneratorAction policy h value) =
      signedExactOrientedLocalAction h
        (normalizedPhysicalRelationOperator policy value) := by
  rw [normalizedPhysicalRelationOperator, LinearMap.comp_apply,
    physicalRelationOperator_equivariant]
  exact normalizeExactContextual_signed_equivariant h
    (physicalRelationOperator policy value)

def normalizedPhysicalRelationSubmodule
    (policy : PhysicalRelationPolicy) :
    Submodule ℚ ExactOrientedLocalSpace :=
  LinearMap.range (normalizedPhysicalRelationOperator policy)

theorem normalizedPhysicalRelationSubmodule_signed_invariant
    (policy : PhysicalRelationPolicy) (h : Hypercubic4)
    (value : ExactOrientedLocalSpace)
    (membership : value ∈ normalizedPhysicalRelationSubmodule policy) :
    signedExactOrientedLocalAction h value ∈
      normalizedPhysicalRelationSubmodule policy := by
  rcases membership with ⟨source, rfl⟩
  exact ⟨signedPhysicalRelationGeneratorAction policy h source,
    normalizedPhysicalRelationOperator_equivariant policy h source⟩

end HypercubicDimension16PhysicalRelationOperator
end YangMills
end QuantumTheory
end Mettapedia
