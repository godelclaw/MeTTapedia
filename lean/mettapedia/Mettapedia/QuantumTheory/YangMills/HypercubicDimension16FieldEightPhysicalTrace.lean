import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16PhysicalOrbitOperator
import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16SignedOrbitCoinvariants

/-!
# The standard physical trace operator on the eight-field sector

The derivative-free eight-field trace relations are the literal one-letter
traceless row, polarized Cayley--Hamilton anticommutator row, and six-term
fundamental `2 x 2` trace row on the genuine field-relabel orbit module.  The
three row schemas and their signed hypercubic intertwining law are defined
before any finite chart or rank computation.
-/

set_option autoImplicit false
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16FieldEightPhysicalTrace

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16LocalWordCarrier
open HypercubicDimension16PhysicalInvariantSpace
open HypercubicDimension16SignedOrbitCoinvariants

structure FieldEightTracelessSite where
  sector : LabeledLocalWordSector 8 0
  field : Fin 8
  singleton : sector.trace field = field

structure FieldEightAnticommutatorSite where
  sector : LabeledLocalWordSector 8 0
  left : Fin 8
  cycleLength_ge_three : sector.trace (sector.trace left) ≠ left

structure FieldEightFundamentalSite where
  sector : LabeledLocalWordSector 8 0
  label : Fin 3 ↪ Fin 8

inductive FieldEightTraceGenerator where
  | traceless (site : FieldEightTracelessSite)
  | anticommutator (site : FieldEightAnticommutatorSite)
  | fundamental (site : FieldEightFundamentalSite)

def setFieldEightTraceOrder (sector : LabeledLocalWordSector 8 0)
    (traceOrder : Equiv.Perm (Fin 8)) : LabeledLocalWordSector 8 0 where
  trace := traceOrder
  decoration := sector.decoration

@[simp] theorem setFieldEightTraceOrder_self
    (sector : LabeledLocalWordSector 8 0) :
    setFieldEightTraceOrder sector sector.trace = sector := by
  rfl

def fieldEightOrbitSingle (sector : LabeledLocalWordSector 8 0) :
    FieldEightOrbitSpace :=
  Finsupp.single (Quotient.mk _ sector) 1

def fieldEightSwapAdjacentTraceOrder
    (site : FieldEightAnticommutatorSite) : Equiv.Perm (Fin 8) :=
  let right := site.sector.trace site.left
  let successor := site.sector.trace right
  site.sector.trace.trans
    ((Equiv.swap right successor).trans (Equiv.swap site.left right))

def fieldEightSplitAdjacentTraceOrder
    (site : FieldEightAnticommutatorSite) : Equiv.Perm (Fin 8) :=
  let successor := site.sector.trace (site.sector.trace site.left)
  site.sector.trace.trans (Equiv.swap site.left successor)

def fieldEightFundamentalCycleForward
    (site : FieldEightFundamentalSite) : Equiv.Perm (Fin 8) :=
  (Equiv.swap (site.label 1) (site.label 2)).trans
    (Equiv.swap (site.label 0) (site.label 1))

def fieldEightFundamentalCycleBackward
    (site : FieldEightFundamentalSite) : Equiv.Perm (Fin 8) :=
  (Equiv.swap (site.label 0) (site.label 1)).trans
    (Equiv.swap (site.label 1) (site.label 2))

/-- The three standard derivative-free `SU(2)` trace families written on the
genuine field-relabel orbit carrier. -/
def fieldEightPhysicalTraceRow :
    FieldEightTraceGenerator → FieldEightOrbitSpace
  | .traceless site => fieldEightOrbitSingle site.sector
  | .anticommutator site =>
      fieldEightOrbitSingle site.sector +
        fieldEightOrbitSingle
          (setFieldEightTraceOrder site.sector
            (fieldEightSwapAdjacentTraceOrder site)) -
        fieldEightOrbitSingle
          (setFieldEightTraceOrder site.sector
            (fieldEightSplitAdjacentTraceOrder site))
  | .fundamental site =>
      fieldEightOrbitSingle site.sector -
        fieldEightOrbitSingle
          (setFieldEightTraceOrder site.sector
            (site.sector.trace.trans
              (Equiv.swap (site.label 0) (site.label 1)))) -
        fieldEightOrbitSingle
          (setFieldEightTraceOrder site.sector
            (site.sector.trace.trans
              (Equiv.swap (site.label 0) (site.label 2)))) -
        fieldEightOrbitSingle
          (setFieldEightTraceOrder site.sector
            (site.sector.trace.trans
              (Equiv.swap (site.label 1) (site.label 2)))) +
        fieldEightOrbitSingle
          (setFieldEightTraceOrder site.sector
            (site.sector.trace.trans
              (fieldEightFundamentalCycleForward site))) +
        fieldEightOrbitSingle
          (setFieldEightTraceOrder site.sector
            (site.sector.trace.trans
              (fieldEightFundamentalCycleBackward site)))

def FieldEightTraceGenerator.act (h : Hypercubic4) :
    FieldEightTraceGenerator → FieldEightTraceGenerator
  | .traceless site =>
      .traceless
        { sector := site.sector.hypercubicAct h
          field := site.field
          singleton := site.singleton }
  | .anticommutator site =>
      .anticommutator
        { sector := site.sector.hypercubicAct h
          left := site.left
          cycleLength_ge_three := site.cycleLength_ge_three }
  | .fundamental site =>
      .fundamental
        { sector := site.sector.hypercubicAct h
          label := site.label }

def FieldEightTraceGenerator.tensorSign
    (h : Hypercubic4) : FieldEightTraceGenerator → ℚ
  | .traceless site => site.sector.tensorSign h
  | .anticommutator site => site.sector.tensorSign h
  | .fundamental site => site.sector.tensorSign h

@[simp] theorem fieldEightSwapAdjacentTraceOrder_act
    (h : Hypercubic4) (site : FieldEightAnticommutatorSite) :
    fieldEightSwapAdjacentTraceOrder
        { sector := site.sector.hypercubicAct h
          left := site.left
          cycleLength_ge_three := site.cycleLength_ge_three } =
      fieldEightSwapAdjacentTraceOrder site := by
  rfl

@[simp] theorem fieldEightSplitAdjacentTraceOrder_act
    (h : Hypercubic4) (site : FieldEightAnticommutatorSite) :
    fieldEightSplitAdjacentTraceOrder
        { sector := site.sector.hypercubicAct h
          left := site.left
          cycleLength_ge_three := site.cycleLength_ge_three } =
      fieldEightSplitAdjacentTraceOrder site := by
  rfl

@[simp] theorem fieldEightFundamentalCycleForward_act
    (h : Hypercubic4) (site : FieldEightFundamentalSite) :
    fieldEightFundamentalCycleForward
        { sector := site.sector.hypercubicAct h
          label := site.label } =
      fieldEightFundamentalCycleForward site := by
  rfl

@[simp] theorem fieldEightFundamentalCycleBackward_act
    (h : Hypercubic4) (site : FieldEightFundamentalSite) :
    fieldEightFundamentalCycleBackward
        { sector := site.sector.hypercubicAct h
          label := site.label } =
      fieldEightFundamentalCycleBackward site := by
  rfl

@[simp] theorem setFieldEightTraceOrder_hypercubicAct
    (sector : LabeledLocalWordSector 8 0)
    (traceOrder : Equiv.Perm (Fin 8)) (h : Hypercubic4) :
    (setFieldEightTraceOrder sector traceOrder).hypercubicAct h =
      setFieldEightTraceOrder (sector.hypercubicAct h) traceOrder := by
  rfl

@[simp] theorem hypercubicAct_trace_fieldEight
    (sector : LabeledLocalWordSector 8 0) (h : Hypercubic4) :
    (sector.hypercubicAct h).trace = sector.trace := by
  rfl

@[simp] theorem setFieldEightTraceOrder_tensorSign
    (sector : LabeledLocalWordSector 8 0)
    (traceOrder : Equiv.Perm (Fin 8)) (h : Hypercubic4) :
    (setFieldEightTraceOrder sector traceOrder).tensorSign h =
      sector.tensorSign h := by
  rfl

theorem signedSectorFieldOrbitAction_fieldEightOrbitSingle
    (h : Hypercubic4) (sector : LabeledLocalWordSector 8 0) :
    signedSectorFieldOrbitAction h 8 0 (fieldEightOrbitSingle sector) =
      sector.tensorSign h •
        fieldEightOrbitSingle (sector.hypercubicAct h) := by
  simp [fieldEightOrbitSingle]

/-- Equivariance is inherited term by term before any rank computation. -/
theorem fieldEightPhysicalTraceRow_equivariant
    (h : Hypercubic4) (generator : FieldEightTraceGenerator) :
    signedSectorFieldOrbitAction h 8 0
        (fieldEightPhysicalTraceRow generator) =
      generator.tensorSign h •
        fieldEightPhysicalTraceRow (generator.act h) := by
  cases generator with
  | traceless site =>
      exact signedSectorFieldOrbitAction_fieldEightOrbitSingle h site.sector
  | anticommutator site =>
      simp [fieldEightPhysicalTraceRow, FieldEightTraceGenerator.act,
        FieldEightTraceGenerator.tensorSign,
        fieldEightSwapAdjacentTraceOrder,
        fieldEightSplitAdjacentTraceOrder,
        signedSectorFieldOrbitAction_fieldEightOrbitSingle,
        smul_add, smul_sub]
  | fundamental site =>
      simp [fieldEightPhysicalTraceRow, FieldEightTraceGenerator.act,
        FieldEightTraceGenerator.tensorSign,
        fieldEightFundamentalCycleForward,
        fieldEightFundamentalCycleBackward,
        signedSectorFieldOrbitAction_fieldEightOrbitSingle,
        smul_add, smul_sub]

def fieldEightPhysicalTraceOperator :
    (FieldEightTraceGenerator →₀ ℚ) →ₗ[ℚ] FieldEightOrbitSpace :=
  Finsupp.linearCombination ℚ fieldEightPhysicalTraceRow

def signedFieldEightTraceGeneratorActionBasis (h : Hypercubic4)
    (generator : FieldEightTraceGenerator) :
    FieldEightTraceGenerator →₀ ℚ :=
  generator.tensorSign h • Finsupp.single (generator.act h) 1

def signedFieldEightTraceGeneratorAction (h : Hypercubic4) :
    (FieldEightTraceGenerator →₀ ℚ) →ₗ[ℚ]
      (FieldEightTraceGenerator →₀ ℚ) :=
  Finsupp.linearCombination ℚ
    (signedFieldEightTraceGeneratorActionBasis h)

@[simp] theorem fieldEightPhysicalTraceOperator_single
    (generator : FieldEightTraceGenerator) (coefficient : ℚ) :
    fieldEightPhysicalTraceOperator
        (Finsupp.single generator coefficient) =
      coefficient • fieldEightPhysicalTraceRow generator := by
  simp [fieldEightPhysicalTraceOperator]

/-- The sector trace operator intertwines the literal signed hypercubic
actions. -/
theorem fieldEightPhysicalTraceOperator_equivariant
    (h : Hypercubic4) (value : FieldEightTraceGenerator →₀ ℚ) :
    fieldEightPhysicalTraceOperator
        (signedFieldEightTraceGeneratorAction h value) =
      signedSectorFieldOrbitAction h 8 0
        (fieldEightPhysicalTraceOperator value) := by
  induction value using Finsupp.induction_linear with
  | zero => simp
  | add left right hleft hright => simp [map_add, hleft, hright]
  | single generator coefficient =>
      simp [signedFieldEightTraceGeneratorAction,
        signedFieldEightTraceGeneratorActionBasis,
        fieldEightPhysicalTraceRow_equivariant, smul_smul]

/-- Standard trace rows after imposing the independently defined signed
hypercubic coinvariant relations. -/
def fieldEightCoinvariantTraceRow
    (generator : FieldEightTraceGenerator) :
    FieldEightSignedOrbitCoinvariant :=
  Submodule.Quotient.mk (fieldEightPhysicalTraceRow generator)

def fieldEightPhysicalTraceRelationSubmodule :
    Submodule ℚ FieldEightSignedOrbitCoinvariant :=
  Submodule.span ℚ (Set.range fieldEightCoinvariantTraceRow)

abbrev FieldEightPhysicalTraceQuotient :=
  FieldEightSignedOrbitCoinvariant ⧸
    fieldEightPhysicalTraceRelationSubmodule

end HypercubicDimension16FieldEightPhysicalTrace
end YangMills
end QuantumTheory
end Mettapedia
