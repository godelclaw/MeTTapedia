import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16DifferentialRelations

/-!
# Equivariant integration-by-parts and traceless-letter rows

An integrated total covariant derivative is represented by choosing a
globally outermost derivative position and summing over every possible field
owner.  This is the integration-by-parts row on the local action sector.

The trace permutation already represents disjoint cyclic words without a
chosen starting point or an ordering of trace factors.  Uniform field-label
alpha rows identify conjugate labeled presentations.  The remaining
elementary `SU(2)` trace relation supplied here kills a one-letter trace,
because every covariantly differentiated field strength is traceless.
-/

set_option autoImplicit false
noncomputable section

open scoped BigOperators

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16IBPTraceRelations

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance

/-! ## Integrated total derivatives -/

/-- A position which precedes every other position in the global ordered-word
presentation.  Different-owner shuffle rows make this a common outer slot for
all field words. -/
def IsGloballyOutermostDerivative (carrier : RelationCarrier)
    (position : Fin (dimension16DerivativeCount carrier.1)) : Prop :=
  ∀ other, position ≤ other

theorem isGloballyOutermostDerivative_act_iff (h : Hypercubic4)
    (carrier : RelationCarrier)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    IsGloballyOutermostDerivative
        (exactDimension16DerivativeAlphaReducedAct h carrier) position ↔
      IsGloballyOutermostDerivative carrier position := by
  rfl

def setDerivativeOwner (carrier : RelationCarrier)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (field : Fin carrier.1.1) : RelationCarrier :=
  ⟨carrier.1,
    { trace := carrier.2.trace
      fieldFirst := carrier.2.fieldFirst
      fieldSecond := carrier.2.fieldSecond
      derivativeWord :=
        { ownerAtPosition := Function.update
            carrier.2.derivativeWord.ownerAtPosition position field
          axisAtPosition := carrier.2.derivativeWord.axisAtPosition } }⟩

theorem setDerivativeOwner_act (h : Hypercubic4)
    (carrier : RelationCarrier)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (field : Fin carrier.1.1) :
    exactDimension16DerivativeAlphaReducedAct h
        (setDerivativeOwner carrier position field) =
      setDerivativeOwner
        (exactDimension16DerivativeAlphaReducedAct h carrier)
        position field := by
  rcases carrier with ⟨fieldCount, sector⟩
  rfl

theorem setDerivativeOwner_tensorSign (h : Hypercubic4)
    (carrier : RelationCarrier)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (field : Fin carrier.1.1) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (setDerivativeOwner carrier position field) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier := by
  rcases carrier with ⟨fieldCount, sector⟩
  rfl

/-- The product-rule sum for an integrated total covariant derivative. -/
def integrationByPartsRow (carrier : RelationCarrier)
    (position : Fin (dimension16DerivativeCount carrier.1)) :
    RelationSpace :=
  ∑ field : Fin carrier.1.1,
    Finsupp.single (setDerivativeOwner carrier position field) 1

theorem integrationByPartsRow_equivariant (h : Hypercubic4)
    (carrier : RelationCarrier)
    (position : Fin (dimension16DerivativeCount carrier.1))
    (_houtermost : IsGloballyOutermostDerivative carrier position) :
    signedRelationAction h
        (integrationByPartsRow carrier position) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        integrationByPartsRow
          (exactDimension16DerivativeAlphaReducedAct h carrier) position := by
  rcases carrier with ⟨fieldCount, sector⟩
  change signedRelationAction h
      (integrationByPartsRow (⟨fieldCount, sector⟩ : RelationCarrier)
        position) =
    exactDimension16DerivativeAlphaReducedTensorSign h
        (⟨fieldCount, sector⟩ : RelationCarrier) •
      integrationByPartsRow
        (⟨fieldCount, derivativeAlphaReducedSectorAct h sector⟩ :
          RelationCarrier) position
  unfold integrationByPartsRow
  rw [map_sum, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro field _
  have howner := setDerivativeOwner_act h
    (⟨fieldCount, sector⟩ : RelationCarrier) position field
  change exactDimension16DerivativeAlphaReducedAct h
      (setDerivativeOwner (⟨fieldCount, sector⟩ : RelationCarrier)
        position field) =
    setDerivativeOwner
      (⟨fieldCount, derivativeAlphaReducedSectorAct h sector⟩ :
        RelationCarrier) position field at howner
  rw [signedRelationAction_single, howner,
    setDerivativeOwner_tensorSign]
  simp

/-! ## Traceless one-letter trace words -/

def IsSingletonTrace (carrier : RelationCarrier)
    (field : Fin carrier.1.1) : Prop :=
  carrier.2.trace.traceOrder field = field

theorem isSingletonTrace_act_iff (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1) :
    IsSingletonTrace
        (exactDimension16DerivativeAlphaReducedAct h carrier) field ↔
      IsSingletonTrace carrier field := by
  rfl

/-- `Tr X = 0` for a single traceless `su(2)`-valued letter `X`. -/
def tracelessLetterRow (carrier : RelationCarrier)
    (_field : Fin carrier.1.1) : RelationSpace :=
  Finsupp.single carrier 1

theorem tracelessLetterRow_equivariant (h : Hypercubic4)
    (carrier : RelationCarrier) (field : Fin carrier.1.1)
    (_hsingleton : IsSingletonTrace carrier field) :
    signedRelationAction h (tracelessLetterRow carrier field) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        tracelessLetterRow
          (exactDimension16DerivativeAlphaReducedAct h carrier) field := by
  simp [tracelessLetterRow]

end HypercubicDimension16IBPTraceRelations
end YangMills
end QuantumTheory
end Mettapedia
