import Mettapedia.QuantumTheory.YangMills.HypercubicDimension16CovariantCommutator
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Equivariant `SU(2)` trace-anticommutator rows

Every covariantly differentiated field-strength letter is a traceless
two-by-two matrix.  The polarized Cayley--Hamilton identity is therefore

`A * B + B * A = Matrix.trace (A * B) • 1`.

For adjacent letters in a trace cycle this gives

`Tr(U A B V) + Tr(U B A V) - Tr(A B) Tr(U V) = 0`.

This module constructs the last term by actually splitting the `A,B` pair
into a two-cycle and reconnecting the remaining trace word.  It does not
apply a four-letter identity to an arbitrary segment of a longer word.
-/

set_option autoImplicit false
noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicDimension16SU2TraceRelations

open V14HypercubicFDCensus
open HypercubicRawFDDimension16Census
open HypercubicDimension16AlphaReduction
open HypercubicDimension16RelationEquivariance

/-! ## The semantic two-by-two matrix identity -/

/-- The polarized Cayley--Hamilton identity for two traceless two-by-two
matrices over a commutative ring. -/
theorem traceless_fin_two_anticommutator
    {R : Type*} [CommRing R]
    (A B : Matrix (Fin 2) (Fin 2) R)
    (hA : Matrix.trace A = 0) (hB : Matrix.trace B = 0) :
    A * B + B * A =
      Matrix.trace (A * B) • (1 : Matrix (Fin 2) (Fin 2) R) := by
  simp only [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two] at hA hB
  have hA11 : A 1 1 = -A 0 0 := by
    linear_combination hA
  have hB11 : B 1 1 = -B 0 0 := by
    linear_combination hB
  ext i j
  fin_cases i <;> fin_cases j
  all_goals
    simp [Matrix.trace, Matrix.diag_apply, Fin.sum_univ_two,
      Matrix.mul_apply, Matrix.smul_apply,
      smul_eq_mul, Matrix.add_apply]
  all_goals rw [hA11, hB11]
  all_goals ring

/-- Trace-context form of the same identity.  The matrices `U,V` may be
arbitrary products; only the adjacent letters `A,B` are assumed traceless. -/
theorem traceless_fin_two_trace_anticommutator
    {R : Type*} [CommRing R]
    (U A B V : Matrix (Fin 2) (Fin 2) R)
    (hA : Matrix.trace A = 0) (hB : Matrix.trace B = 0) :
    Matrix.trace (U * (A * B) * V) +
        Matrix.trace (U * (B * A) * V) =
      Matrix.trace (A * B) * Matrix.trace (U * V) := by
  calc
    Matrix.trace (U * (A * B) * V) +
        Matrix.trace (U * (B * A) * V) =
        Matrix.trace (U * ((A * B) + (B * A)) * V) := by
          rw [mul_add, add_mul, Matrix.trace_add]
    _ = Matrix.trace
        (U * (Matrix.trace (A * B) •
          (1 : Matrix (Fin 2) (Fin 2) R)) * V) := by
          rw [traceless_fin_two_anticommutator A B hA hB]
    _ = Matrix.trace (A * B) * Matrix.trace (U * V) := by
          simp [Matrix.trace_smul]

/-- The six-term fundamental trace identity for two-by-two matrices.  Unlike
the traceless anticommutator specialization, this identity also joins and
splits distinct trace cycles. -/
theorem fin_two_fundamental_trace_identity
    {R : Type*} [CommRing R]
    (A B C : Matrix (Fin 2) (Fin 2) R) :
    Matrix.trace A * Matrix.trace B * Matrix.trace C -
        Matrix.trace (A * B) * Matrix.trace C -
        Matrix.trace (A * C) * Matrix.trace B -
        Matrix.trace (B * C) * Matrix.trace A +
        Matrix.trace ((A * B) * C) +
        Matrix.trace ((A * C) * B) = 0 := by
  simp [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Fin.sum_univ_two]
  ring

/-! ## An adjacent pair in a trace cycle -/

structure TraceAnticommutatorSite (carrier : RelationCarrier) where
  left : Fin carrier.1.1
  cycleLength_ge_three :
    carrier.2.trace.traceOrder
        (carrier.2.trace.traceOrder left) ≠ left

namespace TraceAnticommutatorSite

def right {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) : Fin carrier.1.1 :=
  carrier.2.trace.traceOrder site.left

def successor {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) : Fin carrier.1.1 :=
  carrier.2.trace.traceOrder site.right

def predecessor {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) : Fin carrier.1.1 :=
  carrier.2.trace.traceOrder.symm site.left

theorem successor_ne_left {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) :
    site.successor ≠ site.left :=
  site.cycleLength_ge_three

theorem right_ne_left {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) :
    site.right ≠ site.left := by
  intro hright
  apply site.successor_ne_left
  change carrier.2.trace.traceOrder site.right = site.left
  rw [hright]
  exact hright

theorem successor_ne_right {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) :
    site.successor ≠ site.right := by
  intro hsuccessor
  apply site.right_ne_left
  apply carrier.2.trace.traceOrder.injective
  exact hsuccessor

def act (h : Hypercubic4) {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) :
    TraceAnticommutatorSite
      (exactDimension16DerivativeAlphaReducedAct h carrier) where
  left := site.left
  cycleLength_ge_three := site.cycleLength_ge_three

@[simp] theorem act_left (h : Hypercubic4)
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    (site.act h).left = site.left := rfl

@[simp] theorem act_right (h : Hypercubic4)
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    (site.act h).right = site.right := rfl

@[simp] theorem act_successor (h : Hypercubic4)
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    (site.act h).successor = site.successor := rfl

end TraceAnticommutatorSite

/-! ## Exact cycle rewiring -/

/-- Replace `... P -> A -> B -> S ...` by
`... P -> B -> A -> S ...`. -/
def swapAdjacentTraceOrder {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) :
    Equiv.Perm (Fin carrier.1.1) :=
  carrier.2.trace.traceOrder.trans
    ((Equiv.swap site.right site.successor).trans
      (Equiv.swap site.left site.right))

/-- Replace `... P -> A -> B -> S ...` by a two-cycle `A <-> B`
and the bypass `... P -> S ...`. -/
def splitAdjacentTraceOrder {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) :
    Equiv.Perm (Fin carrier.1.1) :=
  carrier.2.trace.traceOrder.trans
    (Equiv.swap site.left site.successor)

@[simp] theorem swapAdjacentTraceOrder_apply_predecessor
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    swapAdjacentTraceOrder site site.predecessor = site.right := by
  rw [swapAdjacentTraceOrder, Equiv.trans_apply, Equiv.trans_apply]
  rw [TraceAnticommutatorSite.predecessor, Equiv.apply_symm_apply]
  rw [Equiv.swap_apply_of_ne_of_ne site.right_ne_left.symm
    site.successor_ne_left.symm]
  exact Equiv.swap_apply_left site.left site.right

@[simp] theorem swapAdjacentTraceOrder_apply_left
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    swapAdjacentTraceOrder site site.left = site.successor := by
  rw [swapAdjacentTraceOrder, Equiv.trans_apply, Equiv.trans_apply]
  rw [show carrier.2.trace.traceOrder site.left = site.right from rfl]
  rw [Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne
    site.successor_ne_left site.successor_ne_right

@[simp] theorem swapAdjacentTraceOrder_apply_right
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    swapAdjacentTraceOrder site site.right = site.left := by
  rw [swapAdjacentTraceOrder, Equiv.trans_apply, Equiv.trans_apply]
  rw [show carrier.2.trace.traceOrder site.right = site.successor from rfl]
  rw [Equiv.swap_apply_right]
  exact Equiv.swap_apply_right site.left site.right

@[simp] theorem splitAdjacentTraceOrder_apply_predecessor
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    splitAdjacentTraceOrder site site.predecessor = site.successor := by
  rw [splitAdjacentTraceOrder, Equiv.trans_apply]
  rw [TraceAnticommutatorSite.predecessor, Equiv.apply_symm_apply]
  exact Equiv.swap_apply_left site.left site.successor

@[simp] theorem splitAdjacentTraceOrder_apply_left
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    splitAdjacentTraceOrder site site.left = site.right := by
  rw [splitAdjacentTraceOrder, Equiv.trans_apply]
  rw [show carrier.2.trace.traceOrder site.left = site.right from rfl]
  exact Equiv.swap_apply_of_ne_of_ne site.right_ne_left
    site.successor_ne_right.symm

@[simp] theorem splitAdjacentTraceOrder_apply_right
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    splitAdjacentTraceOrder site site.right = site.left := by
  rw [splitAdjacentTraceOrder, Equiv.trans_apply]
  rw [show carrier.2.trace.traceOrder site.right = site.successor from rfl]
  exact Equiv.swap_apply_right site.left site.successor

def setTraceOrder (carrier : RelationCarrier)
    (traceOrder : Equiv.Perm (Fin carrier.1.1)) : RelationCarrier :=
  ⟨carrier.1,
    { trace := ⟨traceOrder⟩
      fieldFirst := carrier.2.fieldFirst
      fieldSecond := carrier.2.fieldSecond
      derivativeWord := carrier.2.derivativeWord }⟩

def swapAdjacentTraceCarrier {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) : RelationCarrier :=
  setTraceOrder carrier (swapAdjacentTraceOrder site)

def splitAdjacentTraceCarrier {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) : RelationCarrier :=
  setTraceOrder carrier (splitAdjacentTraceOrder site)

theorem setTraceOrder_act (h : Hypercubic4) (carrier : RelationCarrier)
    (traceOrder : Equiv.Perm (Fin carrier.1.1)) :
    exactDimension16DerivativeAlphaReducedAct h
        (setTraceOrder carrier traceOrder) =
      setTraceOrder
        (exactDimension16DerivativeAlphaReducedAct h carrier) traceOrder := by
  rcases carrier with ⟨fieldCount, sector⟩
  rfl

theorem setTraceOrder_tensorSign (h : Hypercubic4)
    (carrier : RelationCarrier)
    (traceOrder : Equiv.Perm (Fin carrier.1.1)) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (setTraceOrder carrier traceOrder) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier := by
  rcases carrier with ⟨fieldCount, sector⟩
  rfl

theorem swapAdjacentTraceCarrier_act (h : Hypercubic4)
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    exactDimension16DerivativeAlphaReducedAct h
        (swapAdjacentTraceCarrier site) =
      swapAdjacentTraceCarrier (site.act h) := by
  exact setTraceOrder_act h carrier (swapAdjacentTraceOrder site)

theorem splitAdjacentTraceCarrier_act (h : Hypercubic4)
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    exactDimension16DerivativeAlphaReducedAct h
        (splitAdjacentTraceCarrier site) =
      splitAdjacentTraceCarrier (site.act h) := by
  exact setTraceOrder_act h carrier (splitAdjacentTraceOrder site)

theorem swapAdjacentTraceCarrier_tensorSign (h : Hypercubic4)
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (swapAdjacentTraceCarrier site) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier :=
  setTraceOrder_tensorSign h carrier (swapAdjacentTraceOrder site)

theorem splitAdjacentTraceCarrier_tensorSign (h : Hypercubic4)
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (splitAdjacentTraceCarrier site) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier :=
  setTraceOrder_tensorSign h carrier (splitAdjacentTraceOrder site)

/-! ## The sparse equivariant relation row -/

/-- The trace-anticommutator relation
`Tr(UABV) + Tr(UBAV) - Tr(AB) Tr(UV) = 0`. -/
def traceAnticommutatorRow {carrier : RelationCarrier}
    (site : TraceAnticommutatorSite carrier) : RelationSpace :=
  Finsupp.single carrier 1 +
    Finsupp.single (swapAdjacentTraceCarrier site) 1 -
    Finsupp.single (splitAdjacentTraceCarrier site) 1

theorem traceAnticommutatorRow_equivariant (h : Hypercubic4)
    {carrier : RelationCarrier} (site : TraceAnticommutatorSite carrier) :
    signedRelationAction h (traceAnticommutatorRow site) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        traceAnticommutatorRow (site.act h) := by
  simp [traceAnticommutatorRow, swapAdjacentTraceCarrier_act,
    splitAdjacentTraceCarrier_act, swapAdjacentTraceCarrier_tensorSign,
    splitAdjacentTraceCarrier_tensorSign, smul_sub, smul_add]

/-! ## The fundamental three-cut trace identity -/

/-- Three distinct cut labels for the fundamental `2 × 2` trace identity. -/
structure FundamentalTraceSite (carrier : RelationCarrier) where
  label : Fin 3 ↪ Fin carrier.1.1

namespace FundamentalTraceSite

def first {carrier : RelationCarrier}
    (site : FundamentalTraceSite carrier) : Fin carrier.1.1 :=
  site.label 0

def second {carrier : RelationCarrier}
    (site : FundamentalTraceSite carrier) : Fin carrier.1.1 :=
  site.label 1

def third {carrier : RelationCarrier}
    (site : FundamentalTraceSite carrier) : Fin carrier.1.1 :=
  site.label 2

theorem first_ne_second {carrier : RelationCarrier}
    (site : FundamentalTraceSite carrier) :
    site.first ≠ site.second := by
  exact site.label.injective.ne (by decide)

theorem first_ne_third {carrier : RelationCarrier}
    (site : FundamentalTraceSite carrier) :
    site.first ≠ site.third := by
  exact site.label.injective.ne (by decide)

theorem second_ne_third {carrier : RelationCarrier}
    (site : FundamentalTraceSite carrier) :
    site.second ≠ site.third := by
  exact site.label.injective.ne (by decide)

def act (h : Hypercubic4) {carrier : RelationCarrier}
    (site : FundamentalTraceSite carrier) :
    FundamentalTraceSite
      (exactDimension16DerivativeAlphaReducedAct h carrier) where
  label := site.label

@[simp] theorem act_label (h : Hypercubic4)
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier) :
    (site.act h).label = site.label := rfl

@[simp] theorem act_first (h : Hypercubic4)
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier) :
    (site.act h).first = site.first := rfl

@[simp] theorem act_second (h : Hypercubic4)
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier) :
    (site.act h).second = site.second := rfl

@[simp] theorem act_third (h : Hypercubic4)
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier) :
    (site.act h).third = site.third := rfl

end FundamentalTraceSite

def fundamentalCycleForward {carrier : RelationCarrier}
    (site : FundamentalTraceSite carrier) :
    Equiv.Perm (Fin carrier.1.1) :=
  (Equiv.swap site.second site.third).trans
    (Equiv.swap site.first site.second)

def fundamentalCycleBackward {carrier : RelationCarrier}
    (site : FundamentalTraceSite carrier) :
    Equiv.Perm (Fin carrier.1.1) :=
  (Equiv.swap site.first site.second).trans
    (Equiv.swap site.second site.third)

@[simp] theorem fundamentalCycleForward_apply_first
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier) :
    fundamentalCycleForward site site.first = site.second := by
  rw [fundamentalCycleForward, Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne site.first_ne_second
    site.first_ne_third]
  exact Equiv.swap_apply_left site.first site.second

@[simp] theorem fundamentalCycleForward_apply_second
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier) :
    fundamentalCycleForward site site.second = site.third := by
  rw [fundamentalCycleForward, Equiv.trans_apply,
    Equiv.swap_apply_left]
  exact Equiv.swap_apply_of_ne_of_ne
    site.first_ne_third.symm site.second_ne_third.symm

@[simp] theorem fundamentalCycleForward_apply_third
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier) :
    fundamentalCycleForward site site.third = site.first := by
  rw [fundamentalCycleForward, Equiv.trans_apply,
    Equiv.swap_apply_right, Equiv.swap_apply_right]

@[simp] theorem fundamentalCycleBackward_apply_first
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier) :
    fundamentalCycleBackward site site.first = site.third := by
  rw [fundamentalCycleBackward, Equiv.trans_apply,
    Equiv.swap_apply_left, Equiv.swap_apply_left]

@[simp] theorem fundamentalCycleBackward_apply_second
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier) :
    fundamentalCycleBackward site site.second = site.first := by
  rw [fundamentalCycleBackward, Equiv.trans_apply,
    Equiv.swap_apply_right]
  exact Equiv.swap_apply_of_ne_of_ne site.first_ne_second
    site.first_ne_third

@[simp] theorem fundamentalCycleBackward_apply_third
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier) :
    fundamentalCycleBackward site site.third = site.second := by
  rw [fundamentalCycleBackward, Equiv.trans_apply]
  rw [Equiv.swap_apply_of_ne_of_ne site.first_ne_third.symm
    site.second_ne_third.symm]
  exact Equiv.swap_apply_right site.second site.third

/-- Rewire the three selected outgoing trace edges by `rewire`. -/
def rewireTraceCarrier (carrier : RelationCarrier)
    (rewire : Equiv.Perm (Fin carrier.1.1)) : RelationCarrier :=
  setTraceOrder carrier (carrier.2.trace.traceOrder.trans rewire)

theorem rewireTraceCarrier_act (h : Hypercubic4)
    (carrier : RelationCarrier)
    (rewire : Equiv.Perm (Fin carrier.1.1)) :
    exactDimension16DerivativeAlphaReducedAct h
        (rewireTraceCarrier carrier rewire) =
      rewireTraceCarrier
        (exactDimension16DerivativeAlphaReducedAct h carrier) rewire := by
  exact setTraceOrder_act h carrier _

theorem rewireTraceCarrier_tensorSign (h : Hypercubic4)
    (carrier : RelationCarrier)
    (rewire : Equiv.Perm (Fin carrier.1.1)) :
    exactDimension16DerivativeAlphaReducedTensorSign h
        (rewireTraceCarrier carrier rewire) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier :=
  setTraceOrder_tensorSign h carrier _

/-- The diagrammatic fundamental trace identity
`Σ_{σ ∈ S₃} sign(σ) Tr_{πσ} = 0`, written as its six sparse terms. -/
def fundamentalTraceRow {carrier : RelationCarrier}
    (site : FundamentalTraceSite carrier) : RelationSpace :=
  Finsupp.single carrier 1 -
    Finsupp.single
      (rewireTraceCarrier carrier
        (Equiv.swap site.first site.second)) 1 -
    Finsupp.single
      (rewireTraceCarrier carrier
        (Equiv.swap site.first site.third)) 1 -
    Finsupp.single
      (rewireTraceCarrier carrier
        (Equiv.swap site.second site.third)) 1 +
    Finsupp.single
      (rewireTraceCarrier carrier (fundamentalCycleForward site)) 1 +
    Finsupp.single
      (rewireTraceCarrier carrier (fundamentalCycleBackward site)) 1

theorem fundamentalTraceRow_equivariant (h : Hypercubic4)
    {carrier : RelationCarrier} (site : FundamentalTraceSite carrier) :
    signedRelationAction h (fundamentalTraceRow site) =
      exactDimension16DerivativeAlphaReducedTensorSign h carrier •
        fundamentalTraceRow (site.act h) := by
  simp [fundamentalTraceRow, rewireTraceCarrier_act,
    rewireTraceCarrier_tensorSign, fundamentalCycleForward,
    fundamentalCycleBackward, smul_sub, smul_add]
  rfl

end HypercubicDimension16SU2TraceRelations
end YangMills
end QuantumTheory
end Mettapedia
