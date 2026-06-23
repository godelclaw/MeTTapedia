import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mettapedia.Computability.PNP.FiniteSwitchingAdmissibility

/-!
# PNP v13 switching core prefix interface

Core switched-step, success-history, prefix-instantiation, and finite-count split utilities.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- One switched coordinate in the v13 product-success argument.  The event
used by the tower product is exact success of the observer's output bit on the
hidden target bit for this coordinate. -/
structure V13SwitchedStep (Ω : Type u) where
  coordinate : Nat
  observerBit : Ω → Bool
  targetBit : Ω → Bool

namespace V13SwitchedStep

/-- The exact-success event `A_j = B_j` for one switched coordinate. -/
def successEvent {Ω : Type u} (step : V13SwitchedStep Ω) : FiniteEvent Ω where
  pred := fun ω => step.observerBit ω = step.targetBit ω
  decidablePred := fun _ => inferInstance

end V13SwitchedStep

/-- The success-event history induced by an ordered list of v13 switched
coordinates. -/
def v13SuccessEvents {Ω : Type u} :
    List (V13SwitchedStep Ω) → List (FiniteEvent Ω)
  | [] => []
  | step :: rest => step.successEvent :: v13SuccessEvents rest

@[simp] theorem v13SuccessEvents_length {Ω : Type u}
    (steps : List (V13SwitchedStep Ω)) :
    (v13SuccessEvents steps).length = steps.length := by
  induction steps with
  | nil =>
      rfl
  | cons step rest ih =>
      simp [v13SuccessEvents, ih]

/-- A finite atom ledger for one v13 prefix.  The `Cell` type represents the
atoms of the full switched history field before the next coordinate.  The two
decomposition equalities say that these atoms exactly account for the current
success prefix and for the prefix plus the next success event.  The cellwise
half bound is the finite form of v13 admissibility on every positive or empty
history atom. -/
structure V13PrefixInstantiation {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) where
  Cell : Type u
  [fintypeCell : Fintype Cell]
  prefixCount : Cell → Nat
  successCount : Cell → Nat
  prefix_decomp :
    finiteHistoryCount Ω hist = Finset.univ.sum prefixCount
  success_decomp :
    finiteHistoryCount Ω (hist ++ [step.successEvent]) =
      Finset.univ.sum successCount
  cell_half : ∀ cell, 2 * successCount cell ≤ prefixCount cell

attribute [instance] V13PrefixInstantiation.fintypeCell

/-- Supplying a v13 atom ledger for one prefix implies the generic prefix
half-step required by the tower theorem. -/
theorem prefixHalfStep_of_v13PrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13PrefixInstantiation hist step) :
    PrefixHalfStep hist step.successEvent := by
  rw [PrefixHalfStep, cert.success_decomp, cert.prefix_decomp]
  calc
    2 * Finset.univ.sum cert.successCount =
        Finset.univ.sum (fun cell => 2 * cert.successCount cell) := by
        rw [Finset.mul_sum]
    _ ≤ Finset.univ.sum cert.prefixCount := by
        exact Finset.sum_le_sum (fun cell _ => cert.cell_half cell)

/-- The summary ledger above is exactly as strong as the generic prefix
half-step: when the prefix half-step holds, the whole history can be represented
as one abstract cell.  This is useful as a guardrail: a real v13 instantiation
must add semantic content about the cells, not merely supply this summary
ledger. -/
def v13PrefixInstantiation_of_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : PrefixHalfStep hist step.successEvent) :
    V13PrefixInstantiation hist step := by
  refine
    { Cell := PUnit.{u+1}
      prefixCount := fun _ => finiteHistoryCount Ω hist
      successCount := fun _ => finiteHistoryCount Ω (hist ++ [step.successEvent])
      prefix_decomp := ?_
      success_decomp := ?_
      cell_half := ?_ }
  · simp
  · simp
  · intro cell
    simpa [PrefixHalfStep] using h

/-- The proposition that the v13 atom-ledger obligation has been instantiated
for a particular prefix and next switched coordinate. -/
def V13PrefixInstantiated {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) : Prop :=
  Nonempty (V13PrefixInstantiation hist step)

theorem prefixHalfStep_of_v13PrefixInstantiated
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : V13PrefixInstantiated hist step) :
    PrefixHalfStep hist step.successEvent := by
  rcases h with ⟨cert⟩
  exact prefixHalfStep_of_v13PrefixInstantiation cert

/-- The abstract v13 summary-ledger proposition is equivalent to the generic
prefix half-step.  The later concrete-cell interface is the non-vacuous
instantiation target. -/
theorem v13PrefixInstantiated_iff_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13PrefixInstantiated hist step ↔
      PrefixHalfStep hist step.successEvent := by
  constructor
  · exact prefixHalfStep_of_v13PrefixInstantiated
  · intro h
    exact ⟨v13PrefixInstantiation_of_prefixHalfStep h⟩

/-- Failure of the generic prefix half-step rules out any v13 atom-ledger
instantiation for that prefix. -/
theorem not_v13PrefixInstantiated_of_not_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (hfail : ¬ PrefixHalfStep hist step.successEvent) :
    ¬ V13PrefixInstantiated hist step := by
  intro h
  exact hfail (prefixHalfStep_of_v13PrefixInstantiated h)

/-- Finite event counts respect pointwise logical equivalence. -/
theorem finiteEventCount_congr {Ω : Type u} [Fintype Ω]
    {E F : Ω → Prop} [DecidablePred E] [DecidablePred F]
    (h : ∀ ω, E ω ↔ F ω) :
    finiteEventCount Ω E = finiteEventCount Ω F := by
  apply le_antisymm
  · exact finiteEventCount_le_of_imp (fun ω hE => (h ω).1 hE)
  · exact finiteEventCount_le_of_imp (fun ω hF => (h ω).2 hF)

/-- Split a finite event by a decidable subevent. -/
def finiteEventSplitEquiv {Ω : Type u} {E F : Ω → Prop} [DecidablePred F] :
    {ω : Ω // E ω} ≃
      ({ω : Ω // E ω ∧ F ω} ⊕ {ω : Ω // E ω ∧ ¬ F ω}) where
  toFun := fun ω =>
    if hF : F ω.1 then Sum.inl ⟨ω.1, ω.2, hF⟩
    else Sum.inr ⟨ω.1, ω.2, hF⟩
  invFun := fun s =>
    match s with
    | Sum.inl ω => ⟨ω.1, ω.2.1⟩
    | Sum.inr ω => ⟨ω.1, ω.2.1⟩
  left_inv := by
    intro ω
    by_cases hF : F ω.1 <;> simp [hF]
  right_inv := by
    intro s
    cases s with
    | inl ω => simp [ω.2.2]
    | inr ω => simp [ω.2.2]

/-- A finite event count splits into the part satisfying a decidable subevent
and the complementary part. -/
theorem finiteEventCount_split {Ω : Type u} [Fintype Ω]
    {E F : Ω → Prop} [DecidablePred E] [DecidablePred F] :
    finiteEventCount Ω E =
      finiteEventCount Ω (fun ω => E ω ∧ F ω) +
        finiteEventCount Ω (fun ω => E ω ∧ ¬ F ω) := by
  change Fintype.card {ω : Ω // E ω} =
    Fintype.card {ω : Ω // E ω ∧ F ω} +
      Fintype.card {ω : Ω // E ω ∧ ¬ F ω}
  rw [Fintype.card_congr (finiteEventSplitEquiv (E := E) (F := F))]
  exact Fintype.card_sum

/-- A singleton extension of a history is the intersection of the history with
the final event. -/
theorem allEvents_append_singleton_iff {Ω : Type u}
    (hist : List (FiniteEvent Ω)) (E : FiniteEvent Ω) (ω : Ω) :
    allEvents (hist ++ [E]) ω ↔ allEvents hist ω ∧ E.pred ω := by
  induction hist with
  | nil =>
      simp [allEvents]
  | cons F rest ih =>
      simp [allEvents, ih, and_assoc]

/-- Counting a history extended by one event is the same as counting the
intersection of the old history and that event. -/
theorem finiteHistoryCount_append_singleton {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (E : FiniteEvent Ω) :
    finiteHistoryCount Ω (hist ++ [E]) =
      finiteEventCount Ω (fun ω => allEvents hist ω ∧ E.pred ω) := by
  simpa [finiteHistoryCount] using
    finiteEventCount_congr (Ω := Ω)
      (E := allEvents (hist ++ [E]))
      (F := fun ω => allEvents hist ω ∧ E.pred ω)
      (allEvents_append_singleton_iff hist E)

end Mettapedia.Computability.PNP
