import Mettapedia.Computability.PNP.PNPv13SwitchingHistoryFieldPrefix

/-!
# PNP v13 switching: same-cell failure matching

Success/failure fibers, same-cell matching, and the equivalence between fixed-field prefix certificates and constructive failure matching.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- The successful points in a supplied history cell for the next v13 switched
coordinate. -/
def V13CellSuccessFiber {Ω : Type u} [Fintype Ω]
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) (cell : field.Cell) : Type u :=
  {ω : Ω // allEvents hist ω ∧ field.cellOf ω = cell ∧ step.successEvent.pred ω}

/-- The unsuccessful points in a supplied history cell for the next v13
switched coordinate. -/
def V13CellFailureFiber {Ω : Type u} [Fintype Ω]
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) (cell : field.Cell) : Type u :=
  {ω : Ω // allEvents hist ω ∧ field.cellOf ω = cell ∧ ¬ step.successEvent.pred ω}

instance v13CellSuccessFiber_fintype {Ω : Type u} [Fintype Ω]
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) (cell : field.Cell) :
    Fintype (V13CellSuccessFiber field hist step cell) := by
  unfold V13CellSuccessFiber
  infer_instance

instance v13CellFailureFiber_fintype {Ω : Type u} [Fintype Ω]
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) (cell : field.Cell) :
    Fintype (V13CellFailureFiber field hist step cell) := by
  unfold V13CellFailureFiber
  infer_instance

/-- The operational fixed-field obligation: in every supplied history cell,
successful prefix points can be injectively matched to unsuccessful prefix
points in the same cell. -/
def V13FieldFailureMatching {Ω : Type u} [Fintype Ω]
    (field : V13HistoryField Ω) (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) : Prop :=
  ∀ cell, Nonempty
    (V13CellSuccessFiber field hist step cell ↪
      V13CellFailureFiber field hist step cell)

/-- A same-cell failure matching gives an explicit failed prefix point in the
same supplied field cell for every successful prefix point. -/
theorem exists_sameCell_failure_of_fieldFailureMatching_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step)
    {ω : Ω} (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω) :
    ∃ ω' : Ω,
      allEvents hist ω' ∧
        field.cellOf ω' = field.cellOf ω ∧
          ¬ step.successEvent.pred ω' := by
  rcases hmatch (field.cellOf ω) with ⟨emb⟩
  rcases emb ⟨ω, hhist, rfl, hsucc⟩ with ⟨ω', hω'⟩
  exact ⟨ω', hω'.1, hω'.2.1, hω'.2.2⟩

/-- If one successful prefix point has no failed prefix point in its supplied
field cell, the same-cell failure matching obligation is impossible. -/
theorem not_v13FieldFailureMatching_of_success_without_sameCell_failure
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} {ω : Ω}
    (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents hist ω' →
          field.cellOf ω' = field.cellOf ω →
            step.successEvent.pred ω') :
    ¬ V13FieldFailureMatching field hist step := by
  intro hmatch
  rcases exists_sameCell_failure_of_fieldFailureMatching_success
      hmatch hhist hsucc with
    ⟨ω', hhist', hcell', hfail'⟩
  exact hfail' (hnoFailure hhist' hcell')

/-- The same-cell failure matching interface is exactly the per-cell
success-versus-failure count balance. -/
theorem v13FieldFailureMatching_iff_success_le_failure
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} :
    V13FieldFailureMatching field hist step ↔
      ∀ cell,
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
          v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell := by
  constructor
  · intro hmatch cell
    rcases hmatch cell with ⟨emb⟩
    have hcard := Fintype.card_le_of_embedding emb
    simpa [V13CellSuccessFiber, V13CellFailureFiber,
      v13ConcreteSuccessCount, v13ConcreteFailureCount, finiteEventCount]
      using hcard
  · intro hbalance cell
    rw [Function.Embedding.nonempty_iff_card_le]
    simpa [V13CellSuccessFiber, V13CellFailureFiber,
      v13ConcreteSuccessCount, v13ConcreteFailureCount, finiteEventCount]
      using hbalance cell

/-- If fixed-field same-cell matching fails, then some supplied cell has more
next-success prefix points than next-failure prefix points. -/
theorem exists_bad_cell_of_not_v13FieldFailureMatching
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hfail : ¬ V13FieldFailureMatching field hist step) :
    ∃ cell : field.Cell,
      v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell <
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell := by
  by_contra hno
  have hbalance :
      ∀ cell,
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell ≤
          v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell := by
    intro cell
    exact le_of_not_gt (by
      intro hbad
      exact hno ⟨cell, hbad⟩)
  exact hfail (v13FieldFailureMatching_iff_success_le_failure.mpr hbalance)

/-- A fixed-field v13 prefix certificate is equivalent to an explicit
same-cell injection from successful prefix points to unsuccessful prefix
points.  This is the constructive interface a proof of v13 sequential
admissibility must supply after the field is fixed. -/
theorem v13FieldPrefixInstantiation_iff_failureMatching
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} :
    V13FieldPrefixInstantiation field hist step ↔
      V13FieldFailureMatching field hist step := by
  constructor
  · intro cert
    exact v13FieldFailureMatching_iff_success_le_failure.mpr
      (v13FieldPrefixInstantiation_iff_success_le_failure.mp cert)
  · intro hmatch
    exact v13FieldPrefixInstantiation_iff_success_le_failure.mpr
      (v13FieldFailureMatching_iff_success_le_failure.mp hmatch)

/-- An explicit same-cell success-to-failure matching is sufficient to build
the fixed-field prefix certificate. -/
def v13FieldPrefixInstantiation_of_failureMatching
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hmatch : V13FieldFailureMatching field hist step) :
    V13FieldPrefixInstantiation field hist step :=
  v13FieldPrefixInstantiation_iff_failureMatching.mpr hmatch

/-- A fixed-field prefix certificate gives an explicit failed prefix point in
the same supplied field cell for every successful prefix point. -/
theorem exists_sameCell_failure_of_fieldPrefixInstantiation_success
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (cert : V13FieldPrefixInstantiation field hist step)
    {ω : Ω} (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω) :
    ∃ ω' : Ω,
      allEvents hist ω' ∧
        field.cellOf ω' = field.cellOf ω ∧
          ¬ step.successEvent.pred ω' := by
  exact
    exists_sameCell_failure_of_fieldFailureMatching_success
      (v13FieldPrefixInstantiation_iff_failureMatching.mp cert) hhist hsucc

/-- Failure of the same-cell matching obligation blocks the fixed-field prefix
certificate. -/
theorem not_v13FieldPrefixInstantiation_of_not_failureMatching
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hfail : ¬ V13FieldFailureMatching field hist step) :
    ¬ V13FieldPrefixInstantiation field hist step := by
  intro cert
  exact hfail (v13FieldPrefixInstantiation_iff_failureMatching.mp cert)

/-- If a fixed-field prefix certificate fails, then some supplied cell has more
next-success prefix points than next-failure prefix points. -/
theorem exists_bad_cell_of_not_v13FieldPrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω}
    (hfail : ¬ V13FieldPrefixInstantiation field hist step) :
    ∃ cell : field.Cell,
      v13ConcreteFailureCount (Ω := Ω) hist step field.cellOf cell <
        v13ConcreteSuccessCount (Ω := Ω) hist step field.cellOf cell := by
  exact exists_bad_cell_of_not_v13FieldFailureMatching
    (field := field) (hist := hist) (step := step)
    (fun hmatch => hfail (v13FieldPrefixInstantiation_of_failureMatching hmatch))

/-- If one successful prefix point has no failed prefix point in its supplied
field cell, the fixed-field prefix certificate is impossible. -/
theorem not_v13FieldPrefixInstantiation_of_success_without_sameCell_failure
    {Ω : Type u} [Fintype Ω]
    {field : V13HistoryField Ω} {hist : List (FiniteEvent Ω)}
    {step : V13SwitchedStep Ω} {ω : Ω}
    (hhist : allEvents hist ω)
    (hsucc : step.successEvent.pred ω)
    (hnoFailure :
      ∀ ⦃ω' : Ω⦄,
        allEvents hist ω' →
          field.cellOf ω' = field.cellOf ω →
            step.successEvent.pred ω') :
    ¬ V13FieldPrefixInstantiation field hist step := by
  exact not_v13FieldPrefixInstantiation_of_not_failureMatching
    (not_v13FieldFailureMatching_of_success_without_sameCell_failure
      hhist hsucc hnoFailure)

end Mettapedia.Computability.PNP
