import Mettapedia.Computability.PNP.PNPv13SwitchingInstantiationCore

/-!
# PNP v13 switching concrete cell instantiation

Concrete finite cell partitions and semantic prefix-instantiation certificates.
-/

namespace Mettapedia.Computability.PNP

open scoped BigOperators

universe u

/-- Partition a finite event by an arbitrary finite cell map.  This is the
generic counting fact behind the concrete v13 atom ledger: once a finite
`cellOf` map is supplied, the decomposition equations are ordinary finite
partition identities. -/
def finiteEventCellPartitionEquiv {Ω Cell : Type u} {E : Ω → Prop}
    (cellOf : Ω → Cell) :
    {ω : Ω // E ω} ≃
      Sigma (fun cell : Cell => {ω : Ω // E ω ∧ cellOf ω = cell}) where
  toFun := fun ω => ⟨cellOf ω.1, ⟨ω.1, ω.2, rfl⟩⟩
  invFun := fun cellω => ⟨cellω.2.1, cellω.2.2.1⟩
  left_inv := by
    intro ω
    rfl
  right_inv := by
    rintro ⟨cell, ω, hE, hcell⟩
    cases hcell
    rfl

/-- Finite event counts split as the sum of their finite cell fibers. -/
theorem finiteEventCount_cell_partition {Ω Cell : Type u}
    [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    {E : Ω → Prop} [DecidablePred E] (cellOf : Ω → Cell) :
    finiteEventCount Ω E =
      Finset.univ.sum (fun cell =>
        finiteEventCount Ω (fun ω => E ω ∧ cellOf ω = cell)) := by
  change Fintype.card {ω : Ω // E ω} =
    Finset.univ.sum (fun cell : Cell =>
      Fintype.card {ω : Ω // E ω ∧ cellOf ω = cell})
  rw [Fintype.card_congr (finiteEventCellPartitionEquiv cellOf)]
  rw [Fintype.card_sigma]

/-- The count of a concrete history atom selected by a cell map. -/
def v13ConcretePrefixCount {Ω Cell : Type u} [Fintype Ω]
    [DecidableEq Cell] (hist : List (FiniteEvent Ω))
    (cellOf : Ω → Cell) (cell : Cell) : Nat :=
  finiteEventCount Ω (fun ω => allEvents hist ω ∧ cellOf ω = cell)

/-- The count of points in a concrete history atom that also satisfy the next
exact-success event. -/
def v13ConcreteSuccessCount {Ω Cell : Type u} [Fintype Ω]
    [DecidableEq Cell] (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) (cellOf : Ω → Cell) (cell : Cell) : Nat :=
  finiteEventCount Ω
    (fun ω => allEvents hist ω ∧ cellOf ω = cell ∧ step.successEvent.pred ω)

/-- The count of points in a concrete history atom that fail the next
exact-success event. -/
def v13ConcreteFailureCount {Ω Cell : Type u} [Fintype Ω]
    [DecidableEq Cell] (hist : List (FiniteEvent Ω))
    (step : V13SwitchedStep Ω) (cellOf : Ω → Cell) (cell : Cell) : Nat :=
  finiteEventCount Ω
    (fun ω => allEvents hist ω ∧ cellOf ω = cell ∧ ¬ step.successEvent.pred ω)

/-- A concrete history atom splits exactly into its next-success and
next-failure parts. -/
theorem v13ConcretePrefixCount_eq_success_add_failure {Ω Cell : Type u}
    [Fintype Ω] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (cellOf : Ω → Cell) (cell : Cell) :
    v13ConcretePrefixCount (Ω := Ω) hist cellOf cell =
      v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell +
        v13ConcreteFailureCount (Ω := Ω) hist step cellOf cell := by
  have hsplit := finiteEventCount_split (Ω := Ω)
    (E := fun ω => allEvents hist ω ∧ cellOf ω = cell)
    (F := step.successEvent.pred)
  rw [v13ConcretePrefixCount, v13ConcreteSuccessCount,
    v13ConcreteFailureCount]
  rw [hsplit]
  congr 1
  · exact finiteEventCount_congr (Ω := Ω)
      (E := fun ω =>
        (allEvents hist ω ∧ cellOf ω = cell) ∧ step.successEvent.pred ω)
      (F := fun ω =>
        allEvents hist ω ∧ cellOf ω = cell ∧ step.successEvent.pred ω)
      (by
        intro ω
        constructor
        · intro h
          exact ⟨h.1.1, h.1.2, h.2⟩
        · intro h
          exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩)
  · exact finiteEventCount_congr (Ω := Ω)
      (E := fun ω =>
        (allEvents hist ω ∧ cellOf ω = cell) ∧ ¬ step.successEvent.pred ω)
      (F := fun ω =>
        allEvents hist ω ∧ cellOf ω = cell ∧ ¬ step.successEvent.pred ω)
      (by
        intro ω
        constructor
        · intro h
          exact ⟨h.1.1, h.1.2, h.2⟩
        · intro h
          exact ⟨⟨h.1, h.2.1⟩, h.2.2⟩)

/-- The fixed-cell half-success inequality is exactly a success-versus-failure
balance condition inside that cell. -/
theorem v13ConcreteCellHalf_iff_success_le_failure {Ω Cell : Type u}
    [Fintype Ω] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (cellOf : Ω → Cell) (cell : Cell) :
    (2 * v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist cellOf cell) ↔
      v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
        v13ConcreteFailureCount (Ω := Ω) hist step cellOf cell := by
  have hsplit := v13ConcretePrefixCount_eq_success_add_failure
    (Ω := Ω) hist step cellOf cell
  constructor
  · intro h
    omega
  · intro h
    omega

/-- Any finite cell map automatically decomposes the current v13 success
prefix into its concrete cell fibers. -/
theorem v13ConcretePrefixCount_decomp {Ω Cell : Type u}
    [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (cellOf : Ω → Cell) :
    finiteHistoryCount Ω hist =
      Finset.univ.sum (v13ConcretePrefixCount (Ω := Ω) hist cellOf) := by
  simpa [finiteHistoryCount, v13ConcretePrefixCount] using
    finiteEventCount_cell_partition (Ω := Ω) (Cell := Cell)
      (E := allEvents hist) cellOf

/-- Any finite cell map automatically decomposes the next-success prefix into
its concrete cell fibers. -/
theorem v13ConcreteSuccessCount_decomp {Ω Cell : Type u}
    [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω)
    (cellOf : Ω → Cell) :
    finiteHistoryCount Ω (hist ++ [step.successEvent]) =
      Finset.univ.sum (v13ConcreteSuccessCount (Ω := Ω) hist step cellOf) := by
  have hpartition :
      finiteEventCount Ω (fun ω => allEvents hist ω ∧ step.successEvent.pred ω) =
        Finset.univ.sum (fun cell =>
          finiteEventCount Ω
            (fun ω =>
              (allEvents hist ω ∧ step.successEvent.pred ω) ∧
                cellOf ω = cell)) :=
    finiteEventCount_cell_partition (Ω := Ω) (Cell := Cell)
      (E := fun ω => allEvents hist ω ∧ step.successEvent.pred ω) cellOf
  have hsum :
      Finset.univ.sum (fun cell =>
          finiteEventCount Ω
            (fun ω =>
              (allEvents hist ω ∧ step.successEvent.pred ω) ∧
                cellOf ω = cell)) =
        Finset.univ.sum (v13ConcreteSuccessCount (Ω := Ω) hist step cellOf) := by
    apply Finset.sum_congr rfl
    intro cell hcell
    exact finiteEventCount_congr (Ω := Ω)
      (E := fun ω =>
        (allEvents hist ω ∧ step.successEvent.pred ω) ∧ cellOf ω = cell)
      (F := fun ω =>
        allEvents hist ω ∧ cellOf ω = cell ∧ step.successEvent.pred ω)
      (by
        intro ω
        constructor
        · intro h
          exact ⟨h.1.1, h.2, h.1.2⟩
        · intro h
          exact ⟨⟨h.1, h.2.2⟩, h.2.1⟩)
  rw [finiteHistoryCount_append_singleton (Ω := Ω) hist step.successEvent,
    hpartition, hsum]

/-- A semantic v13 prefix certificate.  Unlike `V13PrefixInstantiation`, this
contains an actual finite cell map on sample points.  The decomposition fields
are retained in the record for auditability, but the lemmas above show that
they are automatic for every finite `cellOf` map; the nontrivial burden is the
cellwise half-success inequality. -/
structure V13ConcretePrefixInstantiation {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) where
  Cell : Type u
  [fintypeCell : Fintype Cell]
  [decidableEqCell : DecidableEq Cell]
  cellOf : Ω → Cell
  prefix_decomp :
    finiteHistoryCount Ω hist =
      Finset.univ.sum (v13ConcretePrefixCount (Ω := Ω) hist cellOf)
  success_decomp :
    finiteHistoryCount Ω (hist ++ [step.successEvent]) =
      Finset.univ.sum (v13ConcreteSuccessCount (Ω := Ω) hist step cellOf)
  cell_half : ∀ cell,
    2 * v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
      v13ConcretePrefixCount (Ω := Ω) hist cellOf cell

attribute [instance] V13ConcretePrefixInstantiation.fintypeCell
attribute [instance] V13ConcretePrefixInstantiation.decidableEqCell

/-- Build a semantic concrete-cell certificate from a finite cell map plus the
cellwise half-success inequalities.  The decomposition fields are supplied by
finite partition identities. -/
def v13ConcretePrefixInstantiation_of_cellHalf
    {Ω Cell : Type u} [Fintype Ω] [Fintype Cell] [DecidableEq Cell]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cellOf : Ω → Cell)
    (hhalf : ∀ cell,
      2 * v13ConcreteSuccessCount (Ω := Ω) hist step cellOf cell ≤
        v13ConcretePrefixCount (Ω := Ω) hist cellOf cell) :
    V13ConcretePrefixInstantiation hist step where
  Cell := Cell
  cellOf := cellOf
  prefix_decomp := v13ConcretePrefixCount_decomp hist cellOf
  success_decomp := v13ConcreteSuccessCount_decomp hist step cellOf
  cell_half := hhalf

/-- A concrete cell-map certificate induces the abstract summary ledger. -/
def v13PrefixInstantiation_of_concretePrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13ConcretePrefixInstantiation hist step) :
    V13PrefixInstantiation hist step := by
  letI : Fintype cert.Cell := cert.fintypeCell
  letI : DecidableEq cert.Cell := cert.decidableEqCell
  exact
    { Cell := cert.Cell
      prefixCount := v13ConcretePrefixCount (Ω := Ω) hist cert.cellOf
      successCount := v13ConcreteSuccessCount (Ω := Ω) hist step cert.cellOf
      prefix_decomp := cert.prefix_decomp
      success_decomp := cert.success_decomp
      cell_half := cert.cell_half }

/-- A concrete cell-map certificate is sufficient for the generic prefix
half-step. -/
theorem prefixHalfStep_of_v13ConcretePrefixInstantiation
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (cert : V13ConcretePrefixInstantiation hist step) :
    PrefixHalfStep hist step.successEvent := by
  exact prefixHalfStep_of_v13PrefixInstantiation
    (v13PrefixInstantiation_of_concretePrefixInstantiation cert)

/-- The proposition that a semantic v13 cell-map certificate has been supplied
for one prefix. -/
def V13ConcretePrefixInstantiated {Ω : Type u} [Fintype Ω]
    (hist : List (FiniteEvent Ω)) (step : V13SwitchedStep Ω) : Prop :=
  Nonempty (V13ConcretePrefixInstantiation hist step)

theorem v13PrefixInstantiated_of_v13ConcretePrefixInstantiated
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : V13ConcretePrefixInstantiated hist step) :
    V13PrefixInstantiated hist step := by
  rcases h with ⟨cert⟩
  exact ⟨v13PrefixInstantiation_of_concretePrefixInstantiation cert⟩

theorem prefixHalfStep_of_v13ConcretePrefixInstantiated
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : V13ConcretePrefixInstantiated hist step) :
    PrefixHalfStep hist step.successEvent := by
  exact prefixHalfStep_of_v13PrefixInstantiated
    (v13PrefixInstantiated_of_v13ConcretePrefixInstantiated h)

/-- Even the existential concrete-cell certificate is equivalent to the generic
prefix half-step: the constant cell map witnesses it whenever the half-step
already holds.  A non-vacuous v13 instantiation therefore has to fix the
history field externally. -/
def v13ConcretePrefixInstantiation_of_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω}
    (h : PrefixHalfStep hist step.successEvent) :
    V13ConcretePrefixInstantiation hist step := by
  let cellOf : Ω → PUnit.{u+1} := fun _ => PUnit.unit
  refine
    { Cell := PUnit.{u+1}
      cellOf := cellOf
      prefix_decomp := ?_
      success_decomp := ?_
      cell_half := ?_ }
  · have hcount :
        finiteHistoryCount Ω hist =
          finiteEventCount Ω
            (fun ω => allEvents hist ω ∧ cellOf ω = PUnit.unit) := by
      simp [finiteHistoryCount, cellOf]
    simpa [v13ConcretePrefixCount, cellOf] using hcount
  · have hcount :
        finiteHistoryCount Ω (hist ++ [step.successEvent]) =
          finiteEventCount Ω
            (fun ω =>
              allEvents hist ω ∧ cellOf ω = PUnit.unit ∧
                step.successEvent.pred ω) := by
      have hhist :
          finiteHistoryCount Ω (hist ++ [step.successEvent]) =
            finiteEventCount Ω
              (fun ω => allEvents hist ω ∧ step.successEvent.pred ω) :=
        finiteHistoryCount_append_singleton (Ω := Ω) hist step.successEvent
      have hcell :
          finiteEventCount Ω
              (fun ω => allEvents hist ω ∧ step.successEvent.pred ω) =
            finiteEventCount Ω
              (fun ω =>
                allEvents hist ω ∧ cellOf ω = PUnit.unit ∧
                  step.successEvent.pred ω) := by
        exact finiteEventCount_congr (Ω := Ω)
          (E := fun ω => allEvents hist ω ∧ step.successEvent.pred ω)
          (F := fun ω =>
            allEvents hist ω ∧ cellOf ω = PUnit.unit ∧
              step.successEvent.pred ω)
          (by intro ω; simp [cellOf])
      exact hhist.trans hcell
    simpa [v13ConcreteSuccessCount, cellOf] using hcount
  · intro cell
    cases cell
    have hprefix :
        finiteHistoryCount Ω hist =
          v13ConcretePrefixCount (Ω := Ω) hist cellOf PUnit.unit := by
      have hcount :
          finiteHistoryCount Ω hist =
            finiteEventCount Ω
              (fun ω => allEvents hist ω ∧ cellOf ω = PUnit.unit) := by
        simp [finiteHistoryCount, cellOf]
      simpa [v13ConcretePrefixCount, cellOf] using hcount
    have hsuccess :
        finiteHistoryCount Ω (hist ++ [step.successEvent]) =
          v13ConcreteSuccessCount (Ω := Ω) hist step cellOf PUnit.unit := by
      have hcount :
          finiteHistoryCount Ω (hist ++ [step.successEvent]) =
            finiteEventCount Ω
              (fun ω =>
                allEvents hist ω ∧ cellOf ω = PUnit.unit ∧
                  step.successEvent.pred ω) := by
        have hhist :
            finiteHistoryCount Ω (hist ++ [step.successEvent]) =
              finiteEventCount Ω
                (fun ω => allEvents hist ω ∧ step.successEvent.pred ω) :=
          finiteHistoryCount_append_singleton (Ω := Ω) hist step.successEvent
        have hcell :
            finiteEventCount Ω
                (fun ω => allEvents hist ω ∧ step.successEvent.pred ω) =
              finiteEventCount Ω
                (fun ω =>
                  allEvents hist ω ∧ cellOf ω = PUnit.unit ∧
                    step.successEvent.pred ω) := by
          exact finiteEventCount_congr (Ω := Ω)
            (E := fun ω => allEvents hist ω ∧ step.successEvent.pred ω)
            (F := fun ω =>
              allEvents hist ω ∧ cellOf ω = PUnit.unit ∧
                step.successEvent.pred ω)
            (by intro ω; simp [cellOf])
        exact hhist.trans hcell
      simpa [v13ConcreteSuccessCount, cellOf] using hcount
    rw [← hprefix, ← hsuccess]
    exact h

/-- The existential concrete-cell proposition is still exactly the generic
prefix half-step. -/
theorem v13ConcretePrefixInstantiated_iff_prefixHalfStep
    {Ω : Type u} [Fintype Ω]
    {hist : List (FiniteEvent Ω)} {step : V13SwitchedStep Ω} :
    V13ConcretePrefixInstantiated hist step ↔
      PrefixHalfStep hist step.successEvent := by
  constructor
  · exact prefixHalfStep_of_v13ConcretePrefixInstantiated
  · intro h
    exact ⟨v13ConcretePrefixInstantiation_of_prefixHalfStep h⟩

end Mettapedia.Computability.PNP
