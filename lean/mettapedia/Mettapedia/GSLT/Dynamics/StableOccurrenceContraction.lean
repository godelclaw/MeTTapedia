import Mathlib.Data.List.GetD
import Mathlib.Tactic

/-!
# Stable contraction of ordered occurrence families

A mutable MeTTa space is observed as an ordered family of occurrences.  A
bulk removal therefore acts on occurrence positions, not merely on distinct
values: equal rows may be retained or removed independently, and every
retained row keeps its relative order.

This module separates that semantic contraction from its coordinate
realization.  `contract` is the independent list semantics.  `compile` emits
the same target together with a partial source-to-target coordinate map.
The coordinate theorem licenses an implementation that transports derived
indexes through the map instead of rebuilding them from the target rows.

The final cost statement is intentionally representation-relative.  For an
explicit target array, exactness fixes the number of target-row writes.  It
does not claim a lower bound for persistent, compressed, or symbolic
realizations.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dynamics.StableOccurrenceContraction

universe uRow uTarget

/-- Stable ordered contraction.  A missing mask suffix retains nothing; the
runtime admission law separately requires equal source and mask lengths. -/
def contract {Row : Type uRow} : List Bool → List Row → List Row
  | true :: mask, row :: rows => row :: contract mask rows
  | false :: mask, _ :: rows => contract mask rows
  | _, _ => []

/-- An executable contraction result.  `sourceToTarget[i] = some j` says that
source occurrence `i` survives at target occurrence `j`; `none` receipts a
removed source occurrence. -/
structure Result (Row : Type uRow) where
  rows : List Row
  sourceToTarget : List (Option Nat)
deriving DecidableEq, Repr

private def shiftCoordinate : Option Nat → Option Nat :=
  Option.map Nat.succ

/-- Compile a stable contraction and its coordinate transport in one pass. -/
def compile {Row : Type uRow} : List Bool → List Row → Result Row
  | true :: mask, row :: rows =>
      let tail := compile mask rows
      { rows := row :: tail.rows
        sourceToTarget := some 0 :: tail.sourceToTarget.map shiftCoordinate }
  | false :: mask, _ :: rows =>
      let tail := compile mask rows
      { rows := tail.rows
        sourceToTarget := none :: tail.sourceToTarget }
  | _, _ => { rows := [], sourceToTarget := [] }

/-- The coordinate compiler is independently adequate for the ordered-list
semantics. -/
theorem compile_rows_exact {Row : Type uRow}
    (mask : List Bool) (rows : List Row) :
    (compile mask rows).rows = contract mask rows := by
  induction mask generalizing rows with
  | nil => simp [compile, contract]
  | cons keep mask inductionHypothesis =>
      cases rows with
      | nil => simp [compile, contract]
      | cons row rows =>
          cases keep <;> simp [compile, contract, inductionHypothesis]

/-- Stable contraction is natural in the row payload: changing every payload
before contraction is the same as changing every retained payload afterward.
This is the commuting square used by payload-independent indexes. -/
theorem contract_map {Row : Type uRow} {Target : Type uTarget}
    (transform : Row → Target) (mask : List Bool) (rows : List Row) :
    contract mask (rows.map transform) =
      (contract mask rows).map transform := by
  induction mask generalizing rows with
  | nil => simp [contract]
  | cons keep mask inductionHypothesis =>
      cases rows with
      | nil => simp [contract]
      | cons row rows =>
          cases keep <;> simp [contract, inductionHypothesis]

/-- Every emitted source-to-target coordinate points to the same occurrence
payload in the independent source and target observations. -/
theorem sourceToTarget_sound {Row : Type uRow}
    (mask : List Bool) (rows : List Row) (sourceIndex targetIndex : Nat)
    (mapped :
      (compile mask rows).sourceToTarget[sourceIndex]? =
        some (some targetIndex)) :
    rows[sourceIndex]? = (compile mask rows).rows[targetIndex]? := by
  induction mask generalizing rows sourceIndex targetIndex with
  | nil => simp [compile] at mapped
  | cons keep mask inductionHypothesis =>
      cases rows with
      | nil => simp [compile] at mapped
      | cons row rows =>
          cases keep with
          | false =>
              cases sourceIndex with
              | zero => simp [compile] at mapped
              | succ sourceIndex =>
                  simp only [compile] at mapped ⊢
                  exact inductionHypothesis rows sourceIndex targetIndex mapped
          | true =>
              cases sourceIndex with
              | zero =>
                  simp [compile] at mapped
                  subst targetIndex
                  simp [compile]
              | succ sourceIndex =>
                  simp only [compile] at mapped
                  cases coordinate :
                      (compile mask rows).sourceToTarget[sourceIndex]? with
                  | none => simp [coordinate] at mapped
                  | some coordinateValue =>
                      cases coordinateValue with
                      | none => simp [coordinate, shiftCoordinate] at mapped
                      | some tailTargetIndex =>
                          simp [coordinate, shiftCoordinate] at mapped
                          subst targetIndex
                          simp only [compile]
                          exact inductionHypothesis rows sourceIndex
                            tailTargetIndex coordinate

/-- The compiled coordinate table covers exactly the common source/mask
prefix.  Equal lengths therefore give one receipt per source occurrence. -/
theorem sourceToTarget_length {Row : Type uRow}
    (mask : List Bool) (rows : List Row) :
    (compile mask rows).sourceToTarget.length =
      min mask.length rows.length := by
  induction mask generalizing rows with
  | nil => simp [compile]
  | cons keep mask inductionHypothesis =>
      cases rows with
      | nil => simp [compile]
      | cons row rows =>
          cases keep <;>
            simp [compile, inductionHypothesis, Nat.succ_min_succ]

/-- A coordinate transport is stable exactly when removed source occurrences
may be skipped and each retained source occurrence receives the next target
coordinate.  The retained coordinates are therefore monotone, gap-free, and
begin at zero. -/
inductive IsStableCoordinateTransport : Nat → List (Option Nat) → Prop where
  | nil : IsStableCoordinateTransport 0 []
  | removed {targetLength coordinates} :
      IsStableCoordinateTransport targetLength coordinates →
      IsStableCoordinateTransport targetLength (none :: coordinates)
  | retained {targetLength coordinates} :
      IsStableCoordinateTransport targetLength coordinates →
      IsStableCoordinateTransport (Nat.succ targetLength)
        (some 0 :: coordinates.map shiftCoordinate)

/-- The complete admission certificate carried by a compiled coordinate
transport: one coordinate receipt exists for every source occurrence in the
common source/mask prefix, and the surviving receipts enumerate the target
coordinates stably. -/
structure TransportCertificate
    (sourceLength targetLength : Nat)
    (coordinates : List (Option Nat)) : Prop where
  coversSource : coordinates.length = sourceLength
  stable : IsStableCoordinateTransport targetLength coordinates

/-- The one-pass compiler emits a stable, gap-free coordinate transport. -/
theorem compile_sourceToTarget_stable {Row : Type uRow}
    (mask : List Bool) (rows : List Row) :
    IsStableCoordinateTransport
      (compile mask rows).rows.length
      (compile mask rows).sourceToTarget := by
  induction mask generalizing rows with
  | nil => exact IsStableCoordinateTransport.nil
  | cons keep mask inductionHypothesis =>
      cases rows with
      | nil => simpa [compile] using IsStableCoordinateTransport.nil
      | cons row rows =>
          cases keep with
          | false =>
              exact IsStableCoordinateTransport.removed
                (inductionHypothesis rows)
          | true =>
              exact IsStableCoordinateTransport.retained
                (inductionHypothesis rows)

/-- Equal source/mask lengths specialize the compiler to a certificate over
the whole source family; unequal inputs still receive an honest certificate
for their common prefix. -/
theorem compile_transport_certificate {Row : Type uRow}
    (mask : List Bool) (rows : List Row) :
    TransportCertificate
      (min mask.length rows.length)
      (compile mask rows).rows.length
      (compile mask rows).sourceToTarget where
  coversSource := sourceToTarget_length mask rows
  stable := compile_sourceToTarget_stable mask rows

/-- Removing only rows outside a projection preserves its complete ordered
observation, including duplicate values. This supplies the semantic premise
for retaining an equation index across data-only contraction; the coordinate
compiler separately supplies each surviving row's new address. -/
theorem contract_filterMap_of_retained {Row : Type uRow} {Value : Type uTarget}
    (project : Row → Option Value) (mask : List Bool) (rows : List Row)
    (lengths : mask.length = rows.length)
    (retained : ∀ (index : Nat) row, rows[index]? = some row →
      project row ≠ none → mask[index]? = some true) :
    (contract mask rows).filterMap project = rows.filterMap project := by
  induction mask generalizing rows with
  | nil =>
      cases rows with
      | nil => rfl
      | cons row rows => simp at lengths
  | cons keep mask ih =>
      cases rows with
      | nil => simp at lengths
      | cons row rows =>
          have tailLengths : mask.length = rows.length := by simpa using lengths
          have tailRetained : ∀ (index : Nat) value, rows[index]? = some value →
              project value ≠ none → mask[index]? = some true := by
            intro index value found visible
            simpa using retained (index + 1) value (by simpa using found) visible
          have tail := ih rows tailLengths tailRetained
          cases keep with
          | false =>
              have erased : project row = none := by
                by_contra visible
                have impossible := retained 0 row (by simp) visible
                simp at impossible
              simp [contract, erased, tail]
          | true =>
              cases projected : project row <;> simp [contract, projected, tail]

example : ((contract [false, true, false, true] [1, 7, 2, 7]).filterMap
    (fun n : Nat => if n == 7 then some n else none)) = [7, 7] := by decide

/-- Dropping a projected occurrence changes its observation even when an
equal projected value survives elsewhere. -/
example : ((contract [false, false, false, true] [1, 7, 2, 7]).filterMap
    (fun n : Nat => if n == 7 then some n else none)) ≠ [7, 7] := by decide

/-! ## Single-occurrence erasure and projection retention -/

/-- Removing a row outside a projection preserves its exact ordered observation,
including repeated values. The lookup premise also covers an out-of-range erase. -/
theorem eraseIdx_filterMap_of_unobserved {Row : Type uRow} {Value : Type uTarget}
    (project : Row → Option Value) (rows : List Row) (removed : Nat)
    (unobserved : (rows[removed]?).bind project = none) :
    (rows.eraseIdx removed).filterMap project = rows.filterMap project := by
  induction rows generalizing removed with
  | nil => simp
  | cons row rows ih =>
      cases removed with
      | zero =>
          have omitted : project row = none := by simpa using unobserved
          simp [omitted]
      | succ removed =>
          simp only [List.getElem?_cons_succ] at unobserved
          simp [List.eraseIdx_cons_succ, List.filterMap_cons, ih removed unobserved]

/-- The dense coordinate adjustment for an ordered erasure preserves the row at
every surviving source coordinate, independently of the row's payload. -/
theorem eraseIdx_coordinate_preserved {Row : Type uRow}
    (rows : List Row) (removed source : Nat) (survives : source ≠ removed) :
    (rows.eraseIdx removed)[source - (if removed < source then 1 else 0)]? =
      rows[source]? := by
  by_cases later : removed < source
  · simp only [later, ↓reduceIte]
    rw [List.getElem?_eraseIdx_of_ge (by omega)]
    congr 1
    omega
  · simp only [later, ↓reduceIte, Nat.sub_zero]
    exact List.getElem?_eraseIdx_of_lt (by omega)

/-- Unordered erasure fills the removed slot with the last row. Both rows must
be outside the projection: ignoring only the removed row would allow a visible
tail to cross other visible rows. -/
theorem swap_erase_filterMap_of_unobserved {Row : Type uRow} {Value : Type uTarget}
    (project : Row → Option Value) (before middle : List Row) (removed tail : Row)
    (removed_unobserved : project removed = none)
    (tail_unobserved : project tail = none) :
    (before ++ tail :: middle).filterMap project =
      (before ++ removed :: (middle ++ [tail])).filterMap project := by
  simp [removed_unobserved, tail_unobserved]

/-- Repeated visible rows survive an ordered deletion independently. -/
example : (([7, 0, 7, 9] : List Nat).eraseIdx 1).filterMap
    (fun n => if n == 0 then none else some n) = [7, 7, 9] := by decide

/-- Moving an unobserved tail does not disturb the intervening observation. -/
example : (([0, 7, 7] : List Nat).filterMap
    (fun n => if n == 0 then none else some n)) = [7, 7] := by decide

/-- A visible tail cannot be moved across a different visible occurrence while
claiming that the ordered projection is unchanged. -/
example : (([9, 7] : List Nat).filterMap
    (fun n => if n == 0 then none else some n)) ≠
    ([0, 7, 9].filterMap (fun n => if n == 0 then none else some n)) := by decide

/-! ## Retaining a projection and its negative exclusion certificate -/

/-- An index observes its selected rows and whether a row can defeat negative
exclusion. For declaration indexes the latter includes open outer patterns. -/
def guardedProjection {Row : Type uRow} {Value : Type uTarget}
    (project : Row → Option Value) (openRow : Row → Bool) (rows : List Row) :
    List Value × Bool := (rows.filterMap project, rows.any openRow)

/-- A deletion cannot introduce a row defeating an absence certificate. -/
theorem contract_any_eq_false {Row : Type uRow}
    (openRow : Row → Bool) (mask : List Bool) (rows : List Row)
    (closed : rows.any openRow = false) :
    (contract mask rows).any openRow = false := by
  induction mask generalizing rows with
  | nil => simp [contract]
  | cons keep mask ih =>
      cases rows with
      | nil => simp [contract]
      | cons row rows =>
          have parts : openRow row = false ∧ rows.any openRow = false := by
            simpa only [List.any_cons, Bool.or_eq_false_iff] using closed
          cases keep <;> simp [contract, parts.1, ih rows parts.2]

/-- A stable contraction preserving the selected rows can reuse the complete
guarded observation when its negative certificate was clear. -/
theorem contract_guardedProjection_of_retained {Row : Type uRow} {Value : Type uTarget}
    (project : Row → Option Value) (openRow : Row → Bool)
    (mask : List Bool) (rows : List Row) (lengths : mask.length = rows.length)
    (retained : ∀ (index : Nat) row, rows[index]? = some row →
      project row ≠ none → mask[index]? = some true)
    (closed : rows.any openRow = false) :
    guardedProjection project openRow (contract mask rows) =
      guardedProjection project openRow rows := by
  exact Prod.ext (contract_filterMap_of_retained project mask rows lengths retained)
    ((contract_any_eq_false openRow mask rows closed).trans closed.symm)

/-- The same certificate applies to a single ordered erasure. -/
theorem eraseIdx_guardedProjection_of_unobserved {Row : Type uRow} {Value : Type uTarget}
    (project : Row → Option Value) (openRow : Row → Bool) (rows : List Row) (removed : Nat)
    (unobserved : (rows[removed]?).bind project = none)
    (closed : rows.any openRow = false) :
    guardedProjection project openRow (rows.eraseIdx removed) =
      guardedProjection project openRow rows := by
  have clear : (rows.eraseIdx removed).any openRow = false := by
    apply List.any_eq_false.mpr
    intro row included
    exact List.any_eq_false.mp closed row (List.mem_of_mem_eraseIdx included)
  exact Prod.ext (eraseIdx_filterMap_of_unobserved project rows removed unobserved)
    (clear.trans closed.symm)

/-- Swapping the unobserved tail into an unobserved slot also preserves a
negative certificate, since it merely relocates a surviving row. -/
theorem swap_erase_guardedProjection_of_unobserved {Row : Type uRow} {Value : Type uTarget}
    (project : Row → Option Value) (openRow : Row → Bool)
    (before middle : List Row) (removed tail : Row)
    (removed_unobserved : project removed = none)
    (tail_unobserved : project tail = none)
    (closed : (before ++ removed :: (middle ++ [tail])).any openRow = false) :
    guardedProjection project openRow (before ++ tail :: middle) =
      guardedProjection project openRow (before ++ removed :: (middle ++ [tail])) := by
  have clear : (before ++ tail :: middle).any openRow = false := by
    simp only [List.any_append, List.any_cons, List.any_nil, Bool.or_false,
      Bool.or_eq_false_iff] at closed ⊢
    exact ⟨closed.1, closed.2.2.2, closed.2.2.1⟩
  exact Prod.ext
    (swap_erase_filterMap_of_unobserved project before middle removed tail
      removed_unobserved tail_unobserved) (clear.trans closed.symm)

example : guardedProjection (fun n : Nat => if n == 7 then some n else none)
    (fun n => n == 0) (contract [true, false, true] [7, 2, 7]) = ([7, 7], false) := by
  decide

/-- An unchanged selected list is insufficient when deleting the last open row
changes its accompanying exclusion metadata. -/
example : guardedProjection (fun n : Nat => if n == 7 then some n else none)
    (fun n => n == 0) (contract [false, true] [0, 7]) ≠
    guardedProjection (fun n : Nat => if n == 7 then some n else none)
      (fun n => n == 0) [0, 7] := by decide

/-- Contraction never increases the number of observed occurrences. -/
theorem contract_length_le {Row : Type uRow}
    (mask : List Bool) (rows : List Row) :
    (contract mask rows).length ≤ rows.length := by
  induction mask generalizing rows with
  | nil => simp [contract]
  | cons keep mask inductionHypothesis =>
      cases rows with
      | nil => simp [contract]
      | cons row rows =>
          cases keep with
          | false =>
              exact Nat.le.step (inductionHypothesis rows)
          | true =>
              simpa [contract] using
                Nat.succ_le_succ (inductionHypothesis rows)

/-- One explicit-array realization of the contraction semantics. -/
structure ExplicitRealization (Row : Type uRow)
    (mask : List Bool) (source : List Row) where
  target : List Row
  exact : target = contract mask source

/-- Representation-relative lower bound: every exact explicit target stores
exactly one cell per retained occurrence.  Symbolic and persistent carriers
are deliberately outside this statement. -/
theorem explicit_target_cells_exact {Row : Type uRow}
    (mask : List Bool) (source : List Row)
    (realization : ExplicitRealization Row mask source) :
    realization.target.length = (contract mask source).length := by
  rw [realization.exact]

/-! ## Independent positive and negative controls -/

/-- Equal payloads remain distinct occurrences when only one is removed. -/
example :
    contract [true, false, true] ["same", "same", "tail"] =
      ["same", "tail"] := by
  decide

/-- Stable contraction cannot reverse the retained occurrences. -/
example :
    contract [true, false, true] ["left", "middle", "right"] ≠
      ["right", "left"] := by
  decide

/-- The coordinate map distinguishes equal occurrences by position. -/
example :
    (compile [false, true, true] ["same", "same", "tail"]).sourceToTarget =
      [none, some 0, some 1] := by
  decide

/-- The compiled example carries the stronger monotone, gap-free transport
certificate, not merely the expected concrete coordinate bytes. -/
example :
    IsStableCoordinateTransport 2 [none, some 0, some 1] := by
  exact IsStableCoordinateTransport.removed
    (IsStableCoordinateTransport.retained
      (IsStableCoordinateTransport.retained
        IsStableCoordinateTransport.nil))

/-- Reversing two retained coordinates is not a stable transport. -/
example :
    ¬ IsStableCoordinateTransport 2 [some 1, some 0] := by
  intro transport
  cases transport

/-! ## Batched contraction

A removal may mark its occurrence and leave the contraction for later.  The
marks of several removals then contract the family in one pass.  `refine`
composes two masks: it keeps a source occurrence when the first mask keeps it
and the second keeps its retained image.  One pass over the composed mask is
the two contractions in turn, for the rows and for the coordinate map that
carries derived indexes. -/

/-- The source mask that keeps an occurrence when `outer` keeps it and
`inner` keeps its retained image.  A missing `inner` suffix retains nothing,
as in `contract`. -/
def refine : List Bool → List Bool → List Bool
  | true :: outer, keep :: inner => keep :: refine outer inner
  | true :: outer, [] => false :: refine outer []
  | false :: outer, inner => false :: refine outer inner
  | [], _ => []

theorem contract_nil_rows {Row : Type uRow} (mask : List Bool) :
    contract mask ([] : List Row) = [] := by
  cases mask with
  | nil => rfl
  | cons keep mask => cases keep <;> rfl

/-- One pass over the composed marks is the two contractions in turn. -/
theorem contract_refine {Row : Type uRow}
    (outer inner : List Bool) (rows : List Row) :
    contract inner (contract outer rows) =
      contract (refine outer inner) rows := by
  induction outer generalizing inner rows with
  | nil => simp [contract, refine, contract_nil_rows]
  | cons keepOuter outer ih =>
      cases rows with
      | nil => simp [contract_nil_rows]
      | cons row rows =>
          cases keepOuter with
          | false => simpa [contract, refine] using ih inner rows
          | true =>
              cases inner with
              | nil =>
                  simpa [contract, refine, contract_nil_rows] using
                    (ih [] rows).symm
              | cons keepInner inner =>
                  cases keepInner <;> simp [contract, refine, ih]

/-- Coordinates through `outer`, then through `inner`. -/
def composeCoordinates (outer inner : List (Option Nat)) :
    List (Option Nat) :=
  outer.map fun coordinate =>
    coordinate.bind fun target => (inner[target]?).join

private theorem composeCoordinates_shift_retained
    (outer inner : List (Option Nat)) :
    composeCoordinates (outer.map shiftCoordinate)
        (some 0 :: inner.map shiftCoordinate) =
      (composeCoordinates outer inner).map shiftCoordinate := by
  simp only [composeCoordinates, List.map_map]
  congr 1
  funext coordinate
  cases coordinate with
  | none => rfl
  | some target =>
      cases found : inner[target]? with
      | none => simp [shiftCoordinate, found]
      | some value => cases value <;> simp [shiftCoordinate, found]

private theorem composeCoordinates_shift_removed
    (outer inner : List (Option Nat)) :
    composeCoordinates (outer.map shiftCoordinate) (none :: inner) =
      composeCoordinates outer inner := by
  simp only [composeCoordinates, List.map_map]
  congr 1
  funext coordinate
  cases coordinate <;> simp [shiftCoordinate]

/-- The coordinate map of one pass over the composed marks is the composition
of the two maps, so derived indexes may be carried once per batch. -/
theorem compile_refine_sourceToTarget {Row : Type uRow}
    (outer inner : List Bool) (rows : List Row) :
    (compile (refine outer inner) rows).sourceToTarget =
      composeCoordinates (compile outer rows).sourceToTarget
        (compile inner (contract outer rows)).sourceToTarget := by
  induction outer generalizing inner rows with
  | nil =>
      cases rows <;> simp [compile, refine, composeCoordinates]
  | cons keepOuter outer ih =>
      cases rows with
      | nil =>
          cases keepOuter <;> cases inner <;>
            simp [compile, refine, composeCoordinates]
      | cons row rows =>
          cases keepOuter with
          | false =>
              simp only [refine, compile, contract]
              rw [ih inner rows]
              simp [composeCoordinates]
          | true =>
              cases inner with
              | nil =>
                  simp only [refine, compile]
                  rw [ih [] rows]
                  simp [composeCoordinates, compile, shiftCoordinate,
                    Function.comp_def, List.map_const']
              | cons keepInner inner =>
                  cases keepInner with
                  | false =>
                      simp only [refine, compile, contract]
                      rw [ih inner rows]
                      have tail := composeCoordinates_shift_removed
                        (compile outer rows).sourceToTarget
                        (compile inner (contract outer rows)).sourceToTarget
                      simp only [composeCoordinates, List.map_cons,
                        Option.bind_some, List.getElem?_cons_zero,
                        Option.join_some] at tail ⊢
                      rw [tail]
                  | true =>
                      simp only [refine, compile, contract]
                      rw [ih inner rows]
                      have tail := composeCoordinates_shift_retained
                        (compile outer rows).sourceToTarget
                        (compile inner (contract outer rows)).sourceToTarget
                      simp only [composeCoordinates, List.map_cons,
                        Option.bind_some, List.getElem?_cons_zero,
                        Option.join_some] at tail ⊢
                      rw [tail]

/-- With equal lengths, a mask retains one occurrence per kept position. -/
theorem contract_length_count {Row : Type uRow}
    (mask : List Bool) (rows : List Row) (lengths : mask.length = rows.length) :
    (contract mask rows).length = mask.count true := by
  induction mask generalizing rows with
  | nil => simp [contract]
  | cons keep mask ih =>
      cases rows with
      | nil => simp at lengths
      | cons row rows =>
          have tail : mask.length = rows.length := by simpa using lengths
          cases keep <;> simp [contract, ih rows tail]

private theorem contract_replicate_true {Row : Type uRow} (rows : List Row) :
    contract (List.replicate rows.length true) rows = rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih => simp [List.replicate_succ, contract, ih]

private theorem contract_replicate_set_false {Row : Type uRow}
    (rows : List Row) (visible : Nat) :
    contract ((List.replicate rows.length true).set visible false) rows =
      rows.eraseIdx visible := by
  induction rows generalizing visible with
  | nil => simp [contract]
  | cons row rows ih =>
      cases visible with
      | zero =>
          simp [List.replicate_succ, contract, contract_replicate_true]
      | succ visible =>
          simp [List.replicate_succ, contract, ih visible]

/-- Marks over the source rows: the occurrence at visible position `visible`
is marked as well. -/
def markVisible (alive : List Bool) (visible : Nat) : List Bool :=
  refine alive ((List.replicate (alive.count true) true).set visible false)

/-- Marking a visible occurrence removes exactly it from the observation: a
marked removal is the ordered erasure, with the contraction left for later. -/
theorem contract_markVisible {Row : Type uRow}
    (alive : List Bool) (rows : List Row) (visible : Nat)
    (lengths : alive.length = rows.length) :
    contract (markVisible alive visible) rows =
      (contract alive rows).eraseIdx visible := by
  rw [markVisible, ← contract_refine, ← contract_length_count alive rows lengths]
  exact contract_replicate_set_false (contract alive rows) visible

/-! ### Scanning work of a threshold policy

A store counts its live occurrences and the marked ones that still await a
pass.  A pass reads every row, live or marked.  The threshold policy runs a
pass when a removal leaves at least as many marked rows as live ones; then
each pass reads at most twice the marks it clears, and the reading over any
run is bounded by twice its removals. -/

/-- Live occurrences and marked ones awaiting the next pass. -/
structure Marks where
  live : Nat
  marked : Nat
deriving DecidableEq, Repr

/-- A change to a store: an appended occurrence or a removed one. -/
inductive Change where
  | append
  | remove
deriving DecidableEq, Repr

/-- One change under the threshold policy, with the rows a pass reads. -/
def thresholdStep (marks : Marks) : Change → Marks × Nat
  | .append => ({ marks with live := marks.live + 1 }, 0)
  | .remove =>
      let live := marks.live - 1
      let marked := marks.marked + 1
      if live ≤ marked then ({ live := live, marked := 0 }, live + marked)
      else ({ live := live, marked := marked }, 0)

/-- One change under the eager policy: every removal runs a pass. -/
def eagerStep (marks : Marks) : Change → Marks × Nat
  | .append => ({ marks with live := marks.live + 1 }, 0)
  | .remove => ({ live := marks.live - 1, marked := 0 }, marks.live + marks.marked)

/-- The rows read by every pass of a run. -/
def scanned (step : Marks → Change → Marks × Nat) :
    Marks → List Change → Nat
  | _, [] => 0
  | marks, change :: changes =>
      (step marks change).2 + scanned step (step marks change).1 changes

def removals (changes : List Change) : Nat :=
  changes.count .remove

theorem removals_cons_append (changes : List Change) :
    removals (.append :: changes) = removals changes := by
  simp [removals]

theorem removals_cons_remove (changes : List Change) :
    removals (.remove :: changes) = removals changes + 1 := by
  simp [removals]

/-- Under the threshold policy a run reads at most twice the marks it starts
with plus twice its removals, whatever the store's size. -/
theorem scanned_threshold_le (marks : Marks) (changes : List Change) :
    scanned thresholdStep marks changes ≤
      2 * (marks.marked + removals changes) := by
  induction changes generalizing marks with
  | nil => simp [scanned]
  | cons change changes ih =>
      cases change with
      | append =>
          have tail : scanned thresholdStep ⟨marks.live + 1, marks.marked⟩ changes ≤
              2 * (marks.marked + removals changes) :=
            ih ⟨marks.live + 1, marks.marked⟩
          have step : thresholdStep marks .append =
              (⟨marks.live + 1, marks.marked⟩, 0) := rfl
          rw [scanned, removals_cons_append, step]
          dsimp only
          omega
      | remove =>
          rw [scanned, removals_cons_remove]
          by_cases pass : marks.live - 1 ≤ marks.marked + 1
          · have tail : scanned thresholdStep ⟨marks.live - 1, 0⟩ changes ≤
                2 * (0 + removals changes) := ih ⟨marks.live - 1, 0⟩
            have step : thresholdStep marks .remove =
                (⟨marks.live - 1, 0⟩, marks.live - 1 + (marks.marked + 1)) := by
              simp [thresholdStep, pass]
            rw [step]
            dsimp only
            omega
          · have tail : scanned thresholdStep
                ⟨marks.live - 1, marks.marked + 1⟩ changes ≤
                2 * (marks.marked + 1 + removals changes) :=
              ih ⟨marks.live - 1, marks.marked + 1⟩
            have step : thresholdStep marks .remove =
                (⟨marks.live - 1, marks.marked + 1⟩, 0) := by
              simp [thresholdStep, pass]
            rw [step]
            dsimp only
            omega

/-- Removing every occurrence of eight: the threshold policy reads 15 rows,
within twice the eight removals. -/
example : scanned thresholdStep ⟨8, 0⟩ (List.replicate 8 .remove) = 15 := by
  decide

/-- The eager policy reads the whole store on each removal: 36 rows for the
same run, more than twice its removals, and quadratic in the store's size. -/
example : scanned eagerStep ⟨8, 0⟩ (List.replicate 8 .remove) = 36 := by
  decide

example : ¬ scanned eagerStep ⟨8, 0⟩ (List.replicate 8 .remove) ≤
    2 * (0 + removals (List.replicate 8 .remove)) := by
  decide

/-- Marks of two removals, contracted in one pass, match two passes. -/
example :
    contract (refine [true, false, true, true] [true, false, true])
        ["a", "b", "c", "d"] =
      contract [true, false, true] (contract [true, false, true, true]
        ["a", "b", "c", "d"]) := by
  decide

/-- The composed coordinates send each survivor to its final position. -/
example :
    (compile (refine [true, false, true, true] [true, false, true])
        ["a", "b", "c", "d"]).sourceToTarget =
      [some 0, none, none, some 1] := by
  decide

/-- A later mark cannot revive an occurrence an earlier mark removed. -/
example :
    contract (refine [true, false, true] [true, true])
        ["a", "b", "c"] ≠ ["a", "b", "c"] := by
  decide

/-- Marking the second visible occurrence erases it, not a later equal one. -/
example :
    contract (markVisible [true, false, true, true] 1)
        ["same", "gone", "same", "tail"] =
      ["same", "tail"] := by
  decide

#print axioms contract_refine
#print axioms compile_refine_sourceToTarget
#print axioms contract_length_count
#print axioms contract_markVisible
#print axioms scanned_threshold_le

#print axioms compile_rows_exact
#print axioms contract_map
#print axioms sourceToTarget_sound
#print axioms sourceToTarget_length
#print axioms compile_sourceToTarget_stable
#print axioms compile_transport_certificate
#print axioms contract_length_le
#print axioms explicit_target_cells_exact
#print axioms eraseIdx_filterMap_of_unobserved
#print axioms eraseIdx_coordinate_preserved
#print axioms swap_erase_filterMap_of_unobserved
#print axioms contract_any_eq_false
#print axioms contract_guardedProjection_of_retained
#print axioms eraseIdx_guardedProjection_of_unobserved
#print axioms swap_erase_guardedProjection_of_unobserved

end Mettapedia.GSLT.Dynamics.StableOccurrenceContraction
