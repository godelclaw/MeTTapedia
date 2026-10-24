import Mettapedia.Algorithms.Retrieval.PrefixSearch

/-!
# Blocked occurrence postings

One event may carry several outer keys while retaining one group and source
position.  Expanding those blocks gives the ordinary occurrence relation.
Selecting a key directly from the blocks is proved equal to selecting it after
expansion, including repeated keys and repeated events.  A compiled column may
sort positions; any permutation preserves the exact prefix count.

These are representation and observation laws.  They do not assert that a
particular native implementation realizes the representation.
-/

set_option autoImplicit false

namespace Mettapedia.Algorithms.Retrieval.BlockedPostings

structure Block (Outer Group Position : Type*) where
  keys : List Outer
  group : Group
  position : Position
deriving Repr, DecidableEq

variable {Outer Group Position Premise Event : Type*}

def expandBlock (block : Block Outer Group Position) :
    List (Outer × Group × Position) :=
  block.keys.map fun key => (key, block.group, block.position)

def expand (blocks : List (Block Outer Group Position)) :
    List (Outer × Group × Position) :=
  blocks.flatMap expandBlock

def selectExpanded [DecidableEq Outer] (key : Outer)
    (blocks : List (Block Outer Group Position)) : List (Group × Position) :=
  (expand blocks).filterMap fun (outer, group, position) =>
    if outer = key then some (group, position) else none

def selectDirect [DecidableEq Outer] (key : Outer)
    (blocks : List (Block Outer Group Position)) : List (Group × Position) :=
  blocks.flatMap fun block =>
    block.keys.filterMap fun outer =>
      if outer = key then some (block.group, block.position) else none

private theorem select_expandKeys [DecidableEq Outer] (key : Outer)
    (keys : List Outer) (group : Group) (position : Position) :
    ((keys.map fun outer => (outer, group, position)).filterMap
      fun (outer, observedGroup, observedPosition) =>
        if outer = key then some (observedGroup, observedPosition) else none) =
      keys.filterMap fun outer =>
        if outer = key then some (group, position) else none := by
  induction keys with
  | nil => rfl
  | cons outer rest ih =>
      simp only [List.map_cons, List.filterMap_cons]
      split <;> simp_all

private theorem select_expandBlock [DecidableEq Outer] (key : Outer)
    (block : Block Outer Group Position) :
    (expandBlock block).filterMap
        (fun (outer, observedGroup, observedPosition) =>
          if outer = key then some (observedGroup, observedPosition) else none) =
      block.keys.filterMap fun outer =>
        if outer = key then some (block.group, block.position) else none := by
  cases block with
  | mk keys group position =>
      exact select_expandKeys key keys group position

/-- Direct observation is extensionally the ordinary expanded occurrence
observation.  No key or event occurrence is deduplicated. -/
theorem selectExpanded_eq_selectDirect [DecidableEq Outer] (key : Outer)
    (blocks : List (Block Outer Group Position)) :
    selectExpanded key blocks = selectDirect key blocks := by
  induction blocks with
  | nil => rfl
  | cons block rest ih =>
      simp only [selectExpanded, selectDirect, expand] at ih
      simp only [selectExpanded, selectDirect, expand, List.flatMap_cons,
        List.filterMap_append]
      rw [select_expandBlock, ih]

def column [DecidableEq Outer] [DecidableEq Group] (key : Outer) (group : Group)
    (blocks : List (Block Outer Group Int)) : List Int :=
  (selectDirect key blocks).filterMap fun (observedGroup, position) =>
    if observedGroup = group then some position else none

def countBefore (positions : List Int) (cutoff : Int) : Nat :=
  (positions.filter fun position => position < cutoff).length

/-- Sorting or otherwise permuting a compiled column cannot change an exact
prefix count. -/
theorem countBefore_eq_of_perm (cutoff : Int) {left right : List Int}
    (sameOccurrences : left.Perm right) :
    countBefore left cutoff = countBefore right cutoff := by
  simpa [countBefore] using
    (sameOccurrences.filter (fun position => decide (position < cutoff))).length_eq

/-- A compiled column that is a permutation of the direct block observation
answers the same prefix query.  `PrefixSearch.lowerBound_eq_countBefore` may
then replace this count when the compiled column is sorted. -/
theorem compiled_count_eq_direct [DecidableEq Outer] [DecidableEq Group]
    (blocks : List (Block Outer Group Int)) (key : Outer) (group : Group)
    (cutoff : Int) (compiled : List Int)
    (refines : compiled.Perm (column key group blocks)) :
    countBefore compiled cutoff = countBefore (column key group blocks) cutoff :=
  countBefore_eq_of_perm cutoff refines

/-! ## One tagged occurrence relation in place of local ledgers -/

structure LocalLedger (Premise Event : Type*) where
  premise : Premise
  events : List Event
deriving Repr, DecidableEq

def flattenLedgers (ledgers : List (LocalLedger Premise Event)) :
    List (Premise × Event) :=
  ledgers.flatMap fun ledger =>
    ledger.events.map fun event => (ledger.premise, event)

def observeLocal [DecidableEq Premise] (premise : Premise)
    (ledgers : List (LocalLedger Premise Event)) : List Event :=
  ledgers.flatMap fun ledger =>
    if ledger.premise = premise then ledger.events else []

def observeTagged [DecidableEq Premise] (premise : Premise)
    (events : List (Premise × Event)) : List Event :=
  events.filterMap fun (observedPremise, event) =>
    if observedPremise = premise then some event else none

private theorem observe_tagged_ledger [DecidableEq Premise]
    (premise observedPremise : Premise) (events : List Event) :
    ((events.map fun event => (observedPremise, event)).filterMap
      fun (candidate, event) =>
        if candidate = premise then some event else none) =
      if observedPremise = premise then events else [] := by
  induction events with
  | nil => simp
  | cons event rest ih =>
      simp only [List.map_cons, List.filterMap_cons]
      split <;> simp_all

/-- Replacing a family of premise-owned ledgers by one premise-tagged
occurrence relation preserves order, duplicate events, and repeated ledger
segments. -/
theorem observeTagged_flattenLedgers_eq_observeLocal
    [DecidableEq Premise] (premise : Premise)
    (ledgers : List (LocalLedger Premise Event)) :
    observeTagged premise (flattenLedgers ledgers) =
      observeLocal premise ledgers := by
  induction ledgers with
  | nil => rfl
  | cons ledger rest ih =>
      simp only [observeTagged, flattenLedgers, observeLocal,
        List.flatMap_cons, List.filterMap_append]
      rw [observe_tagged_ledger]
      congr 1

/-- `none` is a disjoint observation key for the use-count view; feature
keys occupy `some feature`. Thus each event contributes exactly one use
occurrence while retaining every feature occurrence. -/
def eventBlock (features : List Outer) (group : Group)
    (position : Position) : Block (Option Outer) Group Position where
  keys := none :: features.map some
  group := group
  position := position

def eventBlocks (events : List (List Outer × Group × Position)) :
    List (Block (Option Outer) Group Position) :=
  events.map fun (features, group, position) =>
    eventBlock features group position

private theorem selectDirect_cons [DecidableEq Outer] (key : Outer)
    (block : Block Outer Group Position)
    (blocks : List (Block Outer Group Position)) :
    selectDirect key (block :: blocks) =
      (block.keys.filterMap fun outer =>
        if outer = key then some (block.group, block.position) else none) ++
      selectDirect key blocks := rfl

private theorem selectDirect_eventBlock_use [DecidableEq Outer]
    (features : List Outer) (group : Group) (position : Position) :
    ((eventBlock features group position).keys.filterMap fun key =>
      if key = none then
        some ((eventBlock features group position).group,
          (eventBlock features group position).position)
      else none) =
      [(group, position)] := by
  simp [eventBlock]

theorem selectDirect_use_eventBlocks
    [DecidableEq Outer]
    (events : List (List Outer × Group × Position)) :
    selectDirect none (eventBlocks events) =
      events.map fun (_, group, position) => (group, position) := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
      rcases event with ⟨features, group, position⟩
      change selectDirect none
          (eventBlock features group position :: eventBlocks rest) =
        (group, position) ::
          rest.map fun (_, observedGroup, observedPosition) =>
            (observedGroup, observedPosition)
      rw [selectDirect_cons, selectDirect_eventBlock_use, ih]
      rfl

example :
    selectDirect "a"
      [{ keys := ["a", "b"], group := 0, position := 4 },
       { keys := ["a"], group := 0, position := 1 },
       { keys := ["a"], group := 2, position := 3 }] =
      [(0, 4), (0, 1), (2, 3)] := by decide +kernel

/-- Repeated keys are repeated posting occurrences, not set membership. -/
example :
    selectDirect "b"
      [{ keys := ["b", "b"], group := 1, position := 2 }] =
      [(1, 2), (1, 2)] := by decide +kernel

example :
    selectDirect "absent"
      [{ keys := ["a"], group := 0, position := 1 }] = [] := by decide +kernel

/-- Deduplicating a block's key list changes the occurrence observation. -/
example :
    selectDirect "b"
      [{ keys := ["b", "b"], group := 1, position := 2 }] ≠
    selectDirect "b"
      [{ keys := ["b"], group := 1, position := 2 }] := by decide +kernel

example :
    countBefore [4, 1, 1, 5] 3 = countBefore [1, 5, 1, 4] 3 := by
  decide +kernel

example :
    observeTagged "p"
      (flattenLedgers
        [{ premise := "p", events := [2, 2] },
         { premise := "q", events := [9] },
         { premise := "p", events := [3] }]) =
      [2, 2, 3] := by decide +kernel

/-- Repeated base events remain repeated use occurrences. -/
example :
    selectDirect none
      (eventBlocks
        [(["f"], 0, 4), (["f"], 0, 4)]) =
      [(0, 4), (0, 4)] := by decide +kernel

/-- A feature key cannot collide with the disjoint use key. -/
example :
    selectDirect (some "f")
      (eventBlocks [(([] : List String), 0, 4)]) ≠
    selectDirect none
      (eventBlocks [(([] : List String), 0, 4)]) := by decide +kernel

#print axioms selectExpanded_eq_selectDirect
#print axioms countBefore_eq_of_perm
#print axioms compiled_count_eq_direct
#print axioms observeTagged_flattenLedgers_eq_observeLocal
#print axioms selectDirect_use_eventBlocks

end Mettapedia.Algorithms.Retrieval.BlockedPostings
