import Mathlib.Tactic
import Mettapedia.Sequences.OEIS.Basic
import Mettapedia.Coalgebra.GrowingPrefixTower

/-!
# The Kolakoski sequence

The binary run-length law has one solution. Its independently defined finite
generator realizes every prefix; retained cursors justify the packed program.
Discussed by Rufus Oldenburger (1939), named after William George Kolakoski;
OEIS A000002 was contributed by N. J. A. Sloane.
-/

namespace Mettapedia.Sequences.OEIS.Kolakoski

open Mettapedia.Coalgebra.CoherentPrefixTower

/-- The symbol in the zero-based run numbered `run`: one, two, one, two, ... -/
def runSymbol (run : Nat) : Nat := if run % 2 = 0 then 1 else 2

@[simp] theorem runSymbol_zero : runSymbol 0 = 1 := by decide
@[simp] theorem runSymbol_one : runSymbol 1 = 2 := by decide

theorem runSymbol_binary (run : Nat) :
    runSymbol run = 1 ∨ runSymbol run = 2 := by
  unfold runSymbol; split <;> simp_all

/-- A finite expansion into alternating runs with lengths supplied by `a`. -/
def runPrefix (a : Nat → Nat) (runs : Nat) : List Nat :=
  (List.range runs).flatMap fun run => List.replicate (a run) (runSymbol run)

/--
A sequence is a Kolakoski fixed point when it is binary and every finite
run-length expansion agrees with the corresponding prefix of the sequence.
-/
def IsRunLengthFixedPoint (a : Nat → Nat) : Prop :=
  (∀ n, a n = 1 ∨ a n = 2) ∧
  ∀ runs index (inBounds : index < (runPrefix a runs).length),
    (runPrefix a runs)[index] = a index

/-- A finite generator state whose next unread position is in bounds. -/
structure BuildState (readIndex : Nat) where
  word : List Nat
  readable : readIndex < word.length
  binary : ∀ value, value ∈ word → value = 1 ∨ value = 2

/-- Append the run described at the current readable position. -/
def BuildState.advance {readIndex : Nat}
    (state : BuildState readIndex) : BuildState (readIndex + 1) := by
  let count := state.word[readIndex]'state.readable
  have binary := state.binary count (List.getElem_mem state.readable)
  refine ⟨state.word ++ List.replicate count (runSymbol readIndex), ?_, ?_⟩
  · simp only [List.length_append, List.length_replicate]
    have bound := state.readable
    omega
  · intro v member
    rcases List.mem_append.mp member with old | added
    · exact state.binary v old
    · exact (List.eq_of_mem_replicate added) ▸ runSymbol_binary readIndex

/-- Successive finite prefixes, beginning with the first two complete runs. -/
def build : (steps : Nat) → BuildState (steps + 2)
  | 0 => ⟨[1, 2, 2], by decide, by simp⟩
  | steps + 1 => (build steps).advance

def word (steps : Nat) : List Nat := (build steps).word

theorem word_readable (steps : Nat) : steps + 2 < (word steps).length := (build steps).readable

/-- The canonical sequence read at the stage where its position becomes active. -/
def value : Nat → Nat
  | 0 => 1
  | 1 => 2
  | index + 2 => (build index).word.get ⟨index + 2, (build index).readable⟩

@[simp] theorem value_zero : value 0 = 1 := rfl

@[simp] theorem value_one : value 1 = 2 := rfl

theorem word_succ (steps : Nat) :
    word (steps + 1) = word steps ++
      List.replicate (value (steps + 2)) (runSymbol (steps + 2)) := rfl

theorem word_prefix_succ (steps : Nat) : word steps <+: word (steps + 1) :=
  List.prefix_append _ _

theorem word_prefix_of_le {first last : Nat} (order : first ≤ last) :
    word first <+: word last := prefix_of_le word word_prefix_succ order

theorem word_get_eq_value (steps index : Nat)
    (inBounds : index < (word steps).length) :
    (word steps)[index] = value index := by
  rcases index with _ | (_ | index)
  · exact lookup_eq word word_prefix_succ inBounds (by decide : 0 < (word 0).length)
  · exact lookup_eq word word_prefix_succ inBounds (by decide : 1 < (word 0).length)
  · exact lookup_eq word word_prefix_succ inBounds (build index).readable

/-- Finite observations are read directly from the supplied generator words. -/
def generatedTower : Tower Nat :=
  Tower.ofGrowingLists word word_prefix_succ (fun n => by have h := word_readable n; omega)

theorem generatedTower_toStream : generatedTower.toStream = value := by
  funext n
  exact word_get_eq_value (n + 1) n (by have h := word_readable (n + 1); omega)

theorem runPrefix_succ (a : Nat → Nat) (runs : Nat) :
    runPrefix a (runs + 1) = runPrefix a runs ++
      List.replicate (a runs) (runSymbol runs) := by
  simp [runPrefix, List.range_succ, List.flatMap_append]

theorem runPrefix_value_eq_word (steps : Nat) :
    runPrefix value (steps + 2) = word steps := by
  induction steps with
  | zero => rfl
  | succ steps inductionHypothesis =>
      rw [show steps + 1 + 2 = (steps + 2) + 1 by omega]
      rw [runPrefix_succ, inductionHypothesis, word_succ]

theorem value_binary (index : Nat) : value index = 1 ∨ value index = 2 := by
  rcases index with _ | (_ | index)
  · simp
  · simp
  · exact (build index).binary _ (List.getElem_mem (build index).readable)

/-- The constructed sequence is extensionally its own alternating run-length encoding. -/
theorem value_isRunLengthFixedPoint : IsRunLengthFixedPoint value := by
  refine ⟨value_binary, ?_⟩
  intro runs index bound
  rcases runs with _ | (_ | runs)
  · simp [runPrefix] at bound
  · have zero : index = 0 := by simpa [runPrefix, value, runSymbol] using bound
    subst index; rfl
  · simpa only [runPrefix_value_eq_word] using
      word_get_eq_value runs index (by simpa only [runPrefix_value_eq_word] using bound)

/-- The independent fixed-point laws force the two seed run lengths. -/
theorem fixedPoint_initial {a : Nat → Nat} (h : IsRunLengthFixedPoint a) :
    a 0 = 1 ∧ a 1 = 2 := by
  have positive (n : Nat) : 0 < a n := by rcases h.1 n with one | two <;> omega
  have first : a 0 = 1 := by
    simpa [runPrefix, runSymbol] using (h.2 1 0 (by simpa [runPrefix] using positive 0)).symm
  refine ⟨first, ?_⟩
  have read := h.2 2 1 (by simpa [runPrefix, List.range_succ, first] using positive 1)
  simpa [runPrefix, List.range_succ, first, runSymbol] using read.symm

/-- Every fixed point forces each finite word of the independently defined generator. -/
theorem fixedPoint_runPrefix {a : Nat → Nat} (h : IsRunLengthFixedPoint a) (steps : Nat) :
    runPrefix a (steps + 2) = word steps := by
  induction steps with
  | zero =>
      simp [runPrefix, List.range_succ, word, build, (fixedPoint_initial h).1,
        (fixedPoint_initial h).2, runSymbol]
  | succ steps ih =>
      have next := h.2 (steps + 2) (steps + 2) (by simpa only [ih] using word_readable steps)
      simp only [ih] at next
      have value_eq := next.symm.trans (word_get_eq_value steps (steps + 2) (build steps).readable)
      rw [show steps + 1 + 2 = (steps + 2) + 1 by omega, runPrefix_succ, ih, value_eq, word_succ]

/-- The run-length specification has exactly the constructed sequence as its solution. -/
theorem fixedPoint_iff_eq_value (a : Nat → Nat) : IsRunLengthFixedPoint a ↔ a = value := by
  refine ⟨fun h => ?_, fun same => same ▸ value_isRunLengthFixedPoint⟩
  funext n
  have bound : n < (word n).length := by have readable := word_readable n; omega
  have read := h.2 (n + 2) n (by simpa only [fixedPoint_runPrefix h n] using bound)
  simpa only [fixedPoint_runPrefix h n, word_get_eq_value] using read.symm

/-- Every generator word agrees with the unique solution on its entire prefix. -/
theorem fixedPoint_word {a : Nat → Nat} (h : IsRunLengthFixedPoint a) (steps : Nat) :
    List.ofFn (fun i : Fin (word steps).length => a i.val) = word steps := by
  rw [(fixedPoint_iff_eq_value a).mp h, ← generatedTower_toStream]
  exact Tower.ofGrowingLists_word _ _ _ steps

/-- Number of symbols preceding the zero-based run `run`. -/
def runStart (run : Nat) : Nat := (runPrefix value run).length

@[simp] theorem runStart_zero : runStart 0 = 0 := rfl

theorem runStart_succ (run : Nat) :
    runStart (run + 1) = runStart run + value run := by
  simp [runStart, runPrefix_succ]

theorem runStart_lower_bound (run : Nat) : run ≤ runStart run := by
  induction run with
  | zero => simp
  | succ run ih =>
      rw [runStart_succ]
      rcases value_binary run with one | two <;> omega

/-- Every position inside a declared run has that run's alternating symbol. -/
theorem value_on_run (run offset : Nat) (inside : offset < value run) :
    value (runStart run + offset) = runSymbol run := by
  have bound : runStart run + offset < (runPrefix value (run + 1)).length := by
    simpa only [runPrefix_succ, List.length_append, List.length_replicate, runStart] using
      Nat.add_lt_add_left inside (runStart run)
  have fixed := value_isRunLengthFixedPoint.2 (run + 1) (runStart run + offset) bound
  simpa [runPrefix_succ, runStart] using fixed.symm

/-- The run and within-run offset of a positive sequence position. -/
structure RunCursor (position : Nat) where
  run : Nat
  offset : Nat
  runPositive : 1 ≤ run
  offsetBound : offset < value run
  positionEquation : position = runStart run + offset

/-- Advance one sequence position, either within a run or to the next run. -/
def RunCursor.advance {position : Nat}
    (cursor : RunCursor position) : RunCursor (position + 1) := by
  have position_eq := cursor.positionEquation
  have bound := cursor.offsetBound
  if continues : cursor.offset + 1 < value cursor.run then
    exact ⟨cursor.run, cursor.offset + 1, cursor.runPositive, continues, by omega⟩
  else
    refine ⟨cursor.run + 1, 0, by omega, ?_, ?_⟩
    · rcases value_binary (cursor.run + 1) with one | two <;> omega
    · rw [runStart_succ]; omega

@[simp] theorem RunCursor.advance_run {position : Nat} (c : RunCursor position) :
    c.advance.run = if c.offset + 1 < value c.run then c.run else c.run + 1 := by
  unfold advance; split <;> rfl

@[simp] theorem RunCursor.advance_offset {position : Nat} (c : RunCursor position) :
    c.advance.offset = if c.offset + 1 < value c.run then c.offset + 1 else 0 := by
  unfold advance; split <;> rfl

/-- Cursor for the next symbol after zero-based output position `step`. -/
def cursor : (step : Nat) → RunCursor (step + 1)
  | 0 => ⟨1, 0, by decide, by decide, by decide⟩
  | step + 1 => (cursor step).advance

theorem cursor_run_le_position (step : Nat) :
    (cursor step).run ≤ step + 1 := by
  have startBound := runStart_lower_bound (cursor step).run
  have position := (cursor step).positionEquation
  omega

theorem advance_run_le_succ {position : Nat} (current : RunCursor position) :
    current.advance.run ≤ current.run + 1 := by
  rw [RunCursor.advance_run]
  split <;> omega

theorem cursor_run_le_current {step : Nat} (positive : 1 ≤ step) :
    (cursor step).run ≤ step := by
  rcases step with _ | step
  · omega
  · induction step with
    | zero => decide
    | succ step ih => exact (advance_run_le_succ (cursor (step + 1))).trans (by omega)

theorem value_at_cursor (step : Nat) : value (step + 1) = runSymbol (cursor step).run :=
  (congrArg value (cursor step).positionEquation).trans (value_on_run _ _ (cursor step).offsetBound)

/-- Zero-based bit representation of the binary sequence. -/
def bit (index : Nat) : Nat := value index - 1

theorem bit_binary (index : Nat) : bit index = 0 ∨ bit index = 1 := by
  rcases value_binary index with result | result <;> simp [bit, result]

theorem bit_add_one (index : Nat) : bit index + 1 = value index := by
  rcases value_binary index with result | result <;> simp [bit, result]

/-- One exactly when the next sequence position starts a new run. -/
def boundaryBit (step : Nat) : Nat :=
  if (cursor step).offset = 0 then 1 else 0

theorem boundaryBit_binary (step : Nat) :
    boundaryBit step = 0 ∨ boundaryBit step = 1 := by
  unfold boundaryBit; split <;> simp

/-- Packed cursor used by the reported list-state program. -/
def packedCursor (step : Nat) : Nat :=
  2 * (step + 1 - (cursor step).run) + boundaryBit step

theorem packedCursor_div_two (step : Nat) :
    packedCursor step / 2 = step + 1 - (cursor step).run := by
  rcases boundaryBit_binary step with boundary | boundary <;>
    simp only [packedCursor, boundary] <;> omega

theorem runSymbol_eq_mod_add_one (run : Nat) :
    runSymbol run = run % 2 + 1 := by
  unfold runSymbol
  split <;> omega

theorem bit_on_run (run offset : Nat) (inside : offset < value run) :
    bit (runStart run + offset) = run % 2 := by
  simp [bit, value_on_run run offset inside, runSymbol_eq_mod_add_one]

theorem bit_at_cursor (step : Nat) :
    bit (step + 1) = (cursor step).run % 2 := by
  simp [bit, value_at_cursor, runSymbol_eq_mod_add_one]

/-- The packed parity bit advances the alternating run symbol exactly. -/
theorem bit_succ (step : Nat) :
    (boundaryBit step + bit step) % 2 = bit (step + 1) := by
  cases step with
  | zero => norm_num [boundaryBit, cursor, bit, value]
  | succ step =>
      rw [bit_at_cursor step, bit_at_cursor (step + 1)]
      change ((if (cursor step).advance.offset = 0 then 1 else 0) +
        (cursor step).run % 2) % 2 = (cursor step).advance.run % 2
      rw [RunCursor.advance_run, RunCursor.advance_offset]
      split_ifs <;> first | contradiction | omega

/--
The value selected from the packed history at one machine step.  The initial
state contains only the pointer and the first bit, so its zero-pop lookup reads
the pointer itself; every later step reads the bit at the active run.
-/
def cursorIncrement (step : Nat) : Nat :=
  if step = 0 then 1 else bit (cursor step).run

theorem cursorIncrement_binary (step : Nat) :
    cursorIncrement step = 0 ∨ cursorIncrement step = 1 := by
  unfold cursorIncrement; split_ifs <;> simp_all [bit_binary]

/-- The packed cursor update is exactly the value selected from its history. -/
theorem packedCursor_succ (step : Nat) :
    packedCursor (step + 1) = packedCursor step + cursorIncrement step := by
  by_cases initial : step = 0
  · subst step; decide
  simp only [cursorIncrement, initial, if_false]
  let current := cursor step
  have runBound : current.run ≤ step := cursor_run_le_current (by omega)
  have offsetBound := current.offsetBound
  have binary := value_binary current.run
  change 2 * (step + 1 + 1 - current.advance.run) +
      (if current.advance.offset = 0 then 1 else 0) =
    2 * (step + 1 - current.run) + (if current.offset = 0 then 1 else 0) + (value current.run - 1)
  rw [RunCursor.advance_run, RunCursor.advance_offset]
  split_ifs <;> first | contradiction | omega

/-- The low bit of the packed state is the next sequence bit. -/
theorem packedCursor_add_bit_mod_two (step : Nat) :
    (packedCursor step + bit step) % 2 = bit (step + 1) := by
  simpa [packedCursor, Nat.add_mod, Nat.mul_mod] using bit_succ step

theorem first_words : word 0 = [1, 2, 2] ∧ word 1 = [1, 2, 2, 1, 1] ∧
    word 2 = [1, 2, 2, 1, 1, 2] := by decide

theorem constants_not_fixed :
    ¬ IsRunLengthFixedPoint (fun _ => 1) ∧ ¬ IsRunLengthFixedPoint (fun _ => 2) := by
  constructor <;> intro h <;> have forced := fixedPoint_initial h <;> norm_num at forced

/-- Every finite prefix admits a binary continuation violating the global law. -/
theorem finite_prefix_not_sufficient (depth : Nat) :
    ∃ a, (∀ n, a n = 1 ∨ a n = 2) ∧ (∀ n, n < depth → a n = value n) ∧
      ¬ IsRunLengthFixedPoint a := by
  let a := Function.update value depth (3 - value depth)
  refine ⟨a, ?_, ?_, ?_⟩
  · intro n
    by_cases same : n = depth
    · subst n; rcases value_binary depth with h | h <;> simp [a, h]
    · simpa [a, same] using value_binary n
  · intro n hn; simp [a, ne_of_lt hn]
  · intro h
    have at_depth := congrFun ((fixedPoint_iff_eq_value a).mp h) depth
    rcases value_binary depth with h | h <;> simp [a, h] at at_depth

/-- Source coordinates for OEIS A000002 in the pinned snapshot. -/
def sourceA000002 : EntrySource where
  oeisId := "A000002"
  snapshotRevision := "a6e0f22854cc1c307da428e9d6295093781df7fa"
  entrySha256 := "aec5dbb47113a73fc27ffd20bc7da1e29e5e2383b502d756de3ea0f5e6f83986"
  offset := 1

/-- OEIS A000002, with the public one-based index translated to `value`. -/
def specA000002 : SequenceSpec where
  offset := 1
  Domain := fun index => 1 ≤ index
  value := fun index => Int.ofNat (value (index.toNat - 1))

def formalizationA000002 : Formalization := ⟨sourceA000002, specA000002, rfl⟩

end Mettapedia.Sequences.OEIS.Kolakoski
