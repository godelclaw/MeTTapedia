import MettapediaFourColor.WheelSeedRepairCertificate
import MettapediaFourColor.KempeSharedMaskCertificate
import MettapediaFourColor.WheelRepairData
import FourColor.Bulk.Index

/-!
# Complete wheel repair from checked records and checked input coverage

Terminal records contain genuine colourings of the pinned source. Every other
record supplies an answer for each unsigned exterior skeleton, preserving its
whole chords and decreasing rank. This file proves checker soundness; the
finite checks are separate. Input coverage includes every proper zero-sum
thirteen-port trace, with its colour permutation recorded explicitly.
-/
namespace FourColor.WheelRepairCertificate

open Color KempeProfileCertificate KempeBoundarySplit

abbrev State := Fin WheelRepairData.count

open WheelSeedRepairCertificate (color perm edges source_edges)

/-- Six-bit cells encode the base36 digits of each supplied field. -/
def digit (text : ℕ) (i : ℕ) : ℕ := (text >>> (6 * i)) % 64

def number (text : ℕ) (start width : ℕ) : ℕ :=
  (List.range width).foldl (fun n i => 36 * n + digit text (start + i)) 0

def record (i : State) : ℕ :=
  WheelRepairData.records (i.val / WheelRepairData.block)

def field (i : State) (j : ℕ) : ℕ :=
  digit (record i) (34 * (i.val % WheelRepairData.block) + j)

def word (i : State) : List Color := (List.range 13).map fun j => color (field i j)
def rank (i : State) : ℕ := field i 13

def offset (i : State) : ℕ :=
  number (record i) (34 * (i.val % WheelRepairData.block) + 22) 5

def actionCount (i : State) : ℕ :=
  number (record i) (34 * (i.val % WheelRepairData.block) + 27) 2

def action (i : State) (j : ℕ) : KempeSharedMaskCertificate.Action State :=
  let k := offset i + j
  let text := WheelRepairData.actions (k / WheelRepairData.block)
  let start := 8 * (k % WheelRepairData.block)
  let target : State := ⟨number text (start + 3) 4 % WheelRepairData.count,
    Nat.mod_lt _ (by decide)⟩
  let mask := number text start 3
  ((target, perm (digit text (start + 7))),
    (List.range (KempeChordMasks.active (word i)).length).map fun k => mask.testBit k)

def actions (i : State) : List (KempeSharedMaskCertificate.Action State) :=
  (List.range (actionCount i)).map (action i)

def select (i : State) (j : ℕ) : ℕ :=
  let k := number (record i) (34 * (i.val % WheelRepairData.block) + 29) 5 + j
  number (WheelRepairData.selections (k / WheelRepairData.selectionBlock))
    (2 * (k % WheelRepairData.selectionBlock)) 2

def answers (i : State) : List (State × EdgePerm) :=
  KempeSharedMaskCertificate.answers actions i

def coloring (i : State) (v : Fin 21) : Color :=
  if v.val < 13 then (untrace 0 (word i)).getD v.val 0
  else color (field i (14 + (v.val - 13)))

def terminalCheck (i : State) : Bool :=
  edges.all (fun (a, b) => decide (coloring i a ≠ coloring i b)) &&
    decide (word i = trace (D3009Wheel.input.boundary.map (coloring i)))

def Supports : List Color → Prop :=
  GraphTrace D3009Wheel.input.graph D3009Wheel.input.boundary

theorem terminalCheck_sound (i : State) (h : terminalCheck i = true) : Supports (word i) := by
  rw [terminalCheck, Bool.and_eq_true] at h
  obtain ⟨proper, ht⟩ := h
  refine ⟨.mk (coloring i) (fun {a b} edge => ?_), of_decide_eq_true ht⟩
  rcases (source_edges a b).mp edge with hab | hba
  · exact of_decide_eq_true ((List.all_eq_true.mp proper) (a, b) hab)
  · exact (of_decide_eq_true ((List.all_eq_true.mp proper) (b, a) hba)).symm

def check (i : State) : Bool :=
  if rank i = 0 then terminalCheck i else
    KempeSharedMaskCertificate.check word rank actions select i

theorem check_sound (i : State) (h : check i = true) :
    Supports (word i) ∨
      ((∀ gram, matchg [] (word i) gram →
          ∃ a ∈ answers i, matchg [] (answerWord word a) gram) ∧
        ∀ a ∈ answers i, rank a.1 < rank i) := by
  unfold check at h
  split at h
  · exact Or.inl (terminalCheck_sound i h)
  · exact Or.inr (KempeSharedMaskCertificate.check_sound word rank actions select i h)

/-- Every checked record admits a repair preserving a Kempe-closed exterior. -/
theorem coclosure (checked : ∀ i, check i = true) (i : State) :
    KempeCoclosure Supports (word i) :=
  KempeIndexedCertificate.sound word rank answers (fun i => check_sound i (checked i)) i


def inputAnswer (j : ℕ) : State × EdgePerm :=
  let text := WheelRepairData.lookup (j / WheelRepairData.block)
  let start := 5 * (j % WheelRepairData.block)
  (⟨number text start 4 % WheelRepairData.count, Nat.mod_lt _ (by decide)⟩,
    perm (digit text (start + 4)))

def inputCheck (j : ℕ) : Bool :=
  let et := Bulk.traceOf 12 j
  let a := inputAnswer j
  decide ((Bulk.partialOf 12 j).sum = 0) || decide (et.map a.2 = word a.1)

/-- Completeness consumes a checked finite lookup, not a generator assumption. -/
theorem repair_of_checks (checked : ∀ i, check i = true)
    (coverage : ∀ j : Fin (3 ^ 12), inputCheck j = true) : Repairs Supports 13 := by
  intro et hlen hzero hsum
  have hne : et ≠ [] := by intro h; simp [h] at hlen
  have htail : et.dropLast.length = 12 := by simp [hlen]
  have hz : (0 : Color) ∉ et.dropLast := fun h => hzero (List.mem_of_mem_dropLast h)
  let j := Bulk.indexOf 12 et.dropLast
  have hj := Bulk.indexOf_lt 12 et.dropLast
  have hp : Bulk.partialOf 12 j = et.dropLast := Bulk.partialOf_indexOf htail hz
  have ht : Bulk.traceOf 12 j = et := by
    rw [Bulk.traceOf, hp]
    have hlast := List.dropLast_append_getLast hne
    have hs : et.dropLast.sum + et.getLast hne = 0 := by
      simpa using (congrArg List.sum hlast).trans hsum
    rw [completeTrace, Color.add_eq_zero_iff.mp hs, hlast]
  have hs : (Bulk.partialOf 12 j).sum ≠ 0 := by
    intro zero
    apply hzero
    rw [← ht, Bulk.traceOf, completeTrace, zero]
    simp
  have hc := coverage ⟨j, hj⟩
  simp only [inputCheck, Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc with hc | hc
  · exact (hs hc).elim
  · have he : et.map (inputAnswer j).2 = word (inputAnswer j).1 := by
      simpa only [ht] using hc
    exact kempeCoclosure_of_map (inputAnswer j).2 (he ▸ coclosure checked (inputAnswer j).1)

end FourColor.WheelRepairCertificate
