import MettapediaFourColor.D3009Colouring
import MettapediaFourColor.WheelSeedRepairData
import MettapediaFourColor.KempeMaskCertificate

/-!
# A ranked repair certificate for a nonextending wheel boundary

Terminal records contain genuine colourings of the pinned source. Every other
record supplies an answer for each unsigned exterior skeleton, preserving its
whole chords and decreasing rank. This file proves checker soundness; the
finite checks and the precise set of supported initial traces are separate.
-/
namespace FourColor.WheelSeedRepairCertificate

open Color KempeProfileCertificate KempeBoundarySplit

abbrev State := Fin WheelSeedRepairData.count

def digit (text : String) (i : ℕ) : ℕ :=
  let c := (text.toUTF8[i]?.getD 48).toNat
  if c < 58 then c - 48 else c - 55

def number (text : String) (start width : ℕ) : ℕ :=
  (List.range width).foldl (fun n i => 36 * n + digit text (start + i)) 0

def color (d : ℕ) : Color :=
  match d with | 1 => c1 | 2 => c2 | 3 => c3 | _ => c0

def perm (i : ℕ) : EdgePerm :=
  match i with
  | 0 => .e123 | 1 => .e132 | 2 => .e213
  | 3 => .e231 | 4 => .e312 | _ => .e321

def record (i : State) : String :=
  WheelSeedRepairData.records (i.val / WheelSeedRepairData.block)

def field (i : State) (j : ℕ) : ℕ :=
  digit (record i) (27 * (i.val % WheelSeedRepairData.block) + j)

def word (i : State) : List Color := (List.range 13).map fun j => color (field i j)
def rank (i : State) : ℕ := field i 13

def offset (i : State) : ℕ :=
  number (record i) (27 * (i.val % WheelSeedRepairData.block) + 22) 5

def next (i : State) (j : ℕ) : State × EdgePerm :=
  let k := offset i + j
  let text := WheelSeedRepairData.chords (k / WheelSeedRepairData.block)
  let start := 8 * (k % WheelSeedRepairData.block)
  (⟨number text (start + 3) 4 % WheelSeedRepairData.count, Nat.mod_lt _ (by decide)⟩,
    perm (digit text (start + 7)))

def mask (i : State) (j : ℕ) : List Bool :=
  let k := offset i + j
  let text := WheelSeedRepairData.chords (k / WheelSeedRepairData.block)
  let code := number text (8 * (k % WheelSeedRepairData.block)) 3
  (List.range (KempeChordMasks.active (word i)).length).map fun k => code.testBit k

def answers (i : State) : List (State × EdgePerm) := KempeMaskCertificate.answers word next i

/-- The full list of edges is checked against the pinned source graph. -/
def edges : List (Fin 21 × Fin 21) :=
  [(0, 1), (0, 12), (0, 15), (0, 17), (1, 2), (1, 15),
   (2, 3), (2, 15), (2, 16), (3, 4), (3, 16), (4, 5),
   (4, 14), (4, 16), (5, 6), (5, 14), (5, 20), (6, 7),
   (6, 20), (7, 8), (7, 19), (7, 20), (8, 9), (8, 19),
   (9, 10), (9, 18), (9, 19), (10, 11), (10, 18), (11, 12),
   (11, 17), (11, 18), (12, 17), (13, 14), (13, 15), (13, 16),
   (13, 17), (13, 18), (13, 19), (13, 20), (14, 16), (14, 20),
   (15, 16), (15, 17), (17, 18), (18, 19), (19, 20)]

set_option maxRecDepth 32768 in
theorem source_edges : ∀ a b : Fin 21, D3009Wheel.input.graph.Adj a b ↔
    (a, b) ∈ edges ∨ (b, a) ∈ edges := by decide +kernel

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
    KempeMaskCertificate.check word rank next mask i

theorem check_sound (i : State) (h : check i = true) :
    Supports (word i) ∨
      ((∀ gram, matchg [] (word i) gram →
          ∃ a ∈ answers i, matchg [] (answerWord word a) gram) ∧
        ∀ a ∈ answers i, rank a.1 < rank i) := by
  unfold check at h
  split at h
  · exact Or.inl (terminalCheck_sound i h)
  · exact Or.inr (KempeMaskCertificate.check_sound word rank next mask i h)

/-- Checking the retained closure supports each retained state, not all traces. -/
theorem coclosure (checked : ∀ i, check i = true) (i : State) :
    KempeCoclosure Supports (word i) :=
  KempeIndexedCertificate.sound word rank answers (fun i => check_sound i (checked i)) i

end FourColor.WheelSeedRepairCertificate
