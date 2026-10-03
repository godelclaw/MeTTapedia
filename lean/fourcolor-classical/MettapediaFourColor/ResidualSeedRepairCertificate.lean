import MettapediaFourColor.FiveTriangleCollapseObstruction
import MettapediaFourColor.ResidualSeedRepairData
import MettapediaFourColor.KempeMaskCertificate

/-!
# Checking a compact mixed-pair repair of the D0092 seed

Each terminal supplies a colouring of the complete source graph. Each other
state answers every unsigned exterior matching by whole-chord switches and
strict rank descent. The same signed exterior relation survives each answer.
This module proves soundness independently of the supplied data's validity.
-/
namespace FourColor.ResidualSeedRepairCertificate

open Color KempeProfileCertificate KempeBoundarySplit

abbrev State := Fin ResidualSeedRepairData.count

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
  ResidualSeedRepairData.records (i.val / ResidualSeedRepairData.block)

def field (i : State) (j : ℕ) : ℕ :=
  digit (record i) (22 * (i.val % ResidualSeedRepairData.block) + j)

def word (i : State) : List Color := (List.range 11).map fun j => color (field i j)
def rank (i : State) : ℕ := field i 11

def offset (i : State) : ℕ :=
  number (record i) (22 * (i.val % ResidualSeedRepairData.block) + 19) 3

def next (i : State) (j : ℕ) : State × EdgePerm :=
  let k := offset i + j
  let text := ResidualSeedRepairData.chords (k / ResidualSeedRepairData.block)
  let start := 5 * (k % ResidualSeedRepairData.block)
  (⟨number text (start + 2) 2 % ResidualSeedRepairData.count, Nat.mod_lt _ (by decide)⟩,
    perm (digit text (start + 4)))

def mask (i : State) (j : ℕ) : List Bool :=
  let k := offset i + j
  let text := ResidualSeedRepairData.chords (k / ResidualSeedRepairData.block)
  let code := number text (5 * (k % ResidualSeedRepairData.block)) 2
  (List.range (KempeChordMasks.active (word i)).length).map fun k => code.testBit k

def answers (i : State) : List (State × EdgePerm) := KempeMaskCertificate.answers word next i

/-- The full list of edges is checked against the pinned source graph. -/
def edges : List (Fin 18 × Fin 18) :=
  [(0, 1), (0, 10), (0, 17), (1, 2), (1, 15), (1, 17), (2, 3), (2, 15), (3, 4), (3, 12), (3, 15), (4, 5), (4, 12), (5, 6), (5, 12), (5, 13), (6, 7), (6, 13), (7, 8), (7, 13), (7, 14), (8, 9), (8, 11), (8, 14), (8, 16), (9, 10), (9, 16), (10, 16), (10, 17), (11, 12), (11, 14), (11, 15), (11, 16), (11, 17), (12, 13), (12, 14), (12, 15), (13, 14), (15, 17), (16, 17)]

set_option maxRecDepth 32768 in
theorem source_edges : ∀ a b : Fin 18, FiveTriangleCollapseObstruction.upper.graph.Adj a b ↔
    (a, b) ∈ edges ∨ (b, a) ∈ edges := by decide +kernel

def coloring (i : State) (v : Fin 18) : Color :=
  if v.val < 11 then (untrace 0 (word i)).getD v.val 0
  else color (field i (12 + (v.val - 11)))

def terminalCheck (i : State) : Bool :=
  edges.all (fun (a, b) => decide (coloring i a ≠ coloring i b)) &&
    decide (word i = trace (FiveTriangleCollapseObstruction.upper.boundary.map (coloring i)))

def Supports : List Color → Prop :=
  GraphTrace FiveTriangleCollapseObstruction.upper.graph FiveTriangleCollapseObstruction.upper.boundary

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

end FourColor.ResidualSeedRepairCertificate
