import MettapediaFourColor.ExceptionalCore
import MettapediaFourColor.ExceptionalRepairData
import MettapediaFourColor.KempeMaskCertificate
import MettapediaFourColor.KempeBoundarySplit
import FourColor.Bulk.Index

/-!
# Checked joint-chord repair for the D1774 boundary

The finite certificate uses the same complete-chord theorem as the diamond
family. All answers preserve the chosen exterior chromogram. Terminal
witnesses are checked on every edge of the literal source graph, including
the complete ring. This proves an abstract D-repair contract; realization of
Kempe closure by the actual exterior is a separate geometric obligation.
-/

namespace FourColor.ExceptionalRepairCertificate

open Color KempeProfileCertificate KempeBoundarySplit

abbrev State := Fin ExceptionalRepairData.count

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

def field (i : State) (j : ℕ) : ℕ :=
  digit (ExceptionalRepairData.records i.val) j

def word (i : State) : List Color := (List.range 11).map fun j => color (field i j)
def rank (i : State) : ℕ := field i 11

def answer (text : String) (start : ℕ) : State × EdgePerm :=
  (⟨number text start 3 % ExceptionalRepairData.count, Nat.mod_lt _ (by decide)⟩,
    perm (digit text (start + 3)))

def next (i : State) (j : ℕ) : State × EdgePerm :=
  let k := number (ExceptionalRepairData.records i.val) 20 4 + j
  answer (ExceptionalRepairData.chords (k / 4)) (6 * (k % 4) + 2)

def mask (i : State) (j : ℕ) : List Bool :=
  let k := number (ExceptionalRepairData.records i.val) 20 4 + j
  let code := number (ExceptionalRepairData.chords (k / 4)) (6 * (k % 4)) 2
  (List.range (KempeChordMasks.active (word i)).length).map fun k => code.testBit k

def answers (i : State) : List (State × EdgePerm) := KempeMaskCertificate.answers word next i

/-- All forty-three undirected edges, validated against the source decoder once. -/
def edges : List (Fin 19 × Fin 19) :=
  [(0, 1), (0, 10), (0, 18), (1, 2), (1, 13), (1, 16), (1, 18),
   (2, 3), (2, 13), (3, 4), (3, 13), (3, 14), (4, 5), (4, 14),
   (5, 6), (5, 12), (5, 14), (5, 17), (6, 7), (6, 12), (7, 8),
   (7, 12), (7, 15), (8, 9), (8, 11), (8, 15), (9, 10), (9, 11),
   (10, 11), (10, 18), (11, 14), (11, 15), (11, 16), (11, 17),
   (11, 18), (12, 15), (12, 17), (13, 14), (13, 16), (14, 16),
   (14, 17), (15, 17), (16, 18)]

set_option maxRecDepth 32768 in
theorem source_edges : ∀ a b : Fin 19, ExceptionalCore.input.graph.Adj a b ↔
    (a, b) ∈ edges ∨ (b, a) ∈ edges := by decide +kernel

def coloring (i : State) (v : Fin 19) : Color :=
  if v.val < 11 then (untrace 0 (word i)).getD v.val 0
  else color (field i (12 + (v.val - 11)))

def terminalCheck (i : State) : Bool :=
  edges.all (fun (a, b) => decide (coloring i a ≠ coloring i b)) &&
    decide (word i = trace (ExceptionalCore.input.boundary.map (coloring i)))

def Supports : List Color → Prop :=
  GraphTrace ExceptionalCore.input.graph ExceptionalCore.input.boundary

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

def inputCheck (j : ℕ) : Bool :=
  let et := Bulk.traceOf 10 j
  let a := answer (ExceptionalRepairData.lookup (j / 4)) (4 * (j % 4))
  decide ((Bulk.partialOf 10 j).sum = 0) || decide (et.map a.2 = word a.1)

/-- Completeness consumes a separately checked finite lookup, not a search axiom. -/
theorem repair_of_checks (checked : ∀ i, check i = true)
    (coverage : ∀ j : Fin (3 ^ 10), inputCheck j = true) : Repairs Supports 11 := by
  intro et hlen hzero hsum
  have hne : et ≠ [] := by intro h; simp [h] at hlen
  have htail : et.dropLast.length = 10 := by simp [hlen]
  have hz : (0 : Color) ∉ et.dropLast := fun h => hzero (List.mem_of_mem_dropLast h)
  let j := Bulk.indexOf 10 et.dropLast
  have hj := Bulk.indexOf_lt 10 et.dropLast
  have hp : Bulk.partialOf 10 j = et.dropLast := Bulk.partialOf_indexOf htail hz
  have ht : Bulk.traceOf 10 j = et := by
    rw [Bulk.traceOf, hp]
    have hlast := List.dropLast_append_getLast hne
    have hs : et.dropLast.sum + et.getLast hne = 0 := by
      simpa using (congrArg List.sum hlast).trans hsum
    rw [completeTrace, Color.add_eq_zero_iff.mp hs, hlast]
  have hs : (Bulk.partialOf 10 j).sum ≠ 0 := by
    intro zero
    apply hzero
    rw [← ht, Bulk.traceOf, completeTrace, zero]
    simp
  have hc := coverage ⟨j, hj⟩
  simp only [inputCheck, Bool.or_eq_true, decide_eq_true_eq] at hc
  rcases hc with hc | hc
  · exact (hs hc).elim
  · let a := answer (ExceptionalRepairData.lookup (j / 4)) (4 * (j % 4))
    have h := KempeIndexedCertificate.sound word rank answers
      (fun i => check_sound i (checked i)) a.1
    have he : et.map a.2 = word a.1 := by simpa only [ht] using hc
    exact kempeCoclosure_of_map a.2 (he ▸ h)

end FourColor.ExceptionalRepairCertificate
