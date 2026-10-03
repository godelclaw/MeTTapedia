import MettapediaFourColor.KempeRepairComposition
import MettapediaFourColor.ResidualSeedRepairReconstruction
import MettapediaFourColor.ThreeBlockRepairTransferData

/-! # Three shared decisions repair every symbolic three-run choice

The extension has three nonterminal decisions, six direct source witnesses
and eight references to already checked seed states. Its leaves compose
with those earlier repairs while retaining the same exterior predicate.
This covers the eight Boolean boundary words, not all D0092 colourings.
-/

namespace FourColor.ThreeBlockRepairTransfer

open Color KempeProfileCertificate KempeBoundarySplit
open FiveTriangleCollapseObstruction

abbrev State := Fin ThreeBlockRepairTransferData.count
abbrev Supports := ResidualSeedRepairCertificate.Supports

def field (i : State) (j : ℕ) : ℕ :=
  ResidualSeedRepairCertificate.digit ThreeBlockRepairTransferData.records (23 * i.val + j)

def word (i : State) : List Color :=
  (List.range 11).map fun j => ResidualSeedRepairCertificate.color (field i j)

def rank (i : State) : ℕ := field i 11

def offset (i : State) : ℕ :=
  ResidualSeedRepairCertificate.number ThreeBlockRepairTransferData.records (23 * i.val + 20) 3

def next (i : State) (j : ℕ) : State × EdgePerm :=
  let start := 5 * (offset i + j)
  (⟨ResidualSeedRepairCertificate.number ThreeBlockRepairTransferData.chords
      (start + 2) 2 % ThreeBlockRepairTransferData.count, Nat.mod_lt _ (by decide)⟩,
    ResidualSeedRepairCertificate.perm
      (ResidualSeedRepairCertificate.digit ThreeBlockRepairTransferData.chords (start + 4)))

def mask (i : State) (j : ℕ) : List Bool :=
  let code := ResidualSeedRepairCertificate.number ThreeBlockRepairTransferData.chords
    (5 * (offset i + j)) 2
  (List.range (KempeChordMasks.active (word i)).length).map code.testBit

def answers (i : State) : List (State × EdgePerm) := KempeMaskCertificate.answers word next i

def oldState (i : State) : ResidualSeedRepairCertificate.State :=
  ⟨ResidualSeedRepairCertificate.number ThreeBlockRepairTransferData.records
      (23 * i.val + 13) 2 % ResidualSeedRepairData.count, Nat.mod_lt _ (by decide)⟩

def oldPerm (i : State) : EdgePerm := ResidualSeedRepairCertificate.perm (field i 15)

def coloring (i : State) (v : Fin 18) : Color :=
  if v.val < 11 then (untrace 0 (word i)).getD v.val 0
  else ResidualSeedRepairCertificate.color (field i (13 + (v.val - 11)))

def directCheck (i : State) : Bool :=
  ResidualSeedRepairCertificate.edges.all (fun (a, b) => decide (coloring i a ≠ coloring i b)) &&
    decide (word i = trace (upper.boundary.map (coloring i)))

theorem directCheck_sound (i : State) (h : directCheck i = true) : Supports (word i) := by
  rw [directCheck, Bool.and_eq_true] at h
  obtain ⟨proper, ht⟩ := h
  refine ⟨.mk (coloring i) (fun {a b} edge => ?_), of_decide_eq_true ht⟩
  rcases (ResidualSeedRepairCertificate.source_edges a b).mp edge with hab | hba
  · exact of_decide_eq_true ((List.all_eq_true.mp proper) (a, b) hab)
  · exact (of_decide_eq_true ((List.all_eq_true.mp proper) (b, a) hba)).symm

def leafCheck (i : State) : Bool :=
  if field i 12 = 0 then directCheck i
  else decide ((word i).map (oldPerm i) = ResidualSeedRepairCertificate.word (oldState i))

theorem leafCheck_sound (i : State) (h : leafCheck i = true) :
    KempeCoclosure Supports (word i) := by
  unfold leafCheck at h
  split at h
  · exact KempeAnswerComposition.of_mem (directCheck_sound i h)
  · apply kempeCoclosure_of_map (oldPerm i)
    rw [of_decide_eq_true h]
    exact ResidualSeedRepairCertificate.coclosure ResidualSeedRepairCertificate.checked (oldState i)

def check (i : State) : Bool :=
  if rank i = 0 then leafCheck i else KempeMaskCertificate.check word rank next mask i

theorem check_sound (i : State) (h : check i = true) :
    KempeCoclosure Supports (word i) ∨
      ((∀ gram, matchg [] (word i) gram →
          ∃ a ∈ answers i, matchg [] (answerWord word a) gram) ∧
        ∀ a ∈ answers i, rank a.1 < rank i) := by
  unfold check at h
  split at h
  · exact Or.inl (leafCheck_sound i h)
  · exact Or.inr (KempeMaskCertificate.check_sound word rank next mask i h)

set_option maxRecDepth 65536 in
set_option maxHeartbeats 2000000 in
theorem checked : ∀ i : State, check i = true := by decide +kernel

theorem repair (i : State) : KempeCoclosure Supports (word i) :=
  KempeRepairComposition.sound word rank answers (fun i => check_sound i (checked i)) i

def threeTrace (a b c : Bool) : List Color :=
  trace ((List.finRange 11).map (ThreeBlockCore.word a b c))

theorem direct (a b c : Bool) (hab : a = b) (hbc : b ≠ c) :
    Supports (threeTrace a b c) := by
  refine ⟨ThreeBlockCore.colouring a b c hab hbc, ?_⟩
  rw [ResidualSeedRepairCertificate.source_boundary, List.map_map]
  simp only [Function.comp_def, ThreeBlockCore.colouring_boundary, threeTrace]

def transferRoot (a c : Bool) : State := if a = c then ⟨10, by decide⟩ else ⟨9, by decide⟩

def transferPerm (a c : Bool) : EdgePerm :=
  if a then (if c then .e312 else .e321) else (if c then .e123 else .e213)

set_option maxRecDepth 65536 in
theorem root_word : ∀ a b c, a ≠ b →
    (threeTrace a b c).map (transferPerm a c) = word (transferRoot a c) := by decide +kernel

theorem same_word : ∀ a : Bool,
    (threeTrace a a a).map ((if a then EdgePerm.e321 else EdgePerm.e123) : EdgePerm) =
      ResidualSeedRepairCertificate.seedTrace := by decide +kernel

/-- All eight joint choices share direct extension, the old seed theorem,
or the same three-decision extension. No exterior size bound is imposed. -/
theorem three_run_repair (a b c : Bool) : KempeCoclosure Supports (threeTrace a b c) := by
  by_cases hab : a = b
  · by_cases hbc : b = c
    · subst b; subst c
      apply kempeCoclosure_of_map (if a then EdgePerm.e321 else EdgePerm.e123)
      rw [same_word]
      exact ResidualSeedRepairCertificate.seed_repair
    · exact KempeAnswerComposition.of_mem (direct a b c hab hbc)
  · apply kempeCoclosure_of_map (transferPerm a c)
    rw [root_word a b c hab]
    exact repair (transferRoot a c)

end FourColor.ThreeBlockRepairTransfer
