import MettapediaFourColor.DiamondProfile
import MettapediaFourColor.DiamondProfileData
import MettapediaFourColor.KempeProfileCertificate
import MettapediaFourColor.KempeChordExchange
import MettapediaFourColor.KempeChordMasks
import MettapediaFourColor.KempeAnchorProjection

/-! # One joint-profile certificate for the three diamond cores

The 236 trace representatives use a single rank on 92 joint profile types.
Fifty-one profile types have actual interior colourings; the other 41 descend
through checked Kempe answers. A single-chord theorem handles 71 nonterminal
representatives; a coupled two-ear law handles another 24. Joint anchor
projections handle the remaining five. The rank, partner targets, 216 local
ear-pair classifications and 44 joint-anchor classifications remain finite data.
No original configuration certificate, colour-decorated finite-cover checker
or global Kempe fixed point is used by this certificate.
-/

namespace FourColor.DiamondProfileCertificate

open Color DiamondProfile

def count (s : Shape) : ℕ := match s.val with | 0 => 31 | 1 => 91 | _ => 114
def offset (s : Shape) : ℕ := match s.val with | 0 => 0 | 1 => 31 | _ => 122

theorem count_pos (s : Shape) : 0 < count s := by
  fin_cases s <;> decide

abbrev State (s : Shape) := Fin (count s)

def digit (text : String) (i : ℕ) : ℕ :=
  let c := (text.toUTF8[i]?.getD 48).toNat
  if c < 58 then c - 48 else c - 55

def number (text : String) (start width : ℕ) : ℕ :=
  (List.range width).foldl (fun n i => 36 * n + digit text (start + i)) 0

def readColor (text : String) (i : ℕ) : Color :=
  match digit text i with | 1 => c1 | 2 => c2 | 3 => c3 | _ => c0

def word (s : Shape) (i : State s) : List Color :=
  (List.range (size s)).map fun j => readColor
    (DiamondProfileData.wordCodes (offset s + i.val)) j

def readPerm (i : ℕ) : EdgePerm :=
  match i with
  | 0 => .e123 | 1 => .e132 | 2 => .e213
  | 3 => .e231 | 4 => .e312 | _ => .e321

def answers (s : Shape) (i : State s) : List (State s × EdgePerm) :=
  let data := DiamondProfileData.answerCodes (offset s + i.val)
  (List.range (digit data 0)).map fun j =>
    (⟨number data (1 + 3 * j) 2 % count s,
      Nat.mod_lt _ (count_pos s)⟩,
      readPerm (digit data (3 + 3 * j)))

/-- Zero is terminal; 1--8 select a chord anchor, 9 ears, and 10--12 joint anchors. -/
def strategy (s : Shape) (i : State s) : ℕ :=
  digit (DiamondProfileData.wordCodes (offset s + i.val)) 8

/-- Three shared patterns, in active-port coordinates. -/
def anchorPattern : ℕ → List ℕ
  | 10 => [0, 1]
  | 11 => [0, 4]
  | 12 => [0, 1, 2]
  | _ => []

def coverCheck (s : Shape) (i : State s) : Bool :=
  let et := word s i
  let ans := answers s i
  if strategy s i = 0 then
    false
  else if strategy s i = 9 then
    KempeChordMasks.coverCheck et (ans.map (KempeProfileCertificate.answerWord (word s)))
  else if 10 ≤ strategy s i then
    KempeAnchorProjection.coverCheck et (anchorPattern (strategy s i))
      (ans.map (KempeProfileCertificate.answerWord (word s)))
  else
    let anchor := strategy s i - 1
    decide (anchor ≤ et.length ∧ ((et.rotate anchor).headD 0).hi = true) &&
      (KempeChordExchange.answers et anchor).all fun t => ans.any fun a =>
        decide (KempeProfileCertificate.answerWord (word s) a = t)

theorem coverCheck_sound (s : Shape) (i : State s) (h : coverCheck s i = true)
    (gram : Chromogram) (hm : matchg [] (word s i) gram) :
    ∃ a ∈ answers s i,
      matchg [] (KempeProfileCertificate.answerWord (word s) a) gram := by
  unfold coverCheck at h
  split at h
  · simp at h
  · split at h
    · obtain ⟨t, ht, hmatch⟩ := KempeChordMasks.coverCheck_sound _ _ h gram hm
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
      exact ⟨a, ha, hmatch⟩
    · split at h
      · obtain ⟨t, ht, hmatch⟩ := KempeAnchorProjection.coverCheck_sound _ _ _ h gram hm
        obtain ⟨a, ha, rfl⟩ := List.mem_map.mp ht
        exact ⟨a, ha, hmatch⟩
      · rw [Bool.and_eq_true] at h
        obtain ⟨guard, allAnswers⟩ := h
        obtain ⟨bound, high⟩ := of_decide_eq_true guard
        obtain ⟨t, ht, hmatch⟩ := KempeChordExchange.answer_exists _ _ gram bound high hm
        obtain ⟨a, ha, heq⟩ := List.any_eq_true.mp (List.all_eq_true.mp allAnswers t ht)
        refine ⟨a, ha, ?_⟩
        simpa only [of_decide_eq_true heq] using hmatch

/-- The rank depends on boundary length and the joint availability profile. -/
def rank (s : Shape) (et : List Color) : ℕ :=
  let profile := key s et
  match (List.range 92).find? (fun i =>
      decide (number (DiamondProfileData.rankCodes i) 0 4 = profile)) with
  | none => 0
  | some i => digit (DiamondProfileData.rankCodes i) 4

def check (s : Shape) (i : State s) : Bool :=
  if rank s (word s i) = 1 then good s (word s i) && decide (strategy s i = 0)
  else coverCheck s i &&
    (answers s i).all fun a => decide (rank s (word s a.1) < rank s (word s i))

theorem check_sound (s : Shape) (i : State s) (h : check s i = true) :
    Supports s (word s i) ∨
      ((∀ gram, matchg [] (word s i) gram →
          ∃ a ∈ answers s i,
            matchg [] (KempeProfileCertificate.answerWord (word s) a) gram) ∧
        ∀ a ∈ answers s i, rank s (word s a.1) < rank s (word s i)) := by
  unfold check at h
  split at h
  · rw [Bool.and_eq_true] at h
    exact Or.inl (good_supports s _ h.1)
  · rw [Bool.and_eq_true] at h
    obtain ⟨hc, ha⟩ := h
    exact Or.inr ⟨coverCheck_sound s i hc,
      fun a hm => of_decide_eq_true ((List.all_eq_true.mp ha) a hm)⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Check the finite profile ranks, actual terminal witnesses and all Kempe answers.
theorem checked0 : ∀ i : State 0, check 0 i = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Check the finite profile ranks, actual terminal witnesses and all Kempe answers.
theorem checked1 : ∀ i : State 1, check 1 i = true := by decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 2000000 in
-- Check the finite profile ranks, actual terminal witnesses and all Kempe answers.
theorem checked2 : ∀ i : State 2, check 2 i = true := by decide +kernel

theorem checked (s : Shape) : ∀ i : State s, check s i = true := by
  fin_cases s
  · exact checked0
  · exact checked1
  · exact checked2

/-- Every selected structural consumer is nonterminal and checks its full partner cover. -/
theorem structural_checked (s : Shape) (i : State s) (hs : strategy s i ≠ 0) :
    rank s (word s i) ≠ 1 ∧ coverCheck s i = true := by
  have h := checked s i
  unfold check at h
  split at h
  · rw [Bool.and_eq_true] at h
    exact (hs (of_decide_eq_true h.2)).elim
  · rw [Bool.and_eq_true] at h
    exact ⟨by assumption, h.1⟩

/-- The structural rule has actual consumers in each of the three cores. -/
theorem structural_counts :
    ([0, 1, 2] : List Shape).map (fun s =>
      ((List.finRange (count s)).filter fun i => strategy s i != 0).length) = [15, 52, 33] := by
  decide +kernel

/-- The coupled rule has consumers in all three cores, retaining nine cases each. -/
theorem coupled_counts :
    ([0, 1, 2] : List Shape).map (fun s =>
      ((List.finRange (count s)).filter fun i => strategy s i == 9).length) = [4, 7, 13] ∧
    (KempeChordMasks.earPairs 6).length = 9 := by
  decide +kernel

/-- Five consumers retain 44 joint classifications from three shared signature sets. -/
theorem anchor_counts :
    ([0, 1, 2] : List Shape).map (fun s =>
      ((List.finRange (count s)).filter fun i => decide (10 ≤ strategy s i)).length) =
        [0, 0, 5] ∧
    ([10, 11, 12] : List ℕ).map (fun p =>
      (KempeAnchorProjection.signatures 8 (anchorPattern p)).length) = [7, 10, 10] ∧
    ((List.finRange (count 2)).map fun i =>
      if 10 ≤ strategy 2 i then
        (KempeAnchorProjection.signatures
          (KempeChordMasks.active (word 2 i)).length (anchorPattern (strategy 2 i))).length
      else 0).sum = 44 := by
  decide +kernel

/-- Zero strategy is used only for genuine terminal witnesses, never a residual cover. -/
theorem zero_terminal (s : Shape) (i : State s) (hs : strategy s i = 0) :
    rank s (word s i) = 1 := by
  by_contra hr
  have h := checked s i
  simp [check, hr, coverCheck, hs] at h

/-- A concrete configuration-4 boundary on which the coupled exchange matters. -/
def exampleInput : List Color := [c2, c2, c2, c3, c1, c1, c2, c3]

def exampleGram : Chromogram := [.push, .push, .pop0, .push, .skip, .skip, .pop1, .pop1]

def exampleJointMask : List Bool :=
  List.zipWith xor (KempeChordMasks.ear 6 1) (KempeChordMasks.ear 6 5)

/-- Each separate exchange leaves the ranked set; their joint exchange is terminal. -/
theorem example_checked :
    matchg [] exampleInput exampleGram = true ∧
    KempeChordMasks.paired [] exampleJointMask (KempeChordMasks.skeleton exampleGram) = true ∧
    rank 2 exampleInput = 2 ∧
    rank 2 (KempeChordMasks.recolor (KempeChordMasks.ear 6 1) exampleInput) = 0 ∧
    rank 2 (KempeChordMasks.recolor (KempeChordMasks.ear 6 5) exampleInput) = 0 ∧
    KempeChordMasks.recolor exampleJointMask exampleInput =
      [c3, c3, c3, c3, c1, c1, c2, c2] ∧
    good 2 (KempeChordMasks.recolor exampleJointMask exampleInput) = true := by
  decide +kernel

/-- The shared exterior and the genuine interior witness are simultaneously retained. -/
theorem coupled_example :
    Supports 2 (KempeChordMasks.recolor exampleJointMask exampleInput) ∧
    matchg [] (KempeChordMasks.recolor exampleJointMask exampleInput) exampleGram := by
  exact ⟨good_supports 2 _ example_checked.2.2.2.2.2.2,
    KempeChordMasks.recolor_matches _ _ _ [] [] example_checked.1 example_checked.2.1⟩

/-- The same ranked-answer theorem reconstructs compatible choices for each core. -/
theorem repair (s : Shape) (i : State s) : KempeCoclosure (Supports s) (word s i) :=
  KempeProfileCertificate.sound_of_cover (word s) (rank s) (answers s)
    (fun j => check_sound s j (checked s j)) i

def covered (s : Shape) (et : List Color) : Bool :=
  allEdgePerms.any fun g => (List.finRange (count s)).any fun i => decide (et.map g = word s i)

theorem covered_repair (s : Shape) (et : List Color) (h : covered s et = true) :
    KempeCoclosure (Supports s) et := by
  obtain ⟨g, _, hg⟩ := List.any_eq_true.mp h
  obtain ⟨i, _, hi⟩ := List.any_eq_true.mp hg
  have hi := of_decide_eq_true hi
  exact kempeCoclosure_of_map g (hi ▸ repair s i)

end FourColor.DiamondProfileCertificate
