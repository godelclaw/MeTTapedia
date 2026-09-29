import MettapediaFourColor.DiamondProfile
import MettapediaFourColor.DiamondProfileData
import MettapediaFourColor.KempeProfileCertificate

/-! # One joint-profile certificate for the three diamond cores

The 236 trace representatives use a single rank on 92 joint profile types.
Fifty-one profile types have actual interior colourings; the other 41 descend
through checked Kempe answers. These remain finite certificate obligations.
No original configuration certificate or global Kempe fixed point is used.
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

/-- The rank depends on boundary length and the joint availability profile. -/
def rank (s : Shape) (et : List Color) : ℕ :=
  let profile := key s et
  match (List.range 92).find? (fun i =>
      decide (number (DiamondProfileData.rankCodes i) 0 4 = profile)) with
  | none => 0
  | some i => digit (DiamondProfileData.rankCodes i) 4

def check (s : Shape) (i : State s) : Bool :=
  if rank s (word s i) = 1 then good s (word s i)
  else coversRec (word s i)
      ((answers s i).map fun a => ([], KempeProfileCertificate.answerWord (word s) a)) [] &&
    (answers s i).all fun a => decide (rank s (word s a.1) < rank s (word s i))

theorem check_sound (s : Shape) (i : State s) (h : check s i = true) :
    Supports s (word s i) ∨
      (coversRec (word s i)
        ((answers s i).map fun a => ([], KempeProfileCertificate.answerWord (word s) a)) [] = true ∧
        ∀ a ∈ answers s i, rank s (word s a.1) < rank s (word s i)) := by
  unfold check at h
  split at h
  · exact Or.inl (good_supports s _ h)
  · rw [Bool.and_eq_true] at h
    obtain ⟨hc, ha⟩ := h
    exact Or.inr ⟨hc, fun a hm => of_decide_eq_true ((List.all_eq_true.mp ha) a hm)⟩

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

/-- The same ranked-answer theorem reconstructs compatible choices for each core. -/
theorem repair (s : Shape) (i : State s) : KempeCoclosure (Supports s) (word s i) :=
  KempeProfileCertificate.sound (word s) (rank s) (answers s)
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
