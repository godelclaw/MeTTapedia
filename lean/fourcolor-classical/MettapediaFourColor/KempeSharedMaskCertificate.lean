import MettapediaFourColor.KempeMaskCertificate

/-!
# Sharing a recolouring action across exterior pairings

An action is checked once for its actual answer trace and decreasing rank.
Each unsigned exterior skeleton then selects a checked action and verifies
that its mask consists of complete chords of that skeleton. The original
signed exterior is retained. Sharing an action does not identify exteriors
or replace their joint relation by separate port possibilities.
-/
namespace FourColor.KempeSharedMaskCertificate

open KempeChordMasks KempeProfileCertificate

variable {I : Type*}

abbrev Action (I : Type*) := (I × EdgePerm) × List Bool

def answers (actions : I → List (Action I)) (i : I) : List (I × EdgePerm) :=
  (actions i).map Prod.fst

def check (word : I → List Color) (rank : I → ℕ)
    (actions : I → List (Action I)) (select : I → ℕ → ℕ) (i : I) : Bool :=
  (actions i).all (fun (a, mask) =>
    decide (answerWord word a = recolor mask (word i)) &&
      decide (rank a.1 < rank i)) &&
  (KempeMaskCertificate.entries (active (word i)).length).all fun (ds, j) =>
    ((actions i)[select i j]?).any fun a => paired [] a.2 ds

/-- Coverage reuses action validity while checking every exterior's coupling. -/
theorem check_sound (word : I → List Color) (rank : I → ℕ)
    (actions : I → List (Action I)) (select : I → ℕ → ℕ) (i : I)
    (h : check word rank actions select i = true) :
    (∀ gram, matchg [] (word i) gram →
      ∃ a ∈ answers actions i, matchg [] (answerWord word a) gram) ∧
    ∀ a ∈ answers actions i, rank a.1 < rank i := by
  rw [check, Bool.and_eq_true] at h
  have valid := List.all_eq_true.mp h.1
  have cover := List.all_eq_true.mp h.2
  constructor
  · intro gram hm
    obtain ⟨hb, hl⟩ := matched_skeleton gram (word i) [] hm
    obtain ⟨j, hj⟩ := KempeMaskCertificate.entries_complete (skeleton gram) hb
    rw [hl] at hj
    have hc := cover _ hj
    obtain ⟨⟨a, mask⟩, ha, hp⟩ := (Option.any_eq_true _ _).mp hc
    have hmem : (a, mask) ∈ actions i := List.mem_iff_getElem?.mpr ⟨select i j, ha⟩
    have hv := valid _ hmem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    refine ⟨a, List.mem_map.mpr ⟨(a, mask), hmem, rfl⟩, ?_⟩
    rw [hv.1]
    exact recolor_matches gram (word i) mask [] [] hm hp
  · intro a ha
    obtain ⟨⟨a, mask⟩, hmem, rfl⟩ := List.mem_map.mp ha
    have hv := valid _ hmem
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.2

end FourColor.KempeSharedMaskCertificate
