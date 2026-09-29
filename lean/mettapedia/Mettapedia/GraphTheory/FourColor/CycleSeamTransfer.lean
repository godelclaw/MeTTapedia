import Mettapedia.GraphTheory.FourColor.BoundaryWordFrontier

/-!
# Cycle contraction with a retained seam colour

Merging two adjacent boundary letters erases one internal cycle edge. Its
colour must remain nonzero when reconstructing the longer cycle. Retaining
the colour at the marked seam records exactly this additional condition.
The statements concern literal cycle tangles and their colouring witnesses;
an exterior operation and a strict reduction of a closed map are separate.
-/

namespace Mettapedia.GraphTheory.FourColor.CycleSeamTransfer

open GoertzelV24OpenTangleComposition CycleCap

set_option backward.isDefEq.respectTransparency false

variable {k : ℕ} [NeZero k]

/-- Read the cycle edges of an actual tangle colouring. -/
def edges (c : AllDart k → Color) (i : Fin k) : Color := c (.inl (i, false))

theorem edges_valid (hk : 2 ≤ k) {c : AllDart k → Color}
    (hc : (cap k hk).IsTaitColoring c) : Valid k (edges c) := by
  refine ⟨fun i => hc.2.2 _, ?_⟩
  intro i
  have hm := hc.1 (i + 1, true)
  change c (.inl (i + 1, false)) = c (.inl (i + 1, true)) at hm
  rw [edges, edges, hm]
  apply hc.2.1
  · simp [TwoSidedOpenTangleData.vertOf, cap, twoSidedOpenTangleVertOf, interiorVert]
  · simp

theorem spokes_edges (hk : 2 ≤ k) {c : AllDart k → Color}
    (hc : (cap k hk).IsTaitColoring c) :
    spokes k (edges c) = (cap k hk).rightBoundaryColor c := by
  funext i
  have hm := hc.1 (i + 1, true)
  change c (.inl (i + 1, false)) = c (.inl (i + 1, true)) at hm
  change edges c i + edges c (i + 1) = c (.inr (.inr i))
  rw [edges, edges, hm]
  apply Eq.symm
  apply ZigzagRing.third_eq_add (hc.2.2 _) (hc.2.2 _) (hc.2.2 _)
  all_goals apply hc.2.1
  all_goals simp [TwoSidedOpenTangleData.vertOf, cap, twoSidedOpenTangleVertOf, interiorVert]

/-- Mark an actual internal edge, in addition to the boundary word. -/
def Marked (hk : 2 ≤ k) (word : Fin k → Color) (seam : Color) : Prop :=
  ∃ c, (cap k hk).IsTaitColoring c ∧
    (cap k hk).rightBoundaryColor c = word ∧ c (.inl (0, false)) = seam

theorem marked_iff (hk : 2 ≤ k) (word : Fin k → Color) (seam : Color) :
    Marked hk word seam ↔
      ∃ a : Fin k → Color, Valid k a ∧ spokes k a = word ∧ a 0 = seam := by
  constructor
  · rintro ⟨c, hc, hw, hs⟩
    exact ⟨edges c, edges_valid hk hc, (spokes_edges hk hc).trans hw, hs⟩
  · rintro ⟨a, ha, hw, hs⟩
    exact ⟨coloringOf k a, coloringOf_isTait k hk ha, hw, hs⟩

theorem accepts_iff_marked (hk : 2 ≤ k) (word : Fin k → Color) :
    (cap k hk).AcceptsBoundaryWords Empty.elim word ↔ ∃ seam, Marked hk word seam := by
  constructor
  · rintro ⟨c, hc, _, hw⟩
    exact ⟨c (.inl (0, false)), c, hc, hw, rfl⟩
  · rintro ⟨s, c, hc, hw, _⟩
    exact ⟨c, hc, funext (fun e => e.elim), hw⟩

variable (n : ℕ)

/-- Retained edge indices when edge one is removed. -/
def skip (i : Fin (n + 1)) : Fin (n + 2) :=
  if h : i.val = 0 then 0 else ⟨i.val + 1, by have := i.isLt; omega⟩

@[simp] theorem skip_zero : skip n 0 = 0 := by simp [skip]
@[simp] theorem skip_succ (i : Fin n) : skip n i.succ = i.succ.succ := by
  apply Fin.ext
  simp [skip]

theorem skip_next (hn : 1 ≤ n) (i : Fin (n + 1)) (hi : i ≠ 0) :
    skip n (i + 1) = skip n i + 1 := by
  have hiv : 0 < i.val := by
    by_contra h
    apply hi
    apply Fin.ext
    simp only [Fin.val_zero]
    omega
  have hone : 1 % (n + 1) = 1 := Nat.mod_eq_of_lt (by omega)
  have hone' : 1 % (n + 2) = 1 := Nat.mod_eq_of_lt (by omega)
  by_cases hlast : i.val + 1 = n + 1
  · have he : i + 1 = (0 : Fin (n + 1)) := by
      apply Fin.ext
      simp [Fin.val_add, hone, hlast]
    rw [he, skip_zero]
    apply Fin.ext
    simp [skip, show i.val ≠ 0 by omega, Fin.val_add, hone',
      show i.val + 1 + 1 = n + 2 by omega]
  · have hlt : i.val + 1 < n + 1 := by have := i.isLt; omega
    apply Fin.ext
    simp [skip, Fin.val_add, hone, hone', Nat.mod_eq_of_lt hlt,
      show i.val ≠ 0 by omega,
      Nat.mod_eq_of_lt (show i.val + 1 + 1 < n + 2 by omega)]

def collapse (a : Fin (n + 2) → Color) : Fin (n + 1) → Color := a ∘ skip n

/-- Insert the erased edge with its reconstructed colour. -/
def insert (a : Fin (n + 1) → Color) (middle : Color) : Fin (n + 2) → Color :=
  Fin.cons (a 0) (Fin.cons middle (fun i => a i.succ))

@[simp] theorem insert_zero (a : Fin (n + 1) → Color) (middle : Color) :
    insert n a middle 0 = a 0 := rfl

@[simp] theorem insert_one (a : Fin (n + 1) → Color) (middle : Color) :
    insert n a middle 1 = middle := by simp [insert]

@[simp] theorem insert_skip (a : Fin (n + 1) → Color) (middle : Color)
    (i : Fin (n + 1)) : insert n a middle (skip n i) = a i := by
  refine Fin.cases ?_ (fun j => ?_) i <;> simp [insert]

theorem skip_cases (j : Fin (n + 2)) : j = 1 ∨ ∃ i, skip n i = j := by
  refine Fin.cases ?_ (fun i => ?_) j
  · exact Or.inr ⟨0, skip_zero n⟩
  · refine Fin.cases ?_ (fun h => ?_) i
    · exact Or.inl (by simp)
    · exact Or.inr ⟨h.succ, skip_succ n h⟩

theorem skip_one (hn : 1 ≤ n) : skip n 1 = 2 := by
  apply Fin.ext
  simp [skip, Nat.mod_eq_of_lt (show 1 < n + 1 by omega),
    Nat.mod_eq_of_lt (show 2 < n + 2 by omega)]

private theorem fin_one_add_one : (1 : Fin (n + 2)) + 1 = 2 := by
  apply Fin.ext
  change (1 % (n + 2) + 1 % (n + 2)) % (n + 2) = 2 % (n + 2)
  rw [Nat.mod_eq_of_lt (show 1 < n + 2 by omega)]

@[simp] theorem insert_two (hn : 1 ≤ n) (a : Fin (n + 1) → Color) (middle : Color) :
    insert n a middle 2 = a 1 := by
  rw [← skip_one n hn, insert_skip]

/-- Deleting an edge adds precisely its two adjacent boundary letters. -/
theorem spokes_collapse (hn : 1 ≤ n) (a : Fin (n + 2) → Color) :
    spokes (n + 1) (collapse n a) = BoundaryWordFrontier.contract n (spokes (n + 2) a) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp only [spokes, collapse, Function.comp_apply, zero_add, skip_zero,
      skip_one n hn, BoundaryWordFrontier.contract, Fin.cons_zero]
    rw [fin_one_add_one]
    have h := color_add_self (a 1)
    linear_combination -h
  · have hnext := skip_next n hn j.succ (by simp)
    simpa [spokes, collapse, BoundaryWordFrontier.contract] using
      congrArg (fun x => a (skip n j.succ) + a x) hnext

/-- Inserting one edge retains all other boundary letters. -/
theorem spokes_insert (hn : 1 ≤ n) (a : Fin (n + 1) → Color) (middle : Color) :
    spokes (n + 2) (insert n a middle) =
      BoundaryWordFrontier.expand n (spokes (n + 1) a) (a 0 + middle) (middle + a 1) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [spokes, BoundaryWordFrontier.expand]
  · refine Fin.cases ?_ (fun j => ?_) j
    · simpa [spokes, BoundaryWordFrontier.expand, fin_one_add_one] using
        congrArg (fun x => middle + x) (insert_two n hn a middle)
    · have hnext := skip_next n hn j.succ (by simp)
      rw [← skip_succ n j]
      simp only [spokes, ← hnext, insert_skip]
      simp [BoundaryWordFrontier.expand, spokes]

theorem valid_iff_nonzero_edges_spokes (a : Fin k → Color) :
    Valid k a ↔ (∀ i, a i ≠ 0) ∧ ∀ i, spokes k a i ≠ 0 := by
  simp only [Valid, spokes, ne_eq, add_eq_zero_iff_eq]

theorem collapse_valid (hn : 1 ≤ n) {a : Fin (n + 2) → Color}
    (ha : Valid (n + 2) a) (hne : spokes (n + 2) a 0 ≠ spokes (n + 2) a 1) :
    Valid (n + 1) (collapse n a) := by
  rw [valid_iff_nonzero_edges_spokes, spokes_collapse n hn]
  refine ⟨fun i => ha.1 _, ?_⟩
  intro i
  refine Fin.cases (add_ne_zero_of_ne hne) (fun j => ?_) i
  exact add_ne_zero_of_ne (ha.2 j.succ.succ)

/-- The missing edge colour is forced by the seam and the first port. -/
theorem reconstruct_spokes (hn : 1 ≤ n) {a : Fin (n + 1) → Color}
    {word : Fin (n + 2) → Color}
    (hword : spokes (n + 1) a = BoundaryWordFrontier.contract n word) :
    spokes (n + 2) (insert n a (a 0 + word 0)) = word := by
  have hfirst : a 0 + (a 0 + word 0) = word 0 := by
    rw [← add_assoc, color_add_self, zero_add]
  have hsum : a 0 + a 1 = word 0 + word 1 := by
    simpa [spokes, BoundaryWordFrontier.contract] using congrFun hword 0
  have hsecond : a 0 + word 0 + a 1 = word 1 := by
    calc
      a 0 + word 0 + a 1 = (a 0 + a 1) + word 0 := by abel
      _ = (word 0 + word 1) + word 0 := by rw [hsum]
      _ = (word 0 + word 0) + word 1 := by abel
      _ = word 1 := by rw [color_add_self, zero_add]
  rw [spokes_insert n hn, hfirst, hsecond, hword, BoundaryWordFrontier.expand_contract]

theorem reconstruct_valid (hn : 1 ≤ n) {a : Fin (n + 1) → Color}
    {word : Fin (n + 2) → Color} (ha : Valid (n + 1) a)
    (hword : spokes (n + 1) a = BoundaryWordFrontier.contract n word)
    (hw : ∀ i, word i ≠ 0) (hseam : a 0 ≠ word 0) :
    Valid (n + 2) (insert n a (a 0 + word 0)) := by
  rw [valid_iff_nonzero_edges_spokes, reconstruct_spokes n hn hword]
  refine ⟨?_, hw⟩
  intro i
  rcases skip_cases n i with rfl | ⟨j, rfl⟩
  · simpa using add_ne_zero_of_ne hseam
  · simpa using ha.1 j

/-- Exact witness reconstruction for all cycle lengths. The seam guard is
essential: the erased edge must receive a nonzero colour. -/
theorem marked_contract_iff (hn : 1 ≤ n) (word : Fin (n + 2) → Color)
    (hw : ∀ i, word i ≠ 0) (hne : word 0 ≠ word 1) (seam : Color) :
    Marked (by omega : 2 ≤ n + 2) word seam ↔
      seam ≠ word 0 ∧ Marked (by omega : 2 ≤ n + 1)
        (BoundaryWordFrontier.contract n word) seam := by
  rw [marked_iff, marked_iff]
  constructor
  · rintro ⟨a, ha, hword, hs⟩
    have hs0 : a 0 ≠ word 0 := by
      rw [← hword]
      exact (add_ne_left_of_ne_zero (ha.1 (0 + 1))).symm
    refine ⟨hs ▸ hs0, collapse n a, collapse_valid n hn ha ?_, ?_, ?_⟩
    · simpa [hword] using hne
    · rw [spokes_collapse n hn, hword]
    · simpa [collapse] using hs
  · rintro ⟨hs, a, ha, hword, hseam⟩
    refine ⟨insert n a (a 0 + word 0),
      reconstruct_valid n hn ha hword hw ?_, reconstruct_spokes n hn hword, ?_⟩
    · simpa [hseam] using hs
    · simpa using hseam

/-- Any exterior test of the retained seam can be composed with the same
contraction and reconstruction. -/
theorem marked_contract_in_context (hn : 1 ≤ n) (word : Fin (n + 2) → Color)
    (hw : ∀ i, word i ≠ 0) (hne : word 0 ≠ word 1) (outside : Color → Prop) :
    (∃ seam, Marked (by omega : 2 ≤ n + 2) word seam ∧ outside seam) ↔
      ∃ seam, Marked (by omega : 2 ≤ n + 1) (BoundaryWordFrontier.contract n word) seam ∧
        seam ≠ word 0 ∧ outside seam := by
  simp only [marked_contract_iff n hn word hw hne]
  constructor <;> rintro ⟨s, hs, ht⟩
  · exact ⟨s, hs.2, hs.1, ht⟩
  · exact ⟨s, ⟨ht.1, hs⟩, ht.2⟩

/-- Forgetting the seam admits a contracted word with no longer-cycle lift. -/
def blockedWord : Fin 4 → Color := ![red, blue, red, blue]

theorem blockedWord_no_edges :
    ¬ ∃ a : Fin 4 → Color, Valid 4 a ∧ spokes 4 a = blockedWord := by
  unfold Valid spokes blockedWord
  decide +kernel

theorem blockedWord_not_accepted :
    ¬ (cap 4 (by decide)).AcceptsBoundaryWords Empty.elim blockedWord := by
  rw [accepts_iff_marked]
  rintro ⟨s, hs⟩
  obtain ⟨a, ha, hw, _⟩ := (marked_iff _ _ _).1 hs
  exact blockedWord_no_edges ⟨a, ha, hw⟩

theorem blockedWord_contraction_accepted :
    (cap 3 (by decide)).AcceptsBoundaryWords Empty.elim
      (BoundaryWordFrontier.contract 2 blockedWord) := by
  rw [accepts_iff_marked]
  refine ⟨red, (marked_iff _ _ _).2 ⟨![red, blue, purple], ?_⟩⟩
  unfold Valid spokes BoundaryWordFrontier.contract blockedWord
  decide +kernel

/-- Exact acceptance after contraction quantifies over successful marked
choices; it does not require every smaller colouring to reconstruct. -/
theorem accepts_contract_iff (hn : 1 ≤ n) (word : Fin (n + 2) → Color)
    (hw : ∀ i, word i ≠ 0) (hne : word 0 ≠ word 1) :
    (cap (n + 2) (by omega)).AcceptsBoundaryWords Empty.elim word ↔
      ∃ seam, seam ≠ word 0 ∧ Marked (by omega : 2 ≤ n + 1)
        (BoundaryWordFrontier.contract n word) seam := by
  rw [accepts_iff_marked]
  simp only [marked_contract_iff n hn word hw hne]

end Mettapedia.GraphTheory.FourColor.CycleSeamTransfer
