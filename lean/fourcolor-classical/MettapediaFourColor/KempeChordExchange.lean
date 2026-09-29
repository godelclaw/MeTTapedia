import FourColor.Kempe

/-!
# A single-chord answer to an arbitrary exterior chromogram

An exterior chord starting at a chosen boundary edge ends at an edge of the
opposite parity in the cyclic list of non-fixed colours. Swapping both ends
preserves the same chromogram. Thus a repair can answer every exterior by
checking its possible partners, without enumerating chromograms.

The statement has no bound on boundary length. It makes explicit a classical
Kempe-chord argument using the Gonthier/Emery chromogram semantics.
-/

namespace FourColor.KempeChordExchange

open Color

/-- Parity of the number of edges coloured `c2` or `c3`. -/
def activeParity : List Color → Bool
  | [] => false
  | c :: cs => if c.hi then !activeParity cs else activeParity cs

private theorem bottom_exchange : ∀ (w : Chromogram) (et : List Color)
    (lb : List Bool) (b : Bool), matchg (lb ++ [b]) et w →
    ∃ u c v, et = u ++ c :: v ∧ c.hi = true ∧
      activeParity u = lb.parityLen ∧
      matchg (lb ++ [!b]) (u ++ EdgePerm.e132 c :: v) w := by
  intro w
  induction w with
  | nil =>
    intro et lb b h
    cases et <;> simp [matchg] at h
  | cons s w ih =>
    intro et lb b h
    cases et with
    | nil => simp at h
    | cons e et =>
      cases s with
      | push =>
        cases e with
        | c0 => simp [matchg, matchStep] at h
        | c1 => simp [matchg, matchStep] at h
        | c2 =>
          obtain ⟨u, c, v, rfl, hc, hp, hm⟩ :=
            ih et (false :: lb) b (by simpa [matchg, matchStep] using h)
          refine ⟨c2 :: u, c, v, rfl, hc, ?_, ?_⟩
          · simp [activeParity, hp]
          · simpa [matchg, matchStep] using hm
        | c3 =>
          obtain ⟨u, c, v, rfl, hc, hp, hm⟩ :=
            ih et (true :: lb) b (by simpa [matchg, matchStep] using h)
          refine ⟨c3 :: u, c, v, rfl, hc, ?_, ?_⟩
          · simp [activeParity, hp]
          · simpa [matchg, matchStep] using hm
      | skip =>
        cases e with
        | c0 => simp [matchg, matchStep] at h
        | c1 =>
          obtain ⟨u, c, v, rfl, hc, hp, hm⟩ :=
            ih et lb b (by simpa [matchg, matchStep] using h)
          refine ⟨c1 :: u, c, v, rfl, hc, ?_, ?_⟩
          · simpa [activeParity] using hp
          · simpa [matchg, matchStep] using hm
        | c2 => simp [matchg, matchStep] at h
        | c3 => simp [matchg, matchStep] at h
      | pop0 =>
        cases lb with
        | nil =>
          cases e <;> cases b <;> simp [matchg, matchStep] at h
          all_goals
            refine ⟨[], _, et, rfl, rfl, rfl, ?_⟩
            simpa [matchg, matchStep, EdgePerm.apply] using h
        | cons d lb =>
          cases e <;> cases d <;>
            simp only [List.cons_append, matchg_cons, matchStep, Option.elim, Bool.false_eq_true] at h
          all_goals
            obtain ⟨u, c, v, rfl, hc, hp, hm⟩ := ih et lb b h
            refine ⟨_ :: u, c, v, rfl, hc, ?_, ?_⟩
            · simp [activeParity, hp]
            · simpa [matchg, matchStep] using hm
      | pop1 =>
        cases lb with
        | nil =>
          cases e <;> cases b <;> simp [matchg, matchStep] at h
          all_goals
            refine ⟨[], _, et, rfl, rfl, rfl, ?_⟩
            simpa [matchg, matchStep, EdgePerm.apply] using h
        | cons d lb =>
          cases e <;> cases d <;>
            simp only [List.cons_append, matchg_cons, matchStep, Option.elim, Bool.false_eq_true] at h
          all_goals
            obtain ⟨u, c, v, rfl, hc, hp, hm⟩ := ih et lb b h
            refine ⟨_ :: u, c, v, rfl, hc, ?_, ?_⟩
            · simp [activeParity, hp]
            · simpa [matchg, matchStep] using hm

/-- Every first chord has a partner after an even number of active edges. -/
theorem exchange_first (a : Color) (t : List Color) (w : Chromogram)
    (ha : a.hi = true) (h : matchg [] (a :: t) w) :
    ∃ u c v, t = u ++ c :: v ∧ c.hi = true ∧ activeParity u = false ∧
      matchg [] (EdgePerm.e132 a :: (u ++ EdgePerm.e132 c :: v)) w := by
  cases w with
  | nil => simp at h
  | cons s w =>
    cases a <;> cases s <;>
      simp only [Color.hi, matchg, matchStep, Option.elim, Bool.false_eq_true, Bool.true_eq] at ha h
    all_goals
      obtain ⟨u, c, v, ht, hc, hp, hm⟩ := bottom_exchange w t [] _ h
      refine ⟨u, c, v, ht, hc, hp, ?_⟩
      simpa [matchg, matchStep, EdgePerm.apply] using hm

/-- Flip one active edge after a prefix of the prescribed parity. -/
def tailAnswers : Bool → List Color → List (List Color)
  | _, [] => []
  | odd, c :: cs =>
    let rest := (tailAnswers (if c.hi then !odd else odd) cs).map (c :: ·)
    if c.hi && !odd then (EdgePerm.e132 c :: cs) :: rest else rest

theorem tailAnswer_mem (u : List Color) (c : Color) (v : List Color)
    (hc : c.hi = true) :
    u ++ EdgePerm.e132 c :: v ∈ tailAnswers (activeParity u) (u ++ c :: v) := by
  induction u with
  | nil => simp [activeParity, tailAnswers, hc]
  | cons e u ih =>
    have hnext : (if e.hi then !activeParity (e :: u) else activeParity (e :: u)) =
        activeParity u := by cases he : e.hi <;> simp [activeParity, he]
    have hm := List.mem_map_of_mem (f := (e :: ·)) ih
    simp only [List.cons_append, tailAnswers, hnext]
    split
    · exact List.mem_cons_of_mem _ hm
    · exact hm

/-- The possible answers obtained by exchanging the first chord's two ends. -/
def firstAnswers : List Color → List (List Color)
  | [] => []
  | a :: t => if a.hi then (tailAnswers false t).map (EdgePerm.e132 a :: ·) else []

theorem firstAnswer_exists (et : List Color) (w : Chromogram)
    (ha : (et.headD 0).hi = true) (h : matchg [] et w) :
    ∃ answer ∈ firstAnswers et, matchg [] answer w := by
  cases et with
  | nil => simp at ha
  | cons a t =>
    obtain ⟨u, c, v, rfl, hc, hp, hm⟩ := exchange_first a t w ha h
    have ht := tailAnswer_mem u c v hc
    rw [hp] at ht
    refine ⟨_, ?_, hm⟩
    simpa only [firstAnswers, show a.hi = true from ha, Bool.true_eq, ↓reduceIte] using
      List.mem_map_of_mem (f := (EdgePerm.e132 a :: ·)) ht

private def rotateGram : ℕ → Chromogram → Chromogram
  | 0, w => w
  | n + 1, w => gramRot (rotateGram n w)

private theorem match_rotateGram (et : List Color) (n : ℕ) (w : Chromogram) :
    matchg [] (et.rotate n) (rotateGram n w) = matchg [] et w := by
  induction n with
  | zero => simp [rotateGram]
  | succ n ih =>
    rw [← List.rotate_rotate, rotateGram, matchg_gramRot, ih]

/-- Rotate only for choosing the chord; answers return to the original port order. -/
def answers (et : List Color) (anchor : ℕ) : List (List Color) :=
  (firstAnswers (et.rotate anchor)).map fun t => t.rotate (et.length - anchor)

/-- A uniform cover, valid for every boundary length and every matching exterior. -/
theorem answer_exists (et : List Color) (anchor : ℕ) (w : Chromogram)
    (ha : anchor ≤ et.length) (hh : ((et.rotate anchor).headD 0).hi = true)
    (h : matchg [] et w) :
    ∃ answer ∈ answers et anchor, matchg [] answer w := by
  have hr : matchg [] (et.rotate anchor) (rotateGram anchor w) := by
    rwa [match_rotateGram]
  obtain ⟨t, ht, hm⟩ := firstAnswer_exists _ _ hh hr
  have hlen : t.length = et.length := by
    have h₁ := matchg_length t [] (rotateGram anchor w) hm
    have h₂ := matchg_length (et.rotate anchor) [] (rotateGram anchor w) hr
    simpa using h₁.symm.trans h₂
  have hinv : (t.rotate (et.length - anchor)).rotate anchor = t := by
    rw [List.rotate_rotate, Nat.sub_add_cancel ha, ← hlen, List.rotate_length]
  refine ⟨t.rotate (et.length - anchor), List.mem_map_of_mem ht, ?_⟩
  rw [← match_rotateGram _ anchor w, hinv]
  exact hm

end FourColor.KempeChordExchange
