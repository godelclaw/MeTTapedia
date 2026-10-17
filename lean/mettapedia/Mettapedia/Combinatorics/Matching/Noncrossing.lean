import Mathlib.Combinatorics.Enumerative.Catalan.Basic
import Mettapedia.Combinatorics.Matching.Pairing

/-!
# Noncrossing perfect matchings

Points of a linear order are joined in pairs by chords drawn on one side of a line.  Two
chords `{a, c}` and `{b, d}` cross when their endpoints interleave, `a < b < c < d`.  For a
matching given by its partner function `f`, an involution, this means `a < b < f a < f b`;
`IsNoncrossing f` forbids it.  For involutions this is the same as forbidding interleaved
chords in either orientation (`isNoncrossing_iff_forall_not_chordsCross`), and the orbit
partition of an involution is a noncrossing partition exactly when the involution is
noncrossing in this sense
(`Mettapedia.ProbabilityTheory.FreeProbability.orbitPartition_isNoncrossing_iff`).

`noncrossingMatchings ps` lists the noncrossing perfect matchings of a strictly increasing
list of points as lists of pairs: the first point is paired with a point at even distance,
the points in between are matched among themselves, and the points after are matched
independently.  The enumeration is

* sound (`isNoncrossingMatchingOn_mate`, with the projections `involutive_mate` and
  `isNoncrossing_mate`): each entry's partner function is a noncrossing fixed-point-free
  involution on the points, the identity elsewhere (`IsNoncrossingMatchingOn`);
* complete (`exists_mem_noncrossingMatchings`): every noncrossing involution without
  fixed points on the points agrees on them with an entry;
* without repetition (`nodup_noncrossingMatchings`, `eq_of_mate_eq`);

and its length is a Catalan number (`length_noncrossingMatchings`).  Consequently the
noncrossing perfect matchings of a finite linear order with `2 * n` points number
`catalan n` (`card_noncrossing_pairing`).
-/

namespace NoncrossingMatching

open Function

variable {α : Type*}

section Order

variable [LinearOrder α]

/-- The partner function `f` draws no two chords `{a, f a}` and `{b, f b}` with
interleaved endpoints `a < b < f a < f b`. -/
def IsNoncrossing (f : α → α) : Prop :=
  ∀ a b, a < b → b < f a → f a < f b → False

instance [Fintype α] (f : α → α) : Decidable (IsNoncrossing f) := by
  unfold IsNoncrossing
  infer_instance

/-- The chords `{a, b}` and `{c, d}` cross: their endpoints strictly interleave. -/
def ChordsCross (a b c d : α) : Prop :=
  min a b < min c d ∧ min c d < max a b ∧ max a b < max c d ∨
    min c d < min a b ∧ min a b < max c d ∧ max c d < max a b

theorem chordsCross_comm {a b c d : α} : ChordsCross a b c d ↔ ChordsCross c d a b :=
  Or.comm

/-- For an involution, noncrossing is the absence of interleaved chords in either
orientation. -/
theorem isNoncrossing_iff_forall_not_chordsCross {f : α → α} (hf : Involutive f) :
    IsNoncrossing f ↔ ∀ x y, ¬ ChordsCross x (f x) y (f y) := by
  have hmin : ∀ z, f (min z (f z)) = max z (f z) := by
    intro z
    rcases le_total z (f z) with hz | hz
    · rw [min_eq_left hz, max_eq_right hz]
    · rw [min_eq_right hz, max_eq_left hz, hf z]
  constructor
  · intro h x y hc
    have key : ∀ x y, min x (f x) < min y (f y) → min y (f y) < max x (f x) →
        max x (f x) < max y (f y) → False := fun x y h₁ h₂ h₃ =>
      h _ _ h₁ (by rw [hmin]; exact h₂) (by rw [hmin, hmin]; exact h₃)
    rcases hc with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
    · exact key x y h₁ h₂ h₃
    · exact key y x h₁ h₂ h₃
  · intro h a b hab hbfa hfafb
    have ha : a < f a := hab.trans hbfa
    have hb : b < f b := hbfa.trans hfafb
    refine h a b (Or.inl ?_)
    rw [min_eq_left ha.le, max_eq_right ha.le, min_eq_left hb.le, max_eq_right hb.le]
    exact ⟨hab, hbfa, hfafb⟩

end Order

/-! ### The partner function of a list of pairs -/

section Points

/-- The points named by a list of pairs. -/
def points : List (α × α) → List α
  | [] => []
  | e :: es => e.1 :: e.2 :: points es

@[simp] theorem points_nil : points ([] : List (α × α)) = [] := rfl

@[simp] theorem points_cons (e : α × α) (es : List (α × α)) :
    points (e :: es) = e.1 :: e.2 :: points es := rfl

@[simp] theorem points_append (p q : List (α × α)) : points (p ++ q) = points p ++ points q := by
  induction p with
  | nil => rfl
  | cons e es ih => simp [ih]

theorem length_points (p : List (α × α)) : (points p).length = 2 * p.length := by
  induction p with
  | nil => rfl
  | cons e es ih => simp [ih]; ring

end Points

section Mate

variable [DecidableEq α]

/-- The partner function of a list of pairs: the first pair containing `x` names its
partner, and points in no pair are fixed. -/
def mate : List (α × α) → α → α
  | [], x => x
  | e :: es, x => if x = e.1 then e.2 else if x = e.2 then e.1 else mate es x

@[simp] theorem mate_nil (x : α) : mate [] x = x := rfl

theorem mate_cons_fst (a b : α) (es : List (α × α)) : mate ((a, b) :: es) a = b := by
  simp [mate]

theorem mate_cons_snd {a b : α} (hab : a ≠ b) (es : List (α × α)) :
    mate ((a, b) :: es) b = a := by
  simp [mate, hab.symm]

theorem mate_cons_of_ne {a b x : α} (ha : x ≠ a) (hb : x ≠ b) (es : List (α × α)) :
    mate ((a, b) :: es) x = mate es x := by
  simp [mate, ha, hb]

theorem mate_eq_self_of_notMem {p : List (α × α)} {x : α} (hx : x ∉ points p) :
    mate p x = x := by
  induction p with
  | nil => rfl
  | cons e es ih =>
      simp only [points_cons, List.mem_cons, not_or] at hx
      simp [mate, hx.1, hx.2.1, ih hx.2.2]

theorem mem_points_of_mate_ne {p : List (α × α)} {x : α} (hx : mate p x ≠ x) :
    x ∈ points p := by
  by_contra h
  exact hx (mate_eq_self_of_notMem h)

theorem mate_append_of_mem {p q : List (α × α)} {x : α} (hx : x ∈ points p) :
    mate (p ++ q) x = mate p x := by
  induction p with
  | nil => simp at hx
  | cons e es ih =>
      simp only [points_cons, List.mem_cons] at hx
      simp only [List.cons_append, mate]
      split_ifs with h₁ h₂
      · rfl
      · rfl
      · exact ih (hx.resolve_left h₁ |>.resolve_left h₂)

theorem mate_append_of_notMem {p q : List (α × α)} {x : α} (hx : x ∉ points p) :
    mate (p ++ q) x = mate q x := by
  induction p with
  | nil => rfl
  | cons e es ih =>
      simp only [points_cons, List.mem_cons, not_or] at hx
      simp [mate, hx.1, hx.2.1, ih hx.2.2]

end Mate

/-! ### The enumeration -/

section Enumeration

/-- Implementation of `noncrossingMatchings`, by recursion on an upper bound for the
number of points. -/
def matchingsAux : ℕ → List α → List (List (α × α))
  | _, [] => [[]]
  | 0, _ :: _ => []
  | n + 1, a :: rest =>
      (List.finRange rest.length).flatMap fun (m : Fin rest.length) =>
        if (m : ℕ) % 2 = 0 then
          (matchingsAux n (rest.take m)).flatMap fun inside =>
            (matchingsAux n (rest.drop (m + 1))).map fun outside =>
              (a, rest[m]) :: (inside ++ outside)
        else []

/-- The noncrossing perfect matchings of a list of points, listed as lists of pairs: the
first point is paired with a point at even distance, the points in between are matched
among themselves, and the points after are matched independently.  Intended for strictly
increasing lists. -/
def noncrossingMatchings (ps : List α) : List (List (α × α)) :=
  matchingsAux ps.length ps

theorem matchingsAux_eq (n : ℕ) (ps : List α) (h : ps.length ≤ n) :
    matchingsAux n ps = noncrossingMatchings ps := by
  induction n using Nat.strong_induction_on generalizing ps with
  | _ n ih =>
    cases ps with
    | nil => cases n <;> rfl
    | cons a rest =>
      obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by simp at h; omega⟩
      have hk : rest.length ≤ k := by simpa using h
      rw [noncrossingMatchings, List.length_cons, matchingsAux, matchingsAux]
      refine List.flatMap_congr fun m _ => ?_
      have htake : (rest.take m).length ≤ rest.length := List.length_take_le' _ _
      have hdrop : (rest.drop (m + 1)).length ≤ rest.length := by simp
      rw [ih k (by omega) _ (htake.trans hk), ih k (by omega) _ (hdrop.trans hk),
        ih rest.length (by omega) _ htake, ih rest.length (by omega) _ hdrop]

@[simp] theorem noncrossingMatchings_nil :
    noncrossingMatchings ([] : List α) = [[]] := rfl

theorem noncrossingMatchings_cons (a : α) (rest : List α) :
    noncrossingMatchings (a :: rest) =
      (List.finRange rest.length).flatMap fun (m : Fin rest.length) =>
        if (m : ℕ) % 2 = 0 then
          (noncrossingMatchings (rest.take m)).flatMap fun inside =>
            (noncrossingMatchings (rest.drop (m + 1))).map fun outside =>
              (a, rest[m]) :: (inside ++ outside)
        else [] := by
  rw [noncrossingMatchings, List.length_cons, matchingsAux]
  refine List.flatMap_congr fun m _ => ?_
  rw [matchingsAux_eq _ _ (List.length_take_le' _ _),
    matchingsAux_eq _ _ (by simp)]

theorem mem_noncrossingMatchings_cons {a : α} {rest : List α} {p : List (α × α)} :
    p ∈ noncrossingMatchings (a :: rest) ↔
      ∃ m : Fin rest.length, (m : ℕ) % 2 = 0 ∧
        ∃ inside ∈ noncrossingMatchings (rest.take m),
          ∃ outside ∈ noncrossingMatchings (rest.drop (m + 1)),
            p = (a, rest[m]) :: (inside ++ outside) := by
  rw [noncrossingMatchings_cons, List.mem_flatMap]
  constructor
  · rintro ⟨m, -, hm⟩
    split_ifs at hm with heven
    · simp only [List.mem_flatMap, List.mem_map] at hm
      obtain ⟨inside, hin, outside, hout, rfl⟩ := hm
      exact ⟨m, heven, inside, hin, outside, hout, rfl⟩
    · simp at hm
  · rintro ⟨m, heven, inside, hin, outside, hout, rfl⟩
    refine ⟨m, List.mem_finRange m, ?_⟩
    rw [if_pos heven]
    simp only [List.mem_flatMap, List.mem_map]
    exact ⟨inside, hin, outside, hout, rfl⟩

/-- Induction along the recursion of `noncrossingMatchings`. -/
@[elab_as_elim]
theorem induction_mem
    {P : ∀ (ps : List α) (p : List (α × α)), p ∈ noncrossingMatchings ps → Prop}
    (nil : P [] [] (by simp))
    (cons : ∀ (a : α) (rest : List α) (m : Fin rest.length) (heven : (m : ℕ) % 2 = 0)
      (inside : List (α × α)) (hin : inside ∈ noncrossingMatchings (rest.take m))
      (outside : List (α × α)) (hout : outside ∈ noncrossingMatchings (rest.drop (m + 1))),
        P _ _ hin → P _ _ hout →
          P (a :: rest) ((a, rest[m]) :: (inside ++ outside))
            (mem_noncrossingMatchings_cons.mpr ⟨m, heven, inside, hin, outside, hout, rfl⟩))
    {ps : List α} {p : List (α × α)} (hp : p ∈ noncrossingMatchings ps) : P ps p hp := by
  induction h : ps.length using Nat.strong_induction_on generalizing ps p with
  | _ n ih =>
    cases ps with
    | nil =>
        rw [noncrossingMatchings_nil, List.mem_singleton] at hp
        subst hp
        exact nil
    | cons a rest =>
        obtain ⟨m, heven, inside, hin, outside, hout, rfl⟩ := mem_noncrossingMatchings_cons.mp hp
        have hlen : rest.length < n := by simp [← h]
        exact cons a rest m heven inside hin outside hout
          (ih _ (lt_of_le_of_lt (List.length_take_le' _ _) hlen) hin rfl)
          (ih _ (lt_of_le_of_lt (by simp) hlen) hout rfl)

/-- Every entry pairs off all the points: twice its number of pairs is the number of
points. -/
theorem two_mul_length_of_mem {ps : List α} {p : List (α × α)}
    (hp : p ∈ noncrossingMatchings ps) : 2 * p.length = ps.length := by
  induction hp using induction_mem with
  | nil => rfl
  | cons a rest m _ inside _ outside _ hin hout =>
      have hm := m.isLt
      simp only [List.length_cons, List.length_append, List.length_take, List.length_drop] at *
      omega

/-- The points named by an entry are exactly the given points. -/
theorem mem_points_iff_of_mem {ps : List α} {p : List (α × α)}
    (hp : p ∈ noncrossingMatchings ps) {x : α} : x ∈ points p ↔ x ∈ ps := by
  induction hp using induction_mem generalizing x with
  | nil => simp
  | cons a rest m _ inside _ outside _ hin hout =>
      have hsplit : rest = rest.take m ++ rest[m] :: rest.drop (m + 1) := by
        conv_lhs => rw [← List.take_append_drop m rest, List.drop_eq_getElem_cons m.isLt]
        rfl
      conv_rhs => rw [hsplit]
      simp only [points_cons, points_append, List.mem_cons, List.mem_append, hin, hout]
      tauto

end Enumeration

/-! ### Soundness and completeness -/

section Correctness

variable [LinearOrder α]

/-- A noncrossing perfect matching of the set `s`, given by its partner function: an
involution without fixed points on `s`, the identity elsewhere, drawing no crossing
chords. -/
structure IsNoncrossingMatchingOn (s : Set α) (f : α → α) : Prop where
  involutive : Involutive f
  ne : ∀ x ∈ s, f x ≠ x
  eq_self : ∀ x ∉ s, f x = x
  noncrossing : IsNoncrossing f

theorem IsNoncrossingMatchingOn.mem {s : Set α} {f : α → α} (h : IsNoncrossingMatchingOn s f)
    {x : α} (hx : x ∈ s) : f x ∈ s := by
  by_contra hfx
  have := h.eq_self _ hfx
  rw [h.involutive x] at this
  exact h.ne x hx this.symm

/-- The order facts behind the recursion: splitting off the first point and its partner
at position `m` leaves the points in between and the points after. -/
private theorem split_facts {a : α} {rest : List α} (h : (a :: rest).Pairwise (· < ·))
    (m : Fin rest.length) :
    rest = rest.take m ++ rest[m] :: rest.drop (m + 1) ∧ a < rest[m] ∧
      (∀ x ∈ rest.take m, a < x ∧ x < rest[m]) ∧ (∀ y ∈ rest.drop (m + 1), rest[m] < y) ∧
      (rest.take m).Pairwise (· < ·) ∧ (rest.drop (m + 1)).Pairwise (· < ·) := by
  obtain ⟨hlt, hrest⟩ := List.pairwise_cons.mp h
  have hsplit : rest = rest.take m ++ rest[m] :: rest.drop (m + 1) := by
    conv_lhs => rw [← List.take_append_drop m rest, List.drop_eq_getElem_cons m.isLt]
    rfl
  have hpw := hsplit ▸ hrest
  rw [List.pairwise_append, List.pairwise_cons] at hpw
  obtain ⟨hin, ⟨hb, hout⟩, hcross⟩ := hpw
  exact ⟨hsplit, hlt _ (List.getElem_mem _), fun x hx =>
    ⟨hlt x (List.mem_of_mem_take hx), hcross x hx _ List.mem_cons_self⟩, hb, hin, hout⟩

/-- **Soundness.**  The partner function of an entry is a noncrossing perfect matching of
the points. -/
theorem isNoncrossingMatchingOn_mate {ps : List α} (hps : ps.Pairwise (· < ·))
    {p : List (α × α)} (hp : p ∈ noncrossingMatchings ps) :
    IsNoncrossingMatchingOn {x | x ∈ ps} (mate p) := by
  induction hp using induction_mem with
  | nil => exact ⟨fun x => rfl, fun x hx => absurd hx (List.not_mem_nil), fun x _ => rfl,
      fun a b hab hb _ => (lt_asymm hab hb).elim⟩
  | cons a rest m _ inside hinside outside houtside hI hO =>
    obtain ⟨hsplit, hab, hI_lt, hO_gt, hIs, hOs⟩ := split_facts hps m
    have hI := hI hIs
    have hO := hO hOs
    set b := rest[m] with hb_def
    set I := rest.take m
    set O := rest.drop (m + 1)
    have hptsI : ∀ x, x ∈ points inside ↔ x ∈ I := fun x => mem_points_iff_of_mem hinside
    have hptsO : ∀ x, x ∈ points outside ↔ x ∈ O := fun x => mem_points_iff_of_mem houtside
    have hmemI : ∀ x ∈ I, mate inside x ∈ I := fun x hx => hI.mem hx
    have hmemO : ∀ x ∈ O, mate outside x ∈ O := fun x hx => hO.mem hx
    have hneO_I : ∀ y ∈ O, y ∉ I := fun y hy hyI => lt_asymm (hI_lt y hyI).2 (hO_gt y hy)
    -- the partner function, region by region
    have ga : mate ((a, b) :: (inside ++ outside)) a = b := mate_cons_fst a b _
    have gb : mate ((a, b) :: (inside ++ outside)) b = a := mate_cons_snd hab.ne _
    have gI : ∀ x ∈ I, mate ((a, b) :: (inside ++ outside)) x = mate inside x := by
      intro x hx
      rw [mate_cons_of_ne (hI_lt x hx).1.ne' (hI_lt x hx).2.ne,
        mate_append_of_mem ((hptsI x).mpr hx)]
    have gO : ∀ y ∈ O, mate ((a, b) :: (inside ++ outside)) y = mate outside y := by
      intro y hy
      rw [mate_cons_of_ne (hab.trans (hO_gt y hy)).ne' (hO_gt y hy).ne',
        mate_append_of_notMem fun h => hneO_I y hy ((hptsI y).mp h)]
    have hcases : ∀ x ∈ a :: rest, x = a ∨ x ∈ I ∨ x = b ∨ x ∈ O := by
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Or.inl rfl
      · rw [hsplit] at hx
        rcases List.mem_append.mp hx with hx | hx
        · exact Or.inr (Or.inl hx)
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact Or.inr (Or.inr (Or.inl rfl))
          · exact Or.inr (Or.inr (Or.inr hx))
    have hpts : ∀ x, x ∈ points ((a, b) :: (inside ++ outside)) ↔ x ∈ a :: rest :=
      fun x => mem_points_iff_of_mem (mem_noncrossingMatchings_cons.mpr
        ⟨m, by assumption, inside, hinside, outside, houtside, rfl⟩)
    have goff : ∀ x, x ∉ a :: rest → mate ((a, b) :: (inside ++ outside)) x = x :=
      fun x hx => mate_eq_self_of_notMem fun h => hx ((hpts x).mp h)
    set g := mate ((a, b) :: (inside ++ outside))
    -- `g` maps each region into itself or swaps the two named points
    have hloc : ∀ x ∈ a :: rest, g x ∈ a :: rest ∧ g x ≠ x := by
      intro x hx
      have hmemrest : ∀ y, y ∈ I ∨ y = b ∨ y ∈ O → y ∈ a :: rest := by
        intro y hy
        refine List.mem_cons_of_mem _ ?_
        rw [hsplit]
        rcases hy with hy | rfl | hy
        · exact List.mem_append_left _ hy
        · exact List.mem_append_right _ List.mem_cons_self
        · exact List.mem_append_right _ (List.mem_cons_of_mem _ hy)
      rcases hcases x hx with rfl | hx | rfl | hx
      · exact ⟨by rw [ga]; exact hmemrest _ (Or.inr (Or.inl rfl)), by rw [ga]; exact hab.ne'⟩
      · exact ⟨by rw [gI x hx]; exact hmemrest _ (Or.inl (hmemI x hx)),
          by rw [gI x hx]; exact hI.ne x hx⟩
      · exact ⟨by rw [gb]; exact List.mem_cons_self, by rw [gb]; exact hab.ne⟩
      · exact ⟨by rw [gO x hx]; exact hmemrest _ (Or.inr (Or.inr (hmemO x hx))),
          by rw [gO x hx]; exact hO.ne x hx⟩
    refine ⟨?_, fun x hx => (hloc x hx).2, goff, ?_⟩
    · intro x
      by_cases hx : x ∈ a :: rest
      · rcases hcases x hx with rfl | hx | rfl | hx
        · rw [ga, gb]
        · rw [gI x hx, gI _ (hmemI x hx), hI.involutive x]
        · rw [gb, ga]
        · rw [gO x hx, gO _ (hmemO x hx), hO.involutive x]
      · rw [goff x hx, goff x hx]
    · intro u v huv hvgu hgugv
      by_cases hu : u ∈ a :: rest
      swap
      · rw [goff u hu] at hvgu
        exact lt_asymm huv hvgu
      by_cases hv : v ∈ a :: rest
      swap
      · rw [goff v hv] at hgugv
        exact lt_asymm hvgu hgugv
      rcases hcases u hu with rfl | huI | rfl | huO
      · -- the outer chord: everything strictly inside it is matched inside
        rw [ga] at hvgu hgugv
        rcases hcases v hv with rfl | hvI | rfl | hvO
        · exact lt_irrefl _ huv
        · rw [gI v hvI] at hgugv
          exact lt_asymm hgugv (hI_lt _ (hmemI v hvI)).2
        · exact lt_irrefl _ hvgu
        · exact lt_asymm hvgu (hO_gt v hvO)
      · rw [gI u huI] at hvgu hgugv
        have hgu := hI_lt _ (hmemI u huI)
        rcases hcases v hv with rfl | hvI | rfl | hvO
        · exact lt_asymm huv (hI_lt u huI).1
        · rw [gI v hvI] at hgugv
          exact hI.noncrossing u v huv hvgu hgugv
        · exact lt_asymm hvgu hgu.2
        · exact lt_asymm (hvgu.trans hgu.2) (hO_gt v hvO)
      · rw [gb] at hvgu
        exact lt_asymm (huv.trans hvgu) hab
      · rw [gO u huO] at hvgu hgugv
        rcases hcases v hv with rfl | hvI | rfl | hvO
        · exact lt_asymm huv (hab.trans (hO_gt u huO))
        · exact lt_asymm (hI_lt v hvI).2 ((hO_gt u huO).trans huv)
        · exact lt_asymm huv (hO_gt u huO)
        · rw [gO v hvO] at hgugv
          exact hO.noncrossing u v huv hvgu hgugv

theorem involutive_mate {ps : List α} (hps : ps.Pairwise (· < ·)) {p : List (α × α)}
    (hp : p ∈ noncrossingMatchings ps) : Involutive (mate p) :=
  (isNoncrossingMatchingOn_mate hps hp).involutive

theorem isNoncrossing_mate {ps : List α} (hps : ps.Pairwise (· < ·)) {p : List (α × α)}
    (hp : p ∈ noncrossingMatchings ps) : IsNoncrossing (mate p) :=
  (isNoncrossingMatchingOn_mate hps hp).noncrossing

/-- **Completeness.**  Every noncrossing involution without fixed points on a strictly
increasing list of points agrees on them with an entry of the enumeration. -/
theorem exists_mem_noncrossingMatchings {ps : List α} (hps : ps.Pairwise (· < ·)) {f : α → α}
    (hf : Involutive f) (hmem : ∀ x ∈ ps, f x ∈ ps) (hne : ∀ x ∈ ps, f x ≠ x)
    (hnc : IsNoncrossing f) :
    ∃ p ∈ noncrossingMatchings ps, ∀ x ∈ ps, mate p x = f x := by
  induction h : ps.length using Nat.strong_induction_on generalizing ps with
  | _ n ih =>
  cases ps with
  | nil => exact ⟨[], by simp, by simp⟩
  | cons a rest =>
    have hb_rest : f a ∈ rest :=
      (List.mem_cons.mp (hmem a List.mem_cons_self)).resolve_left (hne a List.mem_cons_self)
    obtain ⟨i, hi, hbi⟩ := List.getElem_of_mem hb_rest
    set m : Fin rest.length := ⟨i, hi⟩
    have hbm : rest[m] = f a := hbi
    obtain ⟨hsplit, hab, hI_lt, hO_gt, hIs, hOs⟩ := split_facts hps m
    rw [hbm] at hab hI_lt hO_gt
    have hfb : f (f a) = a := hf a
    have hcases : ∀ x ∈ rest, x ∈ rest.take m ∨ x = f a ∨ x ∈ rest.drop (m + 1) := by
      intro x hx
      rw [hsplit] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact Or.inl hx
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact Or.inr (Or.inl hbm)
        · exact Or.inr (Or.inr hx)
    -- the points strictly inside the chord at `a` are matched among themselves
    have hI_closed : ∀ x ∈ rest.take m, f x ∈ rest.take m := by
      intro x hx
      have hxr := List.mem_of_mem_take hx
      have hfx : f x ∈ a :: rest := hmem x (List.mem_cons_of_mem _ hxr)
      have hfx_a : f x ≠ a := fun h' => (hI_lt x hx).2.ne (by rw [← h', hf x])
      rcases hcases _ ((List.mem_cons.mp hfx).resolve_left hfx_a) with h' | h' | h'
      · exact h'
      · exact absurd (by rw [← hf x, h', hfb]) (hI_lt x hx).1.ne'
      · exact (hnc a x (hI_lt x hx).1 (hI_lt x hx).2 (hO_gt _ h')).elim
    -- the points after the chord are matched among themselves
    have hO_closed : ∀ y ∈ rest.drop (m + 1), f y ∈ rest.drop (m + 1) := by
      intro y hy
      have hyr := List.mem_of_mem_drop hy
      have hfy : f y ∈ a :: rest := hmem y (List.mem_cons_of_mem _ hyr)
      have hfy_a : f y ≠ a := fun h' => (hO_gt y hy).ne' (by rw [← h', hf y])
      rcases hcases _ ((List.mem_cons.mp hfy).resolve_left hfy_a) with h' | h' | h'
      · exact (hnc a (f y) (hI_lt _ h').1 (hI_lt _ h').2 (by rw [hf y]; exact hO_gt y hy)).elim
      · exact absurd (by rw [← hf y, h', hfb]) (hab.trans (hO_gt y hy)).ne'
      · exact h'
    -- the points inside are evenly many
    have heven : (m : ℕ) % 2 = 0 := by
      have hnd : (rest.take m).Nodup := hIs.imp ne_of_lt
      have hcard : (rest.take m).toFinset.card = m := by
        rw [List.toFinset_card_of_nodup hnd, List.length_take]
        exact min_eq_left hi.le
      have := MatchingParity.even_card_of_closed_of_involutive hf (rest.take m).toFinset
        (fun x hx => List.mem_toFinset.mpr (hI_closed x (List.mem_toFinset.mp hx)))
        (fun x hx => hne x (List.mem_cons_of_mem _
          (List.mem_of_mem_take (List.mem_toFinset.mp hx))))
      rw [hcard] at this
      exact Nat.even_iff.mp this
    have hlen : rest.length < n := by simp [← h]
    obtain ⟨pin, hpin, hpin_agree⟩ := ih _ (lt_of_le_of_lt (List.length_take_le' _ _) hlen) hIs
      hI_closed (fun x hx => hne x (List.mem_cons_of_mem _ (List.mem_of_mem_take hx))) rfl
    obtain ⟨pout, hpout, hpout_agree⟩ := ih _ (lt_of_le_of_lt (by simp) hlen) hOs
      hO_closed (fun x hx => hne x (List.mem_cons_of_mem _ (List.mem_of_mem_drop hx))) rfl
    refine ⟨(a, f a) :: (pin ++ pout),
      mem_noncrossingMatchings_cons.mpr ⟨m, heven, pin, hpin, pout, hpout, by rw [hbm]⟩, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact mate_cons_fst _ _ _
    · rcases hcases x hx with hx | rfl | hx
      · rw [mate_cons_of_ne (hI_lt x hx).1.ne' (hI_lt x hx).2.ne,
          mate_append_of_mem ((mem_points_iff_of_mem hpin).mpr hx), hpin_agree x hx]
      · rw [mate_cons_snd hab.ne, hfb]
      · rw [mate_cons_of_ne (hab.trans (hO_gt x hx)).ne' (hO_gt x hx).ne',
          mate_append_of_notMem fun h' => lt_asymm (hI_lt x
            ((mem_points_iff_of_mem hpin).mp h')).2 (hO_gt x hx), hpout_agree x hx]

end Correctness

/-! ### No repetitions, and the Catalan count -/

section Count

/-- Splitting a list without repetitions at position `m`. -/
private theorem split_nodup {a : α} {rest : List α} (h : (a :: rest).Nodup)
    (m : Fin rest.length) :
    a ∉ rest ∧ rest[m] ∉ rest.take m ∧ rest[m] ∉ rest.drop (m + 1) ∧
      (∀ x ∈ rest.take m, x ∉ rest.drop (m + 1)) ∧
      (rest.take m).Nodup ∧ (rest.drop (m + 1)).Nodup := by
  obtain ⟨ha, hrest⟩ := List.nodup_cons.mp h
  have hsplit : rest = rest.take m ++ rest[m] :: rest.drop (m + 1) := by
    conv_lhs => rw [← List.take_append_drop m rest, List.drop_eq_getElem_cons m.isLt]
    rfl
  have hnd := hsplit ▸ hrest
  rw [List.nodup_append, List.nodup_cons] at hnd
  obtain ⟨hI, ⟨hbO, hO⟩, hdisj⟩ := hnd
  exact ⟨ha, fun hb => hdisj _ hb _ List.mem_cons_self rfl, hbO,
    fun x hx hxO => hdisj x hx x (List.mem_cons_of_mem _ hxO) rfl, hI, hO⟩

variable [DecidableEq α]

/-- **Distinct entries have distinct partner functions** on the points. -/
theorem eq_of_mate_eq {ps : List α} (hps : ps.Nodup) {p q : List (α × α)}
    (hp : p ∈ noncrossingMatchings ps) (hq : q ∈ noncrossingMatchings ps)
    (h : ∀ x ∈ ps, mate p x = mate q x) : p = q := by
  induction hp using induction_mem generalizing q with
  | nil => simpa using hq
  | cons a rest m heven ip hip op hop ihI ihO =>
    obtain ⟨m', heven', iq, hiq, oq, hoq, rfl⟩ := mem_noncrossingMatchings_cons.mp hq
    obtain ⟨ha, hbI, hbO, hIO, hIs, hOs⟩ := split_nodup hps m
    -- the partners of the first point agree, so the split positions agree
    have hmm : m = m' := by
      have h0 := h a List.mem_cons_self
      rw [mate_cons_fst, mate_cons_fst] at h0
      exact Fin.ext ((List.nodup_cons.mp hps).2.getElem_inj_iff.mp h0)
    subst hmm
    have hneI : ∀ x ∈ rest.take m, x ≠ a ∧ x ≠ rest[m] := fun x hx =>
      ⟨fun hxa => ha (hxa ▸ List.mem_of_mem_take hx), fun hxb => hbI (hxb ▸ hx)⟩
    have hneO : ∀ y ∈ rest.drop (m + 1), y ≠ a ∧ y ≠ rest[m] := fun y hy =>
      ⟨fun hya => ha (hya ▸ List.mem_of_mem_drop hy), fun hyb => hbO (hyb ▸ hy)⟩
    have hI : ip = iq := ihI hIs hiq fun x hx => by
      have := h x (List.mem_cons_of_mem _ (List.mem_of_mem_take hx))
      rwa [mate_cons_of_ne (hneI x hx).1 (hneI x hx).2,
        mate_cons_of_ne (hneI x hx).1 (hneI x hx).2,
        mate_append_of_mem ((mem_points_iff_of_mem hip).mpr hx),
        mate_append_of_mem ((mem_points_iff_of_mem hiq).mpr hx)] at this
    subst hI
    have hO : op = oq := ihO hOs hoq fun y hy => by
      have := h y (List.mem_cons_of_mem _ (List.mem_of_mem_drop hy))
      have hyI : y ∉ points ip := fun h' => hIO y ((mem_points_iff_of_mem hip).mp h') hy
      rwa [mate_cons_of_ne (hneO y hy).1 (hneO y hy).2,
        mate_cons_of_ne (hneO y hy).1 (hneO y hy).2,
        mate_append_of_notMem hyI, mate_append_of_notMem hyI] at this
    rw [hO]

omit [DecidableEq α] in
/-- **The enumeration lists no matching twice.** -/
theorem nodup_noncrossingMatchings {ps : List α} (hps : ps.Nodup) :
    (noncrossingMatchings ps).Nodup := by
  induction h : ps.length using Nat.strong_induction_on generalizing ps with
  | _ n ih =>
  cases ps with
  | nil => simp
  | cons a rest =>
    have hlen : rest.length < n := by simp [← h]
    rw [noncrossingMatchings_cons, List.nodup_flatMap]
    refine ⟨fun m _ => ?_, ?_⟩
    · obtain ⟨-, -, -, -, hIs, hOs⟩ := split_nodup hps m
      have hIn := ih _ (lt_of_le_of_lt (List.length_take_le' _ _) hlen) hIs rfl
      have hOn := ih _ (lt_of_le_of_lt (by simp) hlen) hOs rfl
      split_ifs
      · rw [List.nodup_flatMap]
        refine ⟨fun inside _ => hOn.map fun o o' hoo' => ?_, ?_⟩
        · exact List.append_cancel_left (List.cons_injective hoo')
        · refine hIn.pairwise_of_forall_ne fun i hi i' hi' hne => ?_
          intro x hx hx'
          simp only [List.mem_map] at hx hx'
          obtain ⟨o, ho, rfl⟩ := hx
          obtain ⟨o', ho', heq⟩ := hx'
          have happ := (List.cons_injective heq).symm
          exact hne (List.append_inj_left happ (by
            have h₁ := two_mul_length_of_mem hi
            have h₂ := two_mul_length_of_mem hi'
            omega))
      · exact List.nodup_nil
    · refine (List.nodup_finRange _).pairwise_of_forall_ne fun m _ m' _ hne => ?_
      intro x hx hx'
      have hhead : ∀ k : Fin rest.length, ∀ y ∈ (if (k : ℕ) % 2 = 0 then
          (noncrossingMatchings (rest.take k)).flatMap fun inside =>
            (noncrossingMatchings (rest.drop (k + 1))).map fun outside =>
              (a, rest[k]) :: (inside ++ outside)
          else []), y.head? = some (a, rest[k]) := by
        intro k y hy
        split_ifs at hy
        · simp only [List.mem_flatMap, List.mem_map] at hy
          obtain ⟨_, _, _, _, rfl⟩ := hy
          rfl
        · simp at hy
      have h₁ := hhead m x hx
      have h₂ := hhead m' x hx'
      rw [h₁, Option.some.injEq, Prod.mk.injEq] at h₂
      exact hne (Fin.ext ((List.nodup_cons.mp hps).2.getElem_inj_iff.mp h₂.2))

omit [DecidableEq α] in
private theorem length_flatMap_map {β γ : Type*} (l : List β) (l' : List γ)
    (g : β → γ → List (α × α)) :
    (l.flatMap fun x => l'.map (g x)).length = l.length * l'.length := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.succ_mul, Nat.add_comm]

private theorem sum_range_two_mul_add_one (h : ℕ → ℕ) (k : ℕ) :
    ∑ m ∈ Finset.range (2 * k + 1), (if m % 2 = 0 then h (m / 2) else 0) =
      ∑ i ∈ Finset.range (k + 1), h i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, Finset.sum_range_succ,
      Finset.sum_range_succ, ih, Finset.sum_range_succ (n := k + 1)]
    have h₁ : (2 * k + 1) % 2 = 1 := by omega
    have h₂ : (2 * k + 1 + 1) % 2 = 0 := by omega
    have h₃ : (2 * k + 1 + 1) / 2 = k + 1 := by omega
    rw [if_neg (by omega), if_pos h₂, h₃, add_zero]

omit [DecidableEq α] in
/-- **The enumeration has Catalan length**: `catalan k` entries for `2 * k` points, none
for an odd number of points. -/
theorem length_noncrossingMatchings (ps : List α) :
    (noncrossingMatchings ps).length =
      if Even ps.length then catalan (ps.length / 2) else 0 := by
  induction h : ps.length using Nat.strong_induction_on generalizing ps with
  | _ n ih =>
  cases ps with
  | nil => simp at h; subst h; simp
  | cons a rest =>
    have hlen : rest.length < n := by simp [← h]
    have hterm : ∀ m : Fin rest.length, (if (m : ℕ) % 2 = 0 then
          (noncrossingMatchings (rest.take m)).flatMap (fun inside =>
            (noncrossingMatchings (rest.drop (m + 1))).map fun outside =>
              (a, rest[m]) :: (inside ++ outside))
          else []).length =
        if (m : ℕ) % 2 = 0 then catalan ((m : ℕ) / 2) *
          (if Even (rest.length - (m + 1)) then catalan ((rest.length - (m + 1)) / 2) else 0)
        else 0 := by
      intro m
      by_cases heven : (m : ℕ) % 2 = 0
      · rw [if_pos heven, if_pos heven, length_flatMap_map,
          ih _ (lt_of_le_of_lt (List.length_take_le' _ _) hlen) _ rfl,
          ih _ (lt_of_le_of_lt (by simp) hlen) _ rfl]
        have hm : (rest.take m).length = m := by
          rw [List.length_take]; exact min_eq_left m.isLt.le
        rw [hm, List.length_drop, if_pos (Nat.even_iff.mpr heven)]
      · rw [if_neg heven, if_neg heven]
        rfl
    rw [noncrossingMatchings_cons, List.length_flatMap, List.map_congr_left fun m _ => hterm m,
      ← Fin.sum_univ_def, Fin.sum_univ_eq_sum_range
        (fun m => if m % 2 = 0 then catalan (m / 2) *
          (if Even (rest.length - (m + 1)) then catalan ((rest.length - (m + 1)) / 2) else 0)
          else 0) rest.length]
    rw [← h, List.length_cons]
    rcases Nat.even_or_odd rest.length with ⟨k, hk⟩ | ⟨k, hk⟩
    · -- an odd number of points: every term vanishes
      have hodd : ¬ Even (rest.length + 1) := by
        rw [Nat.not_even_iff_odd]; exact ⟨k, by omega⟩
      rw [if_neg hodd]
      refine Finset.sum_eq_zero fun m hm => ?_
      rw [Finset.mem_range] at hm
      by_cases h₁ : m % 2 = 0
      · rw [if_pos h₁, if_neg (by rw [Nat.not_even_iff_odd]; exact ⟨k - m / 2 - 1, by omega⟩),
          mul_zero]
      · rw [if_neg h₁]
    · -- `2 * k + 2` points: the Catalan recursion
      rw [if_pos ⟨k + 1, by omega⟩, show (rest.length + 1) / 2 = k + 1 by omega, catalan_succ,
        Fin.sum_univ_eq_sum_range (fun i => catalan i * catalan (k - i)) (k + 1), hk,
        ← sum_range_two_mul_add_one (fun i => catalan i * catalan (k - i)) k]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mem_range] at hm
      by_cases h₁ : m % 2 = 0
      · rw [if_pos h₁, if_pos h₁, if_pos ⟨k - m / 2, by omega⟩]
        congr 2
        omega
      · rw [if_neg h₁, if_neg h₁]

end Count

/-! ### Noncrossing perfect matchings of a finite linear order -/

section Pairings

variable [LinearOrder α] [Fintype α]

/-- **The noncrossing perfect matchings of `2 * n` linearly ordered points number
`catalan n`.** -/
theorem card_noncrossing_pairing {n : ℕ} (hn : Fintype.card α = 2 * n) :
    Nat.card {M : MatchingParity.Pairing α // IsNoncrossing M.partner} = catalan n := by
  set ps := (Finset.univ : Finset α).sort (· ≤ ·)
  have hps : ps.Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise
  have hmem : ∀ x, x ∈ ps := fun x => by simp [ps]
  have hlen : ps.length = 2 * n := by simp [ps, hn]
  let toPairing : {p // p ∈ noncrossingMatchings ps} →
      {M : MatchingParity.Pairing α // IsNoncrossing M.partner} := fun p =>
    ⟨⟨mate p.1, involutive_mate hps p.2, fun x =>
      (isNoncrossingMatchingOn_mate hps p.2).ne x (hmem x)⟩, isNoncrossing_mate hps p.2⟩
  have hbij : Function.Bijective toPairing := by
    constructor
    · rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
      have hpartner : mate p = mate q := by
        have := congrArg (fun M => M.1.partner) hpq
        simpa [toPairing] using this
      exact Subtype.ext (eq_of_mate_eq hps.nodup hp hq fun x _ => congrFun hpartner x)
    · rintro ⟨⟨f, hff, hfne⟩, hnc⟩
      obtain ⟨p, hp, hagree⟩ := exists_mem_noncrossingMatchings hps hff
        (fun x _ => hmem (f x)) (fun x _ => hfne x) hnc
      refine ⟨⟨p, hp⟩, ?_⟩
      have hfun : mate p = f := funext fun x => hagree x (hmem x)
      simp only [toPairing, Subtype.mk.injEq]
      cases hfun
      rfl
  rw [← Nat.card_congr (Equiv.ofBijective _ hbij)]
  have hcard : Nat.card {p // p ∈ noncrossingMatchings ps} =
      (noncrossingMatchings ps).length := by
    rw [← List.toFinset_card_of_nodup (nodup_noncrossingMatchings hps.nodup),
      ← Nat.card_eq_finsetCard]
    exact Nat.card_congr (Equiv.subtypeEquivRight fun p => List.mem_toFinset.symm)
  rw [hcard, length_noncrossingMatchings, hlen, if_pos (even_two_mul n),
    Nat.mul_div_cancel_left n two_pos]

end Pairings

end NoncrossingMatching
