import FourColor.Bulk.Chords
import Mathlib.Data.List.GetD
import MettapediaFourColor.KempeMajorityRepair

/-!
# Recovering the exterior matching at arbitrary width

The chord scan and its disjointness, coverage and noncrossing theorems are
reused from Gonthier/Emery's development (`FourColor.Bulk.Chords`). No bulk
reducibility data or certificate checker is used. The recovered involution
lets structural repair laws operate on the original accepted chromogram.
-/

namespace FourColor.KempeChromogramMatching

open Color KempeMatchingChromogram

variable {n : ℕ}

def Pair (cs : List (ℕ × ℕ)) (i j : Fin n) : Prop :=
  (min i.val j.val, max i.val j.val) ∈ cs

theorem pair_symm {cs : List (ℕ × ℕ)} {i j : Fin n} (h : Pair cs i j) : Pair cs j i := by
  simpa only [Pair, min_comm, max_comm] using h

noncomputable def mate (cs : List (ℕ × ℕ)) (i : Fin n) : Fin n := by
  classical
  exact if h : ∃ j, Pair cs i j then Classical.choose h else i

theorem mate_pair {cs : List (ℕ × ℕ)} {i : Fin n} (h : ∃ j, Pair cs i j) :
    Pair cs i (mate cs i) := by
  classical
  simp only [mate, dite_eq_left h]
  exact Classical.choose_spec h

theorem pair_ne {cs : List (ℕ × ℕ)}
    (hb : ∀ ab ∈ cs, ab.1 < ab.2) {i j : Fin n} (h : Pair cs i j) : i ≠ j := by
  intro he
  subst j
  have := hb _ h
  simp at this

theorem pair_unique {cs : List (ℕ × ℕ)}
    (hd : ∀ ab ∈ cs, ∀ cd ∈ cs, ab ≠ cd → ChordDisj ab cd)
    {i j k : Fin n} (hj : Pair cs i j) (hk : Pair cs i k) : j = k := by
  have he : (min i.val j.val, max i.val j.val) = (min i.val k.val, max i.val k.val) := by
    by_contra h
    have dis := hd _ hj _ hk h
    unfold ChordDisj at dis
    rcases le_total i.val j.val with hij | hji <;>
      rcases le_total i.val k.val with hik | hki <;>
      simp only [min_eq_left, min_eq_right, max_eq_left, max_eq_right, *] at dis <;> omega
  apply Fin.ext
  have h1 := congrArg Prod.fst he
  have h2 := congrArg Prod.snd he
  dsimp at h1 h2
  omega

theorem mate_involutive {cs : List (ℕ × ℕ)}
    (hd : ∀ ab ∈ cs, ∀ cd ∈ cs, ab ≠ cd → ChordDisj ab cd) :
    Function.Involutive (mate (n := n) cs) := by
  classical
  intro i
  by_cases h : ∃ j, Pair cs i j
  · have hp := pair_symm (mate_pair h)
    exact pair_unique hd (mate_pair ⟨i, hp⟩) hp
  · simp [mate, h]

theorem mate_fixed {cs : List (ℕ × ℕ)}
    (hb : ∀ ab ∈ cs, ab.1 < ab.2) (i : Fin n) :
    mate cs i = i ↔ ¬ ∃ j, Pair cs i j := by
  classical
  constructor
  · intro he h
    exact pair_ne hb (mate_pair h) he.symm
  · intro h
    simp [mate, h]

theorem mate_noncrossing {cs : List (ℕ × ℕ)} (hn : FourColor.NonCrossing cs) :
    KempeMatchingChromogram.Noncrossing (mate (n := n) cs) := by
  classical
  intro i j hcross
  by_cases hi : ∃ k, Pair cs i k
  · by_cases hj : ∃ k, Pair cs j k
    · have pi := mate_pair hi
      have pj := mate_pair hj
      rcases hcross with h | h
      · exact hn _ pi _ pj h
      · exact hn _ pj _ pi h
    · have he : mate cs j = j := by simp [mate, hj]
      simp only [he, min_self, max_self] at hcross
      omega
  · have he : mate cs i = i := by simp [mate, hi]
    simp only [he, min_self, max_self] at hcross
    omega

theorem pair_exists_iff_endpoint {cs : List (ℕ × ℕ)}
    (hb : ∀ ab ∈ cs, ab.1 < ab.2 ∧ ab.2 < n) (i : Fin n) :
    (∃ j, Pair cs i j) ↔ ∃ ab ∈ cs, ab.1 = i.val ∨ ab.2 = i.val := by
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨_, hj, ?_⟩
    rcases le_total i.val j.val with h | h
    · exact Or.inl (min_eq_left h)
    · exact Or.inr (max_eq_left h)
  · rintro ⟨⟨a,b⟩, hab, h | h⟩
    · have hs := hb _ hab
      refine ⟨⟨b, hs.2⟩, ?_⟩
      simp only [Pair, ← h, min_eq_left (Nat.le_of_lt hs.1),
        max_eq_right (Nat.le_of_lt hs.1)]
      exact hab
    · have hs := hb _ hab
      refine ⟨⟨a, by omega⟩, ?_⟩
      simp only [Pair, ← h, min_eq_right (Nat.le_of_lt hs.1),
        max_eq_left (Nat.le_of_lt hs.1)]
      exact hab

private theorem flip_false (c : Color) : flipC false c = c := rfl

private theorem flip_true (c : Color) : flipC true c = EdgePerm.e132 c := by
  cases c <;> rfl

theorem flip_two_eq_switch (c : Fin n → Color) (a b : Fin n) :
    flipFromB (2 ^ a.val ||| 2 ^ b.val) 0 (List.ofFn c) =
      List.ofFn (KempeIntervalRepair.switch c a b) := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    have bound : i < n := by simpa using hi'
    have h := getD_flipFrom (2 ^ a.val ||| 2 ^ b.val) 0 (List.ofFn c) i
    simp only [List.length_ofFn, bound, ↓reduceIte, Nat.zero_add,
      Nat.testBit_or, Nat.testBit_two_pow] at h
    rw [List.getD_eq_getElem _ 0 hi, List.getD_eq_getElem _ 0 (by simpa using bound)] at h
    simp only [List.getElem_ofFn] at h ⊢
    rw [h]
    by_cases ha : i = a.val <;> by_cases hb : i = b.val <;>
      simp [KempeIntervalRepair.switch, Fin.ext_iff, ha, hb, eq_comm, flip_true, flip_false]

/-- A decoded chord can be switched without changing the original chromogram. -/
theorem pair_switch {c : Fin n → Color} {w : Chromogram}
    (hm : matchg [] (List.ofFn c) w) {cs : List (ℕ × ℕ)} (hc : chords w = some cs)
    {a b : Fin n} (hp : Pair cs a b) :
    matchg [] (List.ofFn (KempeIntervalRepair.switch c a b)) w := by
  have hf := (chord_facts hm hc hp).2.2.2.2.2.1
  let mask := 2 ^ a.val ||| 2 ^ b.val
  have bits : ∀ r, mask.testBit r = true ↔
      (r = min a.val b.val ∨ r = max a.val b.val) := by
    intro r
    simp only [mask, Nat.testBit_or, Nat.testBit_two_pow, Bool.or_eq_true, decide_eq_true_eq]
    omega
  have flipped := matchg_flip mask w (List.ofFn c) 0 [] [] hm (hf mask bits)
  simpa only [List.zipWith_nil_left, mask, flip_two_eq_switch] using flipped

/-- Recover a single matching for the supplied exterior, at every boundary
width. Every selected chord retains that very same exterior description. -/
theorem recover (c : Fin n → Color) (w : Chromogram)
    (hm : matchg [] (List.ofFn c) w) :
    ∃ m : Fin n → Fin n, Function.Involutive m ∧ Noncrossing m ∧
      (∀ i, m i = i ↔ c i = c1) ∧
      ∀ i, c i ≠ c1 → matchg [] (List.ofFn (KempeIntervalRepair.switch c i (m i))) w := by
  classical
  obtain ⟨cs, hc⟩ := chords_isSome_of_matchg hm
  have hlen : w.length = n := by simpa using matchg_length (List.ofFn c) [] w hm
  have hb : ∀ ab ∈ cs, ab.1 < ab.2 ∧ ab.2 < n := by
    simpa only [hlen] using chords_bounds hc
  have exists_iff (i : Fin n) : (∃ j, Pair cs i j) ↔ c i ≠ c1 := by
    rw [pair_exists_iff_endpoint hb]
    simpa using chords_endpoints_matchg hm hc i.val (by simp)
  refine ⟨mate cs, mate_involutive (chords_disjoint hc),
    mate_noncrossing (chords_nonCrossing hc), ?_, ?_⟩
  · intro i
    rw [mate_fixed (fun ab hab => (hb ab hab).1), exists_iff, not_not]
  · intro i hi
    exact pair_switch hm hc (mate_pair ((exists_iff i).mpr hi))

open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

/-- The majority law in the actual exterior semantics, without a finite
inverse-layout check. Continuations may themselves be composed repairs. -/
theorem majority_coclosure {m : ℕ} {P : List Color → Prop} (c : Fin n → Color)
    (embed : Fin m → Fin n) (rank : Fin n → Fin m)
    (hre : ∀ i, rank (embed i) = i)
    (her : ∀ i, c i ≠ c1 → embed (rank i) = i)
    (ha : ∀ i, c (embed i) ≠ c1)
    (horder : ∀ a b x y,
      ¬ ChordsCross (embed a) (embed x) (embed b) (embed y) → ¬ ChordsCross a x b y)
    (block : Finset (Fin m))
    (hconvex : ∀ a ∈ block, ∀ b ∈ block, ∀ x, a < x → x < b → x ∈ block)
    (hmajor : m < 2 * block.card)
    (repairs : ∀ a ∈ block, ∀ b ∈ block, b.val = a.val + 1 →
      KempeCoclosure P (List.ofFn (KempeIntervalRepair.switch c (embed a) (embed b)))) :
    KempeCoclosure P (List.ofFn c) := by
  intro outside hout hold
  obtain ⟨_, w, hw, hall⟩ := hout _ hold
  obtain ⟨partner, hi, hn, hf, hs⟩ := recover c w hw
  obtain ⟨lift, inv, free⟩ := KempeMajorityRepair.active_mate c partner hi hf
    embed rank hre her ha
  have order : IsNoncrossingMatching (fun i => rank (partner (embed i))) := by
    intro a b
    apply horder a b
    rw [lift, lift]
    exact hn (embed a) (embed b)
  obtain ⟨i, him, hjm, hadj⟩ := exists_adjacent_majority
    (fun i => rank (partner (embed i))) inv free order block hconvex hmajor
  have repair := repairs i him _ hjm hadj
  rw [lift] at repair
  exact repair outside hout (hall _ (hs (embed i) (ha i)))

end FourColor.KempeChromogramMatching
