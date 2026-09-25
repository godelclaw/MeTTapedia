import Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlatFork

/-!
# A checker for the fork-code audit

The checker reads a list `C` of flat codes and checks by evaluation that

* the canonical form of the flat leaf is in `C`;
* for every ordered pair of members of `C`, every flat descriptor of a planar
  fork, with at most `bound` parent positions, gives a flat fork whose
  canonical form is in `C`;
* no member of `C` without positions is rejecting.

The flat descriptors are enumerated from the pairing words of left with right
positions and, at every open shared vertex, the choice of the kept mark.

**Theorem.**  If the checks pass, every code of the closure `Reach bound` is
stored, up to renaming of its positions, by a member of `C`; hence
`Audit bound` holds.  Every legal descriptor is enumerated, up to the order of
its kept marks, which only renames the positions of the fork.
-/

namespace Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat

open Equiv Equiv.Perm
open GoertzelV24OrderedCutFaceReturnProfile
open PhysicalForkCode

/-! ## Enumeration -/

/-- All lists of length `n` with entries below `b`. -/
def words : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | n + 1, b => (words n b).flatMap fun l => (List.range b).map (· :: l)

theorem mem_words {n b : ℕ} {l : List ℕ} :
    l ∈ words n b ↔ l.length = n ∧ ∀ x ∈ l, x < b := by
  induction n generalizing l with
  | zero =>
      simp only [words, List.mem_singleton]
      constructor
      · rintro rfl; exact ⟨rfl, by simp⟩
      · intro h; exact List.eq_nil_of_length_eq_zero h.1
  | succ n ih =>
      simp only [words, List.mem_flatMap, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨l', hl', d, hd, rfl⟩
        obtain ⟨h1, h2⟩ := ih.mp hl'
        refine ⟨by simp [h1], ?_⟩
        intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hd
        · exact h2 x hx
      · rintro ⟨h1, h2⟩
        cases l with
        | nil => simp at h1
        | cons d l' =>
            exact ⟨l', ih.mpr ⟨by simpa using h1, fun x hx => h2 x (List.mem_cons_of_mem _ hx)⟩,
              d, h2 d List.mem_cons_self, rfl⟩

/-- All lists of booleans of length `n`. -/
def boolLists : ℕ → List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolLists n).flatMap fun l => [false :: l, true :: l]

theorem mem_boolLists {n : ℕ} {l : List Bool} : l ∈ boolLists n ↔ l.length = n := by
  induction n generalizing l with
  | zero =>
      simp only [boolLists, List.mem_singleton]
      exact ⟨fun h => h ▸ rfl, List.eq_nil_of_length_eq_zero⟩
  | succ n ih =>
      simp only [boolLists, List.mem_flatMap, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · rintro ⟨l', hl', rfl | rfl⟩ <;> simp [ih.mp hl']
      · intro h
        cases l with
        | nil => simp at h
        | cons b l' =>
            refine ⟨l', ih.mpr (by simpa using h), ?_⟩
            cases b <;> simp

def nodupB : List ℕ → Bool
  | [] => true
  | x :: xs => !xs.contains x && nodupB xs

theorem nodupB_iff (l : List ℕ) : nodupB l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [nodupB]
  | cons x xs ih => simp [nodupB, ih, List.nodup_cons]

/-- A pairing word is valid: its nonzero entries are distinct, one exists, and
no shared vertex carries two shore edges on both sides.  Entry `i` is `0` when
left position `i` is unshared and `j + 1` when it is shared with right
position `j`. -/
def validM (L R : FCode) (m : List ℕ) : Bool :=
  nodupB (m.filter (· != 0)) && m.any (· != 0) &&
    (List.range L.n).all fun i => getN m i == 0 || !(getB L.two i && getB R.two (getN m i - 1))

/-- The partner list of a pairing word. -/
def prOf (nL nR : ℕ) (m : List ℕ) : List ℕ :=
  (List.range nL).map (fun i => if getN m i = 0 then i else nL + (getN m i - 1)) ++
    (List.range nR).map fun j => if m.contains (j + 1) then m.idxOf (j + 1) else nL + j

/-- A shared position whose vertex keeps a third edge outside the parent. -/
def openF (L R : FCode) (pr : List ℕ) (x : ℕ) : Bool :=
  getN pr x != x && !twoAt L R x && !twoAt L R (getN pr x)

/-- Kept positions: the unshared ones, and at every open shared vertex the left
mark or the right mark as the orientation bit of its left position says. -/
def keptF (L R : FCode) (pr : List ℕ) (o : List Bool) (x : ℕ) : Bool :=
  getN pr x == x || (openF L R pr x && if x < L.n then !getB o x else getB o (getN pr x))

def orients (L R : FCode) (pr : List ℕ) : List (List Bool) :=
  (boolLists L.n).filter fun o => (List.range L.n).all fun i => !getB o i || openF L R pr i

def marksOf (L R : FCode) (pr : List ℕ) (o : List Bool) : List ℕ :=
  (List.range (L.n + R.n)).filter (keptF L R pr o)

def sharedF (nL : ℕ) (pr : List ℕ) : ℕ :=
  ((List.range nL).filter fun i => getN pr i != i).length

/-- The flat Euler guard. -/
def eulerF (L R : FCode) (pr : List ℕ) : Bool :=
  sharedF L.n pr + cycF L.ret L.n + cycF R.ret R.n == 2 + cycF (compList L R pr) (L.n + R.n)

/-- The flat forks of an ordered pair of flat codes. -/
def forksOf (bound : ℕ) (L R : FCode) : List FCode :=
  ((words L.n (R.n + 1)).filter (validM L R)).flatMap fun m =>
    if eulerF L R (prOf L.n R.n m) then
      (orients L R (prOf L.n R.n m)).filterMap fun o =>
        if (marksOf L R (prOf L.n R.n m) o).length ≤ bound then
          some (flatFork L R (prOf L.n R.n m) (marksOf L R (prOf L.n R.n m) o))
        else none
    else []

/-! ## Canonical forms -/

def keyF (c : FCode) : List ℕ :=
  c.n :: (c.two.map fun b => if b then 1 else 0) ++ c.ret ++ c.col.length :: c.col ++ c.cut

def lexLt : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)

def pickMin (r : FCode) (rs : List FCode) : FCode :=
  rs.foldl (fun best q => if lexLt (keyF q) (keyF best) then q else best) r

/-- The least renaming of a flat code. -/
def canon (c : FCode) : FCode :=
  match (List.permutations' (List.range c.n)).map (relabelF c) with
  | [] => c
  | r :: rs => pickMin r rs

theorem pickMin_mem (r : FCode) (rs : List FCode) : pickMin r rs ∈ r :: rs := by
  unfold pickMin
  induction rs generalizing r with
  | nil => simp
  | cons q qs ih =>
      simp only [List.foldl_cons]
      split
      · have := ih q
        simp only [List.mem_cons] at this ⊢
        tauto
      · have := ih r
        simp only [List.mem_cons] at this ⊢
        tauto

theorem canon_spec (c : FCode) :
    canon c = c ∨ ∃ σ ∈ List.permutations' (List.range c.n), canon c = relabelF c σ := by
  unfold canon
  split
  · exact Or.inl rfl
  · rename_i r rs h
    right
    have hmem : pickMin r rs ∈ (List.permutations' (List.range c.n)).map (relabelF c) :=
      h ▸ pickMin_mem r rs
    obtain ⟨σ, hσ, heq⟩ := List.mem_map.mp hmem
    exact ⟨σ, hσ, heq.symm⟩

theorem exists_permList {n : ℕ} {σ : List ℕ} (h : σ.Perm (List.range n)) :
    ∃ τ : Fin n ≃ Fin n, σ = permList τ := by
  have hlen : σ.length = n := by rw [h.length_eq, List.length_range]
  have hnd : σ.Nodup := h.nodup_iff.mpr List.nodup_range
  have htl : ∀ t : Fin n, (t : ℕ) < σ.length := fun t => by rw [hlen]; exact t.2
  have hlt : ∀ t : Fin n, σ[(t : ℕ)]'(htl t) < n := by
    intro t
    have := h.mem_iff.mp (List.getElem_mem (htl t))
    simpa using this
  let f : Fin n → Fin n := fun t => ⟨σ[(t : ℕ)]'(htl t), hlt t⟩
  have hf : Function.Injective f := by
    intro a b hab
    have := congrArg Fin.val hab
    exact Fin.ext ((hnd.getElem_inj_iff).mp this)
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf), ?_⟩
  apply List.ext_getElem
  · rw [hlen, permList_length]
  · intro t h1 h2
    simp [permList, f]

/-- The canonical form stores a renaming of what the flat code stores. -/
theorem represents_canon {n : ℕ} {f : FCode} {c : Code n} (h : Represents f c) :
    ∃ τ : Fin n ≃ Fin n, Represents (canon f) (c.relabel τ) := by
  rcases canon_spec f with hc | ⟨σ, hσ, hc⟩
  · exact ⟨Equiv.refl _, by rw [hc, Code.relabel_refl]; exact h⟩
  · rw [h.dim] at hσ
    obtain ⟨τ, rfl⟩ := exists_permList (List.mem_permutations'.mp hσ)
    exact ⟨τ, by rw [hc]; exact represents_relabel h τ⟩

/-! ## Every legal descriptor is enumerated -/

theorem legal_relabel {nL nR nP : ℕ} {L : Code nL} {R : Code nR} {g : Glue nL nR nP}
    (σ : Fin nP ≃ Fin nP) (h : Legal L R g) : Legal L R (g.relabel σ) := by
  have hr := range_keep_relabel σ g
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨h1, h2, h3, h4, h5, ?_, ?_, ?_⟩
  · intro x hx; rw [hr]; exact h6 x hx
  · intro x hx ho; rw [hr]; exact h7 x hx ho
  · intro x hx ho; rw [hr]; exact h8 x hx ho

theorem getN_append_left {l l' : List ℕ} {i : ℕ} (h : i < l.length) :
    getN (l ++ l') i = getN l i :=
  List.getD_append _ _ _ _ h

theorem getN_append_right {l l' : List ℕ} {i : ℕ} (h : l.length ≤ i) :
    getN (l ++ l') i = getN l' (i - l.length) :=
  List.getD_append_right _ _ _ _ h

theorem idxOf_eq_of_unique {l : List ℕ} {v i : ℕ} (hi : i < l.length) (hv : l[i] = v)
    (huniq : ∀ i' (h' : i' < l.length), l[i'] = v → i' = i) : l.idxOf v = i := by
  have hlt : l.idxOf v < l.length := List.idxOf_lt_length_iff.mpr (hv ▸ List.getElem_mem hi)
  exact huniq _ hlt (List.getElem_idxOf hlt)

section Complete

variable {nL nR nP : ℕ} {fL fR : FCode} {L : Code nL} {R : Code nR} {g : Glue nL nR nP}

/-- The pairing word of a descriptor. -/
def wordOf (g : Glue nL nR nP) : List ℕ :=
  (List.finRange nL).map fun i => match g.pair (.inl i) with
    | .inl _ => 0
    | .inr j => j + 1

theorem getN_wordOf (i : Fin nL) :
    getN (wordOf g) i = match g.pair (.inl i) with
      | .inl _ => 0
      | .inr j => j + 1 := by
  rw [wordOf, getN, getD_map_finRange]

theorem length_wordOf : (wordOf g).length = nL := by simp [wordOf]

theorem wordOf_fixed (i : Fin nL) (h : g.pair (.inl i) = .inl i) : getN (wordOf g) i = 0 := by
  rw [getN_wordOf, h]

theorem wordOf_shared (i : Fin nL) {j : Fin nR} (h : g.pair (.inl i) = .inr j) :
    getN (wordOf g) i = j + 1 := by
  rw [getN_wordOf, h]

theorem pair_inl_cases (hg : Legal L R g) (i : Fin nL) :
    g.pair (.inl i) = .inl i ∨ ∃ j, g.pair (.inl i) = .inr j := hg.pair_left i

theorem pair_inr_cases (hg : Legal L R g) (j : Fin nR) :
    g.pair (.inr j) = .inr j ∨ ∃ i, g.pair (.inr j) = .inl i := hg.pair_right j

theorem pair_inl_eq_inr_iff (hg : Legal L R g) (i : Fin nL) (j : Fin nR) :
    g.pair (.inl i) = .inr j ↔ g.pair (.inr j) = .inl i := by
  constructor
  · intro h; rw [← h, hg.pair_invol]
  · intro h; rw [← h, hg.pair_invol]

theorem mem_wordOf_iff (hg : Legal L R g) (j : Fin nR) :
    (j + 1 : ℕ) ∈ wordOf g ↔ ∃ i, g.pair (.inl i) = .inr j := by
  constructor
  · intro h
    obtain ⟨i, -, hi⟩ := List.mem_map.mp h
    rcases pair_inl_cases hg i with h' | ⟨j', h'⟩
    · simp [h'] at hi
    · simp only [h'] at hi
      exact ⟨i, by rw [h', Fin.ext (by omega : (j' : ℕ) = j)]⟩
  · rintro ⟨i, hi⟩
    exact List.mem_map.mpr ⟨i, List.mem_finRange i, by simp [hi]⟩

theorem idxOf_wordOf (hg : Legal L R g) {i : Fin nL} {j : Fin nR}
    (h : g.pair (.inl i) = .inr j) : (wordOf g).idxOf ((j : ℕ) + 1) = i := by
  have hlen := length_wordOf (g := g)
  apply idxOf_eq_of_unique (by rw [hlen]; exact i.2)
  · have := wordOf_shared i h
    rw [getN, List.getD_eq_getElem _ _ (by rw [hlen]; exact i.2)] at this
    exact this
  · intro i' hi' heq
    have hi'' : i' < nL := hlen ▸ hi'
    have hw := getN_wordOf (g := g) ⟨i', hi''⟩
    rw [getN, List.getD_eq_getElem _ _ hi', heq] at hw
    rcases pair_inl_cases hg ⟨i', hi''⟩ with h' | ⟨j', h'⟩
    · rw [h'] at hw; simp at hw
    · rw [h'] at hw
      simp only at hw
      have hj : j' = j := Fin.ext (by omega)
      subst hj
      have := g.pair.injective (h'.trans h.symm)
      simp only [Sum.inl.injEq] at this
      exact congrArg Fin.val this

theorem prOf_stores (hg : Legal L R g) : Stores (pos nL) (prOf nL nR (wordOf g)) g.pair := by
  intro z
  cases z with
  | inl i =>
      rw [prOf, show pos nL (.inl i : Fin nL ⊕ Fin nR) = (i : ℕ) from rfl,
        getN_append_left (by simp), getN_map_range _ i.2]
      rcases pair_inl_cases hg i with h | ⟨j, h⟩
      · rw [wordOf_fixed i h, h]; rfl
      · rw [wordOf_shared i h, h]; simp [pos]
  | inr j =>
      rw [prOf, getN_append_right (by simp [pos]), List.length_map, List.length_range,
        pos_inr_sub, getN_map_range _ j.2]
      rcases pair_inr_cases hg j with h | ⟨i, h⟩
      · have hnot : ¬ (j + 1 : ℕ) ∈ wordOf g := by
          rw [mem_wordOf_iff hg]
          rintro ⟨i, hi⟩
          rw [(pair_inl_eq_inr_iff hg i j).mp hi] at h
          exact Sum.inl_ne_inr h
        rw [h, ite_eq_right (by rwa [List.contains_iff_mem])]
        rfl
      · have hi := (pair_inl_eq_inr_iff hg i j).mpr h
        rw [ite_eq_left (List.contains_iff_mem.mpr ((mem_wordOf_iff hg j).mpr ⟨i, hi⟩)),
          idxOf_wordOf hg hi, h]
        rfl

theorem validM_wordOf (hL : Represents fL L) (hR : Represents fR R) (hg : Legal L R g) :
    validM fL fR (wordOf g) = true := by
  simp only [validM, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, Bool.or_eq_true,
    beq_iff_eq, bne_iff_ne, ne_eq, List.mem_range, hL.dim]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [nodupB_iff, wordOf, List.filter_map]
    refine List.Nodup.map_on ?_ ((List.nodup_finRange nL).filter _)
    intro x hx y hy hxy
    have hx' := (List.mem_filter.mp hx).2
    simp only [Function.comp_apply, bne_iff_ne, ne_eq] at hx'
    rcases pair_inl_cases hg x with h | ⟨j, h⟩
    · simp [h] at hx'
    · rcases pair_inl_cases hg y with h' | ⟨j', h'⟩
      · simp [h'] at hxy; simp [h] at hxy
      · simp only [h, h'] at hxy
        have hj : j = j' := Fin.ext (by omega)
        subst hj
        have := g.pair.injective (h.trans h'.symm)
        simpa using this
  · obtain ⟨x, hx⟩ := hg.shared
    cases x with
    | inl i =>
        rcases pair_inl_cases hg i with h | ⟨j, h⟩
        · exact absurd h hx
        · exact ⟨j + 1, List.mem_map.mpr ⟨i, List.mem_finRange i, by simp [h]⟩, by omega⟩
    | inr j =>
        rcases pair_inr_cases hg j with h | ⟨i, h⟩
        · exact absurd h hx
        · exact ⟨j + 1, (mem_wordOf_iff hg j).mpr ⟨i, (pair_inl_eq_inr_iff hg i j).mpr h⟩,
            by omega⟩
  · intro i hi
    rcases pair_inl_cases hg ⟨i, hi⟩ with h | ⟨j, h⟩
    · left; exact wordOf_fixed ⟨i, hi⟩ h
    · right
      have hw : getN (wordOf g) i = j + 1 := wordOf_shared ⟨i, hi⟩ h
      rw [hw, Nat.add_sub_cancel, hL.two ⟨i, hi⟩, hR.two j]
      have hdeg := hg.degree (.inl ⟨i, hi⟩) (by rw [h]; exact Sum.inr_ne_inl)
      rw [h] at hdeg
      simp only [twoOf] at hdeg
      rcases hdeg with hd | hd <;> simp [hd]

open Classical in
/-- The orientation word of a descriptor: at the left end of an open shared
vertex, whether the right mark is the kept one. -/
noncomputable def orientOf (L : Code nL) (R : Code nR) (g : Glue nL nR nP) : List Bool :=
  (List.finRange nL).map fun i =>
    decide (g.pair (.inl i) ≠ .inl i ∧ OpenAt L R g (.inl i) ∧ g.pair (.inl i) ∈ Set.range g.keep)

variable {pr : List ℕ}

theorem openF_pos (hL : Represents fL L) (hR : Represents fR R) (hpr : Stores (pos nL) pr g.pair)
    (z : Fin nL ⊕ Fin nR) :
    openF fL fR pr (pos nL z) = true ↔ g.pair z ≠ z ∧ OpenAt L R g z := by
  simp only [openF, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true']
  rw [getN_pr_eq_iff hpr, hpr z, twoAt_pos hL hR, twoAt_pos hL hR]
  simp only [OpenAt]
  tauto

theorem openAt_symm (hg : Legal L R g) (z : Fin nL ⊕ Fin nR) :
    OpenAt L R g (g.pair z) ↔ OpenAt L R g z := by
  simp only [OpenAt, hg.pair_invol]
  tauto

theorem keptF_pos (hL : Represents fL L) (hR : Represents fR R) (hg : Legal L R g)
    (hpr : Stores (pos nL) pr g.pair) (z : Fin nL ⊕ Fin nR) :
    keptF fL fR pr (orientOf L R g) (pos nL z) = true ↔ z ∈ Set.range g.keep := by
  classical
  have hopen := openF_pos hL hR hpr z
  simp only [keptF, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true]
  rw [getN_pr_eq_iff hpr]
  by_cases hfix : g.pair z = z
  · simp only [hfix, true_or, true_iff]
    exact hg.keep_fixed z hfix
  · by_cases hop : OpenAt L R g z
    · have hopF : openF fL fR pr (pos nL z) = true := hopen.mpr ⟨hfix, hop⟩
      simp only [hfix, false_or, hopF, true_and]
      cases z with
      | inl i =>
          have hlt : pos nL (.inl i : Fin nL ⊕ Fin nR) < fL.n := by
            rw [hL.dim]; exact i.2
          rw [ite_eq_left hlt, show pos nL (.inl i : Fin nL ⊕ Fin nR) = (i : ℕ) from rfl, orientOf,
            getB, getD_map_finRange, Bool.not_eq_true', decide_eq_false_iff_not]
          have hk := hg.keep_open (.inl i) hfix hop
          constructor
          · intro h
            exact hk.mpr (fun hm => h ⟨hfix, hop, hm⟩)
          · intro h ⟨_, _, hm⟩
            exact hk.mp h hm
      | inr j =>
          have hnlt : ¬ pos nL (.inr j : Fin nL ⊕ Fin nR) < fL.n := by
            rw [hL.dim]; exact pos_inr_not_lt j
          rcases pair_inr_cases hg j with h | ⟨i, h⟩
          · exact absurd h hfix
          · rw [ite_eq_right hnlt, hpr, h, show pos nL (.inl i : Fin nL ⊕ Fin nR) = (i : ℕ) from rfl,
              orientOf, getB, getD_map_finRange, decide_eq_true_iff]
            have hi := (pair_inl_eq_inr_iff hg i j).mpr h
            have hop' : OpenAt L R g (.inl i) := by
              rw [← h]; exact (openAt_symm hg _).mpr hop
            rw [hi]
            constructor
            · exact fun h => h.2.2
            · exact fun hm => ⟨Sum.inr_ne_inl, hop', hm⟩
    · have hopF : ¬ openF fL fR pr (pos nL z) = true := fun h => hop (hopen.mp h).2
      simp only [hfix, false_or, hopF, Bool.false_eq_true, false_and, false_iff]
      exact hg.keep_closed z hfix hop

theorem orientOf_mem (hL : Represents fL L) (hR : Represents fR R)
    (hpr : Stores (pos nL) pr g.pair) : orientOf L R g ∈ orients fL fR pr := by
  classical
  simp only [orients, List.mem_filter, mem_boolLists, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_true']
  refine ⟨by simp [orientOf, hL.dim], ?_⟩
  intro i hi
  rw [hL.dim] at hi
  by_cases h : getB (orientOf L R g) i = true
  · right
    rw [orientOf, getB, show i = ((⟨i, hi⟩ : Fin nL) : ℕ) from rfl, getD_map_finRange,
      decide_eq_true_iff] at h
    exact (openF_pos hL hR hpr (.inl ⟨i, hi⟩)).mpr ⟨h.1, h.2.1⟩
  · left; simpa using h

/-- A duplicate-free list of the kept marks lists them in some order. -/
theorem exists_relabel_of_marks (marks : List ℕ) (hnd : marks.Nodup)
    (hmem : ∀ x, x ∈ marks ↔ ∃ k, pos nL (g.keep k) = x) :
    ∃ σ : Fin nP ≃ Fin nP,
      marks = (List.finRange nP).map fun k => pos nL ((g.relabel σ).keep k) := by
  classical
  let f : Fin nP → ℕ := fun k => pos nL (g.keep k)
  have hf : Function.Injective f := pos_injective.comp g.keep.injective
  have hlen : marks.length = nP := by
    rw [← List.toFinset_card_of_nodup hnd]
    have : marks.toFinset = Finset.univ.image f := by
      ext x
      simp only [List.mem_toFinset, hmem, Finset.mem_image, Finset.mem_univ, true_and, f]
    rw [this, Finset.card_image_of_injective _ hf, Finset.card_univ, Fintype.card_fin]
  have htl : ∀ t : Fin nP, (t : ℕ) < marks.length := fun t => by rw [hlen]; exact t.2
  have hex : ∀ t : Fin nP, ∃ k, pos nL (g.keep k) = marks[(t : ℕ)]'(htl t) :=
    fun t => (hmem _).mp (List.getElem_mem (htl t))
  let σf : Fin nP → Fin nP := fun t => (hex t).choose
  have hσ : ∀ t, f (σf t) = marks[(t : ℕ)]'(htl t) := fun t => (hex t).choose_spec
  have hinj : Function.Injective σf := by
    intro a b hab
    have := (hσ a).symm.trans ((congrArg f hab).trans (hσ b))
    exact Fin.ext ((hnd.getElem_inj_iff).mp this)
  refine ⟨Equiv.ofBijective σf (Finite.injective_iff_bijective.mp hinj), ?_⟩
  apply List.ext_getElem
  · simp [hlen]
  · intro t h1 h2
    simp only [List.getElem_map, List.getElem_finRange]
    exact (hσ ⟨t, hlen ▸ h1⟩).symm

theorem eulerF_of_euler (hL : Represents fL L) (hR : Represents fR R)
    (hpr : Stores (pos nL) pr g.pair) (he : Euler L R g) : eulerF fL fR pr = true := by
  have hval : ∀ n, Function.Injective (fun i : Fin n => (i : ℕ)) := fun n => Fin.val_injective
  have hrng : ∀ n x, x < n ↔ ∃ i : Fin n, (i : ℕ) = x :=
    fun n x => ⟨fun h => ⟨⟨x, h⟩, rfl⟩, fun ⟨i, hi⟩ => hi ▸ i.2⟩
  have hLs : Stores (fun i : Fin nL => (i : ℕ)) fL.ret L.ret := fun i => hL.ret i
  have hRs : Stores (fun i : Fin nR => (i : ℕ)) fR.ret R.ret := fun i => hR.ret i
  have hst : Stores (pos nL) (compList fL fR pr) (merged L R * g.pair) := by
    intro z
    rw [compList, hL.dim, hR.dim, getN_map_range _ (pos_lt z), hpr z, retAt_pos hL hR]
    rfl
  have hshared : sharedF nL pr = sharedCount g := by
    rw [sharedF, length_filter_range (hval nL) (hrng nL), sharedCount]
    congr 1
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, bne_iff_ne, ne_eq]
    rw [show ((i : ℕ)) = pos nL (.inl i : Fin nL ⊕ Fin nR) from rfl, getN_pr_eq_iff hpr]
  simp only [eulerF, beq_iff_eq, hL.dim, hR.dim]
  rw [hshared, cycF_stores (hval nL) (hrng nL) hLs, cycF_stores (hval nR) (hrng nR) hRs,
    cycF_stores pos_injective pos_range hst]
  exact he

/-- **Every legal planar fork is enumerated**, up to the order of its kept
marks. -/
theorem exists_mem_forksOf {bound : ℕ} (hL : Represents fL L) (hR : Represents fR R)
    (hg : Legal L R g) (he : Euler L R g) (hb : nP ≤ bound) :
    ∃ σ : Fin nP ≃ Fin nP, ∃ q ∈ forksOf bound fL fR, Represents q ((fork L R g).relabel σ) := by
  have hpr := prOf_stores hg
  set pr := prOf nL nR (wordOf g) with hprdef
  set o := orientOf L R g
  set marks := marksOf fL fR pr o with hmarksdef
  have hnd : marks.Nodup := List.nodup_range.filter _
  have hmem : ∀ x, x ∈ marks ↔ ∃ k, pos nL (g.keep k) = x := by
    intro x
    rw [hmarksdef, marksOf, List.mem_filter, List.mem_range, hL.dim, hR.dim]
    constructor
    · rintro ⟨hx, hk⟩
      obtain ⟨z, rfl⟩ := (pos_range x).mp hx
      obtain ⟨k, rfl⟩ := (keptF_pos hL hR hg hpr z).mp hk
      exact ⟨k, rfl⟩
    · rintro ⟨k, rfl⟩
      exact ⟨pos_lt _, (keptF_pos hL hR hg hpr _).mpr ⟨k, rfl⟩⟩
  obtain ⟨σ, hσ⟩ := exists_relabel_of_marks marks hnd hmem
  have hlen : marks.length = nP := marks_length hσ
  refine ⟨σ, flatFork fL fR pr marks, ?_, ?_⟩
  · simp only [forksOf, List.mem_flatMap, List.mem_filter]
    refine ⟨wordOf g, ⟨?_, validM_wordOf hL hR hg⟩, ?_⟩
    · rw [mem_words, hL.dim, hR.dim]
      refine ⟨length_wordOf, fun x hx => ?_⟩
      obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
      rcases pair_inl_cases hg i with h | ⟨j, h⟩
      · simp [h]
      · simp only [h]; omega
    · rw [hL.dim, hR.dim, ← hprdef, ite_eq_left (eulerF_of_euler hL hR hpr he)]
      refine List.mem_filterMap.mpr ⟨o, orientOf_mem hL hR hpr, ?_⟩
      rw [← hmarksdef, ite_eq_left (hlen ▸ hb)]
  · rw [← fork_relabel]
    exact represents_flatFork hL hR (g := g.relabel σ) hpr hσ (legal_relabel σ hg)

end Complete

/-! ## The checker and the audit -/

/-- A flat fork is accepted when it is a root which is not rejecting, or when
its canonical form is in `C`. -/
def pairOk (bound : ℕ) (C : List FCode) (L R : FCode) : Bool :=
  (forksOf bound L R).all fun q => if q.n == 0 then !rejectingF q else C.contains (canon q)

def pageOk (bound : ℕ) (C : List FCode) (L : FCode) : Bool := C.all (pairOk bound C L)

def leafOk (C : List FCode) : Bool := C.contains (canon leafF)

def rootsOk (C : List FCode) : Bool := C.all fun c => c.n != 0 || !rejectingF c

theorem legal_children_pos {nL nR nP : ℕ} {L : Code nL} {R : Code nR} {g : Glue nL nR nP}
    (hg : Legal L R g) : 0 < nL ∧ 0 < nR := by
  obtain ⟨x, hx⟩ := hg.shared
  cases x with
  | inl i =>
      rcases hg.pair_left i with h | ⟨j, _⟩
      · exact absurd h hx
      · exact ⟨Nat.pos_of_ne_zero (fun h0 => (h0 ▸ i).elim0), Nat.pos_of_ne_zero
          (fun h0 => (h0 ▸ j).elim0)⟩
  | inr j =>
      rcases hg.pair_right j with h | ⟨i, _⟩
      · exact absurd h hx
      · exact ⟨Nat.pos_of_ne_zero (fun h0 => (h0 ▸ i).elim0), Nat.pos_of_ne_zero
          (fun h0 => (h0 ▸ j).elim0)⟩

/-- **Soundness of the checker.**  Every code of the closure is stored, up to
renaming, by a member of `C` or by a root which is not rejecting. -/
theorem reach_stored {bound : ℕ} {C : List FCode} (hleaf : leafOk C = true)
    (hpages : ∀ L ∈ C, pageOk bound C L = true) {n : ℕ} {c : Code n} (h : Reach bound n c) :
    ∃ f : FCode, ∃ τ : Fin n ≃ Fin n, Represents f (c.relabel τ) ∧
      (f ∈ C ∨ (f.n = 0 ∧ rejectingF f = false)) := by
  induction h with
  | leaf =>
      obtain ⟨τ, hτ⟩ := represents_canon represents_leaf
      exact ⟨canon leafF, τ, hτ, Or.inl (List.contains_iff_mem.mp hleaf)⟩
  | @fork nL nR nP L R g _ _ hlegal heuler hbound ihL ihR =>
      obtain ⟨hnL, hnR⟩ := legal_children_pos hlegal
      obtain ⟨fL, τL, hL, hfL⟩ := ihL
      obtain ⟨fR, τR, hR, hfR⟩ := ihR
      replace hfL : fL ∈ C := hfL.resolve_right (fun h => by have := hL.dim; have := h.1; omega)
      replace hfR : fR ∈ C := hfR.resolve_right (fun h => by have := hR.dim; have := h.1; omega)
      have hLb : (L.relabel τL).relabel τL.symm = L := Code.relabel_symm L τL
      have hRb : (R.relabel τR).relabel τR.symm = R := Code.relabel_symm R τR
      have hfork : fork L R g =
          fork (L.relabel τL) (R.relabel τR) (g.transport τL.symm τR.symm) := by
        rw [← fork_relabel_children τL.symm τR.symm, hLb, hRb]
      have hlegal' : Legal (L.relabel τL) (R.relabel τR) (g.transport τL.symm τR.symm) :=
        legal_transport τL.symm τR.symm _ _ g (by rw [hLb, hRb]; exact hlegal)
      have heuler' : Euler (L.relabel τL) (R.relabel τR) (g.transport τL.symm τR.symm) :=
        euler_transport τL.symm τR.symm _ _ g (by rw [hLb, hRb]; exact heuler)
      obtain ⟨σ, q, hq, hrep⟩ := exists_mem_forksOf hL hR hlegal' heuler' hbound
      have hpair := List.all_eq_true.mp ((List.all_eq_true.mp (hpages fL hfL)) fR hfR) q hq
      rw [← hfork] at hrep
      by_cases h0 : q.n = 0
      · rw [ite_eq_left (beq_iff_eq.mpr h0), Bool.not_eq_true'] at hpair
        exact ⟨q, σ, hrep, Or.inr ⟨h0, hpair⟩⟩
      · rw [ite_eq_right (by simpa using h0)] at hpair
        obtain ⟨π, hπ⟩ := represents_canon hrep
        refine ⟨canon q, π.trans σ, ?_, Or.inl (List.contains_iff_mem.mp hpair)⟩
        rw [← Code.relabel_relabel]
        exact hπ

/-- **The audit from the checks.** -/
theorem audit_of_checks {bound : ℕ} {C : List FCode} (hleaf : leafOk C = true)
    (hpages : ∀ L ∈ C, pageOk bound C L = true) (hroots : rootsOk C = true) : Audit bound := by
  intro c hc hrej
  obtain ⟨f, τ, hrep, hf⟩ := reach_stored hleaf hpages hc
  rw [Subsingleton.elim τ (Equiv.refl _), Code.relabel_refl] at hrep
  have hbad : rejectingF f = true := (rejecting_of_represents hrep).mpr hrej
  rcases hf with hf | ⟨_, hf⟩
  · have hroot := List.all_eq_true.mp hroots f hf
    rw [hrep.dim, hbad] at hroot
    simp at hroot
  · rw [hbad] at hf
    exact Bool.noConfusion hf

/-- The pages of a list, indexed by position. -/
theorem forall_mem_of_getD {C : List FCode} {P : FCode → Prop}
    (h : ∀ i < C.length, P (C.getD i leafF)) : ∀ L ∈ C, P L := by
  intro L hL
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hL
  have := h i hi
  rwa [List.getD_eq_getElem _ _ hi] at this

/-! ## Certificates -/

/-- Decode a list of flat codes, each written as its number of positions, its
flags, its return, and its colour and cut lists preceded by their lengths. -/
def decodeCodes : ℕ → List ℕ → List FCode
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, n :: rest =>
      let body := rest.drop (n + n)
      let cutPart := body.drop (1 + body.headD 0)
      ⟨n, (rest.take n).map (· == 1), (rest.drop n).take n, (body.drop 1).take (body.headD 0),
        (cutPart.drop 1).take (cutPart.headD 0)⟩ ::
        decodeCodes fuel (cutPart.drop (1 + cutPart.headD 0))

/-- The canonical forms of the decoded codes. -/
def certCodes (cert : List ℕ) : List FCode := (decodeCodes cert.length cert).map canon

end Mettapedia.GraphTheory.FourColor.PhysicalForkCodeFlat
