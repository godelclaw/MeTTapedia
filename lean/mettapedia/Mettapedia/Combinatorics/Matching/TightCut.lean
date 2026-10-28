import Mathlib
import Mettapedia.Combinatorics.Matching.Sum

/-!
# Collapsing one side of a cut

Split the sites into a kept set `S` and its complement.  The perfect matchings that cross the cut
around `S` exactly once are counted by

  `crossOne W S c = ∑ s ∈ S, ∑ t ∉ S, pmSum(S \ s) · W(s, t) · pmSum(Sᶜ \ t)`.

Collapse the complement to a single site `none` whose colour `k` stands for the constant
colouring `k` of the complement.  The collapsed site reaches a kept site `s`, coloured `a`, with
weight

  `∑ t ∉ S, W((s, a), (t, k)) · pmSum_k(Sᶜ \ t)`,

and edges among the kept sites are left alone.  The matching sum of the collapsed system is then
exactly `crossOne` (`amplitude_shoreContract`).

So whenever the matchings that cross the cut more than once contribute nothing — for instance
when the cut is tight, crossed exactly once by every matching of the edges that carry weight —
collapsing loses nothing.  The amplitudes of the colourings that are constant off `S` become those
of a system on `|S| + 1` sites.  A matching of the collapsed system uses the collapsed site once;
tightness says the original matchings used the cut once, so the two counts agree term by term.
Nothing here depends on the characteristic.
-/

namespace MatchingTightCut

open Amplitude MatchingSum

variable {V C : Type*} [Fintype V] [DecidableEq V] {R : Type*} [CommSemiring R]

/-- The part of a matching sum carried by the matchings that cross the cut around `S` exactly
once: a single kept site `s` is matched out, to a site `t` of the complement. -/
def crossOne (W : Sym2 (V × C) → R) (S : Finset V) (c : V → C) : R :=
  ∑ s ∈ S, ∑ t ∈ Finset.univ \ S,
    pmSum W c (S.erase s) * W (Sym2.map (paint c) s(s, t)) *
      pmSum W c ((Finset.univ \ S).erase t)

/-- The colouring equal to `cS` on `S` and constant `k` off it. -/
def glue (S : Finset V) (cS : ↥S → C) (k : C) : V → C :=
  fun v => if h : v ∈ S then cS ⟨v, h⟩ else k

omit [Fintype V] in
theorem glue_of_mem {S : Finset V} (cS : ↥S → C) (k : C) {v : V} (hv : v ∈ S) :
    glue S cS k v = cS ⟨v, hv⟩ := by
  simp [glue, hv]

omit [Fintype V] in
theorem glue_of_not_mem {S : Finset V} (cS : ↥S → C) (k : C) {v : V} (hv : v ∉ S) :
    glue S cS k v = k := by
  simp [glue, hv]

/-- The weight with which the collapsed complement, coloured `k`, reaches the kept site `s`
coloured `a`. -/
def shoreWeight (W : Sym2 (V × C) → R) (S : Finset V) (s : V) (a k : C) : R :=
  ∑ t ∈ Finset.univ \ S,
    W s((s, a), (t, k)) * pmSum W (fun _ => k) ((Finset.univ \ S).erase t)

/-- The weights of the collapsed system, as a function of two coloured sites. -/
def shoreFun (W : Sym2 (V × C) → R) (S : Finset V) : Option ↥S × C → Option ↥S × C → R
  | (some s, a), (some s', b) => W s(((s : V), a), ((s' : V), b))
  | (some s, a), (none, k) => shoreWeight W S s a k
  | (none, k), (some s, a) => shoreWeight W S s a k
  | (none, _), (none, _) => 0

/-- **The collapsed system.**  Edges among the kept sites are unchanged; the collapsed site
`none` reaches each kept site with its `shoreWeight`. -/
def shoreContract (W : Sym2 (V × C) → R) (S : Finset V) : Sym2 (Option ↥S × C) → R :=
  Sym2.lift ⟨shoreFun W S, fun x y => by
    rcases x with ⟨_ | s, a⟩ <;> rcases y with ⟨_ | s', b⟩
    · rfl
    · rfl
    · rfl
    · exact congrArg W (Sym2.eq_swap)⟩

@[simp] theorem shoreContract_some_some (W : Sym2 (V × C) → R) (S : Finset V) (s s' : ↥S)
    (a b : C) :
    shoreContract W S s((some s, a), (some s', b)) = W s(((s : V), a), ((s' : V), b)) := rfl

@[simp] theorem shoreContract_none_some (W : Sym2 (V × C) → R) (S : Finset V) (s : ↥S)
    (a k : C) :
    shoreContract W S s((none, k), (some s, a)) = shoreWeight W S s a k := rfl

@[simp] theorem shoreContract_some_none (W : Sym2 (V × C) → R) (S : Finset V) (s : ↥S)
    (a k : C) :
    shoreContract W S s((some s, a), (none, k)) = shoreWeight W S s a k := rfl

/-- **Among the kept sites the collapsed system is the original one.** -/
theorem pmSum_shoreContract_some (W : Sym2 (V × C) → R) (S : Finset V) (cS : ↥S → C) (k : C)
    (T : Finset ↥S) :
    pmSum (shoreContract W S) (fun o => o.elim k cS) (T.map Function.Embedding.some)
      = pmSum W (glue S cS k) (T.map (Function.Embedding.subtype (· ∈ S))) := by
  classical
  rw [pmSum_restrict_map]
  have hglue : (fun u : ↥S => glue S cS k (u : V)) = cS := by
    funext u
    exact glue_of_mem cS k u.2
  rw [hglue]
  have hmap : ∀ (T' : Finset ↥S) (a : ↥S),
      (T'.map Function.Embedding.some).erase (Function.Embedding.some a)
        = (T'.erase a).map Function.Embedding.some :=
    fun T' a => (Finset.map_erase Function.Embedding.some T' a).symm
  refine eq_pmSum_of_rec (restrictW W S) cS
    (fun T => pmSum (shoreContract W S) (fun o => o.elim k cS)
      (T.map Function.Embedding.some)) ?_ ?_ T
  · simp [pmSum_empty]
  · intro T' hT'
    obtain ⟨u, hu⟩ := hT'
    refine ⟨u, hu, ?_⟩
    have hmem : Function.Embedding.some u ∈ T'.map Function.Embedding.some :=
      Finset.mem_map_of_mem _ hu
    rw [pmSum_expand _ _ hmem, hmap T' u, Finset.sum_map]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [hmap (T'.erase u) v]
    rfl

/-- **The collapsed system counts the single crossings.**  Its matching sum, at kept colouring
`cS` and collapsed colour `k`, is the part of the original matching sum — at the colouring equal
to `cS` on `S` and constant `k` off it — carried by the matchings that cross the cut once. -/
theorem amplitude_shoreContract (W : Sym2 (V × C) → R) (S : Finset V) (cS : ↥S → C) (k : C) :
    amplitude (shoreContract W S) (fun o => o.elim k cS) = crossOne W S (glue S cS k) := by
  classical
  rw [← pmSum_univ, pmSum_expand _ _ (Finset.mem_univ none)]
  have huniv : (Finset.univ : Finset (Option ↥S)).erase none
      = (Finset.univ : Finset ↥S).map Function.Embedding.some := by
    ext o
    cases o <;> simp
  rw [huniv, Finset.sum_map, crossOne, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [← Finset.map_erase, pmSum_shoreContract_some]
  have hS : ((Finset.univ : Finset ↥S).erase s).map (Function.Embedding.subtype (· ∈ S))
      = S.erase s := by
    ext v
    constructor
    · intro hv
      obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hv
      exact Finset.mem_erase.mpr ⟨fun h => (Finset.mem_erase.mp hu).1 (Subtype.ext h), u.2⟩
    · intro hv
      obtain ⟨hvs, hvS⟩ := Finset.mem_erase.mp hv
      exact Finset.mem_map.mpr ⟨⟨v, hvS⟩,
        Finset.mem_erase.mpr ⟨fun h => hvs (congrArg Subtype.val h), Finset.mem_univ _⟩, rfl⟩
  rw [hS]
  show shoreWeight W S s (cS s) k * pmSum W (glue S cS k) (S.erase s) = _
  rw [shoreWeight, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t ht => ?_
  have htS : t ∉ S := (Finset.mem_sdiff.mp ht).2
  have hcol : pmSum W (fun _ => k) ((Finset.univ \ S).erase t)
      = pmSum W (glue S cS k) ((Finset.univ \ S).erase t) :=
    pmSum_congr_colour W (fun x hx =>
      (glue_of_not_mem cS k (Finset.mem_sdiff.mp (Finset.mem_of_mem_erase hx)).2).symm)
  have hw : W (Sym2.map (paint (glue S cS k)) s((s : V), t)) = W s(((s : V), cS s), (t, k)) := by
    show W s(((s : V), glue S cS k s), (t, glue S cS k t)) = _
    rw [glue_of_mem cS k s.2, glue_of_not_mem cS k htS]
  rw [hcol, hw]
  ring

/-! ### Three-site shores

When one side of the cut has three sites, a matching crosses it once or three times.  If one of
the three sites has no weight across the cut at the colouring in question, three crossings are
impossible, so the matching sum is exactly its single-crossing part.  This is the criterion the
applications use to recognise a shore-tight cut from the weights that vanish. -/

/-- The single-crossing sum is symmetric in the two sides of the cut. -/
theorem crossOne_compl (W : Sym2 (V × C) → R) (S : Finset V) (c : V → C) :
    crossOne W (Finset.univ \ S) c = crossOne W S c := by
  classical
  have hSS : Finset.univ \ (Finset.univ \ S) = S :=
    Finset.sdiff_sdiff_eq_self (Finset.subset_univ S)
  rw [crossOne, crossOne, hSS, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => Finset.sum_congr rfl fun s _ => ?_
  rw [show Sym2.map (paint c) s(t, s) = Sym2.map (paint c) s(s, t) by rw [Sym2.eq_swap]]
  ring

/-- **A dead site on a three-site shore.**  If the site `a` of the three-site set `K = {a, b, d}`
carries no weight across the cut at `c`, the matching sum is its single-crossing part. -/
theorem amplitude_eq_crossOne_of_dead (W : Sym2 (V × C) → R) (c : V → C) {a b d : V}
    (hab : a ≠ b) (had : a ≠ d) (hbd : b ≠ d)
    (hdead : ∀ v, v ≠ a → v ≠ b → v ≠ d → W (Sym2.map (paint c) s(a, v)) = 0) :
    amplitude W c = crossOne W {a, b, d} c := by
  classical
  set K : Finset V := {a, b, d} with hK
  set O : Finset V := Finset.univ \ K with hO
  have hmemO : ∀ v, v ∈ O ↔ v ≠ a ∧ v ≠ b ∧ v ≠ d := by
    intro v; simp [hO, hK, not_or]
  have hdO : d ∉ O := fun h => ((hmemO d).mp h).2.2 rfl
  have hbO' : b ∉ O := fun h => ((hmemO b).mp h).2.1 rfl
  -- expand the amplitude at the dead site
  rw [← pmSum_univ, pmSum_expand W c (Finset.mem_univ a)]
  have hsplit : (Finset.univ : Finset V).erase a = insert b (insert d O) := by
    ext v
    simp only [Finset.mem_erase, Finset.mem_univ, and_true, Finset.mem_insert, hmemO]
    constructor
    · intro hva
      by_cases hvb : v = b
      · exact Or.inl hvb
      · by_cases hvd : v = d
        · exact Or.inr (Or.inl hvd)
        · exact Or.inr (Or.inr ⟨hva, hvb, hvd⟩)
    · rintro (rfl | rfl | ⟨h, -, -⟩)
      · exact Ne.symm hab
      · exact Ne.symm had
      · exact h
  have hbO : b ∉ insert d O := by
    rw [Finset.mem_insert, not_or]
    exact ⟨hbd, hbO'⟩
  rw [hsplit, Finset.sum_insert hbO, Finset.sum_insert hdO,
    Finset.sum_eq_zero (fun v hv => by
      obtain ⟨h1, h2, h3⟩ := (hmemO v).mp hv
      rw [hdead v h1 h2 h3, zero_mul]), add_zero]
  rw [Finset.erase_insert hbO, Finset.erase_insert_of_ne hbd, Finset.erase_insert hdO,
    pmSum_expand W c (Finset.mem_insert_self d O), Finset.erase_insert hdO,
    pmSum_expand W c (Finset.mem_insert_self b O), Finset.erase_insert hbO']
  -- the single-crossing sum, read from the side of `K`
  rw [crossOne, ← hO]
  have hKsum : K = insert a (insert b {d}) := by simp [hK]
  have ha' : a ∉ insert b ({d} : Finset V) := by simp [hab, had]
  have hb' : b ∉ ({d} : Finset V) := by simp [hbd]
  rw [hKsum, Finset.sum_insert ha', Finset.sum_insert hb', Finset.sum_singleton]
  have hdeadO : ∀ o ∈ O, W (Sym2.map (paint c) s(a, o)) = 0 := fun o ho => by
    obtain ⟨h1, h2, h3⟩ := (hmemO o).mp ho
    exact hdead o h1 h2 h3
  have hA : ∑ t ∈ O, pmSum W c ((insert a (insert b ({d} : Finset V))).erase a) *
      W (Sym2.map (paint c) s(a, t)) * pmSum W c (O.erase t) = 0 :=
    Finset.sum_eq_zero (fun o ho => by rw [hdeadO o ho, mul_zero, zero_mul])
  rw [hA, zero_add]
  have e1 : (insert a (insert b ({d} : Finset V))).erase b = {a, d} := by
    ext v; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hvb, rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact absurd rfl hvb
      · exact Or.inr rfl
    · rintro (rfl | rfl)
      · exact ⟨hab, Or.inl rfl⟩
      · exact ⟨Ne.symm hbd, Or.inr (Or.inr rfl)⟩
  have e2 : (insert a (insert b ({d} : Finset V))).erase d = {a, b} := by
    ext v; simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hvd, rfl | rfl | rfl⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · exact absurd rfl hvd
    · rintro (rfl | rfl)
      · exact ⟨had, Or.inl rfl⟩
      · exact ⟨hbd, Or.inr (Or.inl rfl)⟩
  rw [e1, e2, pmSum_pair W c (Ne.symm had), pmSum_pair W c (Ne.symm hab), Finset.mul_sum,
    Finset.mul_sum, add_comm]
  congr 1
  · refine Finset.sum_congr rfl fun o _ => ?_
    show W s((a, c a), (d, c d)) * (W (Sym2.map (paint c) s(b, o)) * pmSum W c (O.erase o)) = _
    ring
  · refine Finset.sum_congr rfl fun o _ => ?_
    show W s((a, c a), (b, c b)) * (W (Sym2.map (paint c) s(d, o)) * pmSum W c (O.erase o)) = _
    ring

end MatchingTightCut
