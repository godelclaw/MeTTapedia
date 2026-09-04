import Mathlib

/-!
# Crossing parity for perfect matchings

A perfect matching pairs every vertex with a distinct partner, so it is exactly a
fixed-point-free involution.  The basic counting fact about such a pairing is
that any vertex set `s` is split into matched pairs lying wholly inside `s`,
which contribute two vertices each, and vertices whose partner escapes `s`,
which contribute one each.  Hence the number of matched pairs crossing the
boundary of `s` has the same parity as `|s|`.

In particular a perfect matching crosses an odd-sized vertex set an odd number of
times, which is why splitting a matching sum along an odd split leaves only the
odd crossing counts.  The statement is uniform in the vertex count, and needs no
finiteness assumption on the vertex type -- only the chosen vertex set is finite.
-/

namespace MatchingParity

variable {V : Type*} [DecidableEq V]

/-- A pairing of the vertices: a fixed-point-free involution.  This is the
standard encoding of a perfect matching, sending each vertex to its partner. -/
structure Pairing (V : Type*) where
  /-- The partner of a vertex. -/
  partner : V → V
  /-- Pairing is symmetric. -/
  partner_partner : ∀ x, partner (partner x) = x
  /-- No vertex is its own partner. -/
  partner_ne : ∀ x, partner x ≠ x

omit [DecidableEq V] in
/-- Restrict a pairing to a predicate invariant under its partner map. -/
def Pairing.subtype (pairing : Pairing V) (predicate : V → Prop)
    (closed : ∀ vertex, predicate vertex → predicate (pairing.partner vertex)) :
    Pairing {vertex // predicate vertex} where
  partner vertex :=
    ⟨pairing.partner vertex, closed vertex vertex.property⟩
  partner_partner vertex := by
    apply Subtype.ext
    exact pairing.partner_partner vertex
  partner_ne vertex hfixed := by
    apply pairing.partner_ne vertex
    exact congrArg Subtype.val hfixed

omit [DecidableEq V] in
@[simp]
theorem Pairing.subtype_partner_val (pairing : Pairing V)
    (predicate : V → Prop)
    (closed : ∀ vertex, predicate vertex → predicate (pairing.partner vertex))
    (vertex : {vertex // predicate vertex}) :
    ((pairing.subtype predicate closed).partner vertex).1 =
      pairing.partner vertex :=
  rfl

variable (M : Pairing V)

/-- A vertex set closed under the pairing splits into matched pairs, so it has
even cardinality. -/
theorem even_card_of_closed :
    ∀ s : Finset V, (∀ x ∈ s, M.partner x ∈ s) → Even s.card := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hs
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hpx : M.partner x ∈ s := hs x hx
      have hne : M.partner x ≠ x := M.partner_ne x
      set t : Finset V := (s.erase x).erase (M.partner x) with ht
      have hxt : x ∉ s.erase x := Finset.notMem_erase _ _
      have hsub : t ⊂ s := by
        refine Finset.ssubset_iff_of_subset (fun y hy => ?_) |>.mpr ⟨x, hx, ?_⟩
        · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
        · intro hmem
          exact hxt (Finset.mem_of_mem_erase hmem)
      have hclosed : ∀ y ∈ t, M.partner y ∈ t := by
        intro y hy
        have hy₁ : y ≠ M.partner x := Finset.ne_of_mem_erase hy
        have hy' := Finset.mem_of_mem_erase hy
        have hy₂ : y ≠ x := Finset.ne_of_mem_erase hy'
        have hys : y ∈ s := Finset.mem_of_mem_erase hy'
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hs y hys⟩⟩
        · intro h
          exact hy₂ (by rw [← M.partner_partner y, h, M.partner_partner])
        · intro h
          exact hy₁ (by rw [← h, M.partner_partner])
      have hcard : s.card = t.card + 2 := by
        have h1 : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
        have hpx' : M.partner x ∈ s.erase x :=
          Finset.mem_erase.mpr ⟨hne, hpx⟩
        have h2 : t.card = (s.erase x).card - 1 := Finset.card_erase_of_mem hpx'
        have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨x, hx⟩
        have hpos2 : 1 ≤ (s.erase x).card := Finset.card_pos.mpr ⟨_, hpx'⟩
        omega
      have := ih t hsub hclosed
      rw [hcard]
      exact this.add (even_iff_exists_two_nsmul _ |>.mpr ⟨1, rfl⟩)

/-- **Even cardinality from a local pairing.**  A set closed under an involution
that fixes none of its points has even cardinality.  The involution may fix points
elsewhere: only its behaviour on the set matters.  This is the form needed when a
matching is carried by a permutation of a larger vertex set. -/
theorem even_card_of_closed_of_involutive {f : V → V} (hf : ∀ x, f (f x) = x) :
    ∀ s : Finset V, (∀ x ∈ s, f x ∈ s) → (∀ x ∈ s, f x ≠ x) → Even s.card := by
  intro s
  induction s using Finset.strongInduction with
  | _ s ih =>
    intro hs hne
    rcases s.eq_empty_or_nonempty with rfl | ⟨x, hx⟩
    · simp
    · have hfx : f x ∈ s := hs x hx
      have hxne : f x ≠ x := hne x hx
      set t : Finset V := (s.erase x).erase (f x) with ht
      have hxt : x ∉ s.erase x := Finset.notMem_erase _ _
      have hsub : t ⊂ s := by
        refine Finset.ssubset_iff_of_subset (fun y hy => ?_) |>.mpr ⟨x, hx, ?_⟩
        · exact Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
        · intro hmem
          exact hxt (Finset.mem_of_mem_erase hmem)
      have hts : ∀ y ∈ t, y ∈ s := fun y hy =>
        Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hy)
      have hclosed : ∀ y ∈ t, f y ∈ t := by
        intro y hy
        have hy₁ : y ≠ f x := Finset.ne_of_mem_erase hy
        have hy₂ : y ≠ x := Finset.ne_of_mem_erase (Finset.mem_of_mem_erase hy)
        refine Finset.mem_erase.mpr ⟨?_, Finset.mem_erase.mpr ⟨?_, hs y (hts y hy)⟩⟩
        · intro h
          exact hy₂ (by rw [← hf y, h, hf])
        · intro h
          exact hy₁ (by rw [← h, hf])
      have hcard : s.card = t.card + 2 := by
        have h1 : (s.erase x).card = s.card - 1 := Finset.card_erase_of_mem hx
        have hfx' : f x ∈ s.erase x := Finset.mem_erase.mpr ⟨hxne, hfx⟩
        have h2 : t.card = (s.erase x).card - 1 := Finset.card_erase_of_mem hfx'
        have hpos : 1 ≤ s.card := Finset.card_pos.mpr ⟨x, hx⟩
        have hpos2 : 1 ≤ (s.erase x).card := Finset.card_pos.mpr ⟨_, hfx'⟩
        omega
      have := ih t hsub hclosed (fun y hy => hne y (hts y hy))
      rw [hcard]
      exact this.add (even_iff_exists_two_nsmul _ |>.mpr ⟨1, rfl⟩)

/-- The vertices of `s` whose partner lies outside `s`.  Each such vertex is one
endpoint of a distinct matched pair crossing the boundary, so this counts the
crossing pairs. -/
def crossing (s : Finset V) : Finset V := s.filter (fun x => M.partner x ∉ s)

/-- **Crossing parity.**  A perfect matching crosses a vertex set an odd number
of times exactly when that set is odd.  Uniform in the number of vertices. -/
theorem card_crossing_parity (s : Finset V) :
    (crossing M s).card % 2 = s.card % 2 := by
  have hsplit := Finset.card_filter_add_card_filter_not (s := s) (fun x => M.partner x ∈ s)
  have hin : Even (s.filter (fun x => M.partner x ∈ s)).card := by
    refine even_card_of_closed M _ (fun y hy => ?_)
    have hys : y ∈ s := Finset.mem_of_mem_filter _ hy
    have hpy : M.partner y ∈ s := (Finset.mem_filter.mp hy).2
    exact Finset.mem_filter.mpr ⟨hpy, by rw [M.partner_partner]; exact hys⟩
  obtain ⟨k, hk⟩ := hin
  simp only [crossing]
  omega



/-! ### Two pairings generate a dihedral action -/


/-- A pairing as a permutation of the vertices. -/
def Pairing.toPerm (σ : Pairing V) : Equiv.Perm V :=
  ⟨σ.partner, σ.partner, σ.partner_partner, σ.partner_partner⟩

omit [DecidableEq V] in
@[simp] lemma Pairing.toPerm_apply (σ : Pairing V) (x : V) : σ.toPerm x = σ.partner x := rfl

omit [DecidableEq V] in
/-- A pairing is an involution, so it is its own inverse. -/
@[simp] lemma Pairing.toPerm_inv (σ : Pairing V) : σ.toPerm⁻¹ = σ.toPerm := by
  ext x
  simp only [Equiv.Perm.inv_def, Pairing.toPerm, Equiv.coe_fn_mk, Equiv.coe_fn_symm_mk]

omit [DecidableEq V] in
/-- A pairing has order dividing two. -/
@[simp] lemma Pairing.toPerm_mul_self (σ : Pairing V) : σ.toPerm * σ.toPerm = 1 := by
  ext x
  simp [Pairing.toPerm, σ.partner_partner]

omit [DecidableEq V] in
/-- **The dihedral relation.**  Each pairing conjugates the composite of the two
to its inverse.  This is why the union of two perfect matchings decomposes into
cycles that either matching traverses in opposite directions. -/
theorem Pairing.conj_comp_eq_inv (σ τ : Pairing V) :
    σ.toPerm * (σ.toPerm * τ.toPerm) * σ.toPerm = (σ.toPerm * τ.toPerm)⁻¹ := by
  have h : σ.toPerm * σ.toPerm = 1 := σ.toPerm_mul_self
  calc σ.toPerm * (σ.toPerm * τ.toPerm) * σ.toPerm
      = (σ.toPerm * σ.toPerm) * τ.toPerm * σ.toPerm := by group
    _ = τ.toPerm * σ.toPerm := by rw [h, one_mul]
    _ = τ.toPerm⁻¹ * σ.toPerm⁻¹ := by rw [σ.toPerm_inv, τ.toPerm_inv]
    _ = (σ.toPerm * τ.toPerm)⁻¹ := (mul_inv_rev _ _).symm

/-- A set closed under both pairings has even cardinality.  This is the counting
half of the alternating-cycle decomposition, and it is the second client of
`even_card_of_closed` — the first being crossing parity. -/
theorem even_card_of_closed_pair (σ τ : Pairing V) {s : Finset V}
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (_hτ : ∀ x ∈ s, τ.partner x ∈ s) :
    Even s.card :=
  even_card_of_closed σ s hσ

omit [DecidableEq V] in
/-- An alternating cycle is closed under the composite walk, in both directions. -/
theorem comp_mem_of_closed (σ τ : Pairing V) {s : Finset V}
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s) :
    ∀ x ∈ s, (σ.toPerm * τ.toPerm) x ∈ s := by
  intro x hx
  simpa using hσ _ (hτ x hx)

/-! ### Alternating cycles need four vertices each

The symmetric difference of two perfect matchings is a disjoint union of
alternating cycles.  Each such cycle alternates between the two matchings, so it
has even length, and it cannot be a single shared edge -- so it spends at least
four vertices.  Everything in this section is proved from the involution laws
alone: no cycle machinery, no bound on the number of vertices, and no choice of
a traversal direction.

The consequence that matters for a uniform argument is a *lower* bound on the
vertex count needed to carry two independent alternating cycles.  Two of them
need eight vertices, so on six vertices any two perfect matchings differ along
exactly one cycle, and every statement about the number of alternating cycles is
silent there.  A hypothesis of that shape must be tested at eight.
-/

omit [DecidableEq V] in
/-- Disagreement propagates along the first matching: if a vertex is matched
differently by the two pairings, then so is its partner under `σ`.  This is what
makes the symmetric difference a union of whole cycles rather than loose ends. -/
theorem disagree_closed_left (σ τ : Pairing V) {x : V}
    (h : σ.partner x ≠ τ.partner x) :
    σ.partner (σ.partner x) ≠ τ.partner (σ.partner x) := by
  rw [σ.partner_partner]
  intro hx
  have h2 := congrArg τ.partner hx
  rw [τ.partner_partner] at h2
  exact h h2.symm

omit [DecidableEq V] in
/-- Disagreement propagates along the second matching too. -/
theorem disagree_closed_right (σ τ : Pairing V) {x : V}
    (h : σ.partner x ≠ τ.partner x) :
    σ.partner (τ.partner x) ≠ τ.partner (τ.partner x) := by
  rw [τ.partner_partner]
  intro hx
  have h2 : σ.partner (σ.partner (τ.partner x)) = σ.partner x := by rw [hx]
  rw [σ.partner_partner] at h2
  exact h h2.symm

/-- **An alternating cycle costs four vertices.**  Any vertex set closed under
both pairings which contains even one vertex they match differently already
contains four distinct vertices: the vertex, its two partners, and the far end of
the second step.  Uniform in the vertex count. -/
theorem four_le_card_of_closed_disagree (σ τ : Pairing V) {s : Finset V}
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s)
    {x : V} (hx : x ∈ s) (hne : σ.partner x ≠ τ.partner x) :
    4 ≤ s.card := by
  have hxa : x ≠ σ.partner x := fun h => σ.partner_ne x h.symm
  have hxb : x ≠ τ.partner x := fun h => τ.partner_ne x h.symm
  have hxc : x ≠ σ.partner (τ.partner x) := by
    intro h
    have h2 := congrArg σ.partner h
    rw [σ.partner_partner] at h2
    exact hne h2
  have hac : σ.partner x ≠ σ.partner (τ.partner x) := by
    intro h
    have h2 := congrArg σ.partner h
    rw [σ.partner_partner, σ.partner_partner] at h2
    exact τ.partner_ne x h2.symm
  have hbc : τ.partner x ≠ σ.partner (τ.partner x) :=
    fun h => σ.partner_ne (τ.partner x) h.symm
  have hsub :
      ({x, σ.partner x, τ.partner x, σ.partner (τ.partner x)} : Finset V) ⊆ s := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with rfl | rfl | rfl | rfl
    · exact hx
    · exact hσ x hx
    · exact hτ x hx
    · exact hσ _ (hτ x hx)
  have hcard :
      ({x, σ.partner x, τ.partner x, σ.partner (τ.partner x)} : Finset V).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [hxa, hxb, hxc]),
        Finset.card_insert_of_notMem (by simp [hne, hac]),
        Finset.card_insert_of_notMem (by simp [hbc]),
        Finset.card_singleton]
  exact hcard ▸ Finset.card_le_card hsub

/-- **Two alternating cycles cost eight vertices.**  Disjoint closed sets, each
carrying a disagreement, are each of size at least four. -/
theorem eight_le_card_union_of_two_disagreements (σ τ : Pairing V) {s t : Finset V}
    (hd : Disjoint s t)
    (hσs : ∀ x ∈ s, σ.partner x ∈ s) (hτs : ∀ x ∈ s, τ.partner x ∈ s)
    (hσt : ∀ x ∈ t, σ.partner x ∈ t) (hτt : ∀ x ∈ t, τ.partner x ∈ t)
    {x y : V} (hx : x ∈ s) (hy : y ∈ t)
    (hnex : σ.partner x ≠ τ.partner x) (hney : σ.partner y ≠ τ.partner y) :
    8 ≤ (s ∪ t).card := by
  have h1 := four_le_card_of_closed_disagree σ τ hσs hτs hx hnex
  have h2 := four_le_card_of_closed_disagree σ τ hσt hτt hy hney
  rw [Finset.card_union_of_disjoint hd]
  omega

/-- **Below eight vertices there is only one alternating cycle.**  On any vertex
set smaller than eight, two perfect matchings cannot disagree on two disjoint
closed pieces.  In particular six vertices cannot distinguish one alternating
cycle from several, so a hypothesis about how many cycles separate two matchings
has no six-vertex instance and must be tested at eight. -/
theorem not_two_disagreements_of_card_lt_eight [Fintype V]
    (hV : Fintype.card V < 8) (σ τ : Pairing V) {s t : Finset V}
    (hd : Disjoint s t)
    (hσs : ∀ x ∈ s, σ.partner x ∈ s) (hτs : ∀ x ∈ s, τ.partner x ∈ s)
    (hσt : ∀ x ∈ t, σ.partner x ∈ t) (hτt : ∀ x ∈ t, τ.partner x ∈ t)
    {x y : V} (hx : x ∈ s) (hy : y ∈ t)
    (hnex : σ.partner x ≠ τ.partner x) (hney : σ.partner y ≠ τ.partner y) :
    False := by
  have h := eight_le_card_union_of_two_disagreements σ τ hd hσs hτs hσt hτt hx hy hnex hney
  have hle : (s ∪ t).card ≤ Fintype.card V := Finset.card_le_univ _
  omega

/-- The vertices where two pairings choose different partners: the support of the
symmetric difference. -/
def disagree [Fintype V] (σ τ : Pairing V) : Finset V :=
  Finset.univ.filter (fun x => σ.partner x ≠ τ.partner x)

/-- The symmetric difference of two perfect matchings has even support: it is a
union of whole edges, never half of one. -/
theorem even_card_disagree [Fintype V] (σ τ : Pairing V) :
    Even (disagree σ τ).card := by
  refine even_card_of_closed σ _ (fun z hz => ?_)
  simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  exact disagree_closed_left σ τ hz

/-- Two distinct perfect matchings differ on at least four vertices. -/
theorem four_le_card_disagree [Fintype V] (σ τ : Pairing V)
    {x : V} (hne : σ.partner x ≠ τ.partner x) :
    4 ≤ (disagree σ τ).card := by
  refine four_le_card_of_closed_disagree σ τ (fun z hz => ?_) (fun z hz => ?_) ?_ hne
  · simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact disagree_closed_left σ τ hz
  · simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    exact disagree_closed_right σ τ hz
  · simp only [disagree, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hne

/-- **The alternating cycles between two matchings number at most a quarter of
the vertices.**  Any family of pairwise disjoint closed sets, each carrying a
disagreement between the two pairings, has at most `n / 4` members.  This is the
uniform form of the vertex cost: a hypothesis that counts alternating cycles has
no instance whatever until the vertex count reaches four times the count it
needs. -/
theorem four_mul_card_le_of_disjoint_disagreements [Fintype V] (σ τ : Pairing V)
    (C : Finset (Finset V))
    (hdisj : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t)
    (hσ : ∀ s ∈ C, ∀ x ∈ s, σ.partner x ∈ s)
    (hτ : ∀ s ∈ C, ∀ x ∈ s, τ.partner x ∈ s)
    (hdis : ∀ s ∈ C, ∃ x ∈ s, σ.partner x ≠ τ.partner x) :
    4 * C.card ≤ Fintype.card V := by
  classical
  have hcard : (C.biUnion id).card = ∑ s ∈ C, s.card :=
    Finset.card_biUnion (fun s hs t ht hst => hdisj s hs t ht hst)
  have hlow : 4 * C.card ≤ ∑ s ∈ C, s.card := by
    have : ∑ _s ∈ C, 4 ≤ ∑ s ∈ C, s.card := by
      refine Finset.sum_le_sum (fun s hs => ?_)
      obtain ⟨x, hx, hne⟩ := hdis s hs
      exact four_le_card_of_closed_disagree σ τ (hσ s hs) (hτ s hs) hx hne
    simpa [Finset.sum_const, mul_comm] using this
  have hub : (C.biUnion id).card ≤ Fintype.card V := Finset.card_le_univ _
  omega

/-- **Six vertices carry a single alternating cycle.**  Two perfect matchings on
six vertices cannot be separated into two independent alternating cycles, so the
number of cycles between them is never more than one.  Any conjecture phrased in
terms of that number is vacuous at six vertices and first acquires content at
eight. -/
theorem card_le_one_of_card_le_seven [Fintype V] (hV : Fintype.card V ≤ 7)
    (σ τ : Pairing V) (C : Finset (Finset V))
    (hdisj : ∀ s ∈ C, ∀ t ∈ C, s ≠ t → Disjoint s t)
    (hσ : ∀ s ∈ C, ∀ x ∈ s, σ.partner x ∈ s)
    (hτ : ∀ s ∈ C, ∀ x ∈ s, τ.partner x ∈ s)
    (hdis : ∀ s ∈ C, ∃ x ∈ s, σ.partner x ≠ τ.partner x) :
    C.card ≤ 1 := by
  have := four_mul_card_le_of_disjoint_disagreements σ τ C hdisj hσ hτ hdis
  omega

@[simp] lemma mem_disagree [Fintype V] (σ τ : Pairing V) (x : V) :
    x ∈ disagree σ τ ↔ σ.partner x ≠ τ.partner x := by
  simp [disagree]

/-- The disagreement set is closed under the first matching. -/
theorem disagree_closed_fst [Fintype V] (σ τ : Pairing V) :
    ∀ x ∈ disagree σ τ, σ.partner x ∈ disagree σ τ := by
  intro x hx
  rw [mem_disagree] at hx ⊢
  exact disagree_closed_left σ τ hx

/-- The disagreement set is closed under the second matching. -/
theorem disagree_closed_snd [Fintype V] (σ τ : Pairing V) :
    ∀ x ∈ disagree σ τ, τ.partner x ∈ disagree σ τ := by
  intro x hx
  rw [mem_disagree] at hx ⊢
  exact disagree_closed_right σ τ hx

/-! ### Exchange along a closed set

Given two perfect matchings and a set closed under both, follow the second
matching inside the set and the first outside it.  The result is again a perfect
matching.  This is the fundamental move of matching theory: every
alternating-cycle argument is an instance of it, and the closure hypothesis is
exactly what makes the two halves fit together into an involution.
-/

/-- **Exchange along a closed set.**  Follow `τ` inside `s`, `σ` outside. -/
def Pairing.exchange (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s) : Pairing V where
  partner := fun x => if x ∈ s then τ.partner x else σ.partner x
  partner_partner := by
    intro x
    by_cases hx : x ∈ s
    · rw [if_pos hx, if_pos (hτ x hx), τ.partner_partner]
    · have hnot : σ.partner x ∉ s := by
        intro hmem
        have := hσ _ hmem
        rw [σ.partner_partner] at this
        exact hx this
      rw [if_neg hx, if_neg hnot, σ.partner_partner]
  partner_ne := by
    intro x
    by_cases hx : x ∈ s
    · rw [if_pos hx]; exact τ.partner_ne x
    · rw [if_neg hx]; exact σ.partner_ne x

@[simp] theorem Pairing.exchange_of_mem (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s) {x : V} (hx : x ∈ s) :
    (σ.exchange τ s hσ hτ).partner x = τ.partner x := if_pos hx

@[simp] theorem Pairing.exchange_of_notMem (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s) {x : V} (hx : x ∉ s) :
    (σ.exchange τ s hσ hτ).partner x = σ.partner x := if_neg hx

/-- **Exchange produces nothing new below eight vertices.**  On seven vertices or
fewer, an exchange between two perfect matchings along any closed set returns one
of the two matchings it started from.  There is no room for a second alternating
cycle, so no subset of cycles to choose between.

This is the exact sense in which an argument resting on exchange has no
six-vertex instance: not that the instance is hard to find, but that every
exchange there is the identity or the swap. -/
theorem exchange_trivial_of_card_le_seven [Fintype V] (hV : Fintype.card V ≤ 7)
    (σ τ : Pairing V) {s : Finset V}
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s) :
    (∀ x, (σ.exchange τ s hσ hτ).partner x = σ.partner x) ∨
    (∀ x, (σ.exchange τ s hσ hτ).partner x = τ.partner x) := by
  classical
  by_cases hne : (s ∩ disagree σ τ).Nonempty
  · right
    obtain ⟨x, hxmem⟩ := hne
    rw [Finset.mem_inter] at hxmem
    obtain ⟨hxs, hxD⟩ := hxmem
    -- the part of the disagreement outside `s` must be empty
    have hsub : disagree σ τ ⊆ s := by
      by_contra hcon
      obtain ⟨z, hzD, hzs⟩ := Finset.not_subset.mp hcon
      refine not_two_disagreements_of_card_lt_eight (by omega) σ τ
        (s := s ∩ disagree σ τ) (t := disagree σ τ \ s) ?_ ?_ ?_ ?_ ?_
        (Finset.mem_inter.mpr ⟨hxs, hxD⟩) (Finset.mem_sdiff.mpr ⟨hzD, hzs⟩)
        (by rwa [mem_disagree] at hxD) (by rwa [mem_disagree] at hzD)
      · exact Finset.disjoint_left.mpr (fun a ha hb =>
          (Finset.mem_sdiff.mp hb).2 (Finset.mem_inter.mp ha).1)
      · intro a ha
        rw [Finset.mem_inter] at ha ⊢
        exact ⟨hσ a ha.1, disagree_closed_fst σ τ a ha.2⟩
      · intro a ha
        rw [Finset.mem_inter] at ha ⊢
        exact ⟨hτ a ha.1, disagree_closed_snd σ τ a ha.2⟩
      · intro a ha
        rw [Finset.mem_sdiff] at ha ⊢
        refine ⟨disagree_closed_fst σ τ a ha.1, fun hmem => ha.2 ?_⟩
        have := hσ _ hmem
        rwa [σ.partner_partner] at this
      · intro a ha
        rw [Finset.mem_sdiff] at ha ⊢
        refine ⟨disagree_closed_snd σ τ a ha.1, fun hmem => ha.2 ?_⟩
        have := hτ _ hmem
        rwa [τ.partner_partner] at this
    intro y
    by_cases hy : y ∈ s
    · exact Pairing.exchange_of_mem σ τ s hσ hτ hy
    · rw [Pairing.exchange_of_notMem σ τ s hσ hτ hy]
      by_contra hcon
      exact hy (hsub (by rw [mem_disagree]; exact hcon))
  · left
    intro y
    by_cases hy : y ∈ s
    · rw [Pairing.exchange_of_mem σ τ s hσ hτ hy]
      by_contra hcon
      exact hne ⟨y, Finset.mem_inter.mpr ⟨hy, by rw [mem_disagree]; exact fun h => hcon h.symm⟩⟩
    · exact Pairing.exchange_of_notMem σ τ s hσ hτ hy

/-! ### A partial exchange yields a genuinely new matching

If two matchings disagree both inside a closed set and outside it, exchanging along
that set alone produces a matching equal to neither.  Inside the set it follows the
second, where the first disagreed; outside it follows the first, where the second
disagreed.

This is the step that rules out a union of two matchings having more than one
alternating cycle when the pair is required to be part of a family with no other
members: swap along one cycle and a new member appears.
-/

/-- Inside the exchanged set the result differs from the first matching. -/
theorem exchange_ne_left (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s)
    {a : V} (ha : a ∈ s) (hne : σ.partner a ≠ τ.partner a) :
    (σ.exchange τ s hσ hτ).partner a ≠ σ.partner a := by
  rw [Pairing.exchange_of_mem σ τ s hσ hτ ha]
  exact fun h => hne h.symm

/-- Outside it the result differs from the second. -/
theorem exchange_ne_right (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s)
    {b : V} (hb : b ∉ s) (hne : σ.partner b ≠ τ.partner b) :
    (σ.exchange τ s hσ hτ).partner b ≠ τ.partner b := by
  rw [Pairing.exchange_of_notMem σ τ s hσ hτ hb]
  exact hne

/-- **A partial exchange is a third matching.**  If two matchings disagree both
inside a closed set and outside it, the exchange along that set is neither of
them. -/
theorem exchange_ne_both [Fintype V] (σ τ : Pairing V) (s : Finset V)
    (hσ : ∀ x ∈ s, σ.partner x ∈ s) (hτ : ∀ x ∈ s, τ.partner x ∈ s)
    {a b : V} (ha : a ∈ s) (hane : σ.partner a ≠ τ.partner a)
    (hb : b ∉ s) (hbne : σ.partner b ≠ τ.partner b) :
    (σ.exchange τ s hσ hτ) ≠ σ ∧ (σ.exchange τ s hσ hτ) ≠ τ := by
  constructor
  · intro h
    exact exchange_ne_left σ τ s hσ hτ ha hane (by rw [h])
  · intro h
    exact exchange_ne_right σ τ s hσ hτ hb hbne (by rw [h])

/-! ### Three-matching families over an arbitrary vertex set

Three perfect matchings on the same vertices form an edge-coloured cubic
multigraph, counted with multiplicity.  The following small interface records
the shared-edge parity facts without assuming an ambient graph.
-/

/-- Three pairings of the same vertex set, one per colour. -/
structure Skeleton (V : Type*) where
  /-- The matching carrying colour `i`. -/
  matching : Fin 3 → Pairing V

variable (S : Skeleton V)

/-- The partners of `x` in the three matchings. -/
def Skeleton.partners (x : V) : Fin 3 → V := fun i => (S.matching i).partner x

omit [DecidableEq V] in
/-- No vertex is its own partner in any colour, so every vertex has three
incident skeleton edges counted with multiplicity — the skeleton is cubic as a
multigraph, for every vertex set whatsoever. -/
theorem Skeleton.partners_ne (x : V) (i : Fin 3) : S.partners x i ≠ x :=
  (S.matching i).partner_ne x

omit [DecidableEq V] in
/-- Partnership is symmetric in each colour. -/
theorem Skeleton.partners_involutive (x : V) (i : Fin 3) :
    (S.matching i).partner (S.partners x i) = x :=
  (S.matching i).partner_partner x

omit [DecidableEq V] in
/-- Two colours of a skeleton agree at `x` exactly when they agree at its
partner: shared edges are shared symmetrically. -/
theorem Skeleton.shared_symm {x : V} {i j : Fin 3}
    (h : S.partners x i = S.partners x j) :
    S.partners (S.partners x i) i = S.partners (S.partners x i) j := by
  unfold Skeleton.partners at h ⊢
  rw [(S.matching i).partner_partner, h, (S.matching j).partner_partner]

/-- The vertices where two colours of the skeleton use the same edge. -/
def Skeleton.sharedSet (i j : Fin 3) [Fintype V] : Finset V :=
  Finset.univ.filter (fun x => S.partners x i = S.partners x j)

/-- The shared set of two colours is closed under either matching, hence has even
cardinality: shared edges come in whole edges, never half of one.  Uniform in the
vertex set. -/
theorem Skeleton.even_card_sharedSet [Fintype V] (i j : Fin 3) :
    Even (S.sharedSet i j).card := by
  refine even_card_of_closed (S.matching i) _ (fun x hx => ?_)
  simp only [Skeleton.sharedSet, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  exact S.shared_symm hx

end MatchingParity
