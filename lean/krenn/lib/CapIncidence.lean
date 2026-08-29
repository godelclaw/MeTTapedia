import Mathlib
import ColourPerMatching

/-!
# The cap-incidence form is supported on neighbouring pairs

Contracting two vertices of a weight system replaces the amplitude by a flat term
plus a tangent correction.  The correction is governed by a bilinear form in the
contraction matrix, indexed by a *residual* pair of vertices and a pair of residual
colours; the caps that leave the amplitude flat away from a permitted defect shape
are exactly the kernel of the matrix these entries assemble.  Its rank decides
whether such a cap exists.

For weights that come from colouring the matchings the rank is settled by the
support alone, and this file proves the reason.  An uncoloured edge weighs zero, so
every entry of the form carries a factor that vanishes unless the residual vertices
*neighbour* the contracted ones — one adjacent to each.  Pairs that fail this are
not merely small contributors; their entries are identically zero, and they impose
no condition on the contraction matrix at all.

The combinatorial consequence is immediate and sharp.  Only pairs meeting both
contracted vertices survive, and a defect shape containing every survivor leaves an
empty system, whose kernel is everything.  On a cycle, contracting along an edge
leaves exactly one surviving pair — the two outer neighbours — so a star centred at
either annihilates the system and every contraction is integrable; contracting along
a chord leaves several, and no single centre covers them.
-/

namespace CapIncidence

open ColourPerMatching

variable {V C : Type*} [Fintype V] [DecidableEq V] [Fintype C] [DecidableEq C]

/-! ### Two functionals, one witness

A cap is wanted whose diagonal and whose contraction scalar both fail to vanish.
Those are two linear functionals on the kernel of the incidence matrix, and the
question of whether some vector escapes both of their zero sets is not answered by
inspecting a basis one vector at a time: the witness may be a sum.
-/

section Witness

variable {K : Type*} [Ring K] {M : Type*} [AddCommGroup M] [Module K M]

/-- **Two functionals nonzero somewhere are nonzero together somewhere.**  If `f` does
not vanish at `u` and `g` does not vanish at `v`, then some single vector makes both
nonzero — one of `u`, `v`, or their sum.

The construction is the content: when `g` kills `u` and `f` kills `v`, neither alone
is a witness, but `u + v` is, since `f` sees only `u` there and `g` only `v`.  A
recognizer that checks basis vectors individually will miss exactly this case and
report absence where a cap exists. -/
theorem exists_both_ne_zero (f g : M →ₗ[K] K) {u v : M}
    (hu : f u ≠ 0) (hv : g v ≠ 0) :
    ∃ x : M, f x ≠ 0 ∧ g x ≠ 0 := by
  by_cases hgu : g u = 0
  · by_cases hfv : f v = 0
    · refine ⟨u + v, ?_, ?_⟩
      · rw [map_add, hfv, add_zero]; exact hu
      · rw [map_add, hgu, zero_add]; exact hv
    · exact ⟨v, hfv, hv⟩
  · exact ⟨u, hu, hgu⟩

/-- The witness is one of three explicit vectors, so the search is finite. -/
theorem exists_both_ne_zero_mem (f g : M →ₗ[K] K) (N : Submodule K M) {u v : M}
    (hu' : u ∈ N) (hv' : v ∈ N) (hu : f u ≠ 0) (hv : g v ≠ 0) :
    ∃ x ∈ N, f x ≠ 0 ∧ g x ≠ 0 := by
  by_cases hgu : g u = 0
  · by_cases hfv : f v = 0
    · refine ⟨u + v, N.add_mem hu' hv', ?_, ?_⟩
      · rw [map_add, hfv, add_zero]; exact hu
      · rw [map_add, hgu, zero_add]; exact hv
    · exact ⟨v, hv', hfv, hv⟩
  · exact ⟨u, hu', hu, hgu⟩

/-- **The decoupling.**  A vector of a subspace on which two functionals are both
nonzero exists exactly when each functional is separately nonzero somewhere on it.

This is the characterisation a search wants. The condition defining a usable cap is a
*conjunction* — nonzero diagonal and nonzero contraction scalar — and a conjunction of
that shape ordinarily has to be searched jointly. Here it splits into two independent
questions, each of which is a rank computation: does the constraint space lie inside
the kernel of this functional. -/
theorem exists_both_iff (f g : M →ₗ[K] K) (N : Submodule K M) :
    (∃ x ∈ N, f x ≠ 0 ∧ g x ≠ 0) ↔ (∃ x ∈ N, f x ≠ 0) ∧ (∃ x ∈ N, g x ≠ 0) := by
  constructor
  · rintro ⟨x, hx, hf, hg⟩
    exact ⟨⟨x, hx, hf⟩, ⟨x, hx, hg⟩⟩
  · rintro ⟨⟨u, hu', hu⟩, ⟨v, hv', hv⟩⟩
    exact exists_both_ne_zero_mem f g N hu' hv' hu hv

/-- The same, as a statement about containment in kernels: a usable vector exists
exactly when the space is contained in neither functional's kernel.

Each side is decided by a rank, so this is the form in which the question becomes a
finite linear-algebra computation over the field the weights live in. -/
theorem exists_both_iff_not_le (f g : M →ₗ[K] K) (N : Submodule K M) :
    (∃ x ∈ N, f x ≠ 0 ∧ g x ≠ 0)
      ↔ ¬ N ≤ LinearMap.ker f ∧ ¬ N ≤ LinearMap.ker g := by
  rw [exists_both_iff]
  constructor
  · rintro ⟨⟨u, hu', hu⟩, ⟨v, hv', hv⟩⟩
    exact ⟨fun h => hu (h hu'), fun h => hv (h hv')⟩
  · rintro ⟨hf, hg⟩
    refine ⟨?_, ?_⟩
    · by_contra hc
      push_neg at hc
      exact hf fun x hx => LinearMap.mem_ker.2 (hc x hx)
    · by_contra hc
      push_neg at hc
      exact hg fun x hx => LinearMap.mem_ker.2 (hc x hx)

end Witness

/-- An uncoloured edge weighs zero, whatever colours its endpoints wear. -/
theorem weightOf_eq_zero_of_none (ec : V → V → Option C) (hsymm : ∀ u v, ec u v = ec v u)
    {u v : V} (h : ec u v = none) (i j : C) :
    weightOf ec hsymm s((u, i), (v, j)) = 0 := by
  rw [weightOf_apply]
  refine if_neg ?_
  rintro ⟨-, h2⟩
  rw [h] at h2
  simp at h2

/-- The entry of the cap-incidence form at a residual pair `(k, l)` and residual
colours, for a contraction along `(p, q)` with matrix `M`.

The two summands are the two ways the residual pair can meet the contracted pair. -/
noncomputable def entry (W : Sym2 (V × C) → ℂ) (M : C → C → ℂ)
    (p q k l : V) (x y : C) : ℂ :=
  ∑ a : C, ∑ b : C, M a b *
    (W s((p, a), (k, x)) * W s((q, b), (l, y))
      + W s((p, a), (l, x)) * W s((q, b), (k, y)))

/-- A pair of vertices is *off the support* when its whole weight block vanishes:
no pair of colours gives the edge any weight.  This is the general form of an
uncoloured edge, and it needs no assumption on where the weights came from. -/
def OffSupport (W : Sym2 (V × C) → ℂ) (u v : V) : Prop :=
  ∀ i j : C, W s((u, i), (v, j)) = 0

/-- **Support restriction, for arbitrary weights.**  If each of the two ways a
residual pair can meet the contracted pair is broken by an edge off the support,
the entry vanishes identically — for every contraction matrix and all colours.

Nothing here assumes the weights come from a colouring, so this applies to a
hypothetical solution as much as to a constructed one. -/
theorem entry_eq_zero_of_offSupport (W : Sym2 (V × C) → ℂ) (M : C → C → ℂ)
    (p q k l : V) (x y : C)
    (h₁ : OffSupport W p k ∨ OffSupport W q l)
    (h₂ : OffSupport W p l ∨ OffSupport W q k) :
    entry W M p q k l x y = 0 := by
  unfold entry
  refine Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => ?_
  have e₁ : W s((p, a), (k, x)) * W s((q, b), (l, y)) = 0 := by
    rcases h₁ with h | h
    · rw [h a x, zero_mul]
    · rw [h b y, mul_zero]
  have e₂ : W s((p, a), (l, x)) * W s((q, b), (k, y)) = 0 := by
    rcases h₂ with h | h
    · rw [h a x, zero_mul]
    · rw [h b y, mul_zero]
  rw [e₁, e₂, add_zero, mul_zero]

/-- An uncoloured edge is off the support. -/
theorem offSupport_of_none (ec : V → V → Option C) (hsymm : ∀ u v, ec u v = ec v u)
    {u v : V} (h : ec u v = none) : OffSupport (weightOf ec hsymm) u v :=
  fun i j => weightOf_eq_zero_of_none ec hsymm h i j

/-- **Support restriction.**  If neither way of meeting the contracted pair is fully
coloured — the first summand missing an edge and the second missing one too — then
the entry vanishes identically, for every contraction matrix and all colours.

So a residual pair contributes no constraint unless one of its vertices neighbours
`p` and the other neighbours `q`. -/
theorem entry_eq_zero (ec : V → V → Option C) (hsymm : ∀ u v, ec u v = ec v u)
    (M : C → C → ℂ) (p q k l : V) (x y : C)
    (h₁ : ec p k = none ∨ ec q l = none)
    (h₂ : ec p l = none ∨ ec q k = none) :
    entry (weightOf ec hsymm) M p q k l x y = 0 :=
  entry_eq_zero_of_offSupport _ M p q k l x y
    (h₁.imp (offSupport_of_none ec hsymm) (offSupport_of_none ec hsymm))
    (h₂.imp (offSupport_of_none ec hsymm) (offSupport_of_none ec hsymm))


/-- **Star collapse from a low-degree vertex.**  Suppose `p` meets the residual set
in at most the single vertex `k₀`: every other residual edge at `p` is off the
support.  Then every entry outside the star centred at `k₀` vanishes.

The constraint system therefore reduces to that star, and a contraction whose defect
is confined there meets no condition at all.  This is the exact sense in which the
method is a sparsity method — it asks the contracted vertex to have degree at most
two, counting its partner. -/
theorem entry_eq_zero_of_star (W : Sym2 (V × C) → ℂ) (M : C → C → ℂ)
    (p q : V) {k₀ : V} (h : ∀ k, k ≠ k₀ → k ≠ p → k ≠ q → OffSupport W p k)
    {k l : V} (hk : k ≠ k₀) (hl : l ≠ k₀)
    (hkp : k ≠ p) (hkq : k ≠ q) (hlp : l ≠ p) (hlq : l ≠ q) (x y : C) :
    entry W M p q k l x y = 0 :=
  entry_eq_zero_of_offSupport W M p q k l x y
    (Or.inl (h k hk hkp hkq)) (Or.inl (h l hl hlp hlq))

/-- The residual pairs that can constrain a contraction along `(p, q)`: those with
one vertex coloured to `p` and the other coloured to `q`. -/
def Live (ec : V → V → Option C) (p q k l : V) : Prop :=
  (ec p k ≠ none ∧ ec q l ≠ none) ∨ (ec p l ≠ none ∧ ec q k ≠ none)

/-- Everything outside `Live` is silent: the contracted system sees only live pairs. -/
theorem entry_eq_zero_of_not_live (ec : V → V → Option C) (hsymm : ∀ u v, ec u v = ec v u)
    (M : C → C → ℂ) (p q k l : V) (x y : C) (h : ¬ Live ec p q k l) :
    entry (weightOf ec hsymm) M p q k l x y = 0 := by
  unfold Live at h
  rw [not_or] at h
  obtain ⟨hA, hB⟩ := h
  rw [not_and_or, not_not, not_not] at hA
  rw [not_and_or, not_not, not_not] at hB
  exact entry_eq_zero ec hsymm M p q k l x y hA hB


/-! ### The cap-incidence map for arbitrary weights

The constraints on a cap, its contraction scalar, and its diagonal are all linear in
the cap. Collecting them as linear maps turns the question of a usable cap into a
statement about one subspace and two functionals, which is where the decoupling above
applies.
-/

section Incidence

variable {K : Type*} [CommRing K] [Fintype C]

/-- Pairing a cap against a coefficient array.  Both the incidence constraints and the
contraction scalar have this shape, so they are instances of one construction. -/
noncomputable def pair (w : C → C → K) : (C → C → K) →ₗ[K] K where
  toFun M := ∑ a : C, ∑ b : C, M a b * w a b
  map_add' M N := by
    simp only [Pi.add_apply, add_mul]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => Finset.sum_add_distrib
  map_smul' c M := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, Finset.mul_sum]

@[simp] theorem pair_apply (w M : C → C → K) :
    pair w M = ∑ a : C, ∑ b : C, M a b * w a b := rfl

/-- The incidence constraint at a residual pair and a pair of residual colours. -/
noncomputable def incidence (W : Sym2 (V × C) → K) (p q k l : V) (x y : C) :
    (C → C → K) →ₗ[K] K :=
  pair (fun a b => W s((p, a), (k, x)) * W s((q, b), (l, y))
                 + W s((p, a), (l, x)) * W s((q, b), (k, y)))

/-- The contraction scalar of a cap: its pairing against the contracted edge. -/
noncomputable def contr (W : Sym2 (V × C) → K) (p q : V) : (C → C → K) →ₗ[K] K :=
  pair (fun a b => W s((p, a), (q, b)))

/-- Reading off the diagonal at a chosen colour.  On the subspace of caps with
constant diagonal this is the common value, independent of the choice. -/
noncomputable def diagAt (i : C) : (C → C → K) →ₗ[K] K where
  toFun M := M i i
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Caps with constant diagonal: a subspace, since the conditions are linear. -/
def constDiag : Submodule K (C → C → K) where
  carrier := {M | ∀ a b : C, M a a = M b b}
  add_mem' hM hN := fun a b => by
    simp only [Pi.add_apply]; rw [hM a b, hN a b]
  zero_mem' := fun _ _ => rfl
  smul_mem' c _ hM := fun a b => by
    simp only [Pi.smul_apply]; rw [hM a b]

/-- The caps admissible for a given permitted defect shape: constant diagonal, and
flat at every residual pair and colour pair outside the shape. -/
noncomputable def admissible (W : Sym2 (V × C) → K) (p q : V)
    (S : Finset (V × V × C × C)) : Submodule K (C → C → K) :=
  constDiag ⊓ ⨅ t ∈ S, LinearMap.ker (incidence W p q t.1 t.2.1 t.2.2.1 t.2.2.2)

/-- **A usable cap exists exactly when two rank conditions hold separately.**

The defining requirement is a conjunction — the admissible space must contain a cap
whose diagonal does not vanish *and* whose contraction scalar does not vanish — and
the content here is that the conjunction decouples. Each half asks whether the
admissible space is contained in the kernel of one functional, which is a rank
computation over the field the weights live in.

Searching a basis of the admissible space for a vector satisfying both at once answers
a strictly weaker question, since a witness may be a sum of basis vectors. -/
theorem usable_cap_iff (W : Sym2 (V × C) → K) (p q : V)
    (S : Finset (V × V × C × C)) (i : C) :
    (∃ M ∈ admissible W p q S, diagAt i M ≠ 0 ∧ contr W p q M ≠ 0)
      ↔ ¬ admissible W p q S ≤ LinearMap.ker (diagAt (K := K) i)
        ∧ ¬ admissible W p q S ≤ LinearMap.ker (contr W p q) :=
  exists_both_iff_not_le _ _ _


/-- **A trivial admissible space admits no usable cap.**  If the flatness conditions cut
the caps down to zero, there is nothing left with a nonvanishing diagonal, so no usable
cap exists whatever the contraction scalar does.

This is the direction the incidence rank controls.  The rows lie in a sum of tensor
products of the blocks' column spaces, so blocks of full rank make them span, and a
spanning set of conditions leaves only the zero cap.  Caps therefore require degenerate
blocks, which is the same requirement the degeneration argument was trying to supply. -/
theorem no_usable_cap_of_trivial {K : Type*} [CommRing K] [Fintype C]
    (W : Sym2 (V × C) → K) (p q : V) (S : Finset (V × V × C × C)) (i : C)
    (h : admissible W p q S = ⊥) :
    ¬ ∃ M ∈ admissible W p q S, diagAt i M ≠ 0 ∧ contr W p q M ≠ 0 := by
  rintro ⟨M, hM, hd, -⟩
  rw [h, Submodule.mem_bot] at hM
  exact hd (by rw [hM]; exact map_zero _)

end Incidence


/-! ### Escaping the coordinate hyperplanes

A cap that factors as an outer product has entries `lam a * rho b`, and its diagonal is
constant exactly when `lam a * rho a` does not depend on `a`.  That can be arranged --
take `rho a = kappa / lam a` -- precisely when `lam` has no zero coordinate.

So the question of whether a certain kind of cap exists becomes: does a subspace contain
a vector all of whose coordinates are nonzero?  Over an infinite field the answer is
governed by a rigid alternative, since a space is never the union of finitely many proper
subspaces.
-/

section Coordinates

variable {K : Type*} [Field K] [Infinite K] {C : Type*} [Fintype C]

/-- **Either a vector escapes every coordinate hyperplane, or one coordinate vanishes on
the whole space.**

There is no middle case: a subspace whose every member has *some* zero coordinate is
covered by the coordinate hyperplanes, and a space over an infinite field covered by
finitely many subspaces is one of them. -/
theorem exists_all_nonzero_or_coord_vanishes (N : Submodule K (C → K)) :
    (∃ x ∈ N, ∀ i : C, x i ≠ 0) ∨ ∃ j : C, ∀ x ∈ N, x j = 0 := by
  classical
  by_cases h : ∃ x ∈ N, ∀ i : C, x i ≠ 0
  · exact Or.inl h
  right
  push_neg at h
  set P : C → Submodule K N := fun j => LinearMap.ker (LinearMap.proj j ∘ₗ N.subtype)
    with hP
  have hunion : (⋃ j, (P j : Set N)) = Set.univ := by
    ext x
    simp only [Set.mem_iUnion, Set.mem_univ, iff_true]
    obtain ⟨i, hi⟩ := h x.1 x.2
    exact ⟨i, by simpa [hP, LinearMap.mem_ker] using hi⟩
  obtain ⟨j, hj⟩ := Subspace.exists_eq_top_of_iUnion_eq_univ hunion
  refine ⟨j, fun x hx => ?_⟩
  have hmem : (⟨x, hx⟩ : N) ∈ P j := by rw [hj]; trivial
  simpa [hP, LinearMap.mem_ker] using hmem


/-- **An outer-product cap built from a vector annihilating the block has no contraction
scalar.**

A cap of the form `lam a * rho b` contracts to the pairing of `rho` against the vector
whose entries are `lam` applied to the block's columns.  If `lam` kills those columns the
contraction scalar is zero and the cap is unusable, whatever `rho` is.

This is what couples the two conditions a usable flat cap must meet.  Making the
correction vanish asks `lam` to annihilate the constrained partners' columns; keeping the
contraction scalar alive asks it not to annihilate the block.  On a support where the
partners are few the equations force the first to imply the second, so the route closes
against itself. -/
theorem contr_eq_zero_of_outer {K : Type*} [CommRing K] [Fintype C]
    (W : Sym2 (V × C) → K) (p q : V) (lam rho : C → K)
    (h : ∀ b : C, ∑ a, lam a * W s((p, a), (q, b)) = 0) :
    contr W p q (fun a b => lam a * rho b) = 0 := by
  classical
  unfold contr
  rw [pair_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun b _ => ?_
  have : ∑ a, lam a * rho b * W s((p, a), (q, b))
      = rho b * ∑ a, lam a * W s((p, a), (q, b)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun a _ => by ring
  rw [this, h b, mul_zero]

end Coordinates


end CapIncidence
