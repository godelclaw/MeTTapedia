import Mettapedia.GraphTheory.FourColor.GoertzelV24MapEulerBound

/-!
# Same face on both sides forces a bridge

The classical boundary of the compositional route needs one fact: in a
bridgeless spherical map, the two sides of an edge lie on different faces.
Informally this is read off the Jordan curve theorem.  Here it is derived
from the Euler bound instead, which keeps the whole argument finite.

The setup is deliberately kept in pure permutation language.  A map is a
rotation `σ` together with an edge list; the edge under scrutiny is placed
at the head, so its flip is `Equiv.swap a b` and the remaining edges have
product `β`.  Deleting the edge is then literally passing from `σ * (swap a b * β)`
to `σ * β`, and the two hypotheses `β a = a`, `β b = b` say exactly that no
other edge touches this one.

The argument is three lines of arithmetic:

* the two sides `a` and `b` are swapped by the face permutation, so
  "same face" transports to the pair `(σ a, σ b)` that the surgery law
  actually reads;
* deleting the edge therefore *splits* a face: `orbits` goes up by one;
* the Euler bound applied to the smaller edge list then has no room left,
  and forces at least two components.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24BridgeTwoSided

open Equiv Equiv.Perm
open GoertzelV24PermutationOrbitSurgery
open GoertzelV24WordReachability
open GoertzelV24MapEulerBound

variable {D : Type*} [Fintype D] [DecidableEq D]

section

variable {σ : Perm D} {a b : D} {rest : List (D × D)}

omit [Fintype D] in
/-- The face permutation exchanges the two sides of the head edge. -/
theorem face_apply_left (hβb : swapProduct rest b = b) :
    (σ * (Equiv.swap a b * swapProduct rest)) b = σ a := by
  simp [Perm.mul_apply, hβb, Equiv.swap_apply_right]

omit [Fintype D] in
theorem face_apply_right (hβa : swapProduct rest a = a) :
    (σ * (Equiv.swap a b * swapProduct rest)) a = σ b := by
  simp [Perm.mul_apply, hβa, Equiv.swap_apply_left]

omit [Fintype D] in
/-- **Transport of "same face".**  If the two sides of the edge lie on one
face orbit, then so do the two points the surgery law inspects.  The face
permutation carries `b` to `σ a` and `a` to `σ b`, so the transported pair
is the image of the original one. -/
theorem sameCycle_image_of_sameCycle
    (hβa : swapProduct rest a = a) (hβb : swapProduct rest b = b)
    (hsame : (σ * (Equiv.swap a b * swapProduct rest)).SameCycle a b) :
    (σ * (Equiv.swap a b * swapProduct rest)).SameCycle (σ a) (σ b) := by
  set φ := σ * (Equiv.swap a b * swapProduct rest) with hφ
  have hleft : φ b = σ a := face_apply_left hβb
  have hright : φ a = σ b := face_apply_right hβa
  obtain ⟨i, hi⟩ := hsame.symm
  refine ⟨i, ?_⟩
  have hcomm : (φ ^ i) * φ = φ * (φ ^ i) := ((Commute.refl φ).zpow_left i).eq
  rw [← hleft, ← hright, ← Perm.mul_apply, hcomm, Perm.mul_apply, hi]

/-- **Deleting the edge splits a face.**  Under the same-face hypothesis the
smaller edge list has exactly one more face orbit. -/
theorem orbitCount_delete_eq_succ (hab : a ≠ b)
    (hβa : swapProduct rest a = a) (hβb : swapProduct rest b = b)
    (hsame : (σ * (Equiv.swap a b * swapProduct rest)).SameCycle a b) :
    orbitCount (σ * swapProduct rest) =
      orbitCount (σ * (Equiv.swap a b * swapProduct rest)) + 1 := by
  have hσab : σ a ≠ σ b := fun h => hab (σ.injective h)
  -- the face permutation of the smaller list is a transposition away
  have hsplit : σ * swapProduct rest =
      Equiv.swap (σ a) (σ b) * (σ * (Equiv.swap a b * swapProduct rest)) := by
    rw [← mul_assoc, ← Equiv.mul_swap_eq_swap_mul, mul_assoc,
      ← mul_assoc (Equiv.swap a b), Equiv.swap_mul_self, one_mul]
  rw [hsplit]
  exact orbitCount_swap_mul_of_sameCycle _ hσab
    (sameCycle_image_of_sameCycle hβa hβb hsame)

end

/-- **Same face on both sides forces a bridge.**

Let `σ` be a rotation and let the edge list be `(a, b) :: rest`, with no
other edge touching `a` or `b`.  Write `α := Equiv.swap a b * swapProduct rest`
for the edge flip and `σ * α` for the face permutation.  Assume the map is
spherical, in the form `V + F = E + 2` with `E = rest.length + 1`, and that
the two sides `a`, `b` of the head edge lie on one face.  Then deleting that
edge leaves at least two components: the edge is a bridge. -/
theorem two_le_components_of_sameCycle
    (σ : Perm D) {a b : D} (rest : List (D × D)) (hab : a ≠ b)
    (hβa : swapProduct rest a = a) (hβb : swapProduct rest b = b)
    (hrest : ∀ edge ∈ rest, edge.1 ≠ edge.2)
    (hsphere :
      orbitCount σ + orbitCount (σ * (Equiv.swap a b * swapProduct rest)) =
        rest.length + 3)
    (hsame : (σ * (Equiv.swap a b * swapProduct rest)).SameCycle a b) :
    2 ≤ wordOrbitCount (σ :: swapGenerators rest) := by
  have hdelete := orbitCount_delete_eq_succ hab hβa hβb hsame
  have hbound :=
    orbitCount_add_orbitCount_mul_swapProduct_le σ rest hrest
  omega

/-- **Two-sidedness.**  Contrapositive form: if deleting the head edge keeps
the map connected, its two sides lie on different faces. -/
theorem not_sameCycle_of_components_lt_two
    (σ : Perm D) {a b : D} (rest : List (D × D)) (hab : a ≠ b)
    (hβa : swapProduct rest a = a) (hβb : swapProduct rest b = b)
    (hrest : ∀ edge ∈ rest, edge.1 ≠ edge.2)
    (hsphere :
      orbitCount σ + orbitCount (σ * (Equiv.swap a b * swapProduct rest)) =
        rest.length + 3)
    (hconnected : wordOrbitCount (σ :: swapGenerators rest) < 2) :
    ¬ (σ * (Equiv.swap a b * swapProduct rest)).SameCycle a b := by
  intro hsame
  have := two_le_components_of_sameCycle σ rest hab hβa hβb hrest hsphere hsame
  omega

/-!
## The converse, by a walk argument

The implication above came from Euler's inequality.  Its converse --- a
bridge has one face on both sides --- does *not* follow from that
inequality, which leaves both branches open once the component count rises.
It has instead an elementary proof needing neither Euler nor any embedding:
a facial walk that crosses a bridge has only one way back.

The bridge is presented by its two sides.  Rather than build a connectivity
theory, we take as given a two-valued `side` that `σ` preserves (a rotation
stays at its vertex), that the edge flip preserves away from this one edge
(nothing else crosses), and that separates this edge's own two darts.  That
is what it means for the edge to be a bridge, and it is all the argument
uses.
-/

omit [DecidableEq D] in
/-- **A bridge has one face on both sides.**

`φ` is the face permutation and `d`, `other` the two sides of the edge.
The hypotheses say the edge is a bridge: the first step off `d` crosses
over, and from the far side every step stays there unless taken from
`other`.  That `other` itself lies on the far side is *not* needed --- the
walk must come back, and `other` is the only door. -/
theorem sameCycle_of_bridge
    (φ : Perm D) (side : D → Bool) (d other : D)
    (hstep : ∀ x, x ≠ other → side x ≠ side d → side (φ x) = side x)
    (hcross : side (φ d) ≠ side d) :
    φ.SameCycle d other := by
  classical
  have hN : (φ ^ (orderOf φ)) d = d := by
    rw [pow_orderOf_eq_one]; rfl
  have hexists : ∃ k, 1 ≤ k ∧ side ((φ ^ k) d) = side d :=
    ⟨orderOf φ, orderOf_pos φ, by rw [hN]⟩
  obtain ⟨k, hk_min, hk_one, hk_side⟩ :
      ∃ k, (∀ j, j < k → ¬(1 ≤ j ∧ side ((φ ^ j) d) = side d)) ∧
        1 ≤ k ∧ side ((φ ^ k) d) = side d :=
    ⟨Nat.find hexists, fun j hj => Nat.find_min hexists hj,
      (Nat.find_spec hexists).1, (Nat.find_spec hexists).2⟩
  -- the first step already crosses, so the return is not immediate
  have hk_two : 2 ≤ k := by
    rcases Nat.eq_or_lt_of_le hk_one with h1 | h2
    · exfalso
      apply hcross
      rw [← h1] at hk_side
      simpa [pow_one] using hk_side
    · omega
  -- the point just before the return sits on the far side
  have hprev_side : side ((φ ^ (k - 1)) d) ≠ side d := fun hEq =>
    hk_min (k - 1) (by omega) ⟨by omega, hEq⟩
  -- and only the edge's far dart can step back
  by_contra hcontra
  have hprev_ne : (φ ^ (k - 1)) d ≠ other := fun hEq =>
    hcontra ⟨((k - 1 : ℕ) : ℤ), by rw [zpow_natCast]; exact hEq⟩
  have hstay := hstep ((φ ^ (k - 1)) d) hprev_ne hprev_side
  have hstepEq : (φ ^ k) d = φ ((φ ^ (k - 1)) d) := by
    conv_lhs => rw [show k = (k - 1) + 1 by omega]
    rw [pow_succ', Perm.mul_apply]
  rw [hstepEq, hstay] at hk_side
  exact hprev_side hk_side

/-- **The converse, packaged.**  If deleting the head edge separates its two
endpoints --- that is, if the edge is a bridge --- then its two sides lie on
one face orbit.  The side function is "which component of the deleted map",
and the three hypotheses of the walk lemma are exactly what bridgehood
gives. -/
theorem sameCycle_of_not_wordReachable
    (σ : Perm D) {a b : D} (rest : List (D × D))
    (hβa : swapProduct rest a = a) (hβb : swapProduct rest b = b)
    (hbridge : ¬ WordReachable (σ :: swapGenerators rest) a b) :
    (σ * (Equiv.swap a b * swapProduct rest)).SameCycle a b := by
  classical
  set L := σ :: swapGenerators rest with hL
  set side : D → Bool := fun x => decide (WordReachable L a x) with hside
  have hside_a : side a = true := by
    simp [hside, WordReachable.refl L a]
  -- reaching sigma of a point is reaching the point
  have hsigma : ∀ y : D, WordReachable L a (σ y) ↔ WordReachable L a y := by
    intro y
    constructor
    · intro h
      exact h.trans (wordReachable_step (List.mem_cons_self) y).symm
    · intro h
      exact h.trans (wordReachable_step (List.mem_cons_self) y)
  -- reaching the edge-product image of a point is reaching the point
  have hbeta : ∀ y : D,
      WordReachable L a (swapProduct rest y) ↔ WordReachable L a y := by
    intro y
    constructor
    · intro h
      exact h.trans (wordReachable_swapProduct σ rest y).symm
    · intro h
      exact h.trans (wordReachable_swapProduct σ rest y)
  refine sameCycle_of_bridge _ side a b ?_ ?_
  · -- from the far side, only b steps back
    intro x hxb hxside
    have hxnot : ¬ WordReachable L a x := by
      intro hreach
      apply hxside
      rw [hside_a, hside]
      simpa using hreach
    have hxa : x ≠ a := fun h => hxnot (h ▸ WordReachable.refl L a)
    -- the edge product cannot carry x onto the deleted edge
    have hne_a : swapProduct rest x ≠ a := fun h =>
      hxa ((swapProduct rest).injective (by rw [h, hβa]))
    have hne_b : swapProduct rest x ≠ b := fun h =>
      hxb ((swapProduct rest).injective (by rw [h, hβb]))
    have happly : (σ * (Equiv.swap a b * swapProduct rest)) x
        = σ (swapProduct rest x) := by
      simp [Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hne_a hne_b]
    have : ¬ WordReachable L a (σ (swapProduct rest x)) := by
      rw [hsigma, hbeta]
      exact hxnot
    rw [happly, hside]
    simp only [decide_eq_decide]
    constructor
    · intro h; exact absurd h this
    · intro h; exact absurd h hxnot
  · -- the first step off a crosses to the far side
    have happly : (σ * (Equiv.swap a b * swapProduct rest)) a = σ b := by
      simp [Perm.mul_apply, hβa, Equiv.swap_apply_left]
    have hnot : ¬ WordReachable L a (σ b) := by
      rw [hsigma]
      exact hbridge
    rw [happly, hside_a, hside]
    simp only [ne_eq, decide_eq_true_eq]
    exact hnot

/-!
## A cubic digon always shares a face

Two parallel edges between the same pair of vertices always have a face
containing a dart of each --- provided the vertex is cubic.  The reason is
pure counting on three darts: a rotation of a three-element star makes any
two of its darts cyclically adjacent one way or the other, so one of the two
possible adjacencies must hold, and either one produces the shared face.

This needs neither sphericity nor Euler.  What sphericity is actually needed
for is the *stronger* statement that the shared face is exactly the digon,
which is a separate condition on how the two rotations are oriented relative
to each other.
-/

omit [Fintype D] [DecidableEq D] in
/-- **A digon at a cubic vertex shares a face.**  The hypothesis `hrot` is
what a three-dart rotation supplies: of the two parallel darts, one follows
the other. -/
theorem sameCycle_digon (σ α : Perm D) (p₁ p₂ : D)
    (hinv : Function.Involutive α)
    (hrot : σ p₁ = p₂ ∨ σ p₂ = p₁) :
    (σ * α).SameCycle (α p₁) p₂ ∨ (σ * α).SameCycle (α p₂) p₁ := by
  rcases hrot with h | h
  · refine Or.inl ⟨1, ?_⟩
    simp [Perm.mul_apply, hinv p₁, h]
  · refine Or.inr ⟨1, ?_⟩
    simp [Perm.mul_apply, hinv p₂, h]

end GoertzelV24BridgeTwoSided

end Mettapedia.GraphTheory.FourColor
