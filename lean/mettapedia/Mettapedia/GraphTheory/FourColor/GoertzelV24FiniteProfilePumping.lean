import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Order.Basic

/-!
# Finite-profile reductive pumping

The abstract descent the compositional route runs on: a class of finite
instances, a size, a predicate, and a corridor whose cut positions carry
profiles drawn from a finite set.  If an irreducible large instance has more
cut positions than there are profiles, two of them agree, and deleting the
material between them produces a strictly smaller instance with the same
defect.  So a counterexample descends to the finite base.

The separation qualifier is load-bearing and is carried here explicitly.  The
splice hypothesis fires only for two cuts that are suitably separated, so the
supply hypothesis has to produce cut positions that are *pairwise* suitably
separated; plain pigeonhole on an unrestricted supply could return an adjacent
pair and the splice would not apply.  Asking for more than `N` pairwise
separated positions and drawing the repeat from among them closes that gap.

Nothing here is specific to maps or colourings.  `Cut`, `Separated` and
`profile` are parameters, and the theorem is the pure descent.
-/

universe u v w

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24FiniteProfilePumping

/-- The hypotheses of the source's pumping theorem, verbatim.

`Cut X` is the type of admissible cut positions of `X`, `Separated` is its
suitable-separation relation, and `profile` sends a cut into the finite profile
set `Q`.  `N` bounds the number of profiles and `V₀` the base size. -/
structure PumpingHypotheses (α : Type u) (Q : Type w) [Fintype Q] where
  /-- The size along which the descent runs. -/
  size : α → ℕ
  /-- The predicate whose failure descends. -/
  P : α → Prop
  /-- Having a ladder-reducible local feature. -/
  LadderReducible : α → Prop
  /-- Admissible cut positions of an instance. -/
  Cut : α → Type v
  /-- Suitable separation of two cut positions. -/
  Separated : ∀ {X : α}, Cut X → Cut X → Prop
  /-- The profile carried by a cut. -/
  profile : ∀ {X : α}, Cut X → Q
  /-- The base size. -/
  V₀ : ℕ
  /-- The profile bound. -/
  N : ℕ
  /-- Hypothesis 3: at most `N` profiles. -/
  card_profiles_le : Fintype.card Q ≤ N
  /-- Hypothesis 1: a ladder-reducible failure has a strictly smaller failure. -/
  reduce_of_ladderReducible :
    ∀ X, ¬ P X → LadderReducible X → ∃ Y, size Y < size X ∧ ¬ P Y
  /-- Hypothesis 2: a large irreducible instance has more than `N` **pairwise
  suitably separated** admissible cut positions. -/
  many_separated_cuts :
    ∀ X, ¬ LadderReducible X → V₀ < size X →
      ∃ c : Fin (N + 1) → Cut X, ∀ i j, i ≠ j → Separated (c i) (c j)
  /-- Hypothesis 4: two separated cuts with equal profiles splice to a strictly
  smaller instance preserving the defect. -/
  splice_of_separated_eq_profile :
    ∀ (X : α) (c d : Cut X), Separated c d → profile c = profile d →
      ∃ Y, size Y < size X ∧ (¬ P X → ¬ P Y)

variable {α : Type u} {Q : Type w} [Fintype Q] [DecidableEq Q]

/-- **One descent step.**  A large failure always has a strictly smaller
failure: either the ladder feature supplies one, or the pigeonhole on pairwise
separated cuts does. -/
theorem exists_smaller_failure (H : PumpingHypotheses.{u, v, w} α Q)
    (X : α) (hnP : ¬ H.P X) (hlarge : H.V₀ < H.size X) :
    ∃ Y, H.size Y < H.size X ∧ ¬ H.P Y := by
  by_cases hlad : H.LadderReducible X
  · exact H.reduce_of_ladderReducible X hnP hlad
  · obtain ⟨c, hsep⟩ := H.many_separated_cuts X hlad hlarge
    have hcard : Fintype.card Q < Fintype.card (Fin (H.N + 1)) := by
      simpa using Nat.lt_succ_of_le H.card_profiles_le
    obtain ⟨i, j, hij, heq⟩ :=
      Fintype.exists_ne_map_eq_of_card_lt (fun k => H.profile (c k)) hcard
    obtain ⟨Y, hlt, himp⟩ :=
      H.splice_of_separated_eq_profile X (c i) (c j) (hsep i j hij) heq
    exact ⟨Y, hlt, himp hnP⟩

/-- **The descent.**  Every failure descends to one of size at most `V₀`. -/
theorem exists_small_failure (H : PumpingHypotheses.{u, v, w} α Q) :
    ∀ (X : α), ¬ H.P X → ∃ Y, H.size Y ≤ H.V₀ ∧ ¬ H.P Y := by
  intro X
  induction hn : H.size X using Nat.strong_induction_on generalizing X with
  | _ n ih =>
      intro hnP
      by_cases hle : H.size X ≤ H.V₀
      · exact ⟨X, hle, hnP⟩
      · push_neg at hle
        obtain ⟨Y, hlt, hnPY⟩ := exists_smaller_failure H X hnP hle
        exact ih (H.size Y) (hn ▸ hlt) Y rfl hnPY

/-- **The conclusion.**  If the finite base holds the predicate, so does the
whole class. -/
theorem forall_P_of_base (H : PumpingHypotheses.{u, v, w} α Q)
    (hbase : ∀ Y : α, H.size Y ≤ H.V₀ → H.P Y) :
    ∀ X : α, H.P X := by
  intro X
  by_contra hnP
  obtain ⟨Y, hsize, hnPY⟩ := exists_small_failure H X hnP
  exact hnPY (hbase Y hsize)

end GoertzelV24FiniteProfilePumping

end Mettapedia.GraphTheory.FourColor
