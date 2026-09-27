import Mettapedia.GraphTheory.FourColor.GoertzelV24PortTangleGluing
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.Pigeonhole

/-!
# Raw-noose Count pumping: the algebraic core

Cut a closed instance by a chain of nested nooses, each crossing `k` edges.  The
prefix invariant is not one cut word but the *set* of cut words realized by some
proper colouring of the prefix, and this file proves what that set does.

Three facts, and only the first is physical.

* **Each slab acts by a Boolean relation.**  A slab is a port tangle with `k`
  ordered inputs and `k` ordered outputs, and the gluing bijection (C1) says a
  colouring of a serial composite is exactly a middle word together with a
  colouring of each side realizing it.  Taking nonemptiness turns that into
  relational composition, with no cardinalities involved.
* **Supports update by relational image, and there are `2 ^ (3 ^ k)` of them.**
  A cut word takes one of three genuine Tait colours at each of the `k` crossed
  edges, so there are `3 ^ k` words and `2 ^ (3 ^ k)` possible supports.
* **A repeated support may be spliced out.**  Equal supports followed by the
  same suffix give the same terminal support, hence the same terminal
  nonemptiness against any accepting set.

Nothing here knows about nooses, planarity or bridgelessness.  Those enter only
where the geometric deletion theorem is applied, which is outside this module;
what is proved here is the finite-state algebra that the deletion consumes.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24RawNooseCountPumping

universe u

open GoertzelV24BoundedInterfaceCountLaw
open GoertzelV24PortTangleGluing
open GoertzelV24PortTangleGluing.PortTangle

/-! ## The finite alphabet of cut words -/

/-- A genuine Tait colour: one of the three nonzero Klein colours. -/
def TaitColor : Type := { c : Color // c ≠ 0 }

instance : DecidableEq TaitColor := by unfold TaitColor; infer_instance
instance : Fintype TaitColor := by unfold TaitColor; infer_instance

/-- There are exactly three Tait colours. -/
theorem card_taitColor : Fintype.card TaitColor = 3 := by decide

variable {J : Type u} [Fintype J] [DecidableEq J]

/-- A cut word crossing `k` edges is a Tait colour at each. -/
abbrev CutWord (J : Type*) := J → TaitColor

/-- There are `3 ^ k` cut words. -/
theorem card_cutWord : Fintype.card (CutWord J) = 3 ^ Fintype.card J := by
  rw [Fintype.card_fun, card_taitColor]

/-- **There are `2 ^ (3 ^ k)` possible cumulative supports.** -/
theorem card_supports :
    Fintype.card (Finset (CutWord J)) = 2 ^ (3 ^ Fintype.card J) := by
  rw [Fintype.card_finset, card_cutWord]

/-! ## Each slab acts by a Boolean relation -/

section Physical

open scoped Classical

variable {V W I K : Type u}

/-- Read a cut word as a colouring word. -/
def liftWord (x : CutWord J) : J → Color := fun j => (x j).1

/-- **The support relation of a slab.**  Input word `x` and output word `y` are
related when the slab has a proper colouring realizing both. -/
def supportRel (T : PortTangle V I (J ⊕ J)) (x y : CutWord J) : Prop :=
  Nonempty (Col T (Sum.elim (liftWord x) (liftWord y)))

/-- A realized boundary letter is a genuine Tait colour. -/
theorem word_ne_zero {P : Type u} {T : PortTangle V I P} {w : P → Color}
    (c : Col T w) (p : P) : w p ≠ 0 := by
  rw [← c.2.2]
  exact c.2.1.1 _

/-- **Serial composition is relational composition.**  This is the only place
the physical bijection is used, and it is used exactly once.

The middle word is automatically a cut word: a proper colouring has no zero
letter, so the seam colours are genuine Tait colours. -/
theorem supportRel_series (T₁ : PortTangle V I (J ⊕ J)) (T₂ : PortTangle W K (J ⊕ J))
    (x z : CutWord J) :
    supportRel (series T₁ T₂) x z ↔ ∃ y : CutWord J, supportRel T₁ x y ∧ supportRel T₂ y z := by
  constructor
  · rintro ⟨c⟩
    obtain ⟨y, c₁, c₂⟩ := gluingEquiv T₁ T₂ (liftWord x) (liftWord z) c
    have hy : ∀ j : J, y j ≠ 0 := by
      intro j
      have := word_ne_zero c₁ (Sum.inr j)
      simpa using this
    refine ⟨fun j => ⟨y j, hy j⟩, ⟨?_⟩, ⟨?_⟩⟩
    · exact c₁
    · exact c₂
  · rintro ⟨y, ⟨c₁⟩, ⟨c₂⟩⟩
    exact ⟨(gluingEquiv T₁ T₂ (liftWord x) (liftWord z)).symm ⟨liftWord y, c₁, c₂⟩⟩

/-- **The final iff, stated for the fibres themselves.**  A serially glued Tait
fibre is nonempty exactly when some middle cut word splits it. -/
theorem nonempty_col_series_iff (T₁ : PortTangle V I (J ⊕ J))
    (T₂ : PortTangle W K (J ⊕ J)) (x z : CutWord J) :
    Nonempty (Col (series T₁ T₂) (Sum.elim (liftWord x) (liftWord z))) ↔
      ∃ y : CutWord J,
        Nonempty (Col T₁ (Sum.elim (liftWord x) (liftWord y))) ∧
          Nonempty (Col T₂ (Sum.elim (liftWord y) (liftWord z))) :=
  supportRel_series T₁ T₂ x z

/-- **The link between the physical law and the finite-state algebra.**  The set
of words a two-slab prefix realizes is the relational image of what the first
slab realizes, which is the update rule the pumping runs on. -/
theorem supportRel_series_eq_supportStep (T₁ : PortTangle V I (J ⊕ J))
    (T₂ : PortTangle W K (J ⊕ J)) (x : CutWord J) :
    {z | supportRel (series T₁ T₂) x z} =
      supportStep (supportRel T₂) {y | supportRel T₁ x y} := by
  ext z
  simpa [supportStep] using supportRel_series T₁ T₂ x z

/-- The Boolean support of the Count matrix is exactly the support relation, so
the matrix formulation and the nonemptiness formulation agree wherever the
fibres are finite. -/
theorem support_countMatrix_eq_supportRel (T : PortTangle V I (J ⊕ J))
    [∀ x y : CutWord J, Fintype (Col T (Sum.elim (liftWord x) (liftWord y)))]
    (x y : CutWord J) :
    GoertzelV24BoundedInterfaceCountLaw.support (countMatrix
      (Col := fun a b : CutWord J => Col T (Sum.elim (liftWord a) (liftWord b)))) x y ↔
      supportRel T x y := by
  simpa [GoertzelV24BoundedInterfaceCountLaw.support, countMatrix, supportRel] using
    (Fintype.card_pos_iff (α := Col T (Sum.elim (liftWord x) (liftWord y))))

end Physical

/-! ## The finite-state algebra of prefix supports -/

section Algebra

open scoped Classical

/-- **There are `2 ^ (3 ^ k)` possible cumulative supports**, read as sets. -/
theorem card_supports_set :
    Fintype.card (Set (CutWord J)) = 2 ^ (3 ^ Fintype.card J) := by
  rw [Fintype.card_set, card_cutWord]

/-- The cumulative support after a serial run of slabs.  This is the Count law's
run, instantiated at cut words. -/
def prefixSupport (Rs : List (CutWord J → CutWord J → Prop))
    (S₀ : Set (CutWord J)) : Set (CutWord J) :=
  runSupport Rs S₀

/-- **Supports update by relational image.**  One more slab sends the support to
its image under that slab's relation. -/
theorem prefixSupport_cons (R : CutWord J → CutWord J → Prop)
    (Rs : List (CutWord J → CutWord J → Prop)) (S₀ : Set (CutWord J)) :
    prefixSupport (R :: Rs) S₀ = prefixSupport Rs (supportStep R S₀) := rfl

/-- The one-step image, in the manuscript's displayed form. -/
theorem supportStep_eq (R : CutWord J → CutWord J → Prop) (S : Set (CutWord J)) :
    supportStep R S = {y | ∃ x ∈ S, R x y} := rfl

/-- **Pigeonhole on supports.**  More cut positions than there are supports
force two prefixes to agree. -/
theorem exists_eq_prefixSupport {N : ℕ} (S : Fin (N + 1) → Set (CutWord J))
    (hN : 2 ^ (3 ^ Fintype.card J) ≤ N) :
    ∃ i j : Fin (N + 1), i ≠ j ∧ S i = S j := by
  have hcard : Fintype.card (Set (CutWord J)) < Fintype.card (Fin (N + 1)) := by
    rw [card_supports_set, Fintype.card_fin]
    omega
  exact Fintype.exists_ne_map_eq_of_card_lt S hcard

/-- **A repeated support may be spliced out.**  Equal prefix supports followed by
the same suffix give the same terminal support. -/
theorem prefixSupport_delete_block
    (pre mid suf : List (CutWord J → CutWord J → Prop)) (S₀ : Set (CutWord J))
    (hrepeat : prefixSupport (pre ++ mid) S₀ = prefixSupport pre S₀) :
    prefixSupport (pre ++ mid ++ suf) S₀ = prefixSupport (pre ++ suf) S₀ :=
  runSupport_delete_block pre mid suf S₀ hrepeat

/-- **Terminal acceptance is unchanged by the splice.**  Against any accepting
set of terminal words, deleting the repeated block preserves nonemptiness -- and
in particular preserves a zero count. -/
theorem terminal_nonempty_congr
    (pre mid suf : List (CutWord J → CutWord J → Prop)) (S₀ : Set (CutWord J))
    (F : Set (CutWord J))
    (hrepeat : prefixSupport (pre ++ mid) S₀ = prefixSupport pre S₀) :
    (prefixSupport (pre ++ mid ++ suf) S₀ ∩ F).Nonempty ↔
      (prefixSupport (pre ++ suf) S₀ ∩ F).Nonempty := by
  rw [prefixSupport_delete_block pre mid suf S₀ hrepeat]

end Algebra

end GoertzelV24RawNooseCountPumping

end Mettapedia.GraphTheory.FourColor
