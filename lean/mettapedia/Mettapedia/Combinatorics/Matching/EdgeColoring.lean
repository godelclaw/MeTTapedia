import Mathlib
import Mettapedia.Combinatorics.Matching.Amplitude

/-!
# Colouring the matchings

Some vertex sets carry a solution for a simple reason: their perfect matchings can
be given one colour each, in such a way that no matching mixes colours.  Weight
every edge one exactly when both its endpoints wear that edge's colour, and the
amplitude of a colouring becomes a count — the number of matchings the colouring
admits.

The colouring is allowed to be *partial*.  An uncoloured edge weighs zero, so a
matching using one is never admitted, which is how a graph with missing edges is
expressed here: leave its non-edges uncoloured.  Without that the construction
would be confined to vertex sets whose every matching is monochromatic, and the
only interesting example would be four vertices.

Two conditions make the count come out right.  Coloured edges of a single matching
must agree, which forces any colouring admitting a matching to be constant; and
each colour must be worn by exactly one matching, which makes the constant
colourings count one.
-/

namespace ColourPerMatching

open Amplitude

variable {V C : Type*} [Fintype V] [DecidableEq V] [DecidableEq C]

/-- The weights induced by a partial edge colouring: an edge weighs one exactly
when it is coloured and both its endpoints wear that colour. -/
noncomputable def weightOf (ec : V → V → Option C) (hsymm : ∀ u v, ec u v = ec v u) :
    Sym2 (V × C) → ℂ :=
  Sym2.lift ⟨fun p q => if p.2 = q.2 ∧ ec p.1 q.1 = some p.2 then 1 else 0, by
    intro p q
    dsimp only
    by_cases h : p.2 = q.2
    · rw [h, hsymm p.1 q.1]
    · rw [if_neg (fun hh => h hh.1), if_neg (fun hh => h hh.1.symm)]⟩

omit [Fintype V] [DecidableEq V] in
theorem weightOf_apply (ec : V → V → Option C) (hsymm : ∀ u v, ec u v = ec v u)
    (u v : V) (i j : C) :
    weightOf ec hsymm s((u, i), (v, j)) = if i = j ∧ ec u v = some i then 1 else 0 := rfl

/-- The matchings a colouring admits: those all of whose edges are coloured, with
both endpoints wearing that colour. -/
def admits (ec : V → V → Option C) (c : V → C) : Finset (Equiv.Perm V) :=
  (pairings V).filter (fun σ => ∀ x, c x = c (σ x) ∧ ec x (σ x) = some (c x))

/-- **The amplitude counts.**  Under these weights every matching contributes one
or nothing, so the amplitude is the number of matchings the colouring admits. -/
theorem amplitude_eq_card (ec : V → V → Option C) (hsymm : ∀ u v, ec u v = ec v u)
    (c : V → C) :
    amplitude (weightOf ec hsymm) c = ((admits ec c).card : ℂ) := by
  have hterm : ∀ σ ∈ pairings V,
      (∏ e ∈ edges σ, weightOf ec hsymm (Sym2.map (paint c) e))
        = if (∀ x, c x = c (σ x) ∧ ec x (σ x) = some (c x)) then 1 else 0 := by
    intro σ _
    by_cases h : ∀ x, c x = c (σ x) ∧ ec x (σ x) = some (c x)
    · rw [if_pos h]
      refine Finset.prod_eq_one (fun e he => ?_)
      obtain ⟨y, -, rfl⟩ := Finset.mem_image.mp he
      rw [show Sym2.map (paint c) s(y, σ y) = s((y, c y), (σ y, c (σ y))) from rfl,
        weightOf_apply, if_pos ⟨(h y).1, (h y).2⟩]
    · rw [if_neg h]
      obtain ⟨x, hx⟩ := not_forall.mp h
      refine Finset.prod_eq_zero (i := s(x, σ x))
        (Finset.mem_image_of_mem _ (Finset.mem_univ x)) ?_
      rw [show Sym2.map (paint c) s(x, σ x) = s((x, c x), (σ x, c (σ x))) from rfl,
        weightOf_apply, if_neg (fun hh => hx ⟨hh.1, hh.2⟩)]
  rw [amplitude, Finset.sum_congr rfl hterm, Finset.sum_boole, admits]

/-- **Agreeing matchings force constant colourings.**  If the coloured edges of a
matching always agree, a colouring admitting one has no choice but to be
constant. -/
theorem const_of_admits (ec : V → V → Option C)
    (hmono : ∀ σ ∈ pairings V, (∀ x, (ec x (σ x)).isSome) → ∀ x y : V, ∀ k l : C,
      ec x (σ x) = some k → ec y (σ y) = some l → k = l)
    {c : V → C} {σ : Equiv.Perm V} (hσ : σ ∈ admits ec c) : ∀ x y : V, c x = c y := by
  intro x y
  obtain ⟨hmem, h⟩ := Finset.mem_filter.mp hσ
  exact hmono σ hmem (fun z => by rw [(h z).2]; rfl) x y (c x) (c y) (h x).2 (h y).2

/-- Hence a non-constant colouring has vanishing amplitude. -/
theorem amplitude_eq_zero_of_not_const (ec : V → V → Option C)
    (hsymm : ∀ u v, ec u v = ec v u)
    (hmono : ∀ σ ∈ pairings V, (∀ x, (ec x (σ x)).isSome) → ∀ x y : V, ∀ k l : C,
      ec x (σ x) = some k → ec y (σ y) = some l → k = l)
    {c : V → C} (hc : ¬ ∀ x y : V, c x = c y) :
    amplitude (weightOf ec hsymm) c = 0 := by
  rw [amplitude_eq_card, Nat.cast_eq_zero, Finset.card_eq_zero,
    Finset.eq_empty_iff_forall_notMem]
  exact fun σ hσ => hc (const_of_admits ec hmono hσ)

/-- A constant colouring admits exactly the matchings wearing its colour. -/
theorem admits_const (ec : V → V → Option C) (k : C) :
    admits ec (Amplitude.const k)
      = (pairings V).filter (fun σ => ∀ x, ec x (σ x) = some k) := by
  refine Finset.filter_congr (fun σ _ => ?_)
  exact ⟨fun h x => (h x).2, fun h x => ⟨rfl, h x⟩⟩

/-- **Colour-per-matching gives a solution.**  If the coloured edges of every
totally-coloured matching agree and each colour is worn by exactly one matching, the induced weights
give every constant colouring amplitude one and every other colouring zero. -/
theorem amplitude_spec (ec : V → V → Option C) (hsymm : ∀ u v, ec u v = ec v u)
    (hmono : ∀ σ ∈ pairings V, (∀ x, (ec x (σ x)).isSome) → ∀ x y : V, ∀ k l : C,
      ec x (σ x) = some k → ec y (σ y) = some l → k = l)
    (huniq : ∀ k : C, ((pairings V).filter (fun σ => ∀ x, ec x (σ x) = some k)).card = 1) :
    (∀ k : C, amplitude (weightOf ec hsymm) (Amplitude.const k) = 1) ∧
      (∀ c : V → C, ¬ (∀ x y : V, c x = c y) →
        amplitude (weightOf ec hsymm) c = 0) := by
  refine ⟨fun k => ?_, fun c hc => amplitude_eq_zero_of_not_const ec hsymm hmono hc⟩
  rw [amplitude_eq_card, admits_const, huniq k]
  norm_num

end ColourPerMatching
