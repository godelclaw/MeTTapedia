import Mettapedia.GraphTheory.FourColor.FourPortCountRewire
import Mathlib.Order.Monotone.Basic

/-!
# Scalar normalization does not make the tangle Count image finite

A literal rung has two cubic vertices, one interior edge, and two ports on
each side. Its monochromatic two-port transitions form the three-colour
inequality matrix. Repetition changes relative multiplicities, not merely
an overall factor. The counting law used here is the physical gluing
bijection; no hypothesis about least counterexamples is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.ProjectiveTangleCount

open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open FourPortCountRewire
open GoertzelV24PortTangleCutParity

abbrev Word := Bool → Color

def rung : PortTangle Bool Bool (Bool ⊕ Bool) where
  vert := Sum.elim id (Sum.elim id id)
  alpha := Bool.not
  alpha_involutive := by intro d; cases d <;> rfl
  alpha_fixfree := by intro d; cases d <;> decide
  no_self_loops := by intro d; cases d <;> decide

def boundary (x y : Word) : SquareBoundaryWord :=
  ![x false, y false, y true, x true]

def canonical (x y : Word) (z : Color) : Coloring rung where
  color := Sum.elim (fun _ => z) (Sum.elim x y)
  invariant := fun _ => rfl

theorem canonical_proper : ∀ x y z,
    IsProper (canonical x y z) ↔ IsExtension false (boundary x y) z := by
  intro x y z
  simp [IsProper, canonical, rung, IsExtension, boundary, ProperColorTriple,
    Sum.forall, Bool.forall_bool]
  aesop

theorem coloring_canonical (c : Coloring rung) :
    c = canonical (fun p => word c (.inl p)) (fun p => word c (.inr p))
      (c.color (.inl false)) := by
  apply Coloring.ext'
  funext d
  rcases d with b | (p | p)
  · cases b
    · rfl
    · exact c.invariant false
  · rfl
  · rfl

def rungColEquiv (x y : Word) :
    Col rung (Sum.elim x y) ≃ {z : Color // IsExtension false (boundary x y) z} where
  toFun c := ⟨c.1.color (.inl false), by
    have hx : (fun p => word c.1 (.inl p)) = x := by
      funext p; exact congrFun c.2.2 (.inl p)
    have hy : (fun p => word c.1 (.inr p)) = y := by
      funext p; exact congrFun c.2.2 (.inr p)
    have hp := c.2.1
    rw [coloring_canonical c.1, hx, hy] at hp
    exact (canonical_proper x y _).1 hp⟩
  invFun z := ⟨canonical x y z.1, (canonical_proper x y z.1).2 z.2, rfl⟩
  left_inv c := by
    apply Subtype.ext
    have hx : (fun p => word c.1 (.inl p)) = x := by
      funext p; exact congrFun c.2.2 (.inl p)
    have hy : (fun p => word c.1 (.inr p)) = y := by
      funext p; exact congrFun c.2.2 (.inr p)
    exact (hx ▸ hy ▸ coloring_canonical c.1).symm
  right_inv _ := rfl

noncomputable def count {V I : Type} (T : PortTangle V I (Bool ⊕ Bool))
    (x y : Word) : Nat := Nat.card (Col T (Sum.elim x y))

def rungMatrix (x y : Word) : Nat := fiberCount false (boundary x y)

theorem count_rung (x y : Word) : count rung x y = rungMatrix x y := by
  rw [count, Nat.card_congr (rungColEquiv x y), Nat.card_eq_fintype_card]
  simp [rungMatrix, fiberCount, Fintype.card_subtype]

local instance finiteColoring {V I P : Type} [Finite I] [Finite P]
    (T : PortTangle V I P) : Finite (Coloring T) :=
  Finite.of_injective (fun c => c.color) (fun _ _ h => Coloring.ext' h)

local instance finiteCol {V I P : Type} [Finite I] [Finite P]
    (T : PortTangle V I P) (w : P → Color) : Finite (Col T w) :=
  inferInstanceAs (Finite {c : Coloring T // IsProper c ∧ word c = w})

theorem count_series {V W I K : Type} [Finite I] [Finite K]
    (T : PortTangle V I (Bool ⊕ Bool)) (U : PortTangle W K (Bool ⊕ Bool))
    (x z : Word) : count (series T U) x z = ∑ y : Word, count T x y * count U y z := by
  rw [count, Nat.card_congr (gluingEquiv T U x z), Nat.card_sigma]
  simp only [Nat.card_prod, count]

theorem rung_cubic : IsCubic rung := by
  unfold IsCubic dartsAt
  decide +kernel

theorem series_cubic {V W I K : Type} [Fintype V] [Fintype W] [Fintype I] [Fintype K]
    [DecidableEq V] [DecidableEq W] [DecidableEq I] [DecidableEq K]
    (T : PortTangle V I (Bool ⊕ Bool)) (U : PortTangle W K (Bool ⊕ Bool))
    (hT : IsCubic T) (hU : IsCubic U) : IsCubic (series T U) := by
  intro v
  rcases v with v | v
  · rw [← hT v]
    refine (Finset.card_bij (fun d _ => emb₁ (K := K) (Z := Bool) d) ?_ ?_ ?_).symm
    · intro d hd
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      change seriesVert T U (emb₁ d) = Sum.inl v
      rw [vert_emb₁]
      exact congrArg Sum.inl (Finset.mem_filter.1 hd).2
    · intro a _ b _ hab
      exact emb₁_injective hab
    · intro d hd
      obtain ⟨a, rfl⟩ := exists_emb₁_of_vert_inl T U (Finset.mem_filter.1 hd).2
      refine ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      have hv : seriesVert T U (emb₁ a) = Sum.inl v := (Finset.mem_filter.1 hd).2
      rw [vert_emb₁] at hv
      exact Sum.inl.inj hv
  · rw [← hU v]
    refine (Finset.card_bij (fun d _ => emb₂ (I := I) (X := Bool) d) ?_ ?_ ?_).symm
    · intro d hd
      refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
      change seriesVert T U (emb₂ d) = Sum.inr v
      rw [vert_emb₂]
      exact congrArg Sum.inr (Finset.mem_filter.1 hd).2
    · intro a _ b _ hab
      exact emb₂_injective hab
    · intro d hd
      obtain ⟨a, rfl⟩ := exists_emb₂_of_vert_inr T U (Finset.mem_filter.1 hd).2
      refine ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      have hv : seriesVert T U (emb₂ a) = Sum.inr v := (Finset.mem_filter.1 hd).2
      rw [vert_emb₂] at hv
      exact Sum.inr.inj hv

/-- Finite literal cubic tangles, with no rotation or counterexample data. -/
structure Model where
  V : Type
  I : Type
  [vertices : Fintype V]
  [interiors : Fintype I]
  [decVertex : DecidableEq V]
  [decInterior : DecidableEq I]
  tangle : PortTangle V I (Bool ⊕ Bool)
  cubic : IsCubic tangle

attribute [instance] Model.vertices Model.interiors Model.decVertex Model.decInterior

def rungModel : Model where
  V := Bool
  I := Bool
  tangle := rung
  cubic := rung_cubic

def Model.append (T U : Model) : Model where
  V := T.V ⊕ U.V
  I := (T.I ⊕ U.I) ⊕ (Bool ⊕ Bool)
  tangle := series T.tangle U.tangle
  cubic := series_cubic T.tangle U.tangle T.cubic U.cubic

/-- `chain n` has `n+1` rungs; even the base is a literal cubic tangle. -/
def chain : Nat → Model
  | 0 => rungModel
  | n + 1 => (chain n).append rungModel

def red : Color := (1, 0)
def blue : Color := (0, 1)
def mono (c : Color) : Word := fun _ => c

def delta : Word → Nat := fun w => if w = mono red then 1 else 0
def uniform : Word → Nat := fun w => if w false = w true ∧ w false ≠ 0 then 1 else 0
def push (v : Word → Nat) : Word → Nat := fun z => ∑ y, v y * rungMatrix y z

theorem push_add (v w : Word → Nat) : push (v + w) = push v + push w := by
  funext z
  simp [push, add_mul, Finset.sum_add_distrib]

theorem push_smul (a : Nat) (v : Word → Nat) : push (a • v) = a • push v := by
  funext z
  simp [push, smul_eq_mul, mul_assoc, Finset.mul_sum]

theorem push_delta : push delta = rungMatrix (mono red) := by decide +kernel
theorem push_twice_delta : push (push delta) = delta + uniform := by decide +kernel
theorem push_twice_uniform : push (push uniform) = 4 • uniform := by decide +kernel

def coefficient : Nat → Nat
  | 0 => 0
  | n + 1 => 4 * coefficient n + 1

def row : Nat → Word → Nat
  | 0 => delta
  | n + 1 => push (row n)

theorem chain_row (n : Nat) : count (chain n).tangle (mono red) = row (n + 1) := by
  induction n with
  | zero =>
    funext z
    exact (count_rung (mono red) z).trans (congrFun push_delta z).symm
  | succ n ih =>
    funext z
    change count (series (chain n).tangle rung) (mono red) z = push (row (n + 1)) z
    rw [count_series]
    simp only [count_rung, ih, push]

theorem row_even (n : Nat) : row (2 * n) = delta + coefficient n • uniform := by
  induction n with
  | zero => simp [row, coefficient]
  | succ n ih =>
    rw [show 2 * (n + 1) = (2 * n + 1) + 1 by omega, row, row, ih,
      push_add, push_add, push_smul, push_smul, push_twice_delta, push_twice_uniform]
    funext w
    simp [coefficient]
    ring

theorem coefficient_strictMono : StrictMono coefficient := by
  apply strictMono_nat_of_lt_succ
  intro n
  simp only [coefficient]
  omega

theorem row_even_red (n : Nat) : row (2 * n) (mono red) = coefficient n + 1 := by
  rw [row_even]
  simp [delta, uniform, mono, red, Nat.add_comm]

theorem row_even_blue (n : Nat) : row (2 * n) (mono blue) = coefficient n := by
  rw [row_even]
  have h : mono blue ≠ mono red := by decide +kernel
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, delta, if_neg h]
  rw [show uniform (mono blue) = 1 by decide +kernel]
  omega

/-- Equality after arbitrary positive integer rescaling is already rigid. -/
theorem projective_row_injective {n m a b : Nat} (ha : 0 < a)
    (heq : a • row (2 * n) = b • row (2 * m)) : n = m := by
  have hr := congrFun heq (mono red)
  have hb := congrFun heq (mono blue)
  simp only [Pi.smul_apply, smul_eq_mul, row_even_red] at hr
  simp only [Pi.smul_apply, smul_eq_mul, row_even_blue] at hb
  have hab : a = b := by nlinarith
  subst b
  have hn : coefficient n = coefficient m := Nat.eq_of_mul_eq_mul_left ha hb
  exact coefficient_strictMono.injective hn

/-- The changing relative counts carry no new zero/nonzero information here. -/
theorem even_row_support (n : Nat) (w : Word) :
    0 < row (2 * (n + 1)) w ↔ w false = w true ∧ w false ≠ 0 := by
  rw [row_even]
  change 0 < delta w + coefficient (n + 1) * uniform w ↔ _
  by_cases hw : w false = w true ∧ w false ≠ 0
  · have hp : 0 < coefficient (n + 1) := by simp only [coefficient]; omega
    rw [show uniform w = 1 from if_pos hw, mul_one]
    exact ⟨fun _ => hw, fun _ => by omega⟩
  · have hd : w ≠ mono red := by
      intro hd
      subst w
      exact hw (by decide +kernel)
    simp [uniform, delta, hw, hd]

/-- No finite exact projective code covers this physical composition family. -/
theorem no_finite_projective_chain_code {Q : Type*} [Finite Q] (encode : Nat → Q)
    (hfaithful : ∀ n m, encode n = encode m → ∃ a b : Nat, 0 < a ∧ 0 < b ∧
      a • count (chain (2 * n + 1)).tangle (mono red) =
        b • count (chain (2 * m + 1)).tangle (mono red)) : False := by
  have hi : Function.Injective encode := by
    intro n m hnm
    obtain ⟨a, b, ha, _, hab⟩ := hfaithful n m hnm
    rw [chain_row, chain_row] at hab
    have heq : a • row (2 * (n + 1)) = b • row (2 * (m + 1)) := by
      simpa [Nat.mul_add, Nat.add_assoc] using hab
    have := projective_row_injective ha heq
    omega
  letI : Finite Nat := Finite.of_injective encode hi
  exact not_finite Nat

end Mettapedia.GraphTheory.FourColor.ProjectiveTangleCount
