import Mettapedia.GraphTheory.FourColor.GoertzelV24Square
import Mettapedia.GraphTheory.FourColor.GoertzelV24ClosedCountReplacement
import Mettapedia.GraphTheory.FourColor.PhysicalColorNoFanout

/-!
# Exact Count and a limitation of the two-vertex reconnection

The two planar connections of four cyclic ports are `I = 01|23` and
`H = 03|12`, each with two cubic vertices and one interior edge. These are
not the two wire smoothings, whose counts occur as correction terms.

For any colourable finite cubic exterior with four unrestricted ports,
if closing with I is uncolourable, closing with H is colourable. This is
an actual serial-gluing statement: parity and the existing no-fanout
theorem prevent both connections from failing. No planarity is assumed.

Consequently the elementary reconnection is not a zero-Count-preserving
rewrite. This does not exclude composite rewrites, growing interfaces,
or a different invariant. Exterior colourability is an explicit, essential
hypothesis; no counterexample-class supplier is asserted here.
-/

namespace Mettapedia.GraphTheory.FourColor.FourPortCountRewire

open GoertzelV24PortTangleGluing GoertzelV24PortTangleGluing.PortTangle
open GoertzelV24ClosedCountReplacement GoertzelV24PortTangleCutParity

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- False is I, with port pairs 01 and 23; true is H, with 03 and 12. -/
def IsExtension (h : Bool) (w : SquareBoundaryWord) (z : Color) : Prop :=
  if h then ProperColorTriple (w 0) (w 3) z ∧ ProperColorTriple (w 1) (w 2) z
  else ProperColorTriple (w 0) (w 1) z ∧ ProperColorTriple (w 2) (w 3) z
  deriving Decidable

def fiberCount (h : Bool) (w : SquareBoundaryWord) : ℕ :=
  (Finset.univ.filter (IsExtension h w)).card

/-- Wire smoothings, including the nonzero requirement on all ports. -/
def smoothingCount (h : Bool) (w : SquareBoundaryWord) : ℕ :=
  if w.Nonzero ∧ (if h then w 0 = w 3 ∧ w 1 = w 2
                           else w 0 = w 1 ∧ w 2 = w 3) then 1 else 0

theorem fiber_balance : ∀ w : SquareBoundaryWord,
    fiberCount false w + smoothingCount false w =
      fiberCount true w + smoothingCount true w := by
  decide +kernel

theorem square_balance (w : SquareBoundaryWord) :
    (squareExtensions w).card = smoothingCount false w + smoothingCount true w := by
  rw [squareFiberTable]
  revert w
  decide +kernel

/-- Nonnegative exterior multiplicities, with no bound on their size. -/
def weightedCount (W f : SquareBoundaryWord → ℕ) : ℕ := ∑ w, W w * f w

theorem weighted_balance (W : SquareBoundaryWord → ℕ) :
    weightedCount W (fiberCount false) + weightedCount W (smoothingCount false) =
      weightedCount W (fiberCount true) + weightedCount W (smoothingCount true) := by
  simp only [weightedCount, ← Finset.sum_add_distrib, ← Nat.mul_add, fiber_balance]

theorem flip_zero_iff_smoothing_balance (W : SquareBoundaryWord → ℕ)
    (hzero : weightedCount W (fiberCount false) = 0) :
    weightedCount W (fiberCount true) = 0 ↔
      weightedCount W (smoothingCount false) = weightedCount W (smoothingCount true) := by
  have h := weighted_balance W
  omega

theorem square_zero_iff_both_smoothings_zero (W : SquareBoundaryWord → ℕ) :
    weightedCount W (fun w => (squareExtensions w).card) = 0 ↔
      weightedCount W (smoothingCount false) = 0 ∧
      weightedCount W (smoothingCount true) = 0 := by
  simp only [weightedCount, square_balance, Nat.mul_add, Finset.sum_add_distrib,
    Nat.add_eq_zero_iff]

/-- Which of the two vertices carries a port. -/
def portVertex (h : Bool) (p : Fin 4) : Bool :=
  if h then decide (p = 1 ∨ p = 2) else decide (p = 2 ∨ p = 3)

/-- The literal two-vertex piece, with an empty outer boundary. -/
def cap (h : Bool) : PortTangle Bool Bool (Fin 4 ⊕ PEmpty.{1}) where
  vert := Sum.elim id (Sum.elim (portVertex h) PEmpty.elim)
  alpha := Bool.not
  alpha_involutive := by intro d; cases d <;> rfl
  alpha_fixfree := by intro d; cases d <;> decide
  no_self_loops := by intro d; change d ≠ !d; cases d <;> decide

theorem cap_cubic : ∀ h, IsCubic (cap h) := by
  unfold IsCubic dartsAt
  decide +kernel

def capColoring (h : Bool) (w : SquareBoundaryWord) (z : Color) : Coloring (cap h) where
  color := Sum.elim (fun _ => z) (Sum.elim w PEmpty.elim)
  invariant := fun _ => rfl

theorem capColoring_proper_iff : ∀ h w z,
    IsProper (capColoring h w z) ↔ IsExtension h w z := by
  intro h w z
  cases h <;>
    simp [IsProper, capColoring, cap, portVertex, IsExtension, ProperColorTriple,
      Sum.forall, Bool.forall_bool, Fin.forall_fin_succ] <;> aesop

theorem coloring_eq_canonical (h : Bool) (c : Coloring (cap h)) :
    c = capColoring h (fun p => word c (.inl p)) (c.color (.inl false)) := by
  apply Coloring.ext'
  funext d
  rcases d with b | (p | e)
  · cases b
    · rfl
    · exact c.invariant false
  · rfl
  · exact e.elim

theorem mem_innerSupport_cap_iff (h : Bool) (w : SquareBoundaryWord) :
    w ∈ innerSupport (cap h) ↔ ∃ z, IsExtension h w z := by
  constructor
  · rintro ⟨⟨c, hc, hw⟩⟩
    refine ⟨c.color (.inl false), ?_⟩
    have he : (fun p => word c (.inl p)) = w := by
      funext p
      exact congrFun hw (.inl p)
    have hc' := hc
    rw [coloring_eq_canonical h c, he] at hc'
    exact (capColoring_proper_iff h w _).1 hc'
  · rintro ⟨z, hz⟩
    exact ⟨⟨capColoring h w z, (capColoring_proper_iff h w z).2 hz, rfl⟩⟩

/-- The same identification preserves multiplicities, not merely support. -/
def capColEquiv (h : Bool) (w : SquareBoundaryWord) :
    Col (cap h) (Sum.elim w PEmpty.elim) ≃ {z : Color // IsExtension h w z} where
  toFun c := ⟨c.1.color (.inl false), by
    have he : (fun p => word c.1 (.inl p)) = w := by
      funext p
      exact congrFun c.2.2 (.inl p)
    have hc := c.2.1
    rw [coloring_eq_canonical h c.1, he] at hc
    exact (capColoring_proper_iff h w _).1 hc⟩
  invFun z := ⟨capColoring h w z.1, (capColoring_proper_iff h w z.1).2 z.2, rfl⟩
  left_inv c := by
    apply Subtype.ext
    have he : (fun p => word c.1 (.inl p)) = w := by
      funext p
      exact congrFun c.2.2 (.inl p)
    exact (he ▸ coloring_eq_canonical h c.1).symm
  right_inv _ := rfl

theorem card_cap_col (h : Bool) (w : SquareBoundaryWord) :
    Nat.card (Col (cap h) (Sum.elim w PEmpty.elim)) = fiberCount h w := by
  rw [Nat.card_congr (capColEquiv h w), Nat.card_eq_fintype_card]
  simp [Fintype.card_subtype, fiberCount]

/-- Cut parity reduces the two-vertex extension test to one inequality. -/
theorem extension_iff_ne : ∀ h (w : SquareBoundaryWord),
    w.Nonzero → (∑ p, w p) = 0 →
      ((∃ z, IsExtension h w z) ↔ w 0 ≠ w (if h then 3 else 1)) := by
  decide +kernel

section Exterior

variable {V I : Type} [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I]

def exteriorWord {T : PortTangle V I (PEmpty.{1} ⊕ Fin 4)} (c : Coloring T) :
    SquareBoundaryWord := fun p => word c (.inr p)

omit [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] in
private theorem exteriorWord_nonzero {T : PortTangle V I (PEmpty.{1} ⊕ Fin 4)}
    {c : Coloring T} (hc : IsProper c) : (exteriorWord c).Nonzero :=
  ⟨hc.1 (.inr (.inr 0)), hc.1 (.inr (.inr 1)),
   hc.1 (.inr (.inr 2)), hc.1 (.inr (.inr 3))⟩

private theorem exteriorWord_sum {T : PortTangle V I (PEmpty.{1} ⊕ Fin 4)}
    (hT : IsCubic T) {c : Coloring T} (hc : IsProper c) :
    (∑ p, exteriorWord c p) = 0 := by
  simpa [exteriorWord, Fintype.sum_sum_type] using sum_boundaryWord_eq_zero T hT c hc

omit [Fintype V] [Fintype I] [DecidableEq V] [DecidableEq I] in
theorem closedColorable_cap_iff (T : PortTangle V I (PEmpty.{1} ⊕ Fin 4)) (h : Bool) :
    ClosedColorable T (cap h) ↔
      ∃ c : Coloring T, IsProper c ∧ ∃ z, IsExtension h (exteriorWord c) z := by
  rw [closedColorable_iff]
  constructor
  · rintro ⟨w, ⟨⟨c, hc, hw⟩⟩, hcap⟩
    have he : exteriorWord c = w := by
      funext p
      exact congrFun hw (.inr p)
    exact ⟨c, hc, he ▸ (mem_innerSupport_cap_iff h w).1 hcap⟩
  · rintro ⟨c, hc, z, hz⟩
    refine ⟨exteriorWord c, ⟨⟨c, hc, ?_⟩⟩, (mem_innerSupport_cap_iff _ _).2 ⟨z, hz⟩⟩
    funext p
    rcases p with e | p
    · exact e.elim
    · rfl

/-- The two actual closures cannot both have zero Count when the finite cubic
exterior is colourable. This does not assume planarity or connectedness. -/
theorem flip_colorable_of_original_not_colorable
    (T : PortTangle V I (PEmpty.{1} ⊕ Fin 4)) (hT : IsCubic T)
    (hne : ∃ c : Coloring T, IsProper c)
    (hzero : ¬ ClosedColorable T (cap false)) : ClosedColorable T (cap true) := by
  classical
  by_contra hzero'
  apply PhysicalColorNoFanout.not_three_forced_equal T hT hne
    (.inr 0) (.inr 1) (.inr 3) (by decide) (by decide) (by decide)
  intro c hc
  have hfail : ∀ h : Bool, ¬ ∃ z, IsExtension h (exteriorWord c) z := by
    intro h hz
    have hj := (closedColorable_cap_iff T h).2 ⟨c, hc, hz⟩
    cases h
    · exact hzero hj
    · exact hzero' hj
  have heq : ∀ h : Bool, exteriorWord c 0 = exteriorWord c (if h then 3 else 1) := by
    intro h
    by_contra hn
    exact hfail h ((extension_iff_ne h _ (exteriorWord_nonzero hc)
      (exteriorWord_sum hT hc)).2 hn)
  exact ⟨heq false, heq true⟩

end Exterior

end Mettapedia.GraphTheory.FourColor.FourPortCountRewire
