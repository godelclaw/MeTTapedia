import Mettapedia.GraphTheory.FourColor.GoertzelV24CompositeSeamMultigraph
import Mathlib.GroupTheory.Perm.Cycle.Basic

/-!
# The composed rotation system is cubic and rotation-cyclic

Two more fields of the target map class, delivered on the literal
`composeRotationSystem`.

*Cubicity.*  A retained vertex loses exactly its cut incidences and gains the
corresponding seam incidences, so its dart count is unchanged.  On the carrier
this is immediate: the composite darts over a left vertex `v` are exactly the
left darts over `v`, boundary darts included, transported through the carrier
reassociation.  So if every vertex of each side carries three darts — the cut
half-edges counted — every vertex of the composite does.

*Rotation-cyclicity.*  The composite rotation is the disjoint sum of the two
side rotations, conjugated by the carrier reassociation.  Conjugation and
disjoint sums both preserve "lie on one cycle", so two composite darts at one
vertex lie on one rotation cycle whenever the side's do.

Sphericity is not here.  It needs face orbits and an oriented matching, which
the carrier does not record.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24CompositeSeamCubic

open GoertzelV24OpenTangleComposition
open GoertzelV24OpenTangleComposition.OpenTangleData
open GoertzelV24CompositeSeamMultigraph
open GoertzelV24RotationSpliceConstructor
open GoertzelV24FaceDualConnectedness

/-! ## Side-level notions -/

section Side

variable {V I B : Type*} [Fintype I] [Fintype B] [DecidableEq I] [DecidableEq B] [DecidableEq V]

/-- The darts of an open tangle at a vertex, boundary half-edges included. -/
def openDartsAt (T : OpenTangleData V I B) (v : V) : Finset (I ⊕ B) :=
  Finset.univ.filter fun d => T.vertOf d = v

/-- Cubic at every vertex, counting cut half-edges. -/
def OpenIsCubic (T : OpenTangleData V I B) : Prop :=
  ∀ v : V, (openDartsAt T v).card = 3

/-- Darts at one vertex lie on one rotation cycle. -/
def OpenRotationCyclic (T : OpenTangleData V I B) : Prop :=
  ∀ d d' : I ⊕ B, T.vertOf d = T.vertOf d' → T.rho.SameCycle d d'

end Side

/-! ## Permutation facts -/

section Perm

variable {α β : Type*}

/-- Powers of a disjoint sum act componentwise on the left summand. -/
theorem sumCongr_pow_inl (σ : Equiv.Perm α) (τ : Equiv.Perm β) (n : ℕ) (a : α) :
    ((Equiv.sumCongr σ τ) ^ n) (Sum.inl a) = Sum.inl ((σ ^ n) a) := by
  induction n generalizing a with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      rw [Equiv.Perm.sumCongr_apply, Sum.map_inl, ih]

theorem sumCongr_pow_inr (σ : Equiv.Perm α) (τ : Equiv.Perm β) (n : ℕ) (b : β) :
    ((Equiv.sumCongr σ τ) ^ n) (Sum.inr b) = Sum.inr ((τ ^ n) b) := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
      rw [Equiv.Perm.sumCongr_apply, Sum.map_inr, ih]

/-- Same cycle on a summand lifts to the disjoint sum. -/
theorem sameCycle_sumCongr_inl [Finite α] (σ : Equiv.Perm α) (τ : Equiv.Perm β) {a a' : α}
    (h : σ.SameCycle a a') :
    Equiv.Perm.SameCycle (Equiv.sumCongr σ τ) (Sum.inl a) (Sum.inl a') := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact ⟨n, by rw [zpow_natCast, sumCongr_pow_inl, hn]⟩

theorem sameCycle_sumCongr_inr [Finite β] (σ : Equiv.Perm α) (τ : Equiv.Perm β) {b b' : β}
    (h : τ.SameCycle b b') :
    Equiv.Perm.SameCycle (Equiv.sumCongr σ τ) (Sum.inr b) (Sum.inr b') := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact ⟨n, by rw [zpow_natCast, sumCongr_pow_inr, hn]⟩

end Perm

/-! ## The composite -/

section Composite

variable {V W I L J R : Type*}
  [Fintype V] [DecidableEq V] [Fintype W] [DecidableEq W]
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
  [Fintype L] [DecidableEq L] [Fintype R] [DecidableEq R]
  (left : OpenTangleData V I L) (right : OpenTangleData W J R) (matching : L ≃ R)

/-- The carrier reassociation, as used by `composeData`. -/
abbrev reassoc : ((I ⊕ L) ⊕ (J ⊕ R)) ≃ MatchedSeam.Dart (I ⊕ J) L R :=
  composeDartEquiv (I := I) (L := L) (J := J) (R := R)

/-- The composite's vertex map through the reassociation. -/
theorem vertOf_reassoc (x : (I ⊕ L) ⊕ (J ⊕ R)) :
    (compositeRS left right matching).vertOf (reassoc x) = disjointVertOf left right x :=
  composeData_vertOf_composeDartEquiv left right matching x

/-- Composite darts over a left vertex correspond to the left darts over it. -/
theorem mem_dartsAt_inl_iff (v : V) (x : MatchedSeam.Dart (I ⊕ J) L R) :
    x ∈ (compositeRS left right matching).dartsAt (Sum.inl v) ↔
      ∃ d : I ⊕ L, left.vertOf d = v ∧ reassoc (Sum.inl d) = x := by
  constructor
  · intro hx
    have hx1 : (compositeRS left right matching).vertOf x = Sum.inl v :=
      (Finset.mem_filter.1 hx).2
    have hx' : (compositeRS left right matching).vertOf (reassoc (reassoc.symm x)) = Sum.inl v := by
      rw [Equiv.apply_symm_apply]; exact hx1
    rw [vertOf_reassoc] at hx'
    rcases hy : reassoc.symm x with d | d
    · rw [hy] at hx'
      refine ⟨d, by simpa [disjointVertOf] using hx', ((Equiv.symm_apply_eq _).1 hy).symm⟩
    · rw [hy] at hx'
      simp [disjointVertOf] at hx'
  · rintro ⟨d, hd, rfl⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [vertOf_reassoc]
    simpa [disjointVertOf] using hd

theorem mem_dartsAt_inr_iff (w : W) (x : MatchedSeam.Dart (I ⊕ J) L R) :
    x ∈ (compositeRS left right matching).dartsAt (Sum.inr w) ↔
      ∃ d : J ⊕ R, right.vertOf d = w ∧ reassoc (Sum.inr d) = x := by
  constructor
  · intro hx
    have hx1 : (compositeRS left right matching).vertOf x = Sum.inr w :=
      (Finset.mem_filter.1 hx).2
    have hx' : (compositeRS left right matching).vertOf (reassoc (reassoc.symm x)) = Sum.inr w := by
      rw [Equiv.apply_symm_apply]; exact hx1
    rw [vertOf_reassoc] at hx'
    rcases hy : reassoc.symm x with d | d
    · rw [hy] at hx'
      simp [disjointVertOf] at hx'
    · rw [hy] at hx'
      refine ⟨d, by simpa [disjointVertOf] using hx', ((Equiv.symm_apply_eq _).1 hy).symm⟩
  · rintro ⟨d, hd, rfl⟩
    refine Finset.mem_filter.2 ⟨Finset.mem_univ _, ?_⟩
    rw [vertOf_reassoc]
    simpa [disjointVertOf] using hd

/-- **Composite darts over a left vertex are counted by the left darts.** -/
theorem card_dartsAt_inl (v : V) :
    ((compositeRS left right matching).dartsAt (Sum.inl v)).card = (openDartsAt left v).card := by
  refine (Finset.card_bij (fun d _ => reassoc (Sum.inl d)) ?_ ?_ ?_).symm
  · intro d hd
    exact (mem_dartsAt_inl_iff left right matching v _).2
      ⟨d, (Finset.mem_filter.1 hd).2, rfl⟩
  · intro d _ d' _ h
    simpa using h
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := (mem_dartsAt_inl_iff left right matching v x).1 hx
    exact ⟨d, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩, rfl⟩

theorem card_dartsAt_inr (w : W) :
    ((compositeRS left right matching).dartsAt (Sum.inr w)).card = (openDartsAt right w).card := by
  refine (Finset.card_bij (fun d _ => reassoc (Sum.inr d)) ?_ ?_ ?_).symm
  · intro d hd
    exact (mem_dartsAt_inr_iff left right matching w _).2
      ⟨d, (Finset.mem_filter.1 hd).2, rfl⟩
  · intro d _ d' _ h
    simpa using h
  · intro x hx
    obtain ⟨d, hd, rfl⟩ := (mem_dartsAt_inr_iff left right matching w x).1 hx
    exact ⟨d, Finset.mem_filter.2 ⟨Finset.mem_univ _, hd⟩, rfl⟩

/-- **The composite is cubic** when both sides are, counting cut half-edges. -/
theorem isCubic_composeRotationSystem (hL : OpenIsCubic left) (hR : OpenIsCubic right) :
    (left.composeRotationSystem right matching).IsCubic := by
  rw [← compositeRS_eq]
  intro v
  rcases v with v | w
  · rw [card_dartsAt_inl]; exact hL v
  · rw [card_dartsAt_inr]; exact hR w

/-- Powers of a permutation conjugated across an equivalence of carriers. -/
theorem conjEquiv_pow {α β : Type*} (e : α ≃ β) (σ : Equiv.Perm α) (n : ℕ) (b : β) :
    (((e.symm.trans σ).trans e : Equiv.Perm β) ^ n) b = e ((σ ^ n) (e.symm b)) := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, pow_succ, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, ih]
      simp [Equiv.trans_apply]

/-- Same cycle transports across a conjugating equivalence of carriers. -/
theorem sameCycle_conjEquiv {α β : Type*} [Finite α] (e : α ≃ β) (σ : Equiv.Perm α)
    {x y : α} (h : σ.SameCycle x y) :
    Equiv.Perm.SameCycle ((e.symm.trans σ).trans e) (e x) (e y) := by
  obtain ⟨n, hn⟩ := h.exists_nat_pow_eq
  exact ⟨n, by rw [zpow_natCast, conjEquiv_pow, Equiv.symm_apply_apply, hn]⟩

/-- **The composite is rotation-cyclic** when both sides are. -/
theorem vertexRotationCyclic_composeRotationSystem
    (hL : OpenRotationCyclic left) (hR : OpenRotationCyclic right) :
    VertexRotationCyclic (left.composeRotationSystem right matching) := by
  rw [← compositeRS_eq]
  intro d d' hv
  obtain ⟨x, rfl⟩ := reassoc.surjective d
  obtain ⟨x', rfl⟩ := reassoc.surjective d'
  rw [vertOf_reassoc, vertOf_reassoc] at hv
  change Equiv.Perm.SameCycle
    ((reassoc.symm.trans (Equiv.sumCongr left.rho right.rho)).trans reassoc)
    (reassoc x) (reassoc x')
  rcases x with a | b <;> rcases x' with a' | b'
  · exact sameCycle_conjEquiv _ _
      (sameCycle_sumCongr_inl _ _ (hL a a' (by simpa [disjointVertOf] using hv)))
  · simp [disjointVertOf] at hv
  · simp [disjointVertOf] at hv
  · exact sameCycle_conjEquiv _ _
      (sameCycle_sumCongr_inr _ _ (hR b b' (by simpa [disjointVertOf] using hv)))

end Composite

end GoertzelV24CompositeSeamCubic

end Mettapedia.GraphTheory.FourColor
