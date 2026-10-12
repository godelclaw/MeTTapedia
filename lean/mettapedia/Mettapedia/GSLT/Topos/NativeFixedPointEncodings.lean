import Mettapedia.GSLT.Topos.PresheafPredicateHeyting
import Mathlib.Order.FixedPoints

/-!
# Corrected monotone fixed-point encodings for native predicates

The independent semantics is Knaster--Tarski's least/greatest fixed point.
The derived encodings quantify over all predicates in a complete fibre:
least means every pre-fixed predicate, greatest means some post-fixed
predicate. Subtyping guards here are closed propositions, not a test at one
world. This is the global predicate-fibre reading; it does not assert an
unproved comparison with quantification over local generalized predicates.

The literal displayed encodings in Williams--Stay, Native Type Theory,
§4 (arXiv:2102.04672v3), are recorded separately. In particular the
existential implication printed for mu is not the corrected existential
conjunction for nu. Controls refute both displayed fixed-point readings.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Topos.NativeFixedPointEncodings

open _root_.CategoryTheory

universe u v w z

section Lattice

variable {L : Type z} [CompleteLattice L]

/-- Universal implication: every predicate containing its image is included.
The proof-indexed infimum is implication by a closed subtyping proposition. -/
noncomputable def leastEncoding (f : L →o L) : L :=
  ⨅ candidate, ⨅ (_ : f candidate ≤ candidate), candidate

/-- Existential conjunction: choose a predicate included in its image.
The proof-indexed supremum retains the closed subtyping condition. -/
noncomputable def greatestEncoding (f : L →o L) : L :=
  ⨆ candidate, ⨆ (_ : candidate ≤ f candidate), candidate

/-- Independently defined fixed-point semantics. -/
noncomputable def leastMeaning (f : L →o L) : L := f.lfp

/-- Independently defined coinductive fixed-point semantics. -/
noncomputable def greatestMeaning (f : L →o L) : L := f.gfp

/-- The derived universal encoding computes the independently specified
least fixed point, for every monotone operator on a complete fibre. -/
theorem leastEncoding_eq_meaning (f : L →o L) :
    leastEncoding f = leastMeaning f := by
  apply le_antisymm
  · exact iInf_le_of_le f.lfp (iInf_le_of_le f.map_lfp.le le_rfl)
  · exact le_iInf fun candidate => le_iInf fun closed => f.lfp_le closed

/-- The corrected existential encoding computes the greatest fixed point. -/
theorem greatestEncoding_eq_meaning (f : L →o L) :
    greatestEncoding f = greatestMeaning f := by
  apply le_antisymm
  · exact iSup_le fun candidate => iSup_le fun closed => f.le_gfp closed
  · exact le_iSup_of_le f.gfp (le_iSup_of_le f.map_gfp.ge le_rfl)

theorem least_unfold (f : L →o L) : f (leastEncoding f) = leastEncoding f := by
  rw [leastEncoding_eq_meaning]
  exact f.map_lfp

theorem greatest_unfold (f : L →o L) :
    f (greatestEncoding f) = greatestEncoding f := by
  rw [greatestEncoding_eq_meaning]
  exact f.map_gfp

theorem least_induction (f : L →o L) (candidate : L)
    (closed : f candidate ≤ candidate) : leastEncoding f ≤ candidate := by
  rw [leastEncoding_eq_meaning]
  exact f.lfp_le closed

theorem greatest_coinduction (f : L →o L) (candidate : L)
    (closed : candidate ≤ f candidate) : candidate ≤ greatestEncoding f := by
  rw [greatestEncoding_eq_meaning]
  exact f.le_gfp closed

theorem least_mono {f g : L →o L} (below : f ≤ g) :
    leastEncoding f ≤ leastEncoding g := by
  rw [leastEncoding_eq_meaning, leastEncoding_eq_meaning]
  exact OrderHom.lfp.monotone below

theorem greatest_mono {f g : L →o L} (below : f ≤ g) :
    greatestEncoding f ≤ greatestEncoding g := by
  rw [greatestEncoding_eq_meaning, greatestEncoding_eq_meaning]
  exact OrderHom.gfp.monotone below

theorem finite_least_approximation (f : L →o L) (depth : Nat) :
    f^[depth] ⊥ ≤ leastEncoding f := by
  rw [leastEncoding_eq_meaning]
  induction depth with
  | zero => exact bot_le
  | succ depth prior =>
      rw [Function.iterate_succ_apply']
      exact (f.monotone prior).trans f.map_lfp.le

theorem finite_greatest_approximation (f : L →o L) (depth : Nat) :
    greatestEncoding f ≤ f^[depth] ⊤ := by
  rw [greatestEncoding_eq_meaning]
  induction depth with
  | zero => exact le_top
  | succ depth prior =>
      rw [Function.iterate_succ_apply']
      exact f.map_gfp.ge.trans (f.monotone prior)

/-- The literal existential-implication expression printed for mu. -/
noncomputable def printedMu (f : L →o L) : L :=
  ⨆ candidate, ⨅ (_ : candidate ≤ f candidate), candidate

/-- The literal universal-implication expression printed for nu. -/
noncomputable def printedNu (f : L →o L) : L :=
  ⨅ candidate, ⨅ (_ : f candidate ≤ candidate), candidate

/-- The printed nu computes the least, rather than greatest, fixed point. -/
theorem printedNu_eq_least (f : L →o L) : printedNu f = leastMeaning f :=
  leastEncoding_eq_meaning f

/-- Existential implication is always top in this closed-fibre reading:
choose the top predicate, regardless of whether its guard is inhabited. -/
theorem printedMu_eq_top (f : L →o L) : printedMu f = ⊤ := by
  apply le_antisymm le_top
  exact le_iSup_of_le ⊤ (le_iInf fun _ => le_rfl)

end Lattice

section Transport

variable {L : Type z} {K : Type w} [CompleteLattice L] [CompleteLattice K]

/-- A monotone substitution with a right adjoint preserves the least fixed
point whenever it intertwines the two actual operators. -/
theorem least_substitution (f : L →o L) (g : K →o K)
    (reindex : L →o K) (right : K → L)
    (adj : GaloisConnection reindex right)
    (natural : ∀ candidate, reindex (f candidate) = g (reindex candidate)) :
    reindex (leastEncoding f) = leastEncoding g := by
  rw [leastEncoding_eq_meaning, leastEncoding_eq_meaning]
  change reindex f.lfp = g.lfp
  apply le_antisymm
  · have closed : f (right g.lfp) ≤ right g.lfp := by
      apply (adj _ _).mp
      rw [natural]
      exact (g.monotone (adj.l_u_le g.lfp)).trans g.map_lfp.le
    exact (adj _ _).mpr (f.lfp_le closed)
  · apply g.lfp_le
    rw [← natural, f.map_lfp]

/-- Dually, a substitution with a left adjoint preserves greatest fixed
points for intertwined operators. -/
theorem greatest_substitution (f : L →o L) (g : K →o K)
    (reindex : L →o K) (left : K → L)
    (adj : GaloisConnection left reindex)
    (natural : ∀ candidate, reindex (f candidate) = g (reindex candidate)) :
    reindex (greatestEncoding f) = greatestEncoding g := by
  rw [greatestEncoding_eq_meaning, greatestEncoding_eq_meaning]
  change reindex f.gfp = g.gfp
  apply le_antisymm
  · apply g.le_gfp
    rw [← natural, f.map_gfp]
  · have closed : left g.gfp ≤ f (left g.gfp) := by
      apply (adj _ _).mpr
      rw [natural]
      exact g.map_gfp.ge.trans (g.monotone (adj.le_u_l g.gfp))
    exact (adj _ _).mp (f.le_gfp closed)

end Transport

section Presheaf

variable {C : Type u} [Category.{v} C] {P Q : C ⥤ Type w}

/-- Actual presheaf substitution, retaining all generalized elements. -/
def reindex (σ : P ⟶ Q) : Subfunctor Q →o Subfunctor P where
  toFun φ := φ.preimage σ
  monotone' _ _ below world _ held := below world held

theorem least_preimage (σ : P ⟶ Q)
    (f : Subfunctor Q →o Subfunctor Q) (g : Subfunctor P →o Subfunctor P)
    (natural : ∀ φ, (f φ).preimage σ = g (φ.preimage σ)) :
    (leastEncoding f).preimage σ = leastEncoding g :=
  least_substitution f g (reindex σ) (forallAlong σ)
    (galois_preimage_forallAlong σ) natural

theorem greatest_preimage (σ : P ⟶ Q)
    (f : Subfunctor Q →o Subfunctor Q) (g : Subfunctor P →o Subfunctor P)
    (natural : ∀ φ, (f φ).preimage σ = g (φ.preimage σ)) :
    (greatestEncoding f).preimage σ = greatestEncoding g :=
  greatest_substitution f g (reindex σ) (fun φ => φ.image σ)
    (fun φ ψ => Subfunctor.image_le_iff φ σ ψ) natural

end Presheaf

end Mettapedia.GSLT.Topos.NativeFixedPointEncodings
