import Mettapedia.GraphTheory.FourColor.VertexCodeViability
import Mettapedia.GraphTheory.FourColor.VertexCodeChecks
import Mettapedia.GraphTheory.FourColor.VertexAttachmentTransfer

/-!
# A finite carrier for viable planar prefixes

The unrestricted exact-mass carrier is infinite already at frontier width
three, so a finite state space must come from an admissibility test rather
than from the width alone. The test used here reads only the evaluator's
own coordinates: no component is hidden from the boundary, and the exact
integer Euler mass is four times the number of components visible there.

Both halves are load-bearing and neither implies the other. Without the
visibility half a completed handle can hide behind the frontier and still
satisfy the mass equation; without the mass equation the carrier is not
bounded at all. Under the conjunction the mass is pinned to the finite
range `[0, 4w]`, which is what makes a closure computation possible.

The test is then identified with its intended meaning on decoded runs:
it holds exactly when the constructed tangle has every component exposed
at the boundary and zero Euler defect. Terminal acceptance is a separate
predicate and is deliberately not this one — every closed run fails the
extension test.
-/

namespace Mettapedia.GraphTheory.FourColor.VertexCodeViablePrefix

open ExecutableJointTransfer BoundarySmallCutViability BoundarySmallCutExecutable
open BoundarySmallCutProfile VertexCodeTrace ExecutableVertexCode
open GoertzelV24OpenTangleComposition TwoSidedOpenTangleData
open GoertzelV24CompositeSeamMultigraph SerialTangleSmallCutTransfer
open BoundaryConnectivity OpenTangleReplacementEuler StarAttachmentComponents

variable {r : ℕ}

/-- Components visible at the boundary, read from the zero-cut records by
counting distinct columns. Hidden components contribute no column. -/
def visibleComponents (s : State (Fin 0) (Fin r)) : ℕ :=
  BoundaryComponentCount.count s.cuts (id : Fin 0 ⊕ Fin r → Fin 0 ⊕ Fin r)

theorem visibleComponents_le (s : State (Fin 0) (Fin r)) : visibleComponents s ≤ r := by
  have h : (BoundaryComponentCount.columns s.cuts (id : Fin 0 ⊕ Fin r → Fin 0 ⊕ Fin r)).card ≤
      (Finset.univ : Finset (Fin 0 ⊕ Fin r)).card := Finset.card_image_le
  simpa [visibleComponents, BoundaryComponentCount.count] using h

/-- The executable prefix test. This is an *extension* predicate: it says the
piece can still acquire a connected exterior and currently carries no handle. -/
def Viable (s : State (Fin 0) (Fin r)) : Bool :=
  !rejectsExtension s.cuts && decide (s.mass = 4 * (visibleComponents s : ℤ))

theorem viable_iff (s : State (Fin 0) (Fin r)) :
    Viable s = true ↔
      rejectsExtension s.cuts = false ∧ s.mass = 4 * (visibleComponents s : ℤ) := by
  simp [Viable]

/-- The mass bound is *derived* from the test, not assumed of the carrier. -/
theorem mass_range {s : State (Fin 0) (Fin r)} (h : Viable s = true) :
    0 ≤ s.mass ∧ s.mass ≤ 4 * r := by
  obtain ⟨-, hm⟩ := (viable_iff s).mp h
  have hc := visibleComponents_le s
  omega

section Finiteness

/-- The four coordinates determine the state. -/
def coords (s : State (Fin 0) (Fin r)) :
    Finset ((Fin 0 → Color) × (Fin r → Color)) × Equiv.Perm (Fin 0 ⊕ Fin r) ×
      Finset (BoundarySmallCutProfile.State (Fin 0 ⊕ Fin r)) × ℤ :=
  (s.colours, s.face, s.cuts, s.mass)

theorem coords_injective : Function.Injective (coords (r := r)) := by
  rintro ⟨a, b, c, d⟩ ⟨a', b', c', d'⟩ h
  simp only [coords, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  subst h1; subst h2; subst h3; subst h4; rfl

/-- The whole point: the admissible states at a fixed width form a finite set.
The unrestricted carrier does not, so this is exactly what the test buys. -/
theorem viable_finite (r : ℕ) : {s : State (Fin 0) (Fin r) | Viable s = true}.Finite := by
  classical
  have hbox : ((Set.univ : Set (Finset ((Fin 0 → Color) × (Fin r → Color)))) ×ˢ
      ((Set.univ : Set (Equiv.Perm (Fin 0 ⊕ Fin r))) ×ˢ
        ((Set.univ : Set (Finset (BoundarySmallCutProfile.State (Fin 0 ⊕ Fin r)))) ×ˢ
          Set.Icc (0 : ℤ) (4 * r)))).Finite :=
    Set.finite_univ.prod (Set.finite_univ.prod (Set.finite_univ.prod (Set.finite_Icc _ _)))
  refine Set.Finite.subset (hbox.preimage coords_injective.injOn) ?_
  intro s hs
  obtain ⟨h0, h1⟩ := mass_range hs
  exact ⟨trivial, trivial, trivial, h0, h1⟩

noncomputable instance viableFintype (r : ℕ) :
    Fintype {s : State (Fin 0) (Fin r) // Viable s = true} :=
  (viable_finite r).fintype

/-- A measured bound. It is astronomically large, which is the operative
fact: a closure certificate must replay the *reachable* part, never `Q`. -/
theorem viable_card_le (r : ℕ) :
    Fintype.card {s : State (Fin 0) (Fin r) // Viable s = true} ≤
      2 ^ (4 ^ r) * (Nat.factorial r * (2 ^ (12 * 2 ^ r) * (4 * r + 1))) := by
  classical
  have hinj : Function.Injective
      (fun s : {s : State (Fin 0) (Fin r) // Viable s = true} =>
        (s.1.colours, s.1.face, s.1.cuts,
          (⟨s.1.mass.toNat, by have := mass_range s.2; omega⟩ : Fin (4 * r + 1)))) := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩ h
    have ha' := mass_range ha
    have hb' := mass_range hb
    simp only [Prod.mk.injEq, Fin.mk.injEq] at h
    obtain ⟨h1, h2, h3, h4⟩ := h
    refine Subtype.ext ?_
    have hm : a.mass = b.mass := by omega
    cases a; cases b
    simp_all
  have hcard := Fintype.card_le_of_injective _ hinj
  refine hcard.trans (le_of_eq ?_)
  have hc : Fintype.card ((Fin 0 → Color) × (Fin r → Color)) = 4 ^ r := by simp
  have hs : Fintype.card (Fin 0 ⊕ Fin r) = r := by simp
  simp only [Fintype.card_prod, Fintype.card_finset, hc, Fintype.card_perm, hs,
    BoundarySmallCutProfile.card_state, Fintype.card_fin]

end Finiteness

noncomputable section Bridge
attribute [local instance] Classical.propDecidable

/-- The evaluator's integer coordinate is the literal Euler mass. -/
theorem mass_exact {r} (t : Trace r) :
    (evaluate t).mass = eulerMass (asOpen t.realize) :=
  congrArg SerialTangleJointTransfer.Signature.mass (evaluate_physical t)

/-- On a run with nothing hidden, the executable column count is the actual
number of connected components of the constructed object. -/
theorem visibleComponents_exact {r} (t : Trace r)
    (hv : rejectsExtension (evaluate t).cuts = false) :
    visibleComponents (evaluate t) =
      Nat.card (Component (sideMultigraph (asOpen t.realize))) := by
  have hvis : PortVisible (sideMultigraph (asOpen t.realize))
      (asOpen t.realize).boundaryVert := by
    by_contra hc
    rw [← VertexCodeViability.visibility_exact t] at hc
    rw [hc] at hv
    exact Bool.noConfusion hv
  have hnh : ¬ HasHidden (profile (sideMultigraph (asOpen t.realize))
      (asOpen t.realize).boundaryVert) := fun h =>
    (hidden_iff_not_visible _ _).mp h hvis
  rw [visibleComponents, VertexCodeViability.cuts_exact t,
    BoundaryComponentCount.count_extractTangle]
  exact (card_components_eq_profile _ _ hnh).symm

/-- The executable test means what it is supposed to mean: the constructed
object has every component exposed at the boundary and zero Euler defect. -/
theorem viable_exact {r} (t : Trace r) :
    Viable (evaluate t) = true ↔
      PortVisible (sideMultigraph (asOpen t.realize)) (asOpen t.realize).boundaryVert ∧
        eulerMass (asOpen t.realize) =
          4 * (Nat.card (Component (sideMultigraph (asOpen t.realize))) : ℤ) := by
  rw [viable_iff]
  constructor
  · rintro ⟨hv, hm⟩
    have hvis : PortVisible (sideMultigraph (asOpen t.realize))
        (asOpen t.realize).boundaryVert := by
      by_contra hc
      rw [← VertexCodeViability.visibility_exact t] at hc
      rw [hc] at hv
      exact Bool.noConfusion hv
    refine ⟨hvis, ?_⟩
    rw [← mass_exact t, hm, visibleComponents_exact t hv]
  · rintro ⟨hvis, hm⟩
    have hv : rejectsExtension (evaluate t).cuts = false := by
      cases hc : rejectsExtension (evaluate t).cuts with
      | false => rfl
      | true => exact absurd hvis ((VertexCodeViability.visibility_exact t).mp hc)
    exact ⟨hv, by rw [mass_exact t, hm, visibleComponents_exact t hv]⟩

/-- The same statement in the repository's Euler-defect coordinate. -/
theorem viable_iff_visible_planar {r} (t : Trace r) :
    Viable (evaluate t) = true ↔
      PortVisible (sideMultigraph (asOpen t.realize)) (asOpen t.realize).boundaryVert ∧
        VertexAttachmentTransfer.defect t.realize = 0 := by
  rw [viable_exact]
  unfold VertexAttachmentTransfer.defect
  constructor
  · rintro ⟨h, hm⟩; exact ⟨h, by omega⟩
  · rintro ⟨h, hm⟩; exact ⟨h, by omega⟩

/-- Terminal acceptance is a different predicate. Every closed run fails the
extension test, so `Viable` must never be used as the accepting array. -/
theorem closed_not_viable (t : Trace 0) : Viable (evaluate t) = false := by
  simp [Viable, VertexCodeViability.closed_rejects_extension t]

end Bridge

section Controls

set_option Elab.async false
set_option maxRecDepth 16000

open VertexCodeChecks TubeSlab.VertexTransfer VertexCodePartition

/-- A bare star passes: one visible component, mass four. -/
theorem star_viable : Viable (evaluate (.first birth birth_valid)) = true := by
  decide +kernel

/-- A new vertex consuming nothing: a genuinely disconnected prefix. -/
def disjointStar : Code 3 6 :=
  ⟨![Sum.inr 3, Sum.inr 4, Sum.inr 5], ![some 0, some 1, some 2, none, none, none]⟩

theorem disjointStar_valid : Valid disjointStar := by decide +kernel

/-- Disconnected prefixes are admissible. The test bounds the number of
components; it does not demand connectivity. -/
theorem disjoint_viable :
    Viable (evaluate (.step (.first birth birth_valid) disjointStar disjointStar_valid)) =
      true := by decide +kernel

/-- A completed planar component behind the frontier: the mass equation
already fails, because the hidden component contributes no column. -/
theorem hidden_planar_mass :
    (evaluate (.step (twoStars true) birth birth_valid)).mass = 8 := by decide +kernel

theorem hidden_planar_not_viable :
    Viable (evaluate (.step (twoStars true) birth birth_valid)) = false := by decide +kernel

/-- The decisive control. A completed *handle* behind the frontier satisfies
the mass equation exactly -- its two units of defect cancel against the
component it hides. Only the visibility half rejects it. -/
theorem hidden_handle_mass :
    (evaluate (.step (twoStars false) birth birth_valid)).mass = 4 := by decide +kernel

theorem hidden_handle_components :
    visibleComponents (evaluate (.step (twoStars false) birth birth_valid)) = 1 := by
  decide +kernel

theorem hidden_handle_passes_mass_test :
    (evaluate (.step (twoStars false) birth birth_valid)).mass =
      4 * (visibleComponents (evaluate (.step (twoStars false) birth birth_valid)) : ℤ) := by
  decide +kernel

theorem hidden_handle_not_viable :
    Viable (evaluate (.step (twoStars false) birth birth_valid)) = false := by decide +kernel

end Controls

end Mettapedia.GraphTheory.FourColor.VertexCodeViablePrefix
