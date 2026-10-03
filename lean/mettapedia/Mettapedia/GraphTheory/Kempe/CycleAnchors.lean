import Mettapedia.GraphTheory.Kempe.ForestGuard
import Mathlib.Data.Fintype.Card

/-!
# Retaining colours on a cycle-breaking set

If deleting a retained set from the hidden region leaves a forest, equal
retained colours determine one fixed-exterior Kempe class. Consequently any
family of pairwise unreachable extensions injects into the colour assignments
on that set. For one retained vertex and four colours there are at most four
classes, independently of the size of the hidden region.

The guarded interface also preserves and reconstructs entire histories. It
does not declare every retained colour or transition feasible, bound the
size of a cycle-breaking set, or produce an ordinary smaller planar map.
-/

namespace SimpleGraph.KempeCycleAnchors

open Relation

universe u w

variable {V : Type u} {α : Type w} {G : SimpleGraph V}
variable [Fintype V] [DecidableEq α]

/-- Retaining the colours on a cycle-breaking set removes hidden class loss.
The resulting history fixes both that set and the entire original exterior. -/
theorem same_anchor_path (S K : Set V) (forest : (G.induce (S \ K)).IsAcyclic)
    (C D : G.Coloring α) (outside : ∀ x, x ∉ S → C x = D x)
    (anchors : ∀ x, x ∈ K → C x = D x) :
    ReflTransGen (G.KempeStepAvoiding (S \ K)ᶜ) C D := by
  apply KempeForestFibre.fibre_path (S \ K) forest C D
  intro x hx
  by_cases hs : x ∈ S
  · exact anchors x (by by_contra hk; exact hx ⟨hs, hk⟩)
  · exact outside x hs

/-- Distinct physical classes with a fixed exterior must differ on the retained
cycle-breaking set. This counts class representatives, not all extensions. -/
theorem representatives_card_le [Fintype α] (S K : Set V)
    (forest : (G.induce (S \ K)).IsAcyclic) (C₀ : G.Coloring α)
    (F : Finset (G.Coloring α))
    (outside : ∀ C ∈ F, ∀ x, x ∉ S → C x = C₀ x)
    (separate : ∀ C ∈ F, ∀ D ∈ F, C ≠ D →
      ¬ ReflTransGen (G.KempeStepAvoiding Sᶜ) C D) :
    F.card ≤ Fintype.card α ^ Nat.card K := by
  classical
  let observe : G.Coloring α → (K → α) := fun C x => C x
  have inject : (F : Set (G.Coloring α)).InjOn observe := by
    intro C hC D hD equal
    by_contra different
    apply separate C hC D hD different
    have path := same_anchor_path S K forest C D
      (fun x hx => (outside C hC x hx).trans (outside D hD x hx).symm)
      (fun x hx => congrFun equal ⟨x, hx⟩)
    have boundaryIncluded : Sᶜ ⊆ (S \ K)ᶜ := fun _ hx hs => hx hs.1
    exact ReflTransGen.mono (fun _ _ step => step.mono boundaryIncluded) _ _ path
  have bound := Finset.card_le_card_of_injOn observe
    (t := Finset.univ) (fun _ _ => Finset.mem_univ _) inject
  simpa [Nat.card_eq_fintype_card] using bound

/-- A single retained vertex suffices to distinguish at most four classes if
its deletion makes the hidden region acyclic. No bound on cycle length is used. -/
theorem one_anchor_card_le_four (S : Set V) (v : V)
    (forest : (G.induce (S \ {v})).IsAcyclic) (C₀ : G.Coloring (Fin 4))
    (F : Finset (G.Coloring (Fin 4)))
    (outside : ∀ C ∈ F, ∀ x, x ∉ S → C x = C₀ x)
    (separate : ∀ C ∈ F, ∀ D ∈ F, C ≠ D →
      ¬ ReflTransGen (G.KempeStepAvoiding Sᶜ) C D) : F.card ≤ 4 := by
  classical
  simpa using representatives_card_le S {v} forest C₀ F outside separate

/-- Exact history transport while the original exterior is fixed. Anchor
colours may change, but every change must satisfy the joint forest guard. -/
theorem history_iff (S K : Set V) (forest : (G.induce (S \ K)).IsAcyclic)
    (C D : G.Coloring α) :
    ReflTransGen (KempeGuardedLift.Step (S \ K) Sᶜ)
      (C.restrictInduce (S \ K)ᶜ) (D.restrictInduce (S \ K)ᶜ) ↔
      ReflTransGen (G.KempeStepAvoiding Sᶜ) C D :=
  KempeForestFibre.history_iff (S \ K) forest Sᶜ (fun _ hx hs => hx hs.1) C D

end SimpleGraph.KempeCycleAnchors
