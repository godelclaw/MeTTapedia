import Mettapedia.GraphTheory.FourColor.StarAttachmentComponents

/-!
# Count consumed components from the finite boundary record

Two selected ports represent one component exactly when their columns
in the zero-cut records agree. Counting distinct columns is executable
and agrees with the semantic port quotient. The selector may repeat
ports; neither hidden components nor unused ports affect this count.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundaryComponentCount

open BoundarySmallCutViability BoundarySmallCutProfile BoundarySmallCutExecutable
open GoertzelV24BoundaryEssentialGluing

variable {P Q : Type*} [Fintype P] [Fintype Q]

def column (a : Finset (State P)) (p : P) : Finset (State P) :=
  a.filter fun s => s.cost.val = 0 ∧ s.boundary p = true

def columns (a : Finset (State P)) (selected : Q → P) : Finset (Finset (State P)) :=
  Finset.univ.image (fun q => column a (selected q))

def count (a : Finset (State P)) (selected : Q → P) : Nat := (columns a selected).card

omit [Fintype P] [Fintype Q] in
theorem column_eq_iff (a : Finset (State P)) (p q : P) :
    column a p = column a q ↔ SameComponent (a : Set (State P)) p q := by
  constructor
  · intro h s hs hz
    have he := congrArg (fun b : Finset (State P) => s ∈ b) h
    have hm := Iff.of_eq he
    simp only [column, Finset.mem_filter] at hm
    have ht : s.boundary p = true ↔ s.boundary q = true := by
      exact ⟨fun hp => (hm.mp ⟨hs, hz, hp⟩).2.2,
        fun hq => (hm.mpr ⟨hs, hz, hq⟩).2.2⟩
    cases hp : s.boundary p <;> cases hq : s.boundary q <;> simp_all
  · intro h
    ext s
    simp only [column, Finset.mem_filter]
    constructor
    · rintro ⟨hs, hz, hp⟩
      exact ⟨hs, hz, (h s hs hz).symm.trans hp⟩
    · rintro ⟨hs, hz, hq⟩
      exact ⟨hs, hz, (h s hs hz).trans hq⟩

variable {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  (G : Multigraph V E) (ports : P → V) (selected : Q → P)

noncomputable section
attribute [local instance] Classical.propDecidable

omit [Fintype Q] in
theorem columns_equal (p q : Q) :
    column (extract G ports) (selected p) = column (extract G ports) (selected q) ↔
      SameComponent (profile G (ports ∘ selected)) p q := by
  rw [column_eq_iff, extract_correct, sameComponent_profile, sameComponent_profile]
  rfl

def extractEquiv : Quotient (portSetoid (profile G (ports ∘ selected))) ≃
    {c // c ∈ columns (extract G ports) selected} := by
  let f : Quotient (portSetoid (profile G (ports ∘ selected))) →
      {c // c ∈ columns (extract G ports) selected} :=
    Quotient.lift (fun q => ⟨column (extract G ports) (selected q),
      Finset.mem_image.mpr ⟨q, Finset.mem_univ q, rfl⟩⟩)
      (fun p q h => Subtype.ext ((columns_equal G ports selected p q).mpr h))
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro a b he
    obtain ⟨p, rfl⟩ := Quotient.exists_rep a
    obtain ⟨q, rfl⟩ := Quotient.exists_rep b
    exact Quotient.sound ((columns_equal G ports selected p q).mp (congrArg Subtype.val he))
  · rintro ⟨c, hc⟩
    obtain ⟨q, _, hq⟩ := Finset.mem_image.mp hc
    exact ⟨Quotient.mk (portSetoid (profile G (ports ∘ selected))) q, Subtype.ext hq⟩

theorem count_extract : count (extract G ports) selected =
    Nat.card (Quotient (portSetoid (profile G (ports ∘ selected)))) := by
  rw [Nat.card_congr (extractEquiv G ports selected)]
  simp [count, Nat.card_eq_fintype_card]

open GoertzelV24OpenTangleComposition GoertzelV24CompositeSeamMultigraph
open SerialTangleSmallCutTransfer

variable {L R : Type*} [Fintype L] [Fintype R] [DecidableEq E]

theorem count_extractTangle (T : TwoSidedOpenTangleData V E L R) (sel : Q → L ⊕ R) :
    count (extractTangle T) sel =
      Nat.card (Quotient (portSetoid
        (profile (sideMultigraph (asOpen T)) ((asOpen T).boundaryVert ∘ sel)))) := by
  have he : extractTangle T = extract (sideMultigraph (asOpen T)) (asOpen T).boundaryVert := by
    apply Finset.coe_injective
    rw [extractTangle_correct, extract_correct]
  rw [he, count_extract]

end
end Mettapedia.GraphTheory.FourColor.BoundaryComponentCount
