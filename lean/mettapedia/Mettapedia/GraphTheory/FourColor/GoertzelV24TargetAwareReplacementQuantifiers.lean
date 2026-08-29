import Mettapedia.GraphTheory.FourColor.GoertzelV24TargetAwareSupportReplacement

/-!
# Quantifier boundary for target-aware support replacement

For one fixed exterior, zero Count only asks that the replacement support be
disjoint from that exterior.  This is genuinely weaker than support inclusion.
It does not, however, remain weaker if the exterior ranges over all abstract
support sets: the complement of the original support is then a maximal
adversary, and avoiding it is exactly support inclusion.

Thus a successful target-aware reduction must use a theorem about the supports
realized by physical planar exteriors.  Merely moving the existential choice of
replacement after an unrestricted exterior quantifier gains nothing.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24TargetAwareReplacementQuantifiers

universe u v

variable {Word : Type u} {Candidate : Type v}

/-- The complement of the original support is disjoint from the original. -/
theorem disjoint_compl_self (original : Set Word) :
    Disjoint originalᶜ original := by
  rw [Set.disjoint_left]
  intro word houtside horiginal
  exact houtside horiginal

/-- Avoiding the complement of the original is exactly being contained in
the original. -/
theorem disjoint_compl_iff_subset
    (original replacement : Set Word) :
    Disjoint originalᶜ replacement ↔ replacement ⊆ original := by
  rw [Set.disjoint_left]
  constructor
  · intro h word hreplacement
    by_contra horiginal
    exact h horiginal hreplacement
  · intro h word hcomplement hreplacement
    exact hcomplement (h hreplacement)

/-- **Unrestricted target-aware quantifier collapse.**  A family contains a
replacement which works against every abstract zero exterior, with the
replacement allowed to depend on the exterior, exactly when the family
already contains one context-independent support-subset replacement. -/
theorem unrestricted_targetAware_iff_exists_subset
    (original : Set Word) (replacement : Candidate → Set Word) :
    (∀ exterior : Set Word, Disjoint exterior original →
      ∃ candidate, Disjoint exterior (replacement candidate)) ↔
    ∃ candidate, replacement candidate ⊆ original := by
  constructor
  · intro h
    obtain ⟨candidate, hc⟩ :=
      h originalᶜ (disjoint_compl_self original)
    exact ⟨candidate,
      (disjoint_compl_iff_subset original (replacement candidate)).1 hc⟩
  · rintro ⟨candidate, hsubset⟩ exterior hexterior
    refine ⟨candidate, ?_⟩
    rw [Set.disjoint_left] at hexterior ⊢
    intro word hext hreplacement
    exact hexterior hext (hsubset hreplacement)

/-- The same collapse holds for a restricted class of physical exterior
supports whenever that class contains the maximal complement adversary. -/
theorem physical_targetAware_iff_exists_subset_of_compl_mem
    (original : Set Word) (replacement : Candidate → Set Word)
    (physicalExterior : Set (Set Word))
    (hcomplement : originalᶜ ∈ physicalExterior) :
    (∀ exterior ∈ physicalExterior, Disjoint exterior original →
      ∃ candidate, Disjoint exterior (replacement candidate)) ↔
    ∃ candidate, replacement candidate ⊆ original := by
  constructor
  · intro h
    obtain ⟨candidate, hc⟩ :=
      h originalᶜ hcomplement (disjoint_compl_self original)
    exact ⟨candidate,
      (disjoint_compl_iff_subset original (replacement candidate)).1 hc⟩
  · rintro ⟨candidate, hsubset⟩ exterior - hexterior
    refine ⟨candidate, ?_⟩
    rw [Set.disjoint_left] at hexterior ⊢
    intro word hext hreplacement
    exact hexterior hext (hsubset hreplacement)

/-- If no candidate support is contained in the original, its complement is
an explicit abstract exterior which has zero Count with the original but
meets every candidate support. -/
theorem complement_adversary_of_no_subset
    (original : Set Word) (replacement : Candidate → Set Word)
    (hnoSubset : ∀ candidate, ¬ replacement candidate ⊆ original) :
    Disjoint originalᶜ original ∧
      ∀ candidate, ¬ Disjoint originalᶜ (replacement candidate) := by
  refine ⟨disjoint_compl_self original, ?_⟩
  intro candidate hdisjoint
  exact hnoSubset candidate
    ((disjoint_compl_iff_subset original (replacement candidate)).1 hdisjoint)

end GoertzelV24TargetAwareReplacementQuantifiers

end Mettapedia.GraphTheory.FourColor
