import Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitution

/-!
# MM0 substitution at two designated bound positions

When every bound formal occurs at one of two supplied positions, native
admissibility reduces to argument typing and the two selected independence
rows. The positions and images are retained explicitly. Distinct source bound
positions require distinct target names; interpreted values need not differ.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.Substitution

variable {signature : TermSignature} {target : Context}

theorem admissible_iff_of_two_bound_positions (formal : Context) (expressions : List Preterm)
    (firstPosition firstSort firstImage secondPosition secondSort secondImage : Nat)
    (firstFormal : formal[firstPosition]? = some (.bound firstSort))
    (secondFormal : formal[secondPosition]? = some (.bound secondSort))
    (firstValue : expressions[firstPosition]? = some (.var firstImage))
    (secondValue : expressions[secondPosition]? = some (.var secondImage))
    (onlyThese : ∀ position sort, formal[position]? = some (.bound sort) →
      position = firstPosition ∨ position = secondPosition) :
    Admissible signature formal target expressions ↔
      List.Forall₂ (Preterm.FitsBinder signature target) expressions formal ∧
      (∀ other ∈ entries formal expressions,
        ¬ other.1.1.DependsOn other.2 firstPosition →
          ¬ Preterm.HasVar target firstImage other.1.2) ∧
      (∀ other ∈ entries formal expressions,
        ¬ other.1.1.DependsOn other.2 secondPosition →
          ¬ Preterm.HasVar target secondImage other.1.2) := by
  have firstSelected : ((.bound firstSort, .var firstImage), firstPosition) ∈ entries formal expressions := by
    simp [entries, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, firstFormal, firstValue]
  have secondSelected : ((.bound secondSort, .var secondImage), secondPosition) ∈ entries formal expressions := by
    simp [entries, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, secondFormal, secondValue]
  constructor
  · intro admitted
    exact ⟨admitted.typed, admitted.independent _ firstSelected firstSort firstImage rfl,
      admitted.independent _ secondSelected secondSort secondImage rfl⟩
  · rintro ⟨typed, firstIndependent, secondIndependent⟩
    refine ⟨typed, ?_⟩
    rintro ⟨⟨binder, expression⟩, position⟩ member sort image same other otherMember absent
    have lookups : formal[position]? = some binder ∧ expressions[position]? = some expression := by
      simpa only [entries, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some] using member
    have binderSame : binder = .bound sort := congrArg Prod.fst same
    have expressionSame : expression = .var image := congrArg Prod.snd same
    rw [binderSame] at lookups
    rcases onlyThese position sort lookups.1 with first | second
    · subst position
      have imageSame : image = firstImage := by
        rw [expressionSame] at lookups
        exact Preterm.var.inj (Option.some.inj (lookups.2.symm.trans firstValue))
      subst image
      exact firstIndependent other otherMember absent
    · subst position
      have imageSame : image = secondImage := by
        rw [expressionSame] at lookups
        exact Preterm.var.inj (Option.some.inj (lookups.2.symm.trans secondValue))
      subst image
      exact secondIndependent other otherMember absent

theorem Admissible.bound_images_distinct {formal : Context} {expressions : List Preterm}
    (admitted : Admissible signature formal target expressions)
    {firstPosition secondPosition firstSort secondSort firstImage secondImage : Nat}
    (firstFormal : formal[firstPosition]? = some (.bound firstSort))
    (secondFormal : formal[secondPosition]? = some (.bound secondSort))
    (different : firstPosition ≠ secondPosition)
    (firstValue : expressions[firstPosition]? = some (.var firstImage))
    (secondValue : expressions[secondPosition]? = some (.var secondImage))
    (secondBound : target[secondImage]? = some (.bound secondSort)) :
    firstImage ≠ secondImage := by
  have absent := admitted.preserves_independence firstFormal secondFormal
    (by simp [Preterm.hasVar_var_iff, secondFormal, different]) firstValue secondValue
  intro same
  subst firstImage
  exact absent (.bound secondBound)

#print axioms admissible_iff_of_two_bound_positions
#print axioms Admissible.bound_images_distinct

end Mettapedia.Languages.MM0.Kernel.Substitution
