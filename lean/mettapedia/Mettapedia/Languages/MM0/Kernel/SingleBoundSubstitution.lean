import Mettapedia.Languages.MM0.Kernel.AdmissibleSubstitution

/-!
# Explicit independence for one-bound-parameter MM0 substitutions

The binding profiles used by the maintained HOL typing rules have regular
parameters, one bound object variable, and a body allowed to depend on it.
The preceding regular arguments must avoid that bound image in complete
occurrence support, including occurrences below binding constructors.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.Substitution

variable {signature : TermSignature} {target : Context}

theorem admissible_single_bound_iff (formal : Context) (expressions : List Preterm)
    (position sort image : Nat)
    (formalBound : formal[position]? = some (.bound sort))
    (boundImage : expressions[position]? = some (.var image))
    (uniqueBound : ∀ otherPosition otherSort,
      formal[otherPosition]? = some (.bound otherSort) → otherPosition = position) :
    Admissible signature formal target expressions ↔
      List.Forall₂ (Preterm.FitsBinder signature target) expressions formal ∧
      ∀ other ∈ entries formal expressions,
        ¬ other.1.1.DependsOn other.2 position →
          ¬ Preterm.HasVar target image other.1.2 := by
  have selected : ((.bound sort, .var image), position) ∈ entries formal expressions := by
    simp [entries, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some, formalBound, boundImage]
  constructor
  · intro admitted
    exact ⟨admitted.typed, admitted.independent _ selected sort image rfl⟩
  · rintro ⟨typed, independent⟩
    refine ⟨typed, ?_⟩
    rintro ⟨⟨binder, expression⟩, otherPosition⟩ member otherSort otherImage same other otherMember absent
    have lookups : formal[otherPosition]? = some binder ∧
        expressions[otherPosition]? = some expression := by
      simpa only [entries, List.mem_zipIdx_iff_getElem?, List.getElem?_zip_eq_some] using member
    have binderSame : binder = .bound otherSort := congrArg Prod.fst same
    have expressionSame : expression = .var otherImage := congrArg Prod.snd same
    rw [binderSame] at lookups
    have positionSame := uniqueBound otherPosition otherSort lookups.1
    subst otherPosition
    have imageSame : otherImage = image := by
      rw [expressionSame] at lookups
      exact Preterm.var.inj (Option.some.inj (lookups.2.symm.trans boundImage))
    subst otherImage
    exact independent other otherMember absent

theorem admissible_single_bound_after_three
    (first second third body : Preterm) (firstSort secondSort thirdSort objectSort image : Nat)
    (firstTyped : Preterm.HasType signature target first [] firstSort)
    (secondTyped : Preterm.HasType signature target second [] secondSort)
    (thirdTyped : Preterm.HasType signature target third [] thirdSort)
    (bound : target[image]? = some (.bound objectSort))
    (bodyTyped : Preterm.HasType signature target body [] objectSort)
    (firstIndependent : ¬ Preterm.HasVar target image first)
    (secondIndependent : ¬ Preterm.HasVar target image second)
    (thirdIndependent : ¬ Preterm.HasVar target image third) :
    Admissible signature
      [.regular firstSort ∅, .regular secondSort ∅, .regular thirdSort ∅,
        .bound objectSort, .regular objectSort {3}]
      target [first, second, third, .var image, body] := by
  apply (admissible_single_bound_iff _ _ 3 objectSort image rfl rfl ?_).mpr
  · refine ⟨.cons (.regular firstTyped) (.cons (.regular secondTyped) (.cons (.regular thirdTyped)
      (.cons (.bound bound) (.cons (.regular bodyTyped) .nil)))), ?_⟩
    intro other member absent
    simp [entries] at member
    rcases member with rfl | rfl | rfl | rfl | rfl
    · exact firstIndependent
    · exact secondIndependent
    · exact thirdIndependent
    · exact (absent rfl).elim
    · exact (absent (by simp [Binder.DependsOn])).elim
  · intro position sort found
    have member : (.bound sort, position) ∈
        ([.regular firstSort ∅, .regular secondSort ∅, .regular thirdSort ∅,
          .bound objectSort, .regular objectSort {3}] : Context).zipIdx := by
      simpa only [List.mem_zipIdx_iff_getElem?] using found
    simp at member
    exact member.2

theorem admissible_single_bound_after_two
    (first second body : Preterm) (firstSort secondSort objectSort image : Nat)
    (firstTyped : Preterm.HasType signature target first [] firstSort)
    (secondTyped : Preterm.HasType signature target second [] secondSort)
    (bound : target[image]? = some (.bound objectSort))
    (bodyTyped : Preterm.HasType signature target body [] objectSort)
    (firstIndependent : ¬ Preterm.HasVar target image first)
    (secondIndependent : ¬ Preterm.HasVar target image second) :
    Admissible signature
      [.regular firstSort ∅, .regular secondSort ∅, .bound objectSort, .regular objectSort {2}]
      target [first, second, .var image, body] := by
  apply (admissible_single_bound_iff _ _ 2 objectSort image rfl rfl ?_).mpr
  · refine ⟨.cons (.regular firstTyped) (.cons (.regular secondTyped)
      (.cons (.bound bound) (.cons (.regular bodyTyped) .nil))), ?_⟩
    intro other member absent
    simp [entries] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact firstIndependent
    · exact secondIndependent
    · exact (absent rfl).elim
    · exact (absent (by simp [Binder.DependsOn])).elim
  · intro position sort found
    have member : (.bound sort, position) ∈
        ([.regular firstSort ∅, .regular secondSort ∅,
          .bound objectSort, .regular objectSort {2}] : Context).zipIdx := by
      simpa only [List.mem_zipIdx_iff_getElem?] using found
    simp at member
    exact member.2

theorem Admissible.single_bound_after_three_independence
    {first second third body : Preterm} {firstSort secondSort thirdSort objectSort image : Nat}
    (admitted : Admissible signature
      [.regular firstSort ∅, .regular secondSort ∅, .regular thirdSort ∅,
        .bound objectSort, .regular objectSort {3}]
      target [first, second, third, .var image, body]) :
    (¬ Preterm.HasVar target image first) ∧ (¬ Preterm.HasVar target image second) ∧
      ¬ Preterm.HasVar target image third := by
  refine ⟨?_, ?_, ?_⟩
  · exact admitted.preserves_independence (u := 3) (v := 0) rfl rfl
      (by simp [Preterm.hasVar_var_iff]) rfl rfl
  · exact admitted.preserves_independence (u := 3) (v := 1) rfl rfl
      (by simp [Preterm.hasVar_var_iff]) rfl rfl
  · exact admitted.preserves_independence (u := 3) (v := 2) rfl rfl
      (by simp [Preterm.hasVar_var_iff]) rfl rfl

theorem admissible_single_bound_after_three_iff
    (first second third body : Preterm) (firstSort secondSort thirdSort objectSort image : Nat)
    (firstTyped : Preterm.HasType signature target first [] firstSort)
    (secondTyped : Preterm.HasType signature target second [] secondSort)
    (thirdTyped : Preterm.HasType signature target third [] thirdSort)
    (bound : target[image]? = some (.bound objectSort))
    (bodyTyped : Preterm.HasType signature target body [] objectSort) :
    Admissible signature
      [.regular firstSort ∅, .regular secondSort ∅, .regular thirdSort ∅,
        .bound objectSort, .regular objectSort {3}]
      target [first, second, third, .var image, body] ↔
      (¬ Preterm.HasVar target image first) ∧ (¬ Preterm.HasVar target image second) ∧
        ¬ Preterm.HasVar target image third := by
  constructor
  · exact Admissible.single_bound_after_three_independence
  · rintro ⟨firstIndependent, secondIndependent, thirdIndependent⟩
    exact admissible_single_bound_after_three first second third body
      firstSort secondSort thirdSort objectSort image firstTyped secondTyped thirdTyped bound bodyTyped
      firstIndependent secondIndependent thirdIndependent

theorem Admissible.single_bound_after_two_independence
    {first second body : Preterm} {firstSort secondSort objectSort image : Nat}
    (admitted : Admissible signature
      [.regular firstSort ∅, .regular secondSort ∅, .bound objectSort, .regular objectSort {2}]
      target [first, second, .var image, body]) :
    (¬ Preterm.HasVar target image first) ∧ ¬ Preterm.HasVar target image second := by
  constructor
  · exact admitted.preserves_independence (u := 2) (v := 0) rfl rfl
      (by simp [Preterm.hasVar_var_iff]) rfl rfl
  · exact admitted.preserves_independence (u := 2) (v := 1) rfl rfl
      (by simp [Preterm.hasVar_var_iff]) rfl rfl

theorem admissible_single_bound_after_two_iff
    (first second body : Preterm) (firstSort secondSort objectSort image : Nat)
    (firstTyped : Preterm.HasType signature target first [] firstSort)
    (secondTyped : Preterm.HasType signature target second [] secondSort)
    (bound : target[image]? = some (.bound objectSort))
    (bodyTyped : Preterm.HasType signature target body [] objectSort) :
    Admissible signature
      [.regular firstSort ∅, .regular secondSort ∅, .bound objectSort, .regular objectSort {2}]
      target [first, second, .var image, body] ↔
      (¬ Preterm.HasVar target image first) ∧ ¬ Preterm.HasVar target image second := by
  constructor
  · exact Admissible.single_bound_after_two_independence
  · rintro ⟨firstIndependent, secondIndependent⟩
    exact admissible_single_bound_after_two first second body firstSort secondSort objectSort image
      firstTyped secondTyped bound bodyTyped firstIndependent secondIndependent

#print axioms admissible_single_bound_after_three
#print axioms admissible_single_bound_iff
#print axioms admissible_single_bound_after_two
#print axioms Admissible.single_bound_after_three_independence
#print axioms admissible_single_bound_after_three_iff
#print axioms Admissible.single_bound_after_two_independence
#print axioms admissible_single_bound_after_two_iff

end Mettapedia.Languages.MM0.Kernel.Substitution
