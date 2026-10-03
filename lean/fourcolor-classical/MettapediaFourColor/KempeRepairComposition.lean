import MettapediaFourColor.KempeIndexedCertificate

/-! # Ranked Kempe repairs with already proved repairs as leaves

All steps retain the same exterior predicate. A leaf may invoke another
repair theorem, so composition need not copy or rerun its certificate.
-/

namespace FourColor.KempeRepairComposition

open KempeProfileCertificate

theorem flatten {P : List Color → Prop} {et : List Color}
    (h : KempeCoclosure (KempeCoclosure P) et) : KempeCoclosure P et := by
  intro outside closed start
  obtain ⟨middle, repair, holds⟩ := h outside closed start
  exact repair outside closed holds

theorem sound {I : Type*} {P : List Color → Prop} (word : I → List Color)
    (rank : I → ℕ) (answers : I → List (I × EdgePerm))
    (checked : ∀ i, KempeCoclosure P (word i) ∨
      ((∀ gram, matchg [] (word i) gram →
          ∃ a ∈ answers i, matchg [] (answerWord word a) gram) ∧
        ∀ a ∈ answers i, rank a.1 < rank i))
    (i : I) : KempeCoclosure P (word i) :=
  flatten (KempeIndexedCertificate.sound word rank answers checked i)

end FourColor.KempeRepairComposition
