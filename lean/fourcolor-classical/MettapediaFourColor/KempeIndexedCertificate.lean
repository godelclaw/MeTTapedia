import MettapediaFourColor.KempeProfileCertificate

/-! # Kempe certificates ranked by witness records

Ranking records avoids a reverse search through a large table of traces.
Records may share the same trace: each record still has to cover every
exterior matching that trace, and every answer must have a smaller rank.
This is the usual well-founded Kempe certificate argument.
-/

namespace FourColor.KempeIndexedCertificate

open KempeProfileCertificate

theorem sound {I : Type*} {P : List Color → Prop} (word : I → List Color)
    (rank : I → ℕ) (answers : I → List (I × EdgePerm))
    (checked : ∀ i, P (word i) ∨
      ((∀ gram, matchg [] (word i) gram →
          ∃ a ∈ answers i, matchg [] (answerWord word a) gram) ∧
        ∀ a ∈ answers i, rank a.1 < rank i))
    (i : I) : KempeCoclosure P (word i) := by
  have descend : ∀ n i, rank i = n → KempeCoclosure P (word i) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro i hn outside closed holds
      rcases checked i with terminal | ⟨cover, lower⟩
      · exact ⟨word i, terminal, holds⟩
      · obtain ⟨_, gram, hmatches, stable⟩ := closed (word i) holds
        obtain ⟨a, ha, hm⟩ := cover gram hmatches
        have ans := stable _ hm
        have next := (closed _ ans).1 a.2
        rw [answerWord_map] at next
        exact ih (rank a.1) (hn ▸ lower a ha) a.1 rfl outside closed next
  exact descend (rank i) i rfl

end FourColor.KempeIndexedCertificate
