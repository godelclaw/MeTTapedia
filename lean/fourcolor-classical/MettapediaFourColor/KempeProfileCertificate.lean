import MettapediaFourColor.KempeAnswerComposition

/-! # Finite answers ranked by a shared semantic profile

The rank may be any function of the whole boundary trace. An application can
factor it through a smaller joint profile. Answer coverage can come from a
structural theorem or the reference's proved finite-cover specification. Its
existing well-founded certificate theorem then supplies Kempe co-closure.

This is a presentation of the Gonthier--Werner and Emery certificate argument,
not a new reducibility principle. It leaves terminal witnesses and the chosen
profile's adequacy as explicit obligations of each consumer.
-/

namespace FourColor.KempeProfileCertificate

variable {I : Type*}

def answerWord (word : I → List Color) (a : I × EdgePerm) : List Color :=
  (word a.1).map (a.2⁻¹ : EdgePerm)

theorem answerWord_map (word : I → List Color) (a : I × EdgePerm) :
    (answerWord word a).map a.2 = word a.1 := by
  simp only [answerWord, map_map_edgePerm, mul_inv_cancel, map_one_edgePerm]

/-- Semantic answer coverage and strict profile descent suffice for every state. -/
theorem sound_of_cover {P : List Color → Prop} (word : I → List Color)
    (rank : List Color → ℕ) (answers : I → List (I × EdgePerm))
    (checked : ∀ i, P (word i) ∨
      ((∀ gram, matchg [] (word i) gram →
          ∃ a ∈ answers i, matchg [] (answerWord word a) gram) ∧
        ∀ a ∈ answers i, rank (word a.1) < rank (word i)))
    (i : I) : KempeCoclosure P (word i) := by
  apply kempeCoclosure_of_rank (S := fun et => ∃ j, et = word j) rank ?_ ⟨i, rfl⟩
  rintro _ ⟨j, rfl⟩ gram hgram
  rcases checked j with terminal | ⟨cover, descent⟩
  · exact ⟨word j, hgram, Or.inl terminal⟩
  · obtain ⟨a, hamem, hmatch⟩ := cover gram hgram
    refine ⟨answerWord word a, hmatch, Or.inr ⟨a.2, ?_, ?_⟩⟩
    · exact ⟨a.1, answerWord_map word a⟩
    · rw [answerWord_map]
      exact descent a hamem

/-- The reference finite cover checker supplies the semantic coverage premise. -/
theorem sound {P : List Color → Prop} (word : I → List Color)
    (rank : List Color → ℕ) (answers : I → List (I × EdgePerm))
    (checked : ∀ i, P (word i) ∨
      (coversRec (word i) ((answers i).map fun a => ([], answerWord word a)) [] = true ∧
        ∀ a ∈ answers i, rank (word a.1) < rank (word i)))
    (i : I) : KempeCoclosure P (word i) := by
  apply sound_of_cover word rank answers ?_ i
  intro j
  rcases checked j with terminal | ⟨cover, descent⟩
  · exact Or.inl terminal
  · refine Or.inr ⟨?_, descent⟩
    intro gram hgram
    obtain ⟨_, hmem, hmatch⟩ := coversRec_sound _ _ [] cover gram hgram
    obtain ⟨a, hamem, rfl⟩ := List.mem_map.mp hmem
    exact ⟨a, hamem, hmatch⟩

end FourColor.KempeProfileCertificate
