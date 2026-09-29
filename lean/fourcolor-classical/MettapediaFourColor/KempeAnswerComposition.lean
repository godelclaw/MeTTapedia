import FourColor.Cert

/-!
# Composing finite Kempe answers

A repair step must answer every chromogram that an exterior could supply.
The reference's proved `coversRec` specification checks this obligation for
a finite list of answers. Each answer may itself have a repair proof, so
these steps compose without recomputing a global Kempe fixed point.
-/

namespace FourColor.KempeAnswerComposition

theorem of_mem {P : List Color → Prop} {et : List Color} (h : P et) :
    KempeCoclosure P et := by
  intro Q _ hQ
  exact ⟨et, h, hQ⟩

/-- A finite cover by already repairable answers is itself repairable. -/
theorem of_answers {P : List Color → Prop} {et : List Color}
    (answers : List (List Color))
    (covers : coversRec et (answers.map fun t => ([], t)) [] = true)
    (repairs : ∀ t ∈ answers, KempeCoclosure P t) :
    KempeCoclosure P et := by
  intro Q hQ hQt
  obtain ⟨_, w, hw, hmatches⟩ := hQ et hQt
  obtain ⟨p, hp, hmatch⟩ := coversRec_sound et _ [] covers w hw
  obtain ⟨answer, ha, rfl⟩ := List.mem_map.mp hp
  exact repairs answer ha Q hQ (hmatches answer hmatch)

end FourColor.KempeAnswerComposition
