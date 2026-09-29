import MettapediaFourColor.KempeBoundarySplit

/-!
# Kempe repair across a trivalent boundary junction

Joining two distinct nonzero edge colours keeps their sum and existentially
retains the two original colours. This operation preserves Kempe-closed
relations. Together with boundary splitting, it transports repair through an
actual junction in either direction, provided the consumer reconstructs every
successful joint boundary witness.

The chord surgery uses `gramNeg` and `gramFlip` from the Gonthier/Emery
development. In particular two open chords are joined together, rather than
replacing their correlated colours by separate marginal supports.
-/

namespace FourColor.KempeBoundaryMerge

open Color KempeBoundarySplit

/-- Remove the first two ports, joining their Kempe chords where necessary. -/
def mergeGram : Chromogram → Chromogram
  | .skip :: .push :: w | .push :: .skip :: w => .push :: gramNeg w
  | .push :: .pop1 :: w => .skip :: w
  | .push :: .push :: w => .skip :: gramFlip w
  | _ => [.pop0]

private theorem exists_color (P : Color → Prop) :
    (∃ c, P c) ↔ P c0 ∨ P c1 ∨ P c2 ∨ P c3 := by
  constructor
  · rintro ⟨c, hc⟩; cases c <;> simp_all
  · rintro (h | h | h | h) <;> exact ⟨_, h⟩

private theorem add_def (a b : Color) : a + b = Color.add a b := rfl

set_option maxHeartbeats 800000 in
-- Four colour cases for each of the sixteen leading-symbol pairs.
/-- Exact semantics, including all choices of the two hidden colours. -/
theorem match_merge (c : Color) (t : List Color) (w : Chromogram) :
    matchg [] (c :: t) (mergeGram w) ↔
      ∃ a b, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ a + b = c ∧
        matchg [] (a :: b :: t) w := by
  cases w with
  | nil => cases c <;> simp [mergeGram, matchg, matchStep]
  | cons s w =>
    cases w with
    | nil =>
      cases s <;> cases c <;>
        simp [exists_color, mergeGram, matchg, matchStep, add_def, Color.add]
    | cons u w =>
      cases s <;> cases u <;> cases c <;>
        simp [exists_color, mergeGram, matchg, matchStep, add_def, Color.add,
          matchg_gramNeg, matchg_gramFlip]

/-- The complete input pair remains in the existential witness. -/
def Merge (P : List Color → Prop) (et : List Color) : Prop :=
  ∃ a b t, et = (a + b) :: t ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ P (a :: b :: t)

theorem closed {P : List Color → Prop} (hP : KempeClosed P) : KempeClosed (Merge P) := by
  rintro _ ⟨a, b, t, rfl, ha, hb, hab, ht⟩
  obtain ⟨hperm, w, hw, hall⟩ := hP _ ht
  constructor
  · intro g
    refine ⟨g a, g b, t.map g, ?_, ?_, ?_, ?_, hperm g⟩
    · simp only [List.map_cons, EdgePerm.apply_add]
    · intro h; exact ha (g.apply_injective (by simpa using h))
    · intro h; exact hb (g.apply_injective (by simpa using h))
    · exact fun h => hab (g.apply_injective h)
  · refine ⟨mergeGram w, (match_merge _ _ _).mpr ⟨a, b, ha, hb, hab, rfl, hw⟩, ?_⟩
    intro et het
    cases et with
    | nil =>
      have hlen := matchg_length _ _ _ het
      cases w with
      | nil => simp [mergeGram] at hlen
      | cons s w => cases w with
        | nil => cases s <;> simp [mergeGram] at hlen
        | cons u w => cases s <;> cases u <;> simp [mergeGram] at hlen
    | cons c t =>
      obtain ⟨a, b, ha, hb, hab, rfl, hm⟩ := (match_merge _ _ _).mp het
      exact ⟨a, b, t, rfl, ha, hb, hab, hall _ hm⟩

/-- Repair grows through a junction when every successful pair reconstructs. -/
theorem coclosure_expand {P Q : List Color → Prop}
    (reconstruct : ∀ a b t, a ≠ 0 → b ≠ 0 → a ≠ b →
      P ((a + b) :: t) → Q (a :: b :: t))
    (a b : Color) (t : List Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (repair : KempeCoclosure P ((a + b) :: t)) :
    KempeCoclosure Q (a :: b :: t) := by
  intro outside hout hold
  obtain ⟨et, hP, a', b', t', rfl, ha', hb', hab', ht'⟩ :=
    repair (Merge outside) (closed hout) ⟨a, b, t, rfl, ha, hb, hab, hold⟩
  exact ⟨_, reconstruct a' b' t' ha' hb' hab' hP, ht'⟩

/-- A repaired boundary relation remains repaired after a literal split. -/
theorem split_repair {P : List Color → Prop} (a b : Color) (t : List Color)
    (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b)
    (repair : KempeCoclosure P ((a + b) :: t)) :
    KempeCoclosure (Split P) (a :: b :: t) :=
  coclosure_expand (fun a b t ha hb hab h => ⟨a, b, t, rfl, ha, hb, hab, h⟩)
    a b t ha hb hab repair

end FourColor.KempeBoundaryMerge
