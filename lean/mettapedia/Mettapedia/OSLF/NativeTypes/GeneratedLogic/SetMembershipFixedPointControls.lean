import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipFixedPointDecision
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipCertificateControls
import Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetMembershipSplitControls

/-!
# Controls: fixed points under steps back

- **Guarded**: "some descent of even length reaches the empty set" (`μX. empty ∨ ◇◇X`), "some descent goes on forever"
  (`νX. ◇X`), "every hereditary member, and the set itself, has a descent of even length to the empty set"
  (`νX. (μY. empty ∨ ◇◇Y) ∧ □X`), and "a descent of odd steps reaches `2`" (`μX. is 2 ∨ ◇(μY. X ∨ ◇◇Y)`), where the
  inner body reads the outer variable.
- **Not guarded**: a variable under a step back, a variable under a step back below a step forward, a variable under a
  sort, an unguarded variable, and an enclosing variable at the top of an inner body with no step forward since its
  binder.
- **Evaluated by the kernel**: `2` has a descent of even length to the empty set and `1` has none; `0` is hereditarily
  even and `2` is not; `3` reaches `2` by odd steps and `{1}` does not. No set descends forever: the greatest fixed
  point is the least one here.
- **Under a step back and a sort**, by the evaluation's exactness: some set containing `1` has a descent of even length
  to the empty set (the set `2`) and reaches `2` by odd steps (the set `{1, 2}`); no set containing anything descends
  forever, or is empty and hereditarily even; some set is hereditarily even, and not every set is.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings

open Mettapedia.OSLF.MeTTaIL.Syntax

/-- The body of `evenToEmpty`. -/
def evenToEmptyBody : Formula 1 := .or (.empty .hashSet) (.possibly .any (.possibly .any (.var 0)))

/-- **Some descent of even length reaches the empty set**: `μX. empty ∨ ◇◇X`. -/
def evenToEmpty : Formula 0 := .mu evenToEmptyBody

/-- **Hereditarily even**: `νX. (μY. empty ∨ ◇◇Y) ∧ □X`. -/
def hereditarilyEven : Formula 0 :=
  .nu (.and (.mu (.or (.empty .hashSet) (.possibly .any (.possibly .any (.var 0))))) (.necessarily .any (.var 0)))

/-- **A descent of odd steps reaches `2`**: `μX. is 2 ∨ ◇(μY. X ∨ ◇◇Y)`; the inner body reads `X`. -/
def oddToTwo : Formula 0 :=
  .mu (.or (.is two) (.possibly .any (.mu (.or (.var 1) (.possibly .any (.possibly .any (.var 0)))))))

theorem evenToEmpty_guarded : evenToEmpty.guarded = true := rfl

theorem descendsForever_guarded : descendsForever.guarded = true := rfl

theorem hereditarilyEven_guarded : hereditarilyEven.guarded = true := rfl

theorem oddToTwo_guarded : oddToTwo.guarded = true := rfl

/-- **Not guarded**: the variable under a step back, `μX. is 2 ∨ ◆X`. -/
theorem crossing_not_guarded :
    (Formula.mu (.or (.is two) (.sometimeBefore .any (.var 0))) : Formula 0).guarded = false := rfl

/-- **Not guarded**: a step back under a step forward still crosses, `νX. ◇◆X`. -/
theorem crossing_forward_not_guarded :
    (Formula.nu (.possibly .any (.sometimeBefore .any (.var 0))) : Formula 0).guarded = false := rfl

/-- **Not guarded**: the variable under a sort, `μX. empty ∨ ∃Set. X`. -/
theorem sort_not_guarded :
    (Formula.mu (.or (.empty .hashSet) (.someOf (.base "Set") (.var 0))) : Formula 0).guarded = false := rfl

/-- **Not guarded**: the variable unguarded, `μX. X ∨ empty`. -/
theorem unguarded_not_guarded : (Formula.mu (.or (.var 0) (.empty .hashSet)) : Formula 0).guarded = false := rfl

/-- **Not guarded**: the enclosing variable at the top of an inner body, `νX. μY. (empty ∧ X) ∨ ◇Y`. -/
theorem enclosing_unguarded_not_guarded :
    (Formula.nu (.mu (.or (.and (.empty .hashSet) (.var 1)) (.possibly .any (.var 0)))) : Formula 0).guarded = false :=
  rfl

/-! ## Evaluated by the kernel -/

/-- **`2` has a descent of even length to the empty set**: `2 ∋ 1 ∋ 0`. -/
theorem two_evenToEmpty : HFSets.sat Env.closed evenToEmpty (hfOf two_hf) :=
  (evalGuarded_iff rfl two_hf).mp (by decide)

/-- **`1` has none**: its only descent, `1 ∋ 0`, has length one. -/
theorem one_not_evenToEmpty : ¬ HFSets.sat Env.closed evenToEmpty (hfOf one_hereditary) := fun holds =>
  absurd ((evalGuarded_iff rfl one_hereditary).mpr holds) (by decide)

/-- `νX. ◇X` is false at every height of its iteration. -/
theorem fixIter_descendsForever : ∀ (fuel : ℕ) (term : Pattern),
    fixIter (fun below => evalWith (Fin.cons below Fin.elim0 : Fin 1 → Pattern → Bool) (.possibly .any (.var 0)))
      fuel term = false
  | 0, _ => rfl
  | fuel + 1, term => by
    have below : ∀ other, evalWith (Fin.cons (fixIter (fun below => evalWith (Fin.cons below Fin.elim0 :
        Fin 1 → Pattern → Bool) (.possibly .any (.var 0))) fuel) Fin.elim0 : Fin 1 → Pattern → Bool) (.var 0) other =
          false := fun other => fixIter_descendsForever fuel other
    show (decide (memberLabel .any) && (membersOf term).any _) = false
    simp [below]

/-- **No hereditarily finite set descends forever**: the greatest fixed point is the least one here. -/
theorem not_descendsForever (x : HF) : ¬ HFSets.sat Env.closed descendsForever x := by
  intro holds
  obtain ⟨term, termHolds, same⟩ := x.2
  have atTerm : HFSets.sat Env.closed descendsForever (hfOf termHolds) := by
    rwa [show hfOf termHolds = x from hf_ext same]
  have evaluated := (evalGuarded_iff rfl termHolds).mpr atTerm
  rw [show evalGuarded descendsForever term = false from fixIter_descendsForever (height term) term] at evaluated
  exact Bool.false_ne_true evaluated

theorem zero_hereditarilyEven : HFSets.sat Env.closed hereditarilyEven (hfOf zero_hf) :=
  (evalGuarded_iff rfl zero_hf).mp (by decide)

/-- `2` is not hereditarily even: its member `1` has only a descent of length one. -/
theorem two_not_hereditarilyEven : ¬ HFSets.sat Env.closed hereditarilyEven (hfOf two_hf) := fun holds =>
  absurd ((evalGuarded_iff rfl two_hf).mpr holds) (by decide)

theorem three_oddToTwo : HFSets.sat Env.closed oddToTwo (hfOf three_holds) :=
  (evalGuarded_iff rfl three_holds).mp (by decide +kernel)

/-- `{1}` does not reach `2`. -/
theorem justOne_not_oddToTwo : ¬ HFSets.sat Env.closed oddToTwo (hfOf justOne_holds) := fun holds =>
  absurd ((evalGuarded_iff rfl justOne_holds).mpr holds) (by decide +kernel)

/-! ## Under a step back and a sort -/

/-- **Some set containing `1` has a descent of even length to the empty set**: the set `2`. -/
theorem one_contained_evenToEmpty :
    HFSets.sat Env.closed (.sometimeBefore .any evenToEmpty) (hfOf one_hereditary) :=
  ⟨hfOf two_hf, ⟨trivial, (mem_zfOf_hf two_hf).mpr ⟨one, List.mem_cons_of_mem _ List.mem_cons_self, rfl⟩⟩,
    two_evenToEmpty⟩

theorem evalGuarded_one_contained_evenToEmpty : evalGuarded (.sometimeBefore .any evenToEmpty) one = true :=
  (evalGuarded_iff rfl one_hereditary).mpr one_contained_evenToEmpty

/-- **No set containing `x` descends forever.** -/
theorem not_contained_descendsForever (x : HF) :
    ¬ HFSets.sat Env.closed (.sometimeBefore .any descendsForever) x :=
  fun ⟨container, _, holds⟩ => not_descendsForever container holds

theorem evalGuarded_contained_descendsForever {term : Pattern} (holds : IsHF term) :
    evalGuarded (.sometimeBefore .any descendsForever) term = false := by
  rw [← Bool.not_eq_true, evalGuarded_iff rfl holds]
  exact not_contained_descendsForever _

/-- `{1, 2}`. -/
def oneTwo : Pattern := set [one, two]

theorem oneTwo_holds : IsHF oneTwo := (hereditary_iff _).mp (by decide)

theorem oneTwo_oddToTwo : HFSets.sat Env.closed oddToTwo (hfOf oneTwo_holds) :=
  (evalGuarded_iff rfl oneTwo_holds).mp (by decide +kernel)

/-- **Some set containing `1` reaches `2` by odd steps**: `{1, 2}`. -/
theorem one_contained_oddToTwo : HFSets.sat Env.closed (.sometimeBefore .any oddToTwo) (hfOf one_hereditary) :=
  ⟨hfOf oneTwo_holds, ⟨trivial, (mem_zfOf_hf oneTwo_holds).mpr ⟨one, List.mem_cons_self, rfl⟩⟩, oneTwo_oddToTwo⟩

/-- **The evaluation answers yes**, by its exactness. -/
theorem evalGuarded_one_contained_oddToTwo : evalGuarded (.sometimeBefore .any oddToTwo) one = true :=
  (evalGuarded_iff rfl one_hereditary).mpr one_contained_oddToTwo

/-- **No set containing anything is empty and hereditarily even.** -/
theorem not_contained_emptyEven (x : HF) :
    ¬ HFSets.sat Env.closed (.sometimeBefore .any (.and (.empty .hashSet) hereditarilyEven)) x := by
  rintro ⟨y, ⟨-, member⟩, ⟨-, empty⟩, -⟩
  rw [empty] at member
  exact ZFSet.notMem_empty _ member

/-- **And the evaluation answers no**, at every hereditary term. -/
theorem evalGuarded_contained_emptyEven {term : Pattern} (holds : IsHF term) :
    evalGuarded (.sometimeBefore .any (.and (.empty .hashSet) hereditarilyEven)) term = false := by
  rw [← Bool.not_eq_true, evalGuarded_iff rfl holds]
  exact not_contained_emptyEven _

/-- **Some set is hereditarily even**: the empty set. -/
theorem evalGuarded_some_hereditarilyEven {term : Pattern} (holds : IsHF term) :
    evalGuarded (.someOf (.base "Set") hereditarilyEven) term = true :=
  (evalGuarded_iff rfl holds).mpr ⟨hfOf zero_hf, rfl, zero_hereditarilyEven⟩

/-- **Not every set is hereditarily even**: `2` is not. -/
theorem evalGuarded_every_hereditarilyEven {term : Pattern} (holds : IsHF term) :
    evalGuarded (.everyOf (.base "Set") hereditarilyEven) term = false := by
  rw [← Bool.not_eq_true, evalGuarded_iff rfl holds]
  exact fun every => two_not_hereditarilyEven (every (hfOf two_hf) rfl)

end Mettapedia.OSLF.NativeTypes.GeneratedLogic.SetReadings
