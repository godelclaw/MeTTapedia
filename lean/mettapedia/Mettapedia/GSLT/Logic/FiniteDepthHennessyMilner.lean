import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Finite.Prod

/-!
# Finite-depth behavior and complete observation profiles

Round approximations use the actual labelled steps and atomic observations.
Their independent finite-depth readings record observations and the complete
set of successor readings at each label. Equality of readings is exactly
round agreement, without a branching assumption.

When the actual atom and label carriers are finite, every depth has finitely
many possible readings even if a state has infinitely many successors. This
condition concerns the actual labels, rather than a list of constructors or
instruments. Modal depth does not by itself specify an execution cost.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.HennessyMilner

universe uAtom uLabel

namespace Formula

def depth {Atom : Type uAtom} {Label : Type uLabel} : Formula Atom Label → Nat
  | .top => 0
  | .atom _ => 0
  | .conj first second => max first.depth second.depth
  | .neg inner => inner.depth
  | .dia _ inner => inner.depth + 1

theorem depth_conjList_le {Atom : Type uAtom} {Label : Type uLabel}
    (formulas : List (Formula Atom Label)) (bound : Nat)
    (bounded : ∀ formula ∈ formulas, formula.depth ≤ bound) :
    (conjList formulas).depth ≤ bound := by
  induction formulas with
  | nil => exact Nat.zero_le bound
  | cons first rest inductionHypothesis =>
      exact max_le (bounded first (List.mem_cons_self))
        (inductionHypothesis fun formula member => bounded formula (List.mem_cons_of_mem _ member))

end Formula

namespace FiniteDepth

def Profile (Atom : Type uAtom) (Label : Type uLabel) : Nat → Type (max uAtom uLabel)
  | 0 => ULift.{uLabel} (Set Atom)
  | depth + 1 => Set Atom × (Label → Set (Profile Atom Label depth))

instance finiteProfile {Atom : Type uAtom} {Label : Type uLabel}
    [Finite Atom] [Finite Label] (depth : Nat) : Finite (Profile Atom Label depth) := by
  induction depth with
  | zero => change Finite (ULift.{uLabel} (Set Atom)); infer_instance
  | succ depth inductionHypothesis =>
      let : Finite (Profile Atom Label depth) := inductionHypothesis
      change Finite (Set Atom × (Label → Set (Profile Atom Label depth)))
      infer_instance

variable {S : GSLT} (M : System.{uAtom, uLabel} S)

def observations (first second : S.Term) : Prop :=
  ∀ atom : M.Atom, M.observes atom first ↔ M.observes atom second

def Rounds : Nat → S.Term → S.Term → Prop
  | 0, first, second => observations M first second
  | depth + 1, first, second =>
      observations M first second ∧
      (∀ label target, M.act label first target →
        ∃ matched, M.act label second matched ∧ Rounds depth target matched) ∧
      (∀ label target, M.act label second target →
        ∃ matched, M.act label first matched ∧ Rounds depth matched target)

def reading : (depth : Nat) → S.Term → Profile M.Atom M.Label depth
  | 0, term => ⟨{atom | M.observes atom term}⟩
  | depth + 1, term =>
      ({atom | M.observes atom term},
        fun label => {profile | ∃ target, M.act label term target ∧ reading depth target = profile})

theorem observations_of_rounds (depth : Nat) {first second : S.Term}
    (related : Rounds M depth first second) : observations M first second := by
  cases depth with
  | zero => exact related
  | succ depth => exact related.1

theorem reading_eq_of_rounds (depth : Nat) :
    ∀ {first second : S.Term}, Rounds M depth first second → reading M depth first = reading M depth second := by
  induction depth with
  | zero =>
      intro first second related
      exact congrArg ULift.up (Set.ext related)
  | succ depth inductionHypothesis =>
      intro first second related
      apply Prod.ext
      · exact Set.ext related.1
      · funext label
        apply Set.ext
        intro profile
        constructor
        · rintro ⟨target, actual, readout⟩
          obtain ⟨matched, step, successors⟩ := related.2.1 label target actual
          exact ⟨matched, step, (inductionHypothesis successors).symm.trans readout⟩
        · rintro ⟨target, actual, readout⟩
          obtain ⟨matched, step, successors⟩ := related.2.2 label target actual
          exact ⟨matched, step, (inductionHypothesis successors).trans readout⟩

theorem rounds_of_reading_eq (depth : Nat) :
    ∀ {first second : S.Term}, reading M depth first = reading M depth second → Rounds M depth first second := by
  induction depth with
  | zero =>
      intro first second same atom
      exact Set.ext_iff.mp (congrArg ULift.down same) atom
  | succ depth inductionHypothesis =>
      intro first second same
      refine ⟨?_, ?_, ?_⟩
      · intro atom
        exact Set.ext_iff.mp (congrArg Prod.fst same) atom
      · intro label target actual
        have member : reading M depth target ∈ (reading M (depth + 1) first).2 label :=
          ⟨target, actual, rfl⟩
        rw [same] at member
        obtain ⟨matched, step, matching⟩ := member
        exact ⟨matched, step, inductionHypothesis matching.symm⟩
      · intro label target actual
        have member : reading M depth target ∈ (reading M (depth + 1) second).2 label :=
          ⟨target, actual, rfl⟩
        rw [← same] at member
        obtain ⟨matched, step, matching⟩ := member
        exact ⟨matched, step, inductionHypothesis matching⟩

theorem rounds_iff_reading_eq (depth : Nat) (first second : S.Term) :
    Rounds M depth first second ↔ reading M depth first = reading M depth second :=
  ⟨reading_eq_of_rounds M depth, rounds_of_reading_eq M depth⟩

theorem rounds_refl (depth : Nat) (term : S.Term) : Rounds M depth term term :=
  rounds_of_reading_eq M depth rfl

theorem rounds_symm (depth : Nat) {first second : S.Term}
    (related : Rounds M depth first second) : Rounds M depth second first :=
  rounds_of_reading_eq M depth (reading_eq_of_rounds M depth related).symm

theorem rounds_trans (depth : Nat) {first middle second : S.Term}
    (before : Rounds M depth first middle) (after : Rounds M depth middle second) :
    Rounds M depth first second :=
  rounds_of_reading_eq M depth ((reading_eq_of_rounds M depth before).trans (reading_eq_of_rounds M depth after))

theorem rounds_drop (depth : Nat) :
    ∀ {first second : S.Term}, Rounds M (depth + 1) first second → Rounds M depth first second := by
  induction depth with
  | zero => intro first second related; exact related.1
  | succ depth inductionHypothesis =>
      intro first second related
      refine ⟨related.1, ?_, ?_⟩
      · intro label target actual
        obtain ⟨matched, step, successors⟩ := related.2.1 label target actual
        exact ⟨matched, step, inductionHypothesis successors⟩
      · intro label target actual
        obtain ⟨matched, step, successors⟩ := related.2.2 label target actual
        exact ⟨matched, step, inductionHypothesis successors⟩

theorem rounds_of_isBisimulation {relation : S.Term → S.Term → Prop}
    (bisimulation : M.IsBisimulation relation) (depth : Nat) :
    ∀ {first second : S.Term}, relation first second → Rounds M depth first second := by
  induction depth with
  | zero => intro first second related; exact bisimulation.2.2 related
  | succ depth inductionHypothesis =>
      intro first second related
      refine ⟨bisimulation.2.2 related, ?_, ?_⟩
      · intro label target actual
        obtain ⟨matched, step, successors⟩ := bisimulation.1 related label actual
        exact ⟨matched, step, inductionHypothesis successors⟩
      · intro label target actual
        obtain ⟨matched, step, successors⟩ := bisimulation.2.1 related label actual
        exact ⟨matched, step, inductionHypothesis successors⟩

theorem rounds_of_bisimilar (depth : Nat) {first second : S.Term}
    (related : M.Bisimilar first second) : Rounds M depth first second := by
  obtain ⟨relation, bisimulation, member⟩ := related
  exact rounds_of_isBisimulation M bisimulation depth member

theorem rounds_of_equiv (depth : Nat) {first second : S.Term}
    (equivalent : S.Equiv first second) : Rounds M depth first second :=
  rounds_of_bisimilar M depth (M.bisimilar_of_equiv equivalent)

theorem reading_resp (depth : Nat) {first second : S.Term} (equivalent : S.Equiv first second) :
    reading M depth first = reading M depth second :=
  reading_eq_of_rounds M depth (rounds_of_equiv M depth equivalent)

def LogicallyEquivalent (depth : Nat) (first second : S.Term) : Prop :=
  ∀ formula : Formula M.Atom M.Label, formula.depth ≤ depth →
    (M.sat formula first ↔ M.sat formula second)

theorem sat_iff_of_rounds (formula : Formula M.Atom M.Label) :
    ∀ (depth : Nat) {first second : S.Term}, formula.depth ≤ depth →
      Rounds M depth first second → (M.sat formula first ↔ M.sat formula second) := by
  induction formula with
  | top => intro depth first second bounded related; exact Iff.rfl
  | atom atom =>
      intro depth first second bounded related
      exact observations_of_rounds M depth related atom
  | conj before after beforeRead afterRead =>
      intro depth first second bounded related
      exact and_congr (beforeRead depth (le_trans (Nat.le_max_left _ _) bounded) related)
        (afterRead depth (le_trans (Nat.le_max_right _ _) bounded) related)
  | neg inner inductionHypothesis =>
      intro depth first second bounded related
      exact not_congr (inductionHypothesis depth bounded related)
  | dia label inner inductionHypothesis =>
      intro depth first second bounded related
      cases depth with
      | zero => exact (Nat.not_succ_le_zero inner.depth bounded).elim
      | succ depth =>
          have innerBounded : inner.depth ≤ depth := Nat.le_of_succ_le_succ bounded
          constructor
          · rintro ⟨target, actual, held⟩
            obtain ⟨matched, step, successors⟩ := related.2.1 label target actual
            exact ⟨matched, step, (inductionHypothesis depth innerBounded successors).mp held⟩
          · rintro ⟨target, actual, held⟩
            obtain ⟨matched, step, successors⟩ := related.2.2 label target actual
            exact ⟨matched, step, (inductionHypothesis depth innerBounded successors).mpr held⟩

theorem logicallyEquivalent_of_rounds (depth : Nat) {first second : S.Term}
    (related : Rounds M depth first second) : LogicallyEquivalent M depth first second :=
  fun formula bounded => sat_iff_of_rounds M formula depth bounded related

end FiniteDepth

end Mettapedia.GSLT.HennessyMilner
