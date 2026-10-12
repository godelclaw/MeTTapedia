import Mettapedia.GSLT.Logic.FiniteDepthHennessyMilner

/-!
# Complete characteristic tests at every finite observation depth

The formula for a profile tests every atomic observation and every possible
successor profile, positively or negatively. It is independently formed from
the finite actual atom and label carriers. Its satisfaction is exactly the
complete profile reading, at the stated modal depth.

Thus agreement on all tests through depth `n` is equivalent to `n` rounds of
observed bisimulation without requiring finite branching. The construction
does not identify depth with formula size or with a funded execution budget.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.GSLT.HennessyMilner.FiniteDepth

universe uAtom uLabel uIndex

variable {Atom : Type uAtom} {Label : Type uLabel}

def literal (present : Prop) (formula : Formula Atom Label) : Formula Atom Label := by
  classical
  exact if present then formula else .neg formula

theorem literal_depth (present : Prop) (formula : Formula Atom Label) :
    (literal present formula).depth = formula.depth := by
  classical
  by_cases held : present <;> simp [literal, held, Formula.depth]

def finiteConjunction {Index : Type uIndex} [Finite Index]
    (tests : Index → Formula Atom Label) : Formula Atom Label := by
  classical
  let : Fintype Index := Fintype.ofFinite Index
  exact Formula.conjList (Finset.univ.toList.map tests)

theorem finiteConjunction_depth {Index : Type uIndex} [Finite Index]
    (tests : Index → Formula Atom Label) (bound : Nat)
    (bounded : ∀ index, (tests index).depth ≤ bound) :
    (finiteConjunction tests).depth ≤ bound := by
  classical
  unfold finiteConjunction
  apply Formula.depth_conjList_le
  intro formula member
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
  exact bounded index

def atomicTests [Finite Atom] (observed : Set Atom) : Formula Atom Label :=
  finiteConjunction fun atom => literal (atom ∈ observed) (.atom atom)

theorem atomicTests_depth [Finite Atom] (observed : Set Atom) :
    (atomicTests (Label := Label) observed).depth = 0 := by
  apply Nat.eq_zero_of_le_zero
  apply finiteConjunction_depth
  intro atom
  rw [literal_depth]
  exact Nat.le_refl 0

def characteristic [Finite Atom] [Finite Label] :
    (depth : Nat) → Profile Atom Label depth → Formula Atom Label
  | 0, profile => atomicTests profile.down
  | depth + 1, profile =>
      .conj (atomicTests profile.1)
        (finiteConjunction fun label => finiteConjunction fun successor : Profile Atom Label depth =>
          literal (successor ∈ profile.2 label) (.dia label (characteristic depth successor)))

theorem characteristic_depth [Finite Atom] [Finite Label] (depth : Nat) :
    ∀ profile : Profile Atom Label depth, (characteristic depth profile).depth ≤ depth := by
  induction depth with
  | zero => intro profile; exact le_of_eq (atomicTests_depth profile.down)
  | succ depth inductionHypothesis =>
      intro profile
      apply max_le
      · rw [atomicTests_depth]
        exact Nat.zero_le _
      · apply finiteConjunction_depth
        intro label
        apply finiteConjunction_depth
        intro successor
        rw [literal_depth]
        exact Nat.succ_le_succ (inductionHypothesis successor)

variable {S : GSLT} (M : System.{uAtom, uLabel} S)

theorem literal_satisfaction (present : Prop) (formula : Formula M.Atom M.Label) (term : S.Term) :
    M.sat (literal present formula) term ↔ (M.sat formula term ↔ present) := by
  classical
  by_cases held : present <;> simp [literal, held, System.sat]

theorem finiteConjunction_satisfaction {Index : Type uIndex} [Finite Index]
    (tests : Index → Formula M.Atom M.Label) (term : S.Term) :
    M.sat (finiteConjunction tests) term ↔ ∀ index, M.sat (tests index) term := by
  classical
  let : Fintype Index := Fintype.ofFinite Index
  unfold finiteConjunction
  rw [M.sat_conjList]
  constructor
  · intro every index
    exact every (tests index) (List.mem_map.mpr
      ⟨index, Finset.mem_toList.mpr (Finset.mem_univ index), rfl⟩)
  · intro every formula member
    obtain ⟨index, _, rfl⟩ := List.mem_map.mp member
    exact every index

theorem atomicTests_satisfaction [Finite M.Atom] (observed : Set M.Atom) (term : S.Term) :
    M.sat (atomicTests observed) term ↔ ∀ atom, M.observes atom term ↔ atom ∈ observed := by
  rw [atomicTests, finiteConjunction_satisfaction]
  exact forall_congr' fun atom => literal_satisfaction M (atom ∈ observed) (.atom atom) term

theorem characteristic_satisfaction [Finite M.Atom] [Finite M.Label] (depth : Nat) :
    ∀ (profile : Profile M.Atom M.Label depth) (term : S.Term),
      M.sat (characteristic depth profile) term ↔ reading M depth term = profile := by
  induction depth with
  | zero =>
      intro profile term
      rw [characteristic, atomicTests_satisfaction]
      constructor
      · intro held
        apply ULift.ext
        exact Set.ext held
      · intro same atom
        exact Set.ext_iff.mp (congrArg ULift.down same) atom
  | succ depth inductionHypothesis =>
      intro profile term
      change (M.sat (atomicTests profile.1) term ∧
        M.sat (finiteConjunction fun label => finiteConjunction fun successor : Profile M.Atom M.Label depth =>
          literal (successor ∈ profile.2 label) (.dia label (characteristic depth successor))) term) ↔ _
      rw [atomicTests_satisfaction, finiteConjunction_satisfaction]
      have successorTests : (∀ label : M.Label,
          M.sat (finiteConjunction fun successor : Profile M.Atom M.Label depth =>
            literal (successor ∈ profile.2 label) (.dia label (characteristic depth successor))) term) ↔
          ∀ label successor, (∃ target, M.act label term target ∧ reading M depth target = successor) ↔
            successor ∈ profile.2 label := by
        apply forall_congr'
        intro label
        rw [finiteConjunction_satisfaction]
        apply forall_congr'
        intro successor
        rw [literal_satisfaction]
        exact iff_congr
          (exists_congr fun target => and_congr Iff.rfl (inductionHypothesis successor target)) Iff.rfl
      rw [successorTests]
      constructor
      · rintro ⟨atoms, successors⟩
        apply Prod.ext
        · exact Set.ext atoms
        · funext label
          exact Set.ext (successors label)
      · intro same
        refine ⟨?_, ?_⟩
        · intro atom
          exact Set.ext_iff.mp (congrArg Prod.fst same) atom
        · intro label successor
          exact Set.ext_iff.mp (congrArg (fun value => value.2 label) same) successor

theorem rounds_of_logicallyEquivalent [Finite M.Atom] [Finite M.Label]
    (depth : Nat) {first second : S.Term} (related : LogicallyEquivalent M depth first second) :
    Rounds M depth first second := by
  have firstHolds : M.sat (characteristic depth (reading M depth first)) first :=
    (characteristic_satisfaction M depth _ _).mpr rfl
  have secondHolds := (related _ (characteristic_depth depth _)).mp firstHolds
  exact rounds_of_reading_eq M depth ((characteristic_satisfaction M depth _ _).mp secondHolds).symm

theorem logicallyEquivalent_iff_rounds [Finite M.Atom] [Finite M.Label]
    (depth : Nat) (first second : S.Term) :
    LogicallyEquivalent M depth first second ↔ Rounds M depth first second :=
  ⟨rounds_of_logicallyEquivalent M depth, logicallyEquivalent_of_rounds M depth⟩

end Mettapedia.GSLT.HennessyMilner.FiniteDepth
