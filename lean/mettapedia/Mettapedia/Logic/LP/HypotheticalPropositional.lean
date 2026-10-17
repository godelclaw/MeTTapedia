import Mathlib.Data.Finset.Card
import Mathlib.Logic.Function.Iterate

/-!
# Propositional hypothetical Datalog

A clause concludes an atom from premises, each of which asks for an atom under
extra atomic hypotheses:

  `c ← (H₁ ⇒ a₁), …, (Hₙ ⇒ aₙ)`.

This is the propositional fragment of Bonner's hypothetical Datalog. It is the
shape of every "is this sort inhabited" question for a signature with binders:
a binding argument asks for its body under a hypothesis for the bound variable.

`Derives clauses hypotheses atom` is the least relation closed under the
hypothesis rule and the clauses. It is decided by a nested least fixed point
(`closure`): the outer iteration adds conclusions; a premise that adds
hypotheses asks the same procedure, with one unit of fuel less, for the
enlarged set, once per distinct hypothesis set. One more unit of fuel than the
number of hypothesis atoms is enough (`derives_iff`).

## Main results

* `Derives.mono`, `Derives.cut`: weakening and cut.
* `closure_sound`: everything computed is derivable, at any fuel.
* `closure_complete`: everything derivable is computed with enough fuel.
* `derives_iff`: the decision procedure is exact.
* `Derives.ofFirstOrder_iff`: without hypotheses in premises the procedure is
  ordinary least-model computation.
* `Derives.of_dominates`: clauses may be replaced by dominating ones, whose
  premises are axioms or ask for the same atom under more hypotheses.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.LP.HypotheticalPropositional

universe u

variable {Atom : Type u} [DecidableEq Atom]

/-- A clause with premises under extra hypotheses. -/
structure Clause (Atom : Type u) where
  premises : List (Finset Atom × Atom)
  conclusion : Atom

/-- Derivability from a finite set of hypotheses. -/
inductive Derives (clauses : List (Clause Atom)) : Finset Atom → Atom → Prop where
  | hyp {hypotheses : Finset Atom} {atom : Atom} :
      atom ∈ hypotheses → Derives clauses hypotheses atom
  | clause {hypotheses : Finset Atom} {clause : Clause Atom} :
      clause ∈ clauses →
      (∀ premise ∈ clause.premises, Derives clauses (premise.1 ∪ hypotheses) premise.2) →
      Derives clauses hypotheses clause.conclusion

variable {clauses : List (Clause Atom)}

/-- Weakening: more hypotheses derive more. -/
theorem Derives.mono {small large : Finset Atom} {atom : Atom}
    (derivation : Derives clauses small atom) (subset : small ⊆ large) :
    Derives clauses large atom := by
  induction derivation generalizing large with
  | hyp member => exact .hyp (subset member)
  | clause member _ ih =>
      exact .clause member fun premise premiseMember =>
        ih premise premiseMember (Finset.union_subset_union (subset_refl _) subset)

/-- Cut: derivable hypotheses may be discharged. -/
theorem Derives.cut {extended base : Finset Atom} {atom : Atom}
    (derivation : Derives clauses extended atom)
    (each : ∀ hypothesis ∈ extended, Derives clauses base hypothesis) :
    Derives clauses base atom := by
  induction derivation generalizing base with
  | hyp member => exact each _ member
  | clause member _ ih =>
      refine .clause member fun premise premiseMember => ih premise premiseMember ?_
      intro hypothesis hypothesisMember
      rcases Finset.mem_union.mp hypothesisMember with fromPremise | fromExtended
      · exact .hyp (Finset.mem_union_left _ fromPremise)
      · exact (each hypothesis fromExtended).mono Finset.subset_union_right

/-! ## The decision procedure -/

/-- Hypothesis atoms of a premise list. -/
def premiseHypotheses : List (Finset Atom × Atom) → Finset Atom
  | [] => ∅
  | premise :: premises => premise.1 ∪ premiseHypotheses premises

/-- Every atom that some premise of some clause may add as a hypothesis. -/
def hypothesisAtoms : List (Clause Atom) → Finset Atom
  | [] => ∅
  | clause :: clauses => premiseHypotheses clause.premises ∪ hypothesisAtoms clauses

theorem subset_premiseHypotheses {premises : List (Finset Atom × Atom)}
    {premise : Finset Atom × Atom} (member : premise ∈ premises) :
    premise.1 ⊆ premiseHypotheses premises := by
  induction premises with
  | nil => cases member
  | cons head tail ih =>
      rcases List.mem_cons.mp member with rfl | inTail
      · exact Finset.subset_union_left
      · exact (ih inTail).trans Finset.subset_union_right

theorem subset_hypothesisAtoms {clause : Clause Atom} (clauseMember : clause ∈ clauses)
    {premise : Finset Atom × Atom} (premiseMember : premise ∈ clause.premises) :
    premise.1 ⊆ hypothesisAtoms clauses := by
  induction clauses with
  | nil => cases clauseMember
  | cons head tail ih =>
      rcases List.mem_cons.mp clauseMember with rfl | inTail
      · exact (subset_premiseHypotheses premiseMember).trans Finset.subset_union_left
      · exact (ih inTail).trans Finset.subset_union_right

/-- Conclusions of the clauses. -/
def conclusions (clauses : List (Clause Atom)) : Finset Atom :=
  (clauses.map Clause.conclusion).toFinset

/-- Hypothesis sets of the premises, without repetition. -/
def hypothesisSets (clauses : List (Clause Atom)) : List (Finset Atom) :=
  (clauses.flatMap fun clause => clause.premises.map Prod.fst).dedup

theorem mem_hypothesisSets {clause : Clause Atom} (clauseMember : clause ∈ clauses)
    {premise : Finset Atom × Atom} (premiseMember : premise ∈ clause.premises) :
    premise.1 ∈ hypothesisSets clauses :=
  List.mem_dedup.mpr (List.mem_flatMap.mpr
    ⟨clause, clauseMember, List.mem_map.mpr ⟨premise, premiseMember, rfl⟩⟩)

/-- Read a table of closures by its key. -/
def lookup (table : List (Finset Atom × Finset Atom)) (key : Finset Atom) : Finset Atom :=
  ((table.find? fun entry => decide (entry.1 = key)).map Prod.snd).getD ∅

theorem lookup_map (keys : List (Finset Atom)) (value : Finset Atom → Finset Atom)
    {key : Finset Atom} (member : key ∈ keys) :
    lookup (keys.map fun entry => (entry, value entry)) key = value key := by
  induction keys with
  | nil => cases member
  | cons head tail ih =>
      by_cases same : head = key
      · subst same
        simp [lookup]
      · have inTail : key ∈ tail := by
          rcases List.mem_cons.mp member with equal | inTail
          · exact absurd equal.symm same
          · exact inTail
        simpa [lookup, same] using ih inTail

/-- A premise holds at `current`: when its hypotheses are already assumed its
atom must be in `current`; otherwise it must be in the closure for the
enlarged hypotheses, read from `inner`. -/
def check (hypotheses : Finset Atom) (inner : Finset Atom → Finset Atom) (current : Finset Atom)
    (premise : Finset Atom × Atom) : Bool :=
  if premise.1 ⊆ hypotheses then decide (premise.2 ∈ current)
  else decide (premise.2 ∈ inner premise.1)

/-- Conclusions of the clauses whose premises all hold. -/
def fresh (clauses : List (Clause Atom)) (hypotheses : Finset Atom)
    (inner : Finset Atom → Finset Atom) (current : Finset Atom) : Finset Atom :=
  ((clauses.filter fun clause => clause.premises.all (check hypotheses inner current)).map
    Clause.conclusion).toFinset

/-- One round of the outer iteration. -/
def grow (clauses : List (Clause Atom)) (hypotheses : Finset Atom)
    (inner : Finset Atom → Finset Atom) (current : Finset Atom) : Finset Atom :=
  current ∪ fresh clauses hypotheses inner current

/-- The nested least fixed point, with fuel bounding the nesting depth. The
closures for enlarged hypotheses are computed once per hypothesis set. -/
def closure (clauses : List (Clause Atom)) : Nat → Finset Atom → Finset Atom
  | 0, hypotheses => hypotheses
  | fuel + 1, hypotheses =>
      let inner := lookup (((hypothesisSets clauses).filter fun set => !decide (set ⊆ hypotheses)).map
        fun set => (set, closure clauses fuel (set ∪ hypotheses)))
      (grow clauses hypotheses inner)^[(conclusions clauses).card + 1] hypotheses

/-- The table used by `closure` at a given fuel and hypotheses. -/
def innerOf (clauses : List (Clause Atom)) (fuel : Nat) (hypotheses : Finset Atom) :
    Finset Atom → Finset Atom :=
  lookup (((hypothesisSets clauses).filter fun set => !decide (set ⊆ hypotheses)).map
    fun set => (set, closure clauses fuel (set ∪ hypotheses)))

theorem closure_succ (fuel : Nat) (hypotheses : Finset Atom) :
    closure clauses (fuel + 1) hypotheses =
      (grow clauses hypotheses (innerOf clauses fuel hypotheses))^[(conclusions clauses).card + 1]
        hypotheses := rfl

theorem innerOf_premise (fuel : Nat) (hypotheses : Finset Atom) {clause : Clause Atom}
    (clauseMember : clause ∈ clauses) {premise : Finset Atom × Atom}
    (premiseMember : premise ∈ clause.premises) (adds : ¬ premise.1 ⊆ hypotheses) :
    innerOf clauses fuel hypotheses premise.1 = closure clauses fuel (premise.1 ∪ hypotheses) :=
  lookup_map _ _ (List.mem_filter.mpr ⟨mem_hypothesisSets clauseMember premiseMember, by simpa using adds⟩)

/-- Fuel sufficient for every set of hypotheses. -/
def fuelFor (clauses : List (Clause Atom)) : Nat := (hypothesisAtoms clauses).card + 1

theorem mem_fresh {hypotheses : Finset Atom} {inner : Finset Atom → Finset Atom}
    {current : Finset Atom} {atom : Atom} :
    atom ∈ fresh clauses hypotheses inner current ↔
      ∃ clause ∈ clauses,
        (∀ premise ∈ clause.premises, check hypotheses inner current premise = true) ∧
        clause.conclusion = atom := by
  simp only [fresh, List.mem_toFinset, List.mem_map, List.mem_filter, List.all_eq_true]
  constructor
  · rintro ⟨clause, ⟨member, holds⟩, equal⟩
    exact ⟨clause, member, holds, equal⟩
  · rintro ⟨clause, member, holds, equal⟩
    exact ⟨clause, ⟨member, holds⟩, equal⟩

theorem fresh_subset (hypotheses : Finset Atom) (inner : Finset Atom → Finset Atom)
    (current : Finset Atom) : fresh clauses hypotheses inner current ⊆ conclusions clauses := by
  intro atom member
  obtain ⟨clause, clauseMember, _, rfl⟩ := mem_fresh.mp member
  simpa [conclusions] using ⟨clause, clauseMember, rfl⟩

/-- An inflationary iteration whose additions lie in a fixed finite set
stabilizes after one more round than that set has elements. -/
theorem iterate_union_stable (add : Finset Atom → Finset Atom) (bound : Finset Atom)
    (inside : ∀ set, add set ⊆ bound) (start : Finset Atom) :
    add ((fun set => set ∪ add set)^[bound.card + 1] start) ⊆
      (fun set => set ∪ add set)^[bound.card + 1] start := by
  set step : Finset Atom → Finset Atom := fun set => set ∪ add set with step_def
  have fixed : ∀ set, add set ⊆ set → step set = set := fun set stable =>
    Finset.union_eq_left.mpr stable
  have grows : ∀ set, ¬ add set ⊆ set → (set ∩ bound).card < (step set ∩ bound).card := by
    intro set unstable
    obtain ⟨atom, added, missing⟩ := Finset.not_subset.mp unstable
    apply Finset.card_lt_card
    refine Finset.ssubset_iff_subset_ne.mpr ⟨?_, ?_⟩
    · exact Finset.inter_subset_inter_right Finset.subset_union_left
    · intro equal
      have inStep : atom ∈ step set ∩ bound :=
        Finset.mem_inter.mpr ⟨Finset.mem_union_right _ added, inside set added⟩
      rw [← equal] at inStep
      exact missing (Finset.mem_inter.mp inStep).1
  have key : ∀ rounds, (∃ earlier ≤ rounds, add (step^[earlier] start) ⊆ step^[earlier] start) ∨
      rounds ≤ (step^[rounds] start ∩ bound).card := by
    intro rounds
    induction rounds with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ rounds ih =>
        rcases ih with ⟨earlier, before, stable⟩ | counted
        · exact Or.inl ⟨earlier, Nat.le_succ_of_le before, stable⟩
        · by_cases stable : add (step^[rounds] start) ⊆ step^[rounds] start
          · exact Or.inl ⟨rounds, Nat.le_succ rounds, stable⟩
          · right
            rw [Function.iterate_succ_apply']
            exact Nat.succ_le_of_lt (lt_of_le_of_lt counted (grows _ stable))
  rcases key (bound.card + 1) with ⟨earlier, before, stable⟩ | counted
  · have settled : step^[bound.card + 1] start = step^[earlier] start := by
      rw [show bound.card + 1 = (bound.card + 1 - earlier) + earlier by omega,
        Function.iterate_add_apply]
      exact Function.iterate_fixed (fixed _ stable) _
    rw [settled]
    exact stable
  · exfalso
    have := Finset.card_le_card (Finset.inter_subset_right :
      step^[bound.card + 1] start ∩ bound ⊆ bound)
    omega

theorem subset_iterate_grow (hypotheses : Finset Atom) (inner : Finset Atom → Finset Atom)
    (rounds : Nat) (start : Finset Atom) :
    start ⊆ (grow clauses hypotheses inner)^[rounds] start := by
  induction rounds with
  | zero => exact subset_refl _
  | succ rounds ih =>
      rw [Function.iterate_succ_apply']
      exact ih.trans Finset.subset_union_left

theorem subset_closure (fuel : Nat) (hypotheses : Finset Atom) :
    hypotheses ⊆ closure clauses fuel hypotheses := by
  cases fuel with
  | zero => exact subset_refl _
  | succ fuel => exact subset_iterate_grow _ _ _ _

/-- Saturation: no clause whose premises hold at `current` adds anything. -/
def Saturated (clauses : List (Clause Atom)) (hypotheses : Finset Atom)
    (inner : Finset Atom → Finset Atom) (current : Finset Atom) : Prop :=
  fresh clauses hypotheses inner current ⊆ current

theorem closure_saturated (fuel : Nat) (hypotheses : Finset Atom) :
    Saturated clauses hypotheses (innerOf clauses fuel hypotheses)
      (closure clauses (fuel + 1) hypotheses) :=
  iterate_union_stable (fresh clauses hypotheses (innerOf clauses fuel hypotheses))
    (conclusions clauses) (fresh_subset _ _) hypotheses

/-! ## Soundness -/

theorem closure_sound : ∀ (fuel : Nat) {hypotheses : Finset Atom} {atom : Atom},
    atom ∈ closure clauses fuel hypotheses → Derives clauses hypotheses atom
  | 0, _, _, member => .hyp member
  | fuel + 1, hypotheses, _, member => by
      have invariant : ∀ rounds,
          ∀ atom ∈ (grow clauses hypotheses (innerOf clauses fuel hypotheses))^[rounds] hypotheses,
            Derives clauses hypotheses atom := by
        intro rounds
        induction rounds with
        | zero => exact fun atom member => .hyp member
        | succ rounds ih =>
            intro atom member
            rw [Function.iterate_succ_apply'] at member
            rcases Finset.mem_union.mp member with old | new
            · exact ih atom old
            · obtain ⟨clause, clauseMember, holds, rfl⟩ := mem_fresh.mp new
              refine .clause clauseMember fun premise premiseMember => ?_
              have passed := holds premise premiseMember
              unfold check at passed
              split at passed
              · exact (ih _ (of_decide_eq_true passed)).mono Finset.subset_union_right
              · rename_i adds
                rw [innerOf_premise fuel hypotheses clauseMember premiseMember adds] at passed
                exact closure_sound fuel (of_decide_eq_true passed)
      exact invariant _ _ (by rwa [closure_succ] at member)

/-! ## Completeness -/

theorem complete_aux {hypotheses : Finset Atom} {atom : Atom}
    (derivation : Derives clauses hypotheses atom) :
    ∀ (fuel : Nat) (current : Finset Atom), hypotheses ⊆ current →
      Saturated clauses hypotheses (innerOf clauses fuel hypotheses) current →
      (hypothesisAtoms clauses \ hypotheses).card ≤ fuel → atom ∈ current := by
  induction derivation with
  | hyp member => exact fun _ _ subset _ _ => subset member
  | @clause hypotheses clause clauseMember _ ih =>
      intro fuel current subset saturated measure
      apply saturated
      refine mem_fresh.mpr ⟨clause, clauseMember, fun premise premiseMember => ?_, rfl⟩
      unfold check
      split
      · rename_i premiseIn
        have same : premise.1 ∪ hypotheses = hypotheses := Finset.union_eq_right.mpr premiseIn
        have ihHere := ih premise premiseMember
        rw [same] at ihHere
        exact decide_eq_true (ihHere fuel current subset saturated measure)
      · rename_i premiseOut
        obtain ⟨missing, missingPremise, missingHypotheses⟩ := Finset.not_subset.mp premiseOut
        have missingAtom : missing ∈ hypothesisAtoms clauses \ hypotheses :=
          Finset.mem_sdiff.mpr
            ⟨subset_hypothesisAtoms clauseMember premiseMember missingPremise, missingHypotheses⟩
        rw [innerOf_premise fuel hypotheses clauseMember premiseMember premiseOut]
        cases fuel with
        | zero =>
            exfalso
            have positive := Finset.card_pos.mpr ⟨missing, missingAtom⟩
            omega
        | succ fuel =>
            apply decide_eq_true
            apply ih premise premiseMember fuel _ (subset_closure _ _) (closure_saturated fuel _)
            have shrink : hypothesisAtoms clauses \ (premise.1 ∪ hypotheses) ⊆
                (hypothesisAtoms clauses \ hypotheses).erase missing := by
              intro element member
              obtain ⟨inAtoms, notEnlarged⟩ := Finset.mem_sdiff.mp member
              refine Finset.mem_erase.mpr ⟨?_, Finset.mem_sdiff.mpr ⟨inAtoms, ?_⟩⟩
              · rintro rfl
                exact notEnlarged (Finset.mem_union_left _ missingPremise)
              · exact fun inHypotheses => notEnlarged (Finset.mem_union_right _ inHypotheses)
            have := Finset.card_le_card shrink
            rw [Finset.card_erase_of_mem missingAtom] at this
            omega

theorem closure_complete {hypotheses : Finset Atom} {atom : Atom}
    (derivation : Derives clauses hypotheses atom) {fuel : Nat}
    (enough : (hypothesisAtoms clauses \ hypotheses).card ≤ fuel) :
    atom ∈ closure clauses (fuel + 1) hypotheses :=
  complete_aux derivation fuel _ (subset_closure _ _) (closure_saturated fuel _) enough

/-- The decision procedure is exact. -/
theorem derives_iff (hypotheses : Finset Atom) (atom : Atom) :
    Derives clauses hypotheses atom ↔ atom ∈ closure clauses (fuelFor clauses) hypotheses := by
  constructor
  · intro derivation
    exact closure_complete derivation
      (Finset.card_le_card Finset.sdiff_subset)
  · exact closure_sound _

instance (hypotheses : Finset Atom) (atom : Atom) : Decidable (Derives clauses hypotheses atom) :=
  decidable_of_iff _ (derives_iff hypotheses atom).symm

/-! ## Blocking -/

/-- If every clause concluding in `blocked` has a premise asking for a blocked
atom under unblocked hypotheses, no blocked atom is derivable from unblocked
hypotheses. -/
theorem not_derives_of_blocking (blocked : Atom → Prop)
    (blocking : ∀ clause ∈ clauses, blocked clause.conclusion →
      ∃ premise ∈ clause.premises, blocked premise.2 ∧ ∀ atom ∈ premise.1, ¬ blocked atom)
    {hypotheses : Finset Atom} (unblocked : ∀ atom ∈ hypotheses, ¬ blocked atom) {atom : Atom}
    (derivation : Derives clauses hypotheses atom) : ¬ blocked atom := by
  induction derivation with
  | hyp member => exact unblocked _ member
  | @clause hypotheses clause member _ ih =>
      intro isBlocked
      obtain ⟨premise, premiseMember, premiseBlocked, premiseUnblocked⟩ :=
        blocking clause member isBlocked
      refine ih premise premiseMember ?_ premiseBlocked
      intro atom atomMember
      rcases Finset.mem_union.mp atomMember with fromPremise | fromHypotheses
      · exact premiseUnblocked atom fromPremise
      · exact unblocked atom fromHypotheses

/-! ## Monotonicity in the clauses -/

/-- More clauses derive more. -/
theorem Derives.mono_clauses {small large : List (Clause Atom)} (subset : small ⊆ large)
    {hypotheses : Finset Atom} {atom : Atom} (derivation : Derives small hypotheses atom) :
    Derives large hypotheses atom := by
  induction derivation with
  | hyp member => exact .hyp member
  | clause member _ ih => exact .clause (subset member) ih

/-! ## Domination -/

/-- `small` dominates `big`: every clause of `big` has a clause of `small` with
the same conclusion, each of whose premises holds under any hypotheses in
`small` or is asked by the clause of `big` for the same atom under no more
hypotheses. -/
def Dominates (small big : List (Clause Atom)) : Prop :=
  ∀ clause ∈ big, ∃ witness ∈ small, witness.conclusion = clause.conclusion ∧
    ∀ premise ∈ witness.premises,
      (∀ hypotheses, Derives small hypotheses premise.2) ∨
      ∃ original ∈ clause.premises, original.2 = premise.2 ∧ original.1 ⊆ premise.1

/-- Dominating clauses derive at least as much. -/
theorem Derives.of_dominates {small big : List (Clause Atom)} (dominates : Dominates small big)
    {hypotheses : Finset Atom} {atom : Atom} (derivation : Derives big hypotheses atom) :
    Derives small hypotheses atom := by
  induction derivation with
  | hyp member => exact .hyp member
  | @clause hypotheses clause member _ ih =>
      obtain ⟨witness, witnessMember, sameConclusion, premises⟩ := dominates clause member
      rw [← sameConclusion]
      refine .clause witnessMember fun premise premiseMember => ?_
      rcases premises premise premiseMember with axiomatic | ⟨original, originalMember, sameAtom, fewer⟩
      · exact axiomatic _
      · rw [← sameAtom]
        exact (ih original originalMember).mono (Finset.union_subset_union fewer (subset_refl _))

/-! ## The first-order case -/

/-- Premises without hypotheses: ordinary propositional Horn clauses. -/
def FirstOrder (clauses : List (Clause Atom)) : Prop :=
  ∀ clause ∈ clauses, ∀ premise ∈ clause.premises, premise.1 = ∅

/-- Without hypotheses in premises, one round of fuel is enough. -/
theorem Derives.ofFirstOrder_iff (firstOrder : FirstOrder clauses)
    (hypotheses : Finset Atom) (atom : Atom) :
    Derives clauses hypotheses atom ↔ atom ∈ closure clauses 1 hypotheses := by
  constructor
  · intro derivation
    apply closure_complete derivation
    have empty : hypothesisAtoms clauses = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro atom member
      clear derivation
      induction clauses with
      | nil => simp [hypothesisAtoms] at member
      | cons head tail ih =>
          simp only [hypothesisAtoms, Finset.mem_union] at member
          rcases member with inHead | inTail
          · have : ∀ premises : List (Finset Atom × Atom),
                (∀ premise ∈ premises, premise.1 = ∅) → atom ∉ premiseHypotheses premises := by
              intro premises allEmpty
              induction premises with
              | nil => simp [premiseHypotheses]
              | cons first rest restIh =>
                  simp only [premiseHypotheses, Finset.mem_union, not_or]
                  refine ⟨?_, restIh fun premise member => allEmpty premise (List.mem_cons_of_mem _ member)⟩
                  rw [allEmpty first List.mem_cons_self]
                  exact Finset.notMem_empty _
            exact this head.premises (firstOrder head List.mem_cons_self) inHead
          · exact ih (fun clause member => firstOrder clause (List.mem_cons_of_mem _ member)) inTail
    simp [empty]
  · exact closure_sound 1

end Mettapedia.Logic.LP.HypotheticalPropositional
