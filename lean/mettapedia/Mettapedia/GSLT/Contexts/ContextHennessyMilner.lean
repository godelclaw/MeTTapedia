import Mettapedia.GSLT.Contexts.ContextTheory

/-!
# Hennessy–Milner for context-labelled transitions

A probe of a theory presented through its contexts names observing contexts between interfaces (`Probe`). Its modal
formulas (`ProbeFormula`) say what a term does placed in an observer: some or every step of the placed term leads to a
formula at the observer's result interface.

- **Bisimilar terms satisfy the same formulas** (`holds_iff_of_isBisimulation`), and so do equivalent terms
  (`holds_iff_of_equations`), since equivalence is a bisimulation.
- **When a term placed in an observer has finitely many steps up to the equations** (`ImageFinite`), the converse holds
  (`bisimilar_iff_agree`): terms no formula of the probe tells apart are bisimilar as the probe sees it. A step left
  unmatched is told apart by the observer's possibility of the conjunction of formulas that separate its result from
  each representative result of the other side.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.ContextTheory

universe u

variable {theory : ContextTheory.{u}} (probe : theory.Probe)

/-- **The modal formulas of a probe**, at each index: the connectives, and some or every step of the term placed in an
observer. -/
inductive ProbeFormula : probe.Index → Type u where
  | top {index : probe.Index} : ProbeFormula index
  | bot {index : probe.Index} : ProbeFormula index
  | and {index : probe.Index} : ProbeFormula index → ProbeFormula index → ProbeFormula index
  | or {index : probe.Index} : ProbeFormula index → ProbeFormula index → ProbeFormula index
  | possibly {source target : probe.Index} : probe.Observer source target → ProbeFormula target →
      ProbeFormula source
  | necessarily {source target : probe.Index} : probe.Observer source target → ProbeFormula target →
      ProbeFormula source

namespace ProbeFormula

variable {probe}

/-- **What a formula says of a term**: a step of the term placed in the observer to a term with the inner formula, for
the possibility, and every such step for the necessity. -/
def Holds : {index : probe.Index} → ProbeFormula probe index → theory.Term (probe.interface index) → Prop
  | _, .top, _ => True
  | _, .bot, _ => False
  | _, .and left right, term => left.Holds term ∧ right.Holds term
  | _, .or left right, term => left.Holds term ∨ right.Holds term
  | _, .possibly observer inner, term => ∃ next, theory.Transition term (probe.label observer) next ∧ inner.Holds next
  | _, .necessarily observer inner, term =>
    ∀ next, theory.Transition term (probe.label observer) next → inner.Holds next

/-- The dual: each former exchanged with its dual. -/
def dual : {index : probe.Index} → ProbeFormula probe index → ProbeFormula probe index
  | _, .top => .bot
  | _, .bot => .top
  | _, .and left right => .or left.dual right.dual
  | _, .or left right => .and left.dual right.dual
  | _, .possibly observer inner => .necessarily observer inner.dual
  | _, .necessarily observer inner => .possibly observer inner.dual

/-- **The dual is the negation.** -/
theorem holds_dual : ∀ {index : probe.Index} (formula : ProbeFormula probe index) (term : theory.Term (probe.interface index)),
    formula.dual.Holds term ↔ ¬ formula.Holds term
  | _, .top, _ => by simp [dual, Holds]
  | _, .bot, _ => by simp [dual, Holds]
  | _, .and left right, term => by
    simp only [dual, Holds, holds_dual left term, holds_dual right term, not_and_or]
  | _, .or left right, term => by
    simp only [dual, Holds, holds_dual left term, holds_dual right term, not_or]
  | _, .possibly observer inner, term => by
    simp only [dual, Holds, fun next => holds_dual inner next, not_exists, not_and]
  | _, .necessarily observer inner, term => by
    simp only [dual, Holds, fun next => holds_dual inner next, not_forall, exists_prop]

/-- The conjunction of a list of formulas. -/
def conj {index : probe.Index} : List (ProbeFormula probe index) → ProbeFormula probe index
  | [] => .top
  | formula :: formulas => .and formula (conj formulas)

theorem holds_conj {index : probe.Index} : ∀ {formulas : List (ProbeFormula probe index)}
    {term : theory.Term (probe.interface index)}, (conj formulas).Holds term ↔ ∀ formula ∈ formulas, formula.Holds term
  | [], _ => by simp [conj, Holds]
  | _ :: _, _ => by simp only [conj, Holds, holds_conj, List.mem_cons, forall_eq_or_imp]

end ProbeFormula

open ProbeFormula

variable {probe}

/-- **Bisimilar terms satisfy the same formulas.** -/
theorem holds_iff_of_isBisimulation
    {relation : (index : probe.Index) → theory.Term (probe.interface index) → theory.Term (probe.interface index) → Prop}
    (bisimulation : probe.IsBisimulation relation) :
    ∀ {index : probe.Index} (formula : ProbeFormula probe index) {left right : theory.Term (probe.interface index)},
      relation index left right → (formula.Holds left ↔ formula.Holds right)
  | _, .top, _, _, _ => Iff.rfl
  | _, .bot, _, _, _ => Iff.rfl
  | _, .and first second, _, _, related =>
    and_congr (holds_iff_of_isBisimulation bisimulation first related)
      (holds_iff_of_isBisimulation bisimulation second related)
  | _, .or first second, _, _, related =>
    or_congr (holds_iff_of_isBisimulation bisimulation first related)
      (holds_iff_of_isBisimulation bisimulation second related)
  | _, .possibly observer inner, _, _, related => by
    constructor
    · rintro ⟨next, step, holds⟩
      obtain ⟨matched, matchedStep, nextRelated⟩ := bisimulation.1 related observer step
      exact ⟨matched, matchedStep, (holds_iff_of_isBisimulation bisimulation inner nextRelated).mp holds⟩
    · rintro ⟨next, step, holds⟩
      obtain ⟨matched, matchedStep, nextRelated⟩ := bisimulation.2 related observer step
      exact ⟨matched, matchedStep, (holds_iff_of_isBisimulation bisimulation inner nextRelated).mpr holds⟩
  | _, .necessarily observer inner, _, _, related => by
    constructor
    · intro every next step
      obtain ⟨matched, matchedStep, nextRelated⟩ := bisimulation.2 related observer step
      exact (holds_iff_of_isBisimulation bisimulation inner nextRelated).mp (every matched matchedStep)
    · intro every next step
      obtain ⟨matched, matchedStep, nextRelated⟩ := bisimulation.1 related observer step
      exact (holds_iff_of_isBisimulation bisimulation inner nextRelated).mpr (every matched matchedStep)

/-- **Bisimilar terms, as the probe sees them, satisfy the same formulas.** -/
theorem holds_iff_of_bisimilar {index : probe.Index} {left right : theory.Term (probe.interface index)}
    (bisimilar : probe.Bisimilar left right) (formula : ProbeFormula probe index) :
    formula.Holds left ↔ formula.Holds right := by
  obtain ⟨relation, bisimulation, related⟩ := bisimilar
  exact holds_iff_of_isBisimulation bisimulation formula related

/-- **Equivalent terms satisfy the same formulas.** -/
theorem holds_iff_of_equations {index : probe.Index} {left right : theory.Term (probe.interface index)}
    (equivalent : (theory.equations (probe.interface index)).r left right) (formula : ProbeFormula probe index) :
    formula.Holds left ↔ formula.Holds right :=
  holds_iff_of_bisimilar (Probe.bisimilar_of_equations probe equivalent) formula

variable (probe) in
/-- **The terms no formula of the probe tells apart.** -/
def Agree (index : probe.Index) (left right : theory.Term (probe.interface index)) : Prop :=
  ∀ formula : ProbeFormula probe index, formula.Holds left ↔ formula.Holds right

variable (probe) in
/-- **Finitely many steps up to the equations**: a term placed in an observer steps to some of a finite list of terms,
and to each of them, up to the equations. -/
def ImageFinite : Prop :=
  ∀ {source target : probe.Index} (observer : probe.Observer source target) (term : theory.Term (probe.interface source)),
    ∃ representatives : List (theory.Term (probe.interface target)),
      (∀ representative ∈ representatives, theory.Transition term (probe.label observer) representative) ∧
        ∀ next, theory.Transition term (probe.label observer) next →
          ∃ representative ∈ representatives, (theory.equations (probe.interface target)).r representative next

/-- A formula that holds at one term and fails at another, when they disagree. -/
theorem separates_of_not_agree {index : probe.Index} {first second : theory.Term (probe.interface index)}
    (differ : ¬ Agree probe index first second) :
    ∃ formula : ProbeFormula probe index, formula.Holds first ∧ ¬ formula.Holds second := by
  have found : ∃ formula : ProbeFormula probe index, ¬ (formula.Holds first ↔ formula.Holds second) := by
    by_contra none
    exact differ fun formula => by_contra fun differs => none ⟨formula, differs⟩
  obtain ⟨formula, differs⟩ := found
  by_cases holds : formula.Holds first
  · exact ⟨formula, holds, fun other => differs ⟨fun _ => other, fun _ => holds⟩⟩
  · refine ⟨formula.dual, (holds_dual formula first).mpr holds, fun dualHolds => ?_⟩
    have secondFails := (holds_dual formula second).mp dualHolds
    exact differs ⟨fun inside => (holds inside).elim, fun inside => (secondFails inside).elim⟩

/-- **An unmatched step is told apart**: if no step of `second` in the observer agrees with `next`, a formula holds at
`first` and fails at `second`. -/
theorem told_apart (finite : ImageFinite probe) {source target : probe.Index} (observer : probe.Observer source target)
    {first second : theory.Term (probe.interface source)} {next : theory.Term (probe.interface target)}
    (step : theory.Transition first (probe.label observer) next)
    (unmatched : ∀ matched, theory.Transition second (probe.label observer) matched → ¬ Agree probe target next matched) :
    ∃ formula : ProbeFormula probe source, formula.Holds first ∧ ¬ formula.Holds second := by
  classical
  obtain ⟨representatives, listed, covered⟩ := finite observer second
  have separates : ∀ representative : {item // item ∈ representatives}, ∃ formula : ProbeFormula probe target,
      formula.Holds next ∧ ¬ formula.Holds representative.1 := fun representative =>
    separates_of_not_agree (unmatched representative.1 (listed representative.1 representative.2))
  choose separating holds fails using separates
  refine ⟨.possibly observer (conj (representatives.attach.map separating)),
    ⟨next, step, holds_conj.mpr fun formula member => ?_⟩, ?_⟩
  · obtain ⟨representative, -, rfl⟩ := List.mem_map.mp member
    exact holds representative
  · rintro ⟨matched, matchedStep, matchedHolds⟩
    obtain ⟨representative, member, equivalent⟩ := covered matched matchedStep
    have atRepresentative := (holds_iff_of_equations equivalent _).mpr matchedHolds
    exact fails ⟨representative, member⟩ (holds_conj.mp atRepresentative _
      (List.mem_map.mpr ⟨⟨representative, member⟩, List.mem_attach _ _, rfl⟩))

/-- **Agreement on the formulas is a bisimulation**, with finitely many steps up to the equations. -/
theorem isBisimulation_agree (finite : ImageFinite probe) : probe.IsBisimulation (Agree probe) := by
  constructor
  · intro source left right agree target observer next step
    by_contra unmatched
    obtain ⟨formula, holds, fails⟩ := told_apart finite observer step
      fun matched matchedStep same => unmatched ⟨matched, matchedStep, same⟩
    exact fails ((agree formula).mp holds)
  · intro source left right agree target observer next' step
    by_contra unmatched
    obtain ⟨formula, holds, fails⟩ := told_apart finite observer step
      fun matched matchedStep same => unmatched ⟨matched, matchedStep, fun formula => (same formula).symm⟩
    exact fails ((agree formula).mpr holds)

/-- **Hennessy–Milner for context-labelled transitions**: with finitely many steps up to the equations, terms are
bisimilar as the probe sees them exactly when no formula of the probe tells them apart. -/
theorem bisimilar_iff_agree (finite : ImageFinite probe) {index : probe.Index}
    {left right : theory.Term (probe.interface index)} :
    probe.Bisimilar left right ↔ Agree probe index left right :=
  ⟨fun bisimilar formula => holds_iff_of_bisimilar bisimilar formula,
    fun agree => ⟨_, isBisimulation_agree finite, agree⟩⟩

end Mettapedia.GSLT.ContextTheory
