import Mettapedia.OSLF.Framework.BackwardNarrowing

/-!
# The backward box over Herbrand states, with case splitting

The states that count are given by a predicate on ground terms (`herbrandSpan`): all ground terms,
or the well-sorted ones. Over them, the backward box at a ground term asks that every predecessor
among those states satisfy a property, and its premises are the counted instances of the symbolic
predecessors (`pastBoxOn_iff`).

A premise that no single pattern covers may still be covered case by case. A splitting discipline
(`Splitting`) says how a variable of a premise splits and guarantees that the cases have exactly
the premise's counted instances. Two disciplines are given:

- `Splitting.unsorted`: over a finite signature (`Enumeration`), a variable is a constant or an
  application to fresh variables;
- `Splitting.sorted`: over a sorted signature (`Sorting`), a variable is a constructor of the sort
  its position requires (`varSort`), and only well-sorted terms count (`WellSorted`).

`splitPastBox` checks the box with a splitting allowance; its verdicts are theorems
(`splitPastBox_proved`, `splitPastBox_refuted`).
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.BackwardNarrowing

open Mettapedia.Logic.LP
open Mettapedia.Logic.LP.FirstOrderRewriting (Context Equation Rewrite)
open Mettapedia.OSLF.Framework.DerivedModalities

variable {C F : Type} [DecidableEq C] [DecidableEq F] {arity : F → ℕ}

local notation "Sig" => Signature C F arity

omit [DecidableEq C] [DecidableEq F] in
theorem ground_of_freeVars {term : Term Sig} (none_ : ∀ v, v ∉ term.freeVars) : Ground term :=
  Finset.eq_empty_of_forall_notMem none_

/-! ## The backward box over counted states -/

variable (rules : List (Equation (Signature C F arity))) (counted : Term (Signature C F arity) → Prop)

/-- The steps between counted states. -/
def herbrandSpan : ReductionSpan (Term Sig) where
  Edge := {pair : Term Sig × Term Sig //
    Rewrite {rule | rule ∈ rules} pair.1 pair.2 ∧ counted pair.1 ∧ counted pair.2}
  source edge := edge.1.1
  target edge := edge.1.2

variable {rules counted}

/-- **The backward box over counted states has finitely many premises**: every counted
predecessor of a counted ground term satisfies a property exactly when every counted instance of
every symbolic predecessor does. -/
theorem pastBoxOn_iff {term : Term Sig} (ground : Ground term) (termCounted : counted term)
    (property : Term Sig → Prop) :
    derivedBox (herbrandSpan rules counted) property term ↔
      ∀ previous ∈ backward rules term, ∀ substitution : Subst Sig,
        counted (substitution.applyTerm previous) → property (substitution.applyTerm previous) := by
  constructor
  · intro holds previous member substitution previousCounted
    obtain ⟨event, starts, intoTerm⟩ := backward_sound member _ ⟨substitution, rfl⟩
    have reached : event.1.2 = term := (instance_ground ground _).mp intoTerm
    have rewrite : Rewrite {rule | rule ∈ rules} (substitution.applyTerm previous) term := by
      have step := event.2
      rw [show event.1.1 = substitution.applyTerm previous from starts, reached] at step
      exact step
    exact holds ⟨(substitution.applyTerm previous, term), rewrite, previousCounted, termCounted⟩ rfl
  · intro premises event ends
    rcases event with ⟨⟨source, target⟩, rewrite, sourceCounted, _⟩
    change target = term at ends
    subst ends
    have steps : derivedDiamond (span rules) (Instance target) source :=
      ⟨⟨(source, target), rewrite⟩, rfl, (instance_ground ground _).mpr rfl⟩
    rcases backward_complete (Term.linear_of_freeVars_empty ground) source steps with
      ⟨nonempty, _⟩ | ⟨previous, member, substitution, same⟩
    · rw [ground] at nonempty
      exact absurd nonempty Finset.not_nonempty_empty
    · show property source
      rw [← same] at sourceCounted ⊢
      exact premises previous member substitution sourceCounted

/-! ## Splitting disciplines -/

/-- **A splitting discipline**: the counted states, decided; how a variable of a term splits; and
the guarantee that the cases have exactly the term's counted instances. -/
structure Splitting (C F : Type) (arity : F → ℕ) where
  counted : Term (Signature C F arity) → Prop
  countedCheck : Term (Signature C F arity) → Bool
  countedCheck_iff : ∀ term, countedCheck term = true ↔ counted term
  counted_ground : ∀ term, counted term → Ground term
  cases : Term (Signature C F arity) → ℕ → List (Term (Signature C F arity))
  cases_instance : ∀ term v, ∀ case ∈ cases term v, Instance term case
  cases_cover : ∀ term v, v ∈ term.freeVars → ∀ substitution : Subst (Signature C F arity),
    counted (substitution.applyTerm term) → ∃ case ∈ cases term v, Instance case (substitution.applyTerm term)

/-- The leftmost variable of a term. -/
def firstVar : Term Sig → Option ℕ
  | .var v => some v
  | .const _ => none
  | .app _ arguments => (List.finRange _).findSome? fun i => firstVar (arguments i)

omit [DecidableEq C] [DecidableEq F] in
theorem firstVar_mem : ∀ {term : Term Sig} {v : ℕ}, firstVar term = some v → v ∈ term.freeVars
  | .var w, v, found => by simp [firstVar] at found; subst found; simp [Term.freeVars]
  | .const _, _, found => by simp [firstVar] at found
  | .app _ arguments, v, found => by
    simp only [firstVar] at found
    obtain ⟨i, _, read⟩ := List.exists_of_findSome?_eq_some found
    simp only [Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
    exact ⟨i, firstVar_mem read⟩

/-! ### The two cases of a variable -/

/-- A function symbol applied to fresh variables from an offset on. -/
def freshApplication (start : ℕ) (symbol : F) : Term Sig := .app symbol fun i => .var (start + i.val)

/-- A substitution extended at fresh variables from an offset on. -/
def extendFresh (substitution : Subst Sig) (start : ℕ) {count : ℕ} (values : Fin count → Term Sig) : Subst Sig :=
  fun w => if below : start ≤ w ∧ w - start < count then values ⟨w - start, below.2⟩ else substitution w

omit [DecidableEq C] [DecidableEq F] in
/-- An instance whose variable is a constant is an instance of the constant's case. -/
theorem instance_constant_case {term : Term Sig} {v : ℕ} {substitution : Subst Sig} {constant : C}
    (value : substitution v = .const constant) :
    Instance ((Subst.single v (.const constant)).applyTerm term) (substitution.applyTerm term) := by
  refine ⟨substitution, ?_⟩
  rw [← Subst.applyTerm_comp]
  apply Narrowing.Subst.applyTerm_congr
  intro w _
  by_cases same : w = v
  · subst same
    simp [Subst.comp, Subst.single_eq, value]
  · simp [Subst.comp, Subst.single_ne _ same]

omit [DecidableEq C] [DecidableEq F] in
/-- An instance whose variable is an application is an instance of the symbol's case. -/
theorem instance_application_case {term : Term Sig} {v : ℕ} {substitution : Subst Sig} {symbol : F}
    {arguments : Fin (arity symbol) → Term Sig} (value : substitution v = .app symbol arguments) :
    Instance ((Subst.single v (freshApplication (offset term) symbol)).applyTerm term)
      (substitution.applyTerm term) := by
  refine ⟨extendFresh substitution (offset term) arguments, ?_⟩
  rw [← Subst.applyTerm_comp]
  apply Narrowing.Subst.applyTerm_congr
  intro w member
  by_cases same : w = v
  · subst same
    simp only [Subst.comp, Subst.single_eq, freshApplication, Subst.applyTerm_app, value]
    congr 1
    funext i
    simp [Subst.applyTerm, extendFresh]
  · have below := lt_offset member
    simp only [Subst.comp, Subst.single_ne _ same]
    have notFresh : ¬ (offset term ≤ w ∧ w - offset term < arity symbol) :=
      fun h => absurd h.1 (Nat.not_le.mpr below)
    simp [extendFresh, notFresh]

omit [DecidableEq C] [DecidableEq F] in
theorem instance_of_case {term : Term Sig} {v : ℕ} {replacement : Term Sig} :
    Instance term ((Subst.single v replacement).applyTerm term) :=
  ⟨_, rfl⟩

/-! ### Unsorted Herbrand states -/

/-- A finite signature, listed. -/
structure Enumeration (C F : Type) where
  constants : List C
  symbols : List F
  constants_complete : ∀ constant, constant ∈ constants
  symbols_complete : ∀ symbol, symbol ∈ symbols

omit [DecidableEq C] [DecidableEq F] in
/-- The values a ground instance gives to a term's variables are ground. -/
theorem ground_values (substitution : Subst Sig) :
    ∀ (term : Term Sig), Ground (substitution.applyTerm term) → ∀ v ∈ term.freeVars, Ground (substitution v)
  | .var w, ground, v, inside => by
    simp only [Term.freeVars, Finset.mem_singleton] at inside
    subst inside
    exact ground
  | .const _, _, v, inside => by simp [Term.freeVars] at inside
  | .app _ arguments, ground, v, inside => by
    simp only [Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and] at inside
    obtain ⟨i, inside⟩ := inside
    apply ground_values substitution (arguments i) _ v inside
    apply ground_of_freeVars
    intro w member
    have outer : w ∈ (substitution.applyTerm (.app _ arguments)).freeVars := by
      simp only [Subst.applyTerm_app, Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and]
      exact ⟨i, member⟩
    rw [ground] at outer
    exact Finset.notMem_empty w outer

/-- Every constant, and every function symbol on fresh variables. -/
def splitAll (enumeration : Enumeration C F) (term : Term Sig) (v : ℕ) : List (Term Sig) :=
  enumeration.constants.map (fun constant => (Subst.single v (.const constant)).applyTerm term) ++
    enumeration.symbols.map fun symbol => (Subst.single v (freshApplication (offset term) symbol)).applyTerm term

/-- **All ground terms count**; a variable splits over the whole signature. -/
def Splitting.unsorted (enumeration : Enumeration C F) : Splitting C F arity where
  counted := Ground
  countedCheck term := decide (term.freeVars = ∅)
  countedCheck_iff _ := decide_eq_true_iff
  counted_ground _ ground := ground
  cases := splitAll enumeration
  cases_instance term v case member := by
    simp only [splitAll, List.mem_append, List.mem_map] at member
    rcases member with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact instance_of_case
  cases_cover term v inside substitution ground := by
    have valueGround := ground_values substitution term ground v inside
    cases value : substitution v with
    | var u =>
      rw [value] at valueGround
      have : u ∈ (Term.var u : Term Sig).freeVars := by simp [Term.freeVars]
      rw [valueGround] at this
      exact absurd this (Finset.notMem_empty u)
    | const constant =>
      exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem (enumeration.constants_complete constant)),
        instance_constant_case value⟩
    | app symbol arguments =>
      exact ⟨_, List.mem_append_right _ (List.mem_map_of_mem (f := fun symbol =>
          (Subst.single v (freshApplication (offset term) symbol)).applyTerm term)
          (enumeration.symbols_complete symbol)),
        instance_application_case value⟩

/-! ### Well-sorted states -/

/-- **A sorted signature**: the sort of each constant and of each symbol's result and arguments,
with the constructors of each sort listed. -/
structure Sorting (C F S : Type) (arity : F → ℕ) where
  constant : C → Option S
  symbol : F → Option S
  argument : (symbol : F) → Fin (arity symbol) → S
  constantsOf : S → List C
  symbolsOf : S → List F
  constants_complete : ∀ constant' sort, constant constant' = some sort → constant' ∈ constantsOf sort
  symbols_complete : ∀ symbol' sort, symbol symbol' = some sort → symbol' ∈ symbolsOf sort

variable {S : Type} [DecidableEq S]

/-- A ground term of a sort. -/
def WellSorted (sorting : Sorting C F S arity) : Term Sig → S → Prop
  | .var _, _ => False
  | .const constant, sort => sorting.constant constant = some sort
  | .app symbol arguments, sort =>
      sorting.symbol symbol = some sort ∧ ∀ i, WellSorted sorting (arguments i) (sorting.argument symbol i)

/-- Well-sortedness, decided. -/
def sortedCheck (sorting : Sorting C F S arity) : Term Sig → S → Bool
  | .var _, _ => false
  | .const constant, sort => decide (sorting.constant constant = some sort)
  | .app symbol arguments, sort =>
      decide (sorting.symbol symbol = some sort) &&
        (List.finRange _).all fun i => sortedCheck sorting (arguments i) (sorting.argument symbol i)

omit [DecidableEq C] [DecidableEq F] in
theorem sortedCheck_iff (sorting : Sorting C F S arity) :
    ∀ (term : Term Sig) (sort : S), sortedCheck sorting term sort = true ↔ WellSorted sorting term sort
  | .var _, _ => by simp [sortedCheck, WellSorted]
  | .const _, _ => by simp [sortedCheck, WellSorted]
  | .app symbol arguments, sort => by
    simp only [sortedCheck, WellSorted, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_finRange, true_implies]
    exact and_congr_right fun _ => forall_congr' fun i => sortedCheck_iff sorting (arguments i) _

omit [DecidableEq C] [DecidableEq F] [DecidableEq S] in
theorem sorted_ground (sorting : Sorting C F S arity) :
    ∀ (term : Term Sig) (sort : S), WellSorted sorting term sort → Ground term
  | .var _, _, sorted => sorted.elim
  | .const _, _, _ => rfl
  | .app _ arguments, _, ⟨_, sorted⟩ => by
    apply ground_of_freeVars
    intro v inside
    simp only [Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and] at inside
    obtain ⟨i, inside⟩ := inside
    have ground := sorted_ground sorting (arguments i) _ (sorted i)
    rw [ground] at inside
    exact Finset.notMem_empty v inside

/-- The sort a variable's leftmost position requires. -/
def varSort (sorting : Sorting C F S arity) : Term Sig → S → ℕ → Option S
  | .var w, sort, v => if w = v then some sort else none
  | .const _, _, _ => none
  | .app symbol arguments, _, v =>
      (List.finRange _).findSome? fun i => varSort sorting (arguments i) (sorting.argument symbol i) v

omit [DecidableEq C] [DecidableEq F] [DecidableEq S] in
theorem varSort_sorted (sorting : Sorting C F S arity) (substitution : Subst Sig) :
    ∀ (term : Term Sig) (sort : S) {v : ℕ} {required : S}, varSort sorting term sort v = some required →
      WellSorted sorting (substitution.applyTerm term) sort → WellSorted sorting (substitution v) required
  | .var w, sort, v, required, found, sorted => by
    simp only [varSort] at found
    split_ifs at found with same
    cases found
    subst same
    exact sorted
  | .const _, _, _, _, found, _ => by simp [varSort] at found
  | .app symbol arguments, sort, v, required, found, sorted => by
    simp only [varSort] at found
    obtain ⟨i, _, read⟩ := List.exists_of_findSome?_eq_some found
    exact varSort_sorted sorting substitution (arguments i) _ read (sorted.2 i)

omit [DecidableEq C] [DecidableEq F] [DecidableEq S] in
theorem varSort_some (sorting : Sorting C F S arity) (substitution : Subst Sig) :
    ∀ (term : Term Sig) (sort : S) {v : ℕ}, v ∈ term.freeVars →
      WellSorted sorting (substitution.applyTerm term) sort → ∃ required, varSort sorting term sort v = some required
  | .var w, sort, v, inside, _ => by
    simp only [Term.freeVars, Finset.mem_singleton] at inside
    subst inside
    exact ⟨sort, by simp [varSort]⟩
  | .const _, _, _, inside, _ => by simp [Term.freeVars] at inside
  | .app symbol arguments, sort, v, inside, sorted => by
    simp only [Term.freeVars, Finset.mem_biUnion, Finset.mem_univ, true_and] at inside
    obtain ⟨i, inside⟩ := inside
    obtain ⟨required, found⟩ := varSort_some sorting substitution (arguments i) _ inside (sorted.2 i)
    simp only [varSort]
    exact Option.isSome_iff_exists.mp (List.findSome?_isSome_iff.mpr ⟨i, List.mem_finRange i, by rw [found]; rfl⟩)

/-- The constructors of the sort a variable's position requires. -/
def splitSorted (sorting : Sorting C F S arity) (sort : S) (term : Term Sig) (v : ℕ) : List (Term Sig) :=
  match varSort sorting term sort v with
  | some required =>
      (sorting.constantsOf required).map (fun constant => (Subst.single v (.const constant)).applyTerm term) ++
        (sorting.symbolsOf required).map fun symbol =>
          (Subst.single v (freshApplication (offset term) symbol)).applyTerm term
  | none => []

/-- **The terms of a sort count**; a variable splits over the constructors of its position's sort. -/
def Splitting.sorted (sorting : Sorting C F S arity) (sort : S) : Splitting C F arity where
  counted term := WellSorted sorting term sort
  countedCheck term := sortedCheck sorting term sort
  countedCheck_iff term := sortedCheck_iff sorting term sort
  counted_ground term sorted := sorted_ground sorting term sort sorted
  cases := splitSorted sorting sort
  cases_instance term v case member := by
    unfold splitSorted at member
    split at member
    · simp only [List.mem_append, List.mem_map] at member
      rcases member with ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> exact instance_of_case
    · cases member
  cases_cover term v inside substitution sorted := by
    obtain ⟨required, found⟩ := varSort_some sorting substitution term sort inside sorted
    have valueSorted := varSort_sorted sorting substitution term sort found sorted
    unfold splitSorted
    rw [found]
    cases value : substitution v with
    | var u => rw [value] at valueSorted; exact valueSorted.elim
    | const constant =>
      rw [value] at valueSorted
      exact ⟨_, List.mem_append_left _ (List.mem_map_of_mem
          (sorting.constants_complete constant required valueSorted)), instance_constant_case value⟩
    | app symbol arguments =>
      rw [value] at valueSorted
      exact ⟨_, List.mem_append_right _ (List.mem_map_of_mem (f := fun symbol =>
          (Subst.single v (freshApplication (offset term) symbol)).applyTerm term)
          (sorting.symbols_complete symbol required valueSorted.1)),
        instance_application_case value⟩

/-! ## Checking with a splitting allowance -/

variable (splitting : Splitting C F arity) (types : List (Term (Signature C F arity)))

/-- A pattern among the types covers the term. -/
def coveredOnce (term : Term Sig) : Bool := types.any fun type => instanceOf type term

/-- **Every counted instance is covered**, splitting variables up to an allowance. -/
def coveredDeep : ℕ → Term Sig → Bool
  | 0, term => coveredOnce types term
  | allowance + 1, term => coveredOnce types term ||
      match firstVar term with
      | some v => (splitting.cases term v).all (coveredDeep allowance)
      | none => false

/-- **Some counted instance is not covered**, splitting variables up to an allowance. -/
def refutedDeep : ℕ → Term Sig → Bool
  | 0, term => splitting.countedCheck term && !coveredOnce types term
  | allowance + 1, term => (splitting.countedCheck term && !coveredOnce types term) ||
      match firstVar term with
      | some v => (splitting.cases term v).any (refutedDeep allowance)
      | none => false

variable {splitting types}

theorem coveredOnce_sound {term : Term Sig} (covered : coveredOnce types term = true) {state : Term Sig}
    (instance_ : Instance term state) : ∃ type ∈ types, Instance type state := by
  obtain ⟨type, member, checked⟩ := List.any_eq_true.mp covered
  exact ⟨type, member, instance_of_instance (instance_of_check checked) instance_⟩

theorem coveredDeep_sound : ∀ (allowance : ℕ) {term : Term Sig}, coveredDeep splitting types allowance term = true →
    ∀ substitution : Subst Sig, splitting.counted (substitution.applyTerm term) →
      ∃ type ∈ types, Instance type (substitution.applyTerm term)
  | 0, term, covered, substitution, _ => coveredOnce_sound covered ⟨substitution, rfl⟩
  | allowance + 1, term, covered, substitution, countedInstance => by
    simp only [coveredDeep, Bool.or_eq_true] at covered
    rcases covered with once | deep
    · exact coveredOnce_sound once ⟨substitution, rfl⟩
    · split at deep
      · rename_i v found
        obtain ⟨case, member, other, same⟩ :=
          splitting.cases_cover term v (firstVar_mem found) substitution countedInstance
        rw [← same] at countedInstance ⊢
        exact coveredDeep_sound allowance (List.all_eq_true.mp deep case member) other countedInstance
      · cases deep

theorem refutedDeep_sound : ∀ (allowance : ℕ) {term : Term Sig}, refutedDeep splitting types allowance term = true →
    ∃ substitution : Subst Sig, splitting.counted (substitution.applyTerm term) ∧
      ∀ type ∈ types, ¬ Instance type (substitution.applyTerm term)
  | 0, term, refuted => by
    simp only [refutedDeep, Bool.and_eq_true, Bool.not_eq_true'] at refuted
    obtain ⟨countedTerm, uncovered⟩ := refuted
    have termCounted := (splitting.countedCheck_iff term).mp countedTerm
    have termGround := splitting.counted_ground term termCounted
    refine ⟨Subst.id _, by rw [Subst.applyTerm_id]; exact termCounted, fun type member instance_ => ?_⟩
    rw [Subst.applyTerm_id] at instance_
    have checked := instanceOf_ground termGround instance_
    simp only [coveredOnce, List.any_eq_false] at uncovered
    exact uncovered type member (by simpa using checked)
  | allowance + 1, term, refuted => by
    simp only [refutedDeep, Bool.or_eq_true] at refuted
    rcases refuted with here | deeper
    · exact refutedDeep_sound 0 (by simpa [refutedDeep] using here)
    · split at deeper
      · rename_i v found
        obtain ⟨case, member, caseRefuted⟩ := List.any_eq_true.mp deeper
        obtain ⟨other, caseCounted, uncovered⟩ := refutedDeep_sound allowance caseRefuted
        obtain ⟨substitution, same⟩ :=
          instance_of_instance (splitting.cases_instance term v case member) ⟨other, rfl⟩
        exact ⟨substitution, same ▸ caseCounted, fun type typeMember => same ▸ uncovered type typeMember⟩
      · cases deeper

variable (splitting types) in
/-- **Check finitely many open premises**: proved when each is covered, case by case up to the
allowance; refuted when one has a counted instance no pattern covers. -/
def checkPremises (premises : List (Term Sig)) (allowance : ℕ) : PastBox :=
  if premises.all (coveredDeep splitting types allowance) then .proved
  else if premises.any (refutedDeep splitting types allowance) then .refuted
  else .unknown

theorem checkPremises_proved {premises : List (Term Sig)} {allowance : ℕ}
    (read : checkPremises splitting types premises allowance = .proved) :
    ∀ previous ∈ premises, ∀ substitution : Subst Sig, splitting.counted (substitution.applyTerm previous) →
      ∃ type ∈ types, Instance type (substitution.applyTerm previous) := by
  unfold checkPremises at read
  split_ifs at read with covered
  exact fun previous member substitution countedInstance =>
    coveredDeep_sound allowance (List.all_eq_true.mp covered previous member) substitution countedInstance

theorem checkPremises_refuted {premises : List (Term Sig)} {allowance : ℕ}
    (read : checkPremises splitting types premises allowance = .refuted) :
    ∃ previous ∈ premises, ∃ substitution : Subst Sig, splitting.counted (substitution.applyTerm previous) ∧
      ∀ type ∈ types, ¬ Instance type (substitution.applyTerm previous) := by
  unfold checkPremises at read
  split_ifs at read with covered refuted
  obtain ⟨previous, member, previousRefuted⟩ := List.any_eq_true.mp refuted
  exact ⟨previous, member, refutedDeep_sound allowance previousRefuted⟩

variable (rules splitting types) in
/-- **Check the backward box over counted states**, splitting open premises up to an allowance. -/
def splitPastBox (term : Term Sig) (allowance : ℕ) : PastBox :=
  checkPremises splitting types (backward rules term) allowance

theorem splitPastBox_proved {term : Term Sig} (ground : Ground term) (termCounted : splitting.counted term)
    {allowance : ℕ} (read : splitPastBox rules splitting types term allowance = .proved) :
    derivedBox (herbrandSpan rules splitting.counted) (fun state => ∃ type ∈ types, Instance type state) term :=
  (pastBoxOn_iff ground termCounted _).mpr (checkPremises_proved read)

theorem splitPastBox_refuted {term : Term Sig} (ground : Ground term) (termCounted : splitting.counted term)
    {allowance : ℕ} (read : splitPastBox rules splitting types term allowance = .refuted) :
    ¬ derivedBox (herbrandSpan rules splitting.counted) (fun state => ∃ type ∈ types, Instance type state) term := by
  intro holds
  obtain ⟨previous, member, substitution, countedInstance, uncovered⟩ := checkPremises_refuted read
  obtain ⟨type, typeMember, instance_⟩ :=
    (pastBoxOn_iff ground termCounted _).mp holds previous member substitution countedInstance
  exact uncovered type typeMember instance_

/-! ## Root steps -/

variable (rules counted) in
/-- The root steps between counted states. -/
def herbrandRootSpan : ReductionSpan (Term Sig) where
  Edge := {pair : Term Sig × Term Sig //
    (∃ rule ∈ rules, ∃ substitution : Subst Sig,
      substitution.applyTerm rule.left = pair.1 ∧ substitution.applyTerm rule.right = pair.2) ∧
    counted pair.1 ∧ counted pair.2}
  source edge := edge.1.1
  target edge := edge.1.2

/-- **The backward box over counted states, for root steps**, has the symbolic root predecessors
as premises. -/
theorem rootPastBoxOn_iff {term : Term Sig} (ground : Ground term) (termCounted : counted term)
    (property : Term Sig → Prop) :
    derivedBox (herbrandRootSpan rules counted) property term ↔
      ∀ previous ∈ backwardRoot rules term, ∀ substitution : Subst Sig,
        counted (substitution.applyTerm previous) → property (substitution.applyTerm previous) := by
  constructor
  · intro holds previous member substitution previousCounted
    obtain ⟨event, starts, intoTerm⟩ := backwardRoot_sound member _ ⟨substitution, rfl⟩
    have reached : event.1.2 = term := (instance_ground ground _).mp intoTerm
    obtain ⟨rule, ruleMember, ruleSubstitution, isSource, isTarget⟩ := event.2
    have sourceIs : event.1.1 = substitution.applyTerm previous := starts
    exact holds ⟨(substitution.applyTerm previous, term),
      ⟨rule, ruleMember, ruleSubstitution, isSource.trans sourceIs, isTarget.trans reached⟩,
      previousCounted, termCounted⟩ rfl
  · intro premises event ends
    rcases event with ⟨⟨source, target⟩, step, sourceCounted, _⟩
    change target = term at ends
    subst ends
    have steps : derivedDiamond (rootSpan rules) (Instance target) source :=
      ⟨⟨(source, target), step⟩, rfl, (instance_ground ground _).mpr rfl⟩
    rcases backwardRoot_complete source steps with ⟨variable_, _⟩ | ⟨previous, member, substitution, same⟩
    · cases target with
      | var v =>
        have inside : v ∈ (Term.var v : Term Sig).freeVars := by simp [Term.freeVars]
        rw [ground] at inside
        exact absurd inside (Finset.notMem_empty v)
      | const _ => simp [isVariable] at variable_
      | app _ _ => simp [isVariable] at variable_
    · show property source
      rw [← same] at sourceCounted ⊢
      exact premises previous member substitution sourceCounted

variable (rules splitting types) in
/-- **Check the backward box over counted states for root steps.** -/
def rootPastBox (term : Term Sig) (allowance : ℕ) : PastBox :=
  checkPremises splitting types (backwardRoot rules term) allowance

theorem rootPastBox_proved {term : Term Sig} (ground : Ground term) (termCounted : splitting.counted term)
    {allowance : ℕ} (read : rootPastBox rules splitting types term allowance = .proved) :
    derivedBox (herbrandRootSpan rules splitting.counted) (fun state => ∃ type ∈ types, Instance type state) term :=
  (rootPastBoxOn_iff ground termCounted _).mpr (checkPremises_proved read)

theorem rootPastBox_refuted {term : Term Sig} (ground : Ground term) (termCounted : splitting.counted term)
    {allowance : ℕ} (read : rootPastBox rules splitting types term allowance = .refuted) :
    ¬ derivedBox (herbrandRootSpan rules splitting.counted) (fun state => ∃ type ∈ types, Instance type state)
      term := by
  intro holds
  obtain ⟨previous, member, substitution, countedInstance, uncovered⟩ := checkPremises_refuted read
  obtain ⟨type, typeMember, instance_⟩ :=
    (rootPastBoxOn_iff ground termCounted _).mp holds previous member substitution countedInstance
  exact uncovered type typeMember instance_

end Mettapedia.OSLF.Framework.BackwardNarrowing
