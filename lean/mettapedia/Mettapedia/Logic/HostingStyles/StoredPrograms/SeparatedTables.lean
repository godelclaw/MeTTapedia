import Mettapedia.Logic.HostingStyles.StoredPrograms.TableCheck
import Mettapedia.Logic.HostingStyles.StoredPrograms.Overlap
import Mettapedia.Logic.HostingStyles.StoredPrograms.Letters

/-!
# The table of a separated program is orthogonal

`Overlap.lean` reads off a program whether the equations of one head have
left sides that are apart (`Separated`).  This module carries that property
to the table:

**The table of a program of the class whose equations are separated is a
stored table** (`storedTable_programRules`), for every spelling that writes
two names apart (`Spelling.Apart`).  So its theory is orthogonal
(`separated_orthogonal`), with no computation on the table.

* Two patterns that are apart are read as two terms that clash
  (`clashes_pattern`): the reading is constructor by constructor, two
  constructors are two kinds, two names are written apart, and two literals
  are read apart (`clashes_literal`).
* The rule of an equation with distinct variables and a bound right side
  passes the test of one rule (`storedRuleCheck_ruleOf`).

Both spellings write names apart: a name as a constant
(`constantSpelling_apart`) and a name in letters (`letterSpelling_apart`).

So the two statements of the task are about one condition on the program:
for a program of the class that calls no primitive of its host and whose
equations are separated, a value that the engine returns for a call is a
reduct of the call, and the only normal form that the call reaches
(`separated_normalForm_unique`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HostingStyles.StoredPrograms

open Mettapedia.GSLT
open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.DeterministicEquations
  (Program Equation Host Env LeftLinear patternVarsList Applies)
open Mettapedia.GSLT.Dedukti
  (Theory RewriteRule Step Reduces inst binderFree usesOnly algebraic clashes)
open Mettapedia.Logic.Relation (IsNormal)
open Mettapedia.Logic.HostingStyles.AtomsReduce (RunnableEquations programTheory)

/-! ## Spellings that write names apart -/

/-- **A spelling writes names apart**: the writings of two names clash. -/
def Spelling.Apart (N : Spelling) : Prop :=
  ∀ first second : String, first ≠ second → clashes (N.write first) (N.write second) = true

theorem constantSpelling_apart : constantSpelling.Apart := fun first second different => by
  simpa [constantSpelling, clashes] using different

theorem clashes_digitsTerm : ∀ {first second : List Bool}, first ≠ second →
    clashes (digitsTerm first) (digitsTerm second) = true
  | [], [], different => absurd rfl different
  | [], true :: _, _ => rfl
  | [], false :: _, _ => rfl
  | true :: _, [], _ => rfl
  | false :: _, [], _ => rfl
  | true :: _, false :: _, _ => by simp [digitsTerm, clashes]
  | false :: _, true :: _, _ => by simp [digitsTerm, clashes]
  | true :: rest, true :: others, different => by
      have inner : rest ≠ others := fun same => different (by rw [same])
      simp [digitsTerm, clashes, clashes_digitsTerm inner]
  | false :: rest, false :: others, different => by
      have inner : rest ≠ others := fun same => different (by rw [same])
      simp [digitsTerm, clashes, clashes_digitsTerm inner]

theorem clashes_lettersTerm : ∀ {first second : List (List Bool)}, first ≠ second →
    clashes (lettersTerm first) (lettersTerm second) = true
  | [], [], different => absurd rfl different
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | letter :: rest, other :: others, different => by
      by_cases sameLetter : letter = other
      · have inner : rest ≠ others := fun same => different (by rw [sameLetter, same])
        have tails := clashes_lettersTerm inner
        simp only [lettersTerm] at tails
        simp [lettersTerm, cells, clashes, tails]
      · simp [lettersTerm, cells, clashes, clashes_digitsTerm sameLetter]

theorem letterSpelling_apart : letterSpelling.Apart := fun _ _ different =>
  clashes_lettersTerm fun same => different (lettersOf_injective same)

/-! ## Readings that clash -/

theorem clashes_unary : ∀ {first second : Nat}, first ≠ second →
    clashes (unary first) (unary second) = true
  | 0, 0, different => absurd rfl different
  | 0, _ + 1, _ => rfl
  | _ + 1, 0, _ => rfl
  | first + 1, second + 1, different => by
      have inner : first ≠ second := fun same => different (by rw [same])
      simp [unary, clashes, clashes_unary inner]

/-- **Two literals are read as two terms that clash.** -/
theorem clashes_literal {N : Spelling} (apartN : N.Apart) {first second : String}
    (different : first ≠ second) : clashes (literal N first) (literal N second) = true := by
  unfold literal
  cases firstValue : spelledNumber first with
  | none =>
      cases secondValue : spelledNumber second with
      | none => simp [tag, clashes, apartN first second different]
      | some other =>
          simp only
          split <;> simp [numeral, numbered, tag, clashes]
  | some value =>
      cases secondValue : spelledNumber second with
      | none =>
          simp only
          split <;> simp [numeral, numbered, tag, clashes]
      | some other =>
          simp only
          by_cases sameValue : value = other
          · subst sameValue
            by_cases firstCanon : value.repr = first <;> by_cases secondCanon : value.repr = second
            · exact absurd (firstCanon.symm.trans secondCanon) different
            · rw [if_pos firstCanon, if_neg secondCanon]
              simp [numeral, numbered, tag, clashes]
            · rw [if_neg firstCanon, if_pos secondCanon]
              simp [numeral, numbered, tag, clashes]
            · rw [if_neg firstCanon, if_neg secondCanon]
              simp [numbered, tag, clashes, apartN first second different]
          · have numbers := clashes_unary sameValue
            split <;> split <;> simp [numeral, numbered, clashes, numbers]

/-- A literal clashes with every kind applied to a content, except `lit`. -/
theorem clashes_literal_tag (N : Spelling) (spelling : String) {kind : String} (content : LF.Term)
    (other : kind ≠ "lit") : clashes (literal N spelling) (tag kind content) = true := by
  unfold literal
  split
  · split <;> simp [numeral, numbered, tag, clashes]
  · simp [tag, clashes, Ne.symm other]

theorem clashes_tag_literal (N : Spelling) (spelling : String) {kind : String} (content : LF.Term)
    (other : kind ≠ "lit") : clashes (tag kind content) (literal N spelling) = true := by
  unfold literal
  split
  · split <;> simp [numeral, numbered, tag, clashes]
  · simp [tag, clashes, other]

mutual

/-- **Two patterns that are apart are read as two terms that clash.** -/
theorem clashes_pattern {N : Spelling} (apartN : N.Apart) (names others : List String) :
    ∀ (first second : EngineTerm), apart first second = true →
      clashes (pattern N names first) (pattern N others second) = true
  | .var _, _, distinct => by simp [apart] at distinct
  | .sym name, second, distinct => by
      cases second with
      | var _ => simp [apart] at distinct
      | sym other =>
          have different : name ≠ other := by simpa [apart] using distinct
          simp [pattern, tag, clashes, apartN name other different]
      | lit spelling => simpa [pattern] using clashes_tag_literal N spelling _ (by decide)
      | expr _ => simp [pattern, tag, clashes]
      | list _ => simp [pattern, tag, clashes]
  | .lit spelling, second, distinct => by
      cases second with
      | var _ => simp [apart] at distinct
      | lit other =>
          have different : spelling ≠ other := by simpa [apart] using distinct
          simpa [pattern] using clashes_literal apartN different
      | sym _ => simpa [pattern] using clashes_literal_tag N spelling _ (by decide)
      | expr _ => simpa [pattern] using clashes_literal_tag N spelling _ (by decide)
      | list _ => simpa [pattern] using clashes_literal_tag N spelling _ (by decide)
  | .expr items, second, distinct => by
      cases second with
      | var _ => simp [apart] at distinct
      | expr rest =>
          have inner := clashes_patterns apartN names others items rest
            (by simpa [apart] using distinct)
          simp [pattern, tag, clashes, inner]
      | sym _ => simp [pattern, tag, clashes]
      | lit spelling => simpa [pattern] using clashes_tag_literal N spelling _ (by decide)
      | list _ => simp [pattern, tag, clashes]
  | .list items, second, distinct => by
      cases second with
      | var _ => simp [apart] at distinct
      | list rest =>
          have inner := clashes_patterns apartN names others items rest
            (by simpa [apart] using distinct)
          simp [pattern, tag, clashes, inner]
      | sym _ => simp [pattern, tag, clashes]
      | lit spelling => simpa [pattern] using clashes_tag_literal N spelling _ (by decide)
      | expr _ => simp [pattern, tag, clashes]

theorem clashes_patterns {N : Spelling} (apartN : N.Apart) (names others : List String) :
    ∀ (first second : List EngineTerm), apartList first second = true →
      clashes (cells (patterns N names first)) (cells (patterns N others second)) = true
  | [], [], distinct => by simp [apartList] at distinct
  | [], _ :: _, _ => rfl
  | _ :: _, [], _ => rfl
  | first :: rest, second :: tail, distinct => by
      simp only [apartList, Bool.or_eq_true] at distinct
      rcases distinct with inHead | inTail
      · simp [patterns, cells, clashes, clashes_pattern apartN names others first second inHead]
      · simp [patterns, cells, clashes, clashes_patterns apartN names others rest tail inTail]

end

/-! ## The rule of an equation passes the test -/

/-- A passive term is a headed algebraic pattern. -/
theorem algebraic_passive : ∀ {term : LF.Term}, passive term = true → algebraic true term = true := by
  intro term
  induction term with
  | con name => intro _; rfl
  | app function argument ihFunction ihArgument =>
      intro isPassive
      obtain ⟨-, functionPassive, argumentPassive⟩ := passive_app.mp isPassive
      simp [algebraic, ihFunction functionPassive,
        Dedukti.algebraic_of_headed (ihArgument argumentPassive)]
  | var index => intro isPassive; simp [passive] at isPassive
  | srt sort => intro isPassive; simp [passive] at isPassive
  | pi domain body _ _ => intro isPassive; simp [passive] at isPassive
  | lam domain body _ _ => intro isPassive; simp [passive] at isPassive

/-- A passive term is quiet. -/
theorem quiet_passive : ∀ {term : LF.Term}, passive term = true → quiet term = true := by
  intro term
  induction term with
  | con name => intro _; rfl
  | app function argument ihFunction ihArgument =>
      intro isPassive
      obtain ⟨closed, functionPassive, argumentPassive⟩ := passive_app.mp isPassive
      simp [quiet, closed, ihFunction functionPassive, ihArgument argumentPassive]
  | var index => intro isPassive; simp [passive] at isPassive
  | srt sort => intro isPassive; simp [passive] at isPassive
  | pi domain body _ _ => intro isPassive; simp [passive] at isPassive
  | lam domain body _ _ => intro isPassive; simp [passive] at isPassive

theorem algebraic_cells : ∀ {items : List LF.Term}, (∀ item ∈ items, algebraic false item = true) →
    algebraic true (cells items) = true
  | [], _ => rfl
  | first :: rest, each => by
      have firstAlgebraic := each first (List.mem_cons_self ..)
      have restAlgebraic := Dedukti.algebraic_of_headed
        (algebraic_cells fun item member => each item (List.mem_cons_of_mem _ member))
      simp [cells, algebraic, firstAlgebraic, restAlgebraic]

theorem quiet_cells : ∀ {items : List LF.Term}, (∀ item ∈ items, quiet item = true) →
    quiet (cells items) = true
  | [], _ => rfl
  | first :: rest, each => by
      have firstQuiet := each first (List.mem_cons_self ..)
      have restQuiet := quiet_cells fun item member => each item (List.mem_cons_of_mem _ member)
      simp [cells, quiet, opensRedex, redexKinds, firstQuiet, restQuiet]

theorem algebraic_tag {kind : String} {content : LF.Term} (isAlgebraic : algebraic false content = true) :
    algebraic false (tag kind content) = true := by
  simp [tag, algebraic, isAlgebraic]

theorem quiet_tag {kind : String} {content : LF.Term} (isQuiet : quiet content = true) :
    quiet (tag kind content) = true := by
  simp [tag, quiet, opensRedex, isQuiet]

mutual

/-- A pattern is read as an algebraic pattern, quiet. -/
theorem pattern_shape (N : Spelling) (names : List String) :
    ∀ term : EngineTerm, algebraic false (pattern N names term) = true ∧
      quiet (pattern N names term) = true
  | .var _ => ⟨rfl, rfl⟩
  | .sym name => by
      simp only [pattern]
      exact ⟨algebraic_tag (Dedukti.algebraic_of_headed (algebraic_passive (N.quiet name))),
        quiet_tag (quiet_passive (N.quiet name))⟩
  | .lit spelling => by
      simp only [pattern]
      exact ⟨Dedukti.algebraic_of_headed (algebraic_passive (passive_literal N spelling)),
        quiet_passive (passive_literal N spelling)⟩
  | .expr items => by
      simp only [pattern]
      exact ⟨algebraic_tag (Dedukti.algebraic_of_headed
          (algebraic_cells fun item member => (patterns_shape N names items item member).1)),
        quiet_tag (quiet_cells fun item member => (patterns_shape N names items item member).2)⟩
  | .list items => by
      simp only [pattern]
      exact ⟨algebraic_tag (Dedukti.algebraic_of_headed
          (algebraic_cells fun item member => (patterns_shape N names items item member).1)),
        quiet_tag (quiet_cells fun item member => (patterns_shape N names items item member).2)⟩

theorem patterns_shape (N : Spelling) (names : List String) :
    ∀ items : List EngineTerm, ∀ item ∈ patterns N names items,
      algebraic false item = true ∧ quiet item = true
  | [] => by simp [patterns]
  | first :: rest => by
      intro item member
      simp only [patterns, List.mem_cons] at member
      rcases member with rfl | later
      · exact pattern_shape N names first
      · exact patterns_shape N names rest item later

end

/-- **The rule of an equation with distinct variables and a bound right side
passes the test of one rule.** -/
theorem storedRuleCheck_ruleOf (N : Spelling) (called : String → Bool) {equation : Equation}
    (linear : (slots equation).Nodup) (bound : boundRight equation = true) :
    storedRuleCheck (ruleOf N called equation) = true := by
  have runnable := ruleOf_runnable N called bound
  have shapes := patterns_shape N (slots equation) equation.params
  have leftAlgebraic : algebraic true (ruleOf N called equation).lhs = true := by
    have argument := Dedukti.algebraic_of_headed
      (algebraic_cells fun item member => (shapes item member).1)
    simp [ruleOf, callTerm, algebraic, argument]
  have distinct : (Dedukti.patternVars (ruleOf N called equation).lhs).Nodup := by
    rw [patternVars_ruleOf]
    exact List.Nodup.map_on (fun first member second _ same => (List.idxOf_inj member).mp same) linear
  have argumentQuiet : quiet (callArgument (ruleOf N called equation).lhs) = true :=
    quiet_cells fun item member => (shapes item member).2
  simp [storedRuleCheck, ruleOf_rewritesCall, leftAlgebraic, distinct, runnable.2, runnable.1.2,
    argumentQuiet]

/-- The left sides of the rules of two equations clash, when the equations
have two heads or left sides that are apart. -/
theorem clashes_ruleOf {N : Spelling} (apartN : N.Apart) (called other : String → Bool)
    {first second : Equation}
    (separated : first.head = second.head → apartList first.params second.params = true) :
    clashes (ruleOf N called first).lhs (ruleOf N other second).lhs = true := by
  by_cases sameHead : first.head = second.head
  · have inner := clashes_patterns apartN (slots first) (slots second) first.params second.params
      (separated sameHead)
    simp [ruleOf, callTerm, clashes, inner]
  · simp [ruleOf, callTerm, clashes, sameHead]

/-- **The rules of separated equations with distinct variables and bound right
sides are a stored table**, for a spelling that writes names apart. -/
theorem storedTable_rules (N : Spelling) (apartN : N.Apart) (called : String → Bool)
    {equations : List Equation} (linear : ∀ equation ∈ equations, (slots equation).Nodup)
    (bound : ∀ equation ∈ equations, boundRight equation = true)
    (separated : Separated equations) : StoredTable (equations.map (ruleOf N called)) where
  each := by
    intro rule member
    obtain ⟨equation, inEquations, rfl⟩ := List.mem_map.mp member
    exact storedRuleCheck_ruleOf N called (linear equation inEquations) (bound equation inEquations)
  apart := List.pairwise_map.mpr (separated.imp fun apartness => clashes_ruleOf apartN _ _ apartness)

/-- **The table of a program of the class whose equations are separated is a
stored table**, for a spelling that writes names apart. -/
theorem storedTable_programRules (N : Spelling) (apartN : N.Apart) {program : Program}
    {host : Host} {primitives : List String} (storable : Storable program host primitives)
    (separated : Separated program) : StoredTable (programRules N program primitives) :=
  storedTable_rules N apartN _ storable.leftLinear storable.bound separated

/-- **The table of a separated program of the class has an orthogonal
theory.** -/
theorem separated_orthogonal (N : Spelling) (apartN : N.Apart) {program : Program} {host : Host}
    {primitives : List String} (storable : Storable program host primitives)
    (separated : Separated program) :
    (programTheory (programRules N program primitives)).Orthogonal :=
  (storedTable_programRules N apartN storable separated).orthogonal

/-- **Nothing else is reached, from a condition on the program**: for a
program of the class that calls no primitive of its host and whose equations
are separated, every normal form that a call reaches is the datum of the value
that the engine returns for it. -/
theorem separated_normalForm_unique (N : Spelling) (apartN : N.Apart) {program : Program}
    {host : Host} (storable : Storable program host []) (separated : Separated program)
    {head : String} {arguments : List EngineTerm} {result : EngineTerm}
    (defined : program.definesAt head arguments.length = true)
    (applies : Applies program host head arguments result) {normalForm : LF.Term}
    (reaches : Reduces (programTheory (programRules N program []))
      (callTerm head (data N arguments)) normalForm)
    (normal : IsNormal (Step (programTheory (programRules N program []))) normalForm) :
    normalForm = datum N result :=
  (stores_of_storable N storable).normalForm_unique
    (separated_orthogonal N apartN storable separated) defined applies reaches normal

/-- **Positive**: the table of unary addition is orthogonal, from the
separation of its two equations. -/
theorem additionProgram_orthogonal_of_separated :
    (programTheory (programRules constantSpelling additionProgram [])).Orthogonal :=
  separated_orthogonal constantSpelling constantSpelling_apart additionProgram_storable
    additionProgram_separated

#print axioms constantSpelling_apart
#print axioms letterSpelling_apart
#print axioms clashes_literal
#print axioms clashes_pattern
#print axioms storedRuleCheck_ruleOf
#print axioms storedTable_programRules
#print axioms separated_orthogonal
#print axioms separated_normalForm_unique

end Mettapedia.Logic.HostingStyles.StoredPrograms
