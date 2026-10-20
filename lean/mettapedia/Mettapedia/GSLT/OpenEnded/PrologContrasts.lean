import Mettapedia.GSLT.OpenEnded.IdealCompletion
import Mathlib.Order.FixedPoints

/-!
# Standard Prolog semantics and alternative constructions

Each section isolates one property, names the Prolog semantics it concerns,
and proves the mathematics on both sides, with positive and negative examples.
Depth-first search in clause order, against fair schedules and depth-bounded
search, is treated in `ChaoticIteration`.

* **Negation: two-valued supported models against three-valued evidence.** The
  supported models of a normal program, the fixed points of its immediate
  consequence operator with negation read against the same set, are the
  two-valued models of Clark's completion, for which Prolog's negation as
  failure is sound (Clark 1978). The liar `p ← ¬p` has no supported model
  (`liar_no_supported_model`); the choice `p ← ¬q, q ← ¬p` has two and no least
  (`choice_no_least_supported_model`). Fitting's three-valued operator,
  relative to a declared set of complete definitions (`evidenceStep`), always
  has a least fixed point (`isLeast_leastEvidence`), and that least state is
  consistent (`leastEvidence_consistent`). In it the liar and the choice are
  unknown (`liar_unknown`, `liar_unknown_when_closed`, `choice_unknown`), definite
  consequences are established (`definite_established`), and an atom with no
  applicable rule is refuted when its definition is declared complete
  (`closed_definition_refutes`) and not otherwise
  (`open_definition_not_refuted`). With every definition declared complete this
  is the Kripke–Kleene semantics (Fitting 1985).
* **Absence at stages of an unclosed growth.** On the ideal completion of
  finite stages, the Scott-continuous observations are decided at finite
  stages (`IdealCompletion.scottContinuous_prop_factor`). Presence of a fact is
  one (`present_scottContinuous`). Absence is not monotone
  (`absent_not_monotone`), hence not Scott-continuous
  (`absent_not_scottContinuous`): the closed-world reading of absence at the
  current database, as by Prolog's negation as failure, is not monotone in the
  database. Absence becomes a finite-stage observation once a closing is
  declared. At a declared final stage it is non-membership in a finite set
  (`absent_principal_iff`). In a growth, reading absence at a stage is correct
  exactly when that stage is a closing for the fact
  (`absent_iff_notMem_iff_closingFor`, `closing_examples`).
* **Equations modulo a declared theory.** Prolog's `=/2` unifies syntactically,
  that is, modulo the empty equational theory. Under a commutative pairing, the
  syntactic solution set of an equation changes when one side is replaced by an
  equal term (`syntactic_solutions_not_invariant`); the solution set modulo
  commutativity does not (`solutionsModE_invariant`).
* **Two term models.** `X = f(X)` has no solution among finite terms
  (`no_finite_cyclic_term`) and exactly one among infinite trees
  (`cyclic_solution_in_trees`, `cyclic_solution_unique`), into which finite
  terms embed preserving `f` (`toTree_f`, `toTree_injective`). Prolog systems
  provide both models: unification without the occurs check, the default of
  SWI-Prolog's `=/2`, builds the cyclic solution, as in the rational trees of
  Prolog II (Colmerauer 1982), and `unify_with_occurs_check/2` solves among
  finite terms.

The last section is not a contrast: Prolog provides both models. Neither is the
choice between using one answer of a nondeterministic value twice and drawing
an answer at each use, which Prolog expresses as one variable in two argument
positions or as two calls; when the two readings agree is proved in
`Mettapedia.GSLT.Dynamics.DemandAgreement` (`sharedPair_eq_resampledPair_iff`,
`lazyShared_eq_resampledUses_iff`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.OpenEnded.PrologContrasts

open Set

universe u

/-! ## Negation: two-valued supported models against three-valued evidence -/

section Evidence

variable {A : Type u}

/-- A rule with a positive and a negative body. -/
structure NormalRule (A : Type u) where
  head : A
  pos : Set A
  neg : Set A

/-- The immediate consequence operator of a normal program with negation read
against the same set: a head holds when some rule's positive body holds and no
atom of its negative body does. Its fixed points are the supported models, the
two-valued models of Clark's completion. -/
def nafStep (program : Set (NormalRule A)) (S : Set A) : Set A :=
  {h | ∃ rule ∈ program, rule.head = h ∧ rule.pos ⊆ S ∧ ∀ x ∈ rule.neg, x ∉ S}

/-- Fitting's three-valued operator, relative to a declared set of complete
definitions: an atom is established by a rule whose positive body is
established and whose negative body is refuted; it is refuted only when its
definition is declared complete and every rule for it is blocked. -/
def evidenceStep (program : Set (NormalRule A)) (complete : Set A) :
    Set A × Set A →o Set A × Set A where
  toFun evidence :=
    ({h | ∃ rule ∈ program, rule.head = h ∧ rule.pos ⊆ evidence.1 ∧ rule.neg ⊆ evidence.2},
     {h | h ∈ complete ∧ ∀ rule ∈ program, rule.head = h →
        (∃ x ∈ rule.pos, x ∈ evidence.2) ∨ (∃ x ∈ rule.neg, x ∈ evidence.1)})
  monotone' evidence evidence' le := by
    refine ⟨fun h ⟨rule, member, head, pos, neg⟩ =>
      ⟨rule, member, head, pos.trans le.1, neg.trans le.2⟩, fun h ⟨inComplete, blocked⟩ =>
      ⟨inComplete, fun rule member head => ?_⟩⟩
    rcases blocked rule member head with ⟨x, inPos, against⟩ | ⟨x, inNeg, for'⟩
    · exact Or.inl ⟨x, inPos, le.2 against⟩
    · exact Or.inr ⟨x, inNeg, le.1 for'⟩

/-- The least evidence state: what is established and what is refuted. -/
def leastEvidence (program : Set (NormalRule A)) (complete : Set A) : Set A × Set A :=
  OrderHom.lfp (evidenceStep program complete)

/-- **The least evidence state always exists.** -/
theorem isLeast_leastEvidence (program : Set (NormalRule A)) (complete : Set A) :
    IsLeast {evidence | evidenceStep program complete evidence ≤ evidence}
      (leastEvidence program complete) :=
  OrderHom.isLeast_lfp_le _

theorem leastEvidence_le {program : Set (NormalRule A)} {complete : Set A}
    {evidence : Set A × Set A} (prefixed : evidenceStep program complete evidence ≤ evidence) :
    leastEvidence program complete ≤ evidence :=
  OrderHom.lfp_le _ prefixed

theorem leastEvidence_fixed (program : Set (NormalRule A)) (complete : Set A) :
    evidenceStep program complete (leastEvidence program complete) = leastEvidence program complete :=
  OrderHom.map_lfp _

/-- **The least evidence state is consistent**: nothing is both established and
refuted. Removing the overlap from a fixed point gives a prefixed point, so the
least state has no overlap. -/
theorem leastEvidence_consistent (program : Set (NormalRule A)) (complete : Set A) :
    Disjoint (leastEvidence program complete).1 (leastEvidence program complete).2 := by
  have fixed := leastEvidence_fixed program complete
  set E := leastEvidence program complete
  have below : ((E.1 \ E.2, E.2 \ E.1) : Set A × Set A) ≤ E := ⟨Set.sdiff_subset, Set.sdiff_subset⟩
  have step := (evidenceStep program complete).monotone below
  rw [fixed] at step
  have prefixed : evidenceStep program complete (E.1 \ E.2, E.2 \ E.1) ≤ (E.1 \ E.2, E.2 \ E.1) := by
    refine ⟨fun h established => ⟨step.1 established, fun refuted => ?_⟩,
      fun h refuted => ⟨step.2 refuted, fun established => ?_⟩⟩
    · obtain ⟨rule, member, head, pos, neg⟩ := established
      rw [← fixed] at refuted
      obtain ⟨_, blocked⟩ := refuted
      rcases blocked rule member head with ⟨x, inPos, against⟩ | ⟨x, inNeg, for'⟩
      · exact (pos inPos).2 against
      · exact (neg inNeg).2 for'
    · obtain ⟨_, blocked⟩ := refuted
      rw [← fixed] at established
      obtain ⟨rule, member, head, pos, neg⟩ := established
      rcases blocked rule member head with ⟨x, inPos, against⟩ | ⟨x, inNeg, for'⟩
      · exact against.2 (pos inPos)
      · exact for'.2 (neg inNeg)
  have least := leastEvidence_le prefixed
  rw [Set.disjoint_left]
  intro h established refuted
  exact (least.1 established).2 refuted

end Evidence

/-- Two atoms. -/
inductive Atom
  | p
  | q
  deriving DecidableEq

open Atom

/-- `p` if not `p`. -/
def liar : Set (NormalRule Atom) :=
  {⟨p, ∅, {p}⟩}

/-- `p` if not `q`, and `q` if not `p`. -/
def choice : Set (NormalRule Atom) :=
  {⟨p, ∅, {q}⟩, ⟨q, ∅, {p}⟩}

/-- **The liar has no supported model.** (Its clause has the classical model
`{p}`, which is not supported.) -/
theorem liar_no_supported_model (S : Set Atom) : nafStep liar S ≠ S := by
  intro fixed
  by_cases inS : p ∈ S
  · have inStep : p ∈ nafStep liar S := by rw [fixed]; exact inS
    obtain ⟨rule, member, _, _, notNeg⟩ := inStep
    obtain rfl : rule = ⟨p, ∅, {p}⟩ := member
    exact notNeg p rfl inS
  · have inStep : p ∈ nafStep liar S :=
      ⟨⟨p, ∅, {p}⟩, rfl, rfl, empty_subset S, fun x member => by
        have same : x = p := member
        exact same ▸ inS⟩
    rw [fixed] at inStep
    exact inS inStep

theorem choice_model_p : nafStep choice {p} = {p} := by
  ext h
  constructor
  · rintro ⟨rule, member, rfl, _, notNeg⟩
    rcases member with rfl | rfl
    · rfl
    · exact absurd rfl (notNeg p rfl)
  · intro member
    rw [mem_singleton_iff] at member
    subst member
    exact ⟨⟨p, ∅, {q}⟩, Or.inl rfl, rfl, empty_subset _, fun x inNeg inS => by
      rw [mem_singleton_iff] at inNeg inS
      rw [inNeg] at inS
      cases inS⟩

theorem choice_model_q : nafStep choice {q} = {q} := by
  ext h
  constructor
  · rintro ⟨rule, member, rfl, _, notNeg⟩
    rcases member with rfl | rfl
    · exact absurd rfl (notNeg q rfl)
    · rfl
  · intro member
    rw [mem_singleton_iff] at member
    subst member
    exact ⟨⟨q, ∅, {p}⟩, Or.inr rfl, rfl, empty_subset _, fun x inNeg inS => by
      rw [mem_singleton_iff] at inNeg inS
      rw [inNeg] at inS
      cases inS⟩

/-- **The choice has two supported models and no least one.** -/
theorem choice_no_least_supported_model : ¬ ∃ m, IsLeast {S | nafStep choice S = S} m := by
  rintro ⟨m, fixed, lower⟩
  have inP : m ⊆ {p} := lower choice_model_p
  have inQ : m ⊆ {q} := lower choice_model_q
  have empty : m = ∅ := by
    apply eq_empty_of_forall_notMem
    intro x member
    have one : x = p := inP member
    have two : x = q := inQ member
    rw [one] at two
    cases two
  rw [empty] at fixed
  have : p ∈ nafStep choice ∅ :=
    ⟨⟨p, ∅, {q}⟩, Or.inl rfl, rfl, empty_subset _, fun _ _ absent => absent⟩
  rw [fixed] at this
  exact this

/-- **Evidence: the liar is unknown.** -/
theorem liar_unknown : leastEvidence liar ∅ = (∅, ∅) := by
  apply le_antisymm _ bot_le
  apply leastEvidence_le
  refine ⟨?_, ?_⟩
  · rintro h ⟨rule, member, _, _, neg⟩
    obtain rfl : rule = ⟨p, ∅, {p}⟩ := member
    exact (notMem_empty p (neg (mem_singleton p))).elim
  · rintro h ⟨inComplete, _⟩
    exact inComplete

/-- **Evidence: the liar stays unknown when its definition is declared
complete.** -/
theorem liar_unknown_when_closed :
    (leastEvidence liar univ).1 = ∅ ∧ p ∉ (leastEvidence liar univ).2 := by
  have below : leastEvidence liar univ ≤ (∅, {q}) := by
    apply leastEvidence_le
    refine ⟨?_, ?_⟩
    · rintro h ⟨rule, member, _, _, neg⟩
      obtain rfl : rule = ⟨p, ∅, {p}⟩ := member
      have : p ∈ ({q} : Set Atom) := neg rfl
      cases this
    · rintro h ⟨_, blocked⟩
      cases h with
      | p =>
          rcases blocked ⟨p, ∅, {p}⟩ rfl rfl with ⟨x, absurd, _⟩ | ⟨x, _, absurd⟩
          · exact (notMem_empty x absurd).elim
          · exact (notMem_empty x absurd).elim
      | q => rfl
  refine ⟨subset_antisymm below.1 (empty_subset _), fun member => ?_⟩
  have : p ∈ ({q} : Set Atom) := below.2 member
  cases this

/-- **Evidence: the choice is unknown, with no arbitrary pick.** -/
theorem choice_unknown : leastEvidence choice univ = (∅, ∅) := by
  apply le_antisymm _ bot_le
  apply leastEvidence_le
  refine ⟨?_, ?_⟩
  · rintro h ⟨rule, member, _, _, neg⟩
    rcases member with rfl | rfl
    · exact (notMem_empty q (neg (mem_singleton q))).elim
    · exact (notMem_empty p (neg (mem_singleton p))).elim
  · rintro h ⟨_, blocked⟩
    cases h with
    | p =>
        rcases blocked ⟨p, ∅, {q}⟩ (Or.inl rfl) rfl with ⟨x, absurd, _⟩ | ⟨x, _, absurd⟩
        · exact (notMem_empty x absurd).elim
        · exact (notMem_empty x absurd).elim
    | q =>
        rcases blocked ⟨q, ∅, {p}⟩ (Or.inr rfl) rfl with ⟨x, absurd, _⟩ | ⟨x, _, absurd⟩
        · exact (notMem_empty x absurd).elim
        · exact (notMem_empty x absurd).elim

/-- `p` as a fact, and `q` from `p`. -/
def definite : Set (NormalRule Atom) :=
  {⟨p, ∅, ∅⟩, ⟨q, {p}, ∅⟩}

/-- **Evidence establishes what follows from facts.** -/
theorem definite_established :
    p ∈ (leastEvidence definite ∅).1 ∧ q ∈ (leastEvidence definite ∅).1 := by
  have fixed := leastEvidence_fixed definite ∅
  have hp : p ∈ (leastEvidence definite ∅).1 := by
    rw [← fixed]
    exact ⟨⟨p, ∅, ∅⟩, Or.inl rfl, rfl, empty_subset _, empty_subset _⟩
  refine ⟨hp, ?_⟩
  rw [← fixed]
  exact ⟨⟨q, {p}, ∅⟩, Or.inr rfl, rfl, singleton_subset_iff.mpr hp, empty_subset _⟩

/-- `p` as a fact, and no rule for `q`. -/
def onlyP : Set (NormalRule Atom) :=
  {⟨p, ∅, ∅⟩}

/-- **A declared complete definition refutes an atom without applicable
rules.** -/
theorem closed_definition_refutes : q ∈ (leastEvidence onlyP univ).2 := by
  rw [← leastEvidence_fixed onlyP univ]
  refine ⟨mem_univ q, fun rule member head => ?_⟩
  obtain rfl : rule = ⟨p, ∅, ∅⟩ := member
  cases head

/-- **Without the declaration, the same atom is not refuted.** -/
theorem open_definition_not_refuted : q ∉ (leastEvidence onlyP ∅).2 := by
  rw [← leastEvidence_fixed onlyP ∅]
  rintro ⟨absurd, _⟩
  exact absurd

/-! ## Absence at stages of an unclosed growth -/

section Absence

open Order

/-- Absence of a fact at every stage of a growth. -/
def absent (n : ℕ) (I : Ideal (Finset ℕ)) : Prop :=
  ∀ s ∈ I, n ∉ s

/-- Presence of a fact at some stage of a growth. -/
def present (n : ℕ) (I : Ideal (Finset ℕ)) : Prop :=
  ∃ s ∈ I, n ∈ s

theorem absent_iff_not_present (n : ℕ) (I : Ideal (Finset ℕ)) : absent n I ↔ ¬ present n I := by
  constructor
  · rintro absentAll ⟨s, member, inS⟩
    exact absentAll s member inS
  · intro notPresent s member inS
    exact notPresent ⟨s, member, inS⟩

/-- **Presence is a finitary observation of the growth.** -/
theorem present_scottContinuous (n : ℕ) : ScottContinuous (present n) := by
  have same : present n = IdealCompletion.extend (fun s : Finset ℕ => n ∈ s) := by
    funext I
    apply propext
    change (∃ s ∈ I, n ∈ s) ↔ sSup ((fun s : Finset ℕ => n ∈ s) '' (I : Set (Finset ℕ)))
    rw [sSup_Prop_eq]
    constructor
    · rintro ⟨s, member, inS⟩
      exact ⟨_, ⟨s, member, rfl⟩, inS⟩
    · rintro ⟨_, ⟨s, member, rfl⟩, inS⟩
      exact ⟨s, member, inS⟩
  rw [same]
  exact IdealCompletion.extend_scottContinuous fun _ _ le inS => le inS

/-- **Absence holds at a stage and fails at a larger one.** -/
theorem absent_not_monotone :
    Ideal.principal (∅ : Finset ℕ) ≤ Ideal.principal {0} ∧
      absent 0 (Ideal.principal ∅) ∧ ¬ absent 0 (Ideal.principal {0}) := by
  refine ⟨Ideal.principal_le_iff.mpr (Ideal.mem_principal.mpr (Finset.empty_subset _)), ?_, ?_⟩
  · intro s member
    have empty : s ⊆ ∅ := Ideal.mem_principal.mp member
    exact fun inS => Finset.notMem_empty 0 (empty inS)
  · intro absentEverywhere
    exact absentEverywhere {0} Ideal.mem_principal_self (Finset.mem_singleton_self 0)

/-- **On the ideal completion of finite stages, absence is not a
Scott-continuous observation.** -/
theorem absent_not_scottContinuous : ¬ ScottContinuous (absent 0) := by
  intro continuous
  obtain ⟨le, before, after⟩ := absent_not_monotone
  exact after (continuous.monotone le before)

/-- **At a declared final stage absence is non-membership in a finite set.** -/
theorem absent_principal_iff (n : ℕ) (s : Finset ℕ) : absent n (Ideal.principal s) ↔ n ∉ s := by
  constructor
  · intro absentAll
    exact absentAll s Ideal.mem_principal_self
  · intro notIn t member inT
    exact notIn (Ideal.mem_principal.mp member inT)

instance decidableAbsentPrincipal (n : ℕ) (s : Finset ℕ) :
    Decidable (absent n (Ideal.principal s)) :=
  decidable_of_iff _ (absent_principal_iff n s).symm

/-- A declared closing for a fact: a stage of the growth that decides it, so
that the fact appears in the growth only if it appears at that stage. -/
def ClosingFor (n : ℕ) (I : Ideal (Finset ℕ)) (s : Finset ℕ) : Prop :=
  s ∈ I ∧ ∀ t ∈ I, n ∈ t → n ∈ s

/-- **With a declared closing, absence in the growth is decided at the closing
stage.** -/
theorem absent_iff_of_closing {n : ℕ} {I : Ideal (Finset ℕ)} {s : Finset ℕ}
    (closing : ClosingFor n I s) : absent n I ↔ n ∉ s := by
  constructor
  · intro absentAll
    exact absentAll s closing.1
  · intro notIn t member inT
    exact notIn (closing.2 t member inT)

/-- **Reading absence at a stage is correct exactly when the stage is a closing
for the fact.** -/
theorem absent_iff_notMem_iff_closingFor {n : ℕ} {I : Ideal (Finset ℕ)} {s : Finset ℕ}
    (member : s ∈ I) : (absent n I ↔ n ∉ s) ↔ ClosingFor n I s := by
  constructor
  · intro reads
    refine ⟨member, fun t inI inT => ?_⟩
    by_contra notIn
    exact (reads.mpr notIn) t inI inT
  · exact absent_iff_of_closing

/-- In the growth with the single stage `{0}` above `∅`, the stage `{0}` is a
closing for `0` and the stage `∅` is not. -/
theorem closing_examples :
    ClosingFor 0 (Ideal.principal {0}) {0} ∧ ¬ ClosingFor 0 (Ideal.principal {0}) ∅ := by
  refine ⟨⟨Ideal.mem_principal_self, fun t member inT => Ideal.mem_principal.mp member inT⟩, ?_⟩
  rintro ⟨_, decides⟩
  exact Finset.notMem_empty 0
    (decides {0} Ideal.mem_principal_self (Finset.mem_singleton_self 0))

end Absence

/-! ## Equations modulo a declared theory -/

/-- Terms with two constants, one metavariable and a pairing. -/
inductive PairTerm
  | a
  | b
  | var
  | pair (left right : PairTerm)

/-- Substituting a term for the metavariable. -/
def PairTerm.subst : PairTerm → PairTerm → PairTerm
  | .var, value => value
  | .pair left right, value => .pair (left.subst value) (right.subst value)
  | .a, _ => .a
  | .b, _ => .b

/-- Equality modulo commutativity of the pairing. -/
inductive CommEq : PairTerm → PairTerm → Prop
  | refl (t : PairTerm) : CommEq t t
  | symm {t u : PairTerm} : CommEq t u → CommEq u t
  | trans {t u v : PairTerm} : CommEq t u → CommEq u v → CommEq t v
  | comm (left right : PairTerm) : CommEq (.pair left right) (.pair right left)
  | congr {left left' right right' : PairTerm} :
      CommEq left left' → CommEq right right' → CommEq (.pair left right) (.pair left' right')

theorem CommEq.subst_stable {t u : PairTerm} (equal : CommEq t u) (value : PairTerm) :
    CommEq (t.subst value) (u.subst value) := by
  induction equal with
  | refl t => exact .refl _
  | symm _ ih => exact .symm ih
  | trans _ _ ihFirst ihSecond => exact .trans ihFirst ihSecond
  | comm left right =>
      change CommEq (.pair (left.subst value) (right.subst value))
        (.pair (right.subst value) (left.subst value))
      exact .comm _ _
  | @congr left left' right right' _ _ ihLeft ihRight =>
      change CommEq (.pair (left.subst value) (right.subst value))
        (.pair (left'.subst value) (right'.subst value))
      exact .congr ihLeft ihRight

/-- The values of the metavariable making two terms syntactically equal. -/
def syntacticSolutions (left right : PairTerm) : Set PairTerm :=
  {value | left.subst value = right.subst value}

/-- The values of the metavariable making two terms equal modulo
commutativity. -/
def solutionsModE (left right : PairTerm) : Set PairTerm :=
  {value | CommEq (left.subst value) (right.subst value)}

/-- **Solutions modulo the equations do not depend on the presentation of a
side.** -/
theorem solutionsModE_invariant {left left' right : PairTerm} (equal : CommEq left left') :
    solutionsModE left right = solutionsModE left' right := by
  ext value
  constructor
  · intro solves
    exact .trans (.symm (equal.subst_stable value)) solves
  · intro solves
    exact .trans (equal.subst_stable value) solves

/-- **Syntactic solutions do.** `(a, b)` and `(b, a)` are equal modulo
commutativity; unifying the first with `(b, X)` has no syntactic solution,
unifying the second has one, and modulo commutativity the first has it too. -/
theorem syntactic_solutions_not_invariant :
    CommEq (.pair .a .b) (.pair .b .a) ∧
      syntacticSolutions (.pair .a .b) (.pair .b .var) = ∅ ∧
      PairTerm.a ∈ syntacticSolutions (.pair .b .a) (.pair .b .var) ∧
      PairTerm.a ∈ solutionsModE (.pair .a .b) (.pair .b .var) := by
  refine ⟨.comm _ _, ?_, show PairTerm.subst (.pair .b .a) .a = PairTerm.subst (.pair .b .var) .a from rfl,
    show CommEq (PairTerm.pair .a .b) (PairTerm.pair .b .a) from .comm _ _⟩
  apply eq_empty_of_forall_notMem
  intro value solves
  change PairTerm.pair .a .b = PairTerm.pair .b value at solves
  cases solves

/-! ## Two term models: finite terms and infinite trees -/

/-- Finite first-order terms with one unary symbol. -/
inductive FiniteTerm
  | var (n : ℕ)
  | const
  | f (t : FiniteTerm)

/-- **`X = f(X)` has no solution among finite terms.** -/
theorem no_finite_cyclic_term (t : FiniteTerm) : t ≠ .f t := by
  induction t with
  | var n => exact fun same => by cases same
  | const => exact fun same => by cases same
  | f t ih => exact fun same => ih (FiniteTerm.f.inj same)

/-- Labels of possibly infinite unary trees, read from the root. -/
inductive Label
  | var (n : ℕ)
  | const
  | fsym

/-- Applying `f` to a possibly infinite tree. -/
def consF (tree : ℕ → Label) : ℕ → Label
  | 0 => .fsym
  | n + 1 => tree n

/-- Finite terms as trees: the leaf label repeats below the leaf. -/
def toTree : FiniteTerm → ℕ → Label
  | .var n => fun _ => .var n
  | .const => fun _ => .const
  | .f t => consF (toTree t)

/-- The embedding preserves `f`. -/
theorem toTree_f (t : FiniteTerm) : toTree (.f t) = consF (toTree t) :=
  rfl

theorem toTree_injective : Function.Injective toTree := by
  intro t
  induction t with
  | var n =>
      intro t' same
      cases t' with
      | var m => have := congrFun same 0; cases this; rfl
      | const => have := congrFun same 0; cases this
      | f t' => have := congrFun same 0; cases this
  | const =>
      intro t' same
      cases t' with
      | var m => have := congrFun same 0; cases this
      | const => rfl
      | f t' => have := congrFun same 0; cases this
  | f t ih =>
      intro t' same
      cases t' with
      | var m => have := congrFun same 0; cases this
      | const => have := congrFun same 0; cases this
      | f t' =>
          have tails : toTree t = toTree t' := funext fun n => congrFun same (n + 1)
          rw [ih tails]

/-- **Among infinite trees `X = f(X)` has a solution, which is no finite
term.** -/
theorem cyclic_solution_in_trees : ∃ tree : ℕ → Label, consF tree = tree ∧ tree ∉ range toTree := by
  refine ⟨fun _ => .fsym, funext fun n => by cases n <;> rfl, ?_⟩
  rintro ⟨t, same⟩
  have cyclic : toTree (.f t) = toTree t := by
    rw [toTree_f, same]
    funext n
    cases n <;> rfl
  exact no_finite_cyclic_term t (toTree_injective cyclic).symm

/-- **Among infinite trees the solution of `X = f(X)` is unique.** -/
theorem cyclic_solution_unique {tree : ℕ → Label} (solves : consF tree = tree) :
    tree = fun _ => .fsym := by
  funext n
  induction n with
  | zero =>
      rw [← solves]
      rfl
  | succ n ih =>
      rw [← solves]
      exact ih

#print axioms liar_no_supported_model
#print axioms choice_no_least_supported_model
#print axioms isLeast_leastEvidence
#print axioms leastEvidence_consistent
#print axioms liar_unknown
#print axioms liar_unknown_when_closed
#print axioms choice_unknown
#print axioms definite_established
#print axioms closed_definition_refutes
#print axioms open_definition_not_refuted
#print axioms present_scottContinuous
#print axioms absent_not_monotone
#print axioms absent_not_scottContinuous
#print axioms absent_principal_iff
#print axioms absent_iff_of_closing
#print axioms absent_iff_notMem_iff_closingFor
#print axioms closing_examples
#print axioms solutionsModE_invariant
#print axioms syntactic_solutions_not_invariant
#print axioms no_finite_cyclic_term
#print axioms toTree_injective
#print axioms cyclic_solution_in_trees
#print axioms cyclic_solution_unique

end Mettapedia.GSLT.OpenEnded.PrologContrasts
