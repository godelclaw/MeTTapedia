import Mettapedia.OSLF.Framework.SortedInstrumentCongruenceSystem
import Mathlib.Data.Set.Finite.Basic

/-!
# The structural-modal logic of an instrument kit, and its adequacy

Formulas are sorted. They have arbitrary conjunction, negation, the authored
observations, a diamond for each authored label and target sort, and one
structural connective per constructor. A term satisfies the connective for
`c` when it is equal, in the equation theory, to `c` applied to terms
satisfying the argument formulas. Satisfaction is defined on terms alone;
it mentions no instrument and no bundle.

A policy admits the structural connectives of its constructors. Two
fragments are treated together: all admitted formulas, and the admitted
formulas whose conjunctions are finite.

Proved here, for every congruence and every authored system:

* satisfaction cannot separate equal terms;
* the characteristic formula of a term, built from its own constructors and
  nothing else, holds of exactly the terms equal to it; so the structural
  connectives alone separate equation classes, and the connectives of a
  policy separate a supported term from every other class;
* for every policy, two terms are bisimilar in the instrument system exactly
  when they satisfy the same admitted formulas;
* the same holds for finite conjunctions when each authored label has
  finitely many successors, and each admitted constructor finitely many
  decompositions, up to the equations.

The third statement is the partial characterization for every observation
signature: the structural connective for `c` reads an `ask c` step followed
by one `get c i` step per position. With nothing admitted it is the
Hennessy-Milner theorem for the authored system, which is why some
conjunction or branching hypothesis is unavoidable there. On supported
terms the structural connectives suffice without conjunction, negation or
any branching hypothesis.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SortedInstrumentCongruence

open Mettapedia.GSLT
open Mettapedia.OSLF.SortedConstructors

universe u v uAtom uLabel

variable {signature : Signature.{u,v}}

/-- Sorted structural-modal formulas. Conjunctions are indexed by any type
at the level of the terms. -/
inductive Formula (signature : Signature.{u,v}) (Atom : Type uAtom) (Proper : Type uLabel) :
    signature.Srt → Type (max (max u v + 1) uAtom uLabel) where
  | conj {sort : signature.Srt} {Index : Type (max u v)}
      (parts : Index → Formula signature Atom Proper sort) : Formula signature Atom Proper sort
  | neg {sort : signature.Srt} (inner : Formula signature Atom Proper sort) :
      Formula signature Atom Proper sort
  | atom {sort : signature.Srt} (observation : Atom) : Formula signature Atom Proper sort
  | proper {sort : signature.Srt} (label : Proper) (next : signature.Srt)
      (inner : Formula signature Atom Proper next) : Formula signature Atom Proper sort
  | node (constructor : signature.Constructor)
      (arguments : (position : Fin (signature.arity constructor)) →
        Formula signature Atom Proper (signature.input constructor position)) :
      Formula signature Atom Proper (signature.output constructor)

namespace Formula

variable {Atom : Type uAtom} {Proper : Type uLabel}

/-- The empty conjunction. -/
def top {sort : signature.Srt} : Formula signature Atom Proper sort :=
  .conj (Index := PEmpty.{max u v + 1}) (fun index => index.elim)

/-- Every structural connective belongs to an admitted constructor. -/
def Allowed (opened : signature.Constructor → Prop) :
    {sort : signature.Srt} → Formula signature Atom Proper sort → Prop
  | _, .conj parts => ∀ index, Allowed opened (parts index)
  | _, .neg inner => Allowed opened inner
  | _, .atom _ => True
  | _, .proper _ _ inner => Allowed opened inner
  | _, .node constructor arguments =>
      opened constructor ∧ ∀ position, Allowed opened (arguments position)

/-- Every conjunction is finite. -/
def Finitary : {sort : signature.Srt} → Formula signature Atom Proper sort → Prop
  | _, .conj (Index := Index) parts => Finite Index ∧ ∀ index, Finitary (parts index)
  | _, .neg inner => Finitary inner
  | _, .atom _ => True
  | _, .proper _ _ inner => Finitary inner
  | _, .node _ arguments => ∀ position, Finitary (arguments position)

/-- Built from structural connectives alone. -/
def Structural : {sort : signature.Srt} → Formula signature Atom Proper sort → Prop
  | _, .conj _ => False
  | _, .neg _ => False
  | _, .atom _ => False
  | _, .proper _ _ _ => False
  | _, .node _ arguments => ∀ position, Structural (arguments position)

theorem Allowed.mono {smaller larger : signature.Constructor → Prop}
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    {sort : signature.Srt} {formula : Formula signature Atom Proper sort}
    (allowed : formula.Allowed smaller) : formula.Allowed larger := by
  induction formula with
  | conj parts inductionHypothesis => exact fun index => inductionHypothesis index (allowed index)
  | neg inner inductionHypothesis => exact inductionHypothesis allowed
  | atom observation => exact trivial
  | proper label next inner inductionHypothesis => exact inductionHypothesis allowed
  | node constructor arguments inductionHypothesis =>
    exact ⟨inclusion constructor allowed.1,
      fun position => inductionHypothesis position (allowed.2 position)⟩

end Formula

variable {E : Congruence signature}

/-- Satisfaction by a closed term. The structural connective quantifies over
every decomposition the equation theory provides. -/
def Holds (base : BaseSystem.{u,v,uAtom,uLabel} E) :
    {sort : signature.Srt} → Formula signature base.Atom base.Label sort →
      Term signature sort → Prop
  | _, .conj parts, term => ∀ index, Holds base (parts index) term
  | _, .neg inner, term => ¬ Holds base inner term
  | _, .atom observation, term => base.observes observation term
  | _, .proper label next inner, term =>
      ∃ target : Term signature next, base.act label term target ∧ Holds base inner target
  | _, .node constructor arguments, term =>
      ∃ children : (position : Fin (signature.arity constructor)) →
          Term signature (signature.input constructor position),
        E.Rel term (Term.node constructor children) ∧
          ∀ position, Holds base (arguments position) (children position)

variable (base : BaseSystem.{u,v,uAtom,uLabel} E)

theorem holds_top {sort : signature.Srt} (term : Term signature sort) :
    Holds base (Formula.top : Formula signature base.Atom base.Label sort) term :=
  fun index => index.elim

/-- **Satisfaction respects the equations.** -/
theorem holds_resp {sort : signature.Srt} (formula : Formula signature base.Atom base.Label sort) :
    ∀ {left right : Term signature sort}, E.Rel left right →
      (Holds base formula left ↔ Holds base formula right) := by
  induction formula with
  | conj parts inductionHypothesis =>
    intro left right equation
    exact forall_congr' (fun index => inductionHypothesis index equation)
  | neg inner inductionHypothesis =>
    intro left right equation
    exact not_congr (inductionHypothesis equation)
  | atom observation =>
    intro left right equation
    exact base.observes_resp observation equation
  | proper label next inner inductionHypothesis =>
    intro left right equation
    constructor
    · rintro ⟨target, authored, satisfied⟩
      obtain ⟨target', authored', related⟩ := base.act_resp_left equation authored
      exact ⟨target', authored', (inductionHypothesis related).mp satisfied⟩
    · rintro ⟨target, authored, satisfied⟩
      obtain ⟨target', authored', related⟩ := base.act_resp_left (E.symm equation) authored
      exact ⟨target', authored', (inductionHypothesis related).mp satisfied⟩
  | node constructor arguments _ =>
    intro left right equation
    constructor
    · rintro ⟨children, decomposition, satisfied⟩
      exact ⟨children, E.trans (E.symm equation) decomposition, satisfied⟩
    · rintro ⟨children, decomposition, satisfied⟩
      exact ⟨children, E.trans equation decomposition, satisfied⟩

/-! ## Characteristic formulas -/

/-- The formula read off a term's own constructors. -/
def characteristic {Atom : Type uAtom} {Proper : Type uLabel} :
    {sort : signature.Srt} → Term signature sort → Formula signature Atom Proper sort
  | _, .node constructor arguments =>
      .node constructor (fun position => characteristic (arguments position))

theorem characteristic_structural {Atom : Type uAtom} {Proper : Type uLabel}
    {sort : signature.Srt} (term : Term signature sort) :
    (characteristic term : Formula signature Atom Proper sort).Structural := by
  induction term with
  | node constructor arguments inductionHypothesis => exact inductionHypothesis

theorem characteristic_finitary {Atom : Type uAtom} {Proper : Type uLabel}
    {sort : signature.Srt} (term : Term signature sort) :
    (characteristic term : Formula signature Atom Proper sort).Finitary := by
  induction term with
  | node constructor arguments inductionHypothesis => exact inductionHypothesis

theorem characteristic_allowed_iff {Atom : Type uAtom} {Proper : Type uLabel}
    (opened : signature.Constructor → Prop) {sort : signature.Srt} (term : Term signature sort) :
    (characteristic term : Formula signature Atom Proper sort).Allowed opened ↔
      Supported opened term := by
  induction term with
  | node constructor arguments inductionHypothesis =>
    exact and_congr Iff.rfl (forall_congr' inductionHypothesis)

/-- A term satisfies another's characteristic formula exactly when the two
are equal in the equation theory. -/
theorem holds_characteristic_iff {sort : signature.Srt} (term : Term signature sort) :
    ∀ other : Term signature sort,
      Holds base (characteristic term) other ↔ E.Rel other term := by
  induction term with
  | node constructor arguments inductionHypothesis =>
    intro other
    constructor
    · rintro ⟨children, decomposition, satisfied⟩
      exact E.trans decomposition (E.node constructor
        (fun position => (inductionHypothesis position _).mp (satisfied position)))
    · intro equation
      exact ⟨arguments, equation,
        fun position => (inductionHypothesis position _).mpr (E.refl _)⟩

/-- **Structural separation.** Two closed terms are equal in the equation
theory exactly when every purely structural formula true of the first is
true of the second. No condition is imposed on the equation theory. -/
theorem rel_iff_structural {sort : signature.Srt} (left right : Term signature sort) :
    E.Rel left right ↔
      ∀ formula : Formula signature base.Atom base.Label sort, formula.Structural →
        Holds base formula left → Holds base formula right := by
  constructor
  · intro equation formula _ satisfied
    exact (holds_resp base formula equation).mp satisfied
  · intro transfer
    have own : Holds base (characteristic left) left :=
      (holds_characteristic_iff base left left).mpr (E.refl left)
    exact E.symm ((holds_characteristic_iff base left right).mp
      (transfer _ (characteristic_structural left) own))

/-- **Structural separation on the supported part.** The structural
connectives of a policy separate a supported term from every other class. -/
theorem rel_iff_structural_of_supported {opened : signature.Constructor → Prop}
    {sort : signature.Srt} {left : Term signature sort} (supported : Supported opened left)
    (right : Term signature sort) :
    E.Rel left right ↔
      ∀ formula : Formula signature base.Atom base.Label sort, formula.Structural →
        formula.Allowed opened → Holds base formula left → Holds base formula right := by
  constructor
  · intro equation formula _ _ satisfied
    exact (holds_resp base formula equation).mp satisfied
  · intro transfer
    have own : Holds base (characteristic left) left :=
      (holds_characteristic_iff base left left).mpr (E.refl left)
    exact E.symm ((holds_characteristic_iff base left right).mp
      (transfer _ (characteristic_structural left)
        ((characteristic_allowed_iff opened left).mpr supported) own))

/-! ## Soundness: bisimilar terms satisfy the same admitted formulas -/

variable {base} {opened : signature.Constructor → Prop}

theorem holds_iff_of_related {relation : State signature → State signature → Prop}
    (bisimulation : (system base opened).IsBisimulation relation)
    {sort : signature.Srt} (formula : Formula signature base.Atom base.Label sort) :
    formula.Allowed opened → ∀ left right : Term signature sort,
      relation (.term left) (.term right) →
        (Holds base formula left ↔ Holds base formula right) := by
  have forward := bisimulation.1
  have backward := bisimulation.2.1
  have atoms := bisimulation.2.2
  induction formula with
  | conj parts inductionHypothesis =>
    intro allowed left right related
    exact forall_congr' (fun index => inductionHypothesis index (allowed index) left right related)
  | neg inner inductionHypothesis =>
    intro allowed left right related
    exact not_congr (inductionHypothesis allowed left right related)
  | atom observation =>
    intro _ left right related
    exact atoms related (Sum.inr observation)
  | proper label next inner inductionHypothesis =>
    intro allowed left right related
    constructor
    · rintro ⟨target, authored, satisfied⟩
      obtain ⟨matched, step, nextRelated⟩ :=
        forward related (Label.proper label) (Act.proper authored)
      obtain ⟨first, second, start, reached, sourceShape, rfl, authored'⟩ := Act.proper_inv step
      cases sourceShape
      have sorts : next = second := sort_eq_of_related bisimulation nextRelated
      subst sorts
      exact ⟨reached, authored', (inductionHypothesis allowed _ _ nextRelated).mp satisfied⟩
    · rintro ⟨target, authored, satisfied⟩
      obtain ⟨matched, step, nextRelated⟩ :=
        backward related (Label.proper label) (Act.proper authored)
      obtain ⟨first, second, start, reached, sourceShape, rfl, authored'⟩ := Act.proper_inv step
      cases sourceShape
      have sorts : second = next := sort_eq_of_related bisimulation nextRelated
      subst sorts
      exact ⟨reached, authored', (inductionHypothesis allowed _ _ nextRelated).mpr satisfied⟩
  | node constructor arguments inductionHypothesis =>
    intro allowed left right related
    constructor
    · rintro ⟨children, decomposition, satisfied⟩
      obtain ⟨matched, step, bundlesRelated⟩ :=
        forward related (Label.ask constructor) (Act.ask constructor allowed.1 decomposition)
      obtain ⟨-, value, others, sourceShape, rfl, decomposition'⟩ := Act.ask_inv step
      have valueEq : right = value := State.term_injective sourceShape
      subst valueEq
      refine ⟨others, decomposition', fun position => ?_⟩
      obtain ⟨projected, projectedStep, childRelated⟩ :=
        forward bundlesRelated (Label.get constructor position)
          (Act.get constructor allowed.1 position (E.refl _))
      obtain ⟨-, compared, target, bundleShape, rfl, projection⟩ := Act.get_inv projectedStep
      have comparedEq : others = compared := State.bundle_injective bundleShape
      subst comparedEq
      exact (holds_resp base (arguments position) projection).mpr
        ((inductionHypothesis position (allowed.2 position) _ _ childRelated).mp
          (satisfied position))
    · rintro ⟨children, decomposition, satisfied⟩
      obtain ⟨matched, step, bundlesRelated⟩ :=
        backward related (Label.ask constructor) (Act.ask constructor allowed.1 decomposition)
      obtain ⟨-, value, others, sourceShape, rfl, decomposition'⟩ := Act.ask_inv step
      have valueEq : left = value := State.term_injective sourceShape
      subst valueEq
      refine ⟨others, decomposition', fun position => ?_⟩
      obtain ⟨projected, projectedStep, childRelated⟩ :=
        backward bundlesRelated (Label.get constructor position)
          (Act.get constructor allowed.1 position (E.refl _))
      obtain ⟨-, compared, target, bundleShape, rfl, projection⟩ := Act.get_inv projectedStep
      have comparedEq : others = compared := State.bundle_injective bundleShape
      subst comparedEq
      exact (holds_resp base (arguments position) projection).mpr
        ((inductionHypothesis position (allowed.2 position) _ _ childRelated).mpr
          (satisfied position))

/-! ## Fragments large enough for their branching -/

variable (base opened)

/-- A class of admitted formulas closed under the connectives, together with
covers of every successor set and every decomposition set over which it can
form a conjunction. -/
structure Fragment where
  Admits : {sort : signature.Srt} → Formula signature base.Atom base.Label sort → Prop
  allowed : ∀ {sort : signature.Srt} {formula : Formula signature base.Atom base.Label sort},
    Admits formula → formula.Allowed opened
  top : ∀ sort : signature.Srt,
    Admits (Formula.top : Formula signature base.Atom base.Label sort)
  neg : ∀ {sort : signature.Srt} {formula : Formula signature base.Atom base.Label sort},
    Admits formula → Admits (Formula.neg formula)
  atom : ∀ (sort : signature.Srt) (observation : base.Atom),
    Admits (Formula.atom observation : Formula signature base.Atom base.Label sort)
  proper : ∀ {sort : signature.Srt} (label : base.Label) (next : signature.Srt)
    {inner : Formula signature base.Atom base.Label next},
    Admits inner →
      Admits (Formula.proper label next inner : Formula signature base.Atom base.Label sort)
  node : ∀ (constructor : signature.Constructor), opened constructor →
    ∀ {arguments : (position : Fin (signature.arity constructor)) →
      Formula signature base.Atom base.Label (signature.input constructor position)},
    (∀ position, Admits (arguments position)) → Admits (Formula.node constructor arguments)
  properCover : ∀ (label : base.Label) {source : signature.Srt} (start : Term signature source)
    (target : signature.Srt),
    ∃ cover : Set (Term signature target),
      (∀ next : Term signature target, base.act label start next →
        ∃ representative ∈ cover, E.Rel next representative) ∧
      ∀ {sort : signature.Srt} (parts : cover → Formula signature base.Atom base.Label sort),
        (∀ index, Admits (parts index)) → Admits (Formula.conj parts)
  decompositionCover : ∀ (constructor : signature.Constructor), opened constructor →
    ∀ whole : Term signature (signature.output constructor),
    ∃ cover : Set ((position : Fin (signature.arity constructor)) →
        Term signature (signature.input constructor position)),
      (∀ children, E.Rel whole (Term.node constructor children) →
        ∃ representative ∈ cover, ∀ position, E.Rel (children position) (representative position)) ∧
      ∀ {sort : signature.Srt} (parts : cover → Formula signature base.Atom base.Label sort),
        (∀ index, Admits (parts index)) → Admits (Formula.conj parts)

namespace Fragment

variable {base opened} (fragment : Fragment base opened)

/-- The same admitted formulas hold. -/
def Equivalent {sort : signature.Srt} (left right : Term signature sort) : Prop :=
  ∀ formula : Formula signature base.Atom base.Label sort, fragment.Admits formula →
    (Holds base formula left ↔ Holds base formula right)

theorem equivalent_symm {sort : signature.Srt} {left right : Term signature sort}
    (equivalent : fragment.Equivalent left right) : fragment.Equivalent right left :=
  fun formula admitted => (equivalent formula admitted).symm

theorem equivalent_trans {sort : signature.Srt} {left middle right : Term signature sort}
    (first : fragment.Equivalent left middle) (second : fragment.Equivalent middle right) :
    fragment.Equivalent left right :=
  fun formula admitted => (first formula admitted).trans (second formula admitted)

theorem equivalent_of_rel {sort : signature.Srt} {left right : Term signature sort}
    (equation : E.Rel left right) : fragment.Equivalent left right :=
  fun formula _ => holds_resp base formula equation

/-- Inequivalent terms have an admitted formula true of the first only. -/
theorem exists_separator {sort : signature.Srt} {left right : Term signature sort}
    (distinct : ¬ fragment.Equivalent left right) :
    ∃ formula : Formula signature base.Atom base.Label sort,
      fragment.Admits formula ∧ Holds base formula left ∧ ¬ Holds base formula right := by
  classical
  by_contra none
  apply distinct
  intro formula admitted
  constructor
  · intro leftHolds
    by_contra rightFails
    exact none ⟨formula, admitted, leftHolds, rightFails⟩
  · intro rightHolds
    by_contra leftFails
    exact none ⟨Formula.neg formula, fragment.neg admitted, leftFails,
      fun rightFails => rightFails rightHolds⟩

open Classical in
/-- A formula true of the first term, and false of the second whenever the
fragment tells them apart. -/
noncomputable def separator {sort : signature.Srt} (left right : Term signature sort) :
    Formula signature base.Atom base.Label sort :=
  if distinct : fragment.Equivalent left right then Formula.top
  else Classical.choose (fragment.exists_separator distinct)

theorem separator_admits {sort : signature.Srt} (left right : Term signature sort) :
    fragment.Admits (fragment.separator left right) := by
  classical
  unfold separator
  split
  · exact fragment.top sort
  · rename_i distinct
    exact (Classical.choose_spec (fragment.exists_separator distinct)).1

theorem separator_holds {sort : signature.Srt} (left right : Term signature sort) :
    Holds base (fragment.separator left right) left := by
  classical
  unfold separator
  split
  · exact holds_top base left
  · rename_i distinct
    exact (Classical.choose_spec (fragment.exists_separator distinct)).2.1

theorem separator_fails {sort : signature.Srt} {left right : Term signature sort}
    (distinct : ¬ fragment.Equivalent left right) :
    ¬ Holds base (fragment.separator left right) right := by
  classical
  unfold separator
  rw [dif_neg distinct]
  exact (Classical.choose_spec (fragment.exists_separator distinct)).2.2

/-- Equivalence in the fragment, read on states. Bundles are compared
componentwise and as rebuilt terms. -/
inductive Related : State signature → State signature → Prop where
  | term {sort : signature.Srt} {left right : Term signature sort} :
      fragment.Equivalent left right → Related (.term left) (.term right)
  | bundle (constructor : signature.Constructor)
      {left right : (position : Fin (signature.arity constructor)) →
        Term signature (signature.input constructor position)} :
      (∀ position, fragment.Equivalent (left position) (right position)) →
      fragment.Equivalent (Term.node constructor left) (Term.node constructor right) →
        Related (.bundle constructor left) (.bundle constructor right)

theorem related_symm {left right : State signature} (related : fragment.Related left right) :
    fragment.Related right left := by
  cases related with
  | term equivalent => exact .term (fragment.equivalent_symm equivalent)
  | bundle constructor children whole =>
    exact .bundle constructor (fun position => fragment.equivalent_symm (children position))
      (fragment.equivalent_symm whole)

/-- Every step of one state is matched by the other. A missing match would
give, over the cover, a conjunction of separators that the two terms
disagree on. -/
theorem related_forward {left right : State signature} (related : fragment.Related left right)
    {label : Label signature base.Label} {left' : State signature}
    (step : Act base opened label left left') :
    ∃ right', Act base opened label right right' ∧ fragment.Related left' right' := by
  classical
  cases related with
  | @term sort first second equivalent =>
    cases step with
    | @proper label _ target _ next authored =>
      suffices matching : ∃ next' : Term signature target,
          base.act label second next' ∧ fragment.Equivalent next next' by
        obtain ⟨next', authored', equivalent'⟩ := matching
        exact ⟨.term next', .proper authored', .term equivalent'⟩
      by_contra absent
      obtain ⟨cover, covers, closed⟩ := fragment.properCover label second target
      let parts : cover → Formula signature base.Atom base.Label target :=
        fun representative => fragment.separator next representative.1
      have admitted : fragment.Admits (Formula.proper (sort := sort) label target
          (Formula.conj parts)) :=
        fragment.proper label target
          (closed parts (fun representative => fragment.separator_admits next representative.1))
      have firstHolds : Holds base (Formula.proper (sort := sort) label target
          (Formula.conj parts)) first :=
        ⟨next, authored, fun representative => fragment.separator_holds next representative.1⟩
      obtain ⟨reached, authored', satisfied⟩ := (equivalent _ admitted).mp firstHolds
      obtain ⟨representative, member, close⟩ := covers reached authored'
      have distinct : ¬ fragment.Equivalent next representative := fun equivalent' =>
        absent ⟨representative, base.act_resp_right authored' close, equivalent'⟩
      have transported : Holds base (fragment.separator next representative) representative :=
        (holds_resp base _ close).mp (satisfied ⟨representative, member⟩)
      exact fragment.separator_fails distinct transported
    | @ask constructor permission source arguments decomposition =>
      suffices matching : ∃ others : (position : Fin (signature.arity constructor)) →
            Term signature (signature.input constructor position),
          E.Rel second (Term.node constructor others) ∧
            ∀ position, fragment.Equivalent (arguments position) (others position) by
        obtain ⟨others, decomposition', children⟩ := matching
        refine ⟨.bundle constructor others, .ask constructor permission decomposition',
          .bundle constructor children ?_⟩
        exact fragment.equivalent_trans (fragment.equivalent_of_rel (E.symm decomposition))
          (fragment.equivalent_trans equivalent (fragment.equivalent_of_rel decomposition'))
      by_contra absent
      obtain ⟨cover, covers, closed⟩ := fragment.decompositionCover constructor permission second
      let parts : (position : Fin (signature.arity constructor)) → cover →
          Formula signature base.Atom base.Label (signature.input constructor position) :=
        fun position representative =>
          fragment.separator (arguments position) (representative.1 position)
      have admitted : fragment.Admits
          (Formula.node constructor (fun position => Formula.conj (parts position))) :=
        fragment.node constructor permission (fun position => closed (parts position)
          (fun representative =>
            fragment.separator_admits (arguments position) (representative.1 position)))
      have firstHolds : Holds base
          (Formula.node constructor (fun position => Formula.conj (parts position))) source :=
        ⟨arguments, decomposition, fun position representative =>
          fragment.separator_holds (arguments position) (representative.1 position)⟩
      obtain ⟨others, decomposition', satisfied⟩ := (equivalent _ admitted).mp firstHolds
      obtain ⟨representative, member, close⟩ := covers others decomposition'
      obtain ⟨position, distinct⟩ := not_forall.mp (fun children =>
        absent ⟨representative, E.trans decomposition' (E.node constructor close), children⟩)
      have transported : Holds base
          (fragment.separator (arguments position) (representative position))
          (representative position) :=
        (holds_resp base _ (close position)).mp (satisfied position ⟨representative, member⟩)
      exact fragment.separator_fails distinct transported
  | @bundle constructor first second children whole =>
    cases step with
    | get _ permission position projection =>
      exact ⟨.term (second position), .get constructor permission position (E.refl _),
        .term (fragment.equivalent_trans (fragment.equivalent_of_rel (E.symm projection))
          (children position))⟩
    | build _ permission rebuilt =>
      exact ⟨.term (Term.node constructor second), .build constructor permission (E.refl _),
        .term (fragment.equivalent_trans (fragment.equivalent_of_rel (E.symm rebuilt)) whole)⟩

/-- Equivalence in the fragment is a bisimulation of the instrument system. -/
theorem related_isBisimulation : (system base opened).IsBisimulation fragment.Related := by
  refine ⟨?_, ?_, ?_⟩
  · intro left right related label left' step
    exact fragment.related_forward related step
  · intro left right related label right' step
    obtain ⟨left', step', related'⟩ :=
      fragment.related_forward (fragment.related_symm related) step
    exact ⟨left', step', fragment.related_symm related'⟩
  · intro left right related atom
    cases related with
    | @term sort first second equivalent =>
      cases atom with
      | inl tag => exact Iff.rfl
      | inr observation => exact equivalent _ (fragment.atom sort observation)
    | bundle constructor children whole => exact Iff.rfl

/-- **Adequacy of a fragment.** Two terms satisfy the same formulas of the
fragment exactly when they are bisimilar in the instrument system. -/
theorem equivalent_iff_bisimilar {sort : signature.Srt} (left right : Term signature sort) :
    fragment.Equivalent left right ↔ Bisimilar base opened (.term left) (.term right) := by
  constructor
  · intro equivalent
    exact ⟨fragment.Related, fragment.related_isBisimulation, .term equivalent⟩
  · rintro ⟨relation, bisimulation, related⟩ formula admitted
    exact holds_iff_of_related bisimulation formula (fragment.allowed admitted) left right related

end Fragment

/-! ## The two fragments -/

/-- Every admitted formula, with arbitrary conjunction. It needs no
branching hypothesis: each cover is the whole set. -/
def Fragment.all : Fragment base opened where
  Admits formula := formula.Allowed opened
  allowed admitted := admitted
  top _ := fun index => index.elim
  neg admitted := admitted
  atom _ _ := trivial
  proper := by
    intro sort label next inner admitted
    exact admitted
  node := by
    intro constructor permission arguments admitted
    exact ⟨permission, admitted⟩
  properCover _ _ _ _ :=
    ⟨Set.univ, fun next _ => ⟨next, trivial, E.refl next⟩, fun _ admitted => admitted⟩
  decompositionCover _ _ _ :=
    ⟨Set.univ, fun children _ => ⟨children, trivial, fun _ => E.refl _⟩,
      fun _ admitted => admitted⟩

/-- Each authored label has finitely many successors of each sort, up to
the equations. -/
def FiniteAuthoredBranching : Prop :=
  ∀ (label : base.Label) {source : signature.Srt} (start : Term signature source)
    (target : signature.Srt),
    ∃ cover : Set (Term signature target), cover.Finite ∧
      ∀ next : Term signature target, base.act label start next →
        ∃ representative ∈ cover, E.Rel next representative

variable (E) in
/-- Each admitted constructor decomposes each term in finitely many ways, up
to the equations. -/
def FiniteDecompositions : Prop :=
  ∀ (constructor : signature.Constructor), opened constructor →
    ∀ whole : Term signature (signature.output constructor),
    ∃ cover : Set ((position : Fin (signature.arity constructor)) →
        Term signature (signature.input constructor position)), cover.Finite ∧
      ∀ children, E.Rel whole (Term.node constructor children) →
        ∃ representative ∈ cover, ∀ position, E.Rel (children position) (representative position)

variable {base opened}

/-- The admitted formulas with finite conjunctions, under finite branching. -/
def Fragment.finitary (authored : FiniteAuthoredBranching base)
    (decompositions : FiniteDecompositions E opened) : Fragment base opened where
  Admits formula := formula.Allowed opened ∧ formula.Finitary
  allowed admitted := admitted.1
  top _ := ⟨fun index => index.elim, inferInstance, fun index => index.elim⟩
  neg admitted := admitted
  atom _ _ := ⟨trivial, trivial⟩
  proper := by
    intro sort label next inner admitted
    exact admitted
  node := by
    intro constructor permission arguments admitted
    exact ⟨⟨permission, fun position => (admitted position).1⟩,
      fun position => (admitted position).2⟩
  properCover label _ start target := by
    obtain ⟨cover, finite, covers⟩ := authored label start target
    exact ⟨cover, covers, fun _ admitted =>
      ⟨fun index => (admitted index).1, finite.to_subtype, fun index => (admitted index).2⟩⟩
  decompositionCover constructor permission whole := by
    obtain ⟨cover, finite, covers⟩ := decompositions constructor permission whole
    exact ⟨cover, covers, fun _ admitted =>
      ⟨fun index => (admitted index).1, finite.to_subtype, fun index => (admitted index).2⟩⟩

variable (base opened)

/-- The same admitted formulas hold of both terms. -/
def LogicallyEquivalent {sort : signature.Srt} (left right : Term signature sort) : Prop :=
  ∀ formula : Formula signature base.Atom base.Label sort, formula.Allowed opened →
    (Holds base formula left ↔ Holds base formula right)

/-- The same admitted formulas with finite conjunctions hold of both terms. -/
def FinitaryEquivalent {sort : signature.Srt} (left right : Term signature sort) : Prop :=
  ∀ formula : Formula signature base.Atom base.Label sort, formula.Allowed opened →
    formula.Finitary → (Holds base formula left ↔ Holds base formula right)

/-- **Partial characterization, for every policy.** Bisimilarity in the
instrument system is equivalence in the logic whose structural connectives
are those of the admitted constructors. -/
theorem logicallyEquivalent_iff_bisimilar {sort : signature.Srt}
    (left right : Term signature sort) :
    LogicallyEquivalent base opened left right ↔
      Bisimilar base opened (.term left) (.term right) :=
  (Fragment.all base opened).equivalent_iff_bisimilar left right

variable {base opened}

/-- **Partial characterization with finite conjunctions**, under finite
branching of the authored steps and of the admitted decompositions. -/
theorem finitaryEquivalent_iff_bisimilar (authored : FiniteAuthoredBranching base)
    (decompositions : FiniteDecompositions E opened) {sort : signature.Srt}
    (left right : Term signature sort) :
    FinitaryEquivalent base opened left right ↔
      Bisimilar base opened (.term left) (.term right) := by
  have adequate := (Fragment.finitary authored decompositions).equivalent_iff_bisimilar left right
  constructor
  · intro equivalent
    exact adequate.mp (fun formula admitted => equivalent formula admitted.1 admitted.2)
  · intro related formula allowed finitary
    exact adequate.mpr related formula ⟨allowed, finitary⟩

/-- **Logical correspondence.** With every constructor admitted, equality
in the equation theory, bisimilarity in the instrument system, equivalence
in the full logic and transfer of purely structural formulas all coincide. -/
theorem correspondence (complete : ∀ constructor, opened constructor)
    {sort : signature.Srt} (left right : Term signature sort) :
    (E.Rel left right ↔ Bisimilar base opened (.term left) (.term right)) ∧
      (E.Rel left right ↔ LogicallyEquivalent base opened left right) ∧
      (E.Rel left right ↔
        ∀ formula : Formula signature base.Atom base.Label sort, formula.Structural →
          Holds base formula left → Holds base formula right) :=
  ⟨(bisimilar_iff_rel complete left right).symm,
    (bisimilar_iff_rel complete left right).symm.trans
      (logicallyEquivalent_iff_bisimilar base opened left right).symm,
    rel_iff_structural base left right⟩

/-- **Downward closure.** For a term built from admitted constructors, all
four readings coincide against every term of its sort, and the purely
structural formulas of the policy already decide them. -/
theorem correspondence_of_supported {sort : signature.Srt} {left : Term signature sort}
    (supported : Supported opened left) (right : Term signature sort) :
    (E.Rel left right ↔ Bisimilar base opened (.term left) (.term right)) ∧
      (E.Rel left right ↔ LogicallyEquivalent base opened left right) ∧
      (E.Rel left right ↔
        ∀ formula : Formula signature base.Atom base.Label sort, formula.Structural →
          formula.Allowed opened → Holds base formula left → Holds base formula right) :=
  ⟨(bisimilar_iff_rel_of_supported supported right).symm,
    (bisimilar_iff_rel_of_supported supported right).symm.trans
      (logicallyEquivalent_iff_bisimilar base opened left right).symm,
    rel_iff_structural_of_supported base supported right⟩

end Mettapedia.OSLF.Framework.SortedInstrumentCongruence
