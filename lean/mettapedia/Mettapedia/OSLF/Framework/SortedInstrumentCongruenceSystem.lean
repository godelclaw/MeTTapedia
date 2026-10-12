import Mettapedia.OSLF.Syntax.SortedConstructorCongruences
import Mettapedia.GSLT.Logic.HennessyMilnerAdequacy

/-!
# Instrument kits beside authored steps, over an arbitrary equation theory

The carrier is the closed term algebra of a many-sorted first-order
signature with any congruence as its equations. The authored theory supplies
labelled steps and observations that respect those equations. A policy admits
constructors to the kit. An admitted constructor `c` contributes three
labels:

* `ask c` leads from a term to an argument bundle exactly when the term is
  equal, in the equation theory, to `c` applied to that bundle;
* `get c i` leads from a bundle to its component at position `i`;
* `build c` leads from a bundle back to the constructed term.

Targets are closed under the equations, so equal terms have the same
labelled steps. The sort of a term is an observation.

Proved here, for every congruence and every authored system:

* equal terms are bisimilar under every policy (calibration);
* a supported term is bisimilar to another term only if they are equal, so a
  complete policy makes bisimilarity the equation theory itself;
* enlarging the policy refines bisimilarity, because the added steps carry
  labels the smaller kit does not have;
* with nothing admitted, bisimilarity is the authored system's own;
* hence authored-bisimilar terms in different classes are separated exactly
  by the instruments.

The reconstruction recurses on the supplied left-hand term. It uses no size
measure and no lean representative, so it imposes no condition on the
equation theory.

These are the direct labelled steps. Deriving them as least context labels
of a reactive system needs relative pushouts modulo the equations and is a
separate comparison. Binding constructors are outside this carrier.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.SortedInstrumentCongruence

open Mettapedia.GSLT
open Mettapedia.OSLF.SortedConstructors

universe u v uAtom uLabel

variable {signature : Signature.{u,v}}

-- Observations and labels have separately sized carriers.
set_option linter.checkUnivs false in
/-- The authored theory's labelled steps and observations on closed terms.
Both respect the equation theory. -/
structure BaseSystem (E : Congruence signature) where
  Atom : Type uAtom
  observes : Atom → {sort : signature.Srt} → Term signature sort → Prop
  observes_resp : ∀ (atom : Atom) {sort : signature.Srt} {left right : Term signature sort},
    E.Rel left right → (observes atom left ↔ observes atom right)
  Label : Type uLabel
  act : Label → {source target : signature.Srt} →
    Term signature source → Term signature target → Prop
  act_resp_left : ∀ {label : Label} {source target : signature.Srt}
    {left right : Term signature source} {next : Term signature target},
    E.Rel left right → act label left next →
      ∃ next' : Term signature target, act label right next' ∧ E.Rel next next'
  act_resp_right : ∀ {label : Label} {source target : signature.Srt}
    {start : Term signature source} {next next' : Term signature target},
    act label start next → E.Rel next next' → act label start next'

/-- No authored steps and no authored observations. -/
def BaseSystem.silent (E : Congruence signature) : BaseSystem.{u,v,0,0} E where
  Atom := Empty
  observes atom := atom.elim
  observes_resp atom := atom.elim
  Label := Empty
  act label := label.elim
  act_resp_left {label} := label.elim
  act_resp_right {label} := label.elim

/-- A closed term, or the argument bundle an opening returned. -/
inductive State (signature : Signature.{u,v}) : Type (max u v) where
  | term {sort : signature.Srt} (value : Term signature sort) : State signature
  | bundle (constructor : signature.Constructor)
      (arguments : (position : Fin (signature.arity constructor)) →
        Term signature (signature.input constructor position)) : State signature

/-- An authored label, or one of a constructor's three instrument labels. -/
inductive Label (signature : Signature.{u,v}) (Proper : Type uLabel) : Type (max v uLabel) where
  | proper (label : Proper) : Label signature Proper
  | ask (constructor : signature.Constructor) : Label signature Proper
  | get (constructor : signature.Constructor)
      (position : Fin (signature.arity constructor)) : Label signature Proper
  | build (constructor : signature.Constructor) : Label signature Proper

/-- Authored labels are always available; an instrument label needs its
constructor admitted. -/
def Label.Permitted (opened : signature.Constructor → Prop) {Proper : Type uLabel} :
    Label signature Proper → Prop
  | .proper _ => True
  | .ask constructor => opened constructor
  | .get constructor _ => opened constructor
  | .build constructor => opened constructor

theorem State.term_injective {sort : signature.Srt} {left right : Term signature sort}
    (same : (State.term left : State signature) = State.term right) : left = right := by
  cases same
  rfl

theorem State.bundle_injective {constructor : signature.Constructor}
    {left right : (position : Fin (signature.arity constructor)) →
      Term signature (signature.input constructor position)}
    (same : State.bundle constructor left = State.bundle constructor right) : left = right := by
  cases same
  rfl

/-- The equations on states: equal terms, and bundles equal componentwise. -/
inductive StateRel (E : Congruence signature) : State signature → State signature → Prop where
  | term {sort : signature.Srt} {left right : Term signature sort} :
      E.Rel left right → StateRel E (.term left) (.term right)
  | bundle (constructor : signature.Constructor)
      {left right : (position : Fin (signature.arity constructor)) →
        Term signature (signature.input constructor position)} :
      (∀ position, E.Rel (left position) (right position)) →
        StateRel E (.bundle constructor left) (.bundle constructor right)

namespace StateRel

variable {E : Congruence signature}

theorem refl (E : Congruence signature) : ∀ state : State signature, StateRel E state state
  | .term value => .term (E.refl value)
  | .bundle constructor _ => .bundle constructor (fun _ => E.refl _)

theorem symm {left right : State signature} (related : StateRel E left right) :
    StateRel E right left := by
  cases related with
  | term equation => exact .term (E.symm equation)
  | bundle constructor children =>
    exact .bundle constructor (fun position => E.symm (children position))

theorem trans {left middle right : State signature} (first : StateRel E left middle)
    (second : StateRel E middle right) : StateRel E left right := by
  cases first with
  | term firstEquation =>
    cases second with
    | term secondEquation => exact .term (E.trans firstEquation secondEquation)
  | bundle constructor firstChildren =>
    cases second with
    | bundle _ secondChildren =>
      exact .bundle constructor
        (fun position => E.trans (firstChildren position) (secondChildren position))

end StateRel

variable {E : Congruence signature}

/-- The labelled steps of the authored system extended by an instrument kit. -/
inductive Act (base : BaseSystem.{u,v,uAtom,uLabel} E) (opened : signature.Constructor → Prop) :
    Label signature base.Label → State signature → State signature → Prop where
  | proper {label : base.Label} {source target : signature.Srt}
      {start : Term signature source} {next : Term signature target} :
      base.act label start next → Act base opened (.proper label) (.term start) (.term next)
  | ask (constructor : signature.Constructor) (permission : opened constructor)
      {source : Term signature (signature.output constructor)}
      {arguments : (position : Fin (signature.arity constructor)) →
        Term signature (signature.input constructor position)} :
      E.Rel source (Term.node constructor arguments) →
        Act base opened (.ask constructor) (.term source) (.bundle constructor arguments)
  | get (constructor : signature.Constructor) (permission : opened constructor)
      {arguments : (position : Fin (signature.arity constructor)) →
        Term signature (signature.input constructor position)}
      (position : Fin (signature.arity constructor))
      {target : Term signature (signature.input constructor position)} :
      E.Rel (arguments position) target →
        Act base opened (.get constructor position) (.bundle constructor arguments) (.term target)
  | build (constructor : signature.Constructor) (permission : opened constructor)
      {arguments : (position : Fin (signature.arity constructor)) →
        Term signature (signature.input constructor position)}
      {target : Term signature (signature.output constructor)} :
      E.Rel (Term.node constructor arguments) target →
        Act base opened (.build constructor) (.bundle constructor arguments) (.term target)

namespace Act

variable {base : BaseSystem.{u,v,uAtom,uLabel} E} {opened : signature.Constructor → Prop}

theorem proper_inv {label : base.Label} {source target : State signature}
    (step : Act base opened (.proper label) source target) :
    ∃ (first second : signature.Srt) (start : Term signature first)
      (next : Term signature second),
      source = .term start ∧ target = .term next ∧ base.act label start next := by
  cases step with
  | proper authored => exact ⟨_, _, _, _, rfl, rfl, authored⟩

theorem ask_inv {constructor : signature.Constructor} {source target : State signature}
    (step : Act base opened (.ask constructor) source target) :
    opened constructor ∧
      ∃ (value : Term signature (signature.output constructor))
        (arguments : (position : Fin (signature.arity constructor)) →
          Term signature (signature.input constructor position)),
        source = .term value ∧ target = .bundle constructor arguments ∧
          E.Rel value (Term.node constructor arguments) := by
  cases step with
  | ask _ permission decomposition => exact ⟨permission, _, _, rfl, rfl, decomposition⟩

theorem get_inv {constructor : signature.Constructor}
    {position : Fin (signature.arity constructor)} {source target : State signature}
    (step : Act base opened (.get constructor position) source target) :
    opened constructor ∧
      ∃ (arguments : (index : Fin (signature.arity constructor)) →
          Term signature (signature.input constructor index))
        (value : Term signature (signature.input constructor position)),
        source = .bundle constructor arguments ∧ target = .term value ∧
          E.Rel (arguments position) value := by
  cases step with
  | get _ permission _ projection => exact ⟨permission, _, _, rfl, rfl, projection⟩

theorem build_inv {constructor : signature.Constructor} {source target : State signature}
    (step : Act base opened (.build constructor) source target) :
    opened constructor ∧
      ∃ (arguments : (index : Fin (signature.arity constructor)) →
          Term signature (signature.input constructor index))
        (value : Term signature (signature.output constructor)),
        source = .bundle constructor arguments ∧ target = .term value ∧
          E.Rel (Term.node constructor arguments) value := by
  cases step with
  | build _ permission rebuilt => exact ⟨permission, _, _, rfl, rfl, rebuilt⟩

/-- Equal sources have the same labelled steps, to the same targets. -/
theorem resp_left {label : Label signature base.Label} {left right target : State signature}
    (equation : StateRel E left right) (step : Act base opened label left target) :
    ∃ target', Act base opened label right target' ∧ StateRel E target target' := by
  cases step with
  | proper authored =>
    cases equation with
    | term equation =>
      obtain ⟨next', step', related⟩ := base.act_resp_left equation authored
      exact ⟨.term next', .proper step', .term related⟩
  | ask constructor permission decomposition =>
    cases equation with
    | term equation =>
      exact ⟨_, .ask constructor permission (E.trans (E.symm equation) decomposition),
        StateRel.refl E _⟩
  | get constructor permission position projection =>
    cases equation with
    | bundle _ children =>
      exact ⟨_, .get constructor permission position
        (E.trans (E.symm (children position)) projection), StateRel.refl E _⟩
  | build constructor permission rebuilt =>
    cases equation with
    | bundle _ children =>
      exact ⟨_, .build constructor permission
        (E.trans (E.symm (E.node constructor children)) rebuilt), StateRel.refl E _⟩

/-- Targets are closed under the equations. -/
theorem resp_right {label : Label signature base.Label} {source target target' : State signature}
    (step : Act base opened label source target) (equation : StateRel E target target') :
    Act base opened label source target' := by
  cases step with
  | proper authored =>
    cases equation with
    | term equation => exact .proper (base.act_resp_right authored equation)
  | ask constructor permission decomposition =>
    cases equation with
    | bundle _ children =>
      exact .ask constructor permission (E.trans decomposition (E.node constructor children))
  | get constructor permission position projection =>
    cases equation with
    | term equation => exact .get constructor permission position (E.trans projection equation)
  | build constructor permission rebuilt =>
    cases equation with
    | term equation => exact .build constructor permission (E.trans rebuilt equation)

/-- A smaller kit has exactly the larger kit's steps at the labels it permits. -/
theorem iff_permitted {smaller larger : signature.Constructor → Prop}
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    {label : Label signature base.Label} {source target : State signature} :
    Act base smaller label source target ↔
      label.Permitted smaller ∧ Act base larger label source target := by
  constructor
  · intro step
    cases step with
    | proper authored => exact ⟨trivial, .proper authored⟩
    | ask constructor permission decomposition =>
      exact ⟨permission, .ask constructor (inclusion _ permission) decomposition⟩
    | get constructor permission position projection =>
      exact ⟨permission, .get constructor (inclusion _ permission) position projection⟩
    | build constructor permission rebuilt =>
      exact ⟨permission, .build constructor (inclusion _ permission) rebuilt⟩
  · rintro ⟨permitted, step⟩
    cases step with
    | proper authored => exact .proper authored
    | ask constructor _ decomposition => exact .ask constructor permitted decomposition
    | get constructor _ position projection => exact .get constructor permitted position projection
    | build constructor _ rebuilt => exact .build constructor permitted rebuilt

end Act

/-- A term state shows its sort and the authored observations of its term.
A bundle shows neither. -/
def observes (base : BaseSystem.{u,v,uAtom,uLabel} E) (atom : signature.Srt ⊕ base.Atom) :
    State signature → Prop
  | @State.term _ actual value =>
      match atom with
      | .inl sort => actual = sort
      | .inr authored => base.observes authored value
  | .bundle _ _ => False

/-- States with the congruence as equations and the authored steps as
rewrites. The carrier does not depend on the instrument policy. -/
def gslt (base : BaseSystem.{u,v,uAtom,uLabel} E) : GSLT where
  Term := State signature
  equations := ⟨StateRel E, StateRel.refl E, StateRel.symm, StateRel.trans⟩
  rewrites source target := ∃ label, Act base (fun _ => False) label source target
  rewrites_resp_left := by
    rintro source source' target equation ⟨label, step⟩
    obtain ⟨target', step', related⟩ := Act.resp_left equation step
    exact ⟨target', ⟨label, step'⟩, related⟩
  rewrites_resp_right := by
    rintro source target target' ⟨label, step⟩ equation
    exact ⟨label, Act.resp_right step equation⟩

/-- The authored system extended by the admitted instruments. -/
def system (base : BaseSystem.{u,v,uAtom,uLabel} E) (opened : signature.Constructor → Prop) :
    HennessyMilner.System.{max u uAtom, max v uLabel} (gslt base) where
  Atom := signature.Srt ⊕ base.Atom
  observes := observes base
  observes_resp := by
    intro atom left right equation
    cases equation with
    | term equation =>
      cases atom with
      | inl sort => exact Iff.rfl
      | inr authored => exact base.observes_resp authored equation
    | bundle constructor children => exact Iff.rfl
  Label := Label signature base.Label
  act := Act base opened
  act_resp_left := fun equation step => Act.resp_left equation step
  act_resp_right := fun step equation => Act.resp_right step equation

variable (base : BaseSystem.{u,v,uAtom,uLabel} E) (opened : signature.Constructor → Prop)

/-- Bisimilarity of states under a policy. -/
abbrev Bisimilar (left right : State signature) : Prop :=
  (system base opened).Bisimilar left right

variable {base opened}

/-- Related term states have the same sort. -/
theorem sort_eq_of_related {relation : State signature → State signature → Prop}
    (bisimulation : (system base opened).IsBisimulation relation)
    {first second : signature.Srt} {left : Term signature first} {right : Term signature second}
    (related : relation (.term left) (.term right)) : first = second := by
  have observed := (bisimulation.2.2 related (Sum.inl first)).mp
  exact (observed rfl).symm

theorem sort_eq_of_bisimilar {first second : signature.Srt} {left : Term signature first}
    {right : Term signature second} (related : Bisimilar base opened (.term left) (.term right)) :
    first = second := by
  obtain ⟨relation, bisimulation, holds⟩ := related
  exact sort_eq_of_related bisimulation holds

/-- **Calibration.** Equal terms are bisimilar under every policy. -/
theorem bisimilar_of_rel {sort : signature.Srt} {left right : Term signature sort}
    (equation : E.Rel left right) : Bisimilar base opened (.term left) (.term right) :=
  (system base opened).bisimilar_of_equiv (left := State.term left) (right := State.term right)
    (StateRel.term equation)

/-- A supported term related to another term by any bisimulation is equal
to it. The recursion is on the supported term; the other term supplies an
arbitrary matching decomposition at each opening. -/
theorem rel_of_related {relation : State signature → State signature → Prop}
    (bisimulation : (system base opened).IsBisimulation relation)
    {sort : signature.Srt} (left : Term signature sort) :
    Supported opened left → ∀ right : Term signature sort,
      relation (.term left) (.term right) → E.Rel left right := by
  induction left with
  | node constructor arguments inductionHypothesis =>
    intro supported right related
    have forward := bisimulation.1
    obtain ⟨matched, matchedStep, bundlesRelated⟩ :=
      forward related (Label.ask constructor) (Act.ask constructor supported.1 (E.refl _))
    obtain ⟨-, value, others, sourceShape, rfl, decomposition⟩ := Act.ask_inv matchedStep
    have valueEq : right = value := State.term_injective sourceShape
    subst valueEq
    have children : ∀ position, E.Rel (arguments position) (others position) := by
      intro position
      obtain ⟨projected, projectedStep, childRelated⟩ :=
        forward bundlesRelated (Label.get constructor position)
          (Act.get constructor supported.1 position (E.refl _))
      obtain ⟨-, compared, target, bundleShape, rfl, projection⟩ := Act.get_inv projectedStep
      have comparedEq : others = compared := State.bundle_injective bundleShape
      subst comparedEq
      exact E.trans (inductionHypothesis position (supported.2 position) target childRelated)
        (E.symm projection)
    exact E.trans (E.node constructor children) (E.symm decomposition)

/-- **Reconstruction on the supported part.** For a term built from admitted
constructors, bisimilarity to any term of its sort is equality in the
equation theory. -/
theorem bisimilar_iff_rel_of_supported {sort : signature.Srt} {left : Term signature sort}
    (supported : Supported opened left) (right : Term signature sort) :
    Bisimilar base opened (.term left) (.term right) ↔ E.Rel left right := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    exact rel_of_related bisimulation left supported right related
  · exact bisimilar_of_rel

/-- **Reconstruction.** With every constructor admitted, bisimilarity of
closed terms is the equation theory. No condition is imposed on it. -/
theorem bisimilar_iff_rel (complete : ∀ constructor, opened constructor)
    {sort : signature.Srt} (left right : Term signature sort) :
    Bisimilar base opened (.term left) (.term right) ↔ E.Rel left right :=
  bisimilar_iff_rel_of_supported (supported_of_complete complete left) right

/-- **Monotonicity.** A larger kit relates fewer states. The added steps
carry labels the smaller kit does not have, so a bisimulation for the larger
kit is one for the smaller. -/
theorem bisimilar_mono {smaller larger : signature.Constructor → Prop}
    (inclusion : ∀ constructor, smaller constructor → larger constructor)
    {left right : State signature} (related : Bisimilar base larger left right) :
    Bisimilar base smaller left right := by
  obtain ⟨relation, ⟨forward, backward, atoms⟩, holds⟩ := related
  refine ⟨relation, ⟨?_, ?_, atoms⟩, holds⟩
  · intro source other pair label source' step
    obtain ⟨permitted, largerStep⟩ := (Act.iff_permitted inclusion).mp step
    obtain ⟨other', otherStep, pair'⟩ := forward pair label largerStep
    exact ⟨other', (Act.iff_permitted inclusion).mpr ⟨permitted, otherStep⟩, pair'⟩
  · intro source other pair label other' step
    obtain ⟨permitted, largerStep⟩ := (Act.iff_permitted inclusion).mp step
    obtain ⟨source', sourceStep, pair'⟩ := backward pair label largerStep
    exact ⟨source', (Act.iff_permitted inclusion).mpr ⟨permitted, sourceStep⟩, pair'⟩

/-! ## The authored system's own bisimilarity -/

/-- A closed term together with its sort. -/
abbrev Packed (signature : Signature.{u,v}) := Σ sort : signature.Srt, Term signature sort

namespace BaseSystem

variable (base : BaseSystem.{u,v,uAtom,uLabel} E)

/-- A bisimulation of the authored labelled steps. It is defined on terms
alone, with no instrument and no bundle. -/
def IsBisimulation (relation : Packed signature → Packed signature → Prop) : Prop :=
  (∀ ⦃left right⦄, relation left right → ∀ (label : base.Label) ⦃next : Packed signature⦄,
      base.act label left.2 next.2 →
        ∃ next' : Packed signature, base.act label right.2 next'.2 ∧ relation next next') ∧
    (∀ ⦃left right⦄, relation left right → ∀ (label : base.Label) ⦃next : Packed signature⦄,
      base.act label right.2 next.2 →
        ∃ next' : Packed signature, base.act label left.2 next'.2 ∧ relation next' next) ∧
    (∀ ⦃left right⦄, relation left right → left.1 = right.1) ∧
    (∀ ⦃left right⦄, relation left right → ∀ atom : base.Atom,
      base.observes atom left.2 ↔ base.observes atom right.2)

/-- Bisimilarity of the authored system. -/
def Bisimilar (left right : Packed signature) : Prop :=
  ∃ relation, base.IsBisimulation relation ∧ relation left right

end BaseSystem

/-- A relation on packed terms, read on term states. -/
inductive Lifted (relation : Packed signature → Packed signature → Prop) :
    State signature → State signature → Prop where
  | mk {first second : signature.Srt} (left : Term signature first)
      (right : Term signature second) :
      relation ⟨first, left⟩ ⟨second, right⟩ → Lifted relation (.term left) (.term right)

/-- **The empty kit.** With nothing admitted, bisimilarity of terms is the
authored system's own bisimilarity. -/
theorem bisimilar_closed_iff {first second : signature.Srt} (left : Term signature first)
    (right : Term signature second) :
    Bisimilar base (fun _ => False) (.term left) (.term right) ↔
      base.Bisimilar ⟨first, left⟩ ⟨second, right⟩ := by
  constructor
  · rintro ⟨relation, bisimulation, related⟩
    obtain ⟨forward, backward, atoms⟩ := bisimulation
    refine ⟨fun source other => relation (.term source.2) (.term other.2), ⟨?_, ?_, ?_, ?_⟩, related⟩
    · intro source other pair label next authored
      obtain ⟨matched, step, pair'⟩ :=
        forward pair (Label.proper label) (Act.proper authored)
      obtain ⟨start, reached, value, target, sourceShape, rfl, authored'⟩ := Act.proper_inv step
      cases sourceShape
      exact ⟨⟨reached, target⟩, authored', pair'⟩
    · intro source other pair label next authored
      obtain ⟨matched, step, pair'⟩ :=
        backward pair (Label.proper label) (Act.proper authored)
      obtain ⟨start, reached, value, target, sourceShape, rfl, authored'⟩ := Act.proper_inv step
      cases sourceShape
      exact ⟨⟨reached, target⟩, authored', pair'⟩
    · intro source other pair
      exact sort_eq_of_related ⟨forward, backward, atoms⟩ pair
    · intro source other pair atom
      exact atoms pair (Sum.inr atom)
  · rintro ⟨relation, ⟨forward, backward, sorts, atoms⟩, related⟩
    refine ⟨Lifted relation, ⟨?_, ?_, ?_⟩, Lifted.mk left right related⟩
    · rintro _ _ ⟨source, other, pair⟩ label source' step
      cases step with
      | proper authored =>
        obtain ⟨⟨reached, target⟩, authored', pair'⟩ := forward pair _ (next := ⟨_, _⟩) authored
        exact ⟨.term target, .proper authored', Lifted.mk _ target pair'⟩
      | ask constructor permission decomposition => exact permission.elim
    · rintro _ _ ⟨source, other, pair⟩ label other' step
      cases step with
      | proper authored =>
        obtain ⟨⟨reached, target⟩, authored', pair'⟩ := backward pair _ (next := ⟨_, _⟩) authored
        exact ⟨.term target, .proper authored', Lifted.mk target _ pair'⟩
      | ask constructor permission decomposition => exact permission.elim
    · rintro _ _ ⟨source, other, pair⟩ atom
      cases atom with
      | inl sort =>
        have same : _ = _ := sorts pair
        cases same
        exact Iff.rfl
      | inr authored => exact atoms pair authored

/-- **The gap.** Terms the authored system cannot tell apart, lying in
different equation classes, are related by the empty kit and separated by
the complete one. -/
theorem refinement_strict {sort : signature.Srt} {left right : Term signature sort}
    (indistinguishable : base.Bisimilar ⟨sort, left⟩ ⟨sort, right⟩)
    (distinct : ¬ E.Rel left right) :
    Bisimilar base (fun _ => False) (.term left) (.term right) ∧
      ¬ Bisimilar base (fun _ => True) (.term left) (.term right) :=
  ⟨(bisimilar_closed_iff left right).mpr indistinguishable,
    fun related => distinct ((bisimilar_iff_rel (fun _ => trivial) left right).mp related)⟩

end Mettapedia.OSLF.Framework.SortedInstrumentCongruence
