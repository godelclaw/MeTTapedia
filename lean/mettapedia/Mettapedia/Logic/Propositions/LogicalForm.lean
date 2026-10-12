import Mathlib.Control.Bifunctor
import Mathlib.Logic.Function.Basic

/-!
# Logical forms

Every structured account of what a sentence expresses keeps the shape of the
sentence and changes what sits at its leaves.  A sentence has words at its
leaves; a Russellian proposition has the objects and properties the words stand
for (Russell, *The Principles of Mathematics*, 1903, ch. IV); a Fregean
proposition has their senses (Frege, "Über Sinn und Bedeutung", 1892).  Chalmers
states the construction in this form: a structured intension consists of the
intensions "of all the simple expressions in a sentence ... structured
according to the sentence's logical form" ("Propositions and Attitude
Ascriptions: A Fregean Account", *Noûs* 45, 2011, §2).

This module fixes one such shape and makes the leaf type a parameter.

* `Form ν π` is a logical form with name leaves in `ν` and predicate leaves in
  `π`: predication, identity, negation and conjunction.
* `Form.map` replaces the leaves and keeps the shape.  It preserves identities
  and composition (`Form.map_id`, `Form.map_map`), so `Form` is a lawful
  bifunctor, and it is injective when both leaf maps are (`Form.map_injective`).
* `Form.Holds` reads a form as true or false, given when a predicate leaf
  applies to a name leaf and when two name leaves name the same thing.
  Replacing leaves and then reading is reading with the leaf maps composed in
  (`Form.holds_map`).
* A form over pairs of leaves is the same thing as a pair of forms of one
  shape: the two projections together are injective (`Form.unzip_injective`).
* With names that may denote nothing, read negatively, the internal negation of a
  predication (the complementary predicate) and its external negation agree
  exactly when the name denotes (`Form.internal_iff_external_iff_isSome`); over an
  empty domain every universal claim holds and no existential one does, and a
  universal claim carries an existential one exactly on an inhabited domain
  (`subalternation_iff_nonempty`).
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Propositions

universe u v u' v' u'' v''

/-- A logical form with name leaves in `ν` and predicate leaves in `π`. -/
inductive Form (ν : Type u) (π : Type v) : Type (max u v)
  /-- Predication: the predicate applies to what the name stands for. -/
  | pred (predicate : π) (subject : ν) : Form ν π
  /-- Identity: the two names stand for the same thing. -/
  | ident (left right : ν) : Form ν π
  /-- Negation. -/
  | neg (body : Form ν π) : Form ν π
  /-- Conjunction. -/
  | conj (left right : Form ν π) : Form ν π
  deriving DecidableEq

namespace Form

variable {ν : Type u} {π : Type v} {ν' : Type u'} {π' : Type v'} {ν'' : Type u''} {π'' : Type v''}

/-- Replace the leaves of a form and keep its shape. -/
def map (onNames : ν → ν') (onPredicates : π → π') : Form ν π → Form ν' π'
  | pred predicate subject => pred (onPredicates predicate) (onNames subject)
  | ident left right => ident (onNames left) (onNames right)
  | neg body => neg (map onNames onPredicates body)
  | conj left right => conj (map onNames onPredicates left) (map onNames onPredicates right)

@[simp]
theorem map_id (form : Form ν π) : map id id form = form := by
  induction form with
  | pred => rfl
  | ident => rfl
  | neg body ih => simp only [map, ih]
  | conj left right ihLeft ihRight => simp only [map, ihLeft, ihRight]

@[simp]
theorem map_map (onNames : ν → ν') (onNames' : ν' → ν'') (onPredicates : π → π')
    (onPredicates' : π' → π'') (form : Form ν π) :
    map onNames' onPredicates' (map onNames onPredicates form) =
      map (onNames' ∘ onNames) (onPredicates' ∘ onPredicates) form := by
  induction form with
  | pred => rfl
  | ident => rfl
  | neg body ih => simp only [map, ih]
  | conj left right ihLeft ihRight => simp only [map, ihLeft, ihRight]

/-- Replacing leaves injectively loses nothing. -/
theorem map_injective {onNames : ν → ν'} {onPredicates : π → π'}
    (namesInjective : Function.Injective onNames)
    (predicatesInjective : Function.Injective onPredicates) :
    Function.Injective (map onNames onPredicates) := by
  intro first
  induction first with
  | pred predicate subject =>
    intro second same
    cases second <;> simp only [map, pred.injEq, reduceCtorEq] at same
    obtain ⟨samePredicate, sameSubject⟩ := same
    rw [predicatesInjective samePredicate, namesInjective sameSubject]
  | ident left right =>
    intro second same
    cases second <;> simp only [map, ident.injEq, reduceCtorEq] at same
    obtain ⟨sameLeft, sameRight⟩ := same
    rw [namesInjective sameLeft, namesInjective sameRight]
  | neg body ih =>
    intro second same
    cases second <;> simp only [map, neg.injEq, reduceCtorEq] at same
    rw [ih same]
  | conj left right ihLeft ihRight =>
    intro second same
    cases second <;> simp only [map, conj.injEq, reduceCtorEq] at same
    obtain ⟨sameLeft, sameRight⟩ := same
    rw [ihLeft sameLeft, ihRight sameRight]

instance : Bifunctor Form.{u, v} where
  bimap := map

instance : LawfulBifunctor Form.{u, v} where
  id_bimap := map_id
  bimap_bimap onNames onNames' onPredicates onPredicates' form :=
    map_map onNames onNames' onPredicates onPredicates' form

/-- Read a form as true or false.  `applies` says when a predicate leaf applies
to a name leaf, and `same` says when two name leaves name the same thing. -/
def Holds (applies : π → ν → Prop) (same : ν → ν → Prop) : Form ν π → Prop
  | pred predicate subject => applies predicate subject
  | ident left right => same left right
  | neg body => ¬ Holds applies same body
  | conj left right => Holds applies same left ∧ Holds applies same right

/-- Replacing leaves and then reading is reading with the replacement composed
into the reading of the leaves. -/
theorem holds_map (onNames : ν → ν') (onPredicates : π → π') (applies : π' → ν' → Prop)
    (same : ν' → ν' → Prop) (form : Form ν π) :
    Holds applies same (map onNames onPredicates form) ↔
      Holds (fun predicate subject => applies (onPredicates predicate) (onNames subject))
        (fun left right => same (onNames left) (onNames right)) form := by
  induction form with
  | pred => exact Iff.rfl
  | ident => exact Iff.rfl
  | neg body ih => exact not_congr ih
  | conj left right ihLeft ihRight => exact and_congr ihLeft ihRight

/-- Two readings that agree on the leaves agree on every form. -/
theorem holds_congr {applies applies' : π → ν → Prop} {same same' : ν → ν → Prop}
    (appliesAgree : ∀ predicate subject, applies predicate subject ↔ applies' predicate subject)
    (sameAgree : ∀ left right, same left right ↔ same' left right) (form : Form ν π) :
    Holds applies same form ↔ Holds applies' same' form := by
  induction form with
  | pred predicate subject => exact appliesAgree predicate subject
  | ident left right => exact sameAgree left right
  | neg body ih => exact not_congr ih
  | conj left right ihLeft ihRight => exact and_congr ihLeft ihRight

/-- The two component forms of a form over pairs of leaves. -/
def unzip (form : Form (ν × ν') (π × π')) : Form ν π × Form ν' π' :=
  (map Prod.fst Prod.fst form, map Prod.snd Prod.snd form)

/-- A form over pairs of leaves is determined by its two component forms. -/
theorem unzip_injective : Function.Injective (unzip (ν := ν) (π := π) (ν' := ν') (π' := π')) := by
  intro first
  induction first with
  | pred predicate subject =>
    intro second same
    cases second <;>
      simp only [unzip, map, Prod.mk.injEq, pred.injEq, reduceCtorEq, and_false]
        at same
    obtain ⟨⟨firstPredicate, firstSubject⟩, secondPredicate, secondSubject⟩ := same
    rw [Prod.ext firstPredicate secondPredicate, Prod.ext firstSubject secondSubject]
  | ident left right =>
    intro second same
    cases second <;>
      simp only [unzip, map, Prod.mk.injEq, ident.injEq, reduceCtorEq, and_false]
        at same
    obtain ⟨⟨firstLeft, firstRight⟩, secondLeft, secondRight⟩ := same
    rw [Prod.ext firstLeft secondLeft, Prod.ext firstRight secondRight]
  | neg body ih =>
    intro second same
    cases second <;>
      simp only [unzip, map, Prod.mk.injEq, neg.injEq, reduceCtorEq, and_false]
        at same
    rw [ih (Prod.ext same.1 same.2)]
  | conj left right ihLeft ihRight =>
    intro second same
    cases second <;>
      simp only [unzip, map, Prod.mk.injEq, conj.injEq, reduceCtorEq, and_false]
        at same
    obtain ⟨⟨firstLeft, firstRight⟩, secondLeft, secondRight⟩ := same
    rw [ihLeft (Prod.ext firstLeft secondLeft), ihRight (Prod.ext firstRight secondRight)]

end Form

/-! ## Names that may fail to denote, and empty domains

`Form.Holds` reads predication through a relation between predicate leaves and name
leaves.  When a name may stand for nothing, the reading has to say what a
predication of such a name means.  The negative reading (`denotingApplies`) lets a
predicate apply only to what a name denotes, so a predication of a name that denotes
nothing fails: Russell's analysis of denoting phrases ("On Denoting", 1905), the
negative free logics, and the Indian logicians' rule that a reason is unestablished
when its subject is unreal (Dharmakīrti, *Nyāyabindu* III.67).

Under that reading a predication has two negations.  The external one,
`neg (pred P n)`, says that it is not the case that `n` is `P`; the internal one
predicates the complementary predicate, `pred (complement P) n`, that `n` is
non-`P`.  They agree exactly when the name denotes
(`internal_iff_external_iff_isSome`).  On a name that denotes nothing neither the
predicate nor its complement applies, while both external negations hold
(`nondenoting_neither`).

Over an empty domain the quantifiers part in the same way: every universal claim and
its contrary hold, and no existential claim does (`empty_domain_universals`,
`empty_domain_existentials`); a universal claim carries the existential one, as in
the traditional square of opposition, exactly when the domain is inhabited
(`subalternation_iff_nonempty`). -/

namespace Form

universe w

variable {ν : Type u} {π : Type v} {Obj : Type w}

/-- Predication read negatively: a predicate applies to what the name denotes, and a
predication of a name that denotes nothing fails. -/
def denotingApplies (denote : ν → Option Obj) (appliesTo : π → Obj → Prop)
    (predicate : π) (subject : ν) : Prop :=
  ∃ x, denote subject = some x ∧ appliesTo predicate x

variable (denote : ν → Option Obj) (appliesTo : π → Obj → Prop) (same : ν → ν → Prop)
  (complement : π → π)

/-- **Internal and external negation agree exactly when the name denotes.** -/
theorem internal_iff_external_iff_isSome
    (complement_applies : ∀ predicate x,
      appliesTo (complement predicate) x ↔ ¬ appliesTo predicate x)
    (predicate : π) (subject : ν) :
    (Holds (denotingApplies denote appliesTo) same (pred (complement predicate) subject) ↔
        Holds (denotingApplies denote appliesTo) same (neg (pred predicate subject))) ↔
      (denote subject).isSome := by
  simp only [Holds, denotingApplies]
  cases denote subject with
  | none => simp
  | some x => simp [complement_applies]

/-- **On a name that denotes nothing, neither the predicate nor its complement
applies, and both external negations hold.** -/
theorem nondenoting_neither {subject : ν} (nothing : denote subject = none) (predicate : π) :
    ¬ Holds (denotingApplies denote appliesTo) same (pred predicate subject) ∧
      ¬ Holds (denotingApplies denote appliesTo) same (pred (complement predicate) subject) ∧
      Holds (denotingApplies denote appliesTo) same (neg (pred predicate subject)) ∧
      Holds (denotingApplies denote appliesTo) same
        (neg (pred (complement predicate) subject)) := by
  simp [Holds, denotingApplies, nothing]

end Form

/-- **A universal claim carries an existential one exactly on an inhabited
domain.** -/
theorem subalternation_iff_nonempty (α : Sort*) :
    (∀ property : α → Prop, (∀ x, property x) → ∃ x, property x) ↔ Nonempty α :=
  ⟨fun carries => (carries (fun _ => True) fun _ => trivial).elim fun x _ => ⟨x⟩,
    fun ⟨x⟩ _ all => ⟨x, all x⟩⟩

/-- Over an empty domain every universal claim and its contrary hold. -/
theorem empty_domain_universals {α : Sort*} [IsEmpty α] (property : α → Prop) :
    (∀ x, property x) ∧ ∀ x, ¬ property x :=
  ⟨fun x => isEmptyElim x, fun x => isEmptyElim x⟩

/-- Over an empty domain no existential claim holds. -/
theorem empty_domain_existentials {α : Sort*} [IsEmpty α] (property : α → Prop) :
    (¬ ∃ x, property x) ∧ ¬ ∃ x, ¬ property x :=
  ⟨fun ⟨x, _⟩ => isEmptyElim x, fun ⟨x, _⟩ => isEmptyElim x⟩

/-- Over an inhabited domain a universal claim and its contrary exclude each
other. -/
theorem universal_contraries_exclusive {α : Sort*} [Nonempty α] (property : α → Prop) :
    ¬ ((∀ x, property x) ∧ ∀ x, ¬ property x) := by
  rintro ⟨all, none⟩
  obtain ⟨x⟩ := ‹Nonempty α›
  exact none x (all x)

namespace DenotationControl

/-- Two names: `socrates` denotes the one object, `pegasus` denotes nothing. -/
inductive Name
  | socrates
  | pegasus

def denote : Name → Option Unit
  | .socrates => some ()
  | .pegasus => none

/-- One predicate, `wise`, applying to the object; `unwise` is its complement. -/
def appliesTo : Bool → Unit → Prop
  | true, _ => True
  | false, _ => False

def complement : Bool → Bool := not

theorem complement_applies (predicate : Bool) (x : Unit) :
    appliesTo (complement predicate) x ↔ ¬ appliesTo predicate x := by
  cases predicate <;> simp [appliesTo, complement]

/-- Positive control: for `socrates` the two negations of "unwise" agree. -/
theorem socrates_negations_agree :
    Form.Holds (Form.denotingApplies denote appliesTo) (fun _ _ => True)
        (Form.pred (complement false) Name.socrates) ↔
      Form.Holds (Form.denotingApplies denote appliesTo) (fun _ _ => True)
        (Form.neg (Form.pred false Name.socrates)) :=
  (Form.internal_iff_external_iff_isSome denote appliesTo _ complement complement_applies
    false Name.socrates).mpr rfl

/-- Negative control: for `pegasus` they come apart: "Pegasus is not wise" is true
externally, and "Pegasus is unwise" is not. -/
theorem pegasus_negations_differ :
    ¬ (Form.Holds (Form.denotingApplies denote appliesTo) (fun _ _ => True)
          (Form.pred (complement true) Name.pegasus) ↔
        Form.Holds (Form.denotingApplies denote appliesTo) (fun _ _ => True)
          (Form.neg (Form.pred true Name.pegasus))) := by
  rw [Form.internal_iff_external_iff_isSome denote appliesTo _ complement complement_applies]
  simp [denote]

end DenotationControl

end Mettapedia.Logic.Propositions
