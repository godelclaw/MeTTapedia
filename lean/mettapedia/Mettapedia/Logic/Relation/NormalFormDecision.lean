import Mettapedia.Logic.Relation.Normalization
import Mathlib.Algebra.Group.Action.Defs
import Mathlib.Data.Set.Image

/-!
# When conversion is decided by normal forms

A checker that compares two terms by reducing both to normal form and testing
the results for syntactic equality decides the conversion of its reduction
relation only under conditions on that relation.  This module states the
conditions for an arbitrary relation `r` and an arbitrary set `S` of elements
on which the comparison is made (for a typed calculus, the typed terms).

`DecidedOn r S`: every element of `S` reduces to a normal element, and two
elements of `S` are convertible exactly when their normal forms are equal,
whichever normal forms are chosen.

* **Characterization.**  Conversion on `S` is decided by normal forms exactly
  when every element of `S` has a normal form and convertible normal forms of
  elements of `S` are equal (`decidedOn_iff_uniqueNormalForms`); on a set closed
  under steps, exactly when every element has a normal form and convertible
  elements have a common reduct (`decidedOn_iff_churchRosser`).  A confluent
  relation decides its conversion on every set on which it normalizes
  (`decidedOn_of_confluent`), and then every normalization strategy computes
  the same normal form (`DecidedOn.normalForm_unique`).  These are the
  classical facts behind checking conversion by normalization (Newman 1942,
  Huet 1980; Terese 2003, Section 1.2).
* **The symmetry obstruction.**  A map of elements that sends steps to steps,
  with a left inverse that also sends steps to steps (a renaming of variables,
  for terms), sends normal forms to normal forms (`IsNormalFormOf.map`).  So
  when conversion is decided by normal forms, the normal form of an element
  whose class the map preserves is fixed by the map
  (`DecidedOn.map_normalForm_eq`).  A class that the map preserves and that
  contains no element fixed by the map has no decision by normal forms, for
  any relation the map respects (`not_decidedOn_of_symmetric_class`).  For a
  group acting by step-preserving maps: the normal form of an element is fixed
  by every group element that preserves its class
  (`DecidedOn.smul_normalForm_eq`).  The standard instance is commutativity:
  the class of `x + y` is preserved by exchanging `x` and `y`, and neither
  `x + y` nor `y + x` is fixed (`Mettapedia.GSLT.Dedukti.Commutativity`).

No termination is assumed anywhere: normal forms are required to exist on `S`
only, and the decision is a statement about the normal forms that exist.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.Relation

open _root_.Relation

universe u v

variable {α : Type u} {r : α → α → Prop}

/-! ## Definitions -/

/-- `target` is a normal form of `source`: a normal element that `source`
reduces to. -/
def IsNormalFormOf (r : α → α → Prop) (source target : α) : Prop :=
  ReflTransGen r source target ∧ IsNormal r target

/-- Every element of `S` has a normal form. -/
def WeaklyNormalizingOn (r : α → α → Prop) (S : Set α) : Prop :=
  ∀ a ∈ S, ∃ n, IsNormalFormOf r a n

/-- Convertible elements of `S` have a common reduct. -/
def ChurchRosserOn (r : α → α → Prop) (S : Set α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, EqvGen r a b → Join (ReflTransGen r) a b

/-- Convertible normal forms of elements of `S` are equal. -/
def UniqueNormalFormsOn (r : α → α → Prop) (S : Set α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ n m, IsNormalFormOf r a n → IsNormalFormOf r b m → EqvGen r n m → n = m

/-- `S` is closed under steps. -/
def StepClosed (r : α → α → Prop) (S : Set α) : Prop :=
  ∀ ⦃a b : α⦄, a ∈ S → r a b → b ∈ S

/-- **Conversion on `S` is decided by normal forms**: every element of `S` has
a normal form, and two elements of `S` are convertible exactly when their
normal forms are equal, for every choice of the normal forms. -/
def DecidedOn (r : α → α → Prop) (S : Set α) : Prop :=
  WeaklyNormalizingOn r S ∧
    ∀ a ∈ S, ∀ b ∈ S, ∀ n m, IsNormalFormOf r a n → IsNormalFormOf r b m →
      (EqvGen r a b ↔ n = m)

/-! ## Basic facts -/

theorem IsNormalFormOf.eqvGen {a n : α} (normalForm : IsNormalFormOf r a n) : EqvGen r a n :=
  EqvGen.reflTransGen_le_eqvGen r _ _ normalForm.1

theorem StepClosed.reflTransGen {S : Set α} (closed : StepClosed r S) {a b : α} (member : a ∈ S)
    (steps : ReflTransGen r a b) : b ∈ S := by
  induction steps with
  | refl => exact member
  | tail _ step ih => exact closed ih step

/-- Under a decision by normal forms, the normal form of an element of `S` is
unique: every normalization strategy computes the same one. -/
theorem DecidedOn.normalForm_unique {S : Set α} (decided : DecidedOn r S) {a n m : α}
    (member : a ∈ S) (first : IsNormalFormOf r a n) (second : IsNormalFormOf r a m) : n = m :=
  (decided.2 a member a member n m first second).mp (EqvGen.refl a)

/-! ## Characterization -/

/-- **Decision by normal forms is weak normalization with unique normal forms.** -/
theorem decidedOn_iff_uniqueNormalForms {S : Set α} :
    DecidedOn r S ↔ WeaklyNormalizingOn r S ∧ UniqueNormalFormsOn r S := by
  constructor
  · rintro ⟨normalizing, decides⟩
    refine ⟨normalizing, fun a memberA b memberB n m normalA normalB converted => ?_⟩
    exact (decides a memberA b memberB n m normalA normalB).mp
      (EqvGen.trans _ _ _ normalA.eqvGen
        (EqvGen.trans _ _ _ converted (EqvGen.symm _ _ normalB.eqvGen)))
  · rintro ⟨normalizing, unique⟩
    refine ⟨normalizing, fun a memberA b memberB n m normalA normalB => ⟨fun converted => ?_, ?_⟩⟩
    · exact unique a memberA b memberB n m normalA normalB
        (EqvGen.trans _ _ _ (EqvGen.symm _ _ normalA.eqvGen)
          (EqvGen.trans _ _ _ converted normalB.eqvGen))
    · rintro rfl
      exact EqvGen.trans _ _ _ normalA.eqvGen (EqvGen.symm _ _ normalB.eqvGen)

/-- A decision by normal forms gives a common reduct to convertible elements. -/
theorem DecidedOn.churchRosserOn {S : Set α} (decided : DecidedOn r S) : ChurchRosserOn r S := by
  intro a memberA b memberB converted
  obtain ⟨n, normalA⟩ := decided.1 a memberA
  obtain ⟨m, normalB⟩ := decided.1 b memberB
  have same := (decided.2 a memberA b memberB n m normalA normalB).mp converted
  subst same
  exact ⟨n, normalA.1, normalB.1⟩

/-- **On a set closed under steps, decision by normal forms is weak
normalization with the Church–Rosser property.** -/
theorem decidedOn_iff_churchRosser {S : Set α} (closed : StepClosed r S) :
    DecidedOn r S ↔ WeaklyNormalizingOn r S ∧ ChurchRosserOn r S := by
  refine ⟨fun decided => ⟨decided.1, decided.churchRosserOn⟩, ?_⟩
  rintro ⟨normalizing, churchRosser⟩
  refine decidedOn_iff_uniqueNormalForms.mpr ⟨normalizing, ?_⟩
  intro a memberA b memberB n m normalA normalB converted
  obtain ⟨common, fromN, fromM⟩ := churchRosser n (closed.reflTransGen memberA normalA.1)
    m (closed.reflTransGen memberB normalB.1) converted
  exact (normalA.2.reflTransGen_eq fromN).symm.trans (normalB.2.reflTransGen_eq fromM)

/-- **A confluent relation decides its conversion by normal forms wherever it
normalizes.** -/
theorem decidedOn_of_confluent {S : Set α} (confluent : Confluent r)
    (normalizing : WeaklyNormalizingOn r S) : DecidedOn r S := by
  refine decidedOn_iff_uniqueNormalForms.mpr ⟨normalizing, ?_⟩
  intro _ _ _ _ n m normalA normalB converted
  obtain ⟨common, fromN, fromM⟩ := confluent.eqvGen_iff_join.mp converted
  exact (normalA.2.reflTransGen_eq fromN).symm.trans (normalB.2.reflTransGen_eq fromM)

/-- Under confluence, an element has at most one normal form, and two
elements with normal forms are convertible exactly when the normal forms are
equal. -/
theorem conv_iff_normalForm_eq_of_confluent (confluent : Confluent r) {a b n m : α}
    (normalA : IsNormalFormOf r a n) (normalB : IsNormalFormOf r b m) :
    EqvGen r a b ↔ n = m :=
  (decidedOn_of_confluent (S := {a, b}) confluent (by
    rintro x (rfl | rfl)
    · exact ⟨n, normalA⟩
    · exact ⟨m, normalB⟩)).2 a (Or.inl rfl) b (Or.inr rfl) n m normalA normalB

/-! ## The symmetry obstruction -/

section Symmetry

variable {π σ : α → α}

/-- A map with a step-preserving left inverse sends normal elements to normal
elements. -/
theorem IsNormal.map (back : ∀ a, σ (π a) = a) (σSteps : ∀ a b, r a b → r (σ a) (σ b))
    {n : α} (normal : IsNormal r n) : IsNormal r (π n) := by
  intro target step
  have stepped := σSteps _ _ step
  rw [back] at stepped
  exact normal _ stepped

/-- **A step-preserving map with a step-preserving left inverse sends normal
forms to normal forms.** -/
theorem IsNormalFormOf.map (back : ∀ a, σ (π a) = a) (πSteps : ∀ a b, r a b → r (π a) (π b))
    (σSteps : ∀ a b, r a b → r (σ a) (σ b)) {a n : α} (normalForm : IsNormalFormOf r a n) :
    IsNormalFormOf r (π a) (π n) :=
  ⟨normalForm.1.lift π fun _ _ step => πSteps _ _ step, normalForm.2.map back σSteps⟩

/-- A step-preserving map preserves conversion. -/
theorem EqvGen.map_of_steps (πSteps : ∀ a b, r a b → r (π a) (π b)) {a b : α}
    (converted : EqvGen r a b) : EqvGen r (π a) (π b) := by
  induction converted with
  | rel _ _ step => exact EqvGen.rel _ _ (πSteps _ _ step)
  | refl => exact EqvGen.refl _
  | symm _ _ _ ih => exact EqvGen.symm _ _ ih
  | trans _ _ _ _ _ first second => exact EqvGen.trans _ _ _ first second

/-- **The normal form of an element whose class a symmetry preserves is fixed
by the symmetry**, when conversion is decided by normal forms. -/
theorem DecidedOn.map_normalForm_eq {S : Set α} (decided : DecidedOn r S)
    (back : ∀ a, σ (π a) = a) (πSteps : ∀ a b, r a b → r (π a) (π b))
    (σSteps : ∀ a b, r a b → r (σ a) (σ b)) {a n : α} (member : a ∈ S) (mapped : π a ∈ S)
    (normalForm : IsNormalFormOf r a n) (preserved : EqvGen r (π a) a) : π n = n :=
  (decided.2 (π a) mapped a member (π n) n (normalForm.map back πSteps σSteps) normalForm).mp
    preserved

/-- **A class that a symmetry preserves and that has no fixed member is not
decided by normal forms**, for any relation the symmetry respects. -/
theorem not_decidedOn_of_symmetric_class {S : Set α} (back : ∀ a, σ (π a) = a)
    (πSteps : ∀ a b, r a b → r (π a) (π b)) (σSteps : ∀ a b, r a b → r (σ a) (σ b)) {a : α}
    (member : a ∈ S) (mapped : π a ∈ S) (preserved : EqvGen r (π a) a)
    (noFixed : ∀ c, EqvGen r a c → π c ≠ c) : ¬ DecidedOn r S := by
  intro decided
  obtain ⟨n, normalForm⟩ := decided.1 a member
  exact noFixed n normalForm.eqvGen
    (decided.map_normalForm_eq back πSteps σSteps member mapped normalForm preserved)

/-- With confluence alone: an element whose class a symmetry preserves, and
whose class has no fixed member, has no normal form at all. -/
theorem no_normalForm_of_symmetric_class (confluent : Confluent r) (back : ∀ a, σ (π a) = a)
    (πSteps : ∀ a b, r a b → r (π a) (π b)) (σSteps : ∀ a b, r a b → r (σ a) (σ b)) {a : α}
    (preserved : EqvGen r (π a) a) (noFixed : ∀ c, EqvGen r a c → π c ≠ c) :
    ∀ n, ¬ IsNormalFormOf r a n := by
  intro n normalForm
  have decided : DecidedOn r {a, π a} := decidedOn_of_confluent confluent (by
    rintro x (rfl | rfl)
    · exact ⟨n, normalForm⟩
    · exact ⟨π n, normalForm.map back πSteps σSteps⟩)
  exact not_decidedOn_of_symmetric_class back πSteps σSteps (S := {a, π a}) (Or.inl rfl)
    (Or.inr rfl) preserved noFixed decided

end Symmetry

section GroupAction

variable {G : Type v} [Group G] [MulAction G α]

/-- **Normal forms are equivariant**: a group acting by step-preserving maps
sends a normal form of an element to a normal form of its image. -/
theorem IsNormalFormOf.smul (equivariant : ∀ (g : G) a b, r a b → r (g • a) (g • b)) (g : G)
    {a n : α} (normalForm : IsNormalFormOf r a n) : IsNormalFormOf r (g • a) (g • n) :=
  normalForm.map (π := (g • ·)) (σ := (g⁻¹ • ·)) (fun a => inv_smul_smul g a)
    (equivariant g) (equivariant g⁻¹)

/-- **The stabilizer of a class fixes its normal form**, when conversion is
decided by normal forms on a set closed under the action. -/
theorem DecidedOn.smul_normalForm_eq {S : Set α} (decided : DecidedOn r S)
    (equivariant : ∀ (g : G) a b, r a b → r (g • a) (g • b)) (invariant : ∀ (g : G), ∀ a ∈ S, g • a ∈ S)
    {a n : α} (member : a ∈ S) (normalForm : IsNormalFormOf r a n) {g : G}
    (preserved : EqvGen r (g • a) a) : g • n = n :=
  decided.map_normalForm_eq (π := (g • ·)) (σ := (g⁻¹ • ·)) (fun a => inv_smul_smul g a)
    (equivariant g) (equivariant g⁻¹) member (invariant g a member) normalForm preserved

end GroupAction

/-! ## Deciding up to a built-in equivalence -/

/-- **Conversion is decided by normal forms up to `E`** on `S`: every element
of `S` has a normal form, and two elements of `S` are convertible under the
steps and `E` together exactly when their normal forms are related by `E`.
This is how rewriting modulo a theory (associativity and commutativity, for
instance) decides conversion. -/
def DecidedModuloOn (r : α → α → Prop) (E : α → α → Prop) (S : Set α) : Prop :=
  WeaklyNormalizingOn r S ∧
    ∀ a ∈ S, ∀ b ∈ S, ∀ n m, IsNormalFormOf r a n → IsNormalFormOf r b m →
      (EqvGen (fun x y => r x y ∨ E x y) a b ↔ E n m)

/-- **Deciding by normal forms is deciding up to syntactic equality**: the
comparison of a checker that compares normal forms syntactically is the case
of the least built-in equivalence. -/
theorem decidedOn_iff_decidedModuloOn_eq {S : Set α} :
    DecidedOn r S ↔ DecidedModuloOn r (· = ·) S := by
  have same : ∀ a b : α, EqvGen (fun x y => r x y ∨ x = y) a b ↔ EqvGen r a b := by
    intro a b
    constructor
    · intro converted
      induction converted with
      | rel _ _ step => exact step.elim (EqvGen.rel _ _) (fun same => same ▸ EqvGen.refl _)
      | refl => exact EqvGen.refl _
      | symm _ _ _ ih => exact EqvGen.symm _ _ ih
      | trans _ _ _ _ _ first second => exact EqvGen.trans _ _ _ first second
    · intro converted
      exact EqvGen.mono (fun _ _ step => Or.inl step) _ _ converted
  constructor
  · rintro ⟨normalizing, decides⟩
    exact ⟨normalizing, fun a memberA b memberB n m normalA normalB =>
      (same a b).trans (decides a memberA b memberB n m normalA normalB)⟩
  · rintro ⟨normalizing, decides⟩
    exact ⟨normalizing, fun a memberA b memberB n m normalA normalB =>
      (same a b).symm.trans (decides a memberA b memberB n m normalA normalB)⟩

/-! ## Transport along a translation -/

section Transport

variable {β : Type v} {r' : β → β → Prop}

/-- **Transport of a decision along a translation.**  Let a translation `φ`
carry a source relation `finer` into target conversion, and let target
conversion of translations imply a source relation `coarser`.  If the target
decides its conversion by normal forms on the translations of `S`, then for
two elements of `S`, `finer` implies that the target normal forms of their
translations are equal, and equality of those normal forms implies
`coarser`.  When `finer` and `coarser` are one relation, the target's normal
forms decide it. -/
theorem DecidedOn.transport {S : Set α} (φ : α → β) {finer coarser : α → α → Prop}
    (preserves : ∀ a b, finer a b → EqvGen r' (φ a) (φ b))
    (reflects : ∀ a b, EqvGen r' (φ a) (φ b) → coarser a b) (decided : DecidedOn r' (φ '' S))
    {a b : α} (memberA : a ∈ S) (memberB : b ∈ S) {n m : β}
    (normalA : IsNormalFormOf r' (φ a) n) (normalB : IsNormalFormOf r' (φ b) m) :
    (finer a b → n = m) ∧ (n = m → coarser a b) := by
  have decides := decided.2 (φ a) ⟨a, memberA, rfl⟩ (φ b) ⟨b, memberB, rfl⟩ n m normalA normalB
  exact ⟨fun related => decides.mp (preserves a b related),
    fun same => reflects a b (decides.mpr same)⟩

/-- **A simulation carries weak normalization to the image.**  A translation
that sends each step to a reduction, and each normal form of an element of `S`
to an element with a normal form, makes the target weakly normalizing on the
image of a weakly normalizing set; with target confluence the image is decided
by normal forms. -/
theorem decidedOn_image_of_simulation {S : Set α} (φ : α → β)
    (simulates : ∀ a a', r a a' → ReflTransGen r' (φ a) (φ a'))
    (normalizes : ∀ a ∈ S, ∀ n, IsNormalFormOf r a n → ∃ m, IsNormalFormOf r' (φ n) m)
    (confluent : Confluent r') (normalizing : WeaklyNormalizingOn r S) :
    DecidedOn r' (φ '' S) := by
  refine decidedOn_of_confluent confluent ?_
  rintro _ ⟨a, member, rfl⟩
  obtain ⟨n, normalA⟩ := normalizing a member
  obtain ⟨m, normalImage⟩ := normalizes a member n normalA
  have carried : ReflTransGen r' (φ a) (φ n) :=
    normalA.1.lift' φ fun _ _ step => simulates _ _ step
  exact ⟨m, carried.trans normalImage.1, normalImage.2⟩

end Transport

#print axioms decidedOn_iff_uniqueNormalForms
#print axioms decidedOn_iff_churchRosser
#print axioms decidedOn_of_confluent
#print axioms DecidedOn.normalForm_unique
#print axioms DecidedOn.map_normalForm_eq
#print axioms not_decidedOn_of_symmetric_class
#print axioms no_normalForm_of_symmetric_class
#print axioms DecidedOn.smul_normalForm_eq
#print axioms decidedOn_iff_decidedModuloOn_eq
#print axioms DecidedOn.transport
#print axioms decidedOn_image_of_simulation

end Mettapedia.Logic.Relation
