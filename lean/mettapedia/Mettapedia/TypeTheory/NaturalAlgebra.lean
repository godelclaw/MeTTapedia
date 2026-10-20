import Mettapedia.TypeTheory.InductionRecursionBoundary
import Mathlib.Logic.Equiv.Defs

/-!
# Initial successor algebras and representation-independent recursion

A successor algebra has a distinguished element and a unary operation. Its
initiality is the existence of exactly one homomorphism to every target
algebra. The target universe is explicit in `IsInitial`; the comparison
construction uses its four relevant universe instances.

A bijective natural representation proves initiality using the already
constructed natural fold. Comparisons are then constructed from the universal
property, and only afterwards identified with the original representations.
Selected inverses and universal maps are noncomputable; this module does not
claim to provide executable decoders for quotient-valued representations.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.NaturalAlgebra

open InductionRecursionBoundary

universe u v w

structure Algebra (α : Type u) where
  zero : α
  succ : α → α

structure Hom {α : Type u} {β : Type v} (A : Algebra α) (B : Algebra β) where
  toFun : α → β
  map_zero : toFun A.zero = B.zero
  map_succ : ∀ value, toFun (A.succ value) = B.succ (toFun value)

namespace Hom

variable {α : Type u} {β : Type v} {γ : Type w}
variable {A : Algebra α} {B : Algebra β} {C : Algebra γ}

instance : CoeFun (Hom A B) (fun _ => α → β) := ⟨Hom.toFun⟩

@[ext] theorem ext {f g : Hom A B} (same : ∀ value, f value = g value) : f = g := by
  cases f
  cases g
  simp_all only [mk.injEq, funext_iff]
  intro _
  trivial

def id (A : Algebra α) : Hom A A where
  toFun := fun value => value
  map_zero := rfl
  map_succ := fun _ => rfl

def comp (g : Hom B C) (f : Hom A B) : Hom A C where
  toFun := fun value => g (f value)
  map_zero := by rw [f.map_zero, g.map_zero]
  map_succ := fun value => by rw [f.map_succ, g.map_succ]

@[simp] theorem id_apply (value : α) : id A value = value := rfl
@[simp] theorem comp_apply (g : Hom B C) (f : Hom A B) (value : α) :
    comp g f value = g (f value) := rfl

end Hom

structure Iso {α : Type u} {β : Type v} (A : Algebra α) (B : Algebra β) where
  toEquiv : α ≃ β
  map_zero : toEquiv A.zero = B.zero
  map_succ : ∀ value, toEquiv (A.succ value) = B.succ (toEquiv value)

namespace Iso

variable {α : Type u} {β : Type v} {γ : Type w}
variable {A : Algebra α} {B : Algebra β} {C : Algebra γ}

def toHom (e : Iso A B) : Hom A B := ⟨e.toEquiv, e.map_zero, e.map_succ⟩

def symm (e : Iso A B) : Iso B A where
  toEquiv := e.toEquiv.symm
  map_zero := by apply e.toEquiv.injective; simp [e.map_zero]
  map_succ := fun value => by
    apply e.toEquiv.injective
    simp only [Equiv.apply_symm_apply, e.map_succ]

def trans (e : Iso A B) (f : Iso B C) : Iso A C where
  toEquiv := e.toEquiv.trans f.toEquiv
  map_zero := by change f.toEquiv (e.toEquiv A.zero) = _; rw [e.map_zero, f.map_zero]
  map_succ := fun value => by
    change f.toEquiv (e.toEquiv (A.succ value)) = _
    rw [e.map_succ, f.map_succ]
    rfl

@[ext] theorem ext {e f : Iso A B} (same : ∀ value, e.toEquiv value = f.toEquiv value) :
    e = f := by
  have sameEquiv : e.toEquiv = f.toEquiv := Equiv.ext same
  cases e
  cases f
  simp_all

end Iso

/-- Universal recursion, with uniqueness, into every algebra in the target
universe. Different target universes give instances of the same property. -/
def IsInitial {α : Type u} (A : Algebra α) : Prop :=
  ∀ {β : Type v} (B : Algebra β), Nonempty (Unique (Hom A B))

noncomputable def initialHom {α : Type u} {β : Type v} {A : Algebra α}
    (initial : IsInitial.{u, v} A) (B : Algebra β) : Hom A B :=
  (Classical.choice (initial B)).default

theorem initialHom_unique {α : Type u} {β : Type v} {A : Algebra α}
    (initial : IsInitial.{u, v} A) (B : Algebra β) (f : Hom A B) :
    f = initialHom initial B :=
  (Classical.choice (initial B)).uniq f

/-- The mutually selected universal maps are inverse because their composites
are endomorphisms of initial objects. No encoding is used in this construction. -/
noncomputable def isoOfInitial {α : Type u} {β : Type v}
    {A : Algebra α} {B : Algebra β}
    (aToB : IsInitial.{u, v} A) (bToA : IsInitial.{v, u} B)
    (aToA : IsInitial.{u, u} A) (bToB : IsInitial.{v, v} B) : Iso A B where
  toEquiv :=
    { toFun := initialHom aToB B
      invFun := initialHom bToA A
      left_inv := fun value => by
        have same : Hom.comp (initialHom bToA A) (initialHom aToB B) = Hom.id A :=
          (initialHom_unique aToA A _).trans (initialHom_unique aToA A _).symm
        exact congrArg (fun f : Hom A A => f value) same
      right_inv := fun value => by
        have same : Hom.comp (initialHom aToB B) (initialHom bToA A) = Hom.id B :=
          (initialHom_unique bToB B _).trans (initialHom_unique bToB B _).symm
        exact congrArg (fun f : Hom B B => f value) same }
  map_zero := (initialHom aToB B).map_zero
  map_succ := (initialHom aToB B).map_succ

theorem isoOfInitial_unique {α : Type u} {β : Type v}
    {A : Algebra α} {B : Algebra β}
    (aToB : IsInitial.{u, v} A) (bToA : IsInitial.{v, u} B)
    (aToA : IsInitial.{u, u} A) (bToB : IsInitial.{v, v} B)
    (comparison : Iso A B) : comparison = isoOfInitial aToB bToA aToA bToB := by
  apply Iso.ext
  intro value
  exact congrArg (fun f : Hom A B => f value)
    (initialHom_unique aToB B comparison.toHom)

def natAlgebra : Algebra Nat := ⟨0, Nat.succ⟩

def natFoldHom {β : Type v} (B : Algebra β) : Hom natAlgebra B where
  toFun := natFold B.zero B.succ
  map_zero := rfl
  map_succ := fun _ => rfl

theorem nat_initial : IsInitial.{0, v} natAlgebra := by
  intro β B
  refine ⟨{ default := natFoldHom B, uniq := ?_ }⟩
  intro f
  apply Hom.ext
  exact congrFun (natFold_unique B.zero B.succ f f.map_zero f.map_succ)

/-- A faithful finite-successor representation. Unlike predicate induction
alone, bijectivity also excludes cycles and collapsed constructors. -/
structure Representation {α : Type u} (A : Algebra α) where
  encode : Nat → α
  bijective : Function.Bijective encode
  map_zero : encode 0 = A.zero
  map_succ : ∀ count, encode (count + 1) = A.succ (encode count)

namespace Representation

variable {α : Type u} {A : Algebra α}

noncomputable def equiv (representation : Representation A) : Nat ≃ α :=
  Equiv.ofBijective representation.encode representation.bijective

def encodeHom (representation : Representation A) : Hom natAlgebra A :=
  ⟨representation.encode, representation.map_zero, representation.map_succ⟩

noncomputable def presentationIso (representation : Representation A) : Iso natAlgebra A where
  toEquiv := representation.equiv
  map_zero := representation.map_zero
  map_succ := representation.map_succ

noncomputable def foldHom (representation : Representation A)
    {β : Type v} (B : Algebra β) : Hom A B :=
  Hom.comp (natFoldHom B) representation.presentationIso.symm.toHom

@[simp] theorem foldHom_encode (representation : Representation A)
    {β : Type v} (B : Algebra β) (count : Nat) :
    representation.foldHom B (representation.encode count) = natFold B.zero B.succ count := by
  change natFold B.zero B.succ (representation.equiv.symm (representation.equiv count)) = _
  rw [Equiv.symm_apply_apply]

theorem initial (representation : Representation A) : IsInitial.{u, v} A := by
  intro β B
  refine ⟨{ default := representation.foldHom B, uniq := ?_ }⟩
  intro f
  apply Hom.ext
  intro value
  obtain ⟨count, rfl⟩ := representation.bijective.2 value
  rw [foldHom_encode]
  exact congrFun (natFold_unique B.zero B.succ
    (fun n => f (representation.encode n))
    (by rw [representation.map_zero, f.map_zero])
    (fun n => by rw [representation.map_succ, f.map_succ])) count

/-- The comparison is chosen by initiality, not defined as the encoding. -/
noncomputable def canonicalIso (representation : Representation A) : Iso natAlgebra A :=
  isoOfInitial nat_initial representation.initial nat_initial representation.initial

theorem canonicalIso_encode (representation : Representation A) (count : Nat) :
    representation.canonicalIso.toEquiv count = representation.encode count := by
  exact (congrArg (fun f : Hom natAlgebra A => f count)
    (initialHom_unique nat_initial A representation.encodeHom)).symm

theorem canonicalIso_eq_presentationIso (representation : Representation A) :
    representation.canonicalIso = representation.presentationIso := by
  apply Iso.ext
  exact representation.canonicalIso_encode

end Representation

namespace Controls

def booleanAlgebra : Algebra Bool := ⟨false, Bool.not⟩

/-- Genuine induction and even injective successor do not imply initiality. -/
theorem boolean_not_initial : ¬ IsInitial.{0, 0} booleanAlgebra := by
  intro initial
  let f := initialHom initial natAlgebra
  exact boolean_induction_does_not_admit_height ⟨f, f.map_zero, f.map_succ⟩

theorem initial_natural_height (count : Nat) :
    initialHom nat_initial natAlgebra count = count := by
  exact (congrArg (fun f : Hom natAlgebra natAlgebra => f count)
    (initialHom_unique nat_initial natAlgebra (Hom.id natAlgebra))).symm

end Controls

end Mettapedia.TypeTheory.NaturalAlgebra
