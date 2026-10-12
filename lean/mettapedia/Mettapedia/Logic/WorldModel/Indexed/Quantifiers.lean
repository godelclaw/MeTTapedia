import Mathlib.Order.GaloisConnection.Basic
import Mathlib.Order.CompleteLattice.Basic
import Mathlib.Order.Hom.CompleteLattice
import Mettapedia.Logic.WorldModel.Indexed.Doctrine

/-!
# Quantifiers along question maps and Beck–Chevalley

Restriction of answer profiles along a world arrow `f` precomposes with the
question map `Q f` and reads evidence back along `E f`.  When the evidence
carries the joins or meets needed, restriction has adjoints on both sides:

* the existential image `existsAlong φ p a' = ⨆ (a with φ a = a'), p a`, left
  adjoint to precomposition (`existsAlong_gc`);
* the universal image `forallAlong φ p a' = ⨅ (a with φ a = a'), p a`, right
  adjoint to precomposition (`forallAlong_gc`);
* with evidence read back along a map `e` that has a lower adjoint `l`, the
  left adjoint of `p' ↦ e ∘ p' ∘ φ` is `p ↦ existsAlong φ (l ∘ p)`
  (`restrict_gc_of_gc`); dually for an upper adjoint.

**Beck–Chevalley.** For a commuting square of question maps that is a weak
pullback, restriction commutes with both quantifiers (`beckChevalley_exists`,
`beckChevalley_forall`).  Without the weak pullback condition it fails
(`beckChevalley_exists_fails_without_weakPullback`).  In the doctrine the
square is the image under the query functor of a commuting square of worlds
(`beckChevalley_exists_doctrine`).
-/

set_option autoImplicit false

open CategoryTheory Opposite

namespace Mettapedia.Logic.WorldModel.Indexed.Quantifiers

universe u v w vB uB

section Along

variable {A : Type u} {A' : Type v} {L : Type w} [CompleteLattice L]

/-- Existential image of a profile along a question map: the join over each
fibre. -/
def existsAlong (φ : A → A') (p : A → L) : A' → L :=
  fun a' => ⨆ (a : A) (_ : φ a = a'), p a

/-- Universal image of a profile along a question map: the meet over each
fibre. -/
def forallAlong (φ : A → A') (p : A → L) : A' → L :=
  fun a' => ⨅ (a : A) (_ : φ a = a'), p a

/-- Every value lies below the existential image at its question's image. -/
theorem le_existsAlong (φ : A → A') (p : A → L) (a : A) : p a ≤ existsAlong φ p (φ a) :=
  le_iSup₂_of_le (f := fun x (_ : φ x = φ a) => p x) a rfl le_rfl

/-- The universal image at a question's image lies below its value. -/
theorem forallAlong_le (φ : A → A') (p : A → L) (a : A) : forallAlong φ p (φ a) ≤ p a :=
  iInf₂_le (f := fun x (_ : φ x = φ a) => p x) a rfl

/-- Existential image is left adjoint to precomposition. -/
theorem existsAlong_gc (φ : A → A') :
    GaloisConnection (existsAlong (L := L) φ) (fun p' : A' → L => p' ∘ φ) := by
  intro p p'
  constructor
  · intro h a
    exact le_trans (le_existsAlong φ p a) (h (φ a))
  · intro h a'
    exact iSup₂_le fun a ha => ha ▸ h a

/-- Universal image is right adjoint to precomposition. -/
theorem forallAlong_gc (φ : A → A') :
    GaloisConnection (fun p' : A' → L => p' ∘ φ) (forallAlong (L := L) φ) := by
  intro p' p
  constructor
  · intro h a'
    exact le_iInf₂ fun a ha => ha ▸ h a
  · intro h a
    exact le_trans (h (φ a)) (forallAlong_le φ p a)

/-- With evidence read back along `e` having a lower adjoint `l`, restriction
`p' ↦ e ∘ p' ∘ φ` has left adjoint `p ↦ existsAlong φ (l ∘ p)`. -/
theorem restrict_gc_of_gc {M : Type*} [CompleteLattice M] {l : M → L} {e : L → M}
    (gc : GaloisConnection l e) (φ : A → A') :
    GaloisConnection (fun p : A → M => existsAlong φ (l ∘ p))
      (fun p' : A' → L => e ∘ p' ∘ φ) := by
  intro p p'
  rw [existsAlong_gc φ]
  exact ⟨fun h a => gc.le_iff_le.mp (h a), fun h a => gc.le_iff_le.mpr (h a)⟩

/-- With evidence read back along `e` having an upper adjoint `r`,
restriction `p' ↦ e ∘ p' ∘ φ` has right adjoint `p ↦ forallAlong φ (r ∘ p)`. -/
theorem restrict_gc_forall_of_gc {M : Type*} [CompleteLattice M] {e : L → M} {r : M → L}
    (gc : GaloisConnection e r) (φ : A → A') :
    GaloisConnection (fun p' : A' → L => e ∘ p' ∘ φ)
      (fun p : A → M => forallAlong φ (r ∘ p)) := by
  intro p' p
  rw [← forallAlong_gc φ]
  exact ⟨fun h a => gc.le_iff_le.mp (h a), fun h a => gc.le_iff_le.mpr (h a)⟩

end Along

section BeckChevalley

variable {A : Type u} {B' : Type u} {C : Type u} {D : Type u} {L : Type w} [CompleteLattice L]

/-- A commuting square of question maps is a weak pullback when every
compatible pair comes from the corner. -/
def WeakPullback (φ : A → C) (ψ : A → B') (κ : C → D) (χ : B' → D) : Prop :=
  ∀ c b, κ c = χ b → ∃ a, φ a = c ∧ ψ a = b

/-- **Beck–Chevalley, existential.** Restricting an existential image along `κ`
is the existential image of the restriction along `ψ`. -/
theorem beckChevalley_exists {φ : A → C} {ψ : A → B'} {κ : C → D} {χ : B' → D}
    (comm : κ ∘ φ = χ ∘ ψ) (pb : WeakPullback φ ψ κ χ) (p : B' → L) :
    existsAlong χ p ∘ κ = existsAlong φ (p ∘ ψ) := by
  funext c
  apply le_antisymm
  · refine iSup₂_le fun b hb => ?_
    obtain ⟨a, rfl, rfl⟩ := pb c b hb.symm
    exact le_existsAlong φ (p ∘ ψ) a
  · refine iSup₂_le fun a ha => ?_
    subst ha
    exact le_iSup₂_of_le (f := fun x (_ : χ x = κ (φ a)) => p x) (ψ a)
      (congrFun comm a).symm le_rfl

/-- **Beck–Chevalley, universal.** -/
theorem beckChevalley_forall {φ : A → C} {ψ : A → B'} {κ : C → D} {χ : B' → D}
    (comm : κ ∘ φ = χ ∘ ψ) (pb : WeakPullback φ ψ κ χ) (p : B' → L) :
    forallAlong χ p ∘ κ = forallAlong φ (p ∘ ψ) := by
  funext c
  apply le_antisymm
  · refine le_iInf₂ fun a ha => ?_
    subst ha
    exact iInf₂_le (f := fun x (_ : χ x = κ (φ a)) => p x) (ψ a) (congrFun comm a).symm
  · refine le_iInf₂ fun b hb => ?_
    obtain ⟨a, rfl, rfl⟩ := pb c b hb.symm
    exact forallAlong_le φ (p ∘ ψ) a

end BeckChevalley

/-- **Negative.** A commuting square that is not a weak pullback: an empty
corner over two points. Beck–Chevalley fails for the top profile. -/
theorem beckChevalley_exists_fails_without_weakPullback :
    ∃ (φ : PEmpty.{1} → PUnit.{1}) (ψ : PEmpty.{1} → PUnit.{1}) (κ : PUnit.{1} → PUnit.{1})
      (χ : PUnit.{1} → PUnit.{1}) (p : PUnit.{1} → Prop),
      κ ∘ φ = χ ∘ ψ ∧ ¬ WeakPullback φ ψ κ χ ∧
        existsAlong (L := Prop) χ p ∘ κ ≠ existsAlong (L := Prop) φ (p ∘ ψ) := by
  refine ⟨PEmpty.elim, PEmpty.elim, id, id, fun _ => True, funext fun a => a.elim, ?_, ?_⟩
  · intro pb
    obtain ⟨a, _⟩ := pb PUnit.unit PUnit.unit rfl
    exact a.elim
  · intro same
    have := congrFun same PUnit.unit
    simp [existsAlong] at this

/-! ## In the doctrine -/

section Doctrine

variable {Bs : Type uB} [Category.{vB} Bs] (Q : Bs ⥤ Type u) {L : Type u} [CompleteLattice L]

/-- **Beck–Chevalley in the doctrine.** For a commuting square of worlds whose
query square is a weak pullback, restricting the existential image is the
existential image of the restriction. -/
theorem beckChevalley_exists_doctrine {a b c d : Bs} {f : a ⟶ c} {g : a ⟶ b} {k : c ⟶ d}
    {h : b ⟶ d} (comm : f ≫ k = g ≫ h)
    (pb : WeakPullback (Q.map f) (Q.map g) (Q.map k) (Q.map h)) (p : Q.obj b → L) :
    existsAlong (Q.map h) p ∘ Q.map k = existsAlong (Q.map f) (p ∘ Q.map g) := by
  refine beckChevalley_exists ?_ pb p
  funext x
  have := congrArg (fun m => Q.map m x) comm
  simpa [Functor.map_comp] using this

/-- **Beck–Chevalley in the doctrine, universal.** -/
theorem beckChevalley_forall_doctrine {a b c d : Bs} {f : a ⟶ c} {g : a ⟶ b} {k : c ⟶ d}
    {h : b ⟶ d} (comm : f ≫ k = g ≫ h)
    (pb : WeakPullback (Q.map f) (Q.map g) (Q.map k) (Q.map h)) (p : Q.obj b → L) :
    forallAlong (Q.map h) p ∘ Q.map k = forallAlong (Q.map f) (p ∘ Q.map g) := by
  refine beckChevalley_forall ?_ pb p
  funext x
  have := congrArg (fun m => Q.map m x) comm
  simpa [Functor.map_comp] using this

/-- With constant evidence the doctrine's restriction is precomposition with the
question map. -/
theorem restrictProfile_const (M : AddCommMonCat.{u}) {b c : Bs} (f : b ⟶ c)
    (p : Q.obj c → M) :
    restrictProfile Q ((Functor.const Bsᵒᵖ).obj M) f p = p ∘ Q.map f := rfl

end Doctrine

end Mettapedia.Logic.WorldModel.Indexed.Quantifiers
