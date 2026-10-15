import Mathlib.Logic.Relation
import Mathlib.Algebra.Group.ULift
import Mathlib.Algebra.Order.Monoid.Canonical.Defs
import Mathlib.Algebra.Order.Group.Nat
import Mettapedia.Logic.WorldModel.Indexed.FixedQueryBridge
import Mettapedia.Logic.WorldModel.Indexed.Survival

/-!
# Graded arrows: what an arrow preserves

An arrow of world models carries a contract: at each world a relation between
the answer the arrow delivers (the target answer, restricted back) and the
answer it must account for (the source answer).  A contract system is one such
relation per world, carried along restriction (`ContractSystem`).

* The exact contract `ContractSystem.exact` is equality; exact-graded arrows are
  the morphisms of the doctrine (`graded_exact_iff`).
* Contracts compose by relational composition, and graded arrows compose with
  the composite grade (`Graded.comp`); the exact contract is the unit
  (`exact_comp`, `comp_exact`) and composition is associative (`comp_assoc`).
* Dominance (an order on evidence) does not keep exact answers: doubling is a
  dominance-graded arrow that is not exact (`doubling_dominance_not_exact`).
* A bounded-excess contract composes by adding bounds (`excess_comp_le`).
* **View equality.** A profile consumer is kept by every arrow graded by a view
  exactly when it factors through the view's additive hull
  `p ↦ (n ↦ v (n • p))` (`kept_by_viewGraded_iff`).  For an additive view the
  hull and the view carry the same information, so the kept consumers are
  exactly those factoring through the view (`kept_by_additive_viewGraded_iff`).
  For a non-additive view this fails: under the threshold view "at least two",
  the consumer "is zero" is kept by every graded arrow but does not factor
  through the view (`threshold_kept_but_not_factorsThrough`).
-/

set_option autoImplicit false

open CategoryTheory Opposite

namespace Mettapedia.Logic.WorldModel.Indexed

universe vB uB u w

section Contracts

variable {B : Type uB} [Category.{vB} B] (P : Bᵒᵖ ⥤ AddCommMonCat.{u})

/-- A contract system: at every world, a relation between the answer an arrow
delivers and the answer it must account for, carried along restriction. -/
structure ContractSystem where
  /-- The relation at a world: delivered answer, required answer. -/
  rel : ∀ b : B, P.obj (op b) → P.obj (op b) → Prop
  /-- Restriction carries the relation. -/
  restrict : ∀ {b c : B} (f : b ⟶ c) {x y : P.obj (op c)}, rel c x y →
    rel b ((P.map f.op).hom x) ((P.map f.op).hom y)

namespace ContractSystem

variable {P}

@[ext] theorem ext {C D : ContractSystem P} (h : C.rel = D.rel) : C = D := by
  cases C
  cases D
  cases h
  rfl

/-- The exact contract: the delivered answer is the required answer. -/
def exact : ContractSystem P where
  rel _ := Eq
  restrict _ _ _ h := h ▸ rfl

/-- Sequential composition: the later arrow's contract, restricted, followed by
the earlier arrow's contract. -/
def comp (D C : ContractSystem P) : ContractSystem P where
  rel b := Relation.Comp (D.rel b) (C.rel b)
  restrict f := fun ⟨_, hD, hC⟩ => ⟨_, D.restrict f hD, C.restrict f hC⟩

theorem exact_comp (C : ContractSystem P) : exact.comp C = C := by
  ext b x y
  exact ⟨fun ⟨_, h, hC⟩ => h ▸ hC, fun hC => ⟨x, rfl, hC⟩⟩

theorem comp_exact (C : ContractSystem P) : C.comp exact = C := by
  ext b x y
  exact ⟨fun ⟨_, hC, h⟩ => h ▸ hC, fun hC => ⟨y, hC, rfl⟩⟩

theorem comp_assoc (E D C : ContractSystem P) : (E.comp D).comp C = E.comp (D.comp C) := by
  ext b x y
  exact ⟨fun ⟨z, ⟨w, hE, hD⟩, hC⟩ => ⟨w, hE, z, hD, hC⟩,
    fun ⟨w, hE, z, hD, hC⟩ => ⟨z, ⟨w, hE, hD⟩, hC⟩⟩

end ContractSystem

/-- A state map over `f` is graded by a contract when the restricted target
answer and the source answer are related by the contract, at every state. -/
def Graded (C : ContractSystem P) {b c : B} (f : b ⟶ c) (X : Over (P.obj (op b)))
    (Y : Over (P.obj (op c))) (h : X.left ⟶ Y.left) : Prop :=
  ∀ W, C.rel b ((h ≫ Y.hom ≫ P.map f.op).hom W) (X.hom.hom W)

variable {P}

/-- Exact-graded arrows are the morphisms of the doctrine. -/
theorem graded_exact_iff {b c : B} (f : b ⟶ c) (X : Over (P.obj (op b)))
    (Y : Over (P.obj (op c))) (h : X.left ⟶ Y.left) :
    Graded P ContractSystem.exact f X Y h ↔ h ≫ Y.hom ≫ P.map f.op = X.hom := by
  constructor
  · intro graded
    ext W
    exact graded W
  · intro w W
    exact congrArg (fun k : X.left ⟶ P.obj (op b) => k.hom W) w

/-- **Graded arrows compose with the composite grade.** -/
theorem Graded.comp {C D : ContractSystem P} {b c d : B} {f : b ⟶ c} {g : c ⟶ d}
    {X : Over (P.obj (op b))} {Y : Over (P.obj (op c))} {Z : Over (P.obj (op d))}
    {h : X.left ⟶ Y.left} {k : Y.left ⟶ Z.left}
    (hh : Graded P C f X Y h) (hk : Graded P D g Y Z k) :
    Graded P (D.comp C) (f ≫ g) X Z (h ≫ k) := by
  intro W
  refine ⟨(h ≫ Y.hom ≫ P.map f.op).hom W, ?_, hh W⟩
  have restricted := D.restrict f (hk (h.hom W))
  simpa [Functor.map_comp] using restricted

/-- Identities are exact. -/
theorem Graded.id {b : B} (X : Over (P.obj (op b))) :
    Graded P ContractSystem.exact (𝟙 b) X X (𝟙 _) := by
  intro W
  simp [ContractSystem.exact]

/-- A contract that a weaker one includes grades every arrow the stronger one
grades. -/
theorem Graded.mono {C D : ContractSystem P} (le : ∀ b x y, C.rel b x y → D.rel b x y)
    {b c : B} {f : b ⟶ c} {X : Over (P.obj (op b))} {Y : Over (P.obj (op c))}
    {h : X.left ⟶ Y.left} (graded : Graded P C f X Y h) : Graded P D f X Y h :=
  fun W => le b _ _ (graded W)

/-- Exact arrows are graded by every reflexive contract. -/
theorem Graded.of_exact {C : ContractSystem P} (refl : ∀ b x, C.rel b x x)
    {b c : B} {f : b ⟶ c} {X : Over (P.obj (op b))} {Y : Over (P.obj (op c))}
    {h : X.left ⟶ Y.left} (graded : Graded P ContractSystem.exact f X Y h) :
    Graded P C f X Y h :=
  fun W => (graded W) ▸ refl b _

end Contracts

/-! ## View equality -/

section Views

variable {B : Type uB} [Category.{vB} B] {P : Bᵒᵖ ⥤ AddCommMonCat.{u}}
variable {b : B} {V : Type w} {Z : Sort*}

/-- An arrow over `f` is graded by a view at the source world when the view of
the restricted target answer is the view of the source answer. -/
def ViewGraded (v : P.obj (op b) → V) {c : B} (f : b ⟶ c) (X : Over (P.obj (op b)))
    (Y : Over (P.obj (op c))) (h : X.left ⟶ Y.left) : Prop :=
  ∀ W, v ((h ≫ Y.hom ≫ P.map f.op).hom W) = v (X.hom.hom W)

/-- A consumer of profiles at `b` is kept by an arrow over `f` when it reads the
same value from the restricted target answer as from the source answer. -/
def KeptBy (k : P.obj (op b) → Z) {c : B} (f : b ⟶ c) (X : Over (P.obj (op b)))
    (Y : Over (P.obj (op c))) (h : X.left ⟶ Y.left) : Prop :=
  ∀ W, k ((h ≫ Y.hom ≫ P.map f.op).hom W) = k (X.hom.hom W)

/-- Restriction along an identity arrow does nothing. -/
theorem map_id_op_apply (x : P.obj (op b)) : (P.map (𝟙 b).op).hom x = x := by
  rw [op_id, P.map_id]
  rfl

/-- The additive hull of a view: the view of every multiple. -/
def additiveHull (v : P.obj (op b) → V) (p : P.obj (op b)) : ℕ → V := fun n => v (n • p)

/-- The free world model on one profile: natural numbers, the `n`-th state
answering `n • p`. -/
def freeOn (p : P.obj (op b)) : Over (P.obj (op b)) :=
  Over.mk (AddCommMonCat.ofHom
      ({ toFun := fun n => n.down • p
         map_zero' := zero_nsmul p
         map_add' := fun m n => add_nsmul p m.down n.down } : ULift.{u} ℕ →+ P.obj (op b)) :
    AddCommMonCat.of (ULift.{u} ℕ) ⟶ P.obj (op b))

/-- **View law.** A profile consumer is kept by every arrow graded by a view
exactly when it factors through the view's additive hull. -/
theorem kept_by_viewGraded_iff (v : P.obj (op b) → V) (k : P.obj (op b) → Z) :
    (∀ (c : B) (f : b ⟶ c) (X : Over (P.obj (op b))) (Y : Over (P.obj (op c)))
        (h : X.left ⟶ Y.left), ViewGraded v f X Y h → KeptBy k f X Y h) ↔
      k.FactorsThrough (additiveHull v) := by
  constructor
  · intro kept p p' sameHull
    have graded : ViewGraded v (𝟙 b) (freeOn p') (freeOn p)
        (𝟙 (AddCommMonCat.of (ULift.{u} ℕ))) := by
      intro W
      change v ((P.map (𝟙 b).op).hom ((freeOn p).hom.hom W)) = v ((freeOn p').hom.hom W)
      rw [map_id_op_apply]
      exact congrFun sameHull W.down
    have := kept b (𝟙 b) (freeOn p') (freeOn p) (𝟙 (AddCommMonCat.of (ULift.{u} ℕ))) graded
      (ULift.up 1)
    change k ((P.map (𝟙 b).op).hom ((freeOn p).hom.hom (ULift.up 1))) =
      k ((freeOn p').hom.hom (ULift.up 1)) at this
    rw [map_id_op_apply] at this
    have one : k ((1 : ℕ) • p) = k ((1 : ℕ) • p') := this
    simpa only [one_smul] using one
  · intro factors c f X Y h graded W
    apply factors
    funext n
    have hn := graded (n • W)
    simpa [additiveHull, map_nsmul] using hn

/-- For an additive view the hull and the view carry the same information. -/
theorem factorsThrough_additiveHull_iff {V : Type w} [AddCommMonoid V]
    (v : P.obj (op b) →+ V) (k : P.obj (op b) → Z) :
    k.FactorsThrough (additiveHull (P := P) (b := b) v) ↔ k.FactorsThrough v := by
  constructor
  · intro factors p p' same
    apply factors
    funext n
    simp [additiveHull, map_nsmul, same]
  · intro factors p p' same
    apply factors
    simpa [additiveHull] using congrFun same 1

/-- **View law for additive views.** A profile consumer is kept by every arrow
graded by an additive view exactly when it factors through the view. -/
theorem kept_by_additive_viewGraded_iff {V : Type w} [AddCommMonoid V]
    (v : P.obj (op b) →+ V) (k : P.obj (op b) → Z) :
    (∀ (c : B) (f : b ⟶ c) (X : Over (P.obj (op b))) (Y : Over (P.obj (op c)))
        (h : X.left ⟶ Y.left), ViewGraded v f X Y h → KeptBy k f X Y h) ↔
      k.FactorsThrough v :=
  (kept_by_viewGraded_iff (v : P.obj (op b) → V) k).trans (factorsThrough_additiveHull_iff v k)

end Views

/-! ## Concrete contracts on counts over the one-world base -/

namespace CountContracts

open FixedQuery

/-- Counts as the answer profile of the one-world base. -/
def countProfiles : Pointᵒᵖ ⥤ AddCommMonCat := (Functor.const _).obj (AddCommMonCat.of ℕ)

/-- The world. -/
abbrev pt : Point := ⟨PUnit.unit⟩

/-- The count model: a count answers itself. -/
def countModel : Over (countProfiles.obj (op pt)) :=
  Over.mk (𝟙 (AddCommMonCat.of ℕ))

/-- Dominance on counts: the delivered answer is at least the required one. -/
def dominance : ContractSystem countProfiles where
  rel _ x y := (show ℕ from y) ≤ (show ℕ from x)
  restrict _ _ _ h := h

/-- Doubling the count. -/
def doubling : countModel.left ⟶ countModel.left :=
  AddCommMonCat.ofHom (AddMonoidHom.mulLeft (2 : ℕ))

/-- **Dominance does not keep exact answers.** Doubling is dominance-graded and
not exact. -/
theorem doubling_dominance_not_exact :
    Graded countProfiles dominance (𝟙 pt) countModel countModel doubling ∧
      ¬ Graded countProfiles ContractSystem.exact (𝟙 pt) countModel countModel doubling := by
  constructor
  · intro W
    show (show ℕ from W) ≤ 2 * (show ℕ from W)
    omega
  · intro exact
    have one := exact (1 : ℕ)
    have : (2 : ℕ) * 1 = 1 := one
    omega

/-- A bounded-excess contract on counts: the delivered answer exceeds the
required one by at most `ε`. -/
def excess (ε : ℕ) : ContractSystem countProfiles where
  rel _ x y := (show ℕ from y) ≤ (show ℕ from x) ∧ (show ℕ from x) ≤ (show ℕ from y) + ε
  restrict _ _ _ h := h

/-- Bounded excesses compose by adding bounds. -/
theorem excess_comp_le (ε δ : ℕ) (b : Point) (x y : countProfiles.obj (op b)) :
    ((excess δ).comp (excess ε)).rel b x y → (excess (ε + δ)).rel b x y := by
  rintro ⟨z, ⟨h1, h2⟩, ⟨h3, h4⟩⟩
  exact ⟨le_trans h3 h1, by omega⟩

/-- The threshold view on counts: "at least two". -/
def threshold (n : ℕ) : Bool := decide (2 ≤ n)

/-- The consumer "is zero". -/
def isZero (n : ℕ) : Bool := decide (n = 0)

/-- **Non-additive views break the naive law.** "Is zero" is kept by every
threshold-graded arrow but does not factor through the threshold view. -/
theorem threshold_kept_but_not_factorsThrough :
    (∀ (c : Point) (f : pt ⟶ c) (X : Over (countProfiles.obj (op pt)))
        (Y : Over (countProfiles.obj (op c))) (h : X.left ⟶ Y.left),
        ViewGraded (fun p : countProfiles.obj (op pt) => threshold p) f X Y h →
          KeptBy (fun p : countProfiles.obj (op pt) => isZero p) f X Y h) ∧
      ¬ (fun p : countProfiles.obj (op pt) => isZero p).FactorsThrough
          (fun p : countProfiles.obj (op pt) => threshold p) := by
  constructor
  · refine (kept_by_viewGraded_iff _ _).2 ?_
    intro p p' same
    have h1 : threshold (1 * (show ℕ from p)) = threshold (1 * (show ℕ from p')) :=
      congrFun same 1
    have h2 : threshold (2 * (show ℕ from p)) = threshold (2 * (show ℕ from p')) :=
      congrFun same 2
    show isZero (show ℕ from p) = isZero (show ℕ from p')
    generalize (show ℕ from p) = n at h1 h2 ⊢
    generalize (show ℕ from p') = n' at h1 h2 ⊢
    unfold threshold isZero at *
    by_cases hn : n = 0 <;> by_cases hn' : n' = 0 <;> simp_all
  · intro factors
    have := factors (a := (0 : ℕ)) (b := (1 : ℕ)) (by decide)
    exact absurd this (by decide)

end CountContracts

end Mettapedia.Logic.WorldModel.Indexed
