import Mettapedia.Algebra.QuantaleWeakness
import Mathlib.Algebra.Group.End

/-!
# Scalar actions for MetaMo

The action is a monoid action preserving binary joins, exposed through standard
monoid and join homomorphisms. Appraisal and decision specialize this same action.
The stronger order and continuity properties used by applications are separate.
-/

namespace Mettapedia.CognitiveArchitecture.MetaMo

open Mettapedia.Algebra.QuantaleWeakness

/-- A monoid action preserving binary joins. The unit is `1`, which need not be top.
Arbitrary joins, bottom preservation, and scalar monotonicity require further laws. -/
class QModule (Q : Type*) (Θ : Type*)
    [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
    [CompleteLattice Θ] where

  smul : Q → Θ → Θ

  smul_one : ∀ θ : Θ, smul 1 θ = θ

  smul_assoc : ∀ (q₁ q₂ : Q) (θ : Θ), smul (q₁ * q₂) θ = smul q₁ (smul q₂ θ)

  smul_sup : ∀ (q : Q) (θ₁ θ₂ : Θ), smul q (θ₁ ⊔ θ₂) = smul q θ₁ ⊔ smul q θ₂

scoped infixr:73 " • " => QModule.smul

variable {Q : Type*} {Θ : Type*}
  [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
  [CompleteLattice Θ] [QModule Q Θ]

@[simp]
theorem one_smul (θ : Θ) : (1 : Q) • θ = θ := QModule.smul_one θ

theorem mul_smul (q₁ q₂ : Q) (θ : Θ) : (q₁ * q₂) • θ = q₁ • (q₂ • θ) :=
  QModule.smul_assoc q₁ q₂ θ

theorem smul_sup (q : Q) (θ₁ θ₂ : Θ) : q • (θ₁ ⊔ θ₂) = q • θ₁ ⊔ q • θ₂ :=
  QModule.smul_sup q θ₁ θ₂

/-- The scalar action, without registering a competing global `SMul` instance. -/
def scalarAction : Q →* Function.End Θ where
  toFun := QModule.smul
  map_one' := funext QModule.smul_one
  map_mul' q r := funext (QModule.smul_assoc q r)

/-- Composition is the multiplication law of the action homomorphism. -/
theorem scalarAction_comp (q r : Q) :
    (QModule.smul q : Θ → Θ) ∘ QModule.smul r = QModule.smul (q * r) :=
  ((scalarAction (Q := Q) (Θ := Θ)).map_mul q r).symm

/-- Each scalar preserves binary joins; this does not assert bottom preservation. -/
def scalarSupHom (q : Q) : SupHom Θ Θ := ⟨QModule.smul q, QModule.smul_sup q⟩

@[simp] theorem scalarAction_apply (q : Q) (θ : Θ) : scalarAction q θ = q • θ := rfl
@[simp] theorem scalarSupHom_apply (q : Q) (θ : Θ) : scalarSupHom q θ = q • θ := rfl

theorem smul_mono_right (q : Q) {θ₁ θ₂ : Θ} (h : θ₁ ≤ θ₂) : q • θ₁ ≤ q • θ₂ :=
  OrderHomClass.mono (scalarSupHom q) h

theorem smul_smul_comm (q₁ q₂ : Q) (θ : Θ) : q₁ • (q₂ • θ) = q₂ • (q₁ • θ) := by
  rw [← mul_smul, ← mul_smul, mul_comm]

abbrev MotivationalState (Q : Type*) (Θ : Type*)
    [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
    [CompleteLattice Θ] [QModule Q Θ] := Θ

instance selfQModule (Q : Type*) [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q] :
    QModule Q Q where
  smul := (· * ·)
  smul_one θ := one_mul θ
  smul_assoc := mul_assoc
  smul_sup _ _ _ := Quantale.mul_sup_distrib

instance piQModule (Index : Type*) : QModule Q (Index → Θ) where
  smul q state := fun index => q • state index
  smul_one state := by
    funext index
    exact one_smul (state index)
  smul_assoc q₁ q₂ state := by
    funext index
    exact mul_smul q₁ q₂ (state index)
  smul_sup q left right := by
    funext index
    exact smul_sup q (left index) (right index)

@[simp]
theorem pi_smul_apply {Index : Type*} (q : Q) (state : Index → Θ)
    (index : Index) : (q • state) index = q • state index :=
  rfl

/-- Scalar-equivariant maps; preservation of joins is not part of this interface. -/
@[ext]
structure ScalarEquivariantEndo (Q : Type*) (Θ : Type*)
    [CommMonoid Q] [CompleteLattice Q] [IsCommQuantale Q]
    [CompleteLattice Θ] [QModule Q Θ] where

  toFun : Θ → Θ

  map_smul : ∀ (q : Q) (θ : Θ), toFun (q • θ) = q • toFun θ

instance : CoeFun (ScalarEquivariantEndo Q Θ) (fun _ => Θ → Θ) :=
  ⟨ScalarEquivariantEndo.toFun⟩

namespace ScalarEquivariantEndo

def id : ScalarEquivariantEndo Q Θ where
  toFun := _root_.id
  map_smul _ _ := rfl

def comp (g f : ScalarEquivariantEndo Q Θ) : ScalarEquivariantEndo Q Θ where
  toFun := g.toFun ∘ f.toFun
  map_smul q θ := by
    show g (f (q • θ)) = q • g (f θ)
    rw [f.map_smul, g.map_smul]

@[simp]
theorem id_apply (θ : Θ) : (ScalarEquivariantEndo.id : ScalarEquivariantEndo Q Θ) θ = θ := rfl

@[simp]
theorem comp_apply (g f : ScalarEquivariantEndo Q Θ) (θ : Θ) : (g.comp f) θ = g (f θ) := rfl

theorem comp_assoc (h g f : ScalarEquivariantEndo Q Θ) : h.comp (g.comp f) = (h.comp g).comp f := rfl

theorem id_comp (f : ScalarEquivariantEndo Q Θ) : ScalarEquivariantEndo.id.comp f = f := by
  ext θ; rfl

theorem comp_id (f : ScalarEquivariantEndo Q Θ) : f.comp ScalarEquivariantEndo.id = f := by
  ext θ; rfl

end ScalarEquivariantEndo

def smulEndo (q : Q) : ScalarEquivariantEndo Q Θ where
  toFun := fun θ => q • θ
  map_smul q' θ := by
    show q • (q' • θ) = q' • (q • θ)
    exact smul_smul_comm q q' θ

@[simp]
theorem smulEndo_apply (q : Q) (θ : Θ) : smulEndo q θ = q • θ := rfl

theorem smulEndo_comp (q₁ q₂ : Q) :
    (smulEndo q₁ : ScalarEquivariantEndo Q Θ).comp (smulEndo q₂) = smulEndo (q₁ * q₂) := by
  ext θ
  simp only [ScalarEquivariantEndo.comp_apply, smulEndo_apply]
  exact (mul_smul q₁ q₂ θ).symm

theorem smulEndo_comm (q₁ q₂ : Q) :
    (smulEndo q₁ : ScalarEquivariantEndo Q Θ).comp (smulEndo q₂) =
    (smulEndo q₂ : ScalarEquivariantEndo Q Θ).comp (smulEndo q₁) := by
  rw [smulEndo_comp, smulEndo_comp, mul_comm]

end Mettapedia.CognitiveArchitecture.MetaMo
