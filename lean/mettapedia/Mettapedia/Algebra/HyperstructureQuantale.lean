import Mettapedia.Algebra.Hyperstructure
import Mathlib.Algebra.Order.Quantale
import Mathlib.Order.Hom.CompleteLattice

/-!+# Powerset quantales of associative multivalued operations

The carrier is indexed by the selected operation so its multiplication does
not conflict with Mathlib's pointwise multiplication on ordinary sets.
Associativity is required; totality, a unit and commutativity are not.
Exact maps induce direct-image maps preserving both multiplication and all
suprema. Residuation gives the corresponding universal output condition.
-/

set_option autoImplicit false

namespace Mettapedia.Algebra.HyperOp

universe u v
variable {α : Type u} {β : Type v}

/-- Sets equipped with one specified multivalued multiplication. -/
def Powerset (_op : HyperOp α) := Set α

namespace Powerset

variable {op : HyperOp α}

def ofSet (op : HyperOp α) (values : Set α) : Powerset op := values

def toSet (values : Powerset op) : Set α := values

@[simp] theorem toSet_ofSet (op : HyperOp α) (values : Set α) :
    (ofSet op values).toSet = values := rfl

@[simp] theorem ofSet_toSet (values : Powerset op) :
    ofSet op values.toSet = values := rfl

instance : CompleteLattice (Powerset op) := inferInstanceAs (CompleteLattice (Set α))

instance : Mul (Powerset op) := ⟨op.setExtend⟩

@[simp] theorem toSet_mul (left right : Powerset op) :
    (left * right).toSet = op.setExtend left.toSet right.toSet := rfl

theorem le_iff_subset (left right : Powerset op) :
    left ≤ right ↔ left.toSet ⊆ right.toSet := Iff.rfl

instance [law : Fact op.isAssociative] : Semigroup (Powerset op) where
  mul_assoc := (isAssociative_iff_setExtend op).mp law.out |>.assoc

/-- The extension of an associative hyperoperation distributes over every
union, including the empty union. Empty binary outcomes are permitted. -/
instance [Fact op.isAssociative] : IsQuantale (Powerset op) where
  mul_sSup_distrib values family := by
    rw [sSup_eq_iSup]
    change op.setExtend values.toSet (⋃ member ∈ family, member.toSet) =
      ⋃ member ∈ family, op.setExtend values.toSet member.toSet
    simp only [setExtend_iUnion_right]
  sSup_mul_distrib family values := by
    rw [sSup_eq_iSup]
    change op.setExtend (⋃ member ∈ family, member.toSet) values.toSet =
      ⋃ member ∈ family, op.setExtend member.toSet values.toSet
    simp only [setExtend_iUnion_left]

/-- Recovering the binary law from powerset associativity needs no totality. -/
theorem associative_iff : Std.Associative (HMul.hMul : Powerset op → Powerset op → Powerset op) ↔
    op.isAssociative :=
  (isAssociative_iff_setExtend op).symm

/-- Direct image is the existing Mathlib supremum homomorphism. -/
def directImage {target : HyperOp β} (map : Hom op target) :
    sSupHom (Powerset op) (Powerset target) :=
  sSupHom.setImage map

@[simp] theorem directImage_toSet {target : HyperOp β} (map : Hom op target)
    (values : Powerset op) :
    (directImage map values).toSet = map '' values.toSet := rfl

/-- Exactness on generator pairs extends to exact multiplication of sets. -/
theorem directImage_mul {target : HyperOp β} (map : Hom op target)
    (left right : Powerset op) :
    directImage map (left * right) = directImage map left * directImage map right :=
  map.image_setExtend left right

@[simp] theorem directImage_id (values : Powerset op) :
    directImage (Hom.id op) values = values := Set.image_id _

theorem directImage_comp {middle : HyperOp β} {γ : Type*} {target : HyperOp γ}
    (before : Hom op middle) (after : Hom middle target) (values : Powerset op) :
    directImage (after.comp before) values = directImage after (directImage before values) :=
  (Set.image_image after.toFun before.toFun values).symm

/-- A left factor is below the residual exactly when each of its outputs,
against every supplied right factor, meets the required output predicate. -/
theorem le_leftResidual_iff [Fact op.isAssociative]
    (inputs right allowed : Powerset op) :
    inputs ≤ Quantale.leftMulResiduation right allowed ↔
      ∀ a ∈ inputs.toSet, ∀ b ∈ right.toSet, op a b ⊆ allowed.toSet := by
  rw [Quantale.leftMulResiduation_le_iff_mul_le]
  change op.setExtend inputs right ⊆ allowed ↔ _
  constructor
  · intro bounded a ha b hb x hx
    exact bounded ((mem_setExtend ..).mpr ⟨a, ha, b, hb, hx⟩)
  · intro bounded x hx
    obtain ⟨a, ha, b, hb, hx⟩ := (mem_setExtend ..).mp hx
    exact bounded a ha b hb hx

namespace Controls

local instance : Fact (HyperOp.Controls.choice : HyperOp Bool).isAssociative :=
  ⟨HyperOp.Controls.choice_associative⟩

theorem choice_quantale : IsQuantale (Powerset (HyperOp.Controls.choice : HyperOp Bool)) :=
  inferInstance

theorem choice_residual :
    ofSet HyperOp.Controls.choice ({false, true} : Set Bool) ≤
      Quantale.leftMulResiduation (ofSet HyperOp.Controls.choice {false})
        (ofSet HyperOp.Controls.choice {false, true}) := by
  rw [le_leftResidual_iff]
  intro a ha b hb x hx
  rcases (show x = a ∨ x = b from hx) with rfl | rfl
  · exact ha
  · exact Or.inl hb

/-- A concrete quantale with multiple possible outputs; its multiplication
annihilates the empty set despite coinciding with union on nonempty factors. -/
theorem choice_product :
    (ofSet HyperOp.Controls.choice {false} * ofSet HyperOp.Controls.choice {true}).toSet =
      ({false, true} : Set Bool) :=
  setExtend_singletons _ _ _

theorem choice_empty_product :
    (ofSet HyperOp.Controls.choice {false} * ⊥).toSet = (∅ : Set Bool) :=
  setExtend_empty_right _ _

/-- Possibility multiplication is not ordinary union on all inputs. -/
theorem choice_product_not_union :
    (ofSet HyperOp.Controls.choice {false} * ⊥).toSet ≠ ({false} ∪ ∅ : Set Bool) := by
  rw [choice_empty_product]
  simp

end Controls
end Powerset
end Mettapedia.Algebra.HyperOp
