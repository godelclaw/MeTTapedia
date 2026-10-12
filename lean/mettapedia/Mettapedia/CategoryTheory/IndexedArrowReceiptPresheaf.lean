import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Types.Basic

/-!+# Origin-retaining presheaves of independently supplied arrows

A receipt consists of its authored index and a complete generalized argument
in that index's domain. Restriction precomposes that argument. Evaluation
uses the independently supplied indexed arrows; its naturality retains the
entire argument and origin before projecting to the resulting arrow.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.CategoryTheory.IndexedArrowReceiptPresheaf

open _root_.CategoryTheory Opposite

universe u v i w

variable {C : Type u} [Category.{v} C] {Index : Type i}
variable (domains : Index → C)

def receipts : Cᵒᵖ ⥤ Type (max i v w) where
  obj stage := Σ origin : Index, ULift.{max i w} (stage.unop ⟶ domains origin)
  map change := ↾fun receipt => ⟨receipt.1, ULift.up (change.unop ≫ receipt.2.down)⟩
  map_id stage := by
    apply ConcreteCategory.hom_ext
    intro receipt
    cases receipt
    simp
  map_comp before after := by
    apply ConcreteCategory.hom_ext
    intro receipt
    cases receipt
    simp [Category.assoc]

def inclusion (origin : Index) : uliftYoneda.{max i w}.obj (domains origin) ⟶ receipts.{u,v,i,w} domains where
  app _ := ↾fun argument => ⟨origin, argument⟩
  naturality := by
    intro first last change
    rfl

variable {result : C} (operations : ∀ origin, domains origin ⟶ result)

def evaluate : receipts.{u,v,i,w} domains ⟶ uliftYoneda.{max i w}.obj result where
  app _ := ↾fun receipt => ULift.up (receipt.2.down ≫ operations receipt.1)
  naturality := by
    intro first last change
    apply ConcreteCategory.hom_ext
    intro receipt
    exact congrArg ULift.up (Category.assoc change.unop receipt.2.down (operations receipt.1))

theorem complete_component (origin : Index) : inclusion.{u,v,i,w} domains origin ≫
    evaluate domains operations = uliftYoneda.map (operations origin) := rfl

theorem complete_argument {stage : C} (origin : Index) (argument : stage ⟶ domains origin) :
    (evaluate.{u,v,i,w} domains operations).app (op stage) ⟨origin, ULift.up argument⟩ =
      ULift.up (argument ≫ operations origin) := rfl

theorem restrict_origin {first second : C} (change : first ⟶ second)
    (receipt : (receipts.{u,v,i,w} domains).obj (op second)) :
    ((receipts domains).map change.op receipt).1 = receipt.1 := rfl

theorem restrict_argument {first second : C} (change : first ⟶ second)
    (receipt : (receipts.{u,v,i,w} domains).obj (op second)) :
    ((receipts domains).map change.op receipt).2.down = change ≫ receipt.2.down := rfl

theorem complete_restriction {first second : C} (change : first ⟶ second)
    (receipt : (receipts.{u,v,i,w} domains).obj (op second)) :
    ((evaluate domains operations).app (op first)
      ((receipts domains).map change.op receipt)).down =
        change ≫ ((evaluate domains operations).app (op second) receipt).down :=
  Category.assoc change receipt.2.down (operations receipt.1)

theorem postcompose {after : C} (continuation : result ⟶ after) :
    evaluate.{u,v,i,w} domains operations ≫ uliftYoneda.map continuation =
      evaluate domains (fun origin => operations origin ≫ continuation) := by
  apply NatTrans.ext
  funext stage
  apply ConcreteCategory.hom_ext
  intro receipt
  exact congrArg ULift.up (Category.assoc receipt.2.down (operations receipt.1) continuation)

theorem different_origins {stage : C} (first second : Index)
    (different : first ≠ second) (before : stage ⟶ domains first) (after : stage ⟶ domains second) :
    (⟨first,ULift.up before⟩ : (receipts.{u,v,i,w} domains).obj (op stage)) ≠
      ⟨second,ULift.up after⟩ := by
  intro same
  exact different (congrArg Sigma.fst same)

end Mettapedia.CategoryTheory.IndexedArrowReceiptPresheaf
