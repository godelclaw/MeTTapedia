import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafReadout

/-!
# Actual finite code arguments assemble native substitutions

Every ordered vector of natural code maps gives an actual map into the
independently assembled parameter telescope. Its complete variable readout
is the supplied vector, including repetitions and authored order.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticVectors

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory
open NativeLocalTypeFormers ContextualLocalUniverses ContextualModelTelescopes
open Calculi.NativeDependent.Refinement
open CubeNativeSemanticFamilies CubeNativeSemanticOperations CubeNativeSemanticArguments

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)

noncomputable section

abbrev vectorScope {n : Nat} (carriers : Fin n → D.Carrier) :=
  CubeNativeSemanticTelescopes.vectorScope (fun position => codeMeaning operational (carriers position))

def vectorMap {P : Wᵒᵖ ⥤ Type u} : {n : Nat} → (carriers : Fin n → D.Carrier) →
    (arguments : ∀ position, P ⟶ CubePresheafCode.presheaf operational (carriers position)) →
      P ⟶ (vectorScope operational carriers).1
  | 0, _, _ => (NativeModel W).toEmpty P
  | n + 1, carriers, arguments =>
      let previous := vectorMap (fun position : Fin n => carriers position.succ) (fun position => arguments position.succ)
      { app := fun world => TypeCat.ofHom fun value => ⟨previous.app world value, (arguments 0).app world value⟩
        naturality := by
          intro first second arrow
          apply ConcreteCategory.hom_ext
          intro value
          change (⟨previous.app second (P.map arrow value), (arguments 0).app second (P.map arrow value)⟩ :
            (vectorScope operational carriers).1.obj second) =
            ⟨(vectorScope operational (fun position : Fin n => carriers position.succ)).1.map arrow
              (previous.app first value),
             (CubePresheafCode.presheaf operational (carriers 0)).map arrow ((arguments 0).app first value)⟩
          rw [previous.naturality_apply, (arguments 0).naturality_apply] }

theorem vectorMap_components {P : Wᵒᵖ ⥤ Type u} {n : Nat} (carriers : Fin n → D.Carrier)
    (arguments : ∀ position, P ⟶ CubePresheafCode.presheaf operational (carriers position))
    (position : Fin n) :
    (vectorScope operational carriers).2.components (vectorMap operational carriers arguments) position =
      codeValue operational (carriers position) (arguments position) := by
  induction n with
  | zero => exact Fin.elim0 position
  | succ n hypotheses =>
      cases position using Fin.cases with
      | zero =>
          apply Sigma.ext
          · exact CubeNativeSemanticTelescopes.closed_weaken _ _
          · rfl
      | succ position =>
          exact (ScopeData.components_succ
            (vectorScope operational (fun position : Fin n => carriers position.succ)).2
            ((codeMeaning operational (carriers 0)).reindex ((NativeModel W).toEmpty _))
            (vectorMap operational carriers arguments) position).trans
              (hypotheses (fun position : Fin n => carriers position.succ)
                (fun position => arguments position.succ) position)


theorem codeValue_substitution {P Q : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (name : P ⟶ CubePresheafCode.presheaf operational carrier) (arrow : Q ⟶ P) :
    Value.substitute (K := (NativeModel W).toCwf) (codeValue operational carrier name) arrow =
      codeValue operational carrier (arrow ≫ name) := by
  apply Sigma.ext
  · exact CubeNativeSemanticTelescopes.closed_weaken _ _
  · rfl

theorem codeValue_injective {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier) :
    Function.Injective (codeValue operational carrier (P := P)) := by
  intro first second equal
  have sections : codeSection operational carrier first = codeSection operational carrier second :=
    eq_of_heq (Sigma.mk.inj equal).2
  apply NatTrans.ext
  funext world
  apply ConcreteCategory.hom_ext
  intro value
  exact congrArg (fun sectionValue => sectionValue.val ⟨world, value⟩) sections

theorem vectorName_map {P : Wᵒᵖ ⥤ Type u} {n : Nat} (carriers : Fin n → D.Carrier)
    (arguments : ∀ position, P ⟶ CubePresheafCode.presheaf operational (carriers position))
    (position : Fin n) :
    vectorMap operational carriers arguments ≫
      sectionName operational (carriers position)
        (CubeNativeSemanticTelescopes.lookupSection (fun position => codeMeaning operational (carriers position)) position) =
      arguments position := by
  have original := CubeNativeSemanticTelescopes.lookup_exact
    (fun position => codeMeaning operational (carriers position)) position
  have supplied : (vectorScope operational carriers).2.lookup position =
      codeValue operational (carriers position) (sectionName operational (carriers position)
        (CubeNativeSemanticTelescopes.lookupSection (fun position => codeMeaning operational (carriers position)) position)) :=
    original.trans (Sigma.ext rfl (by rfl))
  have read := vectorMap_components operational carriers arguments position
  change Value.substitute (K := (NativeModel W).toCwf) ((vectorScope operational carriers).2.lookup position)
      (vectorMap operational carriers arguments) = _ at read
  rw [supplied, codeValue_substitution] at read
  exact codeValue_injective operational (carriers position) read

theorem vectorLookup_value {P : Wᵒᵖ ⥤ Type u} {n : Nat} (carriers : Fin n → D.Carrier)
    (arguments : ∀ position, P ⟶ CubePresheafCode.presheaf operational (carriers position))
    (position : Fin n) (world : Wᵒᵖ) (value : P.obj world) :
    (CubeNativeSemanticTelescopes.lookupSection (fun position => codeMeaning operational (carriers position)) position).val
      ⟨world, (vectorMap operational carriers arguments).app world value⟩ =
        (arguments position).app world value :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (vectorName_map operational carriers arguments position) world) value

theorem parameterName_vectorMap {P : Wᵒᵖ ⥤ Type u} (declaration : D.Former)
    (arguments : ∀ position, P ⟶ CubePresheafCode.presheaf operational (D.input declaration position))
    (position : Fin (D.arity declaration)) :
    vectorMap operational (D.input declaration) arguments ≫ parameterName operational declaration position =
      arguments position :=
  vectorName_map operational (D.input declaration) arguments position

theorem formerName_composition {P Q : Wᵒᵖ ⥤ Type u} (declaration : D.Former)
    (arguments : ∀ position, P ⟶ CubePresheafCode.presheaf operational (D.input declaration position))
    (arrow : Q ⟶ P) :
    arrow ≫ formerName operational declaration arguments =
      formerName operational declaration (fun position => arrow ≫ arguments position) := by
  ext world value
  rfl

theorem formerValue_vectorMap {P : Wᵒᵖ ⥤ Type u} (declaration : D.Former)
    (arguments : ∀ position, P ⟶ CubePresheafCode.presheaf operational (D.input declaration position)) :
    Value.substitute (K := (NativeModel W).toCwf)
      (⟨formerType operational declaration, formerValue operational declaration⟩ :
        NativeValue (parameterScope operational declaration).1)
      (vectorMap operational (D.input declaration) arguments) =
      codeValue operational (D.output declaration) (formerName operational declaration arguments) := by
  change Value.substitute (K := (NativeModel W).toCwf)
    (codeValue operational (D.output declaration)
      (formerName operational declaration (parameterName operational declaration))) _ = _
  rw [codeValue_substitution, formerName_composition]
  have maps : (fun position => vectorMap operational (D.input declaration) arguments ≫
      parameterName operational declaration position) = arguments := by
    funext position
    exact parameterName_vectorMap operational declaration arguments position
  rw [maps]

end

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticVectors
