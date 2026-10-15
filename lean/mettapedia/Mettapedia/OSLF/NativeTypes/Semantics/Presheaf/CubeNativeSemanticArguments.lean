import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticOperations

/-!
# Native parameter substitution reads the actual code arguments

The two family arguments and all generated constructor arguments use the
ordinary native telescope variable/readout protocol. Their ordered sections
are compared to the independently constructed code maps.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticArguments

open _root_.CategoryTheory Opposite
open Mettapedia.TypeTheory
open ContextualLocalUniverses ContextualModelTelescopes NativeLocalTypeFormers
open Calculi.NativeDependent.Refinement
open CubeNativeSemanticFamilies CubeNativeSemanticOperations

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u)

noncomputable section

def codeValue {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (name : P ⟶ CubePresheafCode.presheaf operational carrier) : NativeValue P :=
  ⟨codeAt operational carrier P, codeSection operational carrier name⟩

theorem pair_component_zero {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (code type : P ⟶ CubePresheafCode.presheaf operational carrier) :
    (typingScope operational carrier).2.components (pairArguments operational carrier code type) 0 =
      codeValue operational carrier code := by
  apply Sigma.ext
  · exact CubeNativeSemanticTelescopes.closed_weaken _ _
  · rfl

theorem pair_component_one {P : Wᵒᵖ ⥤ Type u} (carrier : D.Carrier)
    (code type : P ⟶ CubePresheafCode.presheaf operational carrier) :
    (typingScope operational carrier).2.components (pairArguments operational carrier code type) 1 =
      codeValue operational carrier type := by
  apply Sigma.ext
  · rfl
  · rfl

end

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeSemanticArguments
