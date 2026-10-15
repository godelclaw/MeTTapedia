import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafCertificates
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeControls
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubePresheafUniversalProperty

/-!
# Discriminating controls for the actual cube presheaf meanings

Changing a computed input slot removes actual native fibre inhabitants;
changing its output slot changes the inhabited fibre. Operational carrier
values retain their origin and do not acquire an implicit kind.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafControls

open _root_.CategoryTheory Opposite
open CubeNativeControls CubeNativeSemanticFamilies
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement

universe u
variable {W : Type u} [Category.{u} W]
variable (operational : language.Carrier → Wᵒᵖ ⥤ Type u)

def actualApplication (world : Wᵒᵖ) : (CubePresheafCode.presheaf operational true).obj world :=
  @CubeEnrichment.Code.former language (fun carrier => (operational carrier).obj world) true
    (fun _ => @CubeEnrichment.Code.sort language (fun carrier => (operational carrier).obj world) false .star)

abbrev applicationFibre (vertex : CubeEnrichment.Vertex language) (world : Wᵒᵖ)
    (kind : Mettapedia.OSLF.Framework.ModalHypercube.HSort) :=
  (typingMeaning operational vertex true).decoded.obj
    ⟨world, (pairNameInverse operational true).app world (actualApplication operational world, .sort kind)⟩

theorem original_fibre_inhabited (world : Wᵒᵖ) :
    Nonempty (applicationFibre operational boxSlots world .box) := by
  rw [applicationFibre, typing_inhabited_iff]
  exact CubeEnrichment.inferKind_sound (by rfl)

theorem changed_input_fibre_empty (world : Wᵒᵖ) :
    ¬ Nonempty (applicationFibre operational starInput world .box) := by
  rw [applicationFibre, typing_inhabited_iff, ← CubeEnrichment.inferKind_exact]
  intro impossible
  cases impossible

theorem changed_output_fibre_inhabited (world : Wᵒᵖ) :
    Nonempty (applicationFibre operational starOutput world .star) := by
  rw [applicationFibre, typing_inhabited_iff]
  exact CubeEnrichment.inferKind_sound (by rfl)

theorem changed_output_old_fibre_empty (world : Wᵒᵖ) :
    ¬ Nonempty (applicationFibre operational starOutput world .box) := by
  rw [applicationFibre, typing_inhabited_iff, ← CubeEnrichment.inferKind_exact]
  intro impossible
  cases impossible

theorem authored_origin_preserved (carrier : language.Carrier) (world : Wᵒᵖ)
    (first second : (operational carrier).obj world) (different : first ≠ second) :
    (CubePresheafCode.injection operational carrier).app world first ≠
      (CubePresheafCode.injection operational carrier).app world second :=
  fun equal => different (CubePresheafCode.injection_monic operational carrier world equal)

theorem source_value_has_no_implicit_kind (carrier : language.Carrier) (world : Wᵒᵖ)
    (value : (operational carrier).obj world) (kind : Mettapedia.OSLF.Framework.ModalHypercube.HSort) :
    ¬ Nonempty ((typingMeaning operational boxSlots carrier).decoded.obj
      ⟨world, (pairNameInverse operational carrier).app world (.operational value, .sort kind)⟩) :=
  injected_untyped operational boxSlots carrier world value kind

/-- The actual emitted complete native certificate has its independent
presheaf meaning for every operational-carrier presheaf on the same base. -/
theorem emitted_certificate_interprets :
    Interprets (CubeNativePresheafModel.model operational boxSlots) outputJudgment := by
  apply CubeNativePresheafCertificates.checked_sound operational boxSlots output.2 outputJudgment
  exact CubeNativeKindSearch.nativeFormation?_checked boxSlots application .box output.1 output.2
    (Option.some_get (by decide)).symm

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafControls
