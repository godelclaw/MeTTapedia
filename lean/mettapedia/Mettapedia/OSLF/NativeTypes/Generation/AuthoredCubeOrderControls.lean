import Mettapedia.OSLF.NativeTypes.Generation.AuthoredControls

/-!
# Nonconstant cube coordinates follow authored rely names

The original machine contains modal occurrences whose address and zipper
traversals order surrounding parameters differently. A nonconstant input
profile distinguishes correct name transport from positional zipping.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls

open Mettapedia.OSLF.MeTTaIL.Syntax
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)

def relyKind (name : String) : HSort := if name = "k" then .box else .star

def namedModalVertex (language : LanguageDef) : SortProfiles.Derived.CubeVertex language :=
  (fun position =>
    match ((SortProfiles.Slots.modalFamily language (Occurrences.generate language)[position.1]).inputs[position.2.val]?) with
    | none => .star
    | some slot => relyKind slot.1,
    fun _ => .star)

def mixedMachine : Except Issue Installed :=
  let snapshot := BindingPipeline.Controls.snapshot BindingPipeline.Controls.originalMachine
  generate snapshot BindingPipeline.Controls.fragment BindingPipeline.Controls.fullLogic
    (namedModalVertex (selectedSnapshot snapshot BindingPipeline.Controls.fragment).language)

def mixedSlotsCorrect : Bool :=
  match mixedMachine with
  | .error _ => false
  | .ok installed =>
      (List.finRange installed.operational.modal.length).all fun index =>
        (List.finRange installed.operational.modal[index].rely.length).all fun input =>
          installed.vertex (.inr index) input.castSucc ==
            relyKind installed.operational.modal[index].rely[input].slot.name

def mixedReordered : Bool :=
  match mixedMachine with
  | .error _ => false
  | .ok installed =>
      (List.finRange installed.operational.modal.length).any fun index =>
        match NativeCubeProfile.rawIndex? installed.operational index with
        | none => false
        | some origin =>
            installed.operational.modal[index].rely.map (fun parameter => parameter.slot.name) !=
              (Occurrences.generate (NativeCubeProfile.language installed.operational))[origin].relyNames

#guard mixedSlotsCorrect
#guard mixedReordered

end Mettapedia.OSLF.NativeTypes.Generation.AuthoredPipeline.Controls
