import Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline

/-!
# Original constructor origins through language selection

Native header indices name the selected signature. Their source origins are
read from the retained authored catalogue, whose projection is checked against
that signature. Selection never assigns a shortened-list position as a source
declaration index.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline

open Mettapedia.OSLF.MeTTaIL.Syntax

theorem installGenerated_retains (authored : LanguageDef) (generated : Generated)
    (logic : NativeLogic.Fragment) (installed : Installed)
    (accepted : installGenerated authored generated logic = .ok installed) :
    installed.authored = authored ∧ installed.generated = generated ∧ installed.logic = logic := by
  unfold installGenerated at accepted
  split at accepted
  · cases declarations : NativeSignature.install? (plan generated).snapshot.language with
    | none => simp [declarations, bind, Except.bind] at accepted
    | some declarations =>
        simp only [declarations, bind, Except.bind] at accepted
        repeat' split at accepted
        all_goals simp_all
        cases accepted
        exact ⟨rfl, rfl, rfl⟩
  · cases accepted

namespace Installed

variable (installed : Installed)

def constructorCatalogue : List (GrammarRule × Nat) :=
  selectedConstructors installed.authored installed.generated.languageFragment

theorem constructorCatalogue_length : installed.constructorCatalogue.length =
    (plan installed.generated).snapshot.language.terms.length := by
  have lengths := congrArg List.length installed.selectedTerms
  simpa only [List.length_map, constructorCatalogue] using lengths

def constructorOrigin (constructor : installed.declarations.Constructor) : GrammarRule × Nat :=
  installed.constructorCatalogue[(installed.declarations.origin constructor).val]'(by
    rw [installed.constructorCatalogue_length]
    exact (installed.declarations.origin constructor).isLt)

theorem constructorOrigin_readout (constructor : installed.declarations.Constructor) :
    (installed.constructorOrigin constructor).1 =
      (plan installed.generated).snapshot.language.terms[(installed.declarations.origin constructor).val] := by
  have selectedBound : (installed.declarations.origin constructor).val <
      installed.constructorCatalogue.length := by
    rw [installed.constructorCatalogue_length]
    exact (installed.declarations.origin constructor).isLt
  have selectedMappedBound : (installed.declarations.origin constructor).val <
      (installed.constructorCatalogue.map Prod.fst).length := by
    simpa only [List.length_map] using selectedBound
  have readout := congrArg (fun terms : List GrammarRule => terms[(installed.declarations.origin constructor).val]?)
    installed.selectedTerms
  change (installed.constructorCatalogue.map Prod.fst)[(installed.declarations.origin constructor).val]? = _ at readout
  rw [List.getElem?_eq_getElem selectedMappedBound,
    List.getElem?_eq_getElem (installed.declarations.origin constructor).isLt] at readout
  simpa only [List.getElem_map, constructorOrigin] using Option.some.inj readout

theorem constructorOrigin_admitted (constructor : installed.declarations.Constructor) :
    installed.constructorOrigin constructor ∈ installed.authored.terms.zipIdx ∧
      Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission.selected
        installed.generated.languageFragment.constructorIndices
        (installed.constructorOrigin constructor).2 = true :=
  (selected_constructor_iff installed.authored installed.generated.languageFragment _).mp
    (List.getElem_mem _)

end Installed

end Mettapedia.OSLF.NativeTypes.Generation.BindingPipeline
