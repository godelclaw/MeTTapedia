import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SharedChecking
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.SourceInjection
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.Controls
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.CheckingLaws
import Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.ReceiptChecking
import Mettapedia.OSLF.NativeTypes.Generation.BindingControls

/-! # Formation, carrier, vocabulary and authored-language separating controls -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.RuntimeControls

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Semantics.Presheaf
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open Mettapedia.OSLF.MeTTaIL.Syntax

def generateLanguage (language : LanguageDef) : Except Pipeline.Issue Pipeline.Installed :=
  Pipeline.generate (BindingPipeline.Controls.snapshot language) BindingPipeline.Controls.fragment
    BindingPipeline.Controls.fullLogic (fun _ => .star, fun _ => .star) []

@[noinline] def checkOne (installed : Pipeline.Installed) (index : Fin installed.headers.length) : IO Unit := do
  IO.eprintln ("Checking declaration " ++ toString index.val)
  let certificate := SharedChecking.emit installed.signature (installed.m_form index)
  IO.eprintln "Checking"
  let judgment := SignatureSum.judgmentRight
    (.term (SignatureSum.contextLeft (parameters (D := Pipeline.classifierSignature installed.operational) (installed.interfaces index)))
      (Declarations.modalCode (D := Pipeline.classifierSignature installed.operational) installed.interfaces index)
      (SignatureSum.typeLeft (result (D := Pipeline.classifierSignature installed.operational) (installed.interfaces index))))
  let checked := SharedChecking.check installed.signature installed.operational.logic certificate judgment
  match checked with
  | .accepted => pure ()
  | _ => throw (IO.userError "Generated formation certificate rejected")

@[noinline] def runOne (language : LanguageDef) (position : Nat) : IO Unit := do
  IO.eprintln ("Generating " ++ language.name)
  let .ok installed := generateLanguage language
    | throw (IO.userError ("Indexed formation refused: " ++ language.name))
  if inRange : position < installed.headers.length then
    checkOne installed ⟨position, inRange⟩
  else throw (IO.userError "Generated index outside catalogue")

@[noinline] def runFormation (language : LanguageDef) : IO Unit := do
  IO.eprintln ("Generating " ++ language.name)
  let .ok installed := generateLanguage language
    | throw (IO.userError ("Indexed formation refused: " ++ language.name))
  for index in List.finRange installed.headers.length do
    checkOne installed index
  IO.println (language.name ++ ": checked modal formations=" ++ toString installed.headers.length)

end Mettapedia.OSLF.NativeTypes.Generation.IndexedModal.RuntimeControls
