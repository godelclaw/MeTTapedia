import Mettapedia.Languages.MM0.HOLKernelTermReadback
import Mettapedia.Logic.HOL.SetOperationSignature

/-!
# The six material operations in the native HOL syntax reader

Six distinct regular parameters supply the constant lookup for the shared
MM0-to-HOL reader. The seven-entry prefix contains their base type parameter
and prevents native binders from capturing these declarations. Syntax reading
is independent of material-model validation and source proof reconstruction.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLKernelSetOperationReadback
open Mettapedia.Logic.HOL
open Kernel HOLKernelTermReadback
open Embedding.ZFSetHenkinInterpretation (Symbol)

def readConstant : Nat → Option (NamedElaboration.SomeConst Symbol)
  | 1 => some ⟨_, .member⟩
  | 2 => some ⟨_, .empty⟩
  | 3 => some ⟨_, .union⟩
  | 4 => some ⟨_, .power⟩
  | 5 => some ⟨_, .separate⟩
  | 6 => some ⟨_, .replace⟩
  | _ => none


def readTerm (references : HOLKernelSyntax.Symbol → Nat) {gamma : Ctx Unit}
    (names : Names gamma) (native : Preterm) : Option (Decoded Symbol gamma) :=
  HOLKernelTermReadback.readTerm references readConstant 7 names native

def readFormula (references : HOLKernelSyntax.Symbol → Nat) {gamma : Ctx Unit}
    (names : Names gamma) (native : Preterm) : Option (Formula Symbol gamma) := do
  expect .prop (← readTerm references names native)

end Mettapedia.Languages.MM0.HOLKernelSetOperationReadback
