import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.ConstantRenamingComputation
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorChecking

/-!
# Renaming an actual native Vector iota decoder

The original nonempty Vec-nil code decodes to an independently written input
with a renamed eliminator under the transported decoder. The old decoder
refuses those same expected endpoints. The resulting raw root step is proved
through the generic transport. Formation of a joint declaration signature is
a separate construction.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.RootRenamingControls

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation

open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
open TypedEquality.Normalization

def newEliminator : DeclName := `CumulativeTower.VecUpper.eliminate
def names : DeclName ≃ DeclName := Equiv.swap vecEliminateName newEliminator

def motive : Tower.Tm 0 := .lam (.lam natTm)
def consCase : Tower.Tm 0 := .lam (.lam (.lam (.lam zeroTm)))
def nilCode : Checking.iotaDecoder.Code 0 := ⟨2, [consCase, zeroTm, motive, natTm]⟩
def mappedDecoder := Checking.iotaDecoder.renameConst names

def mappedInput : Tower.Tm 0 :=
  appSpine (.const newEliminator) [natTm, motive, zeroTm, consCase, zeroTm, vnilApp natTm]

def originalInput : Tower.Tm 0 :=
  vecEliminateApp natTm motive zeroTm consCase zeroTm (vnilApp natTm)

theorem source_decode : Checking.iotaDecoder.decode nilCode = some (originalInput, zeroTm) := by
  decide +kernel

theorem input_map_exact : originalInput.mapConst names = mappedInput := by decide +kernel
theorem zero_map_exact : (zeroTm : Tower.Tm 0).mapConst names = zeroTm := by decide +kernel

theorem renamed_decode : mappedDecoder.decode nilCode = some (mappedInput, zeroTm) := by
  simpa only [mappedDecoder, input_map_exact, zero_map_exact] using
    Checking.iotaDecoder.renameConst_decode names source_decode

theorem source_root_step : iotaComputation.step originalInput zeroTm :=
  Checking.iotaDecoder.sound nilCode source_decode

theorem renamed_root_step : (iotaComputation.pullbackConst names.symm).step mappedInput zeroTm := by
  simpa only [input_map_exact, zero_map_exact] using
    iotaComputation.pullbackConst_forward names source_root_step

theorem original_decode_refuses : Checking.iotaDecoder.decode nilCode ≠ some (mappedInput, zeroTm) := by
  decide +kernel

#print axioms renamed_decode
#print axioms renamed_root_step
#print axioms original_decode_refuses

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies.RootRenamingControls
