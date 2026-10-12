import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafRealization
import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeCertificates
import Mettapedia.OSLF.NativeTypes.Certificates.Interpretation

/-! # Complete checked native trees read the independent free cube model -/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafCertificates

open _root_.CategoryTheory
open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open CubeEnrichment CubeNativeDeclarations

universe u
variable {D : CubeEnrichment.Signature} {W : Type u} [Category.{u} W]
variable (operational : D.Carrier → Wᵒᵖ ⥤ Type u) (vertex : Vertex D)

theorem derivation_sound {judgment : Judgment (symbols D)}
    (tree : Derivation (signature vertex) judgment) :
    Interprets (CubeNativePresheafModel.model operational vertex) judgment :=
  tree.native_sound (CubeNativePresheafModel.model operational vertex)
    (CubeNativePresheafRealization.realization operational vertex)

variable [DecidableEq D.Carrier] [DecidableEq D.Former]

theorem checked_sound
    (certificate : Mettapedia.OSLF.NativeTypes.Certificates.Refinement.Certificate (signature vertex))
    (judgment : Judgment (symbols D))
    (accepted : Mettapedia.OSLF.NativeTypes.Certificates.Refinement.check certificate judgment = true) :
    Interprets (CubeNativePresheafModel.model operational vertex) judgment :=
  Mettapedia.OSLF.NativeTypes.Certificates.Refinement.checked_native_sound
    (CubeNativePresheafModel.model operational vertex)
    (CubeNativePresheafRealization.realization operational vertex) certificate judgment accepted

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativePresheafCertificates
