import Mettapedia.QuantumTheory.YangMills.HypercubicSU2HilbertCertificateOffShellBlock0Data

/-! # SU(2) Hilbert replay: off-shell class 0, block 3 -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicSU2HilbertCertificateOffShellBlock0Replay3

open HypercubicCartanMaxwellHilbertCertificate
open HypercubicSU2HilbertCertificate
open HypercubicSU2HilbertCertificateOffShellBlock0Data

theorem certificate_degree_15 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 15
        certificate = true := by
  decide

theorem certificate_degree_16 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 16
        certificate = true := by
  decide

#print axioms certificate_degree_15
#print axioms certificate_degree_16

end HypercubicSU2HilbertCertificateOffShellBlock0Replay3
end YangMills
end QuantumTheory
end Mettapedia
