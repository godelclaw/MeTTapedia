import Mettapedia.QuantumTheory.YangMills.HypercubicSU2HilbertCertificateOffShellBlock0Data

/-! # SU(2) Hilbert replay: off-shell class 0, block 2 -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicSU2HilbertCertificateOffShellBlock0Replay2

open HypercubicCartanMaxwellHilbertCertificate
open HypercubicSU2HilbertCertificate
open HypercubicSU2HilbertCertificateOffShellBlock0Data

theorem certificate_degree_10 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 10
        certificate = true := by
  decide

theorem certificate_degree_11 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 11
        certificate = true := by
  decide

theorem certificate_degree_12 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 12
        certificate = true := by
  decide

theorem certificate_degree_13 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 13
        certificate = true := by
  decide

theorem certificate_degree_14 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 14
        certificate = true := by
  decide

#print axioms certificate_degree_10
#print axioms certificate_degree_11
#print axioms certificate_degree_12
#print axioms certificate_degree_13
#print axioms certificate_degree_14

end HypercubicSU2HilbertCertificateOffShellBlock0Replay2
end YangMills
end QuantumTheory
end Mettapedia
