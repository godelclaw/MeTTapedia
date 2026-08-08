import Mettapedia.QuantumTheory.YangMills.HypercubicSU2HilbertCertificateOffShellBlock0Data

/-! # SU(2) Hilbert replay: off-shell class 0, block 1 -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicSU2HilbertCertificateOffShellBlock0Replay1

open HypercubicCartanMaxwellHilbertCertificate
open HypercubicSU2HilbertCertificate
open HypercubicSU2HilbertCertificateOffShellBlock0Data

theorem certificate_degree_5 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 5
        certificate = true := by
  decide

theorem certificate_degree_6 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 6
        certificate = true := by
  decide

theorem certificate_degree_7 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 7
        certificate = true := by
  decide

theorem certificate_degree_8 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 8
        certificate = true := by
  decide

theorem certificate_degree_9 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 9
        certificate = true := by
  decide

#print axioms certificate_degree_5
#print axioms certificate_degree_6
#print axioms certificate_degree_7
#print axioms certificate_degree_8
#print axioms certificate_degree_9

end HypercubicSU2HilbertCertificateOffShellBlock0Replay1
end YangMills
end QuantumTheory
end Mettapedia
