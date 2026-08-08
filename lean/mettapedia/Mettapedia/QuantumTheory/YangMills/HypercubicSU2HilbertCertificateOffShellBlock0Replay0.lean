import Mettapedia.QuantumTheory.YangMills.HypercubicSU2HilbertCertificateOffShellBlock0Data

/-! # SU(2) Hilbert replay: off-shell class 0, block 0 -/

set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace HypercubicSU2HilbertCertificateOffShellBlock0Replay0

open HypercubicCartanMaxwellHilbertCertificate
open HypercubicSU2HilbertCertificate
open HypercubicSU2HilbertCertificateOffShellBlock0Data

theorem certificate_particles :
    sparseCertificateParticlesValid .offShell (0 : Fin 14) 16
        certificate = true := by
  decide

theorem certificate_degree_0 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 0
        certificate = true := by
  decide

theorem certificate_degree_1 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 1
        certificate = true := by
  decide

theorem certificate_degree_2 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 2
        certificate = true := by
  decide

theorem certificate_degree_3 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 3
        certificate = true := by
  decide

theorem certificate_degree_4 :
    sparseCertificateDegreeValidAt (0 : Fin 14) 16 4
        certificate = true := by
  decide

#print axioms certificate_particles
#print axioms certificate_degree_0
#print axioms certificate_degree_1
#print axioms certificate_degree_2
#print axioms certificate_degree_3
#print axioms certificate_degree_4

end HypercubicSU2HilbertCertificateOffShellBlock0Replay0
end YangMills
end QuantumTheory
end Mettapedia
