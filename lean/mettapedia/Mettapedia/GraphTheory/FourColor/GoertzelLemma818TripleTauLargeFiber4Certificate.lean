import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block0ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block1ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block2ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block3ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block4ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block5ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block6ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block7ComponentCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber certificate

This module aggregates the eight 64-row component-certificate blocks for the
first size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It closes this one large fiber, not the full `TTT` target and not all-chain
`LKR_in`.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Certificate

open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data
open GoertzelLemma818TripleTauLargeFiber4Block0ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block2ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block3ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block4ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block5ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block6ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block7ComponentCertificate

def tttLargeFiber4ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit
    && tttLargeFiber4Block0ComponentCertificateAudit
    && tttLargeFiber4Block1ComponentCertificateAudit
    && tttLargeFiber4Block2ComponentCertificateAudit
    && tttLargeFiber4Block3ComponentCertificateAudit
    && tttLargeFiber4Block4ComponentCertificateAudit
    && tttLargeFiber4Block5ComponentCertificateAudit
    && tttLargeFiber4Block6ComponentCertificateAudit
    && tttLargeFiber4Block7ComponentCertificateAudit

theorem tttLargeFiber4ComponentCertificateAudit_ok :
    tttLargeFiber4ComponentCertificateAudit = true := by
  simp [tttLargeFiber4ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block0ComponentCertificateAudit_ok,
    tttLargeFiber4Block1ComponentCertificateAudit_ok,
    tttLargeFiber4Block2ComponentCertificateAudit_ok,
    tttLargeFiber4Block3ComponentCertificateAudit_ok,
    tttLargeFiber4Block4ComponentCertificateAudit_ok,
    tttLargeFiber4Block5ComponentCertificateAudit_ok,
    tttLargeFiber4Block6ComponentCertificateAudit_ok,
    tttLargeFiber4Block7ComponentCertificateAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Certificate

end Mettapedia.GraphTheory.FourColor
