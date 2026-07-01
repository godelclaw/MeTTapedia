import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Block0ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Block1ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Block2ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Block3ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Block4ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Block5ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Block6ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Block7ComponentCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: second large `TTT` fiber certificate

This module aggregates the eight 64-row component-certificate blocks for the
second size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It closes this one large fiber, not the full `TTT` target and not all-chain
`LKR_in`.
-/

namespace GoertzelLemma818TripleTauLargeFiber8Certificate

open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Data
open GoertzelLemma818TripleTauLargeFiber8Block0ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Block1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Block2ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Block3ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Block4ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Block5ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Block6ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber8Block7ComponentCertificate

def tttLargeFiber8ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber8CountsAudit
    && tttLargeFiber8Block0ComponentCertificateAudit
    && tttLargeFiber8Block1ComponentCertificateAudit
    && tttLargeFiber8Block2ComponentCertificateAudit
    && tttLargeFiber8Block3ComponentCertificateAudit
    && tttLargeFiber8Block4ComponentCertificateAudit
    && tttLargeFiber8Block5ComponentCertificateAudit
    && tttLargeFiber8Block6ComponentCertificateAudit
    && tttLargeFiber8Block7ComponentCertificateAudit

theorem tttLargeFiber8ComponentCertificateAudit_ok :
    tttLargeFiber8ComponentCertificateAudit = true := by
  simp [tttLargeFiber8ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber8CountsAudit_ok,
    tttLargeFiber8Block0ComponentCertificateAudit_ok,
    tttLargeFiber8Block1ComponentCertificateAudit_ok,
    tttLargeFiber8Block2ComponentCertificateAudit_ok,
    tttLargeFiber8Block3ComponentCertificateAudit_ok,
    tttLargeFiber8Block4ComponentCertificateAudit_ok,
    tttLargeFiber8Block5ComponentCertificateAudit_ok,
    tttLargeFiber8Block6ComponentCertificateAudit_ok,
    tttLargeFiber8Block7ComponentCertificateAudit_ok]

end GoertzelLemma818TripleTauLargeFiber8Certificate

end Mettapedia.GraphTheory.FourColor
