import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block1Chunk0ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block1Chunk1ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block1Chunk2ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block1Chunk3ComponentCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 1

This module aggregates four 16-row component-certificate chunks for one
64-row part of the first size-512 fixed-input fiber of the `TTT`/`mode09`
representative target.  The smaller chunks replace the archived non-imported
64-row WIP shape.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block1ComponentCertificate

open GoertzelLemma818TripleTauLargeFiber4Block1Chunk0ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block1Chunk1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block1Chunk2ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block1Chunk3ComponentCertificate

def tttLargeFiber4Block1ComponentCertificateAudit : Bool :=
  tttLargeFiber4Block1Chunk0ComponentCertificateAudit &&
    tttLargeFiber4Block1Chunk1ComponentCertificateAudit &&
    tttLargeFiber4Block1Chunk2ComponentCertificateAudit &&
    tttLargeFiber4Block1Chunk3ComponentCertificateAudit

theorem tttLargeFiber4Block1ComponentCertificateAudit_ok :
    tttLargeFiber4Block1ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block1ComponentCertificateAudit,
    tttLargeFiber4Block1Chunk0ComponentCertificateAudit_ok,
    tttLargeFiber4Block1Chunk1ComponentCertificateAudit_ok,
    tttLargeFiber4Block1Chunk2ComponentCertificateAudit_ok,
    tttLargeFiber4Block1Chunk3ComponentCertificateAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
