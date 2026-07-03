import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorTripleLargeFiber36Block3ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block4Chunk0ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block4Chunk1ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block4Chunk2ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block4Chunk3ComponentCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: fourth checked `MMM` large-fiber block

This module checks another 64-row block for the `MMM`/`mode05` large
fixed-input fiber with reversed key `[b,b,r,r]`.  It reuses the completed
`TTT` block-4 chunks, but rechecks them against the actual mirror-triple word.

This remains a partial large-fiber audit, not the full `MMM` target and not
the all-chain `LKR_in` consequence.
-/

namespace GoertzelLemma818MirrorTripleLargeFiber36Block4ComponentCertificate

open GoertzelLemma818MirrorTripleLargeFiber36Block1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block4Chunk0ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block4Chunk1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block4Chunk2ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block4Chunk3ComponentCertificate

def mmmLargeFiber36Block4Chunk0ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block4Chunk0Rows
    tttLargeFiber4Block4Chunk0Sources

theorem mmmLargeFiber36Block4Chunk0ComponentCertificateAudit_ok :
    mmmLargeFiber36Block4Chunk0ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block4Chunk1ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block4Chunk1Rows
    tttLargeFiber4Block4Chunk1Sources

theorem mmmLargeFiber36Block4Chunk1ComponentCertificateAudit_ok :
    mmmLargeFiber36Block4Chunk1ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block4Chunk2ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block4Chunk2Rows
    tttLargeFiber4Block4Chunk2Sources

theorem mmmLargeFiber36Block4Chunk2ComponentCertificateAudit_ok :
    mmmLargeFiber36Block4Chunk2ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block4Chunk3ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block4Chunk3Rows
    tttLargeFiber4Block4Chunk3Sources

theorem mmmLargeFiber36Block4Chunk3ComponentCertificateAudit_ok :
    mmmLargeFiber36Block4Chunk3ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block4ComponentCertificateAudit : Bool :=
  mmmLargeFiber36Block4Chunk0ComponentCertificateAudit &&
    mmmLargeFiber36Block4Chunk1ComponentCertificateAudit &&
    mmmLargeFiber36Block4Chunk2ComponentCertificateAudit &&
    mmmLargeFiber36Block4Chunk3ComponentCertificateAudit

theorem mmmLargeFiber36Block4ComponentCertificateAudit_ok :
    mmmLargeFiber36Block4ComponentCertificateAudit = true := by
  simp [mmmLargeFiber36Block4ComponentCertificateAudit,
    mmmLargeFiber36Block4Chunk0ComponentCertificateAudit_ok,
    mmmLargeFiber36Block4Chunk1ComponentCertificateAudit_ok,
    mmmLargeFiber36Block4Chunk2ComponentCertificateAudit_ok,
    mmmLargeFiber36Block4Chunk3ComponentCertificateAudit_ok]

end GoertzelLemma818MirrorTripleLargeFiber36Block4ComponentCertificate

end Mettapedia.GraphTheory.FourColor
