import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorTripleLargeFiber36Block1ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block2Chunk0ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block2Chunk1ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block2Chunk2ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block2Chunk3ComponentCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: second checked `MMM` large-fiber block

This module checks another 64-row block for the `MMM`/`mode05` large
fixed-input fiber with reversed key `[b,b,r,r]`.  It reuses the completed
`TTT` block-2 chunks, but rechecks them against the actual mirror-triple word.

This is still only a partial large-fiber audit, not the full `MMM` target and
not the all-chain `LKR_in` consequence.
-/

namespace GoertzelLemma818MirrorTripleLargeFiber36Block2ComponentCertificate

open GoertzelLemma818MirrorTripleLargeFiber36Block1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block2Chunk0ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block2Chunk1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block2Chunk2ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block2Chunk3ComponentCertificate

def mmmLargeFiber36Block2Chunk0ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block2Chunk0Rows
    tttLargeFiber4Block2Chunk0Sources

theorem mmmLargeFiber36Block2Chunk0ComponentCertificateAudit_ok :
    mmmLargeFiber36Block2Chunk0ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block2Chunk1ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block2Chunk1Rows
    tttLargeFiber4Block2Chunk1Sources

theorem mmmLargeFiber36Block2Chunk1ComponentCertificateAudit_ok :
    mmmLargeFiber36Block2Chunk1ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block2Chunk2ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block2Chunk2Rows
    tttLargeFiber4Block2Chunk2Sources

theorem mmmLargeFiber36Block2Chunk2ComponentCertificateAudit_ok :
    mmmLargeFiber36Block2Chunk2ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block2Chunk3ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block2Chunk3Rows
    tttLargeFiber4Block2Chunk3Sources

theorem mmmLargeFiber36Block2Chunk3ComponentCertificateAudit_ok :
    mmmLargeFiber36Block2Chunk3ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block2ComponentCertificateAudit : Bool :=
  mmmLargeFiber36Block2Chunk0ComponentCertificateAudit &&
    mmmLargeFiber36Block2Chunk1ComponentCertificateAudit &&
    mmmLargeFiber36Block2Chunk2ComponentCertificateAudit &&
    mmmLargeFiber36Block2Chunk3ComponentCertificateAudit

theorem mmmLargeFiber36Block2ComponentCertificateAudit_ok :
    mmmLargeFiber36Block2ComponentCertificateAudit = true := by
  simp [mmmLargeFiber36Block2ComponentCertificateAudit,
    mmmLargeFiber36Block2Chunk0ComponentCertificateAudit_ok,
    mmmLargeFiber36Block2Chunk1ComponentCertificateAudit_ok,
    mmmLargeFiber36Block2Chunk2ComponentCertificateAudit_ok,
    mmmLargeFiber36Block2Chunk3ComponentCertificateAudit_ok]

end GoertzelLemma818MirrorTripleLargeFiber36Block2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
