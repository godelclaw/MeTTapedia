import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorTripleLargeFiber36Block2ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block3Chunk0ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block3Chunk1ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block3Chunk2ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block3Chunk3ComponentCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: third checked `MMM` large-fiber block

This module checks another 64-row block for the `MMM`/`mode05` large
fixed-input fiber with reversed key `[b,b,r,r]`.  It reuses the completed
`TTT` block-3 chunks, but rechecks them against the actual mirror-triple word.

This remains a partial large-fiber audit, not the full `MMM` target and not
the all-chain `LKR_in` consequence.
-/

namespace GoertzelLemma818MirrorTripleLargeFiber36Block3ComponentCertificate

open GoertzelLemma818MirrorTripleLargeFiber36Block1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block3Chunk0ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block3Chunk1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block3Chunk2ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block3Chunk3ComponentCertificate

def mmmLargeFiber36Block3Chunk0ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block3Chunk0Rows
    tttLargeFiber4Block3Chunk0Sources

theorem mmmLargeFiber36Block3Chunk0ComponentCertificateAudit_ok :
    mmmLargeFiber36Block3Chunk0ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block3Chunk1ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block3Chunk1Rows
    tttLargeFiber4Block3Chunk1Sources

theorem mmmLargeFiber36Block3Chunk1ComponentCertificateAudit_ok :
    mmmLargeFiber36Block3Chunk1ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block3Chunk2ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block3Chunk2Rows
    tttLargeFiber4Block3Chunk2Sources

theorem mmmLargeFiber36Block3Chunk2ComponentCertificateAudit_ok :
    mmmLargeFiber36Block3Chunk2ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block3Chunk3ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block3Chunk3Rows
    tttLargeFiber4Block3Chunk3Sources

theorem mmmLargeFiber36Block3Chunk3ComponentCertificateAudit_ok :
    mmmLargeFiber36Block3Chunk3ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block3ComponentCertificateAudit : Bool :=
  mmmLargeFiber36Block3Chunk0ComponentCertificateAudit &&
    mmmLargeFiber36Block3Chunk1ComponentCertificateAudit &&
    mmmLargeFiber36Block3Chunk2ComponentCertificateAudit &&
    mmmLargeFiber36Block3Chunk3ComponentCertificateAudit

theorem mmmLargeFiber36Block3ComponentCertificateAudit_ok :
    mmmLargeFiber36Block3ComponentCertificateAudit = true := by
  simp [mmmLargeFiber36Block3ComponentCertificateAudit,
    mmmLargeFiber36Block3Chunk0ComponentCertificateAudit_ok,
    mmmLargeFiber36Block3Chunk1ComponentCertificateAudit_ok,
    mmmLargeFiber36Block3Chunk2ComponentCertificateAudit_ok,
    mmmLargeFiber36Block3Chunk3ComponentCertificateAudit_ok]

end GoertzelLemma818MirrorTripleLargeFiber36Block3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
