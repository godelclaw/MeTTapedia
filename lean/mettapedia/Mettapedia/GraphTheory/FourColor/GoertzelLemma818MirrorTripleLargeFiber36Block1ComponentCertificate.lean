import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorTripleLargeFiber36Chunk0ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block1Chunk1ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block1Chunk2ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Block1Chunk3ComponentCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first `MMM` large-fiber block

This module completes the first checked 64-row block for the `MMM`/`mode05`
large fixed-input fiber with reversed key `[b,b,r,r]`.  It imports the
previous checked 16-row chunk and reuses the remaining three `TTT` block-1
chunks, but rechecks them against the actual mirror-triple word.

This is still only one block of one large fixed-input fiber, not the full
`MMM` target audit and not the all-chain `LKR_in` consequence.
-/

namespace GoertzelLemma818MirrorTripleLargeFiber36Block1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818MirrorTripleComponentSmoke
open GoertzelLemma818MirrorTripleLightSlices
open GoertzelLemma818MirrorTripleLargeFiber36Chunk0ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data
open GoertzelLemma818TripleTauLargeFiber4Block1Chunk1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block1Chunk2ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Block1Chunk3ComponentCertificate

def mmmLargeFiber36ChunkSourcesCheck
    (rows : List TripleComponentParentRow) (sources : List Nat) : Bool :=
  (rows.map fun row => row.source) == sources

def mmmLargeFiber36ChunkRowsAudit
    (rows : List TripleComponentParentRow) : Bool :=
  (List.range 16).all fun i =>
    mmmLightComponentRowValid mmmLargeFiber36Key mmmLargeFiber36Expected
      (listGetD rows i default)

def mmmLargeFiber36ChunkParentMapAudit
    (rows : List TripleComponentParentRow) : Bool :=
  (List.range 16).all fun i =>
    let row := listGetD rows i default
    row.parent == tttLargeFiber4ParentOf row.source

def mmmLargeFiber36ChunkParentsAudit (sources : List Nat) : Bool :=
  (List.range 16).all fun i =>
    tttLargeFiber4ParentIter tttLargeFiber4MaxParentDepth
      (listGetD sources i 0) == tttLargeFiber4Root

def mmmLargeFiber36ChunkAudit
    (rows : List TripleComponentParentRow) (sources : List Nat) : Bool :=
  mmmRepresentativeModeSliceAudit &&
    tttLargeFiber4CountsAudit &&
    mmmLargeFiber36ChunkSourcesCheck rows sources &&
    mmmLargeFiber36ChunkRowsAudit rows &&
    mmmLargeFiber36ChunkParentMapAudit rows &&
    mmmLargeFiber36ChunkParentsAudit sources

def mmmLargeFiber36Block1Chunk1ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block1Chunk1Rows
    tttLargeFiber4Block1Chunk1Sources

theorem mmmLargeFiber36Block1Chunk1ComponentCertificateAudit_ok :
    mmmLargeFiber36Block1Chunk1ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block1Chunk2ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block1Chunk2Rows
    tttLargeFiber4Block1Chunk2Sources

theorem mmmLargeFiber36Block1Chunk2ComponentCertificateAudit_ok :
    mmmLargeFiber36Block1Chunk2ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block1Chunk3ComponentCertificateAudit : Bool :=
  mmmLargeFiber36ChunkAudit tttLargeFiber4Block1Chunk3Rows
    tttLargeFiber4Block1Chunk3Sources

theorem mmmLargeFiber36Block1Chunk3ComponentCertificateAudit_ok :
    mmmLargeFiber36Block1Chunk3ComponentCertificateAudit = true := by
  decide

def mmmLargeFiber36Block1ComponentCertificateAudit : Bool :=
  mmmLargeFiber36Block1Chunk0ComponentCertificateAudit &&
    mmmLargeFiber36Block1Chunk1ComponentCertificateAudit &&
    mmmLargeFiber36Block1Chunk2ComponentCertificateAudit &&
    mmmLargeFiber36Block1Chunk3ComponentCertificateAudit

theorem mmmLargeFiber36Block1ComponentCertificateAudit_ok :
    mmmLargeFiber36Block1ComponentCertificateAudit = true := by
  simp [mmmLargeFiber36Block1ComponentCertificateAudit,
    mmmLargeFiber36Block1Chunk0ComponentCertificateAudit_ok,
    mmmLargeFiber36Block1Chunk1ComponentCertificateAudit_ok,
    mmmLargeFiber36Block1Chunk2ComponentCertificateAudit_ok,
    mmmLargeFiber36Block1Chunk3ComponentCertificateAudit_ok]

end GoertzelLemma818MirrorTripleLargeFiber36Block1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
