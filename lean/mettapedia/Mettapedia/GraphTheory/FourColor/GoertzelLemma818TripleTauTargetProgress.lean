import Mettapedia.GraphTheory.FourColor.GoertzelLemma818SemanticBridge
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber8Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber10Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block0Chunk0ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block0Chunk1ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block0ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block1ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block2ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block3ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block4ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block5ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block6ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Block7ComponentCertificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber20Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber30Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber36Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber44Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber50Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber60Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber70Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber72Certificate
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber76Certificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: `TTT` target progress

This module records the currently checked chain-level surface for the first
non-base semantic target, `TTT`/`mode09`.

The light fibers and all twelve large fixed-input fibers are certified by
explicit component/path tables.  This closes the explicit `TTT` representative
target; it is still not the all-chain `LKR_in` theorem.
-/

namespace GoertzelLemma818TripleTauTargetProgress

open GoertzelLemma814
open GoertzelLemma818FrontierMode
open GoertzelLemma818RepresentativeTargets
open GoertzelLemma818SemanticBridge
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data
open GoertzelLemma818TripleTauLargeFiber4Certificate
open GoertzelLemma818TripleTauLargeFiber8Data
open GoertzelLemma818TripleTauLargeFiber8Certificate
open GoertzelLemma818TripleTauLargeFiber10Data
open GoertzelLemma818TripleTauLargeFiber10Certificate
open GoertzelLemma818TripleTauLargeFiber20Data
open GoertzelLemma818TripleTauLargeFiber20Block0Chunk0ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block0Chunk1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block0ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block1ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block2ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block3ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block4ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block5ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block6ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Block7ComponentCertificate
open GoertzelLemma818TripleTauLargeFiber20Certificate
open GoertzelLemma818TripleTauLargeFiber30Data
open GoertzelLemma818TripleTauLargeFiber30Certificate
open GoertzelLemma818TripleTauLargeFiber36Data
open GoertzelLemma818TripleTauLargeFiber36Certificate
open GoertzelLemma818TripleTauLargeFiber44Data
open GoertzelLemma818TripleTauLargeFiber44Certificate
open GoertzelLemma818TripleTauLargeFiber50Data
open GoertzelLemma818TripleTauLargeFiber50Certificate
open GoertzelLemma818TripleTauLargeFiber60Data
open GoertzelLemma818TripleTauLargeFiber60Certificate
open GoertzelLemma818TripleTauLargeFiber70Data
open GoertzelLemma818TripleTauLargeFiber70Certificate
open GoertzelLemma818TripleTauLargeFiber72Data
open GoertzelLemma818TripleTauLargeFiber72Certificate
open GoertzelLemma818TripleTauLargeFiber76Data
open GoertzelLemma818TripleTauLargeFiber76Certificate

def tttCertifiedLargeFiberKeys : List (List LColor) :=
  [ tttLargeFiber4Key
  , tttLargeFiber8Key
  , tttLargeFiber10Key
  ]

def tttRemainingLargeFiberKeys : List (List LColor) :=
  [ [LColor.r, LColor.p, LColor.r, LColor.p]
  , [LColor.b, LColor.r, LColor.b, LColor.r]
  , [LColor.b, LColor.b, LColor.r, LColor.r]
  , [LColor.b, LColor.b, LColor.p, LColor.p]
  , [LColor.b, LColor.p, LColor.b, LColor.p]
  , [LColor.p, LColor.r, LColor.p, LColor.r]
  , [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCount : Nat :=
  tttLightStateCount +
    tttCertifiedLargeFiberKeys.length * tttRemainingLargeFiberSize

def tttRemainingLargeStateCount : Nat :=
  tttRemainingLargeFiberKeys.length * tttRemainingLargeFiberSize

def tttLargeFiber20FirstChunkCertifiedRows : Nat := 16

def tttLargeFiber20SecondChunkCertifiedRows : Nat := 16

def tttCertifiedStateCountWithFiber20FirstChunk : Nat :=
  tttCertifiedStateCount + tttLargeFiber20FirstChunkCertifiedRows

def tttRemainingStateCountAfterFiber20FirstChunk : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20FirstChunk

def tttCertifiedStateCountWithFiber20FirstTwoChunks : Nat :=
  tttCertifiedStateCountWithFiber20FirstChunk +
    tttLargeFiber20SecondChunkCertifiedRows

def tttRemainingStateCountAfterFiber20FirstTwoChunks : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20FirstTwoChunks

def tttLargeFiber20Block0CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block0 : Nat :=
  tttCertifiedStateCount + tttLargeFiber20Block0CertifiedRows

def tttRemainingStateCountAfterFiber20Block0 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block0

def tttLargeFiber20Block1CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block1 : Nat :=
  tttCertifiedStateCountWithFiber20Block0 + tttLargeFiber20Block1CertifiedRows

def tttRemainingStateCountAfterFiber20Block1 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block1

def tttLargeFiber20Block2CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block2 : Nat :=
  tttCertifiedStateCountWithFiber20Block1 + tttLargeFiber20Block2CertifiedRows

def tttRemainingStateCountAfterFiber20Block2 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block2

def tttLargeFiber20Block3CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block3 : Nat :=
  tttCertifiedStateCountWithFiber20Block2 + tttLargeFiber20Block3CertifiedRows

def tttRemainingStateCountAfterFiber20Block3 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block3

def tttLargeFiber20Block4CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block4 : Nat :=
  tttCertifiedStateCountWithFiber20Block3 + tttLargeFiber20Block4CertifiedRows

def tttRemainingStateCountAfterFiber20Block4 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block4

def tttLargeFiber20Block5CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block5 : Nat :=
  tttCertifiedStateCountWithFiber20Block4 + tttLargeFiber20Block5CertifiedRows

def tttRemainingStateCountAfterFiber20Block5 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block5

def tttLargeFiber20Block6CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block6 : Nat :=
  tttCertifiedStateCountWithFiber20Block5 + tttLargeFiber20Block6CertifiedRows

def tttRemainingStateCountAfterFiber20Block6 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block6

def tttLargeFiber20Block7CertifiedRows : Nat := 64

def tttCertifiedStateCountWithFiber20Block7 : Nat :=
  tttCertifiedStateCountWithFiber20Block6 + tttLargeFiber20Block7CertifiedRows

def tttRemainingStateCountAfterFiber20Block7 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber20Block7

def tttCertifiedLargeFiberKeysAfterFiber20 : List (List LColor) :=
  tttCertifiedLargeFiberKeys ++ [tttLargeFiber20Key]

def tttRemainingLargeFiberKeysAfterFiber20 : List (List LColor) :=
  [ [LColor.b, LColor.r, LColor.b, LColor.r]
  , [LColor.b, LColor.b, LColor.r, LColor.r]
  , [LColor.b, LColor.b, LColor.p, LColor.p]
  , [LColor.b, LColor.p, LColor.b, LColor.p]
  , [LColor.p, LColor.r, LColor.p, LColor.r]
  , [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber30 : Nat :=
  tttCertifiedStateCountWithFiber20Block7 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber30 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber30

def tttCertifiedLargeFiberKeysAfterFiber30 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber20 ++ [tttLargeFiber30Key]

def tttRemainingLargeFiberKeysAfterFiber30 : List (List LColor) :=
  [ [LColor.b, LColor.b, LColor.r, LColor.r]
  , [LColor.b, LColor.b, LColor.p, LColor.p]
  , [LColor.b, LColor.p, LColor.b, LColor.p]
  , [LColor.p, LColor.r, LColor.p, LColor.r]
  , [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber36 : Nat :=
  tttCertifiedStateCountWithFiber30 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber36 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber36

def tttCertifiedLargeFiberKeysAfterFiber36 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber30 ++ [tttLargeFiber36Key]

def tttRemainingLargeFiberKeysAfterFiber36 : List (List LColor) :=
  [ [LColor.b, LColor.b, LColor.p, LColor.p]
  , [LColor.b, LColor.p, LColor.b, LColor.p]
  , [LColor.p, LColor.r, LColor.p, LColor.r]
  , [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber44 : Nat :=
  tttCertifiedStateCountWithFiber36 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber44 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber44

def tttCertifiedLargeFiberKeysAfterFiber44 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber36 ++ [tttLargeFiber44Key]

def tttRemainingLargeFiberKeysAfterFiber44 : List (List LColor) :=
  [ [LColor.b, LColor.p, LColor.b, LColor.p]
  , [LColor.p, LColor.r, LColor.p, LColor.r]
  , [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber50 : Nat :=
  tttCertifiedStateCountWithFiber44 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber50 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber50

def tttCertifiedLargeFiberKeysAfterFiber50 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber44 ++ [tttLargeFiber50Key]

def tttRemainingLargeFiberKeysAfterFiber50 : List (List LColor) :=
  [ [LColor.p, LColor.r, LColor.p, LColor.r]
  , [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber60 : Nat :=
  tttCertifiedStateCountWithFiber50 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber60 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber60

def tttCertifiedLargeFiberKeysAfterFiber60 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber50 ++ [tttLargeFiber60Key]

def tttRemainingLargeFiberKeysAfterFiber60 : List (List LColor) :=
  [ [LColor.p, LColor.b, LColor.p, LColor.b]
  , [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber70 : Nat :=
  tttCertifiedStateCountWithFiber60 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber70 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber70

def tttCertifiedLargeFiberKeysAfterFiber70 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber60 ++ [tttLargeFiber70Key]

def tttRemainingLargeFiberKeysAfterFiber70 : List (List LColor) :=
  [ [LColor.p, LColor.p, LColor.r, LColor.r]
  , [LColor.p, LColor.p, LColor.b, LColor.b]
  ]

def tttCertifiedStateCountWithFiber72 : Nat :=
  tttCertifiedStateCountWithFiber70 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber72 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber72

def tttCertifiedLargeFiberKeysAfterFiber72 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber70 ++ [tttLargeFiber72Key]

def tttRemainingLargeFiberKeysAfterFiber72 : List (List LColor) :=
  [ [LColor.p, LColor.p, LColor.b, LColor.b] ]

def tttCertifiedStateCountWithFiber76 : Nat :=
  tttCertifiedStateCountWithFiber72 + tttRemainingLargeFiberSize

def tttRemainingStateCountAfterFiber76 : Nat :=
  tttCompositeStateCount - tttCertifiedStateCountWithFiber76

def tttCertifiedLargeFiberKeysAfterFiber76 : List (List LColor) :=
  tttCertifiedLargeFiberKeysAfterFiber72 ++ [tttLargeFiber76Key]

def tttRemainingLargeFiberKeysAfterFiber76 : List (List LColor) := []

def tttTargetProgressCountsAudit : Bool :=
  tttLightFiberCount == 69
    && tttLightStateCount == 384
    && tttCertifiedLargeFiberKeys.length == 3
    && tttRemainingLargeFiberKeys.length == 9
    && tttCertifiedLargeFiberKeys ++ tttRemainingLargeFiberKeys ==
      tttLargeFiberKeys
    && tttCertifiedStateCount == 1920
    && tttRemainingLargeStateCount == 4608
    && tttCertifiedStateCount + tttRemainingLargeStateCount ==
      tttCompositeStateCount

theorem tttTargetProgressCountsAudit_ok :
    tttTargetProgressCountsAudit = true := by
  decide

def tttLargeFiber20FirstChunkProgressAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block0Chunk0Sources.length ==
      tttLargeFiber20FirstChunkCertifiedRows
    && tttCertifiedStateCountWithFiber20FirstChunk == 1936
    && tttRemainingStateCountAfterFiber20FirstChunk == 4592
    && tttLargeFiber20Block0Chunk0ComponentCertificateAudit

theorem tttLargeFiber20FirstChunkProgressAudit_ok :
    tttLargeFiber20FirstChunkProgressAudit = true := by
  decide

def tttLargeFiber20SecondChunkProgressAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block0Chunk1Sources.length ==
      tttLargeFiber20SecondChunkCertifiedRows
    && tttLargeFiber20Block0Chunk1ComponentCertificateAudit

theorem tttLargeFiber20SecondChunkProgressAudit_ok :
    tttLargeFiber20SecondChunkProgressAudit = true := by
  decide

def tttLargeFiber20FirstTwoChunksProgressAudit : Bool :=
  tttLargeFiber20FirstChunkProgressAudit
    && tttLargeFiber20SecondChunkProgressAudit
    && tttLargeFiber20FirstChunkCertifiedRows +
        tttLargeFiber20SecondChunkCertifiedRows == 32
    && tttCertifiedStateCountWithFiber20FirstTwoChunks == 1952
    && tttRemainingStateCountAfterFiber20FirstTwoChunks == 4576

theorem tttLargeFiber20FirstTwoChunksProgressAudit_ok :
    tttLargeFiber20FirstTwoChunksProgressAudit = true := by
  decide

def tttLargeFiber20Block0ProgressAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block0CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block0 == 1984
    && tttRemainingStateCountAfterFiber20Block0 == 4544
    && tttLargeFiber20Block0ComponentCertificateAudit

theorem tttLargeFiber20Block0ProgressAudit_ok :
    tttLargeFiber20Block0ProgressAudit = true := by
  decide

def tttLargeFiber20Block1ProgressAudit : Bool :=
  tttLargeFiber20Block0ProgressAudit
    && tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block1CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block1 == 2048
    && tttRemainingStateCountAfterFiber20Block1 == 4480
    && tttLargeFiber20Block1ComponentCertificateAudit

theorem tttLargeFiber20Block1ProgressAudit_ok :
    tttLargeFiber20Block1ProgressAudit = true := by
  decide

def tttLargeFiber20Block2CountAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block2CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block2 == 2112
    && tttRemainingStateCountAfterFiber20Block2 == 4416

theorem tttLargeFiber20Block2CountAudit_ok :
    tttLargeFiber20Block2CountAudit = true := by
  decide

def tttLargeFiber20Block2ProgressAudit : Bool :=
  tttLargeFiber20Block1ProgressAudit
    && tttLargeFiber20Block2CountAudit
    && tttLargeFiber20Block2ComponentCertificateAudit

theorem tttLargeFiber20Block2ProgressAudit_ok :
    tttLargeFiber20Block2ProgressAudit = true := by
  simp [tttLargeFiber20Block2ProgressAudit,
    tttLargeFiber20Block1ProgressAudit_ok,
    tttLargeFiber20Block2CountAudit_ok,
    tttLargeFiber20Block2ComponentCertificateAudit_ok]

def tttLargeFiber20Block3CountAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block3CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block3 == 2176
    && tttRemainingStateCountAfterFiber20Block3 == 4352

theorem tttLargeFiber20Block3CountAudit_ok :
    tttLargeFiber20Block3CountAudit = true := by
  decide

def tttLargeFiber20Block3ProgressAudit : Bool :=
  tttLargeFiber20Block2ProgressAudit
    && tttLargeFiber20Block3CountAudit
    && tttLargeFiber20Block3ComponentCertificateAudit

theorem tttLargeFiber20Block3ProgressAudit_ok :
    tttLargeFiber20Block3ProgressAudit = true := by
  simp [tttLargeFiber20Block3ProgressAudit,
    tttLargeFiber20Block2ProgressAudit_ok,
    tttLargeFiber20Block3CountAudit_ok,
    tttLargeFiber20Block3ComponentCertificateAudit_ok]

def tttLargeFiber20Block4CountAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block4CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block4 == 2240
    && tttRemainingStateCountAfterFiber20Block4 == 4288

theorem tttLargeFiber20Block4CountAudit_ok :
    tttLargeFiber20Block4CountAudit = true := by
  decide

def tttLargeFiber20Block4ProgressAudit : Bool :=
  tttLargeFiber20Block3ProgressAudit
    && tttLargeFiber20Block4CountAudit
    && tttLargeFiber20Block4ComponentCertificateAudit

theorem tttLargeFiber20Block4ProgressAudit_ok :
    tttLargeFiber20Block4ProgressAudit = true := by
  simp [tttLargeFiber20Block4ProgressAudit,
    tttLargeFiber20Block3ProgressAudit_ok,
    tttLargeFiber20Block4CountAudit_ok,
    tttLargeFiber20Block4ComponentCertificateAudit_ok]

def tttLargeFiber20Block5CountAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block5CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block5 == 2304
    && tttRemainingStateCountAfterFiber20Block5 == 4224

theorem tttLargeFiber20Block5CountAudit_ok :
    tttLargeFiber20Block5CountAudit = true := by
  decide

def tttLargeFiber20Block5ProgressAudit : Bool :=
  tttLargeFiber20Block4ProgressAudit
    && tttLargeFiber20Block5CountAudit
    && tttLargeFiber20Block5ComponentCertificateAudit

theorem tttLargeFiber20Block5ProgressAudit_ok :
    tttLargeFiber20Block5ProgressAudit = true := by
  simp [tttLargeFiber20Block5ProgressAudit,
    tttLargeFiber20Block4ProgressAudit_ok,
    tttLargeFiber20Block5CountAudit_ok,
    tttLargeFiber20Block5ComponentCertificateAudit_ok]

def tttLargeFiber20Block6CountAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block6CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block6 == 2368
    && tttRemainingStateCountAfterFiber20Block6 == 4160

theorem tttLargeFiber20Block6CountAudit_ok :
    tttLargeFiber20Block6CountAudit = true := by
  decide

def tttLargeFiber20Block6ProgressAudit : Bool :=
  tttLargeFiber20Block5ProgressAudit
    && tttLargeFiber20Block6CountAudit
    && tttLargeFiber20Block6ComponentCertificateAudit

theorem tttLargeFiber20Block6ProgressAudit_ok :
    tttLargeFiber20Block6ProgressAudit = true := by
  simp [tttLargeFiber20Block6ProgressAudit,
    tttLargeFiber20Block5ProgressAudit_ok,
    tttLargeFiber20Block6CountAudit_ok,
    tttLargeFiber20Block6ComponentCertificateAudit_ok]

def tttLargeFiber20Block7CountAudit : Bool :=
  tttRemainingLargeFiberKeys.contains tttLargeFiber20Key
    && tttLargeFiber20Key ==
      [LColor.r, LColor.p, LColor.r, LColor.p]
    && tttLargeFiber20Block7CertifiedRows == 64
    && tttCertifiedStateCountWithFiber20Block7 == 2432
    && tttRemainingStateCountAfterFiber20Block7 == 4096

theorem tttLargeFiber20Block7CountAudit_ok :
    tttLargeFiber20Block7CountAudit = true := by
  decide

def tttLargeFiber20Block7ProgressAudit : Bool :=
  tttLargeFiber20Block6ProgressAudit
    && tttLargeFiber20Block7CountAudit
    && tttLargeFiber20Block7ComponentCertificateAudit

theorem tttLargeFiber20Block7ProgressAudit_ok :
    tttLargeFiber20Block7ProgressAudit = true := by
  simp [tttLargeFiber20Block7ProgressAudit,
    tttLargeFiber20Block6ProgressAudit_ok,
    tttLargeFiber20Block7CountAudit_ok,
    tttLargeFiber20Block7ComponentCertificateAudit_ok]

def tttLargeFiber20ClosedCountAudit : Bool :=
  tttCertifiedLargeFiberKeysAfterFiber20.length == 4
    && tttRemainingLargeFiberKeysAfterFiber20.length == 8
    && tttCertifiedLargeFiberKeysAfterFiber20 ++
        tttRemainingLargeFiberKeysAfterFiber20 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber20Block7 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber20.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber20Block7 ==
      tttRemainingLargeFiberKeysAfterFiber20.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber20Block7 +
        tttRemainingStateCountAfterFiber20Block7 == tttCompositeStateCount

theorem tttLargeFiber20ClosedCountAudit_ok :
    tttLargeFiber20ClosedCountAudit = true := by
  decide

def tttLargeFiber20ClosedProgressAudit : Bool :=
  tttLargeFiber20Block7ProgressAudit
    && tttLargeFiber20ClosedCountAudit
    && tttLargeFiber20ComponentCertificateAudit

theorem tttLargeFiber20ClosedProgressAudit_ok :
    tttLargeFiber20ClosedProgressAudit = true := by
  simp [tttLargeFiber20ClosedProgressAudit,
    tttLargeFiber20Block7ProgressAudit_ok,
    tttLargeFiber20ClosedCountAudit_ok,
    tttLargeFiber20ComponentCertificateAudit_ok]

def tttLargeFiber30ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber20.contains tttLargeFiber30Key
    && tttLargeFiber30Key ==
      [LColor.b, LColor.r, LColor.b, LColor.r]
    && tttCertifiedLargeFiberKeysAfterFiber30.length == 5
    && tttRemainingLargeFiberKeysAfterFiber30.length == 7
    && tttCertifiedLargeFiberKeysAfterFiber30 ++
        tttRemainingLargeFiberKeysAfterFiber30 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber30 == 2944
    && tttRemainingStateCountAfterFiber30 == 3584
    && tttCertifiedStateCountWithFiber30 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber30.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber30 ==
      tttRemainingLargeFiberKeysAfterFiber30.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber30 +
        tttRemainingStateCountAfterFiber30 == tttCompositeStateCount

theorem tttLargeFiber30ClosedCountAudit_ok :
    tttLargeFiber30ClosedCountAudit = true := by
  decide

def tttLargeFiber30ClosedProgressAudit : Bool :=
  tttLargeFiber20ClosedProgressAudit
    && tttLargeFiber30ClosedCountAudit
    && tttLargeFiber30ComponentCertificateAudit

theorem tttLargeFiber30ClosedProgressAudit_ok :
    tttLargeFiber30ClosedProgressAudit = true := by
  simp [tttLargeFiber30ClosedProgressAudit,
    tttLargeFiber20ClosedProgressAudit_ok,
    tttLargeFiber30ClosedCountAudit_ok,
    tttLargeFiber30ComponentCertificateAudit_ok]

def tttLargeFiber36ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber30.contains tttLargeFiber36Key
    && tttLargeFiber36Key ==
      [LColor.b, LColor.b, LColor.r, LColor.r]
    && tttCertifiedLargeFiberKeysAfterFiber36.length == 6
    && tttRemainingLargeFiberKeysAfterFiber36.length == 6
    && tttCertifiedLargeFiberKeysAfterFiber36 ++
        tttRemainingLargeFiberKeysAfterFiber36 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber36 == 3456
    && tttRemainingStateCountAfterFiber36 == 3072
    && tttCertifiedStateCountWithFiber36 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber36.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber36 ==
      tttRemainingLargeFiberKeysAfterFiber36.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber36 +
        tttRemainingStateCountAfterFiber36 == tttCompositeStateCount

theorem tttLargeFiber36ClosedCountAudit_ok :
    tttLargeFiber36ClosedCountAudit = true := by
  decide

def tttLargeFiber36ClosedProgressAudit : Bool :=
  tttLargeFiber30ClosedProgressAudit
    && tttLargeFiber36ClosedCountAudit
    && tttLargeFiber36ComponentCertificateAudit

theorem tttLargeFiber36ClosedProgressAudit_ok :
    tttLargeFiber36ClosedProgressAudit = true := by
  simp [tttLargeFiber36ClosedProgressAudit,
    tttLargeFiber30ClosedProgressAudit_ok,
    tttLargeFiber36ClosedCountAudit_ok,
    tttLargeFiber36ComponentCertificateAudit_ok]

def tttLargeFiber44ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber36.contains tttLargeFiber44Key
    && tttLargeFiber44Key ==
      [LColor.b, LColor.b, LColor.p, LColor.p]
    && tttCertifiedLargeFiberKeysAfterFiber44.length == 7
    && tttRemainingLargeFiberKeysAfterFiber44.length == 5
    && tttCertifiedLargeFiberKeysAfterFiber44 ++
        tttRemainingLargeFiberKeysAfterFiber44 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber44 == 3968
    && tttRemainingStateCountAfterFiber44 == 2560
    && tttCertifiedStateCountWithFiber44 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber44.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber44 ==
      tttRemainingLargeFiberKeysAfterFiber44.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber44 +
        tttRemainingStateCountAfterFiber44 == tttCompositeStateCount

theorem tttLargeFiber44ClosedCountAudit_ok :
    tttLargeFiber44ClosedCountAudit = true := by
  decide

def tttLargeFiber44ClosedProgressAudit : Bool :=
  tttLargeFiber36ClosedProgressAudit
    && tttLargeFiber44ClosedCountAudit
    && tttLargeFiber44ComponentCertificateAudit

theorem tttLargeFiber44ClosedProgressAudit_ok :
    tttLargeFiber44ClosedProgressAudit = true := by
  simp [tttLargeFiber44ClosedProgressAudit,
    tttLargeFiber36ClosedProgressAudit_ok,
    tttLargeFiber44ClosedCountAudit_ok,
    tttLargeFiber44ComponentCertificateAudit_ok]

def tttLargeFiber50ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber44.contains tttLargeFiber50Key
    && tttLargeFiber50Key ==
      [LColor.b, LColor.p, LColor.b, LColor.p]
    && tttCertifiedLargeFiberKeysAfterFiber50.length == 8
    && tttRemainingLargeFiberKeysAfterFiber50.length == 4
    && tttCertifiedLargeFiberKeysAfterFiber50 ++
        tttRemainingLargeFiberKeysAfterFiber50 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber50 == 4480
    && tttRemainingStateCountAfterFiber50 == 2048
    && tttCertifiedStateCountWithFiber50 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber50.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber50 ==
      tttRemainingLargeFiberKeysAfterFiber50.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber50 +
        tttRemainingStateCountAfterFiber50 == tttCompositeStateCount

theorem tttLargeFiber50ClosedCountAudit_ok :
    tttLargeFiber50ClosedCountAudit = true := by
  decide

def tttLargeFiber50ClosedProgressAudit : Bool :=
  tttLargeFiber44ClosedProgressAudit
    && tttLargeFiber50ClosedCountAudit
    && tttLargeFiber50ComponentCertificateAudit

theorem tttLargeFiber50ClosedProgressAudit_ok :
    tttLargeFiber50ClosedProgressAudit = true := by
  simp [tttLargeFiber50ClosedProgressAudit,
    tttLargeFiber44ClosedProgressAudit_ok,
    tttLargeFiber50ClosedCountAudit_ok,
    tttLargeFiber50ComponentCertificateAudit_ok]

def tttLargeFiber60ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber50.contains tttLargeFiber60Key
    && tttLargeFiber60Key ==
      [LColor.p, LColor.r, LColor.p, LColor.r]
    && tttCertifiedLargeFiberKeysAfterFiber60.length == 9
    && tttRemainingLargeFiberKeysAfterFiber60.length == 3
    && tttCertifiedLargeFiberKeysAfterFiber60 ++
        tttRemainingLargeFiberKeysAfterFiber60 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber60 == 4992
    && tttRemainingStateCountAfterFiber60 == 1536
    && tttCertifiedStateCountWithFiber60 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber60.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber60 ==
      tttRemainingLargeFiberKeysAfterFiber60.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber60 +
        tttRemainingStateCountAfterFiber60 == tttCompositeStateCount

theorem tttLargeFiber60ClosedCountAudit_ok :
    tttLargeFiber60ClosedCountAudit = true := by
  decide

def tttLargeFiber60ClosedProgressAudit : Bool :=
  tttLargeFiber50ClosedProgressAudit
    && tttLargeFiber60ClosedCountAudit
    && tttLargeFiber60ComponentCertificateAudit

theorem tttLargeFiber60ClosedProgressAudit_ok :
    tttLargeFiber60ClosedProgressAudit = true := by
  simp [tttLargeFiber60ClosedProgressAudit,
    tttLargeFiber50ClosedProgressAudit_ok,
    tttLargeFiber60ClosedCountAudit_ok,
    tttLargeFiber60ComponentCertificateAudit_ok]

def tttLargeFiber70ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber60.contains tttLargeFiber70Key
    && tttLargeFiber70Key ==
      [LColor.p, LColor.b, LColor.p, LColor.b]
    && tttCertifiedLargeFiberKeysAfterFiber70.length == 10
    && tttRemainingLargeFiberKeysAfterFiber70.length == 2
    && tttCertifiedLargeFiberKeysAfterFiber70 ++
        tttRemainingLargeFiberKeysAfterFiber70 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber70 == 5504
    && tttRemainingStateCountAfterFiber70 == 1024
    && tttCertifiedStateCountWithFiber70 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber70.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber70 ==
      tttRemainingLargeFiberKeysAfterFiber70.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber70 +
        tttRemainingStateCountAfterFiber70 == tttCompositeStateCount

theorem tttLargeFiber70ClosedCountAudit_ok :
    tttLargeFiber70ClosedCountAudit = true := by
  decide

def tttLargeFiber70ClosedProgressAudit : Bool :=
  tttLargeFiber60ClosedProgressAudit
    && tttLargeFiber70ClosedCountAudit
    && tttLargeFiber70ComponentCertificateAudit

theorem tttLargeFiber70ClosedProgressAudit_ok :
    tttLargeFiber70ClosedProgressAudit = true := by
  simp [tttLargeFiber70ClosedProgressAudit,
    tttLargeFiber60ClosedProgressAudit_ok,
    tttLargeFiber70ClosedCountAudit_ok,
    tttLargeFiber70ComponentCertificateAudit_ok]

def tttLargeFiber72ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber70.contains tttLargeFiber72Key
    && tttLargeFiber72Key ==
      [LColor.p, LColor.p, LColor.r, LColor.r]
    && tttCertifiedLargeFiberKeysAfterFiber72.length == 11
    && tttRemainingLargeFiberKeysAfterFiber72.length == 1
    && tttCertifiedLargeFiberKeysAfterFiber72 ++
        tttRemainingLargeFiberKeysAfterFiber72 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber72 == 6016
    && tttRemainingStateCountAfterFiber72 == 512
    && tttCertifiedStateCountWithFiber72 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber72.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber72 ==
      tttRemainingLargeFiberKeysAfterFiber72.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber72 +
        tttRemainingStateCountAfterFiber72 == tttCompositeStateCount

theorem tttLargeFiber72ClosedCountAudit_ok :
    tttLargeFiber72ClosedCountAudit = true := by
  decide

def tttLargeFiber72ClosedProgressAudit : Bool :=
  tttLargeFiber70ClosedProgressAudit
    && tttLargeFiber72ClosedCountAudit
    && tttLargeFiber72ComponentCertificateAudit

theorem tttLargeFiber72ClosedProgressAudit_ok :
    tttLargeFiber72ClosedProgressAudit = true := by
  simp [tttLargeFiber72ClosedProgressAudit,
    tttLargeFiber70ClosedProgressAudit_ok,
    tttLargeFiber72ClosedCountAudit_ok,
    tttLargeFiber72ComponentCertificateAudit_ok]

def tttLargeFiber76ClosedCountAudit : Bool :=
  tttRemainingLargeFiberKeysAfterFiber72.contains tttLargeFiber76Key
    && tttLargeFiber76Key ==
      [LColor.p, LColor.p, LColor.b, LColor.b]
    && tttCertifiedLargeFiberKeysAfterFiber76.length == 12
    && tttRemainingLargeFiberKeysAfterFiber76.length == 0
    && tttCertifiedLargeFiberKeysAfterFiber76 ++
        tttRemainingLargeFiberKeysAfterFiber76 == tttLargeFiberKeys
    && tttCertifiedStateCountWithFiber76 == 6528
    && tttRemainingStateCountAfterFiber76 == 0
    && tttCertifiedStateCountWithFiber76 ==
      tttLightStateCount +
        tttCertifiedLargeFiberKeysAfterFiber76.length * tttRemainingLargeFiberSize
    && tttRemainingStateCountAfterFiber76 ==
      tttRemainingLargeFiberKeysAfterFiber76.length * tttRemainingLargeFiberSize
    && tttCertifiedStateCountWithFiber76 +
        tttRemainingStateCountAfterFiber76 == tttCompositeStateCount

theorem tttLargeFiber76ClosedCountAudit_ok :
    tttLargeFiber76ClosedCountAudit = true := by
  decide

def tttLargeFiber76ClosedProgressAudit : Bool :=
  tttLargeFiber72ClosedProgressAudit
    && tttLargeFiber76ClosedCountAudit
    && tttLargeFiber76ComponentCertificateAudit

theorem tttLargeFiber76ClosedProgressAudit_ok :
    tttLargeFiber76ClosedProgressAudit = true := by
  simp [tttLargeFiber76ClosedProgressAudit,
    tttLargeFiber72ClosedProgressAudit_ok,
    tttLargeFiber76ClosedCountAudit_ok,
    tttLargeFiber76ComponentCertificateAudit_ok]

def tttMode09WitnessAudit : Bool :=
  semanticWitnessForMode FrontierMode.mode09 ==
      SemanticModeWitness.target RepresentativeSemanticTarget.ttt
    && targetFrontierWord RepresentativeSemanticTarget.ttt == tttFrontierWord
    && targetFrontierMode RepresentativeSemanticTarget.ttt ==
      FrontierMode.mode09
    && wordMode tttFrontierWord == some FrontierMode.mode09

theorem tttMode09WitnessAudit_ok :
    tttMode09WitnessAudit = true := by
  rfl

/--
The length-two `TT` obstruction key is the same fixed input as the generated
`TTT` light-fiber row table at index 32.  The table has twice as many generated
rows after appending `T`; this is a table-level cardinality check, not the
surjective projection witness required by the append parent-row route.
-/
theorem tttFiber32Rows_length_eq_two_mul_ttFiber32Rows_length :
    GoertzelLemma818TripleTauLightComponentCertificate.tttFiber32Key =
      GoertzelLemma818CompositeCertificate.ttFiber32Key ∧
    GoertzelLemma818CompositeCertificate.ttFiber32Rows.length = 8 ∧
    GoertzelLemma818TripleTauLightComponentCertificate.tttFiber32Rows.length =
      2 * GoertzelLemma818CompositeCertificate.ttFiber32Rows.length := by
  decide

def ttFiber32RowIndexToTttFiber32RowIndexCore (i : Fin 8) : Fin 16 :=
  ⟨2 * i.1, by
    have hlt : 2 * i.1 < 2 * 8 :=
      Nat.mul_lt_mul_of_pos_left i.2 (by decide)
    simpa using hlt⟩

theorem ttFiber32RowIndexToTttFiber32RowIndexCore_injective :
    Function.Injective ttFiber32RowIndexToTttFiber32RowIndexCore := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
    (by simpa [ttFiber32RowIndexToTttFiber32RowIndexCore] using hval)

def ttFiber32RowIndexToTttFiber32RowIndex
    (i : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) :
    Fin GoertzelLemma818TripleTauLightComponentCertificate.tttFiber32Rows.length :=
  Fin.cast (by decide :
      16 =
        GoertzelLemma818TripleTauLightComponentCertificate.tttFiber32Rows.length)
    (ttFiber32RowIndexToTttFiber32RowIndexCore
      (Fin.cast (by decide :
          GoertzelLemma818CompositeCertificate.ttFiber32Rows.length = 8) i))

theorem ttFiber32RowIndexToTttFiber32RowIndex_injective :
    Function.Injective ttFiber32RowIndexToTttFiber32RowIndex := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  have hcore :
      ttFiber32RowIndexToTttFiber32RowIndexCore
          (Fin.cast (by decide :
            GoertzelLemma818CompositeCertificate.ttFiber32Rows.length = 8) i) =
        ttFiber32RowIndexToTttFiber32RowIndexCore
          (Fin.cast (by decide :
            GoertzelLemma818CompositeCertificate.ttFiber32Rows.length = 8) j) := by
    apply Fin.ext
    simpa [ttFiber32RowIndexToTttFiber32RowIndex] using hval
  have hcast :=
    ttFiber32RowIndexToTttFiber32RowIndexCore_injective hcore
  exact congrArg Fin.val hcast

theorem ttFiber32SelectedTttFiber32Row_source_eq :
    ∀ i : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length,
      (GoertzelLemma818TripleTauLightComponentCertificate.tttFiber32Rows.get
        (ttFiber32RowIndexToTttFiber32RowIndex i)).source =
        256 + 2 * i.1 := by
  decide

def ttFiber32FrontierWord : List GoertzelLemma818FrontierMode.TauOrient :=
  [ GoertzelLemma818FrontierMode.TauOrient.tau
  , GoertzelLemma818FrontierMode.TauOrient.tau
  ]

def ttFiber32PrefixStates
    (i : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) :
    List TauState :=
  GoertzelLemma818LengthTwoShapeBBridge.ttFiber32StateAt i.1

theorem ttFiber32PrefixStates_mem_concreteChainFiber :
    ∀ i : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length,
      ttFiber32PrefixStates i ∈
        concreteChainFiber ttFiber32FrontierWord
          GoertzelLemma818CompositeCertificate.ttFiber32Key := by
  decide

def ttFiber32PrefixPoint
    (i : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) :
    ChainFiberPoint ttFiber32FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber32Key :=
  ⟨ttFiber32PrefixStates i, ttFiber32PrefixStates_mem_concreteChainFiber i⟩

def ttFiber32PrefixStatesList : List (List TauState) :=
  [ ttFiber32PrefixStates ⟨0, by decide⟩
  , ttFiber32PrefixStates ⟨1, by decide⟩
  , ttFiber32PrefixStates ⟨2, by decide⟩
  , ttFiber32PrefixStates ⟨3, by decide⟩
  , ttFiber32PrefixStates ⟨4, by decide⟩
  , ttFiber32PrefixStates ⟨5, by decide⟩
  , ttFiber32PrefixStates ⟨6, by decide⟩
  , ttFiber32PrefixStates ⟨7, by decide⟩
  ]

theorem ttFiber32PrefixStatesList_nodup :
    ttFiber32PrefixStatesList.Nodup := by
  decide

theorem ttFiber32PrefixStatesList_eq_concreteChainFiber :
    ttFiber32PrefixStatesList =
      concreteChainFiber ttFiber32FrontierWord
        GoertzelLemma818CompositeCertificate.ttFiber32Key := by
  unfold concreteChainFiber concreteChainStates ttFiber32FrontierWord
  change ttFiber32PrefixStatesList =
    chainFiberFrom GoertzelLemma818CompositeCertificate.ttWord
      (allChainStates GoertzelLemma818CompositeCertificate.ttWord)
      GoertzelLemma818CompositeCertificate.ttFiber32Key
  rw [GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber32RealFiber_eq_direct]
  decide

theorem ttFiber32PrefixPoint_surjective :
    ∀ point : ChainFiberPoint ttFiber32FrontierWord
        GoertzelLemma818CompositeCertificate.ttFiber32Key,
      ∃ i : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length,
        ttFiber32PrefixPoint i = point := by
  intro point
  have hmem : point.1 ∈ ttFiber32PrefixStatesList := by
    rw [ttFiber32PrefixStatesList_eq_concreteChainFiber]
    exact point.2
  simp only [ttFiber32PrefixStatesList, List.mem_cons, List.not_mem_nil] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h
  · refine ⟨⟨0, by decide⟩, ?_⟩
    apply Subtype.ext
    exact h.symm
  · refine ⟨⟨1, by decide⟩, ?_⟩
    apply Subtype.ext
    exact h.symm
  · refine ⟨⟨2, by decide⟩, ?_⟩
    apply Subtype.ext
    exact h.symm
  · refine ⟨⟨3, by decide⟩, ?_⟩
    apply Subtype.ext
    exact h.symm
  · refine ⟨⟨4, by decide⟩, ?_⟩
    apply Subtype.ext
    exact h.symm
  · refine ⟨⟨5, by decide⟩, ?_⟩
    apply Subtype.ext
    exact h.symm
  · refine ⟨⟨6, by decide⟩, ?_⟩
    apply Subtype.ext
    exact h.symm
  · refine ⟨⟨7, by decide⟩, ?_⟩
    apply Subtype.ext
    exact h.symm
  · cases h

noncomputable def ttFiber32PrefixPointIndex
    (point : ChainFiberPoint ttFiber32FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber32Key) :
    Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length :=
  Classical.choose (ttFiber32PrefixPoint_surjective point)

theorem ttFiber32PrefixPointIndex_spec
    (point : ChainFiberPoint ttFiber32FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber32Key) :
    ttFiber32PrefixPoint (ttFiber32PrefixPointIndex point) = point :=
  Classical.choose_spec (ttFiber32PrefixPoint_surjective point)

def ttFiber32SelectedTttFiber32States
    (i : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) :
    List TauState :=
  let row :=
    GoertzelLemma818TripleTauLightComponentCertificate.tttFiber32Rows.get
      (ttFiber32RowIndexToTttFiber32RowIndex i)
  tripleStates row.sourceLeft row.sourceMiddle row.sourceRight

theorem ttFiber32SelectedTttFiber32States_0_mem_concreteChainFiber :
    ttFiber32SelectedTttFiber32States ⟨0, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber32Key := by
  decide

theorem ttFiber32SelectedTttFiber32States_1_mem_concreteChainFiber :
    ttFiber32SelectedTttFiber32States ⟨1, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber32Key := by
  decide

theorem ttFiber32SelectedTttFiber32States_2_mem_concreteChainFiber :
    ttFiber32SelectedTttFiber32States ⟨2, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber32Key := by
  decide

theorem ttFiber32SelectedTttFiber32States_3_mem_concreteChainFiber :
    ttFiber32SelectedTttFiber32States ⟨3, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber32Key := by
  decide

theorem ttFiber32SelectedTttFiber32States_4_mem_concreteChainFiber :
    ttFiber32SelectedTttFiber32States ⟨4, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber32Key := by
  decide

theorem ttFiber32SelectedTttFiber32States_5_mem_concreteChainFiber :
    ttFiber32SelectedTttFiber32States ⟨5, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber32Key := by
  decide

theorem ttFiber32SelectedTttFiber32States_6_mem_concreteChainFiber :
    ttFiber32SelectedTttFiber32States ⟨6, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber32Key := by
  decide

theorem ttFiber32SelectedTttFiber32States_7_mem_concreteChainFiber :
    ttFiber32SelectedTttFiber32States ⟨7, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber32Key := by
  decide

theorem ttFiber32SelectedTttFiber32States_mem_concreteChainFiber :
    ∀ i : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length,
      ttFiber32SelectedTttFiber32States i ∈
        concreteChainFiber tttFrontierWord tttFiber32Key := by
  intro i
  rcases i with ⟨n, hn⟩
  have hn8 : n < 8 := by
    simpa [GoertzelLemma818CompositeCertificate.ttFiber32Rows] using hn
  by_cases h0 : n = 0
  · subst n
    have hfin :
        (⟨0, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) =
          ⟨0, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber32SelectedTttFiber32States_0_mem_concreteChainFiber
  by_cases h1 : n = 1
  · subst n
    have hfin :
        (⟨1, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) =
          ⟨1, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber32SelectedTttFiber32States_1_mem_concreteChainFiber
  by_cases h2 : n = 2
  · subst n
    have hfin :
        (⟨2, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) =
          ⟨2, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber32SelectedTttFiber32States_2_mem_concreteChainFiber
  by_cases h3 : n = 3
  · subst n
    have hfin :
        (⟨3, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) =
          ⟨3, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber32SelectedTttFiber32States_3_mem_concreteChainFiber
  by_cases h4 : n = 4
  · subst n
    have hfin :
        (⟨4, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) =
          ⟨4, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber32SelectedTttFiber32States_4_mem_concreteChainFiber
  by_cases h5 : n = 5
  · subst n
    have hfin :
        (⟨5, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) =
          ⟨5, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber32SelectedTttFiber32States_5_mem_concreteChainFiber
  by_cases h6 : n = 6
  · subst n
    have hfin :
        (⟨6, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) =
          ⟨6, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber32SelectedTttFiber32States_6_mem_concreteChainFiber
  have h7 : n = 7 := by omega
  subst n
  have hfin :
      (⟨7, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) =
        ⟨7, by decide⟩ := by
    apply Fin.ext
    rfl
  rw [hfin]
  exact ttFiber32SelectedTttFiber32States_7_mem_concreteChainFiber

def ttFiber32SelectedTttFiber32Point
    (i : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) :
    ChainFiberPoint tttFrontierWord tttFiber32Key :=
  ⟨ttFiber32SelectedTttFiber32States i,
    ttFiber32SelectedTttFiber32States_mem_concreteChainFiber i⟩

def ttFiber32SelectedTttFiber32PointList :
    List (ChainFiberPoint tttFrontierWord tttFiber32Key) :=
  [ ⟨ttFiber32SelectedTttFiber32States ⟨0, by decide⟩,
      ttFiber32SelectedTttFiber32States_0_mem_concreteChainFiber⟩
  , ⟨ttFiber32SelectedTttFiber32States ⟨1, by decide⟩,
      ttFiber32SelectedTttFiber32States_1_mem_concreteChainFiber⟩
  , ⟨ttFiber32SelectedTttFiber32States ⟨2, by decide⟩,
      ttFiber32SelectedTttFiber32States_2_mem_concreteChainFiber⟩
  , ⟨ttFiber32SelectedTttFiber32States ⟨3, by decide⟩,
      ttFiber32SelectedTttFiber32States_3_mem_concreteChainFiber⟩
  , ⟨ttFiber32SelectedTttFiber32States ⟨4, by decide⟩,
      ttFiber32SelectedTttFiber32States_4_mem_concreteChainFiber⟩
  , ⟨ttFiber32SelectedTttFiber32States ⟨5, by decide⟩,
      ttFiber32SelectedTttFiber32States_5_mem_concreteChainFiber⟩
  , ⟨ttFiber32SelectedTttFiber32States ⟨6, by decide⟩,
      ttFiber32SelectedTttFiber32States_6_mem_concreteChainFiber⟩
  , ⟨ttFiber32SelectedTttFiber32States ⟨7, by decide⟩,
      ttFiber32SelectedTttFiber32States_7_mem_concreteChainFiber⟩
  ]

def ttFiber32SelectedTttFiber32PointAt
    (i : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length) :
    ChainFiberPoint tttFrontierWord tttFiber32Key :=
  ttFiber32SelectedTttFiber32PointList.get
    (Fin.cast (by decide :
        GoertzelLemma818CompositeCertificate.ttFiber32Rows.length =
          ttFiber32SelectedTttFiber32PointList.length) i)

theorem ttFiber32SelectedTttFiber32PointAt_value_eq :
    ∀ i : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length,
      (ttFiber32SelectedTttFiber32PointAt i).1 =
        ttFiber32SelectedTttFiber32States i := by
  decide

def ttFiber32SelectedTttFiber32StatesIndex
    (states : List TauState) : Nat :=
  if states = ttFiber32SelectedTttFiber32States ⟨0, by decide⟩ then 0
  else if states = ttFiber32SelectedTttFiber32States ⟨1, by decide⟩ then 1
  else if states = ttFiber32SelectedTttFiber32States ⟨2, by decide⟩ then 2
  else if states = ttFiber32SelectedTttFiber32States ⟨3, by decide⟩ then 3
  else if states = ttFiber32SelectedTttFiber32States ⟨4, by decide⟩ then 4
  else if states = ttFiber32SelectedTttFiber32States ⟨5, by decide⟩ then 5
  else if states = ttFiber32SelectedTttFiber32States ⟨6, by decide⟩ then 6
  else if states = ttFiber32SelectedTttFiber32States ⟨7, by decide⟩ then 7
  else 8

theorem ttFiber32SelectedTttFiber32StatesIndex_selected :
    ∀ i : Fin GoertzelLemma818CompositeCertificate.ttFiber32Rows.length,
      ttFiber32SelectedTttFiber32StatesIndex
        (ttFiber32SelectedTttFiber32States i) = i.1 := by
  decide

theorem ttFiber32SelectedTttFiber32States_injective :
    Function.Injective ttFiber32SelectedTttFiber32States := by
  intro i j h
  have hindex := congrArg ttFiber32SelectedTttFiber32StatesIndex h
  rw [ttFiber32SelectedTttFiber32StatesIndex_selected i,
    ttFiber32SelectedTttFiber32StatesIndex_selected j] at hindex
  exact Fin.ext hindex

theorem ttFiber32SelectedTttFiber32PointAt_injective :
    Function.Injective ttFiber32SelectedTttFiber32PointAt := by
  intro i j h
  have hstates :
      ttFiber32SelectedTttFiber32States i =
        ttFiber32SelectedTttFiber32States j := by
    have hval := congrArg Subtype.val h
    simpa [ttFiber32SelectedTttFiber32PointAt_value_eq] using hval
  exact ttFiber32SelectedTttFiber32States_injective hstates

noncomputable def ttFiber32SelectedTttFiber32PointOfPrefixPoint
    (point : ChainFiberPoint ttFiber32FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber32Key) :
    ChainFiberPoint tttFrontierWord tttFiber32Key :=
  ttFiber32SelectedTttFiber32PointAt (ttFiber32PrefixPointIndex point)

theorem ttFiber32SelectedTttFiber32PointOfPrefixPoint_injective :
    Function.Injective ttFiber32SelectedTttFiber32PointOfPrefixPoint := by
  intro a b h
  have hindex :
      ttFiber32PrefixPointIndex a = ttFiber32PrefixPointIndex b :=
    ttFiber32SelectedTttFiber32PointAt_injective h
  calc
    a = ttFiber32PrefixPoint (ttFiber32PrefixPointIndex a) :=
      (ttFiber32PrefixPointIndex_spec a).symm
    _ = ttFiber32PrefixPoint (ttFiber32PrefixPointIndex b) := by
      rw [hindex]
    _ = b :=
      ttFiber32PrefixPointIndex_spec b

theorem ttFiber32ProjectionInjectivePreimage :
    ∃ preimageOf :
      ChainFiberPoint ttFiber32FrontierWord
        GoertzelLemma818CompositeCertificate.ttFiber32Key →
        ChainFiberPoint tttFrontierWord tttFiber32Key,
      Function.Injective preimageOf :=
  ⟨ttFiber32SelectedTttFiber32PointOfPrefixPoint,
    ttFiber32SelectedTttFiber32PointOfPrefixPoint_injective⟩

theorem ttFiber32AppendProjectionInjectivePreimage :
    ∃ preimageOf :
      ChainFiberPoint ttFiber32FrontierWord
        GoertzelLemma818CompositeCertificate.ttFiber32Key →
        ChainFiberPoint
          (ttFiber32FrontierWord ++
            [GoertzelLemma818FrontierMode.TauOrient.tau])
          GoertzelLemma818CompositeCertificate.ttFiber32Key,
      Function.Injective preimageOf := by
  simpa [ttFiber32FrontierWord,
    GoertzelLemma818TripleTauLightComponentCertificate.tttFrontierWord,
    GoertzelLemma818CompositeCertificate.ttFiber32Key,
    GoertzelLemma818TripleTauLightComponentCertificate.tttFiber32Key] using
    ttFiber32ProjectionInjectivePreimage

noncomputable def ttFiber32AppendSelectedPreimage :
    ChainFiberPoint ttFiber32FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber32Key →
      ChainFiberPoint
        (ttFiber32FrontierWord ++
          [GoertzelLemma818FrontierMode.TauOrient.tau])
        GoertzelLemma818CompositeCertificate.ttFiber32Key :=
  Classical.choose ttFiber32AppendProjectionInjectivePreimage

theorem ttFiber32AppendSelectedPreimage_injective :
    Function.Injective ttFiber32AppendSelectedPreimage :=
  Classical.choose_spec ttFiber32AppendProjectionInjectivePreimage

noncomputable def ttFiber32AppendProjection
    (point :
      ChainFiberPoint
        (ttFiber32FrontierWord ++
          [GoertzelLemma818FrontierMode.TauOrient.tau])
        GoertzelLemma818CompositeCertificate.ttFiber32Key) :
    ChainFiberPoint ttFiber32FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber32Key :=
  by
    classical
    exact
      if h : ∃ b :
          ChainFiberPoint ttFiber32FrontierWord
            GoertzelLemma818CompositeCertificate.ttFiber32Key,
          ttFiber32AppendSelectedPreimage b = point then
        Classical.choose h
      else
        ttFiber32PrefixPoint ⟨0, by decide⟩

theorem ttFiber32AppendProjection_section
    (point : ChainFiberPoint ttFiber32FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber32Key) :
    ttFiber32AppendProjection
        (ttFiber32AppendSelectedPreimage point) = point := by
  classical
  change
    (if h : ∃ b : ChainFiberPoint ttFiber32FrontierWord
        GoertzelLemma818CompositeCertificate.ttFiber32Key,
        ttFiber32AppendSelectedPreimage b =
          ttFiber32AppendSelectedPreimage point then
        Classical.choose h
      else
        ttFiber32PrefixPoint ⟨0, by decide⟩) = point
  let witness :
      ∃ b : ChainFiberPoint ttFiber32FrontierWord
        GoertzelLemma818CompositeCertificate.ttFiber32Key,
        ttFiber32AppendSelectedPreimage b =
          ttFiber32AppendSelectedPreimage point :=
    ⟨point, rfl⟩
  have hchoose : Classical.choose witness = point :=
    ttFiber32AppendSelectedPreimage_injective
      (Classical.choose_spec witness)
  rw [dif_pos witness]
  exact hchoose

theorem ttFiber32AppendProjection_surjective :
    ∀ point : ChainFiberPoint ttFiber32FrontierWord
        GoertzelLemma818CompositeCertificate.ttFiber32Key,
      ∃ y : ChainFiberPoint
          (ttFiber32FrontierWord ++
            [GoertzelLemma818FrontierMode.TauOrient.tau])
          GoertzelLemma818CompositeCertificate.ttFiber32Key,
        ttFiber32AppendProjection y = point := by
  intro point
  exact ⟨ttFiber32AppendSelectedPreimage point,
    ttFiber32AppendProjection_section point⟩

theorem ttFiber32AppendProjectionSection :
    ∃ proj :
      ChainFiberPoint
        (ttFiber32FrontierWord ++
          [GoertzelLemma818FrontierMode.TauOrient.tau])
        GoertzelLemma818CompositeCertificate.ttFiber32Key →
        ChainFiberPoint ttFiber32FrontierWord
          GoertzelLemma818CompositeCertificate.ttFiber32Key,
      ∃ preimageOf :
        ChainFiberPoint ttFiber32FrontierWord
          GoertzelLemma818CompositeCertificate.ttFiber32Key →
          ChainFiberPoint
            (ttFiber32FrontierWord ++
              [GoertzelLemma818FrontierMode.TauOrient.tau])
            GoertzelLemma818CompositeCertificate.ttFiber32Key,
        ∀ point : ChainFiberPoint ttFiber32FrontierWord
            GoertzelLemma818CompositeCertificate.ttFiber32Key,
          proj (preimageOf point) = point :=
  ⟨ttFiber32AppendProjection, ttFiber32AppendSelectedPreimage,
    ttFiber32AppendProjection_section⟩

def ttFiber32SelectedTttFiber32StatesList : List (List TauState) :=
  [ ttFiber32SelectedTttFiber32States ⟨0, by decide⟩
  , ttFiber32SelectedTttFiber32States ⟨1, by decide⟩
  , ttFiber32SelectedTttFiber32States ⟨2, by decide⟩
  , ttFiber32SelectedTttFiber32States ⟨3, by decide⟩
  , ttFiber32SelectedTttFiber32States ⟨4, by decide⟩
  , ttFiber32SelectedTttFiber32States ⟨5, by decide⟩
  , ttFiber32SelectedTttFiber32States ⟨6, by decide⟩
  , ttFiber32SelectedTttFiber32States ⟨7, by decide⟩
  ]

theorem ttFiber32SelectedTttFiber32StatesList_nodup :
    ttFiber32SelectedTttFiber32StatesList.Nodup := by
  decide

def tttPartialTargetCertificateAudit : Bool :=
  tttMode09WitnessAudit
    && tttTargetProgressCountsAudit
    && tttLightComponentCertificateAudit
    && tttLargeFiber4ComponentCertificateAudit
    && tttLargeFiber8ComponentCertificateAudit
    && tttLargeFiber10ComponentCertificateAudit
    && tttLargeFiber20ClosedProgressAudit
    && tttLargeFiber30ClosedProgressAudit
    && tttLargeFiber36ClosedProgressAudit
    && tttLargeFiber44ClosedProgressAudit
    && tttLargeFiber50ClosedProgressAudit
    && tttLargeFiber60ClosedProgressAudit
    && tttLargeFiber70ClosedProgressAudit
    && tttLargeFiber72ClosedProgressAudit
    && tttLargeFiber76ClosedProgressAudit

/--
The currently checked `TTT`/`mode09` semantic surface.

This proves the explicit representative-target progress: the light fibers plus
all twelve large fibers are certified.  It does not prove the remaining
thirteen representative targets or all-chain `LKR_in`.
-/
theorem tttPartialTargetCertificateAudit_ok :
    tttPartialTargetCertificateAudit = true := by
  simp [tttPartialTargetCertificateAudit,
    tttMode09WitnessAudit_ok,
    tttTargetProgressCountsAudit_ok,
    tttLightComponentCertificateAudit_ok,
    tttLargeFiber4ComponentCertificateAudit_ok,
    tttLargeFiber8ComponentCertificateAudit_ok,
    tttLargeFiber10ComponentCertificateAudit_ok,
    tttLargeFiber20ClosedProgressAudit_ok,
    tttLargeFiber30ClosedProgressAudit_ok,
    tttLargeFiber36ClosedProgressAudit_ok,
    tttLargeFiber44ClosedProgressAudit_ok,
    tttLargeFiber50ClosedProgressAudit_ok,
    tttLargeFiber60ClosedProgressAudit_ok,
    tttLargeFiber70ClosedProgressAudit_ok,
    tttLargeFiber72ClosedProgressAudit_ok,
    tttLargeFiber76ClosedProgressAudit_ok]

def tttTargetCertificateAudit : Bool :=
  tttPartialTargetCertificateAudit

theorem tttTargetCertificateAudit_ok :
    tttTargetCertificateAudit = true := by
  simpa [tttTargetCertificateAudit] using tttPartialTargetCertificateAudit_ok

end GoertzelLemma818TripleTauTargetProgress

end Mettapedia.GraphTheory.FourColor
