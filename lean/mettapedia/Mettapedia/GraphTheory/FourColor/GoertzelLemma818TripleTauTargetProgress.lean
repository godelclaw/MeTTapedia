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

def ttFiber32PrefixPointList :
    List (ChainFiberPoint ttFiber32FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber32Key) :=
  [ ttFiber32PrefixPoint ⟨0, by decide⟩
  , ttFiber32PrefixPoint ⟨1, by decide⟩
  , ttFiber32PrefixPoint ⟨2, by decide⟩
  , ttFiber32PrefixPoint ⟨3, by decide⟩
  , ttFiber32PrefixPoint ⟨4, by decide⟩
  , ttFiber32PrefixPoint ⟨5, by decide⟩
  , ttFiber32PrefixPoint ⟨6, by decide⟩
  , ttFiber32PrefixPoint ⟨7, by decide⟩
  ]

theorem ttFiber32PrefixPointList_mem
    (point : ChainFiberPoint ttFiber32FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber32Key) :
    point ∈ ttFiber32PrefixPointList := by
  rcases ttFiber32PrefixPoint_surjective point with ⟨i, rfl⟩
  rcases i with ⟨n, hn⟩
  have hn8 : n < 8 := by
    simpa [GoertzelLemma818CompositeCertificate.ttFiber32Rows] using hn
  by_cases h0 : n = 0
  · subst n
    simp [ttFiber32PrefixPointList]
  by_cases h1 : n = 1
  · subst n
    simp [ttFiber32PrefixPointList]
  by_cases h2 : n = 2
  · subst n
    simp [ttFiber32PrefixPointList]
  by_cases h3 : n = 3
  · subst n
    simp [ttFiber32PrefixPointList]
  by_cases h4 : n = 4
  · subst n
    simp [ttFiber32PrefixPointList]
  by_cases h5 : n = 5
  · subst n
    simp [ttFiber32PrefixPointList]
  by_cases h6 : n = 6
  · subst n
    simp [ttFiber32PrefixPointList]
  have h7 : n = 7 := by omega
  subst n
  simp [ttFiber32PrefixPointList]

noncomputable def ttFiber32AppendPreimageRows :
    List
      (ChainFiberPoint
        (ttFiber32FrontierWord ++
          [GoertzelLemma818FrontierMode.TauOrient.tau])
        GoertzelLemma818CompositeCertificate.ttFiber32Key) :=
  ttFiber32PrefixPointList.map ttFiber32AppendSelectedPreimage

theorem ttFiber32AppendSelectedPreimage_mem_rows
    (point : ChainFiberPoint ttFiber32FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber32Key) :
    ttFiber32AppendSelectedPreimage point ∈
      ttFiber32AppendPreimageRows :=
  List.mem_map.mpr ⟨point, ttFiber32PrefixPointList_mem point, rfl⟩

noncomputable def ttFiber32AppendPreimageRowOf
    (point : ChainFiberPoint ttFiber32FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber32Key) :
    Fin ttFiber32AppendPreimageRows.length :=
  Classical.choose
    (List.get_of_mem (ttFiber32AppendSelectedPreimage_mem_rows point))

theorem ttFiber32AppendPreimageRows_get_rowOf
    (point : ChainFiberPoint ttFiber32FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber32Key) :
    ttFiber32AppendPreimageRows.get
        (ttFiber32AppendPreimageRowOf point) =
      ttFiber32AppendSelectedPreimage point :=
  Classical.choose_spec
    (List.get_of_mem (ttFiber32AppendSelectedPreimage_mem_rows point))

theorem ttFiber32AppendProjectionFiniteSection :
    ∃ proj :
      ChainFiberPoint
        (ttFiber32FrontierWord ++
          [GoertzelLemma818FrontierMode.TauOrient.tau])
        GoertzelLemma818CompositeCertificate.ttFiber32Key →
        ChainFiberPoint ttFiber32FrontierWord
          GoertzelLemma818CompositeCertificate.ttFiber32Key,
      ∃ preimageRows :
        List
          (ChainFiberPoint
            (ttFiber32FrontierWord ++
              [GoertzelLemma818FrontierMode.TauOrient.tau])
            GoertzelLemma818CompositeCertificate.ttFiber32Key),
        ∃ rowOf :
          ChainFiberPoint ttFiber32FrontierWord
            GoertzelLemma818CompositeCertificate.ttFiber32Key →
            Fin preimageRows.length,
          ∀ point : ChainFiberPoint ttFiber32FrontierWord
              GoertzelLemma818CompositeCertificate.ttFiber32Key,
            proj (preimageRows.get (rowOf point)) = point := by
  refine ⟨ttFiber32AppendProjection, ttFiber32AppendPreimageRows,
    ttFiber32AppendPreimageRowOf, ?_⟩
  intro point
  rw [ttFiber32AppendPreimageRows_get_rowOf]
  exact ttFiber32AppendProjection_section point

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

def tttFiber32SourceStates
    (row : TripleComponentParentRow) : List TauState :=
  tripleStates row.sourceLeft row.sourceMiddle row.sourceRight

def tttFiber32ParentStates
    (row : TripleComponentParentRow) : List TauState :=
  tripleStates row.parentLeft row.parentMiddle row.parentRight

def tttFiber32RootClose : List (List TauState) :=
  closeChainFiber (frontierWordToChainWord tttFrontierWord)
    (concreteChainFiber tttFrontierWord tttFiber32Key)
    (concreteChainFiber tttFrontierWord tttFiber32Key).length
    [chainFiberRootState tttFrontierWord tttFiber32Key]

def tttFiber32SourceStatesList : List (List TauState) :=
  tttFiber32Rows.map tttFiber32SourceStates

theorem tttFiber32SourceStatesList_nodup :
    tttFiber32SourceStatesList.Nodup := by
  decide

theorem tttFiber32Rows_mem_source_mem_concreteChainFiber
    {row : TripleComponentParentRow} (hmem : row ∈ tttFiber32Rows) :
    tttFiber32SourceStates row ∈
      concreteChainFiber tttFrontierWord tttFiber32Key := by
  simp [tttFiber32Rows] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide

theorem tttFiber32SourceStatesList_mem_concreteChainFiber
    {states : List TauState} (hmem : states ∈ tttFiber32SourceStatesList) :
    states ∈ concreteChainFiber tttFrontierWord tttFiber32Key := by
  rcases List.mem_map.mp (by simpa [tttFiber32SourceStatesList] using hmem) with
    ⟨row, hrow, rfl⟩
  exact tttFiber32Rows_mem_source_mem_concreteChainFiber hrow

theorem tttFiber32Row0_source_eq_root :
    tttFiber32SourceStates tttFiber32Row0 =
      chainFiberRootState tttFrontierWord tttFiber32Key := by
  decide

theorem tttFiber32Row0_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row0 ∈ tttFiber32RootClose := by
  rw [tttFiber32Row0_source_eq_root]
  unfold tttFiber32RootClose
  exact closeChainFiber_mem_of_seen _ _ _ _ _ (by simp)

private theorem tttFiber32Row_source_mem_rootClose_of_parent_mem
    {row : TripleComponentParentRow}
    (hmem : row ∈ tttFiber32Rows)
    (hne : row.source ≠ row.parent)
    (hparent : tttFiber32ParentStates row ∈ tttFiber32RootClose)
    (hsource :
      tttFiber32SourceStates row ∈
        concreteChainFiber tttFrontierWord tttFiber32Key) :
    tttFiber32SourceStates row ∈ tttFiber32RootClose := by
  have hstepOr := tttFiber32Rows_mem_source_eq_or_reverse_chainSingleKempeStep hmem
  rcases hstepOr with hsame | hstep
  · exact False.elim (hne hsame)
  · unfold tttFiber32RootClose at hparent ⊢
    unfold tttFiber32ParentStates at hparent
    unfold tttFiber32SourceStates at hsource ⊢
    exact closeChainFiber_mem_step_of_close_at_length_of_bounded_saturation
      closeChainFiberBoundedSaturationClosed_ok
      (frontierWordToChainWord tttFrontierWord)
      (concreteChainFiber tttFrontierWord tttFiber32Key)
      [chainFiberRootState tttFrontierWord tttFiber32Key]
      (tripleStates row.parentLeft row.parentMiddle row.parentRight)
      (tripleStates row.sourceLeft row.sourceMiddle row.sourceRight)
      (by simp)
      hparent hsource
      (by
        simpa [tttWord, tttFrontierWord, frontierWordToChainWord,
          frontierOrientToChain] using hstep)

theorem tttFiber32Row1_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row1 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row1) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row0, tttFiber32Row1, tripleRow] using
        tttFiber32Row0_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row2_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row2 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row2) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row0, tttFiber32Row2, tripleRow] using
        tttFiber32Row0_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row3_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row3 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row3) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row1, tttFiber32Row3, tripleRow] using
        tttFiber32Row1_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row4_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row4 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row4) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row0, tttFiber32Row4, tripleRow] using
        tttFiber32Row0_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row5_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row5 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row5) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row1, tttFiber32Row5, tripleRow] using
        tttFiber32Row1_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row6_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row6 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row6) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row2, tttFiber32Row6, tripleRow] using
        tttFiber32Row2_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row7_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row7 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row7) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row3, tttFiber32Row7, tripleRow] using
        tttFiber32Row3_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row8_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row8 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row8) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row0, tttFiber32Row8, tripleRow] using
        tttFiber32Row0_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row9_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row9 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row9) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row1, tttFiber32Row9, tripleRow] using
        tttFiber32Row1_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row10_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row10 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row10) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row2, tttFiber32Row10, tripleRow] using
        tttFiber32Row2_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row11_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row11 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row11) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row3, tttFiber32Row11, tripleRow] using
        tttFiber32Row3_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row12_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row12 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row12) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row4, tttFiber32Row12, tripleRow] using
        tttFiber32Row4_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row13_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row13 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row13) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row5, tttFiber32Row13, tripleRow] using
        tttFiber32Row5_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row14_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row14 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row14) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row6, tttFiber32Row14, tripleRow] using
        tttFiber32Row6_source_mem_rootClose)
    (by decide)

theorem tttFiber32Row15_source_mem_rootClose :
    tttFiber32SourceStates tttFiber32Row15 ∈ tttFiber32RootClose := by
  exact tttFiber32Row_source_mem_rootClose_of_parent_mem
    (row := tttFiber32Row15) (by simp [tttFiber32Rows]) (by decide)
    (by simpa [tttFiber32ParentStates, tttFiber32SourceStates,
      tttFiber32Row7, tttFiber32Row15, tripleRow] using
        tttFiber32Row7_source_mem_rootClose)
    (by decide)

theorem tttFiber32Rows_mem_source_mem_rootClose
    {row : TripleComponentParentRow} (hmem : row ∈ tttFiber32Rows) :
    tttFiber32SourceStates row ∈ tttFiber32RootClose := by
  simp [tttFiber32Rows] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact tttFiber32Row0_source_mem_rootClose
  · exact tttFiber32Row1_source_mem_rootClose
  · exact tttFiber32Row2_source_mem_rootClose
  · exact tttFiber32Row3_source_mem_rootClose
  · exact tttFiber32Row4_source_mem_rootClose
  · exact tttFiber32Row5_source_mem_rootClose
  · exact tttFiber32Row6_source_mem_rootClose
  · exact tttFiber32Row7_source_mem_rootClose
  · exact tttFiber32Row8_source_mem_rootClose
  · exact tttFiber32Row9_source_mem_rootClose
  · exact tttFiber32Row10_source_mem_rootClose
  · exact tttFiber32Row11_source_mem_rootClose
  · exact tttFiber32Row12_source_mem_rootClose
  · exact tttFiber32Row13_source_mem_rootClose
  · exact tttFiber32Row14_source_mem_rootClose
  · exact tttFiber32Row15_source_mem_rootClose

theorem tttFiber32SourceStatesList_mem_rootClose
    {states : List TauState} (hmem : states ∈ tttFiber32SourceStatesList) :
    states ∈ tttFiber32RootClose := by
  rcases List.mem_map.mp (by simpa [tttFiber32SourceStatesList] using hmem) with
    ⟨row, hrow, rfl⟩
  exact tttFiber32Rows_mem_source_mem_rootClose hrow

theorem bindList_bindList {α β γ : Type} (xs : List α)
    (f : α → List β) (g : β → List γ) :
    bindList (bindList xs f) g = bindList xs (fun x => bindList (f x) g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      change bindList (f x ++ bindList xs f) g =
        bindList (f x) g ++ bindList xs (fun x => bindList (f x) g)
      rw [GoertzelLemma818LengthTwoRealFiberBridgePrototype.bindList_append]
      rw [ih]

def tttStatesFromLeft
    (word : List GoertzelLemma814.TauOrient) (left : TauState) :
    List (List TauState) :=
  bindList (allTauStates.filter fun middle =>
    compatibleAdjacent (tauOrientAt word 0) (tauOrientAt word 1) left middle) fun middle =>
      (allTauStates.filter fun right =>
        compatibleAdjacent (tauOrientAt word 1) (tauOrientAt word 2) middle right).map fun right =>
          [left, middle, right]

theorem tttAllChainStates_eq :
    allChainStates tttWord = bindList allTauStates fun left =>
      tttStatesFromLeft tttWord left := by
  simp [tttWord, allChainStates, buildChainStatesFrom, extendChainStates,
    tttStatesFromLeft, chainStateAt, tauOrientAt, listGetD,
    GoertzelLemma818LengthTwoRealFiberBridgePrototype.bindList_map,
    bindList_bindList]

theorem tripleStates_mem_tttAllChainStates_of_indices
    {left middle right : Nat}
    (hleft : stateAt left ∈ allTauStates)
    (hmiddle : stateAt middle ∈ allTauStates)
    (hleftMiddle :
      compatibleAdjacent (tauOrientAt tttWord 0) (tauOrientAt tttWord 1)
        (stateAt left) (stateAt middle) = true)
    (hright : stateAt right ∈ allTauStates)
    (hmiddleRight :
      compatibleAdjacent (tauOrientAt tttWord 1) (tauOrientAt tttWord 2)
        (stateAt middle) (stateAt right) = true) :
    tripleStates left middle right ∈ allChainStates tttWord := by
  rw [tttAllChainStates_eq]
  rw [GoertzelLemma818LengthTwoRealFiberBridgePrototype.bindList_mem]
  refine ⟨stateAt left, hleft, ?_⟩
  unfold tttStatesFromLeft
  rw [GoertzelLemma818LengthTwoRealFiberBridgePrototype.bindList_mem]
  refine ⟨stateAt middle, ?_, ?_⟩
  · rw [List.mem_filter]
    exact ⟨hmiddle, hleftMiddle⟩
  · rw [List.mem_map]
    refine ⟨stateAt right, ?_, rfl⟩
    rw [List.mem_filter]
    exact ⟨hright, hmiddleRight⟩

theorem tttFiber3Rows_length_eq_two_mul_ttFiber3Rows_length :
    GoertzelLemma818TripleTauLightComponentCertificate.tttFiber3Key =
      GoertzelLemma818CompositeCertificate.ttFiber3Key ∧
    GoertzelLemma818CompositeCertificate.ttFiber3Rows.length = 8 ∧
    GoertzelLemma818TripleTauLightComponentCertificate.tttFiber3Rows.length =
      2 * GoertzelLemma818CompositeCertificate.ttFiber3Rows.length := by
  decide

def ttFiber3RowIndexToTttFiber3RowIndexCore (i : Fin 8) : Fin 16 :=
  ⟨i.1, by omega⟩

theorem ttFiber3RowIndexToTttFiber3RowIndexCore_injective :
    Function.Injective ttFiber3RowIndexToTttFiber3RowIndexCore := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simpa [ttFiber3RowIndexToTttFiber3RowIndexCore] using hval

def ttFiber3RowIndexToTttFiber3RowIndex
    (i : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) :
    Fin GoertzelLemma818TripleTauLightComponentCertificate.tttFiber3Rows.length :=
  Fin.cast (by decide :
      16 =
        GoertzelLemma818TripleTauLightComponentCertificate.tttFiber3Rows.length)
    (ttFiber3RowIndexToTttFiber3RowIndexCore
      (Fin.cast (by decide :
          GoertzelLemma818CompositeCertificate.ttFiber3Rows.length = 8) i))

theorem ttFiber3RowIndexToTttFiber3RowIndex_injective :
    Function.Injective ttFiber3RowIndexToTttFiber3RowIndex := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  have hcore :
      ttFiber3RowIndexToTttFiber3RowIndexCore
          (Fin.cast (by decide :
            GoertzelLemma818CompositeCertificate.ttFiber3Rows.length = 8) i) =
        ttFiber3RowIndexToTttFiber3RowIndexCore
          (Fin.cast (by decide :
            GoertzelLemma818CompositeCertificate.ttFiber3Rows.length = 8) j) := by
    apply Fin.ext
    simpa [ttFiber3RowIndexToTttFiber3RowIndex] using hval
  have hcast :=
    ttFiber3RowIndexToTttFiber3RowIndexCore_injective hcore
  exact congrArg Fin.val hcast

theorem ttFiber3SelectedTttFiber3Row_source_eq :
    ∀ i : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length,
      (GoertzelLemma818TripleTauLightComponentCertificate.tttFiber3Rows.get
        (ttFiber3RowIndexToTttFiber3RowIndex i)).source =
        3808 + i.1 := by
  decide

def ttFiber3FrontierWord : List GoertzelLemma818FrontierMode.TauOrient :=
  [ GoertzelLemma818FrontierMode.TauOrient.tau
  , GoertzelLemma818FrontierMode.TauOrient.tau
  ]

def ttFiber3PrefixStates
    (i : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) :
    List TauState :=
  GoertzelLemma818LengthTwoDirectClosurePrototype.ttFiber3StateAt i.1

def ttFiber3PrefixStatesList : List (List TauState) :=
  [ ttFiber3PrefixStates ⟨0, by decide⟩
  , ttFiber3PrefixStates ⟨1, by decide⟩
  , ttFiber3PrefixStates ⟨2, by decide⟩
  , ttFiber3PrefixStates ⟨3, by decide⟩
  , ttFiber3PrefixStates ⟨4, by decide⟩
  , ttFiber3PrefixStates ⟨5, by decide⟩
  , ttFiber3PrefixStates ⟨6, by decide⟩
  , ttFiber3PrefixStates ⟨7, by decide⟩
  ]

theorem ttFiber3PrefixStatesList_nodup :
    ttFiber3PrefixStatesList.Nodup := by
  decide

theorem ttFiber3PrefixStatesList_eq_concreteChainFiber :
    ttFiber3PrefixStatesList =
      concreteChainFiber ttFiber3FrontierWord
        GoertzelLemma818CompositeCertificate.ttFiber3Key := by
  unfold concreteChainFiber concreteChainStates ttFiber3FrontierWord
  change ttFiber3PrefixStatesList =
    chainFiberFrom GoertzelLemma818CompositeCertificate.ttWord
      (allChainStates GoertzelLemma818CompositeCertificate.ttWord)
      GoertzelLemma818CompositeCertificate.ttFiber3Key
  rw [GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber3RealFiber_eq_direct]
  decide

theorem ttFiber3PrefixStates_mem_concreteChainFiber :
    ∀ i : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length,
      ttFiber3PrefixStates i ∈
        concreteChainFiber ttFiber3FrontierWord
          GoertzelLemma818CompositeCertificate.ttFiber3Key := by
  intro i
  have hmem : ttFiber3PrefixStates i ∈ ttFiber3PrefixStatesList := by
    rcases i with ⟨n, hn⟩
    have hn8 : n < 8 := by
      simpa [GoertzelLemma818CompositeCertificate.ttFiber3Rows] using hn
    by_cases h0 : n = 0
    · subst n
      have hfin :
          (⟨0, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
            ⟨0, by decide⟩ := by
        apply Fin.ext
        rfl
      rw [hfin]
      simp [ttFiber3PrefixStatesList]
    by_cases h1 : n = 1
    · subst n
      have hfin :
          (⟨1, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
            ⟨1, by decide⟩ := by
        apply Fin.ext
        rfl
      rw [hfin]
      simp [ttFiber3PrefixStatesList]
    by_cases h2 : n = 2
    · subst n
      have hfin :
          (⟨2, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
            ⟨2, by decide⟩ := by
        apply Fin.ext
        rfl
      rw [hfin]
      simp [ttFiber3PrefixStatesList]
    by_cases h3 : n = 3
    · subst n
      have hfin :
          (⟨3, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
            ⟨3, by decide⟩ := by
        apply Fin.ext
        rfl
      rw [hfin]
      simp [ttFiber3PrefixStatesList]
    by_cases h4 : n = 4
    · subst n
      have hfin :
          (⟨4, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
            ⟨4, by decide⟩ := by
        apply Fin.ext
        rfl
      rw [hfin]
      simp [ttFiber3PrefixStatesList]
    by_cases h5 : n = 5
    · subst n
      have hfin :
          (⟨5, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
            ⟨5, by decide⟩ := by
        apply Fin.ext
        rfl
      rw [hfin]
      simp [ttFiber3PrefixStatesList]
    by_cases h6 : n = 6
    · subst n
      have hfin :
          (⟨6, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
            ⟨6, by decide⟩ := by
        apply Fin.ext
        rfl
      rw [hfin]
      simp [ttFiber3PrefixStatesList]
    have h7 : n = 7 := by omega
    subst n
    have hfin :
        (⟨7, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
          ⟨7, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    simp [ttFiber3PrefixStatesList]
  rw [ttFiber3PrefixStatesList_eq_concreteChainFiber] at hmem
  exact hmem

def ttFiber3PrefixPoint
    (i : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) :
    ChainFiberPoint ttFiber3FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber3Key :=
  ⟨ttFiber3PrefixStates i, ttFiber3PrefixStates_mem_concreteChainFiber i⟩

theorem ttFiber3PrefixPoint_surjective :
    ∀ point : ChainFiberPoint ttFiber3FrontierWord
        GoertzelLemma818CompositeCertificate.ttFiber3Key,
      ∃ i : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length,
        ttFiber3PrefixPoint i = point := by
  intro point
  have hmem : point.1 ∈ ttFiber3PrefixStatesList := by
    rw [ttFiber3PrefixStatesList_eq_concreteChainFiber]
    exact point.2
  simp only [ttFiber3PrefixStatesList, List.mem_cons, List.not_mem_nil] at hmem
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

noncomputable def ttFiber3PrefixPointIndex
    (point : ChainFiberPoint ttFiber3FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber3Key) :
    Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length :=
  Classical.choose (ttFiber3PrefixPoint_surjective point)

theorem ttFiber3PrefixPointIndex_spec
    (point : ChainFiberPoint ttFiber3FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber3Key) :
    ttFiber3PrefixPoint (ttFiber3PrefixPointIndex point) = point :=
  Classical.choose_spec (ttFiber3PrefixPoint_surjective point)

def ttFiber3SelectedTttFiber3States
    (i : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) :
    List TauState :=
  let row :=
    GoertzelLemma818TripleTauLightComponentCertificate.tttFiber3Rows.get
      (ttFiber3RowIndexToTttFiber3RowIndex i)
  tripleStates row.sourceLeft row.sourceMiddle row.sourceRight

theorem ttFiber3SelectedTttFiber3States_0_mem_concreteChainFiber :
    ttFiber3SelectedTttFiber3States ⟨0, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber3Key := by
  have hall : tripleStates 114 54 112 ∈ allChainStates tttWord :=
    tripleStates_mem_tttAllChainStates_of_indices
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hstates :
      ttFiber3SelectedTttFiber3States ⟨0, by decide⟩ =
        tripleStates 114 54 112 := by
    decide
  rw [hstates]
  unfold concreteChainFiber concreteChainStates chainFiberFrom
  rw [List.mem_filter]
  constructor
  · simpa [tttFrontierWord, frontierWordToChainWord, frontierOrientToChain,
      tttWord] using hall
  · decide

theorem ttFiber3SelectedTttFiber3States_1_mem_concreteChainFiber :
    ttFiber3SelectedTttFiber3States ⟨1, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber3Key := by
  have hall : tripleStates 114 54 113 ∈ allChainStates tttWord :=
    tripleStates_mem_tttAllChainStates_of_indices
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hstates :
      ttFiber3SelectedTttFiber3States ⟨1, by decide⟩ =
        tripleStates 114 54 113 := by
    decide
  rw [hstates]
  unfold concreteChainFiber concreteChainStates chainFiberFrom
  rw [List.mem_filter]
  constructor
  · simpa [tttFrontierWord, frontierWordToChainWord, frontierOrientToChain,
      tttWord] using hall
  · decide

theorem ttFiber3SelectedTttFiber3States_2_mem_concreteChainFiber :
    ttFiber3SelectedTttFiber3States ⟨2, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber3Key := by
  have hall : tripleStates 114 54 114 ∈ allChainStates tttWord :=
    tripleStates_mem_tttAllChainStates_of_indices
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hstates :
      ttFiber3SelectedTttFiber3States ⟨2, by decide⟩ =
        tripleStates 114 54 114 := by
    decide
  rw [hstates]
  unfold concreteChainFiber concreteChainStates chainFiberFrom
  rw [List.mem_filter]
  constructor
  · simpa [tttFrontierWord, frontierWordToChainWord, frontierOrientToChain,
      tttWord] using hall
  · decide

theorem ttFiber3SelectedTttFiber3States_3_mem_concreteChainFiber :
    ttFiber3SelectedTttFiber3States ⟨3, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber3Key := by
  have hall : tripleStates 114 54 115 ∈ allChainStates tttWord :=
    tripleStates_mem_tttAllChainStates_of_indices
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hstates :
      ttFiber3SelectedTttFiber3States ⟨3, by decide⟩ =
        tripleStates 114 54 115 := by
    decide
  rw [hstates]
  unfold concreteChainFiber concreteChainStates chainFiberFrom
  rw [List.mem_filter]
  constructor
  · simpa [tttFrontierWord, frontierWordToChainWord, frontierOrientToChain,
      tttWord] using hall
  · decide

theorem ttFiber3SelectedTttFiber3States_4_mem_concreteChainFiber :
    ttFiber3SelectedTttFiber3States ⟨4, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber3Key := by
  have hall : tripleStates 114 55 120 ∈ allChainStates tttWord :=
    tripleStates_mem_tttAllChainStates_of_indices
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hstates :
      ttFiber3SelectedTttFiber3States ⟨4, by decide⟩ =
        tripleStates 114 55 120 := by
    decide
  rw [hstates]
  unfold concreteChainFiber concreteChainStates chainFiberFrom
  rw [List.mem_filter]
  constructor
  · simpa [tttFrontierWord, frontierWordToChainWord, frontierOrientToChain,
      tttWord] using hall
  · decide

theorem ttFiber3SelectedTttFiber3States_5_mem_concreteChainFiber :
    ttFiber3SelectedTttFiber3States ⟨5, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber3Key := by
  have hall : tripleStates 114 55 121 ∈ allChainStates tttWord :=
    tripleStates_mem_tttAllChainStates_of_indices
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hstates :
      ttFiber3SelectedTttFiber3States ⟨5, by decide⟩ =
        tripleStates 114 55 121 := by
    decide
  rw [hstates]
  unfold concreteChainFiber concreteChainStates chainFiberFrom
  rw [List.mem_filter]
  constructor
  · simpa [tttFrontierWord, frontierWordToChainWord, frontierOrientToChain,
      tttWord] using hall
  · decide

theorem ttFiber3SelectedTttFiber3States_6_mem_concreteChainFiber :
    ttFiber3SelectedTttFiber3States ⟨6, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber3Key := by
  have hall : tripleStates 114 55 122 ∈ allChainStates tttWord :=
    tripleStates_mem_tttAllChainStates_of_indices
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hstates :
      ttFiber3SelectedTttFiber3States ⟨6, by decide⟩ =
        tripleStates 114 55 122 := by
    decide
  rw [hstates]
  unfold concreteChainFiber concreteChainStates chainFiberFrom
  rw [List.mem_filter]
  constructor
  · simpa [tttFrontierWord, frontierWordToChainWord, frontierOrientToChain,
      tttWord] using hall
  · decide

theorem ttFiber3SelectedTttFiber3States_7_mem_concreteChainFiber :
    ttFiber3SelectedTttFiber3States ⟨7, by decide⟩ ∈
      concreteChainFiber tttFrontierWord tttFiber3Key := by
  have hall : tripleStates 114 55 123 ∈ allChainStates tttWord :=
    tripleStates_mem_tttAllChainStates_of_indices
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have hstates :
      ttFiber3SelectedTttFiber3States ⟨7, by decide⟩ =
        tripleStates 114 55 123 := by
    decide
  rw [hstates]
  unfold concreteChainFiber concreteChainStates chainFiberFrom
  rw [List.mem_filter]
  constructor
  · simpa [tttFrontierWord, frontierWordToChainWord, frontierOrientToChain,
      tttWord] using hall
  · decide

theorem ttFiber3SelectedTttFiber3States_mem_concreteChainFiber :
    ∀ i : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length,
      ttFiber3SelectedTttFiber3States i ∈
        concreteChainFiber tttFrontierWord tttFiber3Key := by
  intro i
  rcases i with ⟨n, hn⟩
  have hn8 : n < 8 := by
    simpa [GoertzelLemma818CompositeCertificate.ttFiber3Rows] using hn
  by_cases h0 : n = 0
  · subst n
    have hfin :
        (⟨0, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
          ⟨0, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber3SelectedTttFiber3States_0_mem_concreteChainFiber
  by_cases h1 : n = 1
  · subst n
    have hfin :
        (⟨1, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
          ⟨1, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber3SelectedTttFiber3States_1_mem_concreteChainFiber
  by_cases h2 : n = 2
  · subst n
    have hfin :
        (⟨2, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
          ⟨2, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber3SelectedTttFiber3States_2_mem_concreteChainFiber
  by_cases h3 : n = 3
  · subst n
    have hfin :
        (⟨3, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
          ⟨3, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber3SelectedTttFiber3States_3_mem_concreteChainFiber
  by_cases h4 : n = 4
  · subst n
    have hfin :
        (⟨4, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
          ⟨4, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber3SelectedTttFiber3States_4_mem_concreteChainFiber
  by_cases h5 : n = 5
  · subst n
    have hfin :
        (⟨5, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
          ⟨5, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber3SelectedTttFiber3States_5_mem_concreteChainFiber
  by_cases h6 : n = 6
  · subst n
    have hfin :
        (⟨6, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
          ⟨6, by decide⟩ := by
      apply Fin.ext
      rfl
    rw [hfin]
    exact ttFiber3SelectedTttFiber3States_6_mem_concreteChainFiber
  have h7 : n = 7 := by omega
  subst n
  have hfin :
      (⟨7, hn⟩ : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) =
        ⟨7, by decide⟩ := by
    apply Fin.ext
    rfl
  rw [hfin]
  exact ttFiber3SelectedTttFiber3States_7_mem_concreteChainFiber

def ttFiber3SelectedTttFiber3Point
    (i : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) :
    ChainFiberPoint tttFrontierWord tttFiber3Key :=
  ⟨ttFiber3SelectedTttFiber3States i,
    ttFiber3SelectedTttFiber3States_mem_concreteChainFiber i⟩

def ttFiber3SelectedTttFiber3PointList :
    List (ChainFiberPoint tttFrontierWord tttFiber3Key) :=
  [ ⟨ttFiber3SelectedTttFiber3States ⟨0, by decide⟩,
      ttFiber3SelectedTttFiber3States_0_mem_concreteChainFiber⟩
  , ⟨ttFiber3SelectedTttFiber3States ⟨1, by decide⟩,
      ttFiber3SelectedTttFiber3States_1_mem_concreteChainFiber⟩
  , ⟨ttFiber3SelectedTttFiber3States ⟨2, by decide⟩,
      ttFiber3SelectedTttFiber3States_2_mem_concreteChainFiber⟩
  , ⟨ttFiber3SelectedTttFiber3States ⟨3, by decide⟩,
      ttFiber3SelectedTttFiber3States_3_mem_concreteChainFiber⟩
  , ⟨ttFiber3SelectedTttFiber3States ⟨4, by decide⟩,
      ttFiber3SelectedTttFiber3States_4_mem_concreteChainFiber⟩
  , ⟨ttFiber3SelectedTttFiber3States ⟨5, by decide⟩,
      ttFiber3SelectedTttFiber3States_5_mem_concreteChainFiber⟩
  , ⟨ttFiber3SelectedTttFiber3States ⟨6, by decide⟩,
      ttFiber3SelectedTttFiber3States_6_mem_concreteChainFiber⟩
  , ⟨ttFiber3SelectedTttFiber3States ⟨7, by decide⟩,
      ttFiber3SelectedTttFiber3States_7_mem_concreteChainFiber⟩
  ]

def ttFiber3SelectedTttFiber3PointAt
    (i : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length) :
    ChainFiberPoint tttFrontierWord tttFiber3Key :=
  ttFiber3SelectedTttFiber3PointList.get
    (Fin.cast (by decide :
        GoertzelLemma818CompositeCertificate.ttFiber3Rows.length =
          ttFiber3SelectedTttFiber3PointList.length) i)

theorem ttFiber3SelectedTttFiber3PointAt_value_eq :
    ∀ i : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length,
      (ttFiber3SelectedTttFiber3PointAt i).1 =
        ttFiber3SelectedTttFiber3States i := by
  decide

def ttFiber3SelectedTttFiber3StatesIndex
    (states : List TauState) : Nat :=
  if states = ttFiber3SelectedTttFiber3States ⟨0, by decide⟩ then 0
  else if states = ttFiber3SelectedTttFiber3States ⟨1, by decide⟩ then 1
  else if states = ttFiber3SelectedTttFiber3States ⟨2, by decide⟩ then 2
  else if states = ttFiber3SelectedTttFiber3States ⟨3, by decide⟩ then 3
  else if states = ttFiber3SelectedTttFiber3States ⟨4, by decide⟩ then 4
  else if states = ttFiber3SelectedTttFiber3States ⟨5, by decide⟩ then 5
  else if states = ttFiber3SelectedTttFiber3States ⟨6, by decide⟩ then 6
  else if states = ttFiber3SelectedTttFiber3States ⟨7, by decide⟩ then 7
  else 8

theorem ttFiber3SelectedTttFiber3StatesIndex_selected :
    ∀ i : Fin GoertzelLemma818CompositeCertificate.ttFiber3Rows.length,
      ttFiber3SelectedTttFiber3StatesIndex
        (ttFiber3SelectedTttFiber3States i) = i.1 := by
  decide

theorem ttFiber3SelectedTttFiber3States_injective :
    Function.Injective ttFiber3SelectedTttFiber3States := by
  intro i j h
  have hindex := congrArg ttFiber3SelectedTttFiber3StatesIndex h
  rw [ttFiber3SelectedTttFiber3StatesIndex_selected i,
    ttFiber3SelectedTttFiber3StatesIndex_selected j] at hindex
  exact Fin.ext hindex

theorem ttFiber3SelectedTttFiber3PointAt_injective :
    Function.Injective ttFiber3SelectedTttFiber3PointAt := by
  intro i j h
  have hstates :
      ttFiber3SelectedTttFiber3States i =
        ttFiber3SelectedTttFiber3States j := by
    have hval := congrArg Subtype.val h
    simpa [ttFiber3SelectedTttFiber3PointAt_value_eq] using hval
  exact ttFiber3SelectedTttFiber3States_injective hstates

noncomputable def ttFiber3SelectedTttFiber3PointOfPrefixPoint
    (point : ChainFiberPoint ttFiber3FrontierWord
      GoertzelLemma818CompositeCertificate.ttFiber3Key) :
    ChainFiberPoint tttFrontierWord tttFiber3Key :=
  ttFiber3SelectedTttFiber3PointAt (ttFiber3PrefixPointIndex point)

theorem ttFiber3SelectedTttFiber3PointOfPrefixPoint_injective :
    Function.Injective ttFiber3SelectedTttFiber3PointOfPrefixPoint := by
  intro a b h
  have hindex :
      ttFiber3PrefixPointIndex a = ttFiber3PrefixPointIndex b :=
    ttFiber3SelectedTttFiber3PointAt_injective h
  calc
    a = ttFiber3PrefixPoint (ttFiber3PrefixPointIndex a) :=
      (ttFiber3PrefixPointIndex_spec a).symm
    _ = ttFiber3PrefixPoint (ttFiber3PrefixPointIndex b) := by
      rw [hindex]
    _ = b :=
      ttFiber3PrefixPointIndex_spec b

theorem ttFiber3ProjectionInjectivePreimage :
    ∃ preimageOf :
      ChainFiberPoint ttFiber3FrontierWord
        GoertzelLemma818CompositeCertificate.ttFiber3Key →
        ChainFiberPoint tttFrontierWord tttFiber3Key,
      Function.Injective preimageOf :=
  ⟨ttFiber3SelectedTttFiber3PointOfPrefixPoint,
    ttFiber3SelectedTttFiber3PointOfPrefixPoint_injective⟩

theorem ttFiber3AppendProjectionInjectivePreimage :
    ∃ preimageOf :
      ChainFiberPoint ttFiber3FrontierWord
        GoertzelLemma818CompositeCertificate.ttFiber3Key →
        ChainFiberPoint
          (ttFiber3FrontierWord ++
            [GoertzelLemma818FrontierMode.TauOrient.tau])
          GoertzelLemma818CompositeCertificate.ttFiber3Key,
      Function.Injective preimageOf := by
  simpa [ttFiber3FrontierWord,
    GoertzelLemma818TripleTauLightComponentCertificate.tttFrontierWord,
    GoertzelLemma818CompositeCertificate.ttFiber3Key,
    GoertzelLemma818TripleTauLightComponentCertificate.tttFiber3Key] using
    ttFiber3ProjectionInjectivePreimage

def tttFiber3SourceStates
    (row : TripleComponentParentRow) : List TauState :=
  tripleStates row.sourceLeft row.sourceMiddle row.sourceRight

def tttFiber3ParentStates
    (row : TripleComponentParentRow) : List TauState :=
  tripleStates row.parentLeft row.parentMiddle row.parentRight

def tttFiber3SourceStatesList : List (List TauState) :=
  tttFiber3Rows.map tttFiber3SourceStates

theorem tttFiber3SourceStatesList_nodup :
    tttFiber3SourceStatesList.Nodup := by
  decide

private theorem tttFiber3TripleStates_mem_concreteChainFiber
    {left middle right : Nat}
    (hall : tripleStates left middle right ∈ allChainStates tttWord)
    (hkey :
      (chainInputKey tttWord (tripleStates left middle right) ==
        tttFiber3Key) = true) :
    tripleStates left middle right ∈
      concreteChainFiber tttFrontierWord tttFiber3Key := by
  unfold concreteChainFiber concreteChainStates chainFiberFrom
  rw [List.mem_filter]
  constructor
  · simpa [tttFrontierWord, frontierWordToChainWord,
      frontierOrientToChain, tttWord] using hall
  · exact hkey

theorem tttFiber3Rows_mem_source_mem_concreteChainFiber
    {row : TripleComponentParentRow} (hmem : row ∈ tttFiber3Rows) :
    tttFiber3SourceStates row ∈
      concreteChainFiber tttFrontierWord tttFiber3Key := by
  simp [tttFiber3Rows] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [tttFiber3SourceStates, tttFiber3Row0, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row1, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row2, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row3, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row4, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row5, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row6, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row7, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row8, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row9, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row10, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row11, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row12, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row13, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row14, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)
  · simpa [tttFiber3SourceStates, tttFiber3Row15, tripleRow] using
      tttFiber3TripleStates_mem_concreteChainFiber
        (tripleStates_mem_tttAllChainStates_of_indices
          (by decide) (by decide) (by decide) (by decide) (by decide))
        (by decide)

theorem tttFiber3SourceStatesList_mem_concreteChainFiber
    {states : List TauState} (hmem : states ∈ tttFiber3SourceStatesList) :
    states ∈ concreteChainFiber tttFrontierWord tttFiber3Key := by
  rcases List.mem_map.mp (by simpa [tttFiber3SourceStatesList] using hmem) with
    ⟨row, hrow, rfl⟩
  exact tttFiber3Rows_mem_source_mem_concreteChainFiber hrow

theorem tttFiber3Rows_mem_parent_mem_concreteChainFiber
    {row : TripleComponentParentRow} (hmem : row ∈ tttFiber3Rows) :
    tttFiber3ParentStates row ∈
      concreteChainFiber tttFrontierWord tttFiber3Key := by
  simp [tttFiber3Rows] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row0, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row0) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row0, tttFiber3Row1, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row0) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row0, tttFiber3Row2, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row0) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row1, tttFiber3Row3, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row1) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row0, tttFiber3Row4, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row0) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row1, tttFiber3Row5, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row1) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row2, tttFiber3Row6, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row2) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row3, tttFiber3Row7, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row3) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row0, tttFiber3Row8, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row0) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row1, tttFiber3Row9, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row1) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row2, tttFiber3Row10, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row2) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row3, tttFiber3Row11, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row3) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row4, tttFiber3Row12, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row4) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row5, tttFiber3Row13, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row5) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row6, tttFiber3Row14, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row6) (by simp [tttFiber3Rows])
  · simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row7, tttFiber3Row15, tripleRow] using
      tttFiber3Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber3Row7) (by simp [tttFiber3Rows])

def tttFiber3CoverLeftState (left : TauState) : Bool :=
  (tttStatesFromLeft tttWord left).all fun states =>
    !(chainInputKey tttWord states == tttFiber3Key) ||
      tttFiber3SourceStatesList.contains states

def tttFiber3CoverLeftStateList (lefts : List TauState) : Bool :=
  lefts.all tttFiber3CoverLeftState

def tttFiber3CoverAllLefts : Bool :=
  allTauStates.all tttFiber3CoverLeftState

def tttFiber3CoverLeftChunk (start len : Nat) : Bool :=
  tttFiber3CoverLeftStateList ((allTauStates.drop start).take len)

theorem tttFiber3CoverLeftChunk_0_ok :
    tttFiber3CoverLeftChunk 0 32 = true := by
  decide

theorem tttFiber3CoverLeftChunk_32_ok :
    tttFiber3CoverLeftChunk 32 32 = true := by
  decide

theorem tttFiber3CoverLeftChunk_64_ok :
    tttFiber3CoverLeftChunk 64 32 = true := by
  decide

theorem tttFiber3CoverLeftChunk_96_ok :
    tttFiber3CoverLeftChunk 96 32 = true := by
  decide

theorem tttFiber3CoverLeftChunk_128_ok :
    tttFiber3CoverLeftChunk 128 32 = true := by
  decide

theorem tttFiber3CoverLeftChunk_160_ok :
    tttFiber3CoverLeftChunk 160 32 = true := by
  decide

theorem tttFiber3CoverLeftTail_ok :
    tttFiber3CoverLeftStateList
      GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateTail192 =
        true := by
  decide

theorem tttFiber3CoverAllLefts_ok :
    tttFiber3CoverAllLefts = true := by
  have h0 :
      tttFiber3CoverLeftStateList
        (GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32 0) =
          true := by
    simpa [tttFiber3CoverLeftChunk,
      GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32] using
      tttFiber3CoverLeftChunk_0_ok
  have h1 :
      tttFiber3CoverLeftStateList
        (GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32 32) =
          true := by
    simpa [tttFiber3CoverLeftChunk,
      GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32] using
      tttFiber3CoverLeftChunk_32_ok
  have h2 :
      tttFiber3CoverLeftStateList
        (GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32 64) =
          true := by
    simpa [tttFiber3CoverLeftChunk,
      GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32] using
      tttFiber3CoverLeftChunk_64_ok
  have h3 :
      tttFiber3CoverLeftStateList
        (GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32 96) =
          true := by
    simpa [tttFiber3CoverLeftChunk,
      GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32] using
      tttFiber3CoverLeftChunk_96_ok
  have h4 :
      tttFiber3CoverLeftStateList
        (GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32 128) =
          true := by
    simpa [tttFiber3CoverLeftChunk,
      GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32] using
      tttFiber3CoverLeftChunk_128_ok
  have h5 :
      tttFiber3CoverLeftStateList
        (GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32 160) =
          true := by
    simpa [tttFiber3CoverLeftChunk,
      GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32] using
      tttFiber3CoverLeftChunk_160_ok
  have h6 :
      GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateTail192.all
        tttFiber3CoverLeftState = true := by
    simpa [tttFiber3CoverLeftStateList] using tttFiber3CoverLeftTail_ok
  unfold tttFiber3CoverLeftStateList at h0 h1 h2 h3 h4 h5
  unfold tttFiber3CoverAllLefts
  rw [GoertzelLemma818LengthTwoRealFiberBridgePrototype.allTauStates_eq_chunks32]
  simp only [List.all_append]
  simp [h0, h1, h2, h3, h4, h5, h6]

theorem tttFiber3_direct_contains_of_cover_all
    {states : List TauState}
    (hall : tttFiber3CoverAllLefts = true)
    (hmem : states ∈ allChainStates tttWord)
    (hkey : (chainInputKey tttWord states == tttFiber3Key) = true) :
    tttFiber3SourceStatesList.contains states = true := by
  unfold tttFiber3CoverAllLefts at hall
  rw [List.all_eq_true] at hall
  rw [tttAllChainStates_eq] at hmem
  rw [GoertzelLemma818LengthTwoRealFiberBridgePrototype.bindList_mem] at hmem
  rcases hmem with ⟨left, hleft, hstates⟩
  have hcover := hall left hleft
  unfold tttFiber3CoverLeftState at hcover
  rw [List.all_eq_true] at hcover
  have hrow := hcover states hstates
  simpa [hkey] using hrow

theorem tttFiber3RealFiber_subset_sourceStatesList
    {states : List TauState}
    (h : states ∈ chainFiberFrom tttWord (allChainStates tttWord) tttFiber3Key) :
    states ∈ tttFiber3SourceStatesList := by
  unfold chainFiberFrom at h
  rw [List.mem_filter] at h
  rcases h with ⟨hall, hkey⟩
  exact List.contains_iff_mem.mp
    (tttFiber3_direct_contains_of_cover_all
      tttFiber3CoverAllLefts_ok hall hkey)

theorem tttFiber3ConcreteFiber_subset_sourceStatesList
    {states : List TauState}
    (h : states ∈ concreteChainFiber tttFrontierWord tttFiber3Key) :
    states ∈ tttFiber3SourceStatesList := by
  simpa [concreteChainFiber, concreteChainStates, tttFrontierWord,
    frontierWordToChainWord, frontierOrientToChain, tttWord] using
    tttFiber3RealFiber_subset_sourceStatesList h

def tttFiber3CloseFrom (seed : List TauState) : List (List TauState) :=
  closeChainFiber (frontierWordToChainWord tttFrontierWord)
    (concreteChainFiber tttFrontierWord tttFiber3Key)
    (concreteChainFiber tttFrontierWord tttFiber3Key).length
    [seed]

def tttFiber3RowsSingleStepReadyCheck : Bool :=
  tttFiber3Rows.all
    (tripleComponentRowValidWithSingleStepReady
      tttFiber3Key tttFiber3Expected)

theorem tttFiber3RowsSingleStepReadyCheck_ok :
    tttFiber3RowsSingleStepReadyCheck = true := by
  decide

theorem tttFiber3Rows_mem_source_eq_or_chainSingleKempeStep
    {row : TripleComponentParentRow} (hmem : row ∈ tttFiber3Rows) :
    row.source = row.parent ∨
      chainSingleKempeStep tttWord
        (tripleStates row.sourceLeft row.sourceMiddle row.sourceRight)
        (tripleStates row.parentLeft row.parentMiddle row.parentRight) =
          true := by
  have hrowReady :
      tripleComponentRowValidWithSingleStepReady
        tttFiber3Key tttFiber3Expected row = true :=
    (List.all_eq_true.mp tttFiber3RowsSingleStepReadyCheck_ok) row hmem
  rw [tripleComponentRowValidWithSingleStepReady, Bool.and_eq_true]
    at hrowReady
  exact
    tripleComponentRowValid_source_eq_or_chainSingleKempeStep_of_ready
      hrowReady.1 hrowReady.2

theorem tttFiber3Rows_mem_source_eq_or_reverse_chainSingleKempeStep
    {row : TripleComponentParentRow} (hmem : row ∈ tttFiber3Rows) :
    row.source = row.parent ∨
      chainSingleKempeStep tttWord
        (tripleStates row.parentLeft row.parentMiddle row.parentRight)
        (tripleStates row.sourceLeft row.sourceMiddle row.sourceRight) =
          true := by
  have hrowReady :
      tripleComponentRowValidWithSingleStepReady
        tttFiber3Key tttFiber3Expected row = true :=
    (List.all_eq_true.mp tttFiber3RowsSingleStepReadyCheck_ok) row hmem
  rw [tripleComponentRowValidWithSingleStepReady, Bool.and_eq_true]
    at hrowReady
  exact
    tripleComponentRowValid_source_eq_or_reverse_chainSingleKempeStep_of_ready
      hrowReady.1 hrowReady.2

private theorem tttFiber3Source_mem_closeFrom_of_seed_eq
    {seed : List TauState} {row : TripleComponentParentRow}
    (hseed : seed = tttFiber3SourceStates row) :
    tttFiber3SourceStates row ∈ tttFiber3CloseFrom seed := by
  subst seed
  unfold tttFiber3CloseFrom
  exact closeChainFiber_mem_of_seen _ _ _ _ _ (by simp)

private theorem tttFiber3Row_parent_mem_closeFrom_of_source_mem
    {seed : List TauState} {row : TripleComponentParentRow}
    (hmem : row ∈ tttFiber3Rows)
    (hne : row.source ≠ row.parent)
    (hsource : tttFiber3SourceStates row ∈ tttFiber3CloseFrom seed) :
    tttFiber3ParentStates row ∈ tttFiber3CloseFrom seed := by
  have hstepOr := tttFiber3Rows_mem_source_eq_or_chainSingleKempeStep hmem
  rcases hstepOr with hsame | hstep
  · exact False.elim (hne hsame)
  · unfold tttFiber3CloseFrom at hsource ⊢
    unfold tttFiber3SourceStates at hsource
    unfold tttFiber3ParentStates
    exact closeChainFiber_mem_step_of_close_at_length_of_bounded_saturation
      closeChainFiberBoundedSaturationClosed_ok
      (frontierWordToChainWord tttFrontierWord)
      (concreteChainFiber tttFrontierWord tttFiber3Key)
      [seed]
      (tripleStates row.sourceLeft row.sourceMiddle row.sourceRight)
      (tripleStates row.parentLeft row.parentMiddle row.parentRight)
      (by simp)
      hsource
      (by
        simpa [tttFiber3ParentStates] using
          tttFiber3Rows_mem_parent_mem_concreteChainFiber hmem)
      (by
        simpa [tttWord, tttFrontierWord, frontierWordToChainWord,
          frontierOrientToChain] using hstep)

private theorem tttFiber3Row_source_mem_closeFrom_of_parent_mem
    {seed : List TauState}
    {row : TripleComponentParentRow}
    (hmem : row ∈ tttFiber3Rows)
    (hne : row.source ≠ row.parent)
    (hparent : tttFiber3ParentStates row ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates row ∈ tttFiber3CloseFrom seed := by
  have hstepOr := tttFiber3Rows_mem_source_eq_or_reverse_chainSingleKempeStep hmem
  rcases hstepOr with hsame | hstep
  · exact False.elim (hne hsame)
  · unfold tttFiber3CloseFrom at hparent ⊢
    unfold tttFiber3ParentStates at hparent
    unfold tttFiber3SourceStates
    exact closeChainFiber_mem_step_of_close_at_length_of_bounded_saturation
      closeChainFiberBoundedSaturationClosed_ok
      (frontierWordToChainWord tttFrontierWord)
      (concreteChainFiber tttFrontierWord tttFiber3Key)
      [seed]
      (tripleStates row.parentLeft row.parentMiddle row.parentRight)
      (tripleStates row.sourceLeft row.sourceMiddle row.sourceRight)
      (by simp)
      hparent
      (by
        simpa [tttFiber3SourceStates] using
          tttFiber3Rows_mem_source_mem_concreteChainFiber hmem)
      (by
        simpa [tttWord, tttFrontierWord, frontierWordToChainWord,
          frontierOrientToChain] using hstep)

private theorem tttFiber3Row1_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row1 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row0, tttFiber3Row1, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row1) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row2_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row2 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row0, tttFiber3Row2, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row2) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row3_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row3 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row1 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row1, tttFiber3Row3, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row3) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row4_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row4 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row0, tttFiber3Row4, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row4) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row5_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row5 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row1 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row1, tttFiber3Row5, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row5) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row6_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row6 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row2 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row2, tttFiber3Row6, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row6) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row7_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row7 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row3 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row3, tttFiber3Row7, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row7) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row8_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row8 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row0, tttFiber3Row8, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row8) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row9_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row9 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row1 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row1, tttFiber3Row9, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row9) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row10_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row10 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row2 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row2, tttFiber3Row10, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row10) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row11_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row11 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row3 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row3, tttFiber3Row11, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row11) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row12_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row12 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row4 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row4, tttFiber3Row12, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row12) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row13_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row13 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row5 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row5, tttFiber3Row13, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row13) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row14_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row14 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row6 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row6, tttFiber3Row14, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row14) (by simp [tttFiber3Rows]) (by decide) hrow

private theorem tttFiber3Row15_parent_mem_closeFrom
    {seed : List TauState}
    (hrow : tttFiber3SourceStates tttFiber3Row15 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row7 ∈ tttFiber3CloseFrom seed := by
  simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row7, tttFiber3Row15, tripleRow] using
    tttFiber3Row_parent_mem_closeFrom_of_source_mem
      (row := tttFiber3Row15) (by simp [tttFiber3Rows]) (by decide) hrow

theorem tttFiber3Row0_source_mem_closeFrom_of_sourceStatesList_mem
    {seed : List TauState} (hseed : seed ∈ tttFiber3SourceStatesList) :
    tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed := by
  simp [tttFiber3SourceStatesList, tttFiber3Rows] at hseed
  rcases hseed with h0 | h1 | h2 | h3 | h4 | h5 | h6 | h7 |
    h8 | h9 | h10 | h11 | h12 | h13 | h14 | h15
  · exact tttFiber3Source_mem_closeFrom_of_seed_eq h0
  · exact tttFiber3Row1_parent_mem_closeFrom
      (tttFiber3Source_mem_closeFrom_of_seed_eq h1)
  · exact tttFiber3Row2_parent_mem_closeFrom
      (tttFiber3Source_mem_closeFrom_of_seed_eq h2)
  · exact tttFiber3Row1_parent_mem_closeFrom
      (tttFiber3Row3_parent_mem_closeFrom
        (tttFiber3Source_mem_closeFrom_of_seed_eq h3))
  · exact tttFiber3Row4_parent_mem_closeFrom
      (tttFiber3Source_mem_closeFrom_of_seed_eq h4)
  · exact tttFiber3Row1_parent_mem_closeFrom
      (tttFiber3Row5_parent_mem_closeFrom
        (tttFiber3Source_mem_closeFrom_of_seed_eq h5))
  · exact tttFiber3Row2_parent_mem_closeFrom
      (tttFiber3Row6_parent_mem_closeFrom
        (tttFiber3Source_mem_closeFrom_of_seed_eq h6))
  · exact tttFiber3Row1_parent_mem_closeFrom
      (tttFiber3Row3_parent_mem_closeFrom
        (tttFiber3Row7_parent_mem_closeFrom
          (tttFiber3Source_mem_closeFrom_of_seed_eq h7)))
  · exact tttFiber3Row8_parent_mem_closeFrom
      (tttFiber3Source_mem_closeFrom_of_seed_eq h8)
  · exact tttFiber3Row1_parent_mem_closeFrom
      (tttFiber3Row9_parent_mem_closeFrom
        (tttFiber3Source_mem_closeFrom_of_seed_eq h9))
  · exact tttFiber3Row2_parent_mem_closeFrom
      (tttFiber3Row10_parent_mem_closeFrom
        (tttFiber3Source_mem_closeFrom_of_seed_eq h10))
  · exact tttFiber3Row1_parent_mem_closeFrom
      (tttFiber3Row3_parent_mem_closeFrom
        (tttFiber3Row11_parent_mem_closeFrom
          (tttFiber3Source_mem_closeFrom_of_seed_eq h11)))
  · exact tttFiber3Row4_parent_mem_closeFrom
      (tttFiber3Row12_parent_mem_closeFrom
        (tttFiber3Source_mem_closeFrom_of_seed_eq h12))
  · exact tttFiber3Row1_parent_mem_closeFrom
      (tttFiber3Row5_parent_mem_closeFrom
        (tttFiber3Row13_parent_mem_closeFrom
          (tttFiber3Source_mem_closeFrom_of_seed_eq h13)))
  · exact tttFiber3Row2_parent_mem_closeFrom
      (tttFiber3Row6_parent_mem_closeFrom
        (tttFiber3Row14_parent_mem_closeFrom
          (tttFiber3Source_mem_closeFrom_of_seed_eq h14)))
  · exact tttFiber3Row1_parent_mem_closeFrom
      (tttFiber3Row3_parent_mem_closeFrom
        (tttFiber3Row7_parent_mem_closeFrom
          (tttFiber3Row15_parent_mem_closeFrom
            (tttFiber3Source_mem_closeFrom_of_seed_eq h15))))

private theorem tttFiber3Row1_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row1 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row1) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row0, tttFiber3Row1, tripleRow] using
        hrow0)

private theorem tttFiber3Row2_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row2 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row2) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row0, tttFiber3Row2, tripleRow] using
        hrow0)

private theorem tttFiber3Row3_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row3 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row3) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row1, tttFiber3Row3, tripleRow] using
        tttFiber3Row1_source_mem_closeFrom_of_row0_mem hrow0)

private theorem tttFiber3Row4_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row4 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row4) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row0, tttFiber3Row4, tripleRow] using
        hrow0)

private theorem tttFiber3Row5_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row5 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row5) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row1, tttFiber3Row5, tripleRow] using
        tttFiber3Row1_source_mem_closeFrom_of_row0_mem hrow0)

private theorem tttFiber3Row6_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row6 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row6) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row2, tttFiber3Row6, tripleRow] using
        tttFiber3Row2_source_mem_closeFrom_of_row0_mem hrow0)

private theorem tttFiber3Row7_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row7 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row7) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row3, tttFiber3Row7, tripleRow] using
        tttFiber3Row3_source_mem_closeFrom_of_row0_mem hrow0)

private theorem tttFiber3Row8_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row8 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row8) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row0, tttFiber3Row8, tripleRow] using
        hrow0)

private theorem tttFiber3Row9_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row9 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row9) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row1, tttFiber3Row9, tripleRow] using
        tttFiber3Row1_source_mem_closeFrom_of_row0_mem hrow0)

private theorem tttFiber3Row10_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row10 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row10) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row2, tttFiber3Row10, tripleRow] using
        tttFiber3Row2_source_mem_closeFrom_of_row0_mem hrow0)

private theorem tttFiber3Row11_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row11 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row11) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row3, tttFiber3Row11, tripleRow] using
        tttFiber3Row3_source_mem_closeFrom_of_row0_mem hrow0)

private theorem tttFiber3Row12_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row12 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row12) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row4, tttFiber3Row12, tripleRow] using
        tttFiber3Row4_source_mem_closeFrom_of_row0_mem hrow0)

private theorem tttFiber3Row13_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row13 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row13) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row5, tttFiber3Row13, tripleRow] using
        tttFiber3Row5_source_mem_closeFrom_of_row0_mem hrow0)

private theorem tttFiber3Row14_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row14 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row14) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row6, tttFiber3Row14, tripleRow] using
        tttFiber3Row6_source_mem_closeFrom_of_row0_mem hrow0)

private theorem tttFiber3Row15_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed) :
    tttFiber3SourceStates tttFiber3Row15 ∈ tttFiber3CloseFrom seed := by
  exact tttFiber3Row_source_mem_closeFrom_of_parent_mem
    (row := tttFiber3Row15) (by simp [tttFiber3Rows]) (by decide)
    (by simpa [tttFiber3ParentStates, tttFiber3SourceStates,
      tttFiber3Row7, tttFiber3Row15, tripleRow] using
        tttFiber3Row7_source_mem_closeFrom_of_row0_mem hrow0)

theorem tttFiber3Rows_mem_source_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed)
    {row : TripleComponentParentRow} (hmem : row ∈ tttFiber3Rows) :
    tttFiber3SourceStates row ∈ tttFiber3CloseFrom seed := by
  simp [tttFiber3Rows] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact hrow0
  · exact tttFiber3Row1_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row2_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row3_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row4_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row5_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row6_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row7_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row8_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row9_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row10_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row11_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row12_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row13_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row14_source_mem_closeFrom_of_row0_mem hrow0
  · exact tttFiber3Row15_source_mem_closeFrom_of_row0_mem hrow0

theorem tttFiber3SourceStatesList_mem_closeFrom_of_row0_mem
    {seed : List TauState}
    (hrow0 : tttFiber3SourceStates tttFiber3Row0 ∈ tttFiber3CloseFrom seed)
    {states : List TauState} (hmem : states ∈ tttFiber3SourceStatesList) :
    states ∈ tttFiber3CloseFrom seed := by
  rcases List.mem_map.mp (by simpa [tttFiber3SourceStatesList] using hmem) with
    ⟨row, hrow, rfl⟩
  exact tttFiber3Rows_mem_source_mem_closeFrom_of_row0_mem hrow0 hrow

theorem tttFiber3ConcreteChainFiberConnected :
    chainFiberConnected (frontierWordToChainWord tttFrontierWord)
      (concreteChainFiber tttFrontierWord tttFiber3Key) = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  cases hfiber : concreteChainFiber tttFrontierWord tttFiber3Key with
  | nil =>
      simp [hfiber] at hmem
  | cons root rest =>
      have hrootMem :
          root ∈ concreteChainFiber tttFrontierWord tttFiber3Key := by
        simp [hfiber]
      have hrootList := tttFiber3ConcreteFiber_subset_sourceStatesList hrootMem
      have hrow0 :=
        tttFiber3Row0_source_mem_closeFrom_of_sourceStatesList_mem hrootList
      have hstateList := tttFiber3ConcreteFiber_subset_sourceStatesList hmem
      have hstateClose :=
        tttFiber3SourceStatesList_mem_closeFrom_of_row0_mem hrow0 hstateList
      simpa [tttFiber3CloseFrom, hfiber] using hstateClose

theorem tttFiber3RootClosureConnected :
    GoertzelLemma818Fibration.Connected
      (chainFiberRootClosureStep tttFrontierWord tttFiber3Key) :=
  chainFiberRootClosureConnected_of_chainFiberConnected
    tttFiber3ConcreteChainFiberConnected

def tttFiberCoverLeftState
    (word : List GoertzelLemma814.TauOrient) (key : List LColor)
    (direct : List (List TauState)) (left : TauState) : Bool :=
  (tttStatesFromLeft word left).all fun states =>
    !(chainInputKey word states == key) || direct.contains states

def tttFiberCoverLeftStateList
    (word : List GoertzelLemma814.TauOrient) (key : List LColor)
    (direct : List (List TauState)) (lefts : List TauState) : Bool :=
  lefts.all fun left => tttFiberCoverLeftState word key direct left

def tttFiberCoverAllLefts
    (word : List GoertzelLemma814.TauOrient) (key : List LColor)
    (direct : List (List TauState)) : Bool :=
  allTauStates.all fun left => tttFiberCoverLeftState word key direct left

theorem tttFiberCoverAllLefts_of_chunks
    (word : List GoertzelLemma814.TauOrient)
    (key : List LColor) (direct : List (List TauState))
    (h0 : tttFiberCoverLeftStateList word key direct
      (GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32 0) = true)
    (h1 : tttFiberCoverLeftStateList word key direct
      (GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32 32) = true)
    (h2 : tttFiberCoverLeftStateList word key direct
      (GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32 64) = true)
    (h3 : tttFiberCoverLeftStateList word key direct
      (GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32 96) = true)
    (h4 : tttFiberCoverLeftStateList word key direct
      (GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32 128) = true)
    (h5 : tttFiberCoverLeftStateList word key direct
      (GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateChunk32 160) = true)
    (h6 : tttFiberCoverLeftStateList word key direct
      GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateTail192 = true) :
    tttFiberCoverAllLefts word key direct = true := by
  unfold tttFiberCoverLeftStateList at h0 h1 h2 h3 h4 h5 h6
  unfold tttFiberCoverAllLefts
  rw [GoertzelLemma818LengthTwoRealFiberBridgePrototype.allTauStates_eq_chunks32]
  simp only [List.all_append]
  simp [h0, h1, h2, h3, h4, h5, h6]

def tttFiber32CoverLeftChunk (start len : Nat) : Bool :=
  tttFiberCoverLeftStateList tttWord tttFiber32Key tttFiber32SourceStatesList
    ((allTauStates.drop start).take len)

theorem tttFiber32CoverLeftChunk_0_ok :
    tttFiber32CoverLeftChunk 0 32 = true := by
  decide

theorem tttFiber32CoverLeftChunk_32_ok :
    tttFiber32CoverLeftChunk 32 32 = true := by
  decide

theorem tttFiber32CoverLeftChunk_64_ok :
    tttFiber32CoverLeftChunk 64 32 = true := by
  decide

theorem tttFiber32CoverLeftChunk_96_ok :
    tttFiber32CoverLeftChunk 96 32 = true := by
  decide

theorem tttFiber32CoverLeftChunk_128_ok :
    tttFiber32CoverLeftChunk 128 32 = true := by
  decide

theorem tttFiber32CoverLeftChunk_160_ok :
    tttFiber32CoverLeftChunk 160 32 = true := by
  decide

theorem tttFiber32CoverLeftTail_ok :
    tttFiberCoverLeftStateList tttWord tttFiber32Key tttFiber32SourceStatesList
      GoertzelLemma818LengthTwoRealFiberBridgePrototype.tauStateTail192 = true := by
  decide

theorem tttFiber32CoverAllLefts_ok :
    tttFiberCoverAllLefts tttWord tttFiber32Key tttFiber32SourceStatesList = true := by
  exact tttFiberCoverAllLefts_of_chunks tttWord tttFiber32Key tttFiber32SourceStatesList
    tttFiber32CoverLeftChunk_0_ok tttFiber32CoverLeftChunk_32_ok
    tttFiber32CoverLeftChunk_64_ok tttFiber32CoverLeftChunk_96_ok
    tttFiber32CoverLeftChunk_128_ok tttFiber32CoverLeftChunk_160_ok
    tttFiber32CoverLeftTail_ok

theorem ttt_direct_contains_of_cover_all
    {states : List TauState} {key : List LColor} {direct : List (List TauState)}
    (hall : tttFiberCoverAllLefts tttWord key direct = true)
    (hmem : states ∈ allChainStates tttWord)
    (hkey : (chainInputKey tttWord states == key) = true) :
    direct.contains states = true := by
  unfold tttFiberCoverAllLefts at hall
  rw [List.all_eq_true] at hall
  rw [tttAllChainStates_eq] at hmem
  rw [GoertzelLemma818LengthTwoRealFiberBridgePrototype.bindList_mem] at hmem
  rcases hmem with ⟨left, hleft, hstates⟩
  have hcover := hall left hleft
  unfold tttFiberCoverLeftState at hcover
  rw [List.all_eq_true] at hcover
  have hrow := hcover states hstates
  simpa [hkey] using hrow

theorem tttFiber32RealFiber_subset_sourceStatesList
    {states : List TauState}
    (h : states ∈ chainFiberFrom tttWord (allChainStates tttWord) tttFiber32Key) :
    states ∈ tttFiber32SourceStatesList := by
  unfold chainFiberFrom at h
  rw [List.mem_filter] at h
  rcases h with ⟨hall, hkey⟩
  exact List.contains_iff_mem.mp
    (ttt_direct_contains_of_cover_all tttFiber32CoverAllLefts_ok hall hkey)

theorem tttFiber32ConcreteFiber_subset_sourceStatesList
    {states : List TauState}
    (h : states ∈ concreteChainFiber tttFrontierWord tttFiber32Key) :
    states ∈ tttFiber32SourceStatesList := by
  simpa [concreteChainFiber, concreteChainStates, tttFrontierWord,
    frontierWordToChainWord, frontierOrientToChain, tttWord] using
    tttFiber32RealFiber_subset_sourceStatesList h

theorem tttFiber32ConcreteChainFiberConnected :
    chainFiberConnected (frontierWordToChainWord tttFrontierWord)
      (concreteChainFiber tttFrontierWord tttFiber32Key) = true := by
  apply chainFiberConnected_of_forall_mem_close
  intro state hmem
  cases hfiber : concreteChainFiber tttFrontierWord tttFiber32Key with
  | nil =>
      simp [hfiber] at hmem
  | cons root rest =>
      have hlist := tttFiber32ConcreteFiber_subset_sourceStatesList hmem
      have hclose := tttFiber32SourceStatesList_mem_rootClose hlist
      simpa [tttFiber32RootClose, chainFiberRootState, listGetD, hfiber] using hclose

theorem tttFiber32RootClosureConnected :
    GoertzelLemma818Fibration.Connected
      (chainFiberRootClosureStep tttFrontierWord tttFiber32Key) :=
  chainFiberRootClosureConnected_of_chainFiberConnected
    tttFiber32ConcreteChainFiberConnected

theorem tttFiber32RootClosureParentRowsSymmetricRootedConnectedCertificate :
    ∃ totalDecidableEq : DecidableEq (ChainFiberPoint tttFrontierWord tttFiber32Key),
      Nonempty
        (@GoertzelLemma818Fibration.ParentRowsSymmetricRootedConnectedCertificate
          (ChainFiberPoint tttFrontierWord tttFiber32Key)
          totalDecidableEq
          (chainFiberRootClosureStep tttFrontierWord tttFiber32Key)) := by
  let rootPoint : ChainFiberPoint tttFrontierWord tttFiber32Key :=
    ⟨tttFiber32SourceStates tttFiber32Row0,
      tttFiber32Rows_mem_source_mem_concreteChainFiber
        (row := tttFiber32Row0) (by simp [tttFiber32Rows])⟩
  exact
    chainFiberRootClosureParentRowsSymmetricRootedConnectedCertificate_of_connected_nonempty
      tttFiber32RootClosureConnected ⟨rootPoint⟩

theorem ttFiber32AppendedParentRowsProjectionFiniteSection :
    (∃ totalDecidableEq :
      DecidableEq
        (ChainFiberPoint
          (ttFiber32FrontierWord ++
            [GoertzelLemma818FrontierMode.TauOrient.tau])
          GoertzelLemma818CompositeCertificate.ttFiber32Key),
      Nonempty
        (@GoertzelLemma818Fibration.ParentRowsSymmetricRootedConnectedCertificate
          (ChainFiberPoint
            (ttFiber32FrontierWord ++
              [GoertzelLemma818FrontierMode.TauOrient.tau])
            GoertzelLemma818CompositeCertificate.ttFiber32Key)
          totalDecidableEq
          (chainFiberRootClosureStep
            (ttFiber32FrontierWord ++
              [GoertzelLemma818FrontierMode.TauOrient.tau])
            GoertzelLemma818CompositeCertificate.ttFiber32Key))) ∧
    ∃ proj :
      ChainFiberPoint
        (ttFiber32FrontierWord ++
          [GoertzelLemma818FrontierMode.TauOrient.tau])
        GoertzelLemma818CompositeCertificate.ttFiber32Key →
        ChainFiberPoint ttFiber32FrontierWord
          GoertzelLemma818CompositeCertificate.ttFiber32Key,
      ∃ preimageRows :
        List
          (ChainFiberPoint
            (ttFiber32FrontierWord ++
              [GoertzelLemma818FrontierMode.TauOrient.tau])
            GoertzelLemma818CompositeCertificate.ttFiber32Key),
        ∃ rowOf :
          ChainFiberPoint ttFiber32FrontierWord
            GoertzelLemma818CompositeCertificate.ttFiber32Key →
            Fin preimageRows.length,
          ∀ point : ChainFiberPoint ttFiber32FrontierWord
              GoertzelLemma818CompositeCertificate.ttFiber32Key,
            proj (preimageRows.get (rowOf point)) = point := by
  constructor
  · simpa [ttFiber32FrontierWord,
      GoertzelLemma818TripleTauLightComponentCertificate.tttFrontierWord,
      GoertzelLemma818CompositeCertificate.ttFiber32Key,
      GoertzelLemma818TripleTauLightComponentCertificate.tttFiber32Key] using
      tttFiber32RootClosureParentRowsSymmetricRootedConnectedCertificate
  · exact ttFiber32AppendProjectionFiniteSection

theorem ttFiber32FrontierWord_length_gt_one :
    1 < ttFiber32FrontierWord.length := by
  decide

theorem ttFiber32FrontierWord_fibrationCertificate :
    Nonempty (ChainWordConcreteFibrationCertificate ttFiber32FrontierWord) := by
  simpa [ttFiber32FrontierWord,
    GoertzelLemma818FrontierBaseBridge.lengthTwoFrontierWord] using
    concreteChainWordFibrationLengthTwoSeeds_ok
      GoertzelLemma818LengthTwoBase.LengthTwoOrientWord.tt

theorem ttFiber32Key_mem_colorAssignments4 :
    GoertzelLemma818CompositeCertificate.ttFiber32Key ∈
      GoertzelLemma814.colorAssignments4 := by
  decide

theorem ttFiber32AppendedParentRowsProjectionFiniteSection_of_eq
    {word : List GoertzelLemma818FrontierMode.TauOrient}
    {orient : GoertzelLemma818FrontierMode.TauOrient}
    {key : List LColor}
    (hword : word = ttFiber32FrontierWord)
    (horient : orient = GoertzelLemma818FrontierMode.TauOrient.tau)
    (hkey : key = GoertzelLemma818CompositeCertificate.ttFiber32Key)
    (root : List TauState) (rest : List (List TauState))
    (_hfiber : concreteChainFiber word key = root :: rest) :
    (∃ totalDecidableEq :
      DecidableEq (ChainFiberPoint (word ++ [orient]) key),
      Nonempty
        (@GoertzelLemma818Fibration.ParentRowsSymmetricRootedConnectedCertificate
          (ChainFiberPoint (word ++ [orient]) key)
          totalDecidableEq
          (chainFiberRootClosureStep (word ++ [orient]) key))) ∧
    ∃ proj :
      ChainFiberPoint (word ++ [orient]) key →
        ChainFiberPoint word key,
      ∃ preimageRows :
        List (ChainFiberPoint (word ++ [orient]) key),
        ∃ rowOf :
          ChainFiberPoint word key → Fin preimageRows.length,
          ∀ point : ChainFiberPoint word key,
            proj (preimageRows.get (rowOf point)) = point := by
  subst word
  subst orient
  subst key
  exact
    appendedParentRowsProjectionFiniteSectionBody_of_connected_injective_preimage
      _hfiber
      (by
        simpa [ttFiber32FrontierWord,
          GoertzelLemma818TripleTauLightComponentCertificate.tttFrontierWord,
          GoertzelLemma818CompositeCertificate.ttFiber32Key,
          GoertzelLemma818TripleTauLightComponentCertificate.tttFiber32Key] using
          tttFiber32RootClosureConnected)
      ttFiber32AppendProjectionInjectivePreimage

def ttFiber32AppendedParentRowsProjectionFiniteSectionCase :
    AppendedParentRowsProjectionFiniteSectionCase :=
  { word := ttFiber32FrontierWord
    orient := GoertzelLemma818FrontierMode.TauOrient.tau
    key := GoertzelLemma818CompositeCertificate.ttFiber32Key
    lengthGtOne := ttFiber32FrontierWord_length_gt_one
    prefixCertificate := ttFiber32FrontierWord_fibrationCertificate
    keyMem := ttFiber32Key_mem_colorAssignments4
    rows := fun root rest hfiber =>
      ttFiber32AppendedParentRowsProjectionFiniteSection_of_eq
        rfl rfl rfl root rest hfiber }

theorem tttTargetFrontierWord_eq_ttFiber32FrontierWord_append :
    targetFrontierWord RepresentativeSemanticTarget.ttt =
      ttFiber32FrontierWord ++
        [GoertzelLemma818FrontierMode.TauOrient.tau] := by
  rfl

def ttFiber32AppendedParentRowsProjectionFiniteSectionTargetCase :
    AppendedParentRowsProjectionFiniteSectionTargetCase :=
  { target := RepresentativeSemanticTarget.ttt
    prefixWord := ttFiber32FrontierWord
    orient := GoertzelLemma818FrontierMode.TauOrient.tau
    key := GoertzelLemma818CompositeCertificate.ttFiber32Key
    targetWord_eq := tttTargetFrontierWord_eq_ttFiber32FrontierWord_append
    lengthGtOne := ttFiber32FrontierWord_length_gt_one
    prefixCertificate := ttFiber32FrontierWord_fibrationCertificate
    keyMem := ttFiber32Key_mem_colorAssignments4
    rows := fun root rest hfiber =>
      ttFiber32AppendedParentRowsProjectionFiniteSection_of_eq
        rfl rfl rfl root rest hfiber }

theorem ttFiber32AppendedParentRowsProjectionFiniteSectionTargetCase_toCase :
    ttFiber32AppendedParentRowsProjectionFiniteSectionTargetCase.toCase =
      ttFiber32AppendedParentRowsProjectionFiniteSectionCase := by
  rfl

theorem ttFiber32TargetAppendRowSurface
    (root : List TauState) (rest : List (List TauState))
    (hfiber :
      concreteChainFiber (targetAppendPrefix RepresentativeSemanticTarget.ttt)
        GoertzelLemma818CompositeCertificate.ttFiber32Key = root :: rest) :
    appendedParentRowsProjectionFiniteSectionBody
      (targetAppendPrefix RepresentativeSemanticTarget.ttt)
      (targetAppendOrient RepresentativeSemanticTarget.ttt)
      GoertzelLemma818CompositeCertificate.ttFiber32Key := by
  simpa [targetAppendPrefix, targetAppendOrient, ttFiber32FrontierWord,
    appendedParentRowsProjectionFiniteSectionBody] using
    ttFiber32AppendedParentRowsProjectionFiniteSection_of_eq
      rfl rfl rfl root rest hfiber

def ttFiber32TargetAppendRowSurfaceSelectedKeys :
    RepresentativeSemanticTarget → List (List LColor)
  | RepresentativeSemanticTarget.ttt =>
      [GoertzelLemma818CompositeCertificate.ttFiber32Key]
  | _ => []

theorem ttFiber3Key_mem_colorAssignments4 :
    GoertzelLemma818CompositeCertificate.ttFiber3Key ∈ colorAssignments4 := by
  rw [GoertzelLemma818LengthTwoTTRealAudit.ttColorAssignments_eq_fiberKeys]
  decide

theorem ttFiber3TargetAppendPrefixFiber_nonempty :
    ∃ root rest,
      concreteChainFiber (targetAppendPrefix RepresentativeSemanticTarget.ttt)
        GoertzelLemma818CompositeCertificate.ttFiber3Key = root :: rest := by
  refine
    ⟨GoertzelLemma818LengthTwoDirectClosurePrototype.ttFiber3StateAt 0,
      [ GoertzelLemma818LengthTwoDirectClosurePrototype.ttFiber3StateAt 1
      , GoertzelLemma818LengthTwoDirectClosurePrototype.ttFiber3StateAt 2
      , GoertzelLemma818LengthTwoDirectClosurePrototype.ttFiber3StateAt 3
      , GoertzelLemma818LengthTwoDirectClosurePrototype.ttFiber3StateAt 4
      , GoertzelLemma818LengthTwoDirectClosurePrototype.ttFiber3StateAt 5
      , GoertzelLemma818LengthTwoDirectClosurePrototype.ttFiber3StateAt 6
      , GoertzelLemma818LengthTwoDirectClosurePrototype.ttFiber3StateAt 7
      ], ?_⟩
  unfold concreteChainFiber concreteChainStates targetAppendPrefix
  change
    chainFiberFrom GoertzelLemma818CompositeCertificate.ttWord
      (allChainStates GoertzelLemma818CompositeCertificate.ttWord)
      GoertzelLemma818CompositeCertificate.ttFiber3Key =
        GoertzelLemma818LengthTwoDirectClosurePrototype.ttFiber3DirectStates
  rw [GoertzelLemma818LengthTwoRealFiberBridgePrototype.ttFiber3RealFiber_eq_direct]

theorem ttFiber3Key_not_mem_ttFiber32TargetAppendRowSurfaceSelectedKeys_ttt :
    GoertzelLemma818CompositeCertificate.ttFiber3Key ∉
      ttFiber32TargetAppendRowSurfaceSelectedKeys
        RepresentativeSemanticTarget.ttt := by
  decide

theorem not_ttFiber32TargetAppendRowSurfaceSelectedKeys_cover :
    ¬ RepresentativeTargetAppendSelectedKeysCover
        ttFiber32TargetAppendRowSurfaceSelectedKeys := by
  intro hcover
  rcases ttFiber3TargetAppendPrefixFiber_nonempty with
    ⟨root, rest, hfiber⟩
  exact
    ttFiber3Key_not_mem_ttFiber32TargetAppendRowSurfaceSelectedKeys_ttt
      (hcover RepresentativeSemanticTarget.ttt
        GoertzelLemma818CompositeCertificate.ttFiber3Key
        ttFiber3Key_mem_colorAssignments4 root rest hfiber)

def ttFiber32TargetAppendRowSurfaceCases :
    List AppendedParentRowsProjectionFiniteSectionTargetCase :=
  [ttFiber32AppendedParentRowsProjectionFiniteSectionTargetCase]

def ttFiber32TargetAppendRowSurfaceCasesAudit : Bool :=
  ttFiber32TargetAppendRowSurfaceCases.length == 1
    && ttFiber32TargetAppendRowSurfaceSelectedKeys
        RepresentativeSemanticTarget.ttt ==
      [GoertzelLemma818CompositeCertificate.ttFiber32Key]
    && ttFiber32TargetAppendRowSurfaceCases.map
        (fun rowCase => rowCase.target) ==
      [RepresentativeSemanticTarget.ttt]
    && ttFiber32TargetAppendRowSurfaceCases.map
        (fun rowCase => rowCase.prefixWord) ==
      [targetAppendPrefix RepresentativeSemanticTarget.ttt]
    && ttFiber32TargetAppendRowSurfaceCases.map
        (fun rowCase => rowCase.orient) ==
      [targetAppendOrient RepresentativeSemanticTarget.ttt]
    && ttFiber32TargetAppendRowSurfaceCases.map
        (fun rowCase => rowCase.key) ==
      [GoertzelLemma818CompositeCertificate.ttFiber32Key]

theorem ttFiber32TargetAppendRowSurfaceCasesAudit_ok :
    ttFiber32TargetAppendRowSurfaceCasesAudit = true := by
  decide

theorem ttFiber32TargetAppendRowSurfaceCases_cover_on :
    AppendedParentRowsProjectionFiniteSectionTargetAppendCasesCoverOn
      ttFiber32TargetAppendRowSurfaceCases
      ttFiber32TargetAppendRowSurfaceSelectedKeys := by
  intro target _hcert key hselected _hkey _root _rest _hfiber
  cases target <;> simp [ttFiber32TargetAppendRowSurfaceSelectedKeys] at hselected
  subst key
  refine
    ⟨ttFiber32AppendedParentRowsProjectionFiniteSectionTargetCase, ?_, ?_,
      ?_, ?_, ?_⟩
  · simp [ttFiber32TargetAppendRowSurfaceCases]
  · rfl
  · simp [ttFiber32AppendedParentRowsProjectionFiniteSectionTargetCase,
      targetAppendPrefix, ttFiber32FrontierWord]
  · simp [ttFiber32AppendedParentRowsProjectionFiniteSectionTargetCase,
      targetAppendOrient]
  · rfl

theorem ttFiber32TargetAppendRowSurfaceClosedOn :
    representativeTargetAppendParentRowsProjectionFiniteSectionClosedOn
      ttFiber32TargetAppendRowSurfaceSelectedKeys :=
  representativeTargetAppendParentRowsProjectionFiniteSectionClosedOn_of_target_append_cases
    ttFiber32TargetAppendRowSurfaceCases_cover_on

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
