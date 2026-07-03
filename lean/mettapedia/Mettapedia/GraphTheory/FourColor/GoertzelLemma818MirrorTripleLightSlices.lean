import Mettapedia.GraphTheory.FourColor.GoertzelLemma818MirrorTripleComponentSmoke
import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLightComponentCertificate

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: `MMM` light-fiber slices

This module starts scaling the `MMM`/`mode05` representative certificate beyond
the initial smoke fiber.  It reuses an existing `TTT` light-fiber row set and
rechecks it against the actual mirror-chain word and reversed outer input key.

It is still a partial light-fiber certificate for `MMM`, not a full `MMM`
target audit and not the all-chain `LKR_in` consequence.
-/

namespace GoertzelLemma818MirrorTripleLightSlices

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818MirrorTripleComponentSmoke
open GoertzelLemma818TripleTauLightComponentCertificate

def mmmLightComponentRowValid
    (key : List LColor) (expected : List Nat)
    (row :
      GoertzelLemma818TripleTauLightComponentCertificate.TripleComponentParentRow) :
    Bool :=
  expected.contains row.source && expected.contains row.parent &&
    let s := GoertzelLemma818TripleTauLightComponentCertificate.tripleStates
      row.sourceLeft row.sourceMiddle row.sourceRight
    let t := GoertzelLemma818TripleTauLightComponentCertificate.tripleStates
      row.parentLeft row.parentMiddle row.parentRight
    compatibleChainStates mmmWord s && compatibleChainStates mmmWord t &&
      chainInputKey mmmWord s == key && chainInputKey mmmWord t == key &&
        (row.source == row.parent ||
          chainCertifiedKempeStep mmmWord s t row.cert)

def lightColorOfTrit : Nat → LColor
  | 0 => LColor.r
  | 1 => LColor.b
  | _ => LColor.p

def lightKeyOfFiberId (id : Nat) : List LColor :=
  [ lightColorOfTrit (id / 27)
  , lightColorOfTrit ((id / 9) % 3)
  , lightColorOfTrit ((id / 3) % 3)
  , lightColorOfTrit (id % 3)
  ]

def mmmLightKeyFor (id : Nat) : List LColor :=
  (lightKeyOfFiberId id).reverse

def reverseLightFiberId (id : Nat) : Nat :=
  (id % 3) * 27 + ((id / 3) % 3) * 9 + ((id / 9) % 3) * 3 + id / 27

def mmmLightTargetFiberIds : List Nat :=
  tttLightCertifiedFiberIds.map reverseLightFiberId

def mmmLightTargetFiberCoverageAudit : Bool :=
  mmmLightTargetFiberIds.length == tttLightCertifiedFiberIds.length &&
    mmmLightTargetFiberIds.all (fun id => tttLightCertifiedFiberIds.contains id) &&
    tttLightCertifiedFiberIds.all (fun id => mmmLightTargetFiberIds.contains id)

theorem mmmLightTargetFiberCoverageAudit_ok :
    mmmLightTargetFiberCoverageAudit = true := by
  decide

def mmmLightExpectedFor : Nat → List Nat
  | 0 => tttFiber0Expected
  | 1 => tttFiber1Expected
  | 2 => tttFiber2Expected
  | 3 => tttFiber3Expected
  | 5 => tttFiber5Expected
  | 6 => tttFiber6Expected
  | 7 => tttFiber7Expected
  | 9 => tttFiber9Expected
  | 11 => tttFiber11Expected
  | 12 => tttFiber12Expected
  | 13 => tttFiber13Expected
  | 14 => tttFiber14Expected
  | 15 => tttFiber15Expected
  | 16 => tttFiber16Expected
  | 17 => tttFiber17Expected
  | 18 => tttFiber18Expected
  | 19 => tttFiber19Expected
  | 21 => tttFiber21Expected
  | 22 => tttFiber22Expected
  | 23 => tttFiber23Expected
  | 24 => tttFiber24Expected
  | 25 => tttFiber25Expected
  | 26 => tttFiber26Expected
  | 27 => tttFiber27Expected
  | 28 => tttFiber28Expected
  | 29 => tttFiber29Expected
  | 31 => tttFiber31Expected
  | 32 => tttFiber32Expected
  | 33 => tttFiber33Expected
  | 34 => tttFiber34Expected
  | 35 => tttFiber35Expected
  | 37 => tttFiber37Expected
  | 38 => tttFiber38Expected
  | 39 => tttFiber39Expected
  | 40 => tttFiber40Expected
  | 41 => tttFiber41Expected
  | 42 => tttFiber42Expected
  | 43 => tttFiber43Expected
  | 45 => tttFiber45Expected
  | 46 => tttFiber46Expected
  | 47 => tttFiber47Expected
  | 48 => tttFiber48Expected
  | 49 => tttFiber49Expected
  | 51 => tttFiber51Expected
  | 52 => tttFiber52Expected
  | 53 => tttFiber53Expected
  | 54 => tttFiber54Expected
  | 55 => tttFiber55Expected
  | 56 => tttFiber56Expected
  | 57 => tttFiber57Expected
  | 58 => tttFiber58Expected
  | 59 => tttFiber59Expected
  | 61 => tttFiber61Expected
  | 62 => tttFiber62Expected
  | 63 => tttFiber63Expected
  | 64 => tttFiber64Expected
  | 65 => tttFiber65Expected
  | 66 => tttFiber66Expected
  | 67 => tttFiber67Expected
  | 68 => tttFiber68Expected
  | 69 => tttFiber69Expected
  | 71 => tttFiber71Expected
  | 73 => tttFiber73Expected
  | 74 => tttFiber74Expected
  | 75 => tttFiber75Expected
  | 77 => tttFiber77Expected
  | 78 => tttFiber78Expected
  | 79 => tttFiber79Expected
  | 80 => tttFiber80Expected
  | _ => []

def mmmLightRowsFor :
    Nat → List GoertzelLemma818TripleTauLightComponentCertificate.TripleComponentParentRow
  | 0 => tttFiber0Rows
  | 1 => tttFiber1Rows
  | 2 => tttFiber2Rows
  | 3 => tttFiber3Rows
  | 5 => tttFiber5Rows
  | 6 => tttFiber6Rows
  | 7 => tttFiber7Rows
  | 9 => tttFiber9Rows
  | 11 => tttFiber11Rows
  | 12 => tttFiber12Rows
  | 13 => tttFiber13Rows
  | 14 => tttFiber14Rows
  | 15 => tttFiber15Rows
  | 16 => tttFiber16Rows
  | 17 => tttFiber17Rows
  | 18 => tttFiber18Rows
  | 19 => tttFiber19Rows
  | 21 => tttFiber21Rows
  | 22 => tttFiber22Rows
  | 23 => tttFiber23Rows
  | 24 => tttFiber24Rows
  | 25 => tttFiber25Rows
  | 26 => tttFiber26Rows
  | 27 => tttFiber27Rows
  | 28 => tttFiber28Rows
  | 29 => tttFiber29Rows
  | 31 => tttFiber31Rows
  | 32 => tttFiber32Rows
  | 33 => tttFiber33Rows
  | 34 => tttFiber34Rows
  | 35 => tttFiber35Rows
  | 37 => tttFiber37Rows
  | 38 => tttFiber38Rows
  | 39 => tttFiber39Rows
  | 40 => tttFiber40Rows
  | 41 => tttFiber41Rows
  | 42 => tttFiber42Rows
  | 43 => tttFiber43Rows
  | 45 => tttFiber45Rows
  | 46 => tttFiber46Rows
  | 47 => tttFiber47Rows
  | 48 => tttFiber48Rows
  | 49 => tttFiber49Rows
  | 51 => tttFiber51Rows
  | 52 => tttFiber52Rows
  | 53 => tttFiber53Rows
  | 54 => tttFiber54Rows
  | 55 => tttFiber55Rows
  | 56 => tttFiber56Rows
  | 57 => tttFiber57Rows
  | 58 => tttFiber58Rows
  | 59 => tttFiber59Rows
  | 61 => tttFiber61Rows
  | 62 => tttFiber62Rows
  | 63 => tttFiber63Rows
  | 64 => tttFiber64Rows
  | 65 => tttFiber65Rows
  | 66 => tttFiber66Rows
  | 67 => tttFiber67Rows
  | 68 => tttFiber68Rows
  | 69 => tttFiber69Rows
  | 71 => tttFiber71Rows
  | 73 => tttFiber73Rows
  | 74 => tttFiber74Rows
  | 75 => tttFiber75Rows
  | 77 => tttFiber77Rows
  | 78 => tttFiber78Rows
  | 79 => tttFiber79Rows
  | 80 => tttFiber80Rows
  | _ => []

def mmmLightFiberAudit (id : Nat) : Bool :=
  let expected := mmmLightExpectedFor id
  let rows := mmmLightRowsFor id
  let root := listGetD expected 0 0
  (rows.map fun row => row.source) == expected &&
    (List.range rows.length).all (fun i =>
      mmmLightComponentRowValid (mmmLightKeyFor id) expected
        (listGetD rows i default)) &&
    (List.range expected.length).all fun i =>
      tripleParentIter rows tttLightMaxParentDepth
        (listGetD expected i 0) == root

def mmmLightChunk0Ids : List Nat :=
  [0, 1, 2, 3, 5, 6, 7, 9, 11]

def mmmLightChunk1Ids : List Nat :=
  [12, 13, 14, 15, 16, 17, 18, 19, 21]

def mmmLightChunk2Ids : List Nat :=
  [22, 23, 24, 25, 26, 27, 28, 29, 31]

def mmmLightChunk3Ids : List Nat :=
  [32, 33, 34, 35, 37, 38, 39, 40, 41]

def mmmLightChunk4Ids : List Nat :=
  [42, 43, 45, 46, 47, 48, 49, 51, 52]

def mmmLightChunk5Ids : List Nat :=
  [53, 54, 55, 56, 57, 58, 59, 61, 62]

def mmmLightChunk6Ids : List Nat :=
  [63, 64, 65, 66, 67, 68, 69, 71, 73]

def mmmLightChunk7Ids : List Nat :=
  [74, 75, 77, 78, 79, 80]

def mmmLightChunkIds : List Nat :=
  mmmLightChunk0Ids ++
    mmmLightChunk1Ids ++
    mmmLightChunk2Ids ++
    mmmLightChunk3Ids ++
    mmmLightChunk4Ids ++
    mmmLightChunk5Ids ++
    mmmLightChunk6Ids ++
    mmmLightChunk7Ids

def mmmLightChunkCoverageAudit : Bool :=
  mmmLightChunkIds == tttLightCertifiedFiberIds

theorem mmmLightChunkCoverageAudit_ok :
    mmmLightChunkCoverageAudit = true := by
  decide

def mmmLightChunkAudit (ids : List Nat) : Bool :=
  ids.all mmmLightFiberAudit

theorem mmmLightFiber0Audit_ok :
    mmmLightFiberAudit 0 = true := by
  decide

theorem mmmLightFiber1Audit_ok :
    mmmLightFiberAudit 1 = true := by
  decide

theorem mmmLightFiber2Audit_ok :
    mmmLightFiberAudit 2 = true := by
  decide

theorem mmmLightFiber3Audit_ok :
    mmmLightFiberAudit 3 = true := by
  decide

theorem mmmLightFiber5Audit_ok :
    mmmLightFiberAudit 5 = true := by
  decide

theorem mmmLightFiber6Audit_ok :
    mmmLightFiberAudit 6 = true := by
  decide

theorem mmmLightFiber7Audit_ok :
    mmmLightFiberAudit 7 = true := by
  decide

theorem mmmLightFiber9Audit_ok :
    mmmLightFiberAudit 9 = true := by
  decide

theorem mmmLightFiber11Audit_ok :
    mmmLightFiberAudit 11 = true := by
  decide

theorem mmmLightFiber12Audit_ok :
    mmmLightFiberAudit 12 = true := by
  decide

theorem mmmLightFiber13Audit_ok :
    mmmLightFiberAudit 13 = true := by
  decide

theorem mmmLightFiber14Audit_ok :
    mmmLightFiberAudit 14 = true := by
  decide

theorem mmmLightFiber15Audit_ok :
    mmmLightFiberAudit 15 = true := by
  decide

theorem mmmLightFiber16Audit_ok :
    mmmLightFiberAudit 16 = true := by
  decide

theorem mmmLightFiber17Audit_ok :
    mmmLightFiberAudit 17 = true := by
  decide

theorem mmmLightFiber18Audit_ok :
    mmmLightFiberAudit 18 = true := by
  decide

theorem mmmLightFiber19Audit_ok :
    mmmLightFiberAudit 19 = true := by
  decide

theorem mmmLightFiber21Audit_ok :
    mmmLightFiberAudit 21 = true := by
  decide

theorem mmmLightFiber22Audit_ok :
    mmmLightFiberAudit 22 = true := by
  decide

theorem mmmLightFiber23Audit_ok :
    mmmLightFiberAudit 23 = true := by
  decide

theorem mmmLightFiber24Audit_ok :
    mmmLightFiberAudit 24 = true := by
  decide

theorem mmmLightFiber25Audit_ok :
    mmmLightFiberAudit 25 = true := by
  decide

theorem mmmLightFiber26Audit_ok :
    mmmLightFiberAudit 26 = true := by
  decide

theorem mmmLightFiber27Audit_ok :
    mmmLightFiberAudit 27 = true := by
  decide

theorem mmmLightFiber28Audit_ok :
    mmmLightFiberAudit 28 = true := by
  decide

theorem mmmLightFiber29Audit_ok :
    mmmLightFiberAudit 29 = true := by
  decide

theorem mmmLightFiber31Audit_ok :
    mmmLightFiberAudit 31 = true := by
  decide

theorem mmmLightFiber32Audit_ok :
    mmmLightFiberAudit 32 = true := by
  decide

theorem mmmLightFiber33Audit_ok :
    mmmLightFiberAudit 33 = true := by
  decide

theorem mmmLightFiber34Audit_ok :
    mmmLightFiberAudit 34 = true := by
  decide

theorem mmmLightFiber35Audit_ok :
    mmmLightFiberAudit 35 = true := by
  decide

theorem mmmLightFiber37Audit_ok :
    mmmLightFiberAudit 37 = true := by
  decide

theorem mmmLightFiber38Audit_ok :
    mmmLightFiberAudit 38 = true := by
  decide

theorem mmmLightFiber39Audit_ok :
    mmmLightFiberAudit 39 = true := by
  decide

theorem mmmLightFiber40Audit_ok :
    mmmLightFiberAudit 40 = true := by
  decide

theorem mmmLightFiber41Audit_ok :
    mmmLightFiberAudit 41 = true := by
  decide

theorem mmmLightFiber42Audit_ok :
    mmmLightFiberAudit 42 = true := by
  decide

theorem mmmLightFiber43Audit_ok :
    mmmLightFiberAudit 43 = true := by
  decide

theorem mmmLightFiber45Audit_ok :
    mmmLightFiberAudit 45 = true := by
  decide

theorem mmmLightFiber46Audit_ok :
    mmmLightFiberAudit 46 = true := by
  decide

theorem mmmLightFiber47Audit_ok :
    mmmLightFiberAudit 47 = true := by
  decide

theorem mmmLightFiber48Audit_ok :
    mmmLightFiberAudit 48 = true := by
  decide

theorem mmmLightFiber49Audit_ok :
    mmmLightFiberAudit 49 = true := by
  decide

theorem mmmLightFiber51Audit_ok :
    mmmLightFiberAudit 51 = true := by
  decide

theorem mmmLightFiber52Audit_ok :
    mmmLightFiberAudit 52 = true := by
  decide

theorem mmmLightFiber53Audit_ok :
    mmmLightFiberAudit 53 = true := by
  decide

theorem mmmLightFiber54Audit_ok :
    mmmLightFiberAudit 54 = true := by
  decide

theorem mmmLightFiber55Audit_ok :
    mmmLightFiberAudit 55 = true := by
  decide

theorem mmmLightFiber56Audit_ok :
    mmmLightFiberAudit 56 = true := by
  decide

theorem mmmLightFiber57Audit_ok :
    mmmLightFiberAudit 57 = true := by
  decide

theorem mmmLightFiber58Audit_ok :
    mmmLightFiberAudit 58 = true := by
  decide

theorem mmmLightFiber59Audit_ok :
    mmmLightFiberAudit 59 = true := by
  decide

theorem mmmLightFiber61Audit_ok :
    mmmLightFiberAudit 61 = true := by
  decide

theorem mmmLightFiber62Audit_ok :
    mmmLightFiberAudit 62 = true := by
  decide

theorem mmmLightFiber63Audit_ok :
    mmmLightFiberAudit 63 = true := by
  decide

theorem mmmLightFiber64Audit_ok :
    mmmLightFiberAudit 64 = true := by
  decide

theorem mmmLightFiber65Audit_ok :
    mmmLightFiberAudit 65 = true := by
  decide

theorem mmmLightFiber66Audit_ok :
    mmmLightFiberAudit 66 = true := by
  decide

theorem mmmLightFiber67Audit_ok :
    mmmLightFiberAudit 67 = true := by
  decide

theorem mmmLightFiber68Audit_ok :
    mmmLightFiberAudit 68 = true := by
  decide

theorem mmmLightFiber69Audit_ok :
    mmmLightFiberAudit 69 = true := by
  decide

theorem mmmLightFiber71Audit_ok :
    mmmLightFiberAudit 71 = true := by
  decide

theorem mmmLightFiber73Audit_ok :
    mmmLightFiberAudit 73 = true := by
  decide

theorem mmmLightFiber74Audit_ok :
    mmmLightFiberAudit 74 = true := by
  decide

theorem mmmLightFiber75Audit_ok :
    mmmLightFiberAudit 75 = true := by
  decide

theorem mmmLightFiber77Audit_ok :
    mmmLightFiberAudit 77 = true := by
  decide

theorem mmmLightFiber78Audit_ok :
    mmmLightFiberAudit 78 = true := by
  decide

theorem mmmLightFiber79Audit_ok :
    mmmLightFiberAudit 79 = true := by
  decide

theorem mmmLightFiber80Audit_ok :
    mmmLightFiberAudit 80 = true := by
  decide

theorem mmmLightChunk0Audit_ok :
    mmmLightChunkAudit mmmLightChunk0Ids = true := by
  simp [mmmLightChunkAudit, mmmLightChunk0Ids,
    mmmLightFiber0Audit_ok,
    mmmLightFiber1Audit_ok,
    mmmLightFiber2Audit_ok,
    mmmLightFiber3Audit_ok,
    mmmLightFiber5Audit_ok,
    mmmLightFiber6Audit_ok,
    mmmLightFiber7Audit_ok,
    mmmLightFiber9Audit_ok,
    mmmLightFiber11Audit_ok]

theorem mmmLightChunk1Audit_ok :
    mmmLightChunkAudit mmmLightChunk1Ids = true := by
  simp [mmmLightChunkAudit, mmmLightChunk1Ids,
    mmmLightFiber12Audit_ok,
    mmmLightFiber13Audit_ok,
    mmmLightFiber14Audit_ok,
    mmmLightFiber15Audit_ok,
    mmmLightFiber16Audit_ok,
    mmmLightFiber17Audit_ok,
    mmmLightFiber18Audit_ok,
    mmmLightFiber19Audit_ok,
    mmmLightFiber21Audit_ok]

theorem mmmLightChunk2Audit_ok :
    mmmLightChunkAudit mmmLightChunk2Ids = true := by
  simp [mmmLightChunkAudit, mmmLightChunk2Ids,
    mmmLightFiber22Audit_ok,
    mmmLightFiber23Audit_ok,
    mmmLightFiber24Audit_ok,
    mmmLightFiber25Audit_ok,
    mmmLightFiber26Audit_ok,
    mmmLightFiber27Audit_ok,
    mmmLightFiber28Audit_ok,
    mmmLightFiber29Audit_ok,
    mmmLightFiber31Audit_ok]

theorem mmmLightChunk3Audit_ok :
    mmmLightChunkAudit mmmLightChunk3Ids = true := by
  simp [mmmLightChunkAudit, mmmLightChunk3Ids,
    mmmLightFiber32Audit_ok,
    mmmLightFiber33Audit_ok,
    mmmLightFiber34Audit_ok,
    mmmLightFiber35Audit_ok,
    mmmLightFiber37Audit_ok,
    mmmLightFiber38Audit_ok,
    mmmLightFiber39Audit_ok,
    mmmLightFiber40Audit_ok,
    mmmLightFiber41Audit_ok]

theorem mmmLightChunk4Audit_ok :
    mmmLightChunkAudit mmmLightChunk4Ids = true := by
  simp [mmmLightChunkAudit, mmmLightChunk4Ids,
    mmmLightFiber42Audit_ok,
    mmmLightFiber43Audit_ok,
    mmmLightFiber45Audit_ok,
    mmmLightFiber46Audit_ok,
    mmmLightFiber47Audit_ok,
    mmmLightFiber48Audit_ok,
    mmmLightFiber49Audit_ok,
    mmmLightFiber51Audit_ok,
    mmmLightFiber52Audit_ok]

theorem mmmLightChunk5Audit_ok :
    mmmLightChunkAudit mmmLightChunk5Ids = true := by
  simp [mmmLightChunkAudit, mmmLightChunk5Ids,
    mmmLightFiber53Audit_ok,
    mmmLightFiber54Audit_ok,
    mmmLightFiber55Audit_ok,
    mmmLightFiber56Audit_ok,
    mmmLightFiber57Audit_ok,
    mmmLightFiber58Audit_ok,
    mmmLightFiber59Audit_ok,
    mmmLightFiber61Audit_ok,
    mmmLightFiber62Audit_ok]

theorem mmmLightChunk6Audit_ok :
    mmmLightChunkAudit mmmLightChunk6Ids = true := by
  simp [mmmLightChunkAudit, mmmLightChunk6Ids,
    mmmLightFiber63Audit_ok,
    mmmLightFiber64Audit_ok,
    mmmLightFiber65Audit_ok,
    mmmLightFiber66Audit_ok,
    mmmLightFiber67Audit_ok,
    mmmLightFiber68Audit_ok,
    mmmLightFiber69Audit_ok,
    mmmLightFiber71Audit_ok,
    mmmLightFiber73Audit_ok]

theorem mmmLightChunk7Audit_ok :
    mmmLightChunkAudit mmmLightChunk7Ids = true := by
  simp [mmmLightChunkAudit, mmmLightChunk7Ids,
    mmmLightFiber74Audit_ok,
    mmmLightFiber75Audit_ok,
    mmmLightFiber77Audit_ok,
    mmmLightFiber78Audit_ok,
    mmmLightFiber79Audit_ok,
    mmmLightFiber80Audit_ok]

def mmmLightComponentCertificateAudit : Bool :=
  mmmRepresentativeModeSliceAudit &&
    tttLightComponentCountsAudit &&
    mmmLightChunkCoverageAudit &&
    mmmLightTargetFiberCoverageAudit &&
    mmmLightChunkAudit mmmLightChunk0Ids &&
    mmmLightChunkAudit mmmLightChunk1Ids &&
    mmmLightChunkAudit mmmLightChunk2Ids &&
    mmmLightChunkAudit mmmLightChunk3Ids &&
    mmmLightChunkAudit mmmLightChunk4Ids &&
    mmmLightChunkAudit mmmLightChunk5Ids &&
    mmmLightChunkAudit mmmLightChunk6Ids &&
    mmmLightChunkAudit mmmLightChunk7Ids

theorem mmmLightComponentCertificateAudit_ok :
    mmmLightComponentCertificateAudit = true := by
  simp [mmmLightComponentCertificateAudit,
    mmmRepresentativeModeSliceAudit_ok,
    tttLightComponentCountsAudit_ok,
    mmmLightChunkCoverageAudit_ok,
    mmmLightTargetFiberCoverageAudit_ok,
    mmmLightChunk0Audit_ok,
    mmmLightChunk1Audit_ok,
    mmmLightChunk2Audit_ok,
    mmmLightChunk3Audit_ok,
    mmmLightChunk4Audit_ok,
    mmmLightChunk5Audit_ok,
    mmmLightChunk6Audit_ok,
    mmmLightChunk7Audit_ok]

def mmmFiber63Key : List LColor :=
  [LColor.p, LColor.b, LColor.r, LColor.r]

def mmmFiber63Expected : List Nat :=
  GoertzelLemma818TripleTauLightComponentCertificate.tttFiber5Expected

def mmmFiber63Rows :
    List GoertzelLemma818TripleTauLightComponentCertificate.TripleComponentParentRow :=
  GoertzelLemma818TripleTauLightComponentCertificate.tttFiber5Rows

def mmmFiber63SourcesCheck : Bool :=
  (mmmFiber63Rows.map fun row => row.source) == mmmFiber63Expected

theorem mmmFiber63SourcesCheck_ok :
    mmmFiber63SourcesCheck = true := by
  decide

def mmmFiber63RowCheck (i : Nat) : Bool :=
  mmmLightComponentRowValid mmmFiber63Key mmmFiber63Expected
    (listGetD mmmFiber63Rows i default)

theorem mmmFiber63Row_0_ok : mmmFiber63RowCheck 0 = true := by decide
theorem mmmFiber63Row_1_ok : mmmFiber63RowCheck 1 = true := by decide
theorem mmmFiber63Row_2_ok : mmmFiber63RowCheck 2 = true := by decide
theorem mmmFiber63Row_3_ok : mmmFiber63RowCheck 3 = true := by decide
theorem mmmFiber63Row_4_ok : mmmFiber63RowCheck 4 = true := by decide
theorem mmmFiber63Row_5_ok : mmmFiber63RowCheck 5 = true := by decide
theorem mmmFiber63Row_6_ok : mmmFiber63RowCheck 6 = true := by decide
theorem mmmFiber63Row_7_ok : mmmFiber63RowCheck 7 = true := by decide
theorem mmmFiber63Row_8_ok : mmmFiber63RowCheck 8 = true := by decide
theorem mmmFiber63Row_9_ok : mmmFiber63RowCheck 9 = true := by decide
theorem mmmFiber63Row_10_ok : mmmFiber63RowCheck 10 = true := by decide
theorem mmmFiber63Row_11_ok : mmmFiber63RowCheck 11 = true := by decide
theorem mmmFiber63Row_12_ok : mmmFiber63RowCheck 12 = true := by decide
theorem mmmFiber63Row_13_ok : mmmFiber63RowCheck 13 = true := by decide
theorem mmmFiber63Row_14_ok : mmmFiber63RowCheck 14 = true := by decide
theorem mmmFiber63Row_15_ok : mmmFiber63RowCheck 15 = true := by decide

def mmmFiber63ParentCheck (i : Nat) : Bool :=
  GoertzelLemma818TripleTauLightComponentCertificate.tripleParentIter
    mmmFiber63Rows
    GoertzelLemma818TripleTauLightComponentCertificate.tttLightMaxParentDepth
    (listGetD mmmFiber63Expected i 0) == 2432

theorem mmmFiber63Parent_0_ok : mmmFiber63ParentCheck 0 = true := by decide
theorem mmmFiber63Parent_1_ok : mmmFiber63ParentCheck 1 = true := by decide
theorem mmmFiber63Parent_2_ok : mmmFiber63ParentCheck 2 = true := by decide
theorem mmmFiber63Parent_3_ok : mmmFiber63ParentCheck 3 = true := by decide
theorem mmmFiber63Parent_4_ok : mmmFiber63ParentCheck 4 = true := by decide
theorem mmmFiber63Parent_5_ok : mmmFiber63ParentCheck 5 = true := by decide
theorem mmmFiber63Parent_6_ok : mmmFiber63ParentCheck 6 = true := by decide
theorem mmmFiber63Parent_7_ok : mmmFiber63ParentCheck 7 = true := by decide
theorem mmmFiber63Parent_8_ok : mmmFiber63ParentCheck 8 = true := by decide
theorem mmmFiber63Parent_9_ok : mmmFiber63ParentCheck 9 = true := by decide
theorem mmmFiber63Parent_10_ok : mmmFiber63ParentCheck 10 = true := by decide
theorem mmmFiber63Parent_11_ok : mmmFiber63ParentCheck 11 = true := by decide
theorem mmmFiber63Parent_12_ok : mmmFiber63ParentCheck 12 = true := by decide
theorem mmmFiber63Parent_13_ok : mmmFiber63ParentCheck 13 = true := by decide
theorem mmmFiber63Parent_14_ok : mmmFiber63ParentCheck 14 = true := by decide
theorem mmmFiber63Parent_15_ok : mmmFiber63ParentCheck 15 = true := by decide

def mmmFiber63ComponentCertificateAudit : Bool :=
  mmmRepresentativeModeSliceAudit &&
    mmmFiber63SourcesCheck &&
    mmmFiber63RowCheck 0 &&
    mmmFiber63RowCheck 1 &&
    mmmFiber63RowCheck 2 &&
    mmmFiber63RowCheck 3 &&
    mmmFiber63RowCheck 4 &&
    mmmFiber63RowCheck 5 &&
    mmmFiber63RowCheck 6 &&
    mmmFiber63RowCheck 7 &&
    mmmFiber63RowCheck 8 &&
    mmmFiber63RowCheck 9 &&
    mmmFiber63RowCheck 10 &&
    mmmFiber63RowCheck 11 &&
    mmmFiber63RowCheck 12 &&
    mmmFiber63RowCheck 13 &&
    mmmFiber63RowCheck 14 &&
    mmmFiber63RowCheck 15 &&
    mmmFiber63ParentCheck 0 &&
    mmmFiber63ParentCheck 1 &&
    mmmFiber63ParentCheck 2 &&
    mmmFiber63ParentCheck 3 &&
    mmmFiber63ParentCheck 4 &&
    mmmFiber63ParentCheck 5 &&
    mmmFiber63ParentCheck 6 &&
    mmmFiber63ParentCheck 7 &&
    mmmFiber63ParentCheck 8 &&
    mmmFiber63ParentCheck 9 &&
    mmmFiber63ParentCheck 10 &&
    mmmFiber63ParentCheck 11 &&
    mmmFiber63ParentCheck 12 &&
    mmmFiber63ParentCheck 13 &&
    mmmFiber63ParentCheck 14 &&
    mmmFiber63ParentCheck 15

theorem mmmFiber63ComponentCertificateAudit_ok :
    mmmFiber63ComponentCertificateAudit = true := by
  simp [mmmFiber63ComponentCertificateAudit,
    mmmRepresentativeModeSliceAudit_ok,
    mmmFiber63SourcesCheck_ok,
    mmmFiber63Row_0_ok,
    mmmFiber63Row_1_ok,
    mmmFiber63Row_2_ok,
    mmmFiber63Row_3_ok,
    mmmFiber63Row_4_ok,
    mmmFiber63Row_5_ok,
    mmmFiber63Row_6_ok,
    mmmFiber63Row_7_ok,
    mmmFiber63Row_8_ok,
    mmmFiber63Row_9_ok,
    mmmFiber63Row_10_ok,
    mmmFiber63Row_11_ok,
    mmmFiber63Row_12_ok,
    mmmFiber63Row_13_ok,
    mmmFiber63Row_14_ok,
    mmmFiber63Row_15_ok,
    mmmFiber63Parent_0_ok,
    mmmFiber63Parent_1_ok,
    mmmFiber63Parent_2_ok,
    mmmFiber63Parent_3_ok,
    mmmFiber63Parent_4_ok,
    mmmFiber63Parent_5_ok,
    mmmFiber63Parent_6_ok,
    mmmFiber63Parent_7_ok,
    mmmFiber63Parent_8_ok,
    mmmFiber63Parent_9_ok,
    mmmFiber63Parent_10_ok,
    mmmFiber63Parent_11_ok,
    mmmFiber63Parent_12_ok,
    mmmFiber63Parent_13_ok,
    mmmFiber63Parent_14_ok,
    mmmFiber63Parent_15_ok]

def mmmCheckedLightSliceCountAfterFiber63 : Nat := 2

def mmmCheckedLightSlicesAfterFiber63Audit : Bool :=
  mmmFiber9ComponentCertificateAudit &&
    mmmFiber63ComponentCertificateAudit &&
    mmmCheckedLightSliceCountAfterFiber63 == 2

theorem mmmCheckedLightSlicesAfterFiber63Audit_ok :
    mmmCheckedLightSlicesAfterFiber63Audit = true := by
  simp [mmmCheckedLightSlicesAfterFiber63Audit,
    mmmCheckedLightSliceCountAfterFiber63,
    mmmFiber9ComponentCertificateAudit_ok,
    mmmFiber63ComponentCertificateAudit_ok]

end GoertzelLemma818MirrorTripleLightSlices

end Mettapedia.GraphTheory.FourColor
