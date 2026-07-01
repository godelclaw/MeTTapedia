import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 1 chunk 1

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It intentionally keeps the batch smaller than the archived 64-row WIP.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block1Chunk1ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block1Chunk1Sources : List Nat :=
  [2256, 2257, 2258, 2259, 2260, 2261, 2262, 2263,
   2264, 2265, 2266, 2267, 2268, 2269, 2270, 2271]

def tttLargeFiber4Row80 : TripleComponentParentRow :=
  tripleRow 2256 2192 65 90 16 64 82 16
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row81 : TripleComponentParentRow :=
  tripleRow 2257 2193 65 90 17 64 82 17
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row82 : TripleComponentParentRow :=
  tripleRow 2258 2194 65 90 18 64 82 18
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row83 : TripleComponentParentRow :=
  tripleRow 2259 2195 65 90 19 64 82 19
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row84 : TripleComponentParentRow :=
  tripleRow 2260 2196 65 90 32 64 82 32
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row85 : TripleComponentParentRow :=
  tripleRow 2261 2197 65 90 33 64 82 33
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row86 : TripleComponentParentRow :=
  tripleRow 2262 2198 65 90 34 64 82 34
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row87 : TripleComponentParentRow :=
  tripleRow 2263 2199 65 90 35 64 82 35
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row88 : TripleComponentParentRow :=
  tripleRow 2264 2200 65 91 24 64 83 24
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row89 : TripleComponentParentRow :=
  tripleRow 2265 2201 65 91 25 64 83 25
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row90 : TripleComponentParentRow :=
  tripleRow 2266 2202 65 91 26 64 83 26
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row91 : TripleComponentParentRow :=
  tripleRow 2267 2203 65 91 27 64 83 27
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row92 : TripleComponentParentRow :=
  tripleRow 2268 2204 65 91 40 64 83 40
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row93 : TripleComponentParentRow :=
  tripleRow 2269 2205 65 91 41 64 83 41
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row94 : TripleComponentParentRow :=
  tripleRow 2270 2206 65 91 42 64 83 42
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row95 : TripleComponentParentRow :=
  tripleRow 2271 2207 65 91 43 64 83 43
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Block1Chunk1Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row80
  , tttLargeFiber4Row81
  , tttLargeFiber4Row82
  , tttLargeFiber4Row83
  , tttLargeFiber4Row84
  , tttLargeFiber4Row85
  , tttLargeFiber4Row86
  , tttLargeFiber4Row87
  , tttLargeFiber4Row88
  , tttLargeFiber4Row89
  , tttLargeFiber4Row90
  , tttLargeFiber4Row91
  , tttLargeFiber4Row92
  , tttLargeFiber4Row93
  , tttLargeFiber4Row94
  , tttLargeFiber4Row95
  ]

def tttLargeFiber4Block1Chunk1SourcesCheck : Bool :=
  (tttLargeFiber4Block1Chunk1Rows.map fun row => row.source) ==
    tttLargeFiber4Block1Chunk1Sources

theorem tttLargeFiber4Block1Chunk1SourcesCheck_ok :
    tttLargeFiber4Block1Chunk1SourcesCheck = true := by
  decide

def tttLargeFiber4Block1Chunk1RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttLargeFiber4Key tttLargeFiber4Expected
    (listGetD tttLargeFiber4Block1Chunk1Rows i default)

def tttLargeFiber4Block1Chunk1ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block1Chunk1Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block1Chunk1ParentConvergesCheck (i : Nat) : Bool :=
  tttLargeFiber4ParentIter tttLargeFiber4MaxParentDepth
    (listGetD tttLargeFiber4Block1Chunk1Sources i 0) ==
      tttLargeFiber4Root

theorem tttLargeFiber4Block1Chunk1Row_0_ok :
    tttLargeFiber4Block1Chunk1RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_1_ok :
    tttLargeFiber4Block1Chunk1RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_2_ok :
    tttLargeFiber4Block1Chunk1RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_3_ok :
    tttLargeFiber4Block1Chunk1RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_4_ok :
    tttLargeFiber4Block1Chunk1RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_5_ok :
    tttLargeFiber4Block1Chunk1RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_6_ok :
    tttLargeFiber4Block1Chunk1RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_7_ok :
    tttLargeFiber4Block1Chunk1RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_8_ok :
    tttLargeFiber4Block1Chunk1RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_9_ok :
    tttLargeFiber4Block1Chunk1RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_10_ok :
    tttLargeFiber4Block1Chunk1RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_11_ok :
    tttLargeFiber4Block1Chunk1RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_12_ok :
    tttLargeFiber4Block1Chunk1RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_13_ok :
    tttLargeFiber4Block1Chunk1RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_14_ok :
    tttLargeFiber4Block1Chunk1RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Row_15_ok :
    tttLargeFiber4Block1Chunk1RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_0_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_1_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_2_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_3_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_4_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_5_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_6_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_7_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_8_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_9_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_10_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_11_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_12_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_13_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_14_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1ParentMap_15_ok :
    tttLargeFiber4Block1Chunk1ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_0_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 0 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_1_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 1 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_2_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 2 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_3_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 3 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_4_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 4 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_5_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 5 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_6_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 6 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_7_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 7 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_8_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 8 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_9_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 9 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_10_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 10 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_11_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 11 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_12_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 12 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_13_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 13 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_14_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 14 = true := by
  decide

theorem tttLargeFiber4Block1Chunk1Parent_15_ok :
    tttLargeFiber4Block1Chunk1ParentConvergesCheck 15 = true := by
  decide

def tttLargeFiber4Block1Chunk1RowsAudit : Bool :=
  tttLargeFiber4Block1Chunk1RowCheck 0
    && tttLargeFiber4Block1Chunk1RowCheck 1
    && tttLargeFiber4Block1Chunk1RowCheck 2
    && tttLargeFiber4Block1Chunk1RowCheck 3
    && tttLargeFiber4Block1Chunk1RowCheck 4
    && tttLargeFiber4Block1Chunk1RowCheck 5
    && tttLargeFiber4Block1Chunk1RowCheck 6
    && tttLargeFiber4Block1Chunk1RowCheck 7
    && tttLargeFiber4Block1Chunk1RowCheck 8
    && tttLargeFiber4Block1Chunk1RowCheck 9
    && tttLargeFiber4Block1Chunk1RowCheck 10
    && tttLargeFiber4Block1Chunk1RowCheck 11
    && tttLargeFiber4Block1Chunk1RowCheck 12
    && tttLargeFiber4Block1Chunk1RowCheck 13
    && tttLargeFiber4Block1Chunk1RowCheck 14
    && tttLargeFiber4Block1Chunk1RowCheck 15

theorem tttLargeFiber4Block1Chunk1RowsAudit_ok :
    tttLargeFiber4Block1Chunk1RowsAudit = true := by
  simp [tttLargeFiber4Block1Chunk1RowsAudit,
    tttLargeFiber4Block1Chunk1Row_0_ok,
    tttLargeFiber4Block1Chunk1Row_1_ok,
    tttLargeFiber4Block1Chunk1Row_2_ok,
    tttLargeFiber4Block1Chunk1Row_3_ok,
    tttLargeFiber4Block1Chunk1Row_4_ok,
    tttLargeFiber4Block1Chunk1Row_5_ok,
    tttLargeFiber4Block1Chunk1Row_6_ok,
    tttLargeFiber4Block1Chunk1Row_7_ok,
    tttLargeFiber4Block1Chunk1Row_8_ok,
    tttLargeFiber4Block1Chunk1Row_9_ok,
    tttLargeFiber4Block1Chunk1Row_10_ok,
    tttLargeFiber4Block1Chunk1Row_11_ok,
    tttLargeFiber4Block1Chunk1Row_12_ok,
    tttLargeFiber4Block1Chunk1Row_13_ok,
    tttLargeFiber4Block1Chunk1Row_14_ok,
    tttLargeFiber4Block1Chunk1Row_15_ok]

def tttLargeFiber4Block1Chunk1ParentMapAudit : Bool :=
  tttLargeFiber4Block1Chunk1ParentMapCheck 0
    && tttLargeFiber4Block1Chunk1ParentMapCheck 1
    && tttLargeFiber4Block1Chunk1ParentMapCheck 2
    && tttLargeFiber4Block1Chunk1ParentMapCheck 3
    && tttLargeFiber4Block1Chunk1ParentMapCheck 4
    && tttLargeFiber4Block1Chunk1ParentMapCheck 5
    && tttLargeFiber4Block1Chunk1ParentMapCheck 6
    && tttLargeFiber4Block1Chunk1ParentMapCheck 7
    && tttLargeFiber4Block1Chunk1ParentMapCheck 8
    && tttLargeFiber4Block1Chunk1ParentMapCheck 9
    && tttLargeFiber4Block1Chunk1ParentMapCheck 10
    && tttLargeFiber4Block1Chunk1ParentMapCheck 11
    && tttLargeFiber4Block1Chunk1ParentMapCheck 12
    && tttLargeFiber4Block1Chunk1ParentMapCheck 13
    && tttLargeFiber4Block1Chunk1ParentMapCheck 14
    && tttLargeFiber4Block1Chunk1ParentMapCheck 15

theorem tttLargeFiber4Block1Chunk1ParentMapAudit_ok :
    tttLargeFiber4Block1Chunk1ParentMapAudit = true := by
  simp [tttLargeFiber4Block1Chunk1ParentMapAudit,
    tttLargeFiber4Block1Chunk1ParentMap_0_ok,
    tttLargeFiber4Block1Chunk1ParentMap_1_ok,
    tttLargeFiber4Block1Chunk1ParentMap_2_ok,
    tttLargeFiber4Block1Chunk1ParentMap_3_ok,
    tttLargeFiber4Block1Chunk1ParentMap_4_ok,
    tttLargeFiber4Block1Chunk1ParentMap_5_ok,
    tttLargeFiber4Block1Chunk1ParentMap_6_ok,
    tttLargeFiber4Block1Chunk1ParentMap_7_ok,
    tttLargeFiber4Block1Chunk1ParentMap_8_ok,
    tttLargeFiber4Block1Chunk1ParentMap_9_ok,
    tttLargeFiber4Block1Chunk1ParentMap_10_ok,
    tttLargeFiber4Block1Chunk1ParentMap_11_ok,
    tttLargeFiber4Block1Chunk1ParentMap_12_ok,
    tttLargeFiber4Block1Chunk1ParentMap_13_ok,
    tttLargeFiber4Block1Chunk1ParentMap_14_ok,
    tttLargeFiber4Block1Chunk1ParentMap_15_ok]

def tttLargeFiber4Block1Chunk1ParentsAudit : Bool :=
  tttLargeFiber4Block1Chunk1ParentConvergesCheck 0
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 1
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 2
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 3
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 4
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 5
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 6
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 7
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 8
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 9
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 10
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 11
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 12
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 13
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 14
    && tttLargeFiber4Block1Chunk1ParentConvergesCheck 15

theorem tttLargeFiber4Block1Chunk1ParentsAudit_ok :
    tttLargeFiber4Block1Chunk1ParentsAudit = true := by
  simp [tttLargeFiber4Block1Chunk1ParentsAudit,
    tttLargeFiber4Block1Chunk1Parent_0_ok,
    tttLargeFiber4Block1Chunk1Parent_1_ok,
    tttLargeFiber4Block1Chunk1Parent_2_ok,
    tttLargeFiber4Block1Chunk1Parent_3_ok,
    tttLargeFiber4Block1Chunk1Parent_4_ok,
    tttLargeFiber4Block1Chunk1Parent_5_ok,
    tttLargeFiber4Block1Chunk1Parent_6_ok,
    tttLargeFiber4Block1Chunk1Parent_7_ok,
    tttLargeFiber4Block1Chunk1Parent_8_ok,
    tttLargeFiber4Block1Chunk1Parent_9_ok,
    tttLargeFiber4Block1Chunk1Parent_10_ok,
    tttLargeFiber4Block1Chunk1Parent_11_ok,
    tttLargeFiber4Block1Chunk1Parent_12_ok,
    tttLargeFiber4Block1Chunk1Parent_13_ok,
    tttLargeFiber4Block1Chunk1Parent_14_ok,
    tttLargeFiber4Block1Chunk1Parent_15_ok]

def tttLargeFiber4Block1Chunk1ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block1Chunk1SourcesCheck &&
    tttLargeFiber4Block1Chunk1RowsAudit &&
    tttLargeFiber4Block1Chunk1ParentMapAudit &&
    tttLargeFiber4Block1Chunk1ParentsAudit

theorem tttLargeFiber4Block1Chunk1ComponentCertificateAudit_ok :
    tttLargeFiber4Block1Chunk1ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block1Chunk1ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block1Chunk1SourcesCheck_ok,
    tttLargeFiber4Block1Chunk1RowsAudit_ok,
    tttLargeFiber4Block1Chunk1ParentMapAudit_ok,
    tttLargeFiber4Block1Chunk1ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block1Chunk1ComponentCertificate

end Mettapedia.GraphTheory.FourColor
