import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 1 chunk 3

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It intentionally keeps the batch smaller than the archived 64-row WIP.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block1Chunk3ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block1Chunk3Sources : List Nat :=
  [2288, 2289, 2290, 2291, 2292, 2293, 2294, 2295,
   2296, 2297, 2298, 2299, 2300, 2301, 2302, 2303]

def tttLargeFiber4Row112 : TripleComponentParentRow :=
  tripleRow 2288 2224 65 110 64 64 102 64
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row113 : TripleComponentParentRow :=
  tripleRow 2289 2225 65 110 65 64 102 65
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row114 : TripleComponentParentRow :=
  tripleRow 2290 2226 65 110 66 64 102 66
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row115 : TripleComponentParentRow :=
  tripleRow 2291 2227 65 110 67 64 102 67
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row116 : TripleComponentParentRow :=
  tripleRow 2292 2228 65 110 116 64 102 116
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row117 : TripleComponentParentRow :=
  tripleRow 2293 2229 65 110 117 64 102 117
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row118 : TripleComponentParentRow :=
  tripleRow 2294 2230 65 110 118 64 102 118
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row119 : TripleComponentParentRow :=
  tripleRow 2295 2231 65 110 119 64 102 119
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row120 : TripleComponentParentRow :=
  tripleRow 2296 2232 65 111 72 64 103 72
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row121 : TripleComponentParentRow :=
  tripleRow 2297 2233 65 111 73 64 103 73
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row122 : TripleComponentParentRow :=
  tripleRow 2298 2234 65 111 74 64 103 74
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row123 : TripleComponentParentRow :=
  tripleRow 2299 2235 65 111 75 64 103 75
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row124 : TripleComponentParentRow :=
  tripleRow 2300 2236 65 111 124 64 103 124
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row125 : TripleComponentParentRow :=
  tripleRow 2301 2237 65 111 125 64 103 125
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row126 : TripleComponentParentRow :=
  tripleRow 2302 2238 65 111 126 64 103 126
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row127 : TripleComponentParentRow :=
  tripleRow 2303 2239 65 111 127 64 103 127
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Block1Chunk3Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row112
  , tttLargeFiber4Row113
  , tttLargeFiber4Row114
  , tttLargeFiber4Row115
  , tttLargeFiber4Row116
  , tttLargeFiber4Row117
  , tttLargeFiber4Row118
  , tttLargeFiber4Row119
  , tttLargeFiber4Row120
  , tttLargeFiber4Row121
  , tttLargeFiber4Row122
  , tttLargeFiber4Row123
  , tttLargeFiber4Row124
  , tttLargeFiber4Row125
  , tttLargeFiber4Row126
  , tttLargeFiber4Row127
  ]

def tttLargeFiber4Block1Chunk3SourcesCheck : Bool :=
  (tttLargeFiber4Block1Chunk3Rows.map fun row => row.source) ==
    tttLargeFiber4Block1Chunk3Sources

theorem tttLargeFiber4Block1Chunk3SourcesCheck_ok :
    tttLargeFiber4Block1Chunk3SourcesCheck = true := by
  decide

def tttLargeFiber4Block1Chunk3RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttLargeFiber4Key tttLargeFiber4Expected
    (listGetD tttLargeFiber4Block1Chunk3Rows i default)

def tttLargeFiber4Block1Chunk3ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block1Chunk3Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block1Chunk3ParentConvergesCheck (i : Nat) : Bool :=
  tttLargeFiber4ParentIter tttLargeFiber4MaxParentDepth
    (listGetD tttLargeFiber4Block1Chunk3Sources i 0) ==
      tttLargeFiber4Root

theorem tttLargeFiber4Block1Chunk3Row_0_ok :
    tttLargeFiber4Block1Chunk3RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_1_ok :
    tttLargeFiber4Block1Chunk3RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_2_ok :
    tttLargeFiber4Block1Chunk3RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_3_ok :
    tttLargeFiber4Block1Chunk3RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_4_ok :
    tttLargeFiber4Block1Chunk3RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_5_ok :
    tttLargeFiber4Block1Chunk3RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_6_ok :
    tttLargeFiber4Block1Chunk3RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_7_ok :
    tttLargeFiber4Block1Chunk3RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_8_ok :
    tttLargeFiber4Block1Chunk3RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_9_ok :
    tttLargeFiber4Block1Chunk3RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_10_ok :
    tttLargeFiber4Block1Chunk3RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_11_ok :
    tttLargeFiber4Block1Chunk3RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_12_ok :
    tttLargeFiber4Block1Chunk3RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_13_ok :
    tttLargeFiber4Block1Chunk3RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_14_ok :
    tttLargeFiber4Block1Chunk3RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Row_15_ok :
    tttLargeFiber4Block1Chunk3RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_0_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_1_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_2_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_3_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_4_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_5_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_6_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_7_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_8_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_9_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_10_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_11_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_12_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_13_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_14_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3ParentMap_15_ok :
    tttLargeFiber4Block1Chunk3ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_0_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 0 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_1_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 1 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_2_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 2 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_3_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 3 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_4_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 4 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_5_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 5 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_6_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 6 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_7_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 7 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_8_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 8 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_9_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 9 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_10_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 10 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_11_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 11 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_12_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 12 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_13_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 13 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_14_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 14 = true := by
  decide

theorem tttLargeFiber4Block1Chunk3Parent_15_ok :
    tttLargeFiber4Block1Chunk3ParentConvergesCheck 15 = true := by
  decide

def tttLargeFiber4Block1Chunk3RowsAudit : Bool :=
  tttLargeFiber4Block1Chunk3RowCheck 0
    && tttLargeFiber4Block1Chunk3RowCheck 1
    && tttLargeFiber4Block1Chunk3RowCheck 2
    && tttLargeFiber4Block1Chunk3RowCheck 3
    && tttLargeFiber4Block1Chunk3RowCheck 4
    && tttLargeFiber4Block1Chunk3RowCheck 5
    && tttLargeFiber4Block1Chunk3RowCheck 6
    && tttLargeFiber4Block1Chunk3RowCheck 7
    && tttLargeFiber4Block1Chunk3RowCheck 8
    && tttLargeFiber4Block1Chunk3RowCheck 9
    && tttLargeFiber4Block1Chunk3RowCheck 10
    && tttLargeFiber4Block1Chunk3RowCheck 11
    && tttLargeFiber4Block1Chunk3RowCheck 12
    && tttLargeFiber4Block1Chunk3RowCheck 13
    && tttLargeFiber4Block1Chunk3RowCheck 14
    && tttLargeFiber4Block1Chunk3RowCheck 15

theorem tttLargeFiber4Block1Chunk3RowsAudit_ok :
    tttLargeFiber4Block1Chunk3RowsAudit = true := by
  simp [tttLargeFiber4Block1Chunk3RowsAudit,
    tttLargeFiber4Block1Chunk3Row_0_ok,
    tttLargeFiber4Block1Chunk3Row_1_ok,
    tttLargeFiber4Block1Chunk3Row_2_ok,
    tttLargeFiber4Block1Chunk3Row_3_ok,
    tttLargeFiber4Block1Chunk3Row_4_ok,
    tttLargeFiber4Block1Chunk3Row_5_ok,
    tttLargeFiber4Block1Chunk3Row_6_ok,
    tttLargeFiber4Block1Chunk3Row_7_ok,
    tttLargeFiber4Block1Chunk3Row_8_ok,
    tttLargeFiber4Block1Chunk3Row_9_ok,
    tttLargeFiber4Block1Chunk3Row_10_ok,
    tttLargeFiber4Block1Chunk3Row_11_ok,
    tttLargeFiber4Block1Chunk3Row_12_ok,
    tttLargeFiber4Block1Chunk3Row_13_ok,
    tttLargeFiber4Block1Chunk3Row_14_ok,
    tttLargeFiber4Block1Chunk3Row_15_ok]

def tttLargeFiber4Block1Chunk3ParentMapAudit : Bool :=
  tttLargeFiber4Block1Chunk3ParentMapCheck 0
    && tttLargeFiber4Block1Chunk3ParentMapCheck 1
    && tttLargeFiber4Block1Chunk3ParentMapCheck 2
    && tttLargeFiber4Block1Chunk3ParentMapCheck 3
    && tttLargeFiber4Block1Chunk3ParentMapCheck 4
    && tttLargeFiber4Block1Chunk3ParentMapCheck 5
    && tttLargeFiber4Block1Chunk3ParentMapCheck 6
    && tttLargeFiber4Block1Chunk3ParentMapCheck 7
    && tttLargeFiber4Block1Chunk3ParentMapCheck 8
    && tttLargeFiber4Block1Chunk3ParentMapCheck 9
    && tttLargeFiber4Block1Chunk3ParentMapCheck 10
    && tttLargeFiber4Block1Chunk3ParentMapCheck 11
    && tttLargeFiber4Block1Chunk3ParentMapCheck 12
    && tttLargeFiber4Block1Chunk3ParentMapCheck 13
    && tttLargeFiber4Block1Chunk3ParentMapCheck 14
    && tttLargeFiber4Block1Chunk3ParentMapCheck 15

theorem tttLargeFiber4Block1Chunk3ParentMapAudit_ok :
    tttLargeFiber4Block1Chunk3ParentMapAudit = true := by
  simp [tttLargeFiber4Block1Chunk3ParentMapAudit,
    tttLargeFiber4Block1Chunk3ParentMap_0_ok,
    tttLargeFiber4Block1Chunk3ParentMap_1_ok,
    tttLargeFiber4Block1Chunk3ParentMap_2_ok,
    tttLargeFiber4Block1Chunk3ParentMap_3_ok,
    tttLargeFiber4Block1Chunk3ParentMap_4_ok,
    tttLargeFiber4Block1Chunk3ParentMap_5_ok,
    tttLargeFiber4Block1Chunk3ParentMap_6_ok,
    tttLargeFiber4Block1Chunk3ParentMap_7_ok,
    tttLargeFiber4Block1Chunk3ParentMap_8_ok,
    tttLargeFiber4Block1Chunk3ParentMap_9_ok,
    tttLargeFiber4Block1Chunk3ParentMap_10_ok,
    tttLargeFiber4Block1Chunk3ParentMap_11_ok,
    tttLargeFiber4Block1Chunk3ParentMap_12_ok,
    tttLargeFiber4Block1Chunk3ParentMap_13_ok,
    tttLargeFiber4Block1Chunk3ParentMap_14_ok,
    tttLargeFiber4Block1Chunk3ParentMap_15_ok]

def tttLargeFiber4Block1Chunk3ParentsAudit : Bool :=
  tttLargeFiber4Block1Chunk3ParentConvergesCheck 0
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 1
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 2
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 3
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 4
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 5
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 6
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 7
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 8
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 9
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 10
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 11
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 12
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 13
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 14
    && tttLargeFiber4Block1Chunk3ParentConvergesCheck 15

theorem tttLargeFiber4Block1Chunk3ParentsAudit_ok :
    tttLargeFiber4Block1Chunk3ParentsAudit = true := by
  simp [tttLargeFiber4Block1Chunk3ParentsAudit,
    tttLargeFiber4Block1Chunk3Parent_0_ok,
    tttLargeFiber4Block1Chunk3Parent_1_ok,
    tttLargeFiber4Block1Chunk3Parent_2_ok,
    tttLargeFiber4Block1Chunk3Parent_3_ok,
    tttLargeFiber4Block1Chunk3Parent_4_ok,
    tttLargeFiber4Block1Chunk3Parent_5_ok,
    tttLargeFiber4Block1Chunk3Parent_6_ok,
    tttLargeFiber4Block1Chunk3Parent_7_ok,
    tttLargeFiber4Block1Chunk3Parent_8_ok,
    tttLargeFiber4Block1Chunk3Parent_9_ok,
    tttLargeFiber4Block1Chunk3Parent_10_ok,
    tttLargeFiber4Block1Chunk3Parent_11_ok,
    tttLargeFiber4Block1Chunk3Parent_12_ok,
    tttLargeFiber4Block1Chunk3Parent_13_ok,
    tttLargeFiber4Block1Chunk3Parent_14_ok,
    tttLargeFiber4Block1Chunk3Parent_15_ok]

def tttLargeFiber4Block1Chunk3ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block1Chunk3SourcesCheck &&
    tttLargeFiber4Block1Chunk3RowsAudit &&
    tttLargeFiber4Block1Chunk3ParentMapAudit &&
    tttLargeFiber4Block1Chunk3ParentsAudit

theorem tttLargeFiber4Block1Chunk3ComponentCertificateAudit_ok :
    tttLargeFiber4Block1Chunk3ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block1Chunk3ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block1Chunk3SourcesCheck_ok,
    tttLargeFiber4Block1Chunk3RowsAudit_ok,
    tttLargeFiber4Block1Chunk3ParentMapAudit_ok,
    tttLargeFiber4Block1Chunk3ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block1Chunk3ComponentCertificate

end Mettapedia.GraphTheory.FourColor
