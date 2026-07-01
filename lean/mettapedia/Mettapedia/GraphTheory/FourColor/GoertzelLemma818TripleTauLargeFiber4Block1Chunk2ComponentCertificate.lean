import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 1 chunk 2

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It intentionally keeps the batch smaller than the archived 64-row WIP.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block1Chunk2ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block1Chunk2Sources : List Nat :=
  [2272, 2273, 2274, 2275, 2276, 2277, 2278, 2279,
   2280, 2281, 2282, 2283, 2284, 2285, 2286, 2287]

def tttLargeFiber4Row96 : TripleComponentParentRow :=
  tripleRow 2272 2208 65 108 132 64 100 132
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row97 : TripleComponentParentRow :=
  tripleRow 2273 2209 65 108 133 64 100 133
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row98 : TripleComponentParentRow :=
  tripleRow 2274 2210 65 108 134 64 100 134
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row99 : TripleComponentParentRow :=
  tripleRow 2275 2211 65 108 135 64 100 135
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row100 : TripleComponentParentRow :=
  tripleRow 2276 2212 65 108 180 64 100 180
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row101 : TripleComponentParentRow :=
  tripleRow 2277 2213 65 108 181 64 100 181
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row102 : TripleComponentParentRow :=
  tripleRow 2278 2214 65 108 182 64 100 182
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row103 : TripleComponentParentRow :=
  tripleRow 2279 2215 65 108 183 64 100 183
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row104 : TripleComponentParentRow :=
  tripleRow 2280 2216 65 109 140 64 101 140
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row105 : TripleComponentParentRow :=
  tripleRow 2281 2217 65 109 141 64 101 141
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row106 : TripleComponentParentRow :=
  tripleRow 2282 2218 65 109 142 64 101 142
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row107 : TripleComponentParentRow :=
  tripleRow 2283 2219 65 109 143 64 101 143
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row108 : TripleComponentParentRow :=
  tripleRow 2284 2220 65 109 188 64 101 188
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row109 : TripleComponentParentRow :=
  tripleRow 2285 2221 65 109 189 64 101 189
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row110 : TripleComponentParentRow :=
  tripleRow 2286 2222 65 109 190 64 101 190
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row111 : TripleComponentParentRow :=
  tripleRow 2287 2223 65 109 191 64 101 191
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Block1Chunk2Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row96
  , tttLargeFiber4Row97
  , tttLargeFiber4Row98
  , tttLargeFiber4Row99
  , tttLargeFiber4Row100
  , tttLargeFiber4Row101
  , tttLargeFiber4Row102
  , tttLargeFiber4Row103
  , tttLargeFiber4Row104
  , tttLargeFiber4Row105
  , tttLargeFiber4Row106
  , tttLargeFiber4Row107
  , tttLargeFiber4Row108
  , tttLargeFiber4Row109
  , tttLargeFiber4Row110
  , tttLargeFiber4Row111
  ]

def tttLargeFiber4Block1Chunk2SourcesCheck : Bool :=
  (tttLargeFiber4Block1Chunk2Rows.map fun row => row.source) ==
    tttLargeFiber4Block1Chunk2Sources

theorem tttLargeFiber4Block1Chunk2SourcesCheck_ok :
    tttLargeFiber4Block1Chunk2SourcesCheck = true := by
  decide

def tttLargeFiber4Block1Chunk2RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttLargeFiber4Key tttLargeFiber4Expected
    (listGetD tttLargeFiber4Block1Chunk2Rows i default)

def tttLargeFiber4Block1Chunk2ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block1Chunk2Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block1Chunk2ParentConvergesCheck (i : Nat) : Bool :=
  tttLargeFiber4ParentIter tttLargeFiber4MaxParentDepth
    (listGetD tttLargeFiber4Block1Chunk2Sources i 0) ==
      tttLargeFiber4Root

theorem tttLargeFiber4Block1Chunk2Row_0_ok :
    tttLargeFiber4Block1Chunk2RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_1_ok :
    tttLargeFiber4Block1Chunk2RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_2_ok :
    tttLargeFiber4Block1Chunk2RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_3_ok :
    tttLargeFiber4Block1Chunk2RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_4_ok :
    tttLargeFiber4Block1Chunk2RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_5_ok :
    tttLargeFiber4Block1Chunk2RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_6_ok :
    tttLargeFiber4Block1Chunk2RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_7_ok :
    tttLargeFiber4Block1Chunk2RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_8_ok :
    tttLargeFiber4Block1Chunk2RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_9_ok :
    tttLargeFiber4Block1Chunk2RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_10_ok :
    tttLargeFiber4Block1Chunk2RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_11_ok :
    tttLargeFiber4Block1Chunk2RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_12_ok :
    tttLargeFiber4Block1Chunk2RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_13_ok :
    tttLargeFiber4Block1Chunk2RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_14_ok :
    tttLargeFiber4Block1Chunk2RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Row_15_ok :
    tttLargeFiber4Block1Chunk2RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_0_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_1_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_2_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_3_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_4_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_5_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_6_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_7_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_8_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_9_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_10_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_11_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_12_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_13_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_14_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2ParentMap_15_ok :
    tttLargeFiber4Block1Chunk2ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_0_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 0 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_1_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 1 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_2_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 2 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_3_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 3 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_4_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 4 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_5_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 5 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_6_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 6 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_7_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 7 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_8_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 8 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_9_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 9 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_10_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 10 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_11_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 11 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_12_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 12 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_13_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 13 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_14_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 14 = true := by
  decide

theorem tttLargeFiber4Block1Chunk2Parent_15_ok :
    tttLargeFiber4Block1Chunk2ParentConvergesCheck 15 = true := by
  decide

def tttLargeFiber4Block1Chunk2RowsAudit : Bool :=
  tttLargeFiber4Block1Chunk2RowCheck 0
    && tttLargeFiber4Block1Chunk2RowCheck 1
    && tttLargeFiber4Block1Chunk2RowCheck 2
    && tttLargeFiber4Block1Chunk2RowCheck 3
    && tttLargeFiber4Block1Chunk2RowCheck 4
    && tttLargeFiber4Block1Chunk2RowCheck 5
    && tttLargeFiber4Block1Chunk2RowCheck 6
    && tttLargeFiber4Block1Chunk2RowCheck 7
    && tttLargeFiber4Block1Chunk2RowCheck 8
    && tttLargeFiber4Block1Chunk2RowCheck 9
    && tttLargeFiber4Block1Chunk2RowCheck 10
    && tttLargeFiber4Block1Chunk2RowCheck 11
    && tttLargeFiber4Block1Chunk2RowCheck 12
    && tttLargeFiber4Block1Chunk2RowCheck 13
    && tttLargeFiber4Block1Chunk2RowCheck 14
    && tttLargeFiber4Block1Chunk2RowCheck 15

theorem tttLargeFiber4Block1Chunk2RowsAudit_ok :
    tttLargeFiber4Block1Chunk2RowsAudit = true := by
  simp [tttLargeFiber4Block1Chunk2RowsAudit,
    tttLargeFiber4Block1Chunk2Row_0_ok,
    tttLargeFiber4Block1Chunk2Row_1_ok,
    tttLargeFiber4Block1Chunk2Row_2_ok,
    tttLargeFiber4Block1Chunk2Row_3_ok,
    tttLargeFiber4Block1Chunk2Row_4_ok,
    tttLargeFiber4Block1Chunk2Row_5_ok,
    tttLargeFiber4Block1Chunk2Row_6_ok,
    tttLargeFiber4Block1Chunk2Row_7_ok,
    tttLargeFiber4Block1Chunk2Row_8_ok,
    tttLargeFiber4Block1Chunk2Row_9_ok,
    tttLargeFiber4Block1Chunk2Row_10_ok,
    tttLargeFiber4Block1Chunk2Row_11_ok,
    tttLargeFiber4Block1Chunk2Row_12_ok,
    tttLargeFiber4Block1Chunk2Row_13_ok,
    tttLargeFiber4Block1Chunk2Row_14_ok,
    tttLargeFiber4Block1Chunk2Row_15_ok]

def tttLargeFiber4Block1Chunk2ParentMapAudit : Bool :=
  tttLargeFiber4Block1Chunk2ParentMapCheck 0
    && tttLargeFiber4Block1Chunk2ParentMapCheck 1
    && tttLargeFiber4Block1Chunk2ParentMapCheck 2
    && tttLargeFiber4Block1Chunk2ParentMapCheck 3
    && tttLargeFiber4Block1Chunk2ParentMapCheck 4
    && tttLargeFiber4Block1Chunk2ParentMapCheck 5
    && tttLargeFiber4Block1Chunk2ParentMapCheck 6
    && tttLargeFiber4Block1Chunk2ParentMapCheck 7
    && tttLargeFiber4Block1Chunk2ParentMapCheck 8
    && tttLargeFiber4Block1Chunk2ParentMapCheck 9
    && tttLargeFiber4Block1Chunk2ParentMapCheck 10
    && tttLargeFiber4Block1Chunk2ParentMapCheck 11
    && tttLargeFiber4Block1Chunk2ParentMapCheck 12
    && tttLargeFiber4Block1Chunk2ParentMapCheck 13
    && tttLargeFiber4Block1Chunk2ParentMapCheck 14
    && tttLargeFiber4Block1Chunk2ParentMapCheck 15

theorem tttLargeFiber4Block1Chunk2ParentMapAudit_ok :
    tttLargeFiber4Block1Chunk2ParentMapAudit = true := by
  simp [tttLargeFiber4Block1Chunk2ParentMapAudit,
    tttLargeFiber4Block1Chunk2ParentMap_0_ok,
    tttLargeFiber4Block1Chunk2ParentMap_1_ok,
    tttLargeFiber4Block1Chunk2ParentMap_2_ok,
    tttLargeFiber4Block1Chunk2ParentMap_3_ok,
    tttLargeFiber4Block1Chunk2ParentMap_4_ok,
    tttLargeFiber4Block1Chunk2ParentMap_5_ok,
    tttLargeFiber4Block1Chunk2ParentMap_6_ok,
    tttLargeFiber4Block1Chunk2ParentMap_7_ok,
    tttLargeFiber4Block1Chunk2ParentMap_8_ok,
    tttLargeFiber4Block1Chunk2ParentMap_9_ok,
    tttLargeFiber4Block1Chunk2ParentMap_10_ok,
    tttLargeFiber4Block1Chunk2ParentMap_11_ok,
    tttLargeFiber4Block1Chunk2ParentMap_12_ok,
    tttLargeFiber4Block1Chunk2ParentMap_13_ok,
    tttLargeFiber4Block1Chunk2ParentMap_14_ok,
    tttLargeFiber4Block1Chunk2ParentMap_15_ok]

def tttLargeFiber4Block1Chunk2ParentsAudit : Bool :=
  tttLargeFiber4Block1Chunk2ParentConvergesCheck 0
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 1
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 2
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 3
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 4
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 5
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 6
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 7
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 8
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 9
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 10
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 11
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 12
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 13
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 14
    && tttLargeFiber4Block1Chunk2ParentConvergesCheck 15

theorem tttLargeFiber4Block1Chunk2ParentsAudit_ok :
    tttLargeFiber4Block1Chunk2ParentsAudit = true := by
  simp [tttLargeFiber4Block1Chunk2ParentsAudit,
    tttLargeFiber4Block1Chunk2Parent_0_ok,
    tttLargeFiber4Block1Chunk2Parent_1_ok,
    tttLargeFiber4Block1Chunk2Parent_2_ok,
    tttLargeFiber4Block1Chunk2Parent_3_ok,
    tttLargeFiber4Block1Chunk2Parent_4_ok,
    tttLargeFiber4Block1Chunk2Parent_5_ok,
    tttLargeFiber4Block1Chunk2Parent_6_ok,
    tttLargeFiber4Block1Chunk2Parent_7_ok,
    tttLargeFiber4Block1Chunk2Parent_8_ok,
    tttLargeFiber4Block1Chunk2Parent_9_ok,
    tttLargeFiber4Block1Chunk2Parent_10_ok,
    tttLargeFiber4Block1Chunk2Parent_11_ok,
    tttLargeFiber4Block1Chunk2Parent_12_ok,
    tttLargeFiber4Block1Chunk2Parent_13_ok,
    tttLargeFiber4Block1Chunk2Parent_14_ok,
    tttLargeFiber4Block1Chunk2Parent_15_ok]

def tttLargeFiber4Block1Chunk2ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block1Chunk2SourcesCheck &&
    tttLargeFiber4Block1Chunk2RowsAudit &&
    tttLargeFiber4Block1Chunk2ParentMapAudit &&
    tttLargeFiber4Block1Chunk2ParentsAudit

theorem tttLargeFiber4Block1Chunk2ComponentCertificateAudit_ok :
    tttLargeFiber4Block1Chunk2ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block1Chunk2ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block1Chunk2SourcesCheck_ok,
    tttLargeFiber4Block1Chunk2RowsAudit_ok,
    tttLargeFiber4Block1Chunk2ParentMapAudit_ok,
    tttLargeFiber4Block1Chunk2ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block1Chunk2ComponentCertificate

end Mettapedia.GraphTheory.FourColor
