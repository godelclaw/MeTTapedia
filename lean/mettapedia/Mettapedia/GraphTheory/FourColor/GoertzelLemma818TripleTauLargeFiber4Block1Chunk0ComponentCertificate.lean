import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 1 chunk 0

This generated module checks 16 explicit-component rows for the first
size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It intentionally keeps the batch smaller than the archived 64-row WIP.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block1Chunk0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block1Chunk0Sources : List Nat :=
  [2240, 2241, 2242, 2243, 2244, 2245, 2246, 2247,
   2248, 2249, 2250, 2251, 2252, 2253, 2254, 2255]

def tttLargeFiber4Row64 : TripleComponentParentRow :=
  tripleRow 2240 2176 65 88 80 64 80 80
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row65 : TripleComponentParentRow :=
  tripleRow 2241 2177 65 88 81 64 80 81
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row66 : TripleComponentParentRow :=
  tripleRow 2242 2178 65 88 82 64 80 82
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row67 : TripleComponentParentRow :=
  tripleRow 2243 2179 65 88 83 64 80 83
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row68 : TripleComponentParentRow :=
  tripleRow 2244 2180 65 88 100 64 80 100
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row69 : TripleComponentParentRow :=
  tripleRow 2245 2181 65 88 101 64 80 101
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row70 : TripleComponentParentRow :=
  tripleRow 2246 2182 65 88 102 64 80 102
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row71 : TripleComponentParentRow :=
  tripleRow 2247 2183 65 88 103 64 80 103
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row72 : TripleComponentParentRow :=
  tripleRow 2248 2184 65 89 88 64 81 88
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row73 : TripleComponentParentRow :=
  tripleRow 2249 2185 65 89 89 64 81 89
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row74 : TripleComponentParentRow :=
  tripleRow 2250 2186 65 89 90 64 81 90
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row75 : TripleComponentParentRow :=
  tripleRow 2251 2187 65 89 91 64 81 91
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row76 : TripleComponentParentRow :=
  tripleRow 2252 2188 65 89 108 64 81 108
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row77 : TripleComponentParentRow :=
  tripleRow 2253 2189 65 89 109 64 81 109
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row78 : TripleComponentParentRow :=
  tripleRow 2254 2190 65 89 110 64 81 110
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Row79 : TripleComponentParentRow :=
  tripleRow 2255 2191 65 89 111 64 81 111
    (chainMove LColor.b LColor.p 0 TauEdge.B5)
    [ chainEdge 0 TauEdge.B5
    , chainEdge 0 TauEdge.B6
    ]

def tttLargeFiber4Block1Chunk0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row64
  , tttLargeFiber4Row65
  , tttLargeFiber4Row66
  , tttLargeFiber4Row67
  , tttLargeFiber4Row68
  , tttLargeFiber4Row69
  , tttLargeFiber4Row70
  , tttLargeFiber4Row71
  , tttLargeFiber4Row72
  , tttLargeFiber4Row73
  , tttLargeFiber4Row74
  , tttLargeFiber4Row75
  , tttLargeFiber4Row76
  , tttLargeFiber4Row77
  , tttLargeFiber4Row78
  , tttLargeFiber4Row79
  ]

def tttLargeFiber4Block1Chunk0SourcesCheck : Bool :=
  (tttLargeFiber4Block1Chunk0Rows.map fun row => row.source) ==
    tttLargeFiber4Block1Chunk0Sources

theorem tttLargeFiber4Block1Chunk0SourcesCheck_ok :
    tttLargeFiber4Block1Chunk0SourcesCheck = true := by
  decide

def tttLargeFiber4Block1Chunk0RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttLargeFiber4Key tttLargeFiber4Expected
    (listGetD tttLargeFiber4Block1Chunk0Rows i default)

def tttLargeFiber4Block1Chunk0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block1Chunk0Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block1Chunk0ParentConvergesCheck (i : Nat) : Bool :=
  tttLargeFiber4ParentIter tttLargeFiber4MaxParentDepth
    (listGetD tttLargeFiber4Block1Chunk0Sources i 0) ==
      tttLargeFiber4Root

theorem tttLargeFiber4Block1Chunk0Row_0_ok :
    tttLargeFiber4Block1Chunk0RowCheck 0 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_1_ok :
    tttLargeFiber4Block1Chunk0RowCheck 1 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_2_ok :
    tttLargeFiber4Block1Chunk0RowCheck 2 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_3_ok :
    tttLargeFiber4Block1Chunk0RowCheck 3 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_4_ok :
    tttLargeFiber4Block1Chunk0RowCheck 4 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_5_ok :
    tttLargeFiber4Block1Chunk0RowCheck 5 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_6_ok :
    tttLargeFiber4Block1Chunk0RowCheck 6 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_7_ok :
    tttLargeFiber4Block1Chunk0RowCheck 7 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_8_ok :
    tttLargeFiber4Block1Chunk0RowCheck 8 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_9_ok :
    tttLargeFiber4Block1Chunk0RowCheck 9 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_10_ok :
    tttLargeFiber4Block1Chunk0RowCheck 10 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_11_ok :
    tttLargeFiber4Block1Chunk0RowCheck 11 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_12_ok :
    tttLargeFiber4Block1Chunk0RowCheck 12 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_13_ok :
    tttLargeFiber4Block1Chunk0RowCheck 13 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_14_ok :
    tttLargeFiber4Block1Chunk0RowCheck 14 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Row_15_ok :
    tttLargeFiber4Block1Chunk0RowCheck 15 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_0_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 0 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_1_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 1 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_2_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 2 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_3_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 3 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_4_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 4 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_5_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 5 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_6_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 6 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_7_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 7 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_8_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 8 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_9_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 9 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_10_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 10 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_11_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 11 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_12_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 12 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_13_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 13 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_14_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 14 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0ParentMap_15_ok :
    tttLargeFiber4Block1Chunk0ParentMapCheck 15 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_0_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 0 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_1_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 1 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_2_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 2 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_3_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 3 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_4_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 4 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_5_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 5 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_6_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 6 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_7_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 7 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_8_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 8 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_9_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 9 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_10_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 10 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_11_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 11 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_12_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 12 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_13_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 13 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_14_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 14 = true := by
  decide

theorem tttLargeFiber4Block1Chunk0Parent_15_ok :
    tttLargeFiber4Block1Chunk0ParentConvergesCheck 15 = true := by
  decide

def tttLargeFiber4Block1Chunk0RowsAudit : Bool :=
  tttLargeFiber4Block1Chunk0RowCheck 0
    && tttLargeFiber4Block1Chunk0RowCheck 1
    && tttLargeFiber4Block1Chunk0RowCheck 2
    && tttLargeFiber4Block1Chunk0RowCheck 3
    && tttLargeFiber4Block1Chunk0RowCheck 4
    && tttLargeFiber4Block1Chunk0RowCheck 5
    && tttLargeFiber4Block1Chunk0RowCheck 6
    && tttLargeFiber4Block1Chunk0RowCheck 7
    && tttLargeFiber4Block1Chunk0RowCheck 8
    && tttLargeFiber4Block1Chunk0RowCheck 9
    && tttLargeFiber4Block1Chunk0RowCheck 10
    && tttLargeFiber4Block1Chunk0RowCheck 11
    && tttLargeFiber4Block1Chunk0RowCheck 12
    && tttLargeFiber4Block1Chunk0RowCheck 13
    && tttLargeFiber4Block1Chunk0RowCheck 14
    && tttLargeFiber4Block1Chunk0RowCheck 15

theorem tttLargeFiber4Block1Chunk0RowsAudit_ok :
    tttLargeFiber4Block1Chunk0RowsAudit = true := by
  simp [tttLargeFiber4Block1Chunk0RowsAudit,
    tttLargeFiber4Block1Chunk0Row_0_ok,
    tttLargeFiber4Block1Chunk0Row_1_ok,
    tttLargeFiber4Block1Chunk0Row_2_ok,
    tttLargeFiber4Block1Chunk0Row_3_ok,
    tttLargeFiber4Block1Chunk0Row_4_ok,
    tttLargeFiber4Block1Chunk0Row_5_ok,
    tttLargeFiber4Block1Chunk0Row_6_ok,
    tttLargeFiber4Block1Chunk0Row_7_ok,
    tttLargeFiber4Block1Chunk0Row_8_ok,
    tttLargeFiber4Block1Chunk0Row_9_ok,
    tttLargeFiber4Block1Chunk0Row_10_ok,
    tttLargeFiber4Block1Chunk0Row_11_ok,
    tttLargeFiber4Block1Chunk0Row_12_ok,
    tttLargeFiber4Block1Chunk0Row_13_ok,
    tttLargeFiber4Block1Chunk0Row_14_ok,
    tttLargeFiber4Block1Chunk0Row_15_ok]

def tttLargeFiber4Block1Chunk0ParentMapAudit : Bool :=
  tttLargeFiber4Block1Chunk0ParentMapCheck 0
    && tttLargeFiber4Block1Chunk0ParentMapCheck 1
    && tttLargeFiber4Block1Chunk0ParentMapCheck 2
    && tttLargeFiber4Block1Chunk0ParentMapCheck 3
    && tttLargeFiber4Block1Chunk0ParentMapCheck 4
    && tttLargeFiber4Block1Chunk0ParentMapCheck 5
    && tttLargeFiber4Block1Chunk0ParentMapCheck 6
    && tttLargeFiber4Block1Chunk0ParentMapCheck 7
    && tttLargeFiber4Block1Chunk0ParentMapCheck 8
    && tttLargeFiber4Block1Chunk0ParentMapCheck 9
    && tttLargeFiber4Block1Chunk0ParentMapCheck 10
    && tttLargeFiber4Block1Chunk0ParentMapCheck 11
    && tttLargeFiber4Block1Chunk0ParentMapCheck 12
    && tttLargeFiber4Block1Chunk0ParentMapCheck 13
    && tttLargeFiber4Block1Chunk0ParentMapCheck 14
    && tttLargeFiber4Block1Chunk0ParentMapCheck 15

theorem tttLargeFiber4Block1Chunk0ParentMapAudit_ok :
    tttLargeFiber4Block1Chunk0ParentMapAudit = true := by
  simp [tttLargeFiber4Block1Chunk0ParentMapAudit,
    tttLargeFiber4Block1Chunk0ParentMap_0_ok,
    tttLargeFiber4Block1Chunk0ParentMap_1_ok,
    tttLargeFiber4Block1Chunk0ParentMap_2_ok,
    tttLargeFiber4Block1Chunk0ParentMap_3_ok,
    tttLargeFiber4Block1Chunk0ParentMap_4_ok,
    tttLargeFiber4Block1Chunk0ParentMap_5_ok,
    tttLargeFiber4Block1Chunk0ParentMap_6_ok,
    tttLargeFiber4Block1Chunk0ParentMap_7_ok,
    tttLargeFiber4Block1Chunk0ParentMap_8_ok,
    tttLargeFiber4Block1Chunk0ParentMap_9_ok,
    tttLargeFiber4Block1Chunk0ParentMap_10_ok,
    tttLargeFiber4Block1Chunk0ParentMap_11_ok,
    tttLargeFiber4Block1Chunk0ParentMap_12_ok,
    tttLargeFiber4Block1Chunk0ParentMap_13_ok,
    tttLargeFiber4Block1Chunk0ParentMap_14_ok,
    tttLargeFiber4Block1Chunk0ParentMap_15_ok]

def tttLargeFiber4Block1Chunk0ParentsAudit : Bool :=
  tttLargeFiber4Block1Chunk0ParentConvergesCheck 0
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 1
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 2
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 3
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 4
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 5
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 6
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 7
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 8
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 9
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 10
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 11
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 12
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 13
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 14
    && tttLargeFiber4Block1Chunk0ParentConvergesCheck 15

theorem tttLargeFiber4Block1Chunk0ParentsAudit_ok :
    tttLargeFiber4Block1Chunk0ParentsAudit = true := by
  simp [tttLargeFiber4Block1Chunk0ParentsAudit,
    tttLargeFiber4Block1Chunk0Parent_0_ok,
    tttLargeFiber4Block1Chunk0Parent_1_ok,
    tttLargeFiber4Block1Chunk0Parent_2_ok,
    tttLargeFiber4Block1Chunk0Parent_3_ok,
    tttLargeFiber4Block1Chunk0Parent_4_ok,
    tttLargeFiber4Block1Chunk0Parent_5_ok,
    tttLargeFiber4Block1Chunk0Parent_6_ok,
    tttLargeFiber4Block1Chunk0Parent_7_ok,
    tttLargeFiber4Block1Chunk0Parent_8_ok,
    tttLargeFiber4Block1Chunk0Parent_9_ok,
    tttLargeFiber4Block1Chunk0Parent_10_ok,
    tttLargeFiber4Block1Chunk0Parent_11_ok,
    tttLargeFiber4Block1Chunk0Parent_12_ok,
    tttLargeFiber4Block1Chunk0Parent_13_ok,
    tttLargeFiber4Block1Chunk0Parent_14_ok,
    tttLargeFiber4Block1Chunk0Parent_15_ok]

def tttLargeFiber4Block1Chunk0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block1Chunk0SourcesCheck &&
    tttLargeFiber4Block1Chunk0RowsAudit &&
    tttLargeFiber4Block1Chunk0ParentMapAudit &&
    tttLargeFiber4Block1Chunk0ParentsAudit

theorem tttLargeFiber4Block1Chunk0ComponentCertificateAudit_ok :
    tttLargeFiber4Block1Chunk0ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block1Chunk0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block1Chunk0SourcesCheck_ok,
    tttLargeFiber4Block1Chunk0RowsAudit_ok,
    tttLargeFiber4Block1Chunk0ParentMapAudit_ok,
    tttLargeFiber4Block1Chunk0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block1Chunk0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
