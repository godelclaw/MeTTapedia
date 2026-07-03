import Mettapedia.GraphTheory.FourColor.GoertzelLemma818TripleTauLargeFiber4Data

namespace Mettapedia.GraphTheory.FourColor

/-!
# Goertzel Lemma 8.18: first large `TTT` fiber, block 0

This generated module checks the first 64 explicit component rows for the
first size-512 fixed-input fiber of the `TTT`/`mode09` representative target.
It is a decomposed certificate block, not the full large-fiber audit.
-/

namespace GoertzelLemma818TripleTauLargeFiber4Block0ComponentCertificate

open GoertzelLemma814
open GoertzelLemma818ComponentCertificate
open GoertzelLemma818TripleTauLightComponentCertificate
open GoertzelLemma818TripleTauLargeFiber4Data

def tttLargeFiber4Block0Sources : List Nat :=
  [2176, 2177, 2178, 2179, 2180, 2181, 2182, 2183,
   2184, 2185, 2186, 2187, 2188, 2189, 2190, 2191,
   2192, 2193, 2194, 2195, 2196, 2197, 2198, 2199,
   2200, 2201, 2202, 2203, 2204, 2205, 2206, 2207,
   2208, 2209, 2210, 2211, 2212, 2213, 2214, 2215,
   2216, 2217, 2218, 2219, 2220, 2221, 2222, 2223,
   2224, 2225, 2226, 2227, 2228, 2229, 2230, 2231,
   2232, 2233, 2234, 2235, 2236, 2237, 2238, 2239]

def tttLargeFiber4Row0 : TripleComponentParentRow :=
  tripleRow 2176 2176 64 80 80 64 80 80
    default
    []

def tttLargeFiber4Row1 : TripleComponentParentRow :=
  tripleRow 2177 2176 64 80 81 64 80 80
    (chainMove LColor.b LColor.p 2 TauEdge.B5)
    [ chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row2 : TripleComponentParentRow :=
  tripleRow 2178 2176 64 80 82 64 80 80
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row3 : TripleComponentParentRow :=
  tripleRow 2179 2177 64 80 83 64 80 81
    (chainMove LColor.r LColor.b 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row4 : TripleComponentParentRow :=
  tripleRow 2180 2178 64 80 100 64 80 82
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row5 : TripleComponentParentRow :=
  tripleRow 2181 2183 64 80 101 64 80 103
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row6 : TripleComponentParentRow :=
  tripleRow 2182 2177 64 80 102 64 80 81
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row7 : TripleComponentParentRow :=
  tripleRow 2183 2176 64 80 103 64 80 80
    (chainMove LColor.r LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row8 : TripleComponentParentRow :=
  tripleRow 2184 2176 64 81 88 64 80 80
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row9 : TripleComponentParentRow :=
  tripleRow 2185 2177 64 81 89 64 80 81
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row10 : TripleComponentParentRow :=
  tripleRow 2186 2178 64 81 90 64 80 82
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row11 : TripleComponentParentRow :=
  tripleRow 2187 2179 64 81 91 64 80 83
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row12 : TripleComponentParentRow :=
  tripleRow 2188 2180 64 81 108 64 80 100
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row13 : TripleComponentParentRow :=
  tripleRow 2189 2181 64 81 109 64 80 101
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row14 : TripleComponentParentRow :=
  tripleRow 2190 2182 64 81 110 64 80 102
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row15 : TripleComponentParentRow :=
  tripleRow 2191 2183 64 81 111 64 80 103
    (chainMove LColor.b LColor.p 1 TauEdge.B5)
    [ chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row16 : TripleComponentParentRow :=
  tripleRow 2192 2176 64 82 16 64 80 80
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row17 : TripleComponentParentRow :=
  tripleRow 2193 2177 64 82 17 64 80 81
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row18 : TripleComponentParentRow :=
  tripleRow 2194 2178 64 82 18 64 80 82
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row19 : TripleComponentParentRow :=
  tripleRow 2195 2179 64 82 19 64 80 83
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row20 : TripleComponentParentRow :=
  tripleRow 2196 2192 64 82 32 64 82 16
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row21 : TripleComponentParentRow :=
  tripleRow 2197 2193 64 82 33 64 82 17
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row22 : TripleComponentParentRow :=
  tripleRow 2198 2182 64 82 34 64 80 102
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row23 : TripleComponentParentRow :=
  tripleRow 2199 2183 64 82 35 64 80 103
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row24 : TripleComponentParentRow :=
  tripleRow 2200 2184 64 83 24 64 81 88
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row25 : TripleComponentParentRow :=
  tripleRow 2201 2185 64 83 25 64 81 89
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row26 : TripleComponentParentRow :=
  tripleRow 2202 2186 64 83 26 64 81 90
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row27 : TripleComponentParentRow :=
  tripleRow 2203 2187 64 83 27 64 81 91
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row28 : TripleComponentParentRow :=
  tripleRow 2204 2200 64 83 40 64 83 24
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row29 : TripleComponentParentRow :=
  tripleRow 2205 2201 64 83 41 64 83 25
    (chainMove LColor.b LColor.p 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row30 : TripleComponentParentRow :=
  tripleRow 2206 2190 64 83 42 64 81 110
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row31 : TripleComponentParentRow :=
  tripleRow 2207 2191 64 83 43 64 81 111
    (chainMove LColor.r LColor.b 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row32 : TripleComponentParentRow :=
  tripleRow 2208 2224 64 100 132 64 102 64
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row33 : TripleComponentParentRow :=
  tripleRow 2209 2225 64 100 133 64 102 65
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B6
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row34 : TripleComponentParentRow :=
  tripleRow 2210 2198 64 100 134 64 82 34
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber4Row35 : TripleComponentParentRow :=
  tripleRow 2211 2199 64 100 135 64 82 35
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F3
    ]

def tttLargeFiber4Row36 : TripleComponentParentRow :=
  tripleRow 2212 2194 64 100 180 64 82 18
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row37 : TripleComponentParentRow :=
  tripleRow 2213 2215 64 100 181 64 100 183
    (chainMove LColor.b LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row38 : TripleComponentParentRow :=
  tripleRow 2214 2193 64 100 182 64 82 17
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row39 : TripleComponentParentRow :=
  tripleRow 2215 2192 64 100 183 64 82 16
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row40 : TripleComponentParentRow :=
  tripleRow 2216 2232 64 101 140 64 103 72
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row41 : TripleComponentParentRow :=
  tripleRow 2217 2233 64 101 141 64 103 73
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row42 : TripleComponentParentRow :=
  tripleRow 2218 2234 64 101 142 64 103 74
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F0F2
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row43 : TripleComponentParentRow :=
  tripleRow 2219 2216 64 101 143 64 101 140
    (chainMove LColor.r LColor.p 2 TauEdge.F4F5)
    [ chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    , chainEdge 2 TauEdge.B7
    ]

def tttLargeFiber4Row44 : TripleComponentParentRow :=
  tripleRow 2220 2216 64 101 188 64 101 140
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B5
    ]

def tttLargeFiber4Row45 : TripleComponentParentRow :=
  tripleRow 2221 2217 64 101 189 64 101 141
    (chainMove LColor.r LColor.b 2 TauEdge.F2F3)
    [ chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F2F4
    , chainEdge 2 TauEdge.B4
    , chainEdge 2 TauEdge.F4F5
    , chainEdge 2 TauEdge.B6
    ]

def tttLargeFiber4Row46 : TripleComponentParentRow :=
  tripleRow 2222 2238 64 101 190 64 103 126
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row47 : TripleComponentParentRow :=
  tripleRow 2223 2239 64 101 191 64 103 127
    (chainMove LColor.b LColor.p 1 TauEdge.F4F5)
    [ chainEdge 1 TauEdge.F4F5
    , chainEdge 1 TauEdge.B5
    , chainEdge 1 TauEdge.B7
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 2 TauEdge.F2F3
    , chainEdge 2 TauEdge.F0F2
    ]

def tttLargeFiber4Row48 : TripleComponentParentRow :=
  tripleRow 2224 2184 64 102 64 64 81 88
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row49 : TripleComponentParentRow :=
  tripleRow 2225 2185 64 102 65 64 81 89
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row50 : TripleComponentParentRow :=
  tripleRow 2226 2186 64 102 66 64 81 90
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row51 : TripleComponentParentRow :=
  tripleRow 2227 2187 64 102 67 64 81 91
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row52 : TripleComponentParentRow :=
  tripleRow 2228 2188 64 102 116 64 81 108
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row53 : TripleComponentParentRow :=
  tripleRow 2229 2189 64 102 117 64 81 109
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row54 : TripleComponentParentRow :=
  tripleRow 2230 2190 64 102 118 64 81 110
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row55 : TripleComponentParentRow :=
  tripleRow 2231 2191 64 102 119 64 81 111
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B5
    ]

def tttLargeFiber4Row56 : TripleComponentParentRow :=
  tripleRow 2232 2176 64 103 72 64 80 80
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row57 : TripleComponentParentRow :=
  tripleRow 2233 2177 64 103 73 64 80 81
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row58 : TripleComponentParentRow :=
  tripleRow 2234 2178 64 103 74 64 80 82
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row59 : TripleComponentParentRow :=
  tripleRow 2235 2179 64 103 75 64 80 83
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row60 : TripleComponentParentRow :=
  tripleRow 2236 2180 64 103 124 64 80 100
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row61 : TripleComponentParentRow :=
  tripleRow 2237 2181 64 103 125 64 80 101
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row62 : TripleComponentParentRow :=
  tripleRow 2238 2182 64 103 126 64 80 102
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Row63 : TripleComponentParentRow :=
  tripleRow 2239 2183 64 103 127 64 80 103
    (chainMove LColor.r LColor.p 1 TauEdge.F2F3)
    [ chainEdge 1 TauEdge.F2F3
    , chainEdge 1 TauEdge.F2F4
    , chainEdge 1 TauEdge.B4
    , chainEdge 1 TauEdge.F4F5
    , chainEdge 2 TauEdge.F1F0
    , chainEdge 1 TauEdge.B6
    ]

def tttLargeFiber4Block0Rows : List TripleComponentParentRow :=
  [ tttLargeFiber4Row0
  , tttLargeFiber4Row1
  , tttLargeFiber4Row2
  , tttLargeFiber4Row3
  , tttLargeFiber4Row4
  , tttLargeFiber4Row5
  , tttLargeFiber4Row6
  , tttLargeFiber4Row7
  , tttLargeFiber4Row8
  , tttLargeFiber4Row9
  , tttLargeFiber4Row10
  , tttLargeFiber4Row11
  , tttLargeFiber4Row12
  , tttLargeFiber4Row13
  , tttLargeFiber4Row14
  , tttLargeFiber4Row15
  , tttLargeFiber4Row16
  , tttLargeFiber4Row17
  , tttLargeFiber4Row18
  , tttLargeFiber4Row19
  , tttLargeFiber4Row20
  , tttLargeFiber4Row21
  , tttLargeFiber4Row22
  , tttLargeFiber4Row23
  , tttLargeFiber4Row24
  , tttLargeFiber4Row25
  , tttLargeFiber4Row26
  , tttLargeFiber4Row27
  , tttLargeFiber4Row28
  , tttLargeFiber4Row29
  , tttLargeFiber4Row30
  , tttLargeFiber4Row31
  , tttLargeFiber4Row32
  , tttLargeFiber4Row33
  , tttLargeFiber4Row34
  , tttLargeFiber4Row35
  , tttLargeFiber4Row36
  , tttLargeFiber4Row37
  , tttLargeFiber4Row38
  , tttLargeFiber4Row39
  , tttLargeFiber4Row40
  , tttLargeFiber4Row41
  , tttLargeFiber4Row42
  , tttLargeFiber4Row43
  , tttLargeFiber4Row44
  , tttLargeFiber4Row45
  , tttLargeFiber4Row46
  , tttLargeFiber4Row47
  , tttLargeFiber4Row48
  , tttLargeFiber4Row49
  , tttLargeFiber4Row50
  , tttLargeFiber4Row51
  , tttLargeFiber4Row52
  , tttLargeFiber4Row53
  , tttLargeFiber4Row54
  , tttLargeFiber4Row55
  , tttLargeFiber4Row56
  , tttLargeFiber4Row57
  , tttLargeFiber4Row58
  , tttLargeFiber4Row59
  , tttLargeFiber4Row60
  , tttLargeFiber4Row61
  , tttLargeFiber4Row62
  , tttLargeFiber4Row63
  ]

def tttLargeFiber4Block0SourcesCheck : Bool :=
  (tttLargeFiber4Block0Rows.map fun row => row.source) ==
    tttLargeFiber4Block0Sources

theorem tttLargeFiber4Block0SourcesCheck_ok :
    tttLargeFiber4Block0SourcesCheck = true := by
  decide

def tttLargeFiber4Block0RowCheck (i : Nat) : Bool :=
  tripleComponentRowValid tttLargeFiber4Key tttLargeFiber4Expected
    (listGetD tttLargeFiber4Block0Rows i default)

def tttLargeFiber4Block0ParentMapCheck (i : Nat) : Bool :=
  let row := listGetD tttLargeFiber4Block0Rows i default
  row.parent == tttLargeFiber4ParentOf row.source

def tttLargeFiber4Block0ParentConvergesCheck (i : Nat) : Bool :=
  tttLargeFiber4ParentConvergesCheck i

theorem tttLargeFiber4Block0Row_0_ok :
    tttLargeFiber4Block0RowCheck 0 = true := by
  decide
theorem tttLargeFiber4Block0Row_1_ok :
    tttLargeFiber4Block0RowCheck 1 = true := by
  decide
theorem tttLargeFiber4Block0Row_2_ok :
    tttLargeFiber4Block0RowCheck 2 = true := by
  decide
theorem tttLargeFiber4Block0Row_3_ok :
    tttLargeFiber4Block0RowCheck 3 = true := by
  decide
theorem tttLargeFiber4Block0Row_4_ok :
    tttLargeFiber4Block0RowCheck 4 = true := by
  decide
theorem tttLargeFiber4Block0Row_5_ok :
    tttLargeFiber4Block0RowCheck 5 = true := by
  decide
theorem tttLargeFiber4Block0Row_6_ok :
    tttLargeFiber4Block0RowCheck 6 = true := by
  decide
theorem tttLargeFiber4Block0Row_7_ok :
    tttLargeFiber4Block0RowCheck 7 = true := by
  decide
theorem tttLargeFiber4Block0Row_8_ok :
    tttLargeFiber4Block0RowCheck 8 = true := by
  decide
theorem tttLargeFiber4Block0Row_9_ok :
    tttLargeFiber4Block0RowCheck 9 = true := by
  decide
theorem tttLargeFiber4Block0Row_10_ok :
    tttLargeFiber4Block0RowCheck 10 = true := by
  decide
theorem tttLargeFiber4Block0Row_11_ok :
    tttLargeFiber4Block0RowCheck 11 = true := by
  decide
theorem tttLargeFiber4Block0Row_12_ok :
    tttLargeFiber4Block0RowCheck 12 = true := by
  decide
theorem tttLargeFiber4Block0Row_13_ok :
    tttLargeFiber4Block0RowCheck 13 = true := by
  decide
theorem tttLargeFiber4Block0Row_14_ok :
    tttLargeFiber4Block0RowCheck 14 = true := by
  decide
theorem tttLargeFiber4Block0Row_15_ok :
    tttLargeFiber4Block0RowCheck 15 = true := by
  decide
theorem tttLargeFiber4Block0Row_16_ok :
    tttLargeFiber4Block0RowCheck 16 = true := by
  decide
theorem tttLargeFiber4Block0Row_17_ok :
    tttLargeFiber4Block0RowCheck 17 = true := by
  decide
theorem tttLargeFiber4Block0Row_18_ok :
    tttLargeFiber4Block0RowCheck 18 = true := by
  decide
theorem tttLargeFiber4Block0Row_19_ok :
    tttLargeFiber4Block0RowCheck 19 = true := by
  decide
theorem tttLargeFiber4Block0Row_20_ok :
    tttLargeFiber4Block0RowCheck 20 = true := by
  decide
theorem tttLargeFiber4Block0Row_21_ok :
    tttLargeFiber4Block0RowCheck 21 = true := by
  decide
theorem tttLargeFiber4Block0Row_22_ok :
    tttLargeFiber4Block0RowCheck 22 = true := by
  decide
theorem tttLargeFiber4Block0Row_23_ok :
    tttLargeFiber4Block0RowCheck 23 = true := by
  decide
theorem tttLargeFiber4Block0Row_24_ok :
    tttLargeFiber4Block0RowCheck 24 = true := by
  decide
theorem tttLargeFiber4Block0Row_25_ok :
    tttLargeFiber4Block0RowCheck 25 = true := by
  decide
theorem tttLargeFiber4Block0Row_26_ok :
    tttLargeFiber4Block0RowCheck 26 = true := by
  decide
theorem tttLargeFiber4Block0Row_27_ok :
    tttLargeFiber4Block0RowCheck 27 = true := by
  decide
theorem tttLargeFiber4Block0Row_28_ok :
    tttLargeFiber4Block0RowCheck 28 = true := by
  decide
theorem tttLargeFiber4Block0Row_29_ok :
    tttLargeFiber4Block0RowCheck 29 = true := by
  decide
theorem tttLargeFiber4Block0Row_30_ok :
    tttLargeFiber4Block0RowCheck 30 = true := by
  decide
theorem tttLargeFiber4Block0Row_31_ok :
    tttLargeFiber4Block0RowCheck 31 = true := by
  decide
theorem tttLargeFiber4Block0Row_32_ok :
    tttLargeFiber4Block0RowCheck 32 = true := by
  decide
theorem tttLargeFiber4Block0Row_33_ok :
    tttLargeFiber4Block0RowCheck 33 = true := by
  decide
theorem tttLargeFiber4Block0Row_34_ok :
    tttLargeFiber4Block0RowCheck 34 = true := by
  decide
theorem tttLargeFiber4Block0Row_35_ok :
    tttLargeFiber4Block0RowCheck 35 = true := by
  decide
theorem tttLargeFiber4Block0Row_36_ok :
    tttLargeFiber4Block0RowCheck 36 = true := by
  decide
theorem tttLargeFiber4Block0Row_37_ok :
    tttLargeFiber4Block0RowCheck 37 = true := by
  decide
theorem tttLargeFiber4Block0Row_38_ok :
    tttLargeFiber4Block0RowCheck 38 = true := by
  decide
theorem tttLargeFiber4Block0Row_39_ok :
    tttLargeFiber4Block0RowCheck 39 = true := by
  decide
theorem tttLargeFiber4Block0Row_40_ok :
    tttLargeFiber4Block0RowCheck 40 = true := by
  decide
theorem tttLargeFiber4Block0Row_41_ok :
    tttLargeFiber4Block0RowCheck 41 = true := by
  decide
theorem tttLargeFiber4Block0Row_42_ok :
    tttLargeFiber4Block0RowCheck 42 = true := by
  decide
theorem tttLargeFiber4Block0Row_43_ok :
    tttLargeFiber4Block0RowCheck 43 = true := by
  decide
theorem tttLargeFiber4Block0Row_44_ok :
    tttLargeFiber4Block0RowCheck 44 = true := by
  decide
theorem tttLargeFiber4Block0Row_45_ok :
    tttLargeFiber4Block0RowCheck 45 = true := by
  decide
theorem tttLargeFiber4Block0Row_46_ok :
    tttLargeFiber4Block0RowCheck 46 = true := by
  decide
theorem tttLargeFiber4Block0Row_47_ok :
    tttLargeFiber4Block0RowCheck 47 = true := by
  decide
theorem tttLargeFiber4Block0Row_48_ok :
    tttLargeFiber4Block0RowCheck 48 = true := by
  decide
theorem tttLargeFiber4Block0Row_49_ok :
    tttLargeFiber4Block0RowCheck 49 = true := by
  decide
theorem tttLargeFiber4Block0Row_50_ok :
    tttLargeFiber4Block0RowCheck 50 = true := by
  decide
theorem tttLargeFiber4Block0Row_51_ok :
    tttLargeFiber4Block0RowCheck 51 = true := by
  decide
theorem tttLargeFiber4Block0Row_52_ok :
    tttLargeFiber4Block0RowCheck 52 = true := by
  decide
theorem tttLargeFiber4Block0Row_53_ok :
    tttLargeFiber4Block0RowCheck 53 = true := by
  decide
theorem tttLargeFiber4Block0Row_54_ok :
    tttLargeFiber4Block0RowCheck 54 = true := by
  decide
theorem tttLargeFiber4Block0Row_55_ok :
    tttLargeFiber4Block0RowCheck 55 = true := by
  decide
theorem tttLargeFiber4Block0Row_56_ok :
    tttLargeFiber4Block0RowCheck 56 = true := by
  decide
theorem tttLargeFiber4Block0Row_57_ok :
    tttLargeFiber4Block0RowCheck 57 = true := by
  decide
theorem tttLargeFiber4Block0Row_58_ok :
    tttLargeFiber4Block0RowCheck 58 = true := by
  decide
theorem tttLargeFiber4Block0Row_59_ok :
    tttLargeFiber4Block0RowCheck 59 = true := by
  decide
theorem tttLargeFiber4Block0Row_60_ok :
    tttLargeFiber4Block0RowCheck 60 = true := by
  decide
theorem tttLargeFiber4Block0Row_61_ok :
    tttLargeFiber4Block0RowCheck 61 = true := by
  decide
theorem tttLargeFiber4Block0Row_62_ok :
    tttLargeFiber4Block0RowCheck 62 = true := by
  decide
theorem tttLargeFiber4Block0Row_63_ok :
    tttLargeFiber4Block0RowCheck 63 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_0_ok :
    tttLargeFiber4Block0ParentMapCheck 0 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_1_ok :
    tttLargeFiber4Block0ParentMapCheck 1 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_2_ok :
    tttLargeFiber4Block0ParentMapCheck 2 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_3_ok :
    tttLargeFiber4Block0ParentMapCheck 3 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_4_ok :
    tttLargeFiber4Block0ParentMapCheck 4 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_5_ok :
    tttLargeFiber4Block0ParentMapCheck 5 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_6_ok :
    tttLargeFiber4Block0ParentMapCheck 6 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_7_ok :
    tttLargeFiber4Block0ParentMapCheck 7 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_8_ok :
    tttLargeFiber4Block0ParentMapCheck 8 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_9_ok :
    tttLargeFiber4Block0ParentMapCheck 9 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_10_ok :
    tttLargeFiber4Block0ParentMapCheck 10 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_11_ok :
    tttLargeFiber4Block0ParentMapCheck 11 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_12_ok :
    tttLargeFiber4Block0ParentMapCheck 12 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_13_ok :
    tttLargeFiber4Block0ParentMapCheck 13 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_14_ok :
    tttLargeFiber4Block0ParentMapCheck 14 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_15_ok :
    tttLargeFiber4Block0ParentMapCheck 15 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_16_ok :
    tttLargeFiber4Block0ParentMapCheck 16 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_17_ok :
    tttLargeFiber4Block0ParentMapCheck 17 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_18_ok :
    tttLargeFiber4Block0ParentMapCheck 18 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_19_ok :
    tttLargeFiber4Block0ParentMapCheck 19 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_20_ok :
    tttLargeFiber4Block0ParentMapCheck 20 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_21_ok :
    tttLargeFiber4Block0ParentMapCheck 21 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_22_ok :
    tttLargeFiber4Block0ParentMapCheck 22 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_23_ok :
    tttLargeFiber4Block0ParentMapCheck 23 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_24_ok :
    tttLargeFiber4Block0ParentMapCheck 24 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_25_ok :
    tttLargeFiber4Block0ParentMapCheck 25 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_26_ok :
    tttLargeFiber4Block0ParentMapCheck 26 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_27_ok :
    tttLargeFiber4Block0ParentMapCheck 27 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_28_ok :
    tttLargeFiber4Block0ParentMapCheck 28 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_29_ok :
    tttLargeFiber4Block0ParentMapCheck 29 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_30_ok :
    tttLargeFiber4Block0ParentMapCheck 30 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_31_ok :
    tttLargeFiber4Block0ParentMapCheck 31 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_32_ok :
    tttLargeFiber4Block0ParentMapCheck 32 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_33_ok :
    tttLargeFiber4Block0ParentMapCheck 33 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_34_ok :
    tttLargeFiber4Block0ParentMapCheck 34 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_35_ok :
    tttLargeFiber4Block0ParentMapCheck 35 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_36_ok :
    tttLargeFiber4Block0ParentMapCheck 36 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_37_ok :
    tttLargeFiber4Block0ParentMapCheck 37 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_38_ok :
    tttLargeFiber4Block0ParentMapCheck 38 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_39_ok :
    tttLargeFiber4Block0ParentMapCheck 39 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_40_ok :
    tttLargeFiber4Block0ParentMapCheck 40 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_41_ok :
    tttLargeFiber4Block0ParentMapCheck 41 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_42_ok :
    tttLargeFiber4Block0ParentMapCheck 42 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_43_ok :
    tttLargeFiber4Block0ParentMapCheck 43 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_44_ok :
    tttLargeFiber4Block0ParentMapCheck 44 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_45_ok :
    tttLargeFiber4Block0ParentMapCheck 45 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_46_ok :
    tttLargeFiber4Block0ParentMapCheck 46 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_47_ok :
    tttLargeFiber4Block0ParentMapCheck 47 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_48_ok :
    tttLargeFiber4Block0ParentMapCheck 48 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_49_ok :
    tttLargeFiber4Block0ParentMapCheck 49 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_50_ok :
    tttLargeFiber4Block0ParentMapCheck 50 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_51_ok :
    tttLargeFiber4Block0ParentMapCheck 51 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_52_ok :
    tttLargeFiber4Block0ParentMapCheck 52 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_53_ok :
    tttLargeFiber4Block0ParentMapCheck 53 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_54_ok :
    tttLargeFiber4Block0ParentMapCheck 54 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_55_ok :
    tttLargeFiber4Block0ParentMapCheck 55 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_56_ok :
    tttLargeFiber4Block0ParentMapCheck 56 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_57_ok :
    tttLargeFiber4Block0ParentMapCheck 57 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_58_ok :
    tttLargeFiber4Block0ParentMapCheck 58 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_59_ok :
    tttLargeFiber4Block0ParentMapCheck 59 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_60_ok :
    tttLargeFiber4Block0ParentMapCheck 60 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_61_ok :
    tttLargeFiber4Block0ParentMapCheck 61 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_62_ok :
    tttLargeFiber4Block0ParentMapCheck 62 = true := by
  decide
theorem tttLargeFiber4Block0ParentMap_63_ok :
    tttLargeFiber4Block0ParentMapCheck 63 = true := by
  decide
theorem tttLargeFiber4Block0Parent_0_ok :
    tttLargeFiber4Block0ParentConvergesCheck 0 = true := by
  decide
theorem tttLargeFiber4Block0Parent_1_ok :
    tttLargeFiber4Block0ParentConvergesCheck 1 = true := by
  decide
theorem tttLargeFiber4Block0Parent_2_ok :
    tttLargeFiber4Block0ParentConvergesCheck 2 = true := by
  decide
theorem tttLargeFiber4Block0Parent_3_ok :
    tttLargeFiber4Block0ParentConvergesCheck 3 = true := by
  decide
theorem tttLargeFiber4Block0Parent_4_ok :
    tttLargeFiber4Block0ParentConvergesCheck 4 = true := by
  decide
theorem tttLargeFiber4Block0Parent_5_ok :
    tttLargeFiber4Block0ParentConvergesCheck 5 = true := by
  decide
theorem tttLargeFiber4Block0Parent_6_ok :
    tttLargeFiber4Block0ParentConvergesCheck 6 = true := by
  decide
theorem tttLargeFiber4Block0Parent_7_ok :
    tttLargeFiber4Block0ParentConvergesCheck 7 = true := by
  decide
theorem tttLargeFiber4Block0Parent_8_ok :
    tttLargeFiber4Block0ParentConvergesCheck 8 = true := by
  decide
theorem tttLargeFiber4Block0Parent_9_ok :
    tttLargeFiber4Block0ParentConvergesCheck 9 = true := by
  decide
theorem tttLargeFiber4Block0Parent_10_ok :
    tttLargeFiber4Block0ParentConvergesCheck 10 = true := by
  decide
theorem tttLargeFiber4Block0Parent_11_ok :
    tttLargeFiber4Block0ParentConvergesCheck 11 = true := by
  decide
theorem tttLargeFiber4Block0Parent_12_ok :
    tttLargeFiber4Block0ParentConvergesCheck 12 = true := by
  decide
theorem tttLargeFiber4Block0Parent_13_ok :
    tttLargeFiber4Block0ParentConvergesCheck 13 = true := by
  decide
theorem tttLargeFiber4Block0Parent_14_ok :
    tttLargeFiber4Block0ParentConvergesCheck 14 = true := by
  decide
theorem tttLargeFiber4Block0Parent_15_ok :
    tttLargeFiber4Block0ParentConvergesCheck 15 = true := by
  decide
theorem tttLargeFiber4Block0Parent_16_ok :
    tttLargeFiber4Block0ParentConvergesCheck 16 = true := by
  decide
theorem tttLargeFiber4Block0Parent_17_ok :
    tttLargeFiber4Block0ParentConvergesCheck 17 = true := by
  decide
theorem tttLargeFiber4Block0Parent_18_ok :
    tttLargeFiber4Block0ParentConvergesCheck 18 = true := by
  decide
theorem tttLargeFiber4Block0Parent_19_ok :
    tttLargeFiber4Block0ParentConvergesCheck 19 = true := by
  decide
theorem tttLargeFiber4Block0Parent_20_ok :
    tttLargeFiber4Block0ParentConvergesCheck 20 = true := by
  decide
theorem tttLargeFiber4Block0Parent_21_ok :
    tttLargeFiber4Block0ParentConvergesCheck 21 = true := by
  decide
theorem tttLargeFiber4Block0Parent_22_ok :
    tttLargeFiber4Block0ParentConvergesCheck 22 = true := by
  decide
theorem tttLargeFiber4Block0Parent_23_ok :
    tttLargeFiber4Block0ParentConvergesCheck 23 = true := by
  decide
theorem tttLargeFiber4Block0Parent_24_ok :
    tttLargeFiber4Block0ParentConvergesCheck 24 = true := by
  decide
theorem tttLargeFiber4Block0Parent_25_ok :
    tttLargeFiber4Block0ParentConvergesCheck 25 = true := by
  decide
theorem tttLargeFiber4Block0Parent_26_ok :
    tttLargeFiber4Block0ParentConvergesCheck 26 = true := by
  decide
theorem tttLargeFiber4Block0Parent_27_ok :
    tttLargeFiber4Block0ParentConvergesCheck 27 = true := by
  decide
theorem tttLargeFiber4Block0Parent_28_ok :
    tttLargeFiber4Block0ParentConvergesCheck 28 = true := by
  decide
theorem tttLargeFiber4Block0Parent_29_ok :
    tttLargeFiber4Block0ParentConvergesCheck 29 = true := by
  decide
theorem tttLargeFiber4Block0Parent_30_ok :
    tttLargeFiber4Block0ParentConvergesCheck 30 = true := by
  decide
theorem tttLargeFiber4Block0Parent_31_ok :
    tttLargeFiber4Block0ParentConvergesCheck 31 = true := by
  decide
theorem tttLargeFiber4Block0Parent_32_ok :
    tttLargeFiber4Block0ParentConvergesCheck 32 = true := by
  decide
theorem tttLargeFiber4Block0Parent_33_ok :
    tttLargeFiber4Block0ParentConvergesCheck 33 = true := by
  decide
theorem tttLargeFiber4Block0Parent_34_ok :
    tttLargeFiber4Block0ParentConvergesCheck 34 = true := by
  decide
theorem tttLargeFiber4Block0Parent_35_ok :
    tttLargeFiber4Block0ParentConvergesCheck 35 = true := by
  decide
theorem tttLargeFiber4Block0Parent_36_ok :
    tttLargeFiber4Block0ParentConvergesCheck 36 = true := by
  decide
theorem tttLargeFiber4Block0Parent_37_ok :
    tttLargeFiber4Block0ParentConvergesCheck 37 = true := by
  decide
theorem tttLargeFiber4Block0Parent_38_ok :
    tttLargeFiber4Block0ParentConvergesCheck 38 = true := by
  decide
theorem tttLargeFiber4Block0Parent_39_ok :
    tttLargeFiber4Block0ParentConvergesCheck 39 = true := by
  decide
theorem tttLargeFiber4Block0Parent_40_ok :
    tttLargeFiber4Block0ParentConvergesCheck 40 = true := by
  decide
theorem tttLargeFiber4Block0Parent_41_ok :
    tttLargeFiber4Block0ParentConvergesCheck 41 = true := by
  decide
theorem tttLargeFiber4Block0Parent_42_ok :
    tttLargeFiber4Block0ParentConvergesCheck 42 = true := by
  decide
theorem tttLargeFiber4Block0Parent_43_ok :
    tttLargeFiber4Block0ParentConvergesCheck 43 = true := by
  decide
theorem tttLargeFiber4Block0Parent_44_ok :
    tttLargeFiber4Block0ParentConvergesCheck 44 = true := by
  decide
theorem tttLargeFiber4Block0Parent_45_ok :
    tttLargeFiber4Block0ParentConvergesCheck 45 = true := by
  decide
theorem tttLargeFiber4Block0Parent_46_ok :
    tttLargeFiber4Block0ParentConvergesCheck 46 = true := by
  decide
theorem tttLargeFiber4Block0Parent_47_ok :
    tttLargeFiber4Block0ParentConvergesCheck 47 = true := by
  decide
theorem tttLargeFiber4Block0Parent_48_ok :
    tttLargeFiber4Block0ParentConvergesCheck 48 = true := by
  decide
theorem tttLargeFiber4Block0Parent_49_ok :
    tttLargeFiber4Block0ParentConvergesCheck 49 = true := by
  decide
theorem tttLargeFiber4Block0Parent_50_ok :
    tttLargeFiber4Block0ParentConvergesCheck 50 = true := by
  decide
theorem tttLargeFiber4Block0Parent_51_ok :
    tttLargeFiber4Block0ParentConvergesCheck 51 = true := by
  decide
theorem tttLargeFiber4Block0Parent_52_ok :
    tttLargeFiber4Block0ParentConvergesCheck 52 = true := by
  decide
theorem tttLargeFiber4Block0Parent_53_ok :
    tttLargeFiber4Block0ParentConvergesCheck 53 = true := by
  decide
theorem tttLargeFiber4Block0Parent_54_ok :
    tttLargeFiber4Block0ParentConvergesCheck 54 = true := by
  decide
theorem tttLargeFiber4Block0Parent_55_ok :
    tttLargeFiber4Block0ParentConvergesCheck 55 = true := by
  decide
theorem tttLargeFiber4Block0Parent_56_ok :
    tttLargeFiber4Block0ParentConvergesCheck 56 = true := by
  decide
theorem tttLargeFiber4Block0Parent_57_ok :
    tttLargeFiber4Block0ParentConvergesCheck 57 = true := by
  decide
theorem tttLargeFiber4Block0Parent_58_ok :
    tttLargeFiber4Block0ParentConvergesCheck 58 = true := by
  decide
theorem tttLargeFiber4Block0Parent_59_ok :
    tttLargeFiber4Block0ParentConvergesCheck 59 = true := by
  decide
theorem tttLargeFiber4Block0Parent_60_ok :
    tttLargeFiber4Block0ParentConvergesCheck 60 = true := by
  decide
theorem tttLargeFiber4Block0Parent_61_ok :
    tttLargeFiber4Block0ParentConvergesCheck 61 = true := by
  decide
theorem tttLargeFiber4Block0Parent_62_ok :
    tttLargeFiber4Block0ParentConvergesCheck 62 = true := by
  decide
theorem tttLargeFiber4Block0Parent_63_ok :
    tttLargeFiber4Block0ParentConvergesCheck 63 = true := by
  decide

def tttLargeFiber4Block0RowsAudit : Bool :=
  tttLargeFiber4Block0RowCheck 0
    && tttLargeFiber4Block0RowCheck 1
    && tttLargeFiber4Block0RowCheck 2
    && tttLargeFiber4Block0RowCheck 3
    && tttLargeFiber4Block0RowCheck 4
    && tttLargeFiber4Block0RowCheck 5
    && tttLargeFiber4Block0RowCheck 6
    && tttLargeFiber4Block0RowCheck 7
    && tttLargeFiber4Block0RowCheck 8
    && tttLargeFiber4Block0RowCheck 9
    && tttLargeFiber4Block0RowCheck 10
    && tttLargeFiber4Block0RowCheck 11
    && tttLargeFiber4Block0RowCheck 12
    && tttLargeFiber4Block0RowCheck 13
    && tttLargeFiber4Block0RowCheck 14
    && tttLargeFiber4Block0RowCheck 15
    && tttLargeFiber4Block0RowCheck 16
    && tttLargeFiber4Block0RowCheck 17
    && tttLargeFiber4Block0RowCheck 18
    && tttLargeFiber4Block0RowCheck 19
    && tttLargeFiber4Block0RowCheck 20
    && tttLargeFiber4Block0RowCheck 21
    && tttLargeFiber4Block0RowCheck 22
    && tttLargeFiber4Block0RowCheck 23
    && tttLargeFiber4Block0RowCheck 24
    && tttLargeFiber4Block0RowCheck 25
    && tttLargeFiber4Block0RowCheck 26
    && tttLargeFiber4Block0RowCheck 27
    && tttLargeFiber4Block0RowCheck 28
    && tttLargeFiber4Block0RowCheck 29
    && tttLargeFiber4Block0RowCheck 30
    && tttLargeFiber4Block0RowCheck 31
    && tttLargeFiber4Block0RowCheck 32
    && tttLargeFiber4Block0RowCheck 33
    && tttLargeFiber4Block0RowCheck 34
    && tttLargeFiber4Block0RowCheck 35
    && tttLargeFiber4Block0RowCheck 36
    && tttLargeFiber4Block0RowCheck 37
    && tttLargeFiber4Block0RowCheck 38
    && tttLargeFiber4Block0RowCheck 39
    && tttLargeFiber4Block0RowCheck 40
    && tttLargeFiber4Block0RowCheck 41
    && tttLargeFiber4Block0RowCheck 42
    && tttLargeFiber4Block0RowCheck 43
    && tttLargeFiber4Block0RowCheck 44
    && tttLargeFiber4Block0RowCheck 45
    && tttLargeFiber4Block0RowCheck 46
    && tttLargeFiber4Block0RowCheck 47
    && tttLargeFiber4Block0RowCheck 48
    && tttLargeFiber4Block0RowCheck 49
    && tttLargeFiber4Block0RowCheck 50
    && tttLargeFiber4Block0RowCheck 51
    && tttLargeFiber4Block0RowCheck 52
    && tttLargeFiber4Block0RowCheck 53
    && tttLargeFiber4Block0RowCheck 54
    && tttLargeFiber4Block0RowCheck 55
    && tttLargeFiber4Block0RowCheck 56
    && tttLargeFiber4Block0RowCheck 57
    && tttLargeFiber4Block0RowCheck 58
    && tttLargeFiber4Block0RowCheck 59
    && tttLargeFiber4Block0RowCheck 60
    && tttLargeFiber4Block0RowCheck 61
    && tttLargeFiber4Block0RowCheck 62
    && tttLargeFiber4Block0RowCheck 63

theorem tttLargeFiber4Block0RowsAudit_ok :
    tttLargeFiber4Block0RowsAudit = true := by
  simp [tttLargeFiber4Block0RowsAudit,
    tttLargeFiber4Block0Row_0_ok,
    tttLargeFiber4Block0Row_1_ok,
    tttLargeFiber4Block0Row_2_ok,
    tttLargeFiber4Block0Row_3_ok,
    tttLargeFiber4Block0Row_4_ok,
    tttLargeFiber4Block0Row_5_ok,
    tttLargeFiber4Block0Row_6_ok,
    tttLargeFiber4Block0Row_7_ok,
    tttLargeFiber4Block0Row_8_ok,
    tttLargeFiber4Block0Row_9_ok,
    tttLargeFiber4Block0Row_10_ok,
    tttLargeFiber4Block0Row_11_ok,
    tttLargeFiber4Block0Row_12_ok,
    tttLargeFiber4Block0Row_13_ok,
    tttLargeFiber4Block0Row_14_ok,
    tttLargeFiber4Block0Row_15_ok,
    tttLargeFiber4Block0Row_16_ok,
    tttLargeFiber4Block0Row_17_ok,
    tttLargeFiber4Block0Row_18_ok,
    tttLargeFiber4Block0Row_19_ok,
    tttLargeFiber4Block0Row_20_ok,
    tttLargeFiber4Block0Row_21_ok,
    tttLargeFiber4Block0Row_22_ok,
    tttLargeFiber4Block0Row_23_ok,
    tttLargeFiber4Block0Row_24_ok,
    tttLargeFiber4Block0Row_25_ok,
    tttLargeFiber4Block0Row_26_ok,
    tttLargeFiber4Block0Row_27_ok,
    tttLargeFiber4Block0Row_28_ok,
    tttLargeFiber4Block0Row_29_ok,
    tttLargeFiber4Block0Row_30_ok,
    tttLargeFiber4Block0Row_31_ok,
    tttLargeFiber4Block0Row_32_ok,
    tttLargeFiber4Block0Row_33_ok,
    tttLargeFiber4Block0Row_34_ok,
    tttLargeFiber4Block0Row_35_ok,
    tttLargeFiber4Block0Row_36_ok,
    tttLargeFiber4Block0Row_37_ok,
    tttLargeFiber4Block0Row_38_ok,
    tttLargeFiber4Block0Row_39_ok,
    tttLargeFiber4Block0Row_40_ok,
    tttLargeFiber4Block0Row_41_ok,
    tttLargeFiber4Block0Row_42_ok,
    tttLargeFiber4Block0Row_43_ok,
    tttLargeFiber4Block0Row_44_ok,
    tttLargeFiber4Block0Row_45_ok,
    tttLargeFiber4Block0Row_46_ok,
    tttLargeFiber4Block0Row_47_ok,
    tttLargeFiber4Block0Row_48_ok,
    tttLargeFiber4Block0Row_49_ok,
    tttLargeFiber4Block0Row_50_ok,
    tttLargeFiber4Block0Row_51_ok,
    tttLargeFiber4Block0Row_52_ok,
    tttLargeFiber4Block0Row_53_ok,
    tttLargeFiber4Block0Row_54_ok,
    tttLargeFiber4Block0Row_55_ok,
    tttLargeFiber4Block0Row_56_ok,
    tttLargeFiber4Block0Row_57_ok,
    tttLargeFiber4Block0Row_58_ok,
    tttLargeFiber4Block0Row_59_ok,
    tttLargeFiber4Block0Row_60_ok,
    tttLargeFiber4Block0Row_61_ok,
    tttLargeFiber4Block0Row_62_ok,
    tttLargeFiber4Block0Row_63_ok]

def tttLargeFiber4Block0ParentMapAudit : Bool :=
  tttLargeFiber4Block0ParentMapCheck 0
    && tttLargeFiber4Block0ParentMapCheck 1
    && tttLargeFiber4Block0ParentMapCheck 2
    && tttLargeFiber4Block0ParentMapCheck 3
    && tttLargeFiber4Block0ParentMapCheck 4
    && tttLargeFiber4Block0ParentMapCheck 5
    && tttLargeFiber4Block0ParentMapCheck 6
    && tttLargeFiber4Block0ParentMapCheck 7
    && tttLargeFiber4Block0ParentMapCheck 8
    && tttLargeFiber4Block0ParentMapCheck 9
    && tttLargeFiber4Block0ParentMapCheck 10
    && tttLargeFiber4Block0ParentMapCheck 11
    && tttLargeFiber4Block0ParentMapCheck 12
    && tttLargeFiber4Block0ParentMapCheck 13
    && tttLargeFiber4Block0ParentMapCheck 14
    && tttLargeFiber4Block0ParentMapCheck 15
    && tttLargeFiber4Block0ParentMapCheck 16
    && tttLargeFiber4Block0ParentMapCheck 17
    && tttLargeFiber4Block0ParentMapCheck 18
    && tttLargeFiber4Block0ParentMapCheck 19
    && tttLargeFiber4Block0ParentMapCheck 20
    && tttLargeFiber4Block0ParentMapCheck 21
    && tttLargeFiber4Block0ParentMapCheck 22
    && tttLargeFiber4Block0ParentMapCheck 23
    && tttLargeFiber4Block0ParentMapCheck 24
    && tttLargeFiber4Block0ParentMapCheck 25
    && tttLargeFiber4Block0ParentMapCheck 26
    && tttLargeFiber4Block0ParentMapCheck 27
    && tttLargeFiber4Block0ParentMapCheck 28
    && tttLargeFiber4Block0ParentMapCheck 29
    && tttLargeFiber4Block0ParentMapCheck 30
    && tttLargeFiber4Block0ParentMapCheck 31
    && tttLargeFiber4Block0ParentMapCheck 32
    && tttLargeFiber4Block0ParentMapCheck 33
    && tttLargeFiber4Block0ParentMapCheck 34
    && tttLargeFiber4Block0ParentMapCheck 35
    && tttLargeFiber4Block0ParentMapCheck 36
    && tttLargeFiber4Block0ParentMapCheck 37
    && tttLargeFiber4Block0ParentMapCheck 38
    && tttLargeFiber4Block0ParentMapCheck 39
    && tttLargeFiber4Block0ParentMapCheck 40
    && tttLargeFiber4Block0ParentMapCheck 41
    && tttLargeFiber4Block0ParentMapCheck 42
    && tttLargeFiber4Block0ParentMapCheck 43
    && tttLargeFiber4Block0ParentMapCheck 44
    && tttLargeFiber4Block0ParentMapCheck 45
    && tttLargeFiber4Block0ParentMapCheck 46
    && tttLargeFiber4Block0ParentMapCheck 47
    && tttLargeFiber4Block0ParentMapCheck 48
    && tttLargeFiber4Block0ParentMapCheck 49
    && tttLargeFiber4Block0ParentMapCheck 50
    && tttLargeFiber4Block0ParentMapCheck 51
    && tttLargeFiber4Block0ParentMapCheck 52
    && tttLargeFiber4Block0ParentMapCheck 53
    && tttLargeFiber4Block0ParentMapCheck 54
    && tttLargeFiber4Block0ParentMapCheck 55
    && tttLargeFiber4Block0ParentMapCheck 56
    && tttLargeFiber4Block0ParentMapCheck 57
    && tttLargeFiber4Block0ParentMapCheck 58
    && tttLargeFiber4Block0ParentMapCheck 59
    && tttLargeFiber4Block0ParentMapCheck 60
    && tttLargeFiber4Block0ParentMapCheck 61
    && tttLargeFiber4Block0ParentMapCheck 62
    && tttLargeFiber4Block0ParentMapCheck 63

theorem tttLargeFiber4Block0ParentMapAudit_ok :
    tttLargeFiber4Block0ParentMapAudit = true := by
  simp [tttLargeFiber4Block0ParentMapAudit,
    tttLargeFiber4Block0ParentMap_0_ok,
    tttLargeFiber4Block0ParentMap_1_ok,
    tttLargeFiber4Block0ParentMap_2_ok,
    tttLargeFiber4Block0ParentMap_3_ok,
    tttLargeFiber4Block0ParentMap_4_ok,
    tttLargeFiber4Block0ParentMap_5_ok,
    tttLargeFiber4Block0ParentMap_6_ok,
    tttLargeFiber4Block0ParentMap_7_ok,
    tttLargeFiber4Block0ParentMap_8_ok,
    tttLargeFiber4Block0ParentMap_9_ok,
    tttLargeFiber4Block0ParentMap_10_ok,
    tttLargeFiber4Block0ParentMap_11_ok,
    tttLargeFiber4Block0ParentMap_12_ok,
    tttLargeFiber4Block0ParentMap_13_ok,
    tttLargeFiber4Block0ParentMap_14_ok,
    tttLargeFiber4Block0ParentMap_15_ok,
    tttLargeFiber4Block0ParentMap_16_ok,
    tttLargeFiber4Block0ParentMap_17_ok,
    tttLargeFiber4Block0ParentMap_18_ok,
    tttLargeFiber4Block0ParentMap_19_ok,
    tttLargeFiber4Block0ParentMap_20_ok,
    tttLargeFiber4Block0ParentMap_21_ok,
    tttLargeFiber4Block0ParentMap_22_ok,
    tttLargeFiber4Block0ParentMap_23_ok,
    tttLargeFiber4Block0ParentMap_24_ok,
    tttLargeFiber4Block0ParentMap_25_ok,
    tttLargeFiber4Block0ParentMap_26_ok,
    tttLargeFiber4Block0ParentMap_27_ok,
    tttLargeFiber4Block0ParentMap_28_ok,
    tttLargeFiber4Block0ParentMap_29_ok,
    tttLargeFiber4Block0ParentMap_30_ok,
    tttLargeFiber4Block0ParentMap_31_ok,
    tttLargeFiber4Block0ParentMap_32_ok,
    tttLargeFiber4Block0ParentMap_33_ok,
    tttLargeFiber4Block0ParentMap_34_ok,
    tttLargeFiber4Block0ParentMap_35_ok,
    tttLargeFiber4Block0ParentMap_36_ok,
    tttLargeFiber4Block0ParentMap_37_ok,
    tttLargeFiber4Block0ParentMap_38_ok,
    tttLargeFiber4Block0ParentMap_39_ok,
    tttLargeFiber4Block0ParentMap_40_ok,
    tttLargeFiber4Block0ParentMap_41_ok,
    tttLargeFiber4Block0ParentMap_42_ok,
    tttLargeFiber4Block0ParentMap_43_ok,
    tttLargeFiber4Block0ParentMap_44_ok,
    tttLargeFiber4Block0ParentMap_45_ok,
    tttLargeFiber4Block0ParentMap_46_ok,
    tttLargeFiber4Block0ParentMap_47_ok,
    tttLargeFiber4Block0ParentMap_48_ok,
    tttLargeFiber4Block0ParentMap_49_ok,
    tttLargeFiber4Block0ParentMap_50_ok,
    tttLargeFiber4Block0ParentMap_51_ok,
    tttLargeFiber4Block0ParentMap_52_ok,
    tttLargeFiber4Block0ParentMap_53_ok,
    tttLargeFiber4Block0ParentMap_54_ok,
    tttLargeFiber4Block0ParentMap_55_ok,
    tttLargeFiber4Block0ParentMap_56_ok,
    tttLargeFiber4Block0ParentMap_57_ok,
    tttLargeFiber4Block0ParentMap_58_ok,
    tttLargeFiber4Block0ParentMap_59_ok,
    tttLargeFiber4Block0ParentMap_60_ok,
    tttLargeFiber4Block0ParentMap_61_ok,
    tttLargeFiber4Block0ParentMap_62_ok,
    tttLargeFiber4Block0ParentMap_63_ok]

def tttLargeFiber4Block0ParentsAudit : Bool :=
  tttLargeFiber4Block0ParentConvergesCheck 0
    && tttLargeFiber4Block0ParentConvergesCheck 1
    && tttLargeFiber4Block0ParentConvergesCheck 2
    && tttLargeFiber4Block0ParentConvergesCheck 3
    && tttLargeFiber4Block0ParentConvergesCheck 4
    && tttLargeFiber4Block0ParentConvergesCheck 5
    && tttLargeFiber4Block0ParentConvergesCheck 6
    && tttLargeFiber4Block0ParentConvergesCheck 7
    && tttLargeFiber4Block0ParentConvergesCheck 8
    && tttLargeFiber4Block0ParentConvergesCheck 9
    && tttLargeFiber4Block0ParentConvergesCheck 10
    && tttLargeFiber4Block0ParentConvergesCheck 11
    && tttLargeFiber4Block0ParentConvergesCheck 12
    && tttLargeFiber4Block0ParentConvergesCheck 13
    && tttLargeFiber4Block0ParentConvergesCheck 14
    && tttLargeFiber4Block0ParentConvergesCheck 15
    && tttLargeFiber4Block0ParentConvergesCheck 16
    && tttLargeFiber4Block0ParentConvergesCheck 17
    && tttLargeFiber4Block0ParentConvergesCheck 18
    && tttLargeFiber4Block0ParentConvergesCheck 19
    && tttLargeFiber4Block0ParentConvergesCheck 20
    && tttLargeFiber4Block0ParentConvergesCheck 21
    && tttLargeFiber4Block0ParentConvergesCheck 22
    && tttLargeFiber4Block0ParentConvergesCheck 23
    && tttLargeFiber4Block0ParentConvergesCheck 24
    && tttLargeFiber4Block0ParentConvergesCheck 25
    && tttLargeFiber4Block0ParentConvergesCheck 26
    && tttLargeFiber4Block0ParentConvergesCheck 27
    && tttLargeFiber4Block0ParentConvergesCheck 28
    && tttLargeFiber4Block0ParentConvergesCheck 29
    && tttLargeFiber4Block0ParentConvergesCheck 30
    && tttLargeFiber4Block0ParentConvergesCheck 31
    && tttLargeFiber4Block0ParentConvergesCheck 32
    && tttLargeFiber4Block0ParentConvergesCheck 33
    && tttLargeFiber4Block0ParentConvergesCheck 34
    && tttLargeFiber4Block0ParentConvergesCheck 35
    && tttLargeFiber4Block0ParentConvergesCheck 36
    && tttLargeFiber4Block0ParentConvergesCheck 37
    && tttLargeFiber4Block0ParentConvergesCheck 38
    && tttLargeFiber4Block0ParentConvergesCheck 39
    && tttLargeFiber4Block0ParentConvergesCheck 40
    && tttLargeFiber4Block0ParentConvergesCheck 41
    && tttLargeFiber4Block0ParentConvergesCheck 42
    && tttLargeFiber4Block0ParentConvergesCheck 43
    && tttLargeFiber4Block0ParentConvergesCheck 44
    && tttLargeFiber4Block0ParentConvergesCheck 45
    && tttLargeFiber4Block0ParentConvergesCheck 46
    && tttLargeFiber4Block0ParentConvergesCheck 47
    && tttLargeFiber4Block0ParentConvergesCheck 48
    && tttLargeFiber4Block0ParentConvergesCheck 49
    && tttLargeFiber4Block0ParentConvergesCheck 50
    && tttLargeFiber4Block0ParentConvergesCheck 51
    && tttLargeFiber4Block0ParentConvergesCheck 52
    && tttLargeFiber4Block0ParentConvergesCheck 53
    && tttLargeFiber4Block0ParentConvergesCheck 54
    && tttLargeFiber4Block0ParentConvergesCheck 55
    && tttLargeFiber4Block0ParentConvergesCheck 56
    && tttLargeFiber4Block0ParentConvergesCheck 57
    && tttLargeFiber4Block0ParentConvergesCheck 58
    && tttLargeFiber4Block0ParentConvergesCheck 59
    && tttLargeFiber4Block0ParentConvergesCheck 60
    && tttLargeFiber4Block0ParentConvergesCheck 61
    && tttLargeFiber4Block0ParentConvergesCheck 62
    && tttLargeFiber4Block0ParentConvergesCheck 63

theorem tttLargeFiber4Block0ParentsAudit_ok :
    tttLargeFiber4Block0ParentsAudit = true := by
  simp [tttLargeFiber4Block0ParentsAudit,
    tttLargeFiber4Block0Parent_0_ok,
    tttLargeFiber4Block0Parent_1_ok,
    tttLargeFiber4Block0Parent_2_ok,
    tttLargeFiber4Block0Parent_3_ok,
    tttLargeFiber4Block0Parent_4_ok,
    tttLargeFiber4Block0Parent_5_ok,
    tttLargeFiber4Block0Parent_6_ok,
    tttLargeFiber4Block0Parent_7_ok,
    tttLargeFiber4Block0Parent_8_ok,
    tttLargeFiber4Block0Parent_9_ok,
    tttLargeFiber4Block0Parent_10_ok,
    tttLargeFiber4Block0Parent_11_ok,
    tttLargeFiber4Block0Parent_12_ok,
    tttLargeFiber4Block0Parent_13_ok,
    tttLargeFiber4Block0Parent_14_ok,
    tttLargeFiber4Block0Parent_15_ok,
    tttLargeFiber4Block0Parent_16_ok,
    tttLargeFiber4Block0Parent_17_ok,
    tttLargeFiber4Block0Parent_18_ok,
    tttLargeFiber4Block0Parent_19_ok,
    tttLargeFiber4Block0Parent_20_ok,
    tttLargeFiber4Block0Parent_21_ok,
    tttLargeFiber4Block0Parent_22_ok,
    tttLargeFiber4Block0Parent_23_ok,
    tttLargeFiber4Block0Parent_24_ok,
    tttLargeFiber4Block0Parent_25_ok,
    tttLargeFiber4Block0Parent_26_ok,
    tttLargeFiber4Block0Parent_27_ok,
    tttLargeFiber4Block0Parent_28_ok,
    tttLargeFiber4Block0Parent_29_ok,
    tttLargeFiber4Block0Parent_30_ok,
    tttLargeFiber4Block0Parent_31_ok,
    tttLargeFiber4Block0Parent_32_ok,
    tttLargeFiber4Block0Parent_33_ok,
    tttLargeFiber4Block0Parent_34_ok,
    tttLargeFiber4Block0Parent_35_ok,
    tttLargeFiber4Block0Parent_36_ok,
    tttLargeFiber4Block0Parent_37_ok,
    tttLargeFiber4Block0Parent_38_ok,
    tttLargeFiber4Block0Parent_39_ok,
    tttLargeFiber4Block0Parent_40_ok,
    tttLargeFiber4Block0Parent_41_ok,
    tttLargeFiber4Block0Parent_42_ok,
    tttLargeFiber4Block0Parent_43_ok,
    tttLargeFiber4Block0Parent_44_ok,
    tttLargeFiber4Block0Parent_45_ok,
    tttLargeFiber4Block0Parent_46_ok,
    tttLargeFiber4Block0Parent_47_ok,
    tttLargeFiber4Block0Parent_48_ok,
    tttLargeFiber4Block0Parent_49_ok,
    tttLargeFiber4Block0Parent_50_ok,
    tttLargeFiber4Block0Parent_51_ok,
    tttLargeFiber4Block0Parent_52_ok,
    tttLargeFiber4Block0Parent_53_ok,
    tttLargeFiber4Block0Parent_54_ok,
    tttLargeFiber4Block0Parent_55_ok,
    tttLargeFiber4Block0Parent_56_ok,
    tttLargeFiber4Block0Parent_57_ok,
    tttLargeFiber4Block0Parent_58_ok,
    tttLargeFiber4Block0Parent_59_ok,
    tttLargeFiber4Block0Parent_60_ok,
    tttLargeFiber4Block0Parent_61_ok,
    tttLargeFiber4Block0Parent_62_ok,
    tttLargeFiber4Block0Parent_63_ok]

def tttLargeFiber4Block0ComponentCertificateAudit : Bool :=
  tttRepresentativeModeAudit &&
    tttLargeFiber4CountsAudit &&
    tttLargeFiber4Block0SourcesCheck &&
    tttLargeFiber4Block0RowsAudit &&
    tttLargeFiber4Block0ParentMapAudit &&
    tttLargeFiber4Block0ParentsAudit

theorem tttLargeFiber4Block0ComponentCertificateAudit_ok :
    tttLargeFiber4Block0ComponentCertificateAudit = true := by
  simp [tttLargeFiber4Block0ComponentCertificateAudit,
    tttRepresentativeModeAudit_ok,
    tttLargeFiber4CountsAudit_ok,
    tttLargeFiber4Block0SourcesCheck_ok,
    tttLargeFiber4Block0RowsAudit_ok,
    tttLargeFiber4Block0ParentMapAudit_ok,
    tttLargeFiber4Block0ParentsAudit_ok]

end GoertzelLemma818TripleTauLargeFiber4Block0ComponentCertificate

end Mettapedia.GraphTheory.FourColor
