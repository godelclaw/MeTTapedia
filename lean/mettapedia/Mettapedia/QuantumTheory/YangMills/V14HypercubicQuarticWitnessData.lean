import Mettapedia.QuantumTheory.YangMills.V14HypercubicQuarticCanonicalData

/-!
# Supplied witness data for the dimension-eight quartic census

The table contains one signed-permutation transporter or one negative
stabilizer for each of the 126 canonical monomials.  Proofs are replayed in
small companion blocks.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia
namespace QuantumTheory
namespace YangMills
namespace V14HypercubicQuarticCensus

/-- One supplied transporter or negative stabilizer for each canonical
monomial. -/
def canonicalQuarticCertificate : Fin 126 → QuarticCertificate
  | 0 => .orbit 0 16 0
  | 1 => .killed 0 2
  | 2 => .orbit 1 21 0
  | 3 => .killed 0 2
  | 4 => .orbit 0 10 0
  | 5 => .killed 0 2
  | 6 => .killed 0 4
  | 7 => .killed 0 2
  | 8 => .killed 0 4
  | 9 => .orbit 1 15 0
  | 10 => .killed 0 2
  | 11 => .orbit 1 9 0
  | 12 => .killed 0 2
  | 13 => .killed 0 4
  | 14 => .orbit 0 8 0
  | 15 => .killed 0 1
  | 16 => .killed 0 1
  | 17 => .killed 0 1
  | 18 => .killed 0 1
  | 19 => .killed 0 1
  | 20 => .killed 0 1
  | 21 => .killed 0 1
  | 22 => .killed 0 1
  | 23 => .killed 0 1
  | 24 => .killed 0 1
  | 25 => .orbit 1 19 0
  | 26 => .killed 0 2
  | 27 => .orbit 1 18 0
  | 28 => .killed 0 2
  | 29 => .killed 0 4
  | 30 => .orbit 2 0 0
  | 31 => .killed 0 1
  | 32 => .killed 0 1
  | 33 => .killed 0 1
  | 34 => .orbit 0 4 0
  | 35 => .killed 0 1
  | 36 => .killed 0 1
  | 37 => .killed 0 1
  | 38 => .killed 0 1
  | 39 => .killed 0 1
  | 40 => .killed 0 1
  | 41 => .killed 0 1
  | 42 => .killed 0 1
  | 43 => .killed 0 1
  | 44 => .killed 0 1
  | 45 => .killed 0 4
  | 46 => .killed 0 2
  | 47 => .killed 0 4
  | 48 => .killed 0 2
  | 49 => .orbit 3 0 0
  | 50 => .killed 0 4
  | 51 => .killed 0 1
  | 52 => .killed 0 1
  | 53 => .killed 0 1
  | 54 => .killed 0 4
  | 55 => .orbit 1 13 0
  | 56 => .killed 0 2
  | 57 => .orbit 2 1 0
  | 58 => .killed 0 2
  | 59 => .killed 0 4
  | 60 => .orbit 1 12 0
  | 61 => .killed 0 1
  | 62 => .killed 0 1
  | 63 => .killed 0 1
  | 64 => .orbit 1 3 0
  | 65 => .killed 0 1
  | 66 => .killed 0 1
  | 67 => .killed 0 1
  | 68 => .killed 0 4
  | 69 => .orbit 0 2 0
  | 70 => .killed 0 1
  | 71 => .killed 0 1
  | 72 => .killed 0 1
  | 73 => .killed 0 1
  | 74 => .killed 0 1
  | 75 => .killed 0 1
  | 76 => .killed 0 1
  | 77 => .killed 0 1
  | 78 => .killed 0 1
  | 79 => .killed 0 1
  | 80 => .killed 0 2
  | 81 => .killed 0 4
  | 82 => .killed 0 2
  | 83 => .orbit 3 2 0
  | 84 => .killed 0 2
  | 85 => .killed 0 2
  | 86 => .killed 0 1
  | 87 => .killed 0 1
  | 88 => .killed 0 1
  | 89 => .killed 0 2
  | 90 => .killed 0 2
  | 91 => .orbit 3 4 0
  | 92 => .killed 0 2
  | 93 => .killed 0 4
  | 94 => .killed 0 2
  | 95 => .killed 0 2
  | 96 => .killed 0 1
  | 97 => .killed 0 1
  | 98 => .killed 0 1
  | 99 => .killed 0 2
  | 100 => .killed 0 1
  | 101 => .killed 0 1
  | 102 => .killed 0 1
  | 103 => .killed 0 2
  | 104 => .killed 0 2
  | 105 => .orbit 2 3 0
  | 106 => .killed 0 2
  | 107 => .orbit 1 7 0
  | 108 => .killed 0 2
  | 109 => .killed 0 4
  | 110 => .orbit 1 6 0
  | 111 => .killed 0 1
  | 112 => .killed 0 1
  | 113 => .killed 0 1
  | 114 => .orbit 1 1 0
  | 115 => .killed 0 1
  | 116 => .killed 0 1
  | 117 => .killed 0 1
  | 118 => .killed 0 4
  | 119 => .orbit 1 0 0
  | 120 => .killed 0 1
  | 121 => .killed 0 1
  | 122 => .killed 0 1
  | 123 => .killed 0 2
  | 124 => .killed 0 2
  | 125 => .orbit 0 0 0
  | _ => .orbit 0 0 0


/-- Embed one entry of a 21-entry proof block into the 126-entry table. -/
def quarticWitnessBlockIndex (offset : Nat) (hoffset : offset + 21 ≤ 126)
    (entry : Fin 21) : Fin 126 :=
  ⟨offset + entry.1, by omega⟩

end V14HypercubicQuarticCensus
end YangMills
end QuantumTheory
end Mettapedia
