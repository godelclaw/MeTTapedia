import Mettapedia.GraphTheory.FourColor.GoertzelLemma818ClosedCollarBridgeProof

namespace Mettapedia.GraphTheory.FourColor
namespace GoertzelLemma818ClosedCollarS2Word5

open GoertzelLemma814
open GoertzelLemma818ClosedCollarBridgeTarget
open GoertzelLemma818ClosedCollarBridgeProof

def word : List TauOrient := [TauOrient.normal, TauOrient.normal, TauOrient.mirror]

def tauStateChunks : List (List TauState) :=
[
  [stateAt 0, stateAt 1, stateAt 2, stateAt 3, stateAt 4, stateAt 5, stateAt 6, stateAt 7, stateAt 8, stateAt 9, stateAt 10, stateAt 11, stateAt 12, stateAt 13, stateAt 14, stateAt 15]
, [stateAt 16, stateAt 17, stateAt 18, stateAt 19, stateAt 20, stateAt 21, stateAt 22, stateAt 23, stateAt 24, stateAt 25, stateAt 26, stateAt 27, stateAt 28, stateAt 29, stateAt 30, stateAt 31]
, [stateAt 32, stateAt 33, stateAt 34, stateAt 35, stateAt 36, stateAt 37, stateAt 38, stateAt 39, stateAt 40, stateAt 41, stateAt 42, stateAt 43, stateAt 44, stateAt 45, stateAt 46, stateAt 47]
, [stateAt 48, stateAt 49, stateAt 50, stateAt 51, stateAt 52, stateAt 53, stateAt 54, stateAt 55, stateAt 56, stateAt 57, stateAt 58, stateAt 59, stateAt 60, stateAt 61, stateAt 62, stateAt 63]
, [stateAt 64, stateAt 65, stateAt 66, stateAt 67, stateAt 68, stateAt 69, stateAt 70, stateAt 71, stateAt 72, stateAt 73, stateAt 74, stateAt 75, stateAt 76, stateAt 77, stateAt 78, stateAt 79]
, [stateAt 80, stateAt 81, stateAt 82, stateAt 83, stateAt 84, stateAt 85, stateAt 86, stateAt 87, stateAt 88, stateAt 89, stateAt 90, stateAt 91, stateAt 92, stateAt 93, stateAt 94, stateAt 95]
, [stateAt 96, stateAt 97, stateAt 98, stateAt 99, stateAt 100, stateAt 101, stateAt 102, stateAt 103, stateAt 104, stateAt 105, stateAt 106, stateAt 107, stateAt 108, stateAt 109, stateAt 110, stateAt 111]
, [stateAt 112, stateAt 113, stateAt 114, stateAt 115, stateAt 116, stateAt 117, stateAt 118, stateAt 119, stateAt 120, stateAt 121, stateAt 122, stateAt 123, stateAt 124, stateAt 125, stateAt 126, stateAt 127]
, [stateAt 128, stateAt 129, stateAt 130, stateAt 131, stateAt 132, stateAt 133, stateAt 134, stateAt 135, stateAt 136, stateAt 137, stateAt 138, stateAt 139, stateAt 140, stateAt 141, stateAt 142, stateAt 143]
, [stateAt 144, stateAt 145, stateAt 146, stateAt 147, stateAt 148, stateAt 149, stateAt 150, stateAt 151, stateAt 152, stateAt 153, stateAt 154, stateAt 155, stateAt 156, stateAt 157, stateAt 158, stateAt 159]
, [stateAt 160, stateAt 161, stateAt 162, stateAt 163, stateAt 164, stateAt 165, stateAt 166, stateAt 167, stateAt 168, stateAt 169, stateAt 170, stateAt 171, stateAt 172, stateAt 173, stateAt 174, stateAt 175]
, [stateAt 176, stateAt 177, stateAt 178, stateAt 179, stateAt 180, stateAt 181, stateAt 182, stateAt 183, stateAt 184, stateAt 185, stateAt 186, stateAt 187, stateAt 188, stateAt 189, stateAt 190, stateAt 191]
]

theorem tauStateChunks_chunk0 :
    (allTauStates.drop 0).take 16 =
      listGetD tauStateChunks 0 [] := by
  decide

theorem tauStateChunks_chunk1 :
    (allTauStates.drop 16).take 16 =
      listGetD tauStateChunks 1 [] := by
  decide

theorem tauStateChunks_chunk2 :
    (allTauStates.drop 32).take 16 =
      listGetD tauStateChunks 2 [] := by
  decide

theorem tauStateChunks_chunk3 :
    (allTauStates.drop 48).take 16 =
      listGetD tauStateChunks 3 [] := by
  decide

theorem tauStateChunks_chunk4 :
    (allTauStates.drop 64).take 16 =
      listGetD tauStateChunks 4 [] := by
  decide

theorem tauStateChunks_chunk5 :
    (allTauStates.drop 80).take 16 =
      listGetD tauStateChunks 5 [] := by
  decide

theorem tauStateChunks_chunk6 :
    (allTauStates.drop 96).take 16 =
      listGetD tauStateChunks 6 [] := by
  decide

theorem tauStateChunks_chunk7 :
    (allTauStates.drop 112).take 16 =
      listGetD tauStateChunks 7 [] := by
  decide

theorem tauStateChunks_chunk8 :
    (allTauStates.drop 128).take 16 =
      listGetD tauStateChunks 8 [] := by
  decide

theorem tauStateChunks_chunk9 :
    (allTauStates.drop 144).take 16 =
      listGetD tauStateChunks 9 [] := by
  decide

theorem tauStateChunks_chunk10 :
    (allTauStates.drop 160).take 16 =
      listGetD tauStateChunks 10 [] := by
  decide

theorem tauStateChunks_chunk11 :
    (allTauStates.drop 176).take 16 =
      listGetD tauStateChunks 11 [] := by
  decide

theorem tauStateChunks_terminal :
    allTauStates.drop (tauStateChunks.length * 16) = [] := by
  decide

theorem tauStateChunks_get
    (i : Nat) (hi : i < tauStateChunks.length) :
    (allTauStates.drop (i * 16)).take 16 =
      listGetD tauStateChunks i [] := by
  have hlen : tauStateChunks.length = 12 := by
    rfl
  by_cases h0 : i = 0
  · subst i
    simpa using tauStateChunks_chunk0
  by_cases h1 : i = 1
  · subst i
    simpa using tauStateChunks_chunk1
  by_cases h2 : i = 2
  · subst i
    simpa using tauStateChunks_chunk2
  by_cases h3 : i = 3
  · subst i
    simpa using tauStateChunks_chunk3
  by_cases h4 : i = 4
  · subst i
    simpa using tauStateChunks_chunk4
  by_cases h5 : i = 5
  · subst i
    simpa using tauStateChunks_chunk5
  by_cases h6 : i = 6
  · subst i
    simpa using tauStateChunks_chunk6
  by_cases h7 : i = 7
  · subst i
    simpa using tauStateChunks_chunk7
  by_cases h8 : i = 8
  · subst i
    simpa using tauStateChunks_chunk8
  by_cases h9 : i = 9
  · subst i
    simpa using tauStateChunks_chunk9
  by_cases h10 : i = 10
  · subst i
    simpa using tauStateChunks_chunk10
  by_cases h11 : i = 11
  · subst i
    simpa using tauStateChunks_chunk11
  · have hbound : i < 12 := by
      simpa [hlen] using hi
    omega

theorem tauStateChunks_eq : allTauStates = tauStateChunks.flatten := by
  have h := list_eq_join_chunks_of_drop_take
    allTauStates 16 tauStateChunks
    tauStateChunks_get tauStateChunks_terminal
  simpa using h


end GoertzelLemma818ClosedCollarS2Word5
end Mettapedia.GraphTheory.FourColor
