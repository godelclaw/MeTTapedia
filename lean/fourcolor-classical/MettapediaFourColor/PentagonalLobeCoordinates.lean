import MettapediaFourColor.PentagonalLobeTangle
import Mettapedia.GraphTheory.FourColor.ElevenLobeDartCoordinates

/-!
# Coordinates for the literal pentagonal-lobe patch

The compact permutation tables identify the literal sixteen-vertex patch
with two cyclic lists and their three incident darts. Each table equation
is checked by the kernel; no colouring or reducibility certificate is used.
-/

namespace FourColor.PentagonalLobePatch.Tangle.Coordinates

open ConfigurationTable
open Mettapedia.GraphTheory.FourColor.ElevenLobeSpokeOrder

set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

def dartIndex : Coordinate.Dart ≃ Fin 48 where
  toFun
    | .inl (i, s) => ⟨3 * i.val + s.val, by omega⟩
    | .inr (j, s) => ⟨33 + 3 * j.val + s.val, by omega⟩
  invFun d := if h : d.val < 33 then
      .inl (⟨d.val / 3, by omega⟩, ⟨d.val % 3, by omega⟩)
    else .inr (⟨(d.val - 33) / 3, by omega⟩, ⟨(d.val - 33) % 3, by omega⟩)
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def vertexPermutation : Equiv.Perm (Fin 16) where
  toFun := lookup "DMCENLBFOPAGHJKI"
  invFun := lookup "KGCADHLMPNOFBEIJ"
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def dartPermutation : Equiv.Perm (Fin 48) where
  toFun := lookup "JeKILNgifdHFOQhPjlbDcpECRTmokVn\\BaUWXZ^`][AGMSY_"
  invFun := lookup "kaXTWLlKDACEmFMPNYnZc^deofj`igphbSUJBIGOHQ]R[_\\V"
  left_inv := by decide +kernel
  right_inv := by decide +kernel

def vertices : Fin 16 ≃ Coordinate.Vertex := vertexPermutation.trans (finSumFinEquiv (m := 11) (n := 5)).symm

def darts : Dart ≃ Coordinate.Dart := (index.trans dartPermutation).trans dartIndex.symm

theorem vertex (d : Dart) : vertices (piece.vertOf d) = Coordinate.vertex (darts d) := by
  revert d
  decide +kernel

theorem internal (i : Fin 42) : ¬ Coordinate.boundary (darts (.inl i)) := by
  revert i
  decide +kernel

theorem boundary (b : Fin 6) : Coordinate.boundary (darts (.inr b)) := by
  revert b
  decide +kernel

theorem port (b : Fin 6) : darts (.inr b) = .inl (Incidence.outward b, 0) := by
  revert b
  decide +kernel

theorem alpha (i : Fin 42) :
    darts (.inl (piece.interiorAlpha i)) = Coordinate.flip (darts (.inl i)) := by
  revert i
  decide +kernel

theorem rotation (d : Dart) : darts (piece.rho d) = Coordinate.turn (darts d) := by
  revert d
  decide +kernel

end FourColor.PentagonalLobePatch.Tangle.Coordinates
