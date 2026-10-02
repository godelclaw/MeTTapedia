import MettapediaFourColor.NearLinearDiamondData
import MettapediaFourColor.ConfigurationRealization
import MettapediaFourColor.KempeBoundarySplit
import Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

/-!
# An exact three-triangle chain and its boundary subdivision

D0004 and D0006 are from near-linear-4ct/reducible-configurations, revision
c2ce7a96e35256201526e2abb51a39d04a588b53, copyright 2026 Yuta Inoue (MIT).
Their unaltered source files and licence are retained in tools/fourcolor/near-linear.
The larger piece is classical configuration 7. Its complete construction map,
cyclic stars, prescribed degrees and ordered boundary are checked here.
Repair is transported separately; no catalogue coverage is asserted.
-/

namespace FourColor.NearLinearChainData

open NearLinearDiamondData ExecutableConfiguration ConfigurationTable
open Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

set_option maxRecDepth 32768

local instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c : V) : DecidableRel (subdivide G a b c).Adj := fun x y => by
  cases x <;> cases y <;> dsimp [subdivide, removed] <;> infer_instance

def input0004 : Input 13 8 where
  source := "13 8\n9 5 4 5 11 10 3\n10 6 3 9 11 12 13 2\n11 5 6 12 10 9 5\n12 6 7 8 13 10 11 6\n13 5 2 10 12 8 1\n"
  valid := by decide +kernel

def boundary0004 : List (Fin 13) := [7, 6, 5, 4, 3, 2, 1, 0]

theorem boundary_source0004 : boundary0004 = input0004.boundary.reverse := by decide +kernel

def stars0004 (v : Fin 13) : List (Fin 13) :=
  if h : v.val < 8 then ![[1, 12, 7], [0, 2, 9, 12], [1, 3, 8, 9], [2, 4, 8], [3, 5, 10, 8], [4, 6, 11, 10], [5, 7, 11], [0, 12, 11, 6]] ⟨v.val, h⟩
  else input0004.internalStar v

theorem stars_exact0004 : ∀ v : Fin 13, (stars0004 v).Nodup ∧
    ∀ w, w ∈ stars0004 v ↔ input0004.graph.Adj v w := by decide +kernel

theorem degree_source0004 : ∀ i : Fin 5,
    (coreRow input0004.source i).getD 1 0 = (stars0004 (i.natAdd 8)).length := by decide +kernel

def input0006 : Input 14 9 where
  source := "14 9\n10 6 5 6 11 12 13 4\n11 5 7 8 12 10 6\n12 6 9 14 13 10 11 8\n13 6 3 4 10 12 14 2\n14 5 2 13 12 9 1\n"
  valid := by decide +kernel

def boundary0006 : List (Fin 14) := [8, 7, 6, 5, 4, 3, 2, 1, 0]

theorem boundary_source0006 : boundary0006 = input0006.boundary.reverse := by decide +kernel

def stars0006 (v : Fin 14) : List (Fin 14) :=
  if h : v.val < 9 then ![[1, 13, 8], [0, 2, 12, 13], [1, 3, 12], [2, 4, 9, 12], [3, 5, 9], [4, 6, 10, 9], [5, 7, 10], [6, 8, 11, 10], [0, 13, 11, 7]] ⟨v.val, h⟩
  else input0006.internalStar v

theorem stars_exact0006 : ∀ v : Fin 14, (stars0006 v).Nodup ∧
    ∀ w, w ∈ stars0006 v ↔ input0006.graph.Adj v w := by decide +kernel

theorem degree_source0006 : ∀ i : Fin 5,
    (coreRow input0006.source i).getD 1 0 = (stars0006 (i.natAdd 9)).length := by decide +kernel

def program007 : List Step := [.join, .rotate 3, .join, .rotate 8, .join, .rotate 8, .fork, .rotate 6, .join, .rotate 1, .fork, .rotate 5, .join, .rotate 1, .fork, .rotate 5, .fork, .rotate 3, .fork, .rotate 2, .fork, .fork]

theorem reference007 : evaluate program007 = cfmap cf007 := evaluate_eq _

def table007 : Data 60 where
  edges := "BADCFEHGJILKNMPORQTSVUXWZY\\[^]`_badcfehgjilknmporqtsvuxwzy|{"
  nodes := "F`BSDMLRHkJaGVNsPIErTO\\jX]ZA[o^CfnbgdWe|hYKvlc_wpUQztmq{xuyi"
  faces := "C\\E`ASIMKRGkOFQVHsUDNrYf[jW]_ZBocLenagidX|mJbvq^TwuPlzypt{hx"
  cancel := by decide +kernel

set_option maxHeartbeats 4000000 in
-- Check the complete reference construction against the permutation table.
theorem numbered007 : numbered program007 = table007.map := by
  apply table007.eq_of_tables
  decide +kernel

def vertex007 : Fin 60 → Fin 14 := lookup "GFGKGHAIANABIHILINHKHLEDEJEFFJFKCBCMCDDMDJBNBMKJKLNLNMLJLMMJ"
def representative007 : Fin 14 → Fin 60 := lookup "GLaXWBAFHZDPdJ"

def faces007 : ConfigurationFaceGraph.Presentation table007.map input0006.graph where
  vertex := vertex007
  representative := representative007
  vertex_rep := by decide +kernel
  vertex_face := by decide +kernel
  same_face := ConfigurationFaceGraph.same_face_of_reaches (n := 7) (by decide +kernel)
  adjacent := by decide +kernel

def realization007 : Realization (cfmap cf007) table007 0 :=
  reference007 ▸
    ({ numbering := (index program007).symm
       map_eq := numbered007
       point_eq := by decide +kernel } : Realization (evaluate program007) table007 0)

def ring007 : List (Fin 60) := [5, 0, 27, 22, 37, 32, 11, 6, 12]
def boundary007 : List (Fin 14) := [7, 6, 5, 4, 3, 2, 1, 0, 8]

theorem cpring007 : table007.map.cpring 0 = ring007 := by
  apply Hypermap.cpring_eq
  · unfold IsCyclicChain; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem reducibilityTrace007 (et : List Color) :
    (cfmap cf007).map.RingTrace (cfring cf007).reverse et ↔
      KempeBoundarySplit.GraphTrace input0006.graph boundary007 et := by
  rw [cfring, List.reverse_reverse, realization007.forwardRingTrace,
    cpring007, faces007.ringTrace_iff]
  rfl

def degree007 (v : Fin 14) : ℕ := entry "DEDEDEDEEGFGGF" v.val
def stars007 : Fin 14 → List (Fin 14) :=
  ConfigurationFaceGraph.star table007.map vertex007 representative007 degree007

theorem rotation007 : ∀ v : Fin 14, ∃ shift : Fin 7,
    stars007 v = ((stars0006 v).reverse).rotate shift.val := by decide +kernel

theorem boundary007_align : boundary0006.rotate 1 = boundary007 := by decide +kernel

def insert46 : subdivide input0004.graph 5 4 10 ≃g input0006.graph where
  toEquiv :=
    { toFun := fun v => v.elim 2 (fun i => (![6, 7, 8, 0, 1, 3, 4, 5, 13, 11, 12, 9, 10]) i)
      invFun := ![some 3, some 4, none, some 5, some 6, some 7, some 0, some 1, some 2, some 11, some 12, some 9, some 10, some 8]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  map_rel_iff' := by decide +kernel

theorem triangle46 : input0004.graph.Adj 5 4 ∧
    input0004.graph.Adj 5 10 ∧ input0004.graph.Adj 4 10 := by decide +kernel

theorem rotation46 : ∀ v : Option (Fin 13), ∃ shift : Fin 7,
    (stars0006 (insert46 v)).reverse =
      ((ConfigurationFaceGraph.triangleStar (fun x => (stars0004 x).reverse) 5 4 10 v).map insert46).rotate shift.val := by
  decide +kernel

theorem boundary46 :
    ((ConfigurationFaceGraph.triangleBoundary boundary0004 5).map insert46).rotate 6 = boundary0006 := by decide +kernel

end FourColor.NearLinearChainData
