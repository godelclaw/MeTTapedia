import MettapediaFourColor.NearLinearDiamondData
import MettapediaFourColor.ConfigurationRealization
import Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

/-!
# Five exact embedded presentations from the near-linear catalogue

The source rows are from near-linear-4ct/reducible-configurations at revision
c2ce7a96e35256201526e2abb51a39d04a588b53, copyright 2026 Yuta Inoue (MIT).
Unaltered inputs and the notice are retained in tools/fourcolor/near-linear.
Configuration 225 and its construction semantics are reused from Emery's
MIT-licensed port of Gonthier--Werner and Robertson--Sanders--Seymour--Thomas.

The complete graph, cyclic stars, degrees and ordered boundary are retained.
This module establishes constructions, not a repair or coverage theorem.
-/

namespace FourColor.NearLinearFiveData

open NearLinearDiamondData ExecutableConfiguration ConfigurationTable
open Mettapedia.GraphTheory.FourColor.BoundaryTriangleSubdivision

set_option maxRecDepth 32768

local instance {V : Type*} [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (a b c : V) : DecidableRel (subdivide G a b c).Adj := fun x y => by
  cases x <;> cases y <;> dsimp [subdivide, removed] <;> infer_instance

def input0370 : Input 21 12 where
  source := "21 12\n13 7 4 19 21 14 17 15 16\n14 6 8 9 17 13 21 7\n15 7 11 12 20 16 13 17 10\n16 5 13 15 20 18 4\n17 5 10 15 13 14 9\n18 5 3 4 16 20 2\n19 5 5 6 21 13 4\n20 6 2 18 16 15 12 1\n21 5 7 14 13 19 6\n"
  valid := by decide +kernel

def boundary0370 : List (Fin 21) := [11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

theorem boundary_source0370 : boundary0370 = input0370.boundary.reverse := by
  decide +kernel

def stars0370 (v : Fin 21) : List (Fin 21) :=
  if h : v.val < 12 then ![[1, 19, 11], [0, 2, 17, 19], [1, 3, 17], [2, 4, 18, 12, 15, 17], [3, 5, 18], [4, 6, 20, 18], [5, 7, 13, 20], [6, 8, 13], [7, 9, 16, 13], [8, 10, 14, 16], [9, 11, 14], [0, 19, 14, 10]] ⟨v.val, h⟩ else input0370.internalStar v

theorem stars_exact0370 : ∀ v : Fin 21, (stars0370 v).Nodup ∧
    ∀ w, w ∈ stars0370 v ↔ input0370.graph.Adj v w := by decide +kernel

theorem degree_source0370 : ∀ i : Fin 9,
    (coreRow input0370.source i).getD 1 0 = (stars0370 (i.natAdd 12)).length := by
  decide +kernel

def input0464 : Input 22 13 where
  source := "22 13\n14 6 6 7 20 15 17 5\n15 7 16 17 14 20 19 21 2\n16 5 3 4 17 15 2\n17 5 5 14 15 16 4\n18 6 12 13 22 21 19 11\n19 7 10 11 18 21 15 20 9\n20 6 8 9 19 15 14 7\n21 5 15 19 18 22 2\n22 5 2 21 18 13 1\n"
  valid := by decide +kernel

def boundary0464 : List (Fin 22) := [12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

theorem boundary_source0464 : boundary0464 = input0464.boundary.reverse := by
  decide +kernel

def stars0464 (v : Fin 22) : List (Fin 22) :=
  if h : v.val < 13 then ![[1, 21, 12], [0, 2, 15, 14, 20, 21], [1, 3, 15], [2, 4, 16, 15], [3, 5, 13, 16], [4, 6, 13], [5, 7, 19, 13], [6, 8, 19], [7, 9, 18, 19], [8, 10, 18], [9, 11, 17, 18], [10, 12, 17], [0, 21, 17, 11]] ⟨v.val, h⟩ else input0464.internalStar v

theorem stars_exact0464 : ∀ v : Fin 22, (stars0464 v).Nodup ∧
    ∀ w, w ∈ stars0464 v ↔ input0464.graph.Adj v w := by decide +kernel

theorem degree_source0464 : ∀ i : Fin 9,
    (coreRow input0464.source i).getD 1 0 = (stars0464 (i.natAdd 13)).length := by
  decide +kernel

def input0465 : Input 22 13 where
  source := "22 13\n14 6 8 9 18 20 15 7\n15 7 6 7 14 20 16 17 5\n16 7 11 21 22 19 17 15 20\n17 5 5 15 16 19 4\n18 5 10 11 20 14 9\n19 6 3 4 17 16 22 2\n20 5 16 15 14 18 11\n21 5 12 13 22 16 11\n22 6 2 19 16 21 13 1\n"
  valid := by decide +kernel

def boundary0465 : List (Fin 22) := [12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

theorem boundary_source0465 : boundary0465 = input0465.boundary.reverse := by
  decide +kernel

def stars0465 (v : Fin 22) : List (Fin 22) :=
  if h : v.val < 13 then ![[1, 21, 12], [0, 2, 18, 21], [1, 3, 18], [2, 4, 16, 18], [3, 5, 14, 16], [4, 6, 14], [5, 7, 13, 14], [6, 8, 13], [7, 9, 17, 13], [8, 10, 17], [9, 11, 20, 15, 19, 17], [10, 12, 20], [0, 21, 20, 11]] ⟨v.val, h⟩ else input0465.internalStar v

theorem stars_exact0465 : ∀ v : Fin 22, (stars0465 v).Nodup ∧
    ∀ w, w ∈ stars0465 v ↔ input0465.graph.Adj v w := by decide +kernel

theorem degree_source0465 : ∀ i : Fin 9,
    (coreRow input0465.source i).getD 1 0 = (stars0465 (i.natAdd 13)).length := by
  decide +kernel

def input0604 : Input 23 14 where
  source := "23 14\n15 7 3 4 16 21 20 23 2\n16 6 5 6 22 21 15 4\n17 6 13 14 23 20 18 12\n18 6 11 12 17 20 19 10\n19 5 9 10 18 20 8\n20 7 19 18 17 23 15 21 8\n21 5 20 15 16 22 8\n22 5 7 8 21 16 6\n23 6 2 15 20 17 14 1\n"
  valid := by decide +kernel

def boundary0604 : List (Fin 23) := [13, 12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

theorem boundary_source0604 : boundary0604 = input0604.boundary.reverse := by
  decide +kernel

def stars0604 (v : Fin 23) : List (Fin 23) :=
  if h : v.val < 14 then ![[1, 22, 13], [0, 2, 14, 22], [1, 3, 14], [2, 4, 15, 14], [3, 5, 15], [4, 6, 21, 15], [5, 7, 21], [6, 8, 18, 19, 20, 21], [7, 9, 18], [8, 10, 17, 18], [9, 11, 17], [10, 12, 16, 17], [11, 13, 16], [0, 22, 16, 12]] ⟨v.val, h⟩ else input0604.internalStar v

theorem stars_exact0604 : ∀ v : Fin 23, (stars0604 v).Nodup ∧
    ∀ w, w ∈ stars0604 v ↔ input0604.graph.Adj v w := by decide +kernel

theorem degree_source0604 : ∀ i : Fin 9,
    (coreRow input0604.source i).getD 1 0 = (stars0604 (i.natAdd 14)).length := by
  decide +kernel

def input3202 : Input 22 13 where
  source := "22 13\n14 7 15 16 17 18 19 20 1\n15 5 2 3 16 14 1\n16 6 4 5 17 14 15 3\n17 5 6 18 14 16 5\n18 6 7 8 19 14 17 6\n19 7 9 10 21 20 14 18 8\n20 5 14 19 21 22 1\n21 6 11 12 22 20 19 10\n22 5 1 20 21 12 13\n"
  valid := by decide +kernel

def boundary3202 : List (Fin 22) := [12, 11, 10, 9, 8, 7, 6, 5, 4, 3, 2, 1, 0]

theorem boundary_source3202 : boundary3202 = input3202.boundary.reverse := by
  decide +kernel

def stars3202 (v : Fin 22) : List (Fin 22) :=
  if h : v.val < 13 then ![[1, 14, 13, 19, 21, 12], [0, 2, 14], [1, 3, 15, 14], [2, 4, 15], [3, 5, 16, 15], [4, 6, 17, 16], [5, 7, 17], [6, 8, 18, 17], [7, 9, 18], [8, 10, 20, 18], [9, 11, 20], [10, 12, 21, 20], [0, 21, 11]] ⟨v.val, h⟩ else input3202.internalStar v

theorem stars_exact3202 : ∀ v : Fin 22, (stars3202 v).Nodup ∧
    ∀ w, w ∈ stars3202 v ↔ input3202.graph.Adj v w := by decide +kernel

theorem degree_source3202 : ∀ i : Fin 9,
    (coreRow input3202.source i).getD 1 0 = (stars3202 (i.natAdd 13)).length := by
  decide +kernel

def program225 : List Step := [.join, .rotate 2, .join, .rotate 13, .fork, .rotate 3, .join, .rotate 12, .fork, .rotate 3, .join, .rotate 11, .fork, .rotate 3, .join, .rotate 10, .fork, .rotate 3, .join, .rotate 9, .fork, .rotate 3, .join, .rotate 8, .fork, .rotate 3, .join, .rotate 6, .join, .rotate 1, .fork, .rotate 6, .fork, .rotate 1, .fork, .rotate 2, .fork, .rotate 1, .fork, .rotate 1, .fork]

theorem reference225 : evaluate program225 = cfmap cf225 := evaluate_eq _

def table225 : Data 104 where
  base := 20
  edges := "\u0015\u0014\u0017\u0016\u0019\u0018\u001b\u001a\u001d\u001c\u001f\u001e! #\"%$'&)(+*-,/.1032547698;:=<?>A@CBEDGFIHKJMLONQPSRUTWVYX[Z]\\_^a`cbedgfihkjmlonqpsrutwvyx{z"
  nodes := "\u0019V\u0015 \u0017\u001a\u001f#\u001b*\u001d$\u0018[!\u001c)-%4'.\u001eq+&37/>18(u50=A9H;B2y?:GKCREL<fIDQUMaO\u0014F\\SN\u0016eWnY\"Ti]b_P`mcXJjg^h{kdZro,pvs6tzw@xl"
  faces := "\u0016Q\u0018V\u0014 \u001c\u0019\u001e#\u001a*\"\u0017\u001b[&\u001f(-$4,\u001d%q0)27.>6'/u:3<A8H@19yD=FKBRJ;CfNGPULaTEM\\X\u0015Ze!n^S`iObd_WmhI]jlgc{pY+rto5vxs?zkw"
  cancel := by decide +kernel

set_option maxHeartbeats 8000000 in
-- Compare the complete 104-dart construction and the decoded table.
theorem numbered225 : numbered program225 = table225.map := by
  apply table225.eq_of_tables
  decide +kernel

def vertex225 : Fin 104 → Fin 23 := lookup "IHISIJKJKRKLJSJRMLMQMNLRLQANAWABNQNWCBCOCDBWBOEDEPEFDODPGFGVGHFPFVSHSTSRVPVUVHHUHTPOPUUOUTRTRQQTQWWTWOOT"
def representative225 : Fin 23 → Fin 104 := lookupBase 20 ".38=BGL\u0015\u0014\u0019\u001a\u001f$);E'\u001d\u0017Y_O1"

def faces225 : ConfigurationFaceGraph.Presentation table225.map input0604.graph where
  vertex := vertex225
  representative := representative225
  vertex_rep := by decide +kernel
  vertex_face := by decide +kernel
  same_face := ConfigurationFaceGraph.same_face_of_reaches (n := 9) (by decide +kernel)
  adjacent := by decide +kernel

def realization225 : Realization (cfmap cf225) table225 0 :=
  reference225 ▸
    ({ numbering := (index program225).symm
       map_eq := numbered225
       point_eq := by decide +kernel } : Realization (evaluate program225) table225 0)

def ring225 : List (Fin 104) := [5, 0, 61, 56, 51, 46, 41, 36, 31, 26, 21, 16, 11, 6]
def boundary225 : List (Fin 23) := [9, 8, 7, 6, 5, 4, 3, 2, 1, 0, 13, 12, 11, 10]

theorem cpring225 : table225.map.cpring 0 = ring225 := by
  apply Hypermap.cpring_eq
  · unfold IsCyclicChain; decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem reducibilityTrace225 (et : List Color) :
    (cfmap cf225).map.RingTrace (cfring cf225).reverse et ↔
      ∃ k : input0604.graph.Coloring Color, et = trace (boundary225.map k) := by
  rw [cfring, List.reverse_reverse, realization225.forwardRingTrace,
    cpring225, faces225.ringTrace_iff]
  rfl

def degree225 (v : Fin 23) : ℕ := entry "DEDEDEDGDEDEDEHGGGFHFFG" v.val
def stars225 : Fin 23 → List (Fin 23) :=
  ConfigurationFaceGraph.star table225.map vertex225 representative225 degree225

theorem rotation225 : ∀ v : Fin 23, ∃ shift : Fin 9,
    stars225 v = ((stars0604 v).reverse).rotate shift.val := by
  decide +kernel

theorem boundary225_align : boundary0604.rotate 4 = boundary225 := by
  decide +kernel

def insert0370_0464 : subdivide input0370.graph 9 8 16 ≃g input0464.graph where
  toEquiv :=
    { toFun := fun v => v.elim 7 (fun i => (![11, 12, 0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 14, 13, 18, 20, 19, 21, 15, 17, 16]) i)
      invFun := ![some 2, some 3, some 4, some 5, some 6, some 7, some 8, none, some 9, some 10, some 11, some 0, some 1, some 13, some 12, some 18, some 20, some 19, some 14, some 16, some 15, some 17]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  map_rel_iff' := by decide +kernel

theorem triangle0370_0464 : input0370.graph.Adj 9 8 ∧
    input0370.graph.Adj 9 16 ∧ input0370.graph.Adj 8 16 := by decide +kernel

theorem rotation0370_0464 : ∀ v : Option (Fin 21), ∃ shift : Fin 10,
    (stars0464 (insert0370_0464 v)).reverse =
      ((ConfigurationFaceGraph.triangleStar (fun x => (stars0370 x).reverse) 9 8 16 v).map insert0370_0464).rotate
        shift.val := by decide +kernel

theorem boundary0370_0464 :
    ((ConfigurationFaceGraph.triangleBoundary boundary0370 9).map insert0370_0464).rotate
      11 = boundary0464 := by decide +kernel

def insert0370_0465 : subdivide input0370.graph 6 5 20 ≃g input0465.graph where
  toEquiv :=
    { toFun := fun v => v.elim 0 (fun i => (![7, 8, 9, 10, 11, 12, 1, 2, 3, 4, 5, 6, 15, 18, 14, 19, 16, 17, 20, 13, 21]) i)
      invFun := ![none, some 6, some 7, some 8, some 9, some 10, some 11, some 0, some 1, some 2, some 3, some 4, some 5, some 19, some 14, some 12, some 16, some 17, some 13, some 15, some 18, some 20]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  map_rel_iff' := by decide +kernel

theorem triangle0370_0465 : input0370.graph.Adj 6 5 ∧
    input0370.graph.Adj 6 20 ∧ input0370.graph.Adj 5 20 := by decide +kernel

theorem rotation0370_0465 : ∀ v : Option (Fin 21), ∃ shift : Fin 10,
    (stars0465 (insert0370_0465 v)).reverse =
      ((ConfigurationFaceGraph.triangleStar (fun x => (stars0370 x).reverse) 6 5 20 v).map insert0370_0465).rotate
        shift.val := by decide +kernel

theorem boundary0370_0465 :
    ((ConfigurationFaceGraph.triangleBoundary boundary0370 6).map insert0370_0465).rotate
      7 = boundary0465 := by decide +kernel

def insert0465_0604 : subdivide input0465.graph 4 3 16 ≃g input0604.graph where
  toEquiv :=
    { toFun := fun v => v.elim 0 (fun i => (![10, 11, 12, 13, 1, 2, 3, 4, 5, 6, 7, 8, 9, 15, 14, 19, 22, 21, 16, 20, 18, 17]) i)
      invFun := ![none, some 4, some 5, some 6, some 7, some 8, some 9, some 10, some 11, some 12, some 0, some 1, some 2, some 3, some 14, some 13, some 18, some 21, some 20, some 15, some 19, some 17, some 16]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  map_rel_iff' := by decide +kernel

theorem triangle0465_0604 : input0465.graph.Adj 4 3 ∧
    input0465.graph.Adj 4 16 ∧ input0465.graph.Adj 3 16 := by decide +kernel

theorem rotation0465_0604 : ∀ v : Option (Fin 22), ∃ shift : Fin 10,
    (stars0604 (insert0465_0604 v)).reverse =
      ((ConfigurationFaceGraph.triangleStar (fun x => (stars0465 x).reverse) 4 3 16 v).map insert0465_0604).rotate
        shift.val := by decide +kernel

theorem boundary0465_0604 :
    ((ConfigurationFaceGraph.triangleBoundary boundary0465 4).map insert0465_0604).rotate
      10 = boundary0604 := by decide +kernel

def insert0464_0604 : subdivide input0464.graph 4 3 16 ≃g input0604.graph where
  toEquiv :=
    { toFun := fun v => v.elim 10 (fun i => (![6, 7, 8, 9, 11, 12, 13, 0, 1, 2, 3, 4, 5, 16, 19, 18, 17, 15, 14, 22, 20, 21]) i)
      invFun := ![some 7, some 8, some 9, some 10, some 11, some 12, some 0, some 1, some 2, some 3, none, some 4, some 5, some 6, some 18, some 17, some 13, some 16, some 15, some 14, some 20, some 21, some 19]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  map_rel_iff' := by decide +kernel

theorem triangle0464_0604 : input0464.graph.Adj 4 3 ∧
    input0464.graph.Adj 4 16 ∧ input0464.graph.Adj 3 16 := by decide +kernel

theorem rotation0464_0604 : ∀ v : Option (Fin 22), ∃ shift : Fin 10,
    (stars0604 (insert0464_0604 v)).reverse =
      ((ConfigurationFaceGraph.triangleStar (fun x => (stars0464 x).reverse) 4 3 16 v).map insert0464_0604).rotate
        shift.val := by decide +kernel

theorem boundary0464_0604 :
    ((ConfigurationFaceGraph.triangleBoundary boundary0464 4).map insert0464_0604).rotate
      6 = boundary0604 := by decide +kernel

def insert3202_0604 : subdivide input3202.graph 5 4 16 ≃g input0604.graph where
  toEquiv :=
    { toFun := fun v => v.elim 12 (fun i => (![7, 8, 9, 10, 11, 13, 0, 1, 2, 3, 4, 5, 6, 19, 18, 17, 16, 22, 14, 20, 15, 21]) i)
      invFun := ![some 6, some 7, some 8, some 9, some 10, some 11, some 12, some 0, some 1, some 2, some 3, some 4, none, some 5, some 18, some 20, some 16, some 15, some 14, some 13, some 19, some 21, some 17]
      left_inv := by decide +kernel
      right_inv := by decide +kernel }
  map_rel_iff' := by decide +kernel

theorem triangle3202_0604 : input3202.graph.Adj 5 4 ∧
    input3202.graph.Adj 5 16 ∧ input3202.graph.Adj 4 16 := by decide +kernel

theorem rotation3202_0604 : ∀ v : Option (Fin 22), ∃ shift : Fin 10,
    (stars0604 (insert3202_0604 v)).reverse =
      ((ConfigurationFaceGraph.triangleStar (fun x => (stars3202 x).reverse) 5 4 16 v).map insert3202_0604).rotate
        shift.val := by decide +kernel

theorem boundary3202_0604 :
    ((ConfigurationFaceGraph.triangleBoundary boundary3202 5).map insert3202_0604).rotate
      7 = boundary0604 := by decide +kernel

/-- Both orders retain exactly the same source vertex in the upper graph. -/
theorem retained_square (v : Fin 21) :
    insert0464_0604 (some (insert0370_0464 (some v))) =
      insert0465_0604 (some (insert0370_0465 (some v))) := by
  revert v
  decide +kernel

end FourColor.NearLinearFiveData
