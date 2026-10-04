import MettapediaFourColor.StripPhaseObstruction
import MettapediaFourColor.GraphTriangulationEuler

/-!
# The phase obstruction on a degree-five-to-seven spherical triangulation

The source is the existing closing-flat-triangle example. Exact adjacency,
source stars, planar rotation and degree bounds are checked here. The
flat charges and short-cycle exclusions are independently replayed by the
program audit; they are not assumptions silently discharged by this module.

The same general routed obstruction used by the smaller disk applies to
this exterior. Two mixed-pair physical switches reconstruct all vertices.
-/

namespace FourColor.StripSpherePhase

open Color SimpleGraph
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

set_option maxRecDepth 10000

def star : Fin 162 → List (Fin 162) :=
  ![[13,106,46,44,45,43],
    [17,50,51,118,48],
    [22,54,55,56,127],
    [58,135,59,60,140,61],
    [30,62,65,31,66,64],
    [67,68,70,69,71],
    [22,73,75,76,72,123,119],
    [77,158,81,153,78,111],
    [82,85,86,131,84],
    [27,60,133,87,90,157,91],
    [92,141,95,94,93,142],
    [97,115,99,98,101,100],
    [15,105,47,104,103],
    [0,43,102,107,67,108,106],
    [44,110,112,77,109,45],
    [12,103,109,111,114,113,105],
    [46,106,115,116,110],
    [1,48,52,117,50],
    [49,121,122,107,104],
    [49,50,117,123,72,121],
    [83,125,118,105,113],
    [53,127,56,129,57,128,126],
    [2,127,53,73,6,119,54],
    [24,129,56,55,125,84,131],
    [23,131,132,134,87,133,129],
    [58,138,65,62,137,135],
    [57,59,135,139,74,130,128],
    [9,91,88,143,28,140,60],
    [27,143,92,136,61,140],
    [63,147,69,146,144],
    [4,64,148,75,139,137,62],
    [4,65,142,93,150,149,66],
    [63,66,149,152,151,145],
    [68,122,124,76,146,70],
    [69,147,145,99,108,71],
    [78,156,85,114,111],
    [79,155,89,156,153,81],
    [38,161,160,94,159,155,80],
    [37,80,112,110,116,97,161],
    [89,90,134,132,154],
    [88,91,159,95,141],
    [96,160,161,100,101],
    [43,45,109,103,102],
    [0,45,42,102,13],
    [0,46,110,14,45],
    [0,44,14,109,42,43],
    [0,106,16,110,44],
    [12,105,51,49,104],
    [1,118,120,52,17],
    [18,104,47,51,50,19,121],
    [1,17,117,19,49,51],
    [1,50,49,47,105,118],
    [17,48,120,54,119,117],
    [21,126,73,22,127],
    [2,22,119,52,120,55],
    [2,54,120,125,23,56],
    [2,55,23,129,21,127],
    [21,129,133,60,59,26,128],
    [3,61,136,138,25,135],
    [3,135,26,57,60],
    [3,59,57,133,9,27,140],
    [3,140,28,136,58],
    [4,30,137,25,65],
    [29,144,64,66,32,145,147],
    [4,66,63,144,148,30],
    [4,62,25,138,142,31],
    [4,31,149,32,63,64],
    [5,71,108,13,107,122,68],
    [5,67,122,33,70],
    [5,70,146,29,147,34,71],
    [5,68,33,146,69],
    [5,69,34,108,67],
    [6,76,124,121,19,123],
    [6,22,53,126,130,74,75],
    [26,139,75,73,130],
    [6,73,74,139,30,148,76],
    [6,75,148,146,33,124,72],
    [7,111,109,14,112,158],
    [7,153,156,35,111],
    [36,81,158,80,155],
    [37,155,79,158,112,38],
    [7,158,79,36,153],
    [8,84,83,114,85],
    [20,113,114,82,84,125],
    [8,131,23,125,83,82],
    [8,82,114,35,156,154,86],
    [8,85,154,132,131],
    [9,133,24,134,90],
    [27,91,40,141,143],
    [36,155,157,90,39,154,156],
    [9,87,134,39,89,157],
    [9,157,159,40,88,27],
    [10,142,136,28,143,141],
    [10,94,96,150,31,142],
    [10,95,159,37,160,96,93],
    [10,141,40,159,94],
    [41,101,150,93,94,160],
    [11,100,161,38,116,115],
    [11,99,151,152,101],
    [11,115,108,34,145,151,98],
    [11,101,41,161,97],
    [11,98,152,150,96,41,100],
    [13,43,42,103,104,107],
    [12,104,102,42,109,15],
    [12,47,49,18,107,102,103],
    [12,15,113,20,118,51,47],
    [0,13,108,115,16,46],
    [13,102,104,18,122,67],
    [13,67,71,34,99,115,106],
    [14,77,111,15,103,42,45],
    [14,44,46,16,116,38,112],
    [7,78,35,114,15,109,77],
    [14,110,38,80,158,77],
    [15,114,83,20,105],
    [15,111,35,85,82,83,113],
    [11,97,116,16,106,108,99],
    [16,115,97,38,110],
    [17,52,119,123,19,50],
    [1,51,105,20,125,120,48],
    [6,123,117,52,54,22],
    [48,118,125,55,54,52],
    [18,49,19,72,124,122],
    [18,121,124,33,68,67,107],
    [6,72,19,117,119],
    [33,122,121,72,76],
    [20,83,84,23,55,120,118],
    [21,128,130,73,53],
    [2,56,21,53,22],
    [21,57,26,130,126],
    [21,56,23,24,133,57],
    [26,74,73,126,128],
    [8,86,132,24,23,84],
    [24,131,86,154,39,134],
    [9,60,57,129,24,87],
    [24,132,39,90,87],
    [3,58,25,137,139,26,59],
    [28,92,142,138,58,61],
    [25,62,30,139,135],
    [25,58,136,142,65],
    [26,135,137,30,75,74],
    [3,60,27,28,61],
    [10,92,143,88,40,95],
    [10,93,31,65,138,136,92],
    [27,88,141,92,28],
    [29,146,148,64,63],
    [32,151,99,34,147,63],
    [29,69,70,33,76,148,144],
    [29,63,145,34,69],
    [30,64,144,146,76,75],
    [31,150,152,32,66],
    [31,93,96,101,152,149],
    [32,152,98,99,145],
    [32,149,150,101,98,151],
    [7,81,36,156,78],
    [39,132,86,85,156,89],
    [36,79,80,37,159,157,89],
    [35,78,153,36,89,154,85],
    [9,90,89,155,159,91],
    [7,77,112,80,79,81],
    [37,94,95,40,91,157,155],
    [37,161,41,96,94],
    [37,38,97,100,41,160]]

theorem star_symm : ∀ u, (star u).all (fun v => decide (u ∈ star v)) = true := by decide +kernel
theorem star_loopless : ∀ u, u ∉ star u := by decide +kernel

def ambient : SimpleGraph (Fin 162) where
  Adj u v := v ∈ star u
  symm := ⟨fun u v h => of_decide_eq_true (List.all_eq_true.mp (star_symm u) v h)⟩
  loopless := ⟨star_loopless⟩
instance : DecidableRel ambient.Adj := by unfold ambient; infer_instance

def includeExterior : Fin 154 → Fin 162 := ![0,1,2,3,4,5,6,7,8,9,10,12,13,14,15,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,98,99,101,102,103,104,105,107,108,109,110,111,112,113,114,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161]
def image : Fin 19 → Fin 162 := ![41,101,98,99,108,13,0,44,110,38,161,46,16,115,106,116,11,97,100]
def ports : Fin 11 → Fin 154 := ![39,96,94,95,102,12,0,42,104,36,153]

def neighbors : Fin 154 → List (Fin 154) :=
  ![[12,41,42,43],
    [15,45,47,48,110],
    [20,51,52,53,119],
    [55,56,57,58,127,132],
    [28,29,59,61,62,63],
    [64,65,66,67,68],
    [20,69,70,72,73,111,115],
    [74,75,78,105,145,150],
    [79,81,82,83,123],
    [25,57,84,87,88,125,149],
    [89,90,91,92,133,134],
    [14,44,98,99,100],
    [0,41,64,97,101,102],
    [42,43,74,103,104,106],
    [11,98,100,103,105,107,108],
    [1,45,47,49,109],
    [46,99,101,113,114],
    [46,47,69,109,113,115],
    [80,100,107,110,117],
    [50,53,54,118,119,120,121],
    [2,6,50,51,70,111,119],
    [22,52,53,81,117,121,123],
    [21,84,121,123,124,125,126],
    [55,59,62,127,129,130],
    [54,56,71,120,122,127,131],
    [9,26,57,85,88,132,135],
    [25,58,89,128,132,135],
    [60,66,136,138,139],
    [4,59,61,72,129,131,140],
    [4,62,63,90,134,141,142],
    [60,63,137,141,143,144],
    [65,67,73,114,116,138],
    [66,68,95,102,137,139],
    [75,82,105,108,148],
    [76,78,86,145,147,148],
    [36,77,91,147,151,152,153],
    [35,77,104,106,153],
    [86,87,124,126,146],
    [85,88,92,133,151],
    [93,96,152,153],
    [41,43,97,98,103],
    [0,12,40,43,97],
    [0,13,43,104],
    [0,13,40,41,42,103],
    [11,46,48,99,100],
    [1,15,49,110,112],
    [16,17,44,47,48,99,113],
    [1,15,17,46,48,109],
    [1,44,46,47,100,110],
    [15,45,51,109,111,112],
    [19,20,70,118,119],
    [2,20,49,52,111,112],
    [2,21,51,53,112,117],
    [2,19,21,52,119,121],
    [19,24,56,57,120,121,125],
    [3,23,58,127,128,130],
    [3,24,54,57,127],
    [3,9,25,54,56,125,132],
    [3,26,55,128,132],
    [4,23,28,62,129],
    [27,30,61,63,136,137,139],
    [4,28,60,63,136,140],
    [4,23,29,59,130,134],
    [4,29,30,60,61,141],
    [5,12,65,68,101,102,114],
    [5,31,64,67,114],
    [5,27,32,67,68,138,139],
    [5,31,65,66,138],
    [5,32,64,66,102],
    [6,17,73,113,115,116],
    [6,20,50,71,72,118,122],
    [24,70,72,122,131],
    [6,28,70,71,73,131,140],
    [6,31,69,72,116,138,140],
    [7,13,103,105,106,150],
    [7,33,105,145,148],
    [34,77,78,147,150],
    [35,36,76,106,147,150],
    [7,34,76,145,150],
    [8,80,81,82,108],
    [18,79,81,107,108,117],
    [8,21,79,80,117,123],
    [8,33,79,83,108,146,148],
    [8,82,123,124,146],
    [9,22,87,125,126],
    [25,38,88,133,135],
    [34,37,87,146,147,148,149],
    [9,37,84,86,126,149],
    [9,25,38,85,149,151],
    [10,26,128,133,134,135],
    [10,29,91,93,134,142],
    [10,35,90,92,93,151,152],
    [10,38,91,133,151],
    [39,90,91,96,142,152],
    [95,96,143,144],
    [32,94,102,137,143],
    [39,93,94,142,144],
    [12,40,41,98,99,101],
    [11,14,40,97,99,103],
    [11,16,44,46,97,98,101],
    [11,14,18,44,48,107,110],
    [12,16,64,97,99,114],
    [12,32,64,68,95],
    [13,14,40,43,74,98,105],
    [13,36,42,106],
    [7,14,33,74,75,103,108],
    [13,36,74,77,104,150],
    [14,18,80,100,108],
    [14,33,79,80,82,105,107],
    [15,17,47,49,111,115],
    [1,18,45,48,100,112,117],
    [6,20,49,51,109,115],
    [45,49,51,52,110,117],
    [16,17,46,69,114,116],
    [16,31,64,65,101,113,116],
    [6,17,69,109,111],
    [31,69,73,113,114],
    [18,21,52,80,81,110,112],
    [19,50,70,120,122],
    [2,19,20,50,53],
    [19,24,54,118,122],
    [19,21,22,53,54,125],
    [24,70,71,118,120],
    [8,21,22,81,83,124],
    [22,37,83,123,126,146],
    [9,22,54,57,84,121],
    [22,37,84,87,124],
    [3,23,24,55,56,129,131],
    [26,55,58,89,130,134],
    [23,28,59,127,131],
    [23,55,62,128,134],
    [24,28,71,72,127,129],
    [3,25,26,57,58],
    [10,38,85,89,92,135],
    [10,29,62,89,90,128,130],
    [25,26,85,89,133],
    [27,60,61,138,140],
    [30,32,60,95,139,143],
    [27,31,66,67,73,136,140],
    [27,32,60,66,137],
    [28,61,72,73,136,138],
    [29,30,63,142,144],
    [29,90,93,96,141,144],
    [30,94,95,137,144],
    [30,94,96,141,142,143],
    [7,34,75,78,148],
    [37,82,83,86,124,148],
    [34,35,76,77,86,149,151],
    [33,34,75,82,86,145,146],
    [9,86,87,88,147,151],
    [7,74,76,77,78,106],
    [35,38,88,91,92,147,149],
    [35,39,91,93,153],
    [35,36,39,152]]

theorem neighbor_symm : ∀ u, (neighbors u).all (fun v => decide (u ∈ neighbors v)) = true := by decide +kernel
theorem neighbor_loopless : ∀ u, u ∉ neighbors u := by decide +kernel

def exterior : SimpleGraph (Fin 154) where
  Adj u v := v ∈ neighbors u
  symm := ⟨fun u v h => of_decide_eq_true (List.all_eq_true.mp (neighbor_symm u) v h)⟩
  loopless := ⟨neighbor_loopless⟩
instance : DecidableRel exterior.Adj := by unfold exterior; infer_instance

def values : Fin 3 → Fin 154 → Color
  | 0 => ![c2,c0,c3,c3,c2,c1,c2,c3,c0,c1,c3,c2,c0,c2,c1,c2,c0,c2,c0,c0,c0,c0,c2,c3,c2,c3,c2,c1,c3,c3,c3,c3,c2,c3,c3,c1,c0,c2,c3,c0,c2,c3,c0,c1,c0,c3,c1,c3,c2,c1,c3,c2,c1,c2,c3,c2,c1,c2,c1,c1,c2,c1,c0,c0,c3,c0,c3,c2,c0,c0,c1,c3,c0,c1,c1,c1,c1,c2,c2,c3,c1,c2,c1,c2,c3,c1,c1,c0,c0,c1,c1,c0,c1,c3,c3,c0,c1,c1,c0,c3,c3,c2,c1,c3,c1,c2,c3,c2,c0,c0,c1,c3,c0,c3,c1,c1,c2,c3,c2,c1,c1,c1,c0,c1,c3,c0,c1,c0,c0,c2,c1,c1,c0,c2,c2,c0,c3,c1,c0,c0,c2,c1,c2,c2,c0,c0,c0,c0,c2,c3,c0,c2,c2,c3]
  | 1 => ![c2,c0,c3,c3,c0,c1,c2,c3,c2,c1,c3,c2,c0,c2,c1,c2,c0,c2,c0,c2,c0,c2,c0,c3,c0,c3,c0,c1,c3,c3,c3,c3,c0,c3,c3,c1,c2,c0,c3,c2,c2,c3,c0,c1,c0,c3,c1,c3,c2,c1,c3,c2,c1,c0,c3,c0,c1,c0,c1,c1,c0,c1,c2,c2,c3,c0,c3,c2,c2,c0,c1,c3,c0,c1,c1,c1,c1,c0,c0,c3,c1,c0,c1,c0,c3,c1,c1,c2,c2,c1,c1,c2,c1,c3,c3,c2,c1,c1,c0,c3,c3,c2,c1,c3,c1,c2,c3,c2,c0,c0,c1,c3,c0,c3,c1,c1,c2,c3,c0,c1,c1,c1,c2,c1,c3,c2,c1,c2,c2,c0,c1,c1,c2,c0,c0,c2,c3,c1,c0,c2,c2,c1,c0,c0,c2,c2,c2,c2,c0,c3,c2,c0,c0,c3]
  | 2 => ![c1,c0,c3,c3,c0,c1,c1,c3,c1,c2,c3,c1,c0,c1,c2,c1,c0,c1,c0,c1,c0,c1,c0,c3,c0,c3,c0,c1,c3,c3,c3,c3,c0,c3,c3,c2,c1,c0,c3,c1,c1,c3,c0,c2,c0,c3,c2,c3,c1,c2,c3,c1,c2,c0,c3,c0,c1,c0,c2,c2,c0,c2,c1,c1,c3,c0,c3,c2,c2,c0,c2,c3,c0,c2,c2,c2,c2,c0,c0,c3,c2,c0,c2,c0,c3,c2,c2,c1,c1,c2,c2,c1,c2,c3,c3,c2,c2,c2,c0,c3,c3,c1,c1,c3,c2,c1,c3,c1,c0,c0,c2,c3,c0,c3,c2,c2,c1,c3,c0,c2,c2,c2,c1,c2,c3,c1,c2,c2,c1,c0,c2,c1,c1,c0,c0,c1,c3,c1,c0,c2,c1,c2,c0,c0,c1,c1,c1,c1,c0,c3,c1,c0,c0,c3]

theorem proper_rows : ∀ s u, (neighbors u).all (fun v => decide (values s u ≠ values s v)) = true := by decide +kernel

def state (s : Fin 3) : exterior.Coloring Color :=
  .mk (values s) (fun {u} {v} h => of_decide_eq_true (List.all_eq_true.mp (proper_rows s u) v h))

def roots : Fin 6 → Fin 3 → Fin 154
  | 0 => ![39,95,39]
  | 1 => ![39,12,39]
  | 2 => ![39,12,42]
  | 3 => ![96,102,96]
  | 4 => ![96,102,153]
  | 5 => ![94,0,94]

def routeList : Fin 6 → Fin 11 → List (Fin 154)
  | 0 => ![[39],[39,96],[94],[95],[95,102],[95,102,12],[0],[95,102,12,97,98,14,108,82,146,86,147,35,36,104,42],[95,102,12,97,98,14,108,82,146,86,147,35,36,104],[95,102,12,97,98,14,108,82,146,86,147,35,36],[153]]
  | 1 => ![[39],[96],[94],[39,152,91,151,147,77,150,78,145,148,146,83,8,81,21,22,125,57,132,26,128,134,62,4,63,60,139,32,95],[102],[12],[12,0],[12,0,42],[104],[39,152,91,151,147,77,36],[153]]
  | 2 => ![[39],[96],[39,153,36,106,150,7,145,34,147,149,88,25,132,3,127,23,62,29,63,30,144,94],[39,153,36,106,150,7,145,34,147,149,88,25,132,3,127,23,62,29,63,30,144,94,95],[102],[12],[0],[42],[104],[39,153,36],[39,153]]
  | 3 => ![[39],[96],[94],[95],[102],[12],[102,32,137,60,61,140,73,116,114,101,97,40,43,0],[42],[102,32,137,60,61,140,73,116,114,101,97,40,43,13,104],[36],[153]]
  | 4 => ![[39],[96],[96,94],[95],[102],[12],[0],[42],[102,64,114,113,46,99,97,41,43,103,74,106,104],[36],[153]]
  | 5 => ![[39],[96],[94],[95],[102],[12],[0],[42],[104],[36],[94,143,30,60,136,140,28,4,29,142,93,152,153]]

def Active (s : Fin 6) (v : Fin 154) : Prop :=
  state 0 v = (StripPhaseObstruction.pair s).1 ∨ state 0 v = (StripPhaseObstruction.pair s).2
instance (s v) : Decidable (Active s v) := inferInstanceAs (Decidable (_ ∨ _))

theorem boundary : ∀ j, state 0 (ports j) = StripPhaseObstruction.state 0 (StripPhaseObstruction.ports j) := by decide +kernel
theorem route_nonempty : ∀ s j, routeList s j ≠ [] := by decide +kernel
theorem route_chain : ∀ s j, (routeList s j).IsChain exterior.Adj := by decide +kernel
theorem route_head : ∀ s j, Active s (ports j) →
    (routeList s j).head (route_nonempty s j) = roots s (StripPhaseObstruction.label s j) := by decide +kernel
theorem route_last : ∀ s j, (routeList s j).getLast (route_nonempty s j) = ports j := by decide +kernel
theorem route_active : ∀ s j, Active s (ports j) → ∀ x ∈ routeList s j, Active s x := by decide +kernel

theorem routes (s : Fin 6) (j : Fin 11) (h : Active s (ports j)) :
    ∃ p : exterior.Walk (roots s (StripPhaseObstruction.label s j)) (ports j),
      ∀ x ∈ p.support, Active s x := by
  let p := (Walk.ofSupport (routeList s j) (route_nonempty s j) (route_chain s j)).copy
    (route_head s j h) (route_last s j)
  exact ⟨p, fun x hx => route_active s j h x (by simpa [p] using hx)⟩

/-- All six unordered pairs, at arbitrary phase length, need two holes.
This invokes the previous general law rather than rechecking endpoints. -/
theorem phase_requires_two (s : Fin 6) (D : exterior.Coloring Color)
    (history : Relation.ReflTransGen (KempePairHistory.Step
      (StripPhaseObstruction.pair s).1 (StripPhaseObstruction.pair s).2) (state 0) D)
    {h : Finset (Fin 8)} {f : Fin 8 → Color}
    (valid : StripPartialColouring.ValidExcept (fun j => D (ports j)) h f) : 2 ≤ h.card :=
  StripPhaseObstruction.routed_requires_two (state 0) D ports s (roots s) boundary (routes s) history valid

private theorem pair_cases : ∀ a b : Color, a = b ∨
    ∃ s, (a = (StripPhaseObstruction.pair s).1 ∧ b = (StripPhaseObstruction.pair s).2) ∨
      (a = (StripPhaseObstruction.pair s).2 ∧ b = (StripPhaseObstruction.pair s).1) := by
  decide +kernel

/-- Reversed and equal pairs are included as well. -/
theorem any_phase_requires_two (a b : Color) (D : exterior.Coloring Color)
    (history : Relation.ReflTransGen (KempePairHistory.Step a b) (state 0) D)
    {h : Finset (Fin 8)} {f : Fin 8 → Color}
    (valid : StripPartialColouring.ValidExcept (fun j => D (ports j)) h f) : 2 ≤ h.card := by
  rcases pair_cases a b with rfl | ⟨s,he | he⟩
  · have eq : D = state 0 := by
      ext v
      simpa using KempePairHistory.pointwise history v
    subst D
    exact phase_requires_two 0 (state 0) .refl valid
  · rcases he with ⟨rfl,rfl⟩
    exact phase_requires_two s D history valid
  · rcases he with ⟨rfl,rfl⟩
    have pw : ∀ v, D v = state 0 v ∨ D v = Equiv.swap
        (StripPhaseObstruction.pair s).1 (StripPhaseObstruction.pair s).2 (state 0 v) := by
      simpa only [Equiv.swap_comm] using KempePairHistory.pointwise history
    obtain ⟨bits,hb⟩ := KempePhaseBoundary.endpoint (state 0) D _ _ pw
      ports (roots s) (StripPhaseObstruction.label s) (routes s)
    have eq : (fun j => D (ports j)) = StripPhaseObstruction.word s bits := by
      funext j
      simpa only [StripPhaseObstruction.word, boundary] using hb j
    rw [eq] at valid
    exact StripPhaseObstruction.two_holes s bits valid

def repairPair : Fin 2 → Color × Color := ![(c0,c2),(c1,c2)]
def repairChain : Fin 2 → List (Fin 154) := ![[4,62,134,128,26,132,57,125,22,21,53,19,118,122,24,127,55,127,129,127,24,122,118,19,53,21,81,8,83,146,37,87,37,146,148,145,78,150,77,36,77,147,151,88,151,91,152,39,152,91,151,147,77,150,78,145,148,146,83,8,81,21,22,125,57,132,26,135,133,135,26,128,134,62,4,63,60,139,32,68,32,95,143,144,142,144,143,95,32,139,60,63,4],[0,43,13,74,105,14,11,14,107,80,107,14,105,75,145,75,105,74,150,76,147,35,36,104,36,35,91,90,91,92,91,35,147,86,87,9,88,85,135,89,128,58,132,58,128,130,62,59,62,130,128,89,135,85,88,9,125,121,19,119,19,120,122,70,6,73,116,114,101,97,40,97,101,114,116,73,140,61,63,141,144,96,39,96,144,141,63,61,140,73,6,115,17,46,48,110,48,46,17,115,6,70,122,120,19,121,21,52,51,49,15,49,51,52,21,123,8,82,146,82,8,123,21,121,125,9,87,126,87,86,147,76,150,74,13,43,0]]
def repairRoot (t : Fin 2) : Fin 154 := (repairChain t).head!

theorem repair_checked : ∀ t,
    repairRoot t ∈ repairChain t ∧ (repairChain t).IsChain exterior.Adj ∧
    (∀ x ∈ repairChain t, state t.castSucc x = (repairPair t).1 ∨
      state t.castSucc x = (repairPair t).2) ∧
    (∀ x ∈ repairChain t, (neighbors x).all (fun y => decide
      ((state t.castSucc y = (repairPair t).1 ∨ state t.castSucc y = (repairPair t).2) → y ∈ repairChain t)) = true) ∧
    (∀ x, state t.succ x = if x ∈ repairChain t then
      Equiv.swap (repairPair t).1 (repairPair t).2 (state t.castSucc x)
      else state t.castSucc x) := by decide +kernel

def certificate (t : Fin 2) : KempeSeparatedChains.Certificate (state t.castSucc) (repairPair t).1 (repairPair t).2 where
  vertices := repairChain t
  root := repairRoot t
  root_mem := (repair_checked t).1
  connected := (repair_checked t).2.1
  active := (repair_checked t).2.2.1
  closed := by
    intro x hx y edge active
    exact of_decide_eq_true (List.all_eq_true.mp ((repair_checked t).2.2.2.1 x hx) y edge) active

theorem repair_eq (t : Fin 2) : (certificate t).swap = state t.succ := by
  ext x
  rw [KempeSeparatedChains.Certificate.swap_apply]
  exact ((repair_checked t).2.2.2.2 x).symm

noncomputable def repairStep (t : Fin 2) : Step (state t.castSucc) (state t.succ) :=
  repair_eq t ▸ (certificate t).step
noncomputable def repairHistory : History (state 0) (state 2) :=
  .cons (repairStep 0) (.cons (repairStep 1) (.refl _))
theorem repair_length : repairHistory.length = 2 := rfl

def finalValues : Fin 162 → Color := ![c1,c0,c3,c3,c0,c1,c1,c3,c1,c2,c3,c1,c1,c0,c1,c2,c1,c1,c0,c1,c0,c1,c0,c1,c0,c3,c0,c3,c0,c1,c3,c3,c3,c3,c0,c3,c3,c2,c1,c0,c3,c1,c1,c3,c0,c2,c3,c0,c3,c2,c3,c1,c2,c3,c1,c2,c0,c3,c0,c1,c0,c2,c2,c0,c2,c1,c1,c3,c0,c3,c2,c2,c0,c2,c3,c0,c2,c2,c2,c2,c0,c0,c3,c2,c0,c2,c0,c3,c2,c2,c1,c1,c2,c2,c1,c2,c3,c2,c3,c2,c0,c2,c2,c0,c3,c3,c2,c1,c1,c3,c2,c1,c3,c1,c0,c0,c3,c0,c2,c3,c0,c3,c2,c2,c1,c3,c0,c2,c2,c2,c1,c2,c3,c1,c2,c2,c1,c0,c2,c1,c1,c0,c0,c1,c3,c1,c0,c2,c1,c2,c0,c0,c1,c1,c1,c1,c0,c3,c1,c0,c0,c3]

theorem final_proper : ∀ u, (star u).all (fun v => decide (finalValues u ≠ finalValues v)) = true := by decide +kernel

def finalColouring : ambient.Coloring Color :=
  .mk finalValues (fun {u} {v} h => of_decide_eq_true (List.all_eq_true.mp (final_proper u) v h))
theorem reconstructed : ∀ v, finalColouring (includeExterior v) = state 2 v := by decide +kernel

end FourColor.StripSpherePhase
