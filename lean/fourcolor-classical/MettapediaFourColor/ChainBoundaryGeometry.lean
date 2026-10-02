import MettapediaFourColor.RuleChainRecognition

/-! Exact cyclic geometry for the 162-vertex boundary-continuation example.
Global sphericality and short-cycle conditions remain separate program checks;
local inverse laws, cyclicity and triangularity are certified here. -/

namespace FourColor.ChainBoundaryExample

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ChainCoreReading LocalCoverageAssembly

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- The cyclic stars are reversed to match the chain construction. -/
def rowSource (v : Fin 162) : String :=
  match v.val with
  | 0 => "42 45 44 43 102\n"
  | 1 => "47 49 48 118 51\n"
  | 2 => "52 54 126 53 56 55\n"
  | 3 => "57 59 58 61 60\n"
  | 4 => "62 64 63 66 65\n"
  | 5 => "67 71 69 70 68 107\n"
  | 6 => "72 76 148 75 73\n"
  | 7 => "77 78 79 80 158 81\n"
  | 8 => "82 83 84 86 85\n"
  | 9 => "24 87 88 91 89 90\n"
  | 10 => "92 150 96 94 95\n"
  | 11 => "97 116 100 101 98 151 99\n"
  | 12 => "42 102 104 47 105\n"
  | 13 => "43 44 106 108 67 107\n"
  | 14 => "35 77 112 110 109 111\n"
  | 15 => "45 103 113 83 82 114 109\n"
  | 16 => "46 110 112 116 97 115 106\n"
  | 17 => "48 117 119 52 120 118\n"
  | 18 => "19 49 104 107 68 121\n"
  | 19 => "18 121 124 72 50 49\n"
  | 20 => "47 51 125 83 113 105\n"
  | 21 => "53 128 59 57 129 127\n"
  | 22 => "54 119 123 73 130\n"
  | 23 => "55 56 131 132 84\n"
  | 24 => "9 90 134 131 56 87\n"
  | 25 => "62 138 136 135 137\n"
  | 26 => "58 59 128 126 74 139 135\n"
  | 27 => "60 140 88 133 129\n"
  | 28 => "61 142 93 92 143 140\n"
  | 29 => "63 144 69 147 145\n"
  | 30 => "63 64 139 148 144\n"
  | 31 => "65 149 150 93 142\n"
  | 32 => "41 152 149 66 63 145 151 98\n"
  | 33 => "69 146 76 122 70\n"
  | 34 => "71 108 106 115 99 151 145 147\n"
  | 35 => "14 111 85 154 153 78 77\n"
  | 36 => "89 157 155 153 156\n"
  | 37 => "80 159 94 160 158\n"
  | 38 => "81 158 161 101 100 112\n"
  | 39 => "90 156 154 132 134\n"
  | 40 => "91 141 143 159 157\n"
  | 41 => "32 98 101 161 160 96 152\n"
  | 42 => "0 102 12 105 103 45\n"
  | 43 => "0 44 13 107 104 102\n"
  | 44 => "0 45 109 46 106 13 43\n"
  | 45 => "0 42 103 15 109 44\n"
  | 46 => "16 106 44 109 110\n"
  | 47 => "1 51 20 105 12 104 49\n"
  | 48 => "1 49 50 117 17 118\n"
  | 49 => "1 47 104 18 19 50 48\n"
  | 50 => "19 72 123 117 48 49\n"
  | 51 => "1 118 125 20 47\n"
  | 52 => "2 55 120 17 119 54\n"
  | 53 => "2 126 128 21 127 56\n"
  | 54 => "2 52 119 22 130 126\n"
  | 55 => "2 56 23 84 120 52\n"
  | 56 => "2 53 127 87 24 131 23 55\n"
  | 57 => "3 60 129 21 59\n"
  | 58 => "3 59 26 135 61\n"
  | 59 => "3 57 21 128 26 58\n"
  | 60 => "3 61 140 27 129 57\n"
  | 61 => "3 58 135 136 142 28 140 60\n"
  | 62 => "4 65 138 25 137 64\n"
  | 63 => "4 64 30 144 29 145 32 66\n"
  | 64 => "4 62 137 139 30 63\n"
  | 65 => "4 66 149 31 142 138 62\n"
  | 66 => "4 63 32 149 65\n"
  | 67 => "5 107 13 108 71\n"
  | 68 => "5 70 122 121 18 107\n"
  | 69 => "5 71 147 29 144 146 33 70\n"
  | 70 => "5 69 33 122 68\n"
  | 71 => "5 67 108 34 147 69\n"
  | 72 => "6 73 123 50 19 124 76\n"
  | 73 => "6 75 74 130 22 123 72\n"
  | 74 => "26 126 130 73 75 139\n"
  | 75 => "6 148 139 74 73\n"
  | 76 => "6 72 124 122 33 146 148\n"
  | 77 => "7 81 112 14 35 78\n"
  | 78 => "7 77 35 153 79\n"
  | 79 => "7 78 153 155 80\n"
  | 80 => "7 79 155 157 159 37 158\n"
  | 81 => "7 158 38 112 77\n"
  | 82 => "8 85 114 15 83\n"
  | 83 => "8 82 15 113 20 125 120 84\n"
  | 84 => "8 83 120 55 23 132 86\n"
  | 85 => "8 86 154 35 111 114 82\n"
  | 86 => "8 84 132 154 85\n"
  | 87 => "9 24 56 127 133 88\n"
  | 88 => "9 87 133 27 140 141 91\n"
  | 89 => "9 91 157 36 156 90\n"
  | 90 => "9 89 156 39 134 24\n"
  | 91 => "9 88 141 40 157 89\n"
  | 92 => "10 95 143 28 93 150\n"
  | 93 => "28 142 31 150 92\n"
  | 94 => "10 96 160 37 159 95\n"
  | 95 => "10 94 159 143 92\n"
  | 96 => "10 150 152 41 160 94\n"
  | 97 => "11 99 115 16 116\n"
  | 98 => "11 101 41 32 151\n"
  | 99 => "11 151 34 115 97\n"
  | 100 => "11 116 112 38 101\n"
  | 101 => "11 100 38 161 41 98\n"
  | 102 => "0 43 104 12 42\n"
  | 103 => "15 45 42 105 113\n"
  | 104 => "12 102 43 107 18 49 47\n"
  | 105 => "12 47 20 113 103 42\n"
  | 106 => "13 44 46 16 115 34 108\n"
  | 107 => "5 68 18 104 43 13 67\n"
  | 108 => "13 106 34 71 67\n"
  | 109 => "14 110 46 44 45 15 114 111\n"
  | 110 => "14 112 16 46 109\n"
  | 111 => "14 109 114 85 35\n"
  | 112 => "14 77 81 38 100 116 16 110\n"
  | 113 => "15 103 105 20 83\n"
  | 114 => "15 82 85 111 109\n"
  | 115 => "16 97 99 34 106\n"
  | 116 => "11 97 16 112 100\n"
  | 117 => "17 48 50 123 119\n"
  | 118 => "1 48 17 120 125 51\n"
  | 119 => "17 117 123 22 54 52\n"
  | 120 => "17 52 55 84 83 125 118\n"
  | 121 => "18 68 122 124 19\n"
  | 122 => "33 76 124 121 68 70\n"
  | 123 => "22 119 117 50 72 73\n"
  | 124 => "19 121 122 76 72\n"
  | 125 => "20 51 118 120 83\n"
  | 126 => "2 54 130 74 26 128 53\n"
  | 127 => "21 129 133 87 56 53\n"
  | 128 => "21 53 126 26 59\n"
  | 129 => "21 57 60 27 133 127\n"
  | 130 => "22 73 74 126 54\n"
  | 131 => "23 56 24 134 132\n"
  | 132 => "23 131 134 39 154 86 84\n"
  | 133 => "27 88 87 127 129\n"
  | 134 => "24 90 39 132 131\n"
  | 135 => "25 136 61 58 26 139 137\n"
  | 136 => "25 138 142 61 135\n"
  | 137 => "25 135 139 64 62\n"
  | 138 => "25 62 65 142 136\n"
  | 139 => "26 74 75 148 30 64 137 135\n"
  | 140 => "27 60 61 28 143 141 88\n"
  | 141 => "40 91 88 140 143\n"
  | 142 => "28 61 136 138 65 31 93\n"
  | 143 => "28 92 95 159 40 141 140\n"
  | 144 => "29 63 30 148 146 69\n"
  | 145 => "29 147 34 151 32 63\n"
  | 146 => "33 69 144 148 76\n"
  | 147 => "29 69 71 34 145\n"
  | 148 => "6 76 146 144 30 139 75\n"
  | 149 => "31 65 66 32 152 150\n"
  | 150 => "10 92 93 31 149 152 96\n"
  | 151 => "11 98 32 145 34 99\n"
  | 152 => "32 41 96 150 149\n"
  | 153 => "35 154 156 36 155 79 78\n"
  | 154 => "35 85 86 132 39 156 153\n"
  | 155 => "36 157 80 79 153\n"
  | 156 => "36 153 154 39 90 89\n"
  | 157 => "36 89 91 40 159 80 155\n"
  | 158 => "7 80 37 160 161 38 81\n"
  | 159 => "37 80 157 40 143 95 94\n"
  | 160 => "37 94 96 41 161 158\n"
  | 161 => "38 158 160 41 101\n"
  | _ => ""

def star (v : Fin 162) : List (Fin 162) :=
  ((NearLinearDiamondData.rows (rowSource v)).headD []).map fun n => ⟨n % 162, by omega⟩

private theorem symmetric : ∀ u v : Fin 162, v ∈ star u → u ∈ star v := by decide +kernel
private theorem loopless : ∀ v : Fin 162, v ∉ star v := by decide +kernel

def graph : SimpleGraph (Fin 162) where
  Adj u v := v ∈ star u
  symm := ⟨symmetric⟩
  loopless := ⟨loopless⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ star _))
instance : graph.LocallyFinite := fun v => Subtype.fintype (fun w => graph.Adj v w)

def next (u v : Fin 162) : Fin 162 :=
  (star u).getD (((star u).idxOf v + 1) % (star u).length) 0

def prev (u v : Fin 162) : Fin 162 :=
  (star u).getD (((star u).idxOf v + (star u).length - 1) % (star u).length) 0

theorem step_laws : ∀ u v : Fin 162, graph.Adj u v →
    graph.Adj u (next u v) ∧ graph.Adj u (prev u v) ∧
    prev u (next u v) = v ∧ next u (prev u v) = v := by decide +kernel

def walk (u : Fin 162) : ℕ → Fin 162 → Fin 162
  | 0, v => v
  | n + 1, v => next u (walk u n v)

theorem reaches : ∀ u : Fin 162,
    (star u).all (fun v => (star u).all (fun w =>
      decide (walk u (((star u).idxOf w + (star u).length - (star u).idxOf v) %
        (star u).length) v = w))) = true := by
  intro u
  fin_cases u <;> decide +kernel

def rotation : Data graph where
  vertexRotation := {
    toFun := fun d => ⟨(d.fst, next d.fst d.snd), (step_laws d.fst d.snd d.adj).1⟩
    invFun := fun d => ⟨(d.fst, prev d.fst d.snd), (step_laws d.fst d.snd d.adj).2.1⟩
    left_inv := fun d => SimpleGraph.Dart.ext (G := graph) _ _
      (Prod.ext rfl (step_laws d.fst d.snd d.adj).2.2.1)
    right_inv := fun d => SimpleGraph.Dart.ext (G := graph) _ _
      (Prod.ext rfl (step_laws d.fst d.snd d.adj).2.2.2) }
  vertexRotation_fst := fun _ => rfl
  outer := ⟨(112, 81), by decide +kernel⟩

private theorem pow_reading (n : ℕ) (d : graph.Dart) :
    ((rotation.vertexRotation ^ n) d).fst = d.fst ∧
    ((rotation.vertexRotation ^ n) d).snd = walk d.fst n d.snd := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    simp only [pow_succ', Equiv.Perm.mul_apply]
    exact ⟨ih.1, by change next _ _ = _; rw [ih.1, ih.2]; rfl⟩

/-- All outgoing darts at each vertex form one rotation cycle. -/
theorem cyclic : rotation.IsVertexwiseCyclic := by
  intro u
  refine ⟨⟨?_, rotation.vertexRotation.injective.injOn, ?_⟩, ?_⟩
  · intro d hd
    exact (rotation.vertexRotation_fst d).trans hd
  · intro d hd
    exact ⟨rotation.vertexRotation.symm d, hd, Equiv.apply_symm_apply _ d⟩
  · intro x hx y hy
    have xmem : x.snd ∈ star u := hx ▸ x.adj
    have ymem : y.snd ∈ star u := hy ▸ y.adj
    have h := (List.all_eq_true.mp ((List.all_eq_true.mp (reaches u)) x.snd xmem))
      y.snd ymem
    let n := ((star u).idxOf y.snd + (star u).length - (star u).idxOf x.snd) %
      (star u).length
    have hn' : walk u n x.snd = y.snd := of_decide_eq_true h
    refine ⟨(n : ℤ), ?_⟩
    rw [zpow_natCast]
    apply SimpleGraph.Dart.ext
    exact Prod.ext ((pow_reading n x).1.trans (hx.trans hy.symm))
      ((pow_reading n x).2.trans (by rwa [hx]))

/-- Every facial return closes after the three oriented triangle steps. -/
theorem triangular : ExceptionalOverlap.Triangular rotation := by
  unfold ExceptionalOverlap.Triangular
  decide +kernel

end FourColor.ChainBoundaryExample
