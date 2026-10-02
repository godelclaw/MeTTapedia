import MettapediaFourColor.RulePairDiamond

/-!
# A nonempty instance of the shared charge-rule reduction pattern

The cyclic stars below are the exact rotation of the saved 42-vertex
flat-pair experiment. This data module checks local inverse laws and explicit witnesses joining
any two entries in a cyclic star. RulePairExample constructs the rotation,
checks triangularity and the two full rule readings, and consumes the
general mixed-diamond theorem. Flat charges, sphericality and the flip
history remain separate program evidence in flat-pair-probe.json.
-/

namespace FourColor.RulePairExample

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation

set_option maxRecDepth 65536

local instance (r : Fin 84) : NeZero (NearLinearRuleData.size r) :=
  ⟨by have := (NearLinearRuleData.headers r).1; omega⟩

set_option linter.style.longLine false in
def source : String := "21 24 33 22 34\n5 19 13 23 26\n3 25 26 23 17 15\n2 15 35 18 25\n6 30 32 9 16\n1 26 25 18 28 19\n4 16 37 31 30\n11 36 27 40 18\n14 35 15 20 24 21\n4 32 39 36 11 16\n12 29 28 40 37 16 22 33\n7 18 35 14 34 16 9 36\n10 33 20 17 23 13 29\n1 19 29 12 23\n8 21 34 11 35\n2 17 20 8 35 3\n4 9 11 34 22 10 37 6\n2 23 12 20 15\n3 35 11 7 40 28 5 25\n1 5 28 29 13\n8 15 17 12 33 24\n0 34 14 8 24\n0 33 10 16 34\n1 13 12 17 2 26\n0 21 8 20 33\n2 3 18 5 26\n1 23 2 25 5\n7 36 39 38 40\n5 18 40 10 29 19\n10 12 13 19 28\n4 6 31 41 32\n6 37 40 38 41 30\n4 30 41 39 9\n0 24 20 12 10 22\n0 22 16 11 14 21\n3 15 8 14 11 18\n7 11 9 39 27\n6 16 10 40 31\n27 39 41 31 40\n9 32 41 38 27 36\n7 27 38 31 37 10 28 18\n30 31 38 39 32\n"

/-- Row-local flat encodings avoid repeatedly parsing unrelated stars. -/
def rowSource (u : Fin 42) : String :=
  match u.val with
  | 0 => "21 24 33 22 34\n"
  | 1 => "5 19 13 23 26\n"
  | 2 => "3 25 26 23 17 15\n"
  | 3 => "2 15 35 18 25\n"
  | 4 => "6 30 32 9 16\n"
  | 5 => "1 26 25 18 28 19\n"
  | 6 => "4 16 37 31 30\n"
  | 7 => "11 36 27 40 18\n"
  | 8 => "14 35 15 20 24 21\n"
  | 9 => "4 32 39 36 11 16\n"
  | 10 => "12 29 28 40 37 16 22 33\n"
  | 11 => "7 18 35 14 34 16 9 36\n"
  | 12 => "10 33 20 17 23 13 29\n"
  | 13 => "1 19 29 12 23\n"
  | 14 => "8 21 34 11 35\n"
  | 15 => "2 17 20 8 35 3\n"
  | 16 => "4 9 11 34 22 10 37 6\n"
  | 17 => "2 23 12 20 15\n"
  | 18 => "3 35 11 7 40 28 5 25\n"
  | 19 => "1 5 28 29 13\n"
  | 20 => "8 15 17 12 33 24\n"
  | 21 => "0 34 14 8 24\n"
  | 22 => "0 33 10 16 34\n"
  | 23 => "1 13 12 17 2 26\n"
  | 24 => "0 21 8 20 33\n"
  | 25 => "2 3 18 5 26\n"
  | 26 => "1 23 2 25 5\n"
  | 27 => "7 36 39 38 40\n"
  | 28 => "5 18 40 10 29 19\n"
  | 29 => "10 12 13 19 28\n"
  | 30 => "4 6 31 41 32\n"
  | 31 => "6 37 40 38 41 30\n"
  | 32 => "4 30 41 39 9\n"
  | 33 => "0 24 20 12 10 22\n"
  | 34 => "0 22 16 11 14 21\n"
  | 35 => "3 15 8 14 11 18\n"
  | 36 => "7 11 9 39 27\n"
  | 37 => "6 16 10 40 31\n"
  | 38 => "27 39 41 31 40\n"
  | 39 => "9 32 41 38 27 36\n"
  | 40 => "7 27 38 31 37 10 28 18\n"
  | 41 => "30 31 38 39 32\n"
  | _ => ""

/-- Every cached row is the corresponding row of the complete source. -/
theorem row_source_exact : ∀ u : Fin 42,
    (NearLinearDiamondData.rows (rowSource u)).headD [] =
      (NearLinearDiamondData.rows source).getD u.val [] := by decide +kernel

def star (u : Fin 42) : List (Fin 42) :=
  ((NearLinearDiamondData.rows (rowSource u)).headD []).map fun n => ⟨n % 42, by omega⟩

set_option maxRecDepth 65536 in
private theorem symmetric : ∀ u v : Fin 42, v ∈ star u → u ∈ star v := by
  decide +kernel

set_option maxRecDepth 65536 in
private theorem loopless : ∀ u : Fin 42, u ∉ star u := by decide +kernel

def graph : SimpleGraph (Fin 42) where
  Adj u v := v ∈ star u
  symm := ⟨symmetric⟩
  loopless := ⟨loopless⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ star _))
instance : graph.LocallyFinite := fun v => Subtype.fintype (fun w => graph.Adj v w)

def next (u v : Fin 42) : Fin 42 :=
  (star u).getD (((star u).idxOf v + 1) % (star u).length) 0

def prev (u v : Fin 42) : Fin 42 :=
  (star u).getD (((star u).idxOf v + (star u).length - 1) % (star u).length) 0

set_option maxRecDepth 65536 in
theorem step_laws : ∀ u v : Fin 42, graph.Adj u v →
    graph.Adj u (next u v) ∧ graph.Adj u (prev u v) ∧
    prev u (next u v) = v ∧ next u (prev u v) = v := by decide +kernel

def walk (u : Fin 42) : ℕ → Fin 42 → Fin 42
  | 0, v => v
  | n + 1, v => next u (walk u n v)

set_option maxHeartbeats 0 in
-- Kernel evaluation of all finite reachability witnesses.
theorem reaches : ∀ u : Fin 42,
    (star u).all (fun v => (star u).all (fun w =>
      decide (walk u (((star u).idxOf w + (star u).length - (star u).idxOf v) %
        (star u).length) v = w))) = true := by
  intro u
  fin_cases u <;> decide +kernel

end FourColor.RulePairExample
