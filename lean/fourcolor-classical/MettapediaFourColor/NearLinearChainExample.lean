import MettapediaFourColor.NearLinearChainRepair
import MettapediaFourColor.PatchBoundaryGluing
import MettapediaFourColor.GraphTraceAlignment

/-!
# A three-triangle chain in a concrete neighbourhood

These cyclic stars come from the 42-vertex triangulation in
chain-profile-example.json. The five internal stars of D0004 are complete,
all thirteen source vertices have distinct images, and its entire ring is
retained. The generic patch theorem glues genuine compatible colourings.

Flat charge, sphericality and absence of short separating cycles are checked
by the independent program record. They are not conclusions of this module.
The repair consumer keeps actual exterior Kempe closure and a starting
exterior colouring as explicit hypotheses.
-/

namespace FourColor.NearLinearChainExample

open NearLinearChainData KempeBoundarySplit

set_option maxRecDepth 65536

def rowSource (v : Fin 42) : String :=
  match v.val with
  | 0 => "12 16 34 20 23 15\n"
  | 1 => "20 41 33 29 32 36 23\n"
  | 2 => "15 23 27 40 28 17\n"
  | 3 => "5 31 25 26 38 35\n"
  | 4 => "11 41 34 13 40\n"
  | 5 => "3 35 14 37 31\n"
  | 6 => "11 18 37 33 41\n"
  | 7 => "18 27 36 25 31\n"
  | 8 => "19 22 39 24 21\n"
  | 9 => "14 35 38 32 29\n"
  | 10 => "15 17 22 19 30\n"
  | 11 => "4 40 18 6 41\n"
  | 12 => "0 15 30 21 16\n"
  | 13 => "4 34 16 24 39 40\n"
  | 14 => "5 35 9 29 37\n"
  | 15 => "0 23 2 17 10 30 12\n"
  | 16 => "0 12 21 24 13 34\n"
  | 17 => "2 28 22 10 15\n"
  | 18 => "6 11 40 27 7 31 37\n"
  | 19 => "8 21 30 10 22\n"
  | 20 => "0 34 41 1 23\n"
  | 21 => "8 24 16 12 30 19\n"
  | 22 => "8 19 10 17 28 39\n"
  | 23 => "0 20 1 36 27 2 15\n"
  | 24 => "8 39 13 16 21\n"
  | 25 => "3 31 7 36 26\n"
  | 26 => "3 25 36 32 38\n"
  | 27 => "2 23 36 7 18 40\n"
  | 28 => "2 40 39 22 17\n"
  | 29 => "1 33 37 14 9 32\n"
  | 30 => "10 19 21 12 15\n"
  | 31 => "3 5 37 18 7 25\n"
  | 32 => "1 29 9 38 26 36\n"
  | 33 => "1 41 6 37 29\n"
  | 34 => "0 16 13 4 41 20\n"
  | 35 => "3 38 9 14 5\n"
  | 36 => "1 32 26 25 7 27 23\n"
  | 37 => "5 14 29 33 6 18 31\n"
  | 38 => "3 26 32 9 35\n"
  | 39 => "8 22 28 40 13 24\n"
  | 40 => "2 27 18 11 4 13 39 28\n"
  | 41 => "1 20 34 4 11 6 33\n"
  | _ => ""

def star (v : Fin 42) : List (Fin 42) :=
  ((NearLinearDiamondData.rows (rowSource v)).headD []).map fun n => ⟨n % 42, by omega⟩

private theorem symmetric : ∀ u v : Fin 42, v ∈ star u → u ∈ star v := by decide +kernel
private theorem loopless : ∀ v : Fin 42, v ∉ star v := by decide +kernel

def graph : SimpleGraph (Fin 42) where
  Adj u v := v ∈ star u
  symm := ⟨symmetric⟩
  loopless := ⟨loopless⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ star _))

def image : Fin 13 → Fin 42 := ![2, 40, 13, 16, 21, 19, 10, 17, 24, 39, 8, 22, 28]

def occurrence : input0004.graph →g graph where
  toFun := image
  map_rel' := by decide +kernel

theorem injective : Function.Injective occurrence := by decide +kernel

/-- Every cyclic core star is literally present, including all exterior attachments. -/
theorem core_stars : ∀ i : Fin 5, ∃ shift : Fin 8,
    star (image (i.natAdd 8)) =
      ((input0004.internalStar (i.natAdd 8)).map image).rotate shift.val := by decide +kernel

def interior : Set (Fin 13) := {v | 8 ≤ v.val}

/-- No unrecorded ambient edge touches the five-vertex interior. -/
theorem covers : ∀ i : Fin 13, i ∈ interior → ∀ v, graph.Adj (occurrence i) v →
    ∃ a, input0004.graph.Adj i a ∧ occurrence a = v := by
  change ∀ i : Fin 13, 8 ≤ i.val → ∀ v, graph.Adj (occurrence i) v →
    ∃ a, input0004.graph.Adj i a ∧ occurrence a = v
  decide +kernel

theorem no_capture (a : Fin 13) (ha : a ∉ interior) :
    occurrence a ∉ occurrence '' interior := by
  rintro ⟨b, hb, he⟩
  exact ha ((injective he) ▸ hb)

def ProperExterior (outside : Fin 42 → Color) : Prop :=
  ∀ {v w}, v ∉ occurrence '' interior → w ∉ occurrence '' interior →
    graph.Adj v w → outside v ≠ outside w

def ExteriorTrace (et : List Color) : Prop :=
  ∃ outside : Fin 42 → Color, ProperExterior outside ∧
    et = trace (boundary0004.map fun p => outside (occurrence p))

/-- A joint compatible assignment reconstructs while fixing the full exterior. -/
theorem glue {C : Type*} (inside : input0004.graph.Coloring C) (outside : Fin 42 → C)
    (proper : ∀ {v w}, v ∉ occurrence '' interior → w ∉ occurrence '' interior →
      graph.Adj v w → outside v ≠ outside w)
    (agree : ∀ a, a ∉ interior → inside a = outside (occurrence a)) :
    ∃ k : graph.Coloring C, (∀ a, k (occurrence a) = inside a) ∧
      ∀ v, v ∉ occurrence '' interior → k v = outside v :=
  PatchBoundaryGluing.reconstruct occurrence interior injective.injOn no_capture covers
    inside outside proper agree

/-- The transferred repair is consumed by this actual graph. The remaining
exterior hypotheses are explicit; no Four Colour theorem is invoked. -/
theorem repair_actual (closed : KempeClosed ExteriorTrace)
    (et : List Color) (length : et.length = 8) (proper : (0 : Color) ∉ et)
    (conserved : et.sum = 0) (initial : ExteriorTrace et) :
    Nonempty (graph.Coloring Color) := by
  obtain ⟨es, ⟨inside, hins⟩, outside, hout, hext⟩ :=
    NearLinearChainRepair.repair0004 et length proper conserved ExteriorTrace closed initial
  obtain ⟨shifted, he⟩ := GraphTraceAlignment.align boundary0004 inside
    (boundary0004.map fun p => outside (occurrence p)) (by simp) (hins.symm.trans hext)
  have boundary_mem : ∀ a : Fin 13, a ∉ interior → a ∈ boundary0004 := by
    change ∀ a : Fin 13, ¬ 8 ≤ a.val → a ∈ boundary0004
    decide +kernel
  obtain ⟨k, _, _⟩ := glue shifted outside hout (by
    intro a ha
    exact (List.map_eq_map_iff.mp he) _ (boundary_mem a ha))
  exact ⟨k⟩

end FourColor.NearLinearChainExample
