import MettapediaFourColor.StripSixJointRepair
import MettapediaFourColor.StripChainRepair

/-! # A boundary-domain obstruction for every single internal contraction

Three nonextending boundary words give counterexamples for all thirteen
internal edges of D0099. Each counterexample colours the actual eighteen-
vertex quotient. Its boundary neither extends to the source nor matches
one of the currently certified joint/chain stages under an edge palette.

This excludes a single internal contraction as a supplier of that existing
repair domain. It does not exclude further recolouring, other replacements,
or compositional reducibility. The pinned source is inherited from
TriangleStripAnchors; the ninety-one colour digits are checked witnesses
for this obstruction, not a reducibility table.
-/

namespace FourColor.StripContractionSupply

open SimpleGraph Color TriangleStripAnchors StripResponseSummary

set_option maxRecDepth 10000

def edge : Fin 13 → Fin 19 × Fin 19 :=
  ![(11,12),(11,14),(12,13),(12,14),(12,15),(13,14),(13,15),(13,16),(13,17),(15,17),(16,17),(16,18),(17,18)]

theorem edge_bounds : ∀ e, 11 ≤ (edge e).1.val ∧
    (edge e).1.val < (edge e).2.val := by decide +kernel

theorem edge_valid : ∀ e, input0099.graph.Adj (edge e).1 (edge e).2 := by decide +kernel

theorem edges_complete : ∀ u v : Fin 19, 11 ≤ u.val → 11 ≤ v.val →
    input0099.graph.Adj u v → ∃ e, edge e = (u,v) ∨ edge e = (v,u) := by decide +kernel

/-- Merge the right endpoint into the left, then remove its old label. -/
def collapse (e : Fin 13) (v : Fin 19) : Fin 18 :=
  ⟨if v.val = (edge e).2.val then (edge e).1.val
    else if v.val < (edge e).2.val then v.val else v.val - 1, by
    have h := edge_bounds e
    have right := (edge e).2.isLt
    have value := v.isLt
    split_ifs <;> omega⟩

theorem collapse_surjective : ∀ e, Function.Surjective (collapse e) := by
  change ∀ e w, ∃ v, collapse e v = w
  decide +kernel

theorem collapse_fibres : ∀ e u v, collapse e u = collapse e v ↔
    u = v ∨ (u = (edge e).1 ∧ v = (edge e).2) ∨
      (u = (edge e).2 ∧ v = (edge e).1) := by decide +kernel

def quotient (e : Fin 13) : SimpleGraph (Fin 18) := input0099.graph.map (collapse e)

def boundary : Fin 3 → Boundary
  | 0 => ![c0,c1,c2,c1,c0,c3,c0,c2,c0,c2,c3]
  | 1 => ![c0,c1,c0,c1,c2,c0,c1,c2,c3,c2,c1]
  | 2 => ![c0,c1,c0,c1,c0,c1,c0,c2,c0,c2,c1]

def selected : Fin 13 → Fin 3 := ![0,0,0,0,2,0,0,0,1,0,0,1,1]

/-- Seven interior colours for each quotient, in its actual vertex order. -/
def data : String := "3211302132130232113023123012313220313213023132012323110202031233231102323110202031230203123"

def colour (e : Fin 13) (v : Fin 18) : Color :=
  if h : v.val < 11 then boundary (selected e) ⟨v.val,h⟩
  else ![c0,c1,c2,c3] ⟨(data.toUTF8[7 * e.val + (v.val - 11)]?.getD 48).toNat % 4,
    Nat.mod_lt _ (by decide)⟩

theorem valid_on_source : ∀ e u v, input0099.graph.Adj u v → collapse e u ≠ collapse e v →
    colour e (collapse e u) ≠ colour e (collapse e v) := by decide +kernel

def colouring (e : Fin 13) : (quotient e).Coloring Color :=
  .mk (colour e) (by
    intro u v h
    obtain ⟨ne,a,b,adj,ha,hb⟩ := (SimpleGraph.map_adj' _ _ _ _).mp h
    have hne : collapse e a ≠ collapse e b := by rwa [ha,hb]
    simpa only [ha,hb] using valid_on_source e a b adj hne)

theorem boundary_values : ∀ e i, colouring e (collapse e (port i)) = boundary (selected e) i := by
  change ∀ e i, colour e (collapse e (port i)) = boundary (selected e) i
  decide +kernel

theorem no_extension : ∀ s, ¬ ∃ a c, r5 (boundary s) a c := by decide +kernel

theorem no_joint_stage : ∀ s t (g : EdgePerm),
    (trace (List.ofFn (boundary s))).map g ≠ List.ofFn (StripSixJointRepair.word t) := by
  decide +kernel

theorem no_chain_stage : ∀ s t (g : EdgePerm),
    (trace (List.ofFn (boundary s))).map g ≠ List.ofFn (StripChainRepair.word t) := by
  decide +kernel

/-- This predicate is exactly direct extension or reuse of either existing
stage family; it is not the set of all possible successful repairs. -/
def ExistingDomain (et : List Color) : Prop :=
  StripSymbolicRepair.Direct et ∨
  (∃ t : Fin 16, ∃ g : EdgePerm, et.map g = List.ofFn (StripSixJointRepair.word t)) ∨
  (∃ t : Fin 11, ∃ g : EdgePerm, et.map g = List.ofFn (StripChainRepair.word t))

theorem outside_existing_domain (s : Fin 3) :
    ¬ ExistingDomain (trace (List.ofFn (boundary s))) := by
  rintro (h | ⟨t,g,h⟩ | ⟨t,g,h⟩)
  · exact StripResponseSummary.no_trace _ (no_extension s) (StripSymbolicRepair.direct_sound h)
  · exact no_joint_stage s t g h
  · exact no_chain_stage s t g h

/-- Every internal edge contraction has a smaller-graph colouring that
cannot reconstruct while fixing its boundary. The same colouring also
refutes automatic membership in the currently certified repair domain. -/
theorem counterexample (e : Fin 13) :
    ∃ C : (quotient e).Coloring Color,
      (¬ ∃ k : input0099.graph.Coloring Color, ∀ i, k (port i) = C (collapse e (port i))) ∧
      ¬ ExistingDomain (trace (List.ofFn (fun i => C (collapse e (port i))))) := by
  refine ⟨colouring e, ?_, ?_⟩
  · rintro ⟨k,hk⟩
    have h := valid_of_colouring (boundary (selected e)) k
      (fun i => (hk i).trans (boundary_values e i))
    exact no_extension (selected e) ((terminal_iff _).mpr ⟨_,h⟩)
  · simp only [boundary_values]
    exact outside_existing_domain (selected e)

/-- No choice made among the thirteen contractions before colouring can
force every resulting colouring into the existing domain. -/
theorem no_domain_supplier : ¬ ∃ e, ∀ C : (quotient e).Coloring Color,
    ExistingDomain (trace (List.ofFn (fun i => C (collapse e (port i))))) := by
  rintro ⟨e,h⟩
  obtain ⟨C,_,outside⟩ := counterexample e
  exact outside (h C)

end FourColor.StripContractionSupply
