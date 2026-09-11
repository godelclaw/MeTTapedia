import Mettapedia.GraphTheory.FourColor.GoertzelV24TwoEdgeCutMinimality
import Mathlib.Data.Fintype.EquivFin

/-!
# A concrete bounded incidence trace for cubic-map colouring

Each vertex is represented by its three distinct incident edge numbers.
The finite code's colouring test is executable. Every cubic rotation system
has such a code, and the test is equivalent to its actual Tait colourability.
Thus coverage is constructed, not postulated as a reflection field.

This trace carries no chosen rotation or spherical-admissibility certificate.
Its full finite carrier includes nonplanar maps and arbitrary triples, so it
is not by itself a successful spherical-base audit. Connectivity and
bridge-freeness can be read from incidence, but the structural validity test
does not check them. No bounded-width decomposition is asserted.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundedCubicColourTrace

open Mettapedia.GraphTheory.FourColor
open GoertzelV24TwoEdgeCutMinimality

abbrev TaitColour := {c : Color // c ≠ 0}

-- Use the executable subtype enumeration, not a classical retained-vertex instance.
local instance : Fintype TaitColour := Subtype.fintype (fun c : Color => c ≠ 0)

/-- Three edge indices per vertex. No geometric validity is implicit. -/
abbrev Code (vertices edges : Nat) := Fin vertices → Fin 3 → Fin edges

def Proper {n m : Nat} (code : Code n m) (c : Fin m → TaitColour) : Prop :=
  ∀ v i j, i ≠ j → c (code v i) ≠ c (code v j)

instance {n m : Nat} (code : Code n m) (c : Fin m → TaitColour) :
    Decidable (Proper code c) := by
  unfold Proper
  infer_instance

/-- An exhaustive finite test on the incidence code, not an oracle. -/
def hasColouring {n m : Nat} (code : Code n m) : Bool :=
  decide (∃ c : Fin m → TaitColour, Proper code c)

theorem hasColouring_iff {n m : Nat} (code : Code n m) :
    hasColouring code = true ↔ ∃ c, Proper code c := by
  simp [hasColouring]

/-- The vertices incident to one numbered edge. -/
def endpoints {n m : Nat} (code : Code n m) (e : Fin m) : Finset (Fin n) :=
  Finset.univ.filter fun v => ∃ i, code v i = e

/-- A loopless cubic multigraph presentation; parallel edges are permitted. -/
def Valid {n m : Nat} (code : Code n m) : Prop :=
  (∀ v, Function.Injective (code v)) ∧ ∀ e, (endpoints code e).card = 2

instance {n m : Nat} (code : Code n m) : Decidable (Valid code) := by
  unfold Valid Function.Injective
  infer_instance

/-- A finite envelope for incidence codes below a vertex bound. -/
abbrev BoundedCode (bound : Nat) :=
  Σ n : Fin (bound + 1), Σ m : Fin (3 * bound / 2 + 1), Code n.val m.val

def BoundedCode.valid {bound : Nat} (code : BoundedCode bound) : Bool :=
  decide (Valid code.2.2)

def BoundedCode.hasColouring {bound : Nat} (code : BoundedCode bound) : Bool :=
  BoundedCubicColourTrace.hasColouring code.2.2

/-- A computable structural envelope, not a spherical-base certificate. -/
def structuralEnvelope (bound : Nat) : Finset (BoundedCode bound) :=
  Finset.univ.filter fun code => code.valid = true

section Encoding

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E) (hc : RS.IsCubic)

/-- Number the three incident edges at a vertex. -/
noncomputable def starEquiv (v : V) :
    Fin 3 ≃ {e : E // e ∈ RS.incidentEdges v} :=
  (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_coe, RS.incidentEdges_card_eq_three_of_isCubic hc])).symm

noncomputable def starEdge (v : V) (i : Fin 3) : E :=
  (starEquiv RS hc v i).val

theorem starEdge_mem (v : V) (i : Fin 3) :
    starEdge RS hc v i ∈ RS.incidentEdges v :=
  (starEquiv RS hc v i).property

theorem starEdge_injective (v : V) : Function.Injective (starEdge RS hc v) :=
  Subtype.val_injective.comp (starEquiv RS hc v).injective

theorem exists_starEdge {v : V} {e : E} (he : e ∈ RS.incidentEdges v) :
    ∃ i, starEdge RS hc v i = e := by
  refine ⟨(starEquiv RS hc v).symm ⟨e, he⟩, ?_⟩
  exact congrArg Subtype.val ((starEquiv RS hc v).apply_symm_apply ⟨e, he⟩)

/-- An actual code extracted from every cubic rotation map. -/
noncomputable def encode : Code (Fintype.card V) (Fintype.card E) :=
  fun v i => Fintype.equivFin E
    (starEdge RS hc ((Fintype.equivFin V).symm v) i)

@[simp] theorem encode_vertex (v : V) (i : Fin 3) :
    encode RS hc (Fintype.equivFin V v) i =
      Fintype.equivFin E (starEdge RS hc v i) := by
  simp [encode]

theorem encode_injective (v : Fin (Fintype.card V)) :
    Function.Injective (encode RS hc v) :=
  (Fintype.equivFin E).injective.comp
    (starEdge_injective RS hc ((Fintype.equivFin V).symm v))

theorem mem_endpoints_encode (e : Fin (Fintype.card E))
    (v : Fin (Fintype.card V)) :
    v ∈ endpoints (encode RS hc) e ↔
      (Fintype.equivFin V).symm v ∈ RS.endpoints ((Fintype.equivFin E).symm e) := by
  simp only [endpoints, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [RS.mem_endpoints_iff_mem_incidentEdges]
  constructor
  · rintro ⟨i, hi⟩
    have he : starEdge RS hc ((Fintype.equivFin V).symm v) i =
        (Fintype.equivFin E).symm e := by
      exact (Fintype.equivFin E).apply_eq_iff_eq_symm_apply.1 hi
    rw [← he]
    exact starEdge_mem RS hc _ i
  · intro he
    obtain ⟨i, hi⟩ := exists_starEdge RS hc he
    refine ⟨i, ?_⟩
    simp [encode, hi]

theorem endpoints_encode (e : Fin (Fintype.card E)) :
    endpoints (encode RS hc) e =
      (RS.endpoints ((Fintype.equivFin E).symm e)).map
        (Fintype.equivFin V).toEmbedding := by
  ext v
  rw [mem_endpoints_encode]
  simp

theorem encode_valid : Valid (encode RS hc) := by
  refine ⟨encode_injective RS hc, fun e => ?_⟩
  rw [endpoints_encode, Finset.card_map, RS.endpoints_card_two]

theorem hasColouring_encode_iff :
    hasColouring (encode RS hc) = true ↔ RotationSystemTaitColorable RS := by
  rw [hasColouring_iff]
  constructor
  · rintro ⟨c, hproper⟩
    let colouring : RS.EdgeColoring Color :=
      { toFun := fun e => (c (Fintype.equivFin E e)).val
        map_rel' := by
          intro e f hef
          obtain ⟨hne, v, he, hf⟩ := hef
          obtain ⟨i, hi⟩ := exists_starEdge RS hc
            ((RS.mem_endpoints_iff_mem_incidentEdges).1 he)
          obtain ⟨j, hj⟩ := exists_starEdge RS hc
            ((RS.mem_endpoints_iff_mem_incidentEdges).1 hf)
          have hij : i ≠ j := by
            intro hij
            exact hne (hi.symm.trans (hij ▸ hj))
          have h := hproper (Fintype.equivFin V v) i j hij
          simp only [encode_vertex, hi, hj] at h
          exact fun heq => h (Subtype.ext heq) }
    exact ⟨colouring, fun e => (c (Fintype.equivFin E e)).property⟩
  · rintro ⟨colouring, hnonzero⟩
    refine ⟨fun e => ⟨colouring ((Fintype.equivFin E).symm e),
      hnonzero _⟩, ?_⟩
    intro v i j hij heq
    have hv := congrArg Subtype.val heq
    simp only [encode, Equiv.symm_apply_apply] at hv
    apply colouring.valid
      (RS.edgeAdjacencyGraph_adj_of_mem_incidentEdges
        (fun h => hij (starEdge_injective RS hc _ h))
        (starEdge_mem RS hc _ i) (starEdge_mem RS hc _ j))
    exact hv

include RS hc in
theorem edge_count_le_of_vertex_bound {bound : Nat}
    (hb : Fintype.card V ≤ bound) : Fintype.card E ≤ 3 * bound / 2 := by
  have he := RS.card_darts_eq_twice_card_edges
  have hv := RS.card_darts_eq_three_times_card_vertices hc
  omega

/-- Concrete bounded trace of a map, with no alphabet or coverage hypothesis. -/
noncomputable def trace {bound : Nat} (hb : Fintype.card V ≤ bound) :
    BoundedCode bound :=
  ⟨⟨Fintype.card V, by omega⟩,
    ⟨Fintype.card E, by have := edge_count_le_of_vertex_bound RS hc hb; omega⟩,
    encode RS hc⟩

theorem trace_mem_structuralEnvelope {bound : Nat} (hb : Fintype.card V ≤ bound) :
    trace RS hc hb ∈ structuralEnvelope bound := by
  simp only [structuralEnvelope, Finset.mem_filter, Finset.mem_univ, true_and]
  change decide (Valid (encode RS hc)) = true
  exact decide_eq_true (encode_valid RS hc)

theorem trace_hasColouring_iff {bound : Nat} (hb : Fintype.card V ≤ bound) :
    (trace RS hc hb).hasColouring = true ↔ RotationSystemTaitColorable RS :=
  hasColouring_encode_iff RS hc

theorem trace_bad_iff {bound : Nat} (hb : Fintype.card V ≤ bound) :
    (trace RS hc hb).hasColouring = false ↔ ¬ RotationSystemTaitColorable RS := by
  rw [← trace_hasColouring_iff RS hc hb, Bool.eq_false_iff]

end Encoding

/-! Small code checks, including a guard against calling the structural envelope
the spherical bridgeless base. The second code is the six-vertex bridged
multigraph consisting of two doubled-edge triangles joined at their remaining
degree-two vertices. Its colourability obstruction is proved locally. -/

namespace Controls

def tetrahedron : Code 4 6 :=
  ![![0, 1, 2], ![0, 3, 4], ![1, 3, 5], ![2, 4, 5]]

theorem tetrahedron_valid : Valid tetrahedron := by decide +kernel

theorem tetrahedron_hasColouring : hasColouring tetrahedron = true := by decide +kernel

def bridged : Code 6 9 :=
  ![![0, 1, 4], ![0, 2, 3], ![1, 2, 3],
    ![4, 5, 6], ![5, 7, 8], ![6, 7, 8]]

theorem bridged_valid : Valid bridged := by decide +kernel

private theorem not_four_distinct (a b c d : TaitColour) :
    a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → False := by
  revert a b c d
  decide +kernel

theorem bridged_hasNoColouring : hasColouring bridged = false := by
  apply Bool.eq_false_iff.2
  intro h
  obtain ⟨c, hp⟩ := (hasColouring_iff bridged).1 h
  apply not_four_distinct (c 0) (c 1) (c 2) (c 3)
  · simpa [bridged] using hp 0 0 1 (by decide)
  · simpa [bridged] using hp 1 0 1 (by decide)
  · simpa [bridged] using hp 1 0 2 (by decide)
  · simpa [bridged] using hp 2 0 1 (by decide)
  · simpa [bridged] using hp 2 0 2 (by decide)
  · simpa [bridged] using hp 1 1 2 (by decide)

/-- A regression guard: the unrefined structural envelope cannot discharge
the spherical bridgeless base. No claim of admissibility is made for this code. -/
theorem structuralEnvelope_contains_bad {bound : Nat} (hb : 6 ≤ bound) :
    ∃ code ∈ structuralEnvelope bound, code.hasColouring = false := by
  let code : BoundedCode bound :=
    ⟨⟨6, by omega⟩, ⟨9, by omega⟩, bridged⟩
  refine ⟨code, ?_, bridged_hasNoColouring⟩
  simp only [structuralEnvelope, Finset.mem_filter, Finset.mem_univ, true_and]
  change decide (Valid bridged) = true
  exact decide_eq_true bridged_valid

end Controls

end Mettapedia.GraphTheory.FourColor.BoundedCubicColourTrace
