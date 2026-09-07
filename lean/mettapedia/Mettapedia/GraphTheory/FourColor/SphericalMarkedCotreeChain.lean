import Mettapedia.GraphTheory.FourColor.FiniteMarkedChain
import Mettapedia.GraphTheory.FourColor.SphericalCotreePathChain

/-!
# Full cotree cuts avoiding marked vertex material

The geometric cotree supplier is valid before any minimal-counterexample
assumption. Spacing its cuts by `6*w+1` produces a strict cubic star in
every slab. A constant marked-material window then keeps every marked
vertex on the same majority side, without changing width or boundary order.
This does not say that a frozen edge is uncut, or that frozen boundary
colours are preserved by a later splice.
-/

namespace Mettapedia.GraphTheory.FourColor.SphericalMarkedCotreeChain

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24TwoEdgeCutMinimality GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceTwoSided GoertzelV24PrimalCycleFacialBond
open GoertzelV24ConnectedShoreLiteralNode GoertzelV24ConnectedEdgeShoreMajority
open GoertzelV24CubicSmallBoundaryCycle GoertzelV24SphereCutMaterial
open GoertzelV24SimpleGraphTaitBridge GoertzelV24MajorityShoreStateDescent
open GoertzelV24FramedLocalDualCycleBond
open FiniteMarkedChain SphericalCotreePathChain

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] [G.LocallyFinite]

noncomputable section

local instance : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance : DecidableEq G.edgeSet := Subtype.instDecidableEq

omit [G.LocallyFinite] in
/-- Marked endpoints give a constant frozen crossing set, not an empty one.
This identifies the persistent seam edges that a frozen-data splice must
still carry with their original identities and colours. -/
theorem frozen_crossing_invariant {N w : ℕ}
    (nodes : Fin N → ConnectedShoreNode (G := G) w w)
    (marks : Finset V) (frozen : Finset G.edgeSet)
    (hends : ∀ e ∈ frozen, ∀ v ∈ (e : Sym2 V), v ∈ marks)
    {i j : Fin N}
    (hmarks : ∀ v ∈ marks, majorityVertexSide G (nodes i).shore v ↔
      majorityVertexSide G (nodes j).shore v) :
    frozen ∩ localCrossingEdgeFinset G (majorityVertexSide G (nodes i).shore) =
      frozen ∩ localCrossingEdgeFinset G (majorityVertexSide G (nodes j).shore) := by
  classical
  ext e
  simp only [Finset.mem_inter, mem_localCrossingEdgeFinset_iff]
  by_cases he : e ∈ frozen
  · simp only [he, true_and]
    constructor
    · rintro ⟨u, v, hu, hv, hsu, hsv⟩
      exact ⟨u, v, hu, hv, (hmarks u (hends e he u hu)).mp hsu,
        fun h => hsv ((hmarks v (hends e he v hv)).mpr h)⟩
    · rintro ⟨u, v, hu, hv, hsu, hsv⟩
      exact ⟨u, v, hu, hv, (hmarks u (hends e he u hu)).mpr hsu,
        fun h => hsv ((hmarks v (hends e he v hv)).mp h)⟩
  · simp [he]

/-- A spaced pair of nested nodes contains a vertex with its full star in
the slab; the vertex lies strictly between the actual majority sides. -/
theorem exists_star_of_index_gap {N w : ℕ}
    (nodes : Fin N → ConnectedShoreNode (G := G) w w)
    (hstrict : ∀ i j, i < j → (nodes i).shore ⊂ (nodes j).shore)
    (hcubic : ∀ v, (incidentEdgeFinset G v).card = 3)
    {i j : Fin N} (hij : i < j) (hgap : 6 * w < j.val - i.val) :
    ∃ v, majorityVertexSide G (nodes j).shore v ∧
      ¬ majorityVertexSide G (nodes i).shore v ∧
      ∀ e ∈ incidentEdgeFinset G v, e ∈ (nodes j).shore \ (nodes i).shore := by
  classical
  have hcard := strictMono_nat_gap (fun i => (nodes i).shore.card)
    (fun i j hij => Finset.card_lt_card (hstrict i j hij)) hij.le
  have hlarge : 6 * w < ((nodes j).shore \ (nodes i).shore).card := by
    rw [Finset.card_sdiff_of_subset (hstrict i j hij).1]
    omega
  let incident : V → G.edgeSet → Prop := fun v e => v ∈ (e : Sym2 V)
  obtain ⟨v, _, hv⟩ := exists_strict_slab_vertex_of_cubic incident
    (nodes i).shore (nodes j).shore w (exists_incident_vertex (G := G))
    (fun v => by simpa only [incident, incidentEdgeFinset] using (hcubic v).le)
    (nodes i).middleBound (nodes j).middleBound hlarge
  have hstar : ∀ e ∈ incidentEdgeFinset G v, e ∈ (nodes j).shore \ (nodes i).shore := by
    intro e he
    apply hv e
    simpa only [incident, incidentEdgeFinset, Finset.mem_filter, Finset.mem_univ,
      true_and] using he
  exact ⟨v, (strict_majority_material_of_incident_sdiff hcubic hstar).1,
    (strict_majority_material_of_incident_sdiff hcubic hstar).2, hstar⟩

/-- Select a regularly spaced subsequence before removing marked transitions. -/
def spacedIndex (w r : ℕ) : Fin (r + 1) ↪o Fin ((6 * w + 1) * r + 1) where
  toFun i := ⟨(6 * w + 1) * i.val, by
    have := Nat.mul_le_mul_left (6 * w + 1) (show i.val ≤ r by omega)
    omega⟩
  inj' := by
    intro i j h
    apply Fin.ext
    exact Nat.eq_of_mul_eq_mul_left (by omega) (congrArg Fin.val h)
  map_rel_iff' := by
    intro i j
    change (6 * w + 1) * i.val ≤ (6 * w + 1) * j.val ↔ i.val ≤ j.val
    exact Nat.mul_le_mul_left_iff (by omega)

/-- An explicit geometric threshold for `n` nonempty marked-free slabs. -/
def markedCotreeVertexBound (h t n : ℕ) : ℕ :=
  4 ^ ((6 * (2 * h + 1) + 1) * ((t + 1) * n) + 1 + 2 * (2 * h + 1))

/-- Construct connected-shore nodes from spherical geometry and large size.
The marks apply to the actual majority sides consumed by the Count nodes,
not merely to the preliminary fundamental vertex shores. -/
theorem exists_marked_nodes_of_large_card (data : Data G)
    (hclass : BridgelessSphericalCubicMapData data.toRotationSystem)
    (htwo : OrbitFacesTwoSided data.toRotationSystem)
    (root : OrbitFace data.toRotationSystem) (h n : ℕ) (marks : Finset V)
    (hradius : ∀ f, (orbitFaceDualGraph data).dist f root ≤ h)
    (hlarge : markedCotreeVertexBound h marks.card n < Fintype.card V) :
    ∃ nodes : Fin (n + 1) → ConnectedShoreNode (G := G) (2 * h + 1) (2 * h + 1),
      (∀ i j, i < j → (nodes i).shore ⊂ (nodes j).shore) ∧
      (∀ i v, v ∈ marks → (majorityVertexSide G (nodes i).shore v ↔
        majorityVertexSide G (nodes 0).shore v)) ∧
      (∀ i j, i < j → ∃ v, v ∉ marks ∧
        majorityVertexSide G (nodes j).shore v ∧
        ¬ majorityVertexSide G (nodes i).shore v ∧
        ∀ e ∈ incidentEdgeFinset G v, e ∈ (nodes j).shore \ (nodes i).shore) := by
  classical
  let w := 2 * h + 1
  let r := (marks.card + 1) * n
  obtain ⟨raw, hraw⟩ := exists_nested_nodes_of_large_card_of_spherical data hclass htwo
    root h ((6 * w + 1) * r + 1) hradius hlarge
  let spaced := fun i => raw (spacedIndex w r i)
  have hs : ∀ i j, i < j → (spaced i).shore ⊂ (spaced j).shore :=
    fun i j hij => hraw _ _ ((spacedIndex w r).strictMono hij)
  let sides := fun i => {v | majorityVertexSide G (spaced i).shore v}
  have hmono : Monotone sides := by
    intro i j hij
    rcases lt_or_eq_of_le hij with hij | rfl
    · exact fun _ hv => majorityVertexSide_mono (hs i j hij).1 hv
    · exact Set.Subset.rfl
  obtain ⟨start, hmarks⟩ := exists_constant_window marks n sides hmono
  let ix := windowIndex marks.card n start
  let nodes := fun i => spaced (ix i)
  have hm : ∀ i v, v ∈ marks → (majorityVertexSide G (nodes i).shore v ↔
      majorityVertexSide G (nodes 0).shore v) := hmarks
  refine ⟨nodes, (fun i j hij => hs _ _ (ix.strictMono hij)), hm, ?_⟩
  intro i j hij
  have hix := ix.strictMono hij
  have hgap : 6 * w < (spacedIndex w r (ix j)).val -
      (spacedIndex w r (ix i)).val := by
    have hmul := Nat.mul_le_mul_left (6 * w + 1)
      (show (ix i).val + 1 ≤ (ix j).val by omega)
    rw [Nat.mul_add, mul_one] at hmul
    change 6 * w < (6 * w + 1) * (ix j).val - (6 * w + 1) * (ix i).val
    omega
  obtain ⟨v, hvj, hvi, hstar⟩ := exists_star_of_index_gap raw hraw
    (incidentEdgeFinset_card_eq_three_of_toRotationSystem_isCubic data hclass.spherical.cubic)
    ((spacedIndex w r).strictMono hix) hgap
  refine ⟨v, ?_, hvj, hvi, hstar⟩
  intro hv
  exact hvi ((hm i v hv).mpr ((hm j v hv).mp hvj))

end
end Mettapedia.GraphTheory.FourColor.SphericalMarkedCotreeChain
