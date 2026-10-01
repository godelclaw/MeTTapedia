import Mettapedia.GraphTheory.FourColor.GoertzelV24CyclicBoundaryClosure
import Mettapedia.GraphTheory.FourColor.TwoCellSourceRepair
import Mettapedia.GraphTheory.FourColor.DualTruncateKempeTransport
import Mettapedia.GraphTheory.FourColor.DualTruncateConstructionGSLT

/-!
# Alternating source observations at an actual cyclic boundary

The separating-trail theorem applies to the literal facial first-return
order. This module uses that geometry to exclude simultaneous third-colour
connections between alternating equal-coloured source pins. Its conclusion
supplies a separating region; no such region is assumed in the geometric
statement.
-/

namespace Mettapedia.GraphTheory.FourColor.SourceAlternatingBoundaryRepair

open SimpleGraph SimpleGraphDartRotation
open GoertzelV24CyclicBondBoundary GoertzelV24CyclicBoundaryClosure
open GoertzelV24CyclicBoundaryAlternatingTrail
open GoertzelV24FaceDualConnectedness GoertzelV24FaceOrbitIncidence
open GoertzelV24OrbitFaceCurvatureBulk GoertzelV24OrbitFaceTwoSided
open GoertzelV24RotationCutDartDecomposition

noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

local instance graphEdgeSetDecidableEq : DecidableEq G.edgeSet :=
  Subtype.instDecidableEq

/-- Four literal boundary darts, in their actual retained facial order. -/
abbrev fourBoundary (graphData : Data G) (keep : V → Prop)
    (order : Fin 4 ≃ BoundaryDart graphData.toRotationSystem keep)
    (hsuccessor : order.permCongr (finRotate 4) =
      GoertzelV24RetainedRegionBoundaryOrder.retainedRegionBoundarySuccessor
        graphData.toRotationSystem keep) :
    CyclicBondBoundaryData graphData.toRotationSystem keep :=
  ⟨4, by decide, order, hsuccessor⟩

/-- In a spherical cubic embedding, two edge-disjoint retained paths cannot
join the alternating port pairs. The deleted shore closes one path to an
actual separating trail. -/
theorem no_disjoint_four_port_paths
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (keep : V → Prop)
    (hcomplement : (SideGraph G (fun v => ¬keep v)).Connected)
    (order : Fin 4 ≃ BoundaryDart graphData.toRotationSystem keep)
    (hsuccessor : order.permCongr (finRotate 4) =
      GoertzelV24RetainedRegionBoundaryOrder.retainedRegionBoundarySuccessor
        graphData.toRotationSystem keep)
    (inside : (SideGraph G keep).Walk
      (retainedPort graphData keep (fourBoundary graphData keep order hsuccessor) 0)
      (retainedPort graphData keep (fourBoundary graphData keep order hsuccessor) 2))
    (hinside : inside.IsPath)
    (other : (SideGraph G keep).Walk
      (retainedPort graphData keep (fourBoundary graphData keep order hsuccessor) 1)
      (retainedPort graphData keep (fourBoundary graphData keep order hsuccessor) 3))
    (hother : other.IsPath)
    (hdisjoint : other.edges.Disjoint inside.edges) : False := by
  let data := fourBoundary graphData keep order hsuccessor
  obtain ⟨outside, houtside⟩ := hcomplement.exists_isPath
    (deletedPort graphData keep data 2) (deletedPort graphData keep data 0)
  let separator := boundaryClosure graphData keep data 0 2 inside outside
  let route := sideWalkToAmbient G keep other
  have hseparator : separator.IsTrail := boundaryClosure_isTrail
    graphData keep data 0 2 (by change (0 : Fin 4) ≠ 2; decide)
      inside outside hinside.isTrail houtside.isTrail
  have hrouteTrail : route.IsTrail := (sideWalkToAmbient_isPath keep hother).isTrail
  have hrouteDisjoint : route.edges.Disjoint separator.edges :=
    sideWalkToAmbient_edges_disjoint_boundaryClosure
      graphData keep data 0 2 inside outside other hdisjoint
  have hmembership (i : Fin 4) :
      boundaryEdge graphData keep data i ∈ separator.edges ↔ i = 0 ∨ i = 2 :=
    boundaryEdge_mem_boundaryClosure_edges_iff graphData keep data 0 2 inside outside i
  have hcut : boundaryEdge graphData keep data 0 ∈ separator.edges :=
    (hmembership 0).2 (Or.inl rfl)
  have hleft : boundaryEdge graphData keep data 1 ∉ separator.edges := by
    intro h
    exact (hmembership 1).1 h |>.elim (by decide) (by decide)
  have hright : boundaryEdge graphData keep data 3 ∉ separator.edges := by
    intro h
    exact (hmembership 3).1 h |>.elim (by decide) (by decide)
  have hleftArc : ∀ i, i < 0 → boundaryEdge graphData keep data
      ((finRotate 4)^[i] (finRotate 4 0)) ∉ separator.edges := by
    intro i hi; omega
  have hrightArc : ∀ i, i < 1 → boundaryEdge graphData keep data
      ((finRotate 4)^[i] 3) ∉ separator.edges := by
    intro i hi
    have : i = 0 := by omega
    simpa [this] using hright
  by_cases hends : (retainedPort graphData keep data 1).1 ≠
      (retainedPort graphData keep data 3).1
  · have hnil : ¬route.Nil := Walk.not_nil_of_ne hends
    have hfirst : route.firstDart hnil ≠ (order 1).1.1 := by
      intro heq
      have hnot := crossingEdge_not_mem_sideWalkToAmbient_edges keep
        (boundaryEdge_crosses graphData keep data 1) other
      apply hnot
      change (graphData.toRotationSystem.edgeOf (order 1).1.1).1 ∈ route.edges
      rw [← heq]
      change (route.firstDart hnil).edge ∈ route.edges
      rw [route.edge_firstDart hnil]
      exact route.mk_start_snd_mem_edges hnil
    have hlast : graphData.toRotationSystem.alpha (route.lastDart hnil) ≠ (order 3).1.1 := by
      intro heq
      have hnot := crossingEdge_not_mem_sideWalkToAmbient_edges keep
        (boundaryEdge_crosses graphData keep data 3) other
      apply hnot
      change (graphData.toRotationSystem.edgeOf (order 3).1.1).1 ∈ route.edges
      rw [← heq, graphData.toRotationSystem.edge_alpha]
      change (route.lastDart hnil).edge ∈ route.edges
      rw [route.edge_lastDart hnil]
      exact route.mk_penultimate_end_mem_edges hnil
    exact no_disjoint_trail_between_boundary_arcs
      graphData htwoSided hdual hconnected hsphere hcubic hrotation keep data 0 1 3 0 1
      (by change (finRotate 4)^[0] (finRotate 4 0) = (1 : Fin 4); decide)
      (by change (finRotate 4)^[1] (3 : Fin 4) = 0; decide)
      separator hseparator hcut hleft hright hleftArc hrightArc
      route hnil hrouteTrail (fun edge hmem => List.disjoint_left.mp hrouteDisjoint hmem)
      hfirst hlast
  · exact no_distinct_same_vertex_ports_between_boundary_arcs
      graphData htwoSided hdual hconnected hsphere hcubic hrotation keep data 0 1 3
      (by change (1 : Fin 4) ≠ 3; decide) 0 1
      (by change (finRotate 4)^[0] (finRotate 4 0) = (1 : Fin 4); decide)
      (by change (finRotate 4)^[1] (3 : Fin 4) = 0; decide)
      separator hseparator hcut hleft hright
      hleftArc hrightArc (not_ne_iff.mp hends).symm

section ColourPaths

variable {W A : Type*} (H : SimpleGraph W) (c : W → A) (a t : A)

/-- The actual graph restricted to edges whose ends have either of two
specified colours. The vertex carrier is unchanged. -/
def colourGraph : SimpleGraph W where
  Adj v w := H.Adj v w ∧ (c v = a ∨ c v = t) ∧ (c w = a ∨ c w = t)
  symm := ⟨fun _ _ h => ⟨h.1.symm, h.2.2, h.2.1⟩⟩
  loopless := ⟨fun _ h => H.irrefl h.1⟩

theorem colourGraph_le : colourGraph H c a t ≤ H := fun _ _ h => h.1

theorem reachable_colour {root v : W} (hroot : c root = a ∨ c root = t)
    (h : (colourGraph H c a t).Reachable root v) : c v = a ∨ c v = t := by
  rcases h with ⟨walk⟩
  induction walk with
  | nil => exact hroot
  | @cons v w last hadj rest ih => exact ih hadj.2.2

/-- Different third-colour path systems cannot share a properly coloured
edge. The spherical cubic theorem, rather than an abstract drawing, turns
this edge disjointness into separation at alternating boundary ports. -/
theorem colour_walk_edges_disjoint (b : A) (hab : a ≠ b)
    (hc : ∀ v w, H.Adj v w → c v ≠ c w)
    {p₀ p₂ q₁ q₃ : W}
    (p : (colourGraph H c a t).Walk p₀ p₂)
    (q : (colourGraph H c b t).Walk q₁ q₃) :
    q.edges.Disjoint p.edges := by
  rw [List.disjoint_left]
  intro edge hq hp
  induction edge using Sym2.inductionOn with
  | _ v w =>
    have hpa := p.adj_of_mem_edges hp
    have hqa := q.adj_of_mem_edges hq
    have hv : c v = t := by
      rcases hpa.2.1 with ha | ht
      · rcases hqa.2.1 with hb | ht
        · exact (hab (ha.symm.trans hb)).elim
        · exact ht
      · exact ht
    have hw : c w = t := by
      rcases hpa.2.2 with ha | ht
      · rcases hqa.2.2 with hb | ht
        · exact (hab (ha.symm.trans hb)).elim
        · exact ht
      · exact ht
    exact hc v w hpa.1 (hv.trans hw.symm)

end ColourPaths

/-- Geometry guarantees a separating third-colour component for at least
one of the two alternating equal-colour pin pairs. -/
theorem alternating_pair_separation
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (keep : V → Prop)
    (hcomplement : (SideGraph G (fun v => ¬keep v)).Connected)
    (order : Fin 4 ≃ BoundaryDart graphData.toRotationSystem keep)
    (hsuccessor : order.permCongr (finRotate 4) =
      GoertzelV24RetainedRegionBoundaryOrder.retainedRegionBoundarySuccessor
        graphData.toRotationSystem keep)
    (c : V → Color)
    (hproper : ∀ v w, keep v → keep w → G.Adj v w → c v ≠ c w)
    (a b t : Color) (hab : a ≠ b) :
    let ports := retainedPort graphData keep (fourBoundary graphData keep order hsuccessor)
    let sideColour := fun v : SideVertex keep => c v.1
    ¬(colourGraph (SideGraph G keep) sideColour a t).Reachable (ports 0) (ports 2) ∨
      ¬(colourGraph (SideGraph G keep) sideColour b t).Reachable (ports 1) (ports 3) := by
  classical
  dsimp only
  by_cases hp : (colourGraph (SideGraph G keep) (fun v => c v.1) a t).Reachable
      (retainedPort graphData keep (fourBoundary graphData keep order hsuccessor) 0)
      (retainedPort graphData keep (fourBoundary graphData keep order hsuccessor) 2)
  · right
    intro hq
    obtain ⟨p, hpPath⟩ := hp.exists_isPath
    obtain ⟨q, hqPath⟩ := hq.exists_isPath
    have hdisjoint := colour_walk_edges_disjoint (SideGraph G keep) (fun v => c v.1)
      a t b hab (fun v w hadj => hproper v.1 w.1 v.2 w.2 hadj) p q
    have hdisjoint' :
        (q.mapLe (colourGraph_le (SideGraph G keep) (fun v => c v.1) b t)).edges.Disjoint
        (p.mapLe (colourGraph_le (SideGraph G keep) (fun v => c v.1) a t)).edges := by
      simpa only [Walk.edges_mapLe_eq_edges] using hdisjoint
    exact no_disjoint_four_port_paths graphData htwoSided hdual hconnected hsphere
      hcubic hrotation keep hcomplement order hsuccessor _ (hpPath.mapLe _) _
      (hqPath.mapLe _) hdisjoint'
  · exact Or.inl hp

open GoertzelV24HexagonPairingTargetAwareBoundary GoertzelV24PortTangleCommonKempeWeb
open TwoCellSourceRepair

/-- The third-colour pair is determined by the colour that must remain
unchanged. Only the fixed three-colour alphabet is checked here. -/
theorem third_pair (a b : Color) (ha : a ≠ 0) (hb : b ≠ 0) (hab : a ≠ b) :
    ∃ pair : TaitColorPair,
      (∀ x, pairActiveColor pair x ↔ x = b ∨ x = a+b) ∧
      ¬pairActiveColor pair a ∧ Color.swap pair.colors.1 pair.colors.2 b = a+b := by
  rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero a ha with rfl | rfl | rfl <;>
    rcases eq_red_or_eq_blue_or_eq_purple_of_ne_zero b hb with rfl | rfl | rfl
  all_goals first
    | exact (hab rfl).elim
    | refine ⟨.redBlue, ?_⟩; unfold pairActiveColor Color.twoColor; decide +kernel
    | refine ⟨.redPurple, ?_⟩; unfold pairActiveColor Color.twoColor; decide +kernel
    | refine ⟨.bluePurple, ?_⟩; unfold pairActiveColor Color.twoColor; decide +kernel

/-- The literal component containing a retained source vertex, with no
choice of an abstract boundary matching. -/
def componentMask (keep : V → Prop) (c : V → Color) (root : SideVertex keep)
    (a t : Color) (v : V) : Prop :=
  ∃ hv : keep v,
    (colourGraph (SideGraph G keep) (fun w => c w.1) a t).Reachable root ⟨v,hv⟩

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
theorem componentMask_root (keep : V → Prop) (c : V → Color)
    (root : SideVertex keep) (a t : Color) :
    componentMask (G := G) keep c root a t root.1 := ⟨root.2, .rfl⟩

/-- A separating actual component supplies precisely the active and closure
conditions required by the source-switch semantics. -/
theorem component_region (graphData : Data G) (keep : V → Prop) (c : V → Color)
    (root : SideVertex keep) (a t : Color) (hroot : c root.1 = a ∨ c root.1 = t)
    (pair : TaitColorPair)
    (hpair : ∀ x, pairActiveColor pair x ↔ x = a ∨ x = t) :
    SourcePatchKempe.Region graphData.toRotationSystem keep c pair
      (componentMask (G := G) keep c root a t) := by
  constructor
  · rintro v _ ⟨hv, hreach⟩
    exact (hpair _).2 (reachable_colour (SideGraph G keep) (fun w => c w.1)
      a t hroot hreach)
  · intro d hv hw ha ht
    have hedge : (colourGraph (SideGraph G keep) (fun w => c w.1) a t).Adj
        ⟨d.fst,hv⟩ ⟨d.snd,hw⟩ := ⟨d.adj, (hpair _).1 ha, (hpair _).1 ht⟩
    constructor
    · rintro ⟨_, hreach⟩
      exact ⟨hw, hreach.trans hedge.reachable⟩
    · rintro ⟨_, hreach⟩
      exact ⟨hv, hreach.trans hedge.symm.reachable⟩

/-- Both chosen source colours and their joint seam remain explicit. -/
structure Repair {E : Type u} [Fintype E] [DecidableEq E]
    (RS : RotationSystem.{u,u,u} V E) (frame : Frame RS) (c : V → Color) where
  pair : TaitColorPair
  mask : V → Prop
  mask_decidable : DecidablePred mask
  region : SourcePatchKempe.Region RS frame.outside c pair mask
  x : Color
  y : Color
  compatible :
    letI := mask_decidable
    TwoCellBoundaryChoice.Compatible
      (SourcePatchKempe.switched c pair mask (frame.pins 0))
      (SourcePatchKempe.switched c pair mask (frame.pins 1))
      (SourcePatchKempe.switched c pair mask (frame.pins 2))
      (SourcePatchKempe.switched c pair mask (frame.pins 3)) x y

/-- The geometric availability result below is consumed by the already
proved constructor of a genuine full source colouring. -/
def Repair.complete {E : Type u} [Fintype E] [DecidableEq E]
    {RS : RotationSystem.{u,u,u} V E} {frame : Frame RS} {c : V → Color}
    (repair : Repair RS frame c) (hc : SourcePatchKempe.ExteriorProper RS frame.outside c) :
    DualTruncateColoring.ThreeVertexColoring RS := by
  letI := repair.mask_decidable
  exact frame.complete (SourcePatchKempe.switched c repair.pair repair.mask)
    (SourcePatchKempe.switched_exterior RS frame.outside c hc repair.pair repair.mask repair.region)
    repair.x repair.y repair.compatible

/-- Alternating pins in the actual boundary order admit a joint repair.
The geometric hypotheses guarantee the separating component; the result
neither assumes a completed source colouring nor searches a table of them. -/
theorem exists_repair
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (hdual : (interiorDualGraph (orbitFaceBoundary graphData.toRotationSystem)
      (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected)
    (hconnected : G.Connected)
    (hsphere : OrbitSphericalCubicMapData graphData.toRotationSystem)
    (hcubic : graphData.toRotationSystem.IsCubic)
    (hrotation : VertexRotationCyclic graphData.toRotationSystem)
    (frame : Frame graphData.toRotationSystem)
    (hcomplement : (SideGraph G (fun v => ¬frame.outside v)).Connected)
    (order : Fin 4 ≃ BoundaryDart graphData.toRotationSystem frame.outside)
    (hsuccessor : order.permCongr (finRotate 4) =
      GoertzelV24RetainedRegionBoundaryOrder.retainedRegionBoundarySuccessor
        graphData.toRotationSystem frame.outside)
    (hpins : ∀ i, (order i).1.1.fst = frame.pins i)
    (c : V → Color) (hc : SourcePatchKempe.ExteriorProper graphData.toRotationSystem frame.outside c)
    (a b : Color) (hab : a ≠ b)
    (hvalues : c (frame.pins 0) = a ∧ c (frame.pins 1) = b ∧
      c (frame.pins 2) = a ∧ c (frame.pins 3) = b) :
    Nonempty (Repair graphData.toRotationSystem frame c) := by
  classical
  let keep := frame.outside
  let ports := retainedPort graphData keep (fourBoundary graphData keep order hsuccessor)
  have port_eq (i : Fin 4) : (ports i).1 = frame.pins i := hpins i
  have hproper : ∀ v w, keep v → keep w → G.Adj v w → c v ≠ c w := by
    intro v w hv hw h
    exact hc.2 (⟨(v,w),h⟩ : G.Dart) hv hw
  have ha : a ≠ 0 := hvalues.1 ▸ hc.1 _ (frame.pins_outside 0)
  have hb : b ≠ 0 := hvalues.2.1 ▸ hc.1 _ (frame.pins_outside 1)
  have hsplit := alternating_pair_separation graphData htwoSided hdual hconnected hsphere
    hcubic hrotation keep hcomplement order hsuccessor c hproper a b (a+b) hab
  rcases hsplit with hsep | hsep
  · obtain ⟨pair, hpair, hinactive, hswap⟩ := third_pair b a hb ha hab.symm
    let mask := componentMask (G := G) keep c (ports 0) a (a+b)
    have hpair' : ∀ x, pairActiveColor pair x ↔ x = a ∨ x = a+b := by
      simpa only [add_comm b a] using hpair
    have hregion : SourcePatchKempe.Region graphData.toRotationSystem keep c pair mask :=
      component_region graphData keep c (ports 0) a (a+b)
        (Or.inl ((congrArg c (port_eq 0)).trans hvalues.1)) pair hpair'
    have hm0 : mask (frame.pins 0) := by
      rw [← port_eq 0]
      exact componentMask_root keep c (ports 0) a (a+b)
    have hn2 : ¬mask (frame.pins 2) := by
      rintro ⟨hv, hreach⟩
      apply hsep
      simpa only [← port_eq 2] using hreach
    have hn1 : ¬mask (frame.pins 1) := by
      intro hm
      exact hinactive (hvalues.2.1 ▸ hregion.active _ (frame.pins_outside 1) hm)
    have hn3 : ¬mask (frame.pins 3) := by
      intro hm
      exact hinactive (hvalues.2.2.2 ▸ hregion.active _ (frame.pins_outside 3) hm)
    refine ⟨{ pair := pair
              mask := mask
              mask_decidable := Classical.decPred _
              region := hregion
              x := a
              y := a+b
              compatible := ?_ }⟩
    simp only [SourcePatchKempe.switched, ite_eq_left hm0, ite_eq_right hn1,
      ite_eq_right hn2, ite_eq_right hn3, hvalues.1, hvalues.2.1,
      hvalues.2.2.1, hvalues.2.2.2, hswap, add_comm b a]
    have hj := TwoCellBoundaryChoice.repair_one_pin b a hb ha hab.symm
    simp only [add_comm b a, TwoCellBoundaryChoice.Compatible] at hj ⊢
    tauto
  · obtain ⟨pair, hpair, hinactive, hswap⟩ := third_pair a b ha hb hab
    let mask := componentMask (G := G) keep c (ports 1) b (a+b)
    have hregion : SourcePatchKempe.Region graphData.toRotationSystem keep c pair mask :=
      component_region graphData keep c (ports 1) b (a+b)
        (Or.inl ((congrArg c (port_eq 1)).trans hvalues.2.1)) pair hpair
    have hm1 : mask (frame.pins 1) := by
      rw [← port_eq 1]
      exact componentMask_root keep c (ports 1) b (a+b)
    have hn3 : ¬mask (frame.pins 3) := by
      rintro ⟨hv, hreach⟩
      apply hsep
      simpa only [← port_eq 3] using hreach
    have contract : OnePin graphData.toRotationSystem frame c pair mask a b :=
      ⟨hvalues, hab, hinactive, hswap, hm1, hn3⟩
    exact ⟨{ pair := pair
             mask := mask
             mask_decidable := Classical.decPred _
             region := hregion
             x := b
             y := a+b
             compatible := repaired_joint_choices frame c hc pair mask hregion a b contract }⟩

/-- Independent, literal embedding hypotheses consumed by the repair.
The only colour data enter later as a proper partial exterior. -/
structure Geometry (graphData : Data G) (frame : Frame graphData.toRotationSystem) where
  twoSided : OrbitFacesTwoSided graphData.toRotationSystem
  dual : (interiorDualGraph (orbitFaceBoundary graphData.toRotationSystem)
    (Finset.univ : Finset (OrbitFace graphData.toRotationSystem))).Connected
  connected : G.Connected
  spherical : OrbitSphericalCubicMapData graphData.toRotationSystem
  rotation : VertexRotationCyclic graphData.toRotationSystem
  complement : (SideGraph G (fun v => ¬frame.outside v)).Connected
  order : Fin 4 ≃ BoundaryDart graphData.toRotationSystem frame.outside
  successor : order.permCongr (finRotate 4) =
    GoertzelV24RetainedRegionBoundaryOrder.retainedRegionBoundarySuccessor
      graphData.toRotationSystem frame.outside
  pins : ∀ i, (order i).1.1.fst = frame.pins i

namespace Geometry

variable {graphData : Data G} {frame : Frame graphData.toRotationSystem}
  (geometry : Geometry graphData frame) (c : V → Color)
  (hc : SourcePatchKempe.ExteriorProper graphData.toRotationSystem frame.outside c)
  (a b : Color) (hab : a ≠ b)
  (hvalues : c (frame.pins 0) = a ∧ c (frame.pins 1) = b ∧
    c (frame.pins 2) = a ∧ c (frame.pins 3) = b)

/-- A choice of a repair supplied by the geometric theorem. -/
def repair : Repair graphData.toRotationSystem frame c :=
  Classical.choice (exists_repair graphData geometry.twoSided geometry.dual geometry.connected
    geometry.spherical geometry.spherical.cubic geometry.rotation frame geometry.complement
    geometry.order geometry.successor geometry.pins c hc a b hab hvalues)

/-- Geometry, a partial exterior and the shared colour law reconstruct a
genuine whole source witness. -/
def sourceColouring : DualTruncateColoring.ThreeVertexColoring graphData.toRotationSystem :=
  (geometry.repair c hc a b hab hvalues).complete hc

/-- The whole reconstructed target is properly Tait-coloured. -/
theorem target_tait : (DualTruncateColoring.rotation graphData.toRotationSystem).IsTaitEdgeColoring
    (DualTruncateColoring.colouring graphData.toRotationSystem
      (geometry.sourceColouring c hc a b hab hvalues)) :=
  DualTruncateColoring.colouring_nonzero _ _

/-- The supplied source component induces a saturated switch on actual
target edges, with the omitted patch excluded. -/
theorem physical_region :
    let r := geometry.repair c hc a b hab hvalues
    RotationPatchKempe.Region (DualTruncateColoring.rotation graphData.toRotationSystem)
      (fun d => ¬DualTruncateOpenPatch.vertexRegion graphData.toRotationSystem frame.selected d)
      (DualTruncateColoring.edgeColour graphData.toRotationSystem c) r.pair
      (DualTruncateKempeTransport.edgeMask graphData.toRotationSystem frame.selected c r.pair r.mask) := by
  let r := geometry.repair c hc a b hab hvalues
  let := r.mask_decidable
  apply DualTruncateKempeTransport.physical_region
  · simpa only [frame.outside_eq_not_selected] using hc
  · simpa only [frame.outside_eq_not_selected] using r.region

/-- Reconstruction agrees with the actual physical switch on every exterior
star, including all its cut observations. -/
theorem reconstructs :
    let r := geometry.repair c hc a b hab hvalues
    DualTruncateOpenPatch.Extends graphData.toRotationSystem
      (DualTruncateOpenPatch.vertexRegion graphData.toRotationSystem frame.selected)
      (RotationPatchKempe.switched (DualTruncateColoring.edgeColour graphData.toRotationSystem c)
        r.pair (DualTruncateKempeTransport.edgeMask graphData.toRotationSystem frame.selected c r.pair r.mask))
      (DualTruncateColoring.colouring graphData.toRotationSystem
        (geometry.sourceColouring c hc a b hab hvalues)) := by
  dsimp only
  let r := geometry.repair c hc a b hab hvalues
  let := r.mask_decidable
  have hs := SourcePatchKempe.switched_exterior graphData.toRotationSystem frame.outside c hc
    r.pair r.mask r.region
  have hi := frame.reconstructed_extends (SourcePatchKempe.switched c r.pair r.mask) hs
    r.x r.y r.compatible
  have he := DualTruncateKempeTransport.exact_effect graphData.toRotationSystem frame.selected c
    r.pair r.mask (by simpa only [frame.outside_eq_not_selected] using hc)
    (by simpa only [frame.outside_eq_not_selected] using r.region)
  intro d hd i
  exact (hi d hd i).trans (he d hd i)

open TubeSlab.VertexTransfer VertexCodeSourceGeometry SourceVertexCodeTrace VertexConstructionGSLT

include geometry c hc a b hab hvalues in
/-- The reconstructed witness supplies compatible choices on every complete
faithful sweep of the actual expanded map. -/
theorem every_complete_sweep (order : List graphData.toRotationSystem.D)
    (hn : order.Nodup) (he : order ≠ []) (hcover : ∀ d, visited order d) :
    VertexConstructionGSLT.colouring.Supports
      (VertexConstructionGSLT.route (SourceVertexCodeTrace.encodeClosed
        (DualTruncateColoring.cubic graphData.toRotationSystem)
        (DualTruncateConstructionGSLT.rotationCyclic graphData.toRotationSystem)
        order hn he hcover).trace) Fin.elim0 Fin.elim0 :=
  DualTruncateConstructionGSLT.supported_encoded_route graphData.toRotationSystem
    (geometry.sourceColouring c hc a b hab hvalues) order hn he hcover

end Geometry

end
end Mettapedia.GraphTheory.FourColor.SourceAlternatingBoundaryRepair
