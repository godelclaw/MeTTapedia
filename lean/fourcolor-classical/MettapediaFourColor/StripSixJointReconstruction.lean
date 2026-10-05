import MettapediaFourColor.StripSixJointRepair
import MettapediaFourColor.PlanarGraphBoundaryClosure
import MettapediaFourColor.PatchBoundaryGluing

/-!
# Geometric consumers of the joint port-six repair

The local component reading supplies one of the two repaired boundary forms.
For a planar triangulated disk, the Gonthier/Emery Kempe theorem discharges
the closure premise. Compatible source and exterior colourings then glue
across complete core stars into a colouring of the ambient graph.

The exterior has strictly fewer vertices. The input boundary class remains
explicit: this does not say that every colouring of the smaller graph lies
in that class, or that every planar map supplies the patch.
-/

namespace FourColor.StripSixJointRepair

open Color SimpleGraph KempeBoundarySplit TriangleStripAnchors StripResponseSummary

/-- An actual component reading supplies the repaired boundary class. No extra
zero/two guard or successful preparation is required. -/
theorem classified_repair {V : Type*} {H : SimpleGraph V}
    (C : H.Coloring Color) (ports : Fin 11 → V)
    (embedding : ∀ i j, input0099.graph.Adj (port i) (port j) → H.Adj (ports i) (ports j))
    (closed : KempeClosed (GraphTrace H (List.ofFn ports)))
    (initial : ∀ i, C (ports i) ∈ StripSingletonRepair.before i)
    (K : (C.bicoloredSubgraph c0 c1).ConnectedComponent)
    (m6 : ports 6 ∈ C.kempeComponentSet c0 c1 K)
    (n8 : ports 8 ∉ C.kempeComponentSet c0 c1 K) :
    ∃ D : H.Coloring Color, ∃ k : input0099.graph.Coloring Color,
      ∀ i, k (port i) = D (ports i) := by
  obtain ⟨s, hs⟩ := StripSixConnection.classified C ports embedding initial K m6 n8
  have start : GraphTrace H (List.ofFn ports) (trace (List.ofFn (StripSixConnection.input s))) := by
    refine ⟨C, ?_⟩
    simp only [List.map_ofFn, Function.comp_def, hs]
  obtain ⟨D,k,agree,_⟩ := compatible_changed s H ports closed start
  exact ⟨D,k,agree⟩

open Mettapedia.GraphTheory.FourColor.SimpleGraphDartRotation

/-- Actual planar disk geometry supplies the closure used by the repair. -/
theorem disk_compatible {W : Type} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj]
    (rotation : Data H) (cyclic : rotation.IsVertexwiseCyclic)
    (planar : (SimpleGraphBridge.rotationHypermap rotation).Planar)
    (r : List H.Dart)
    (boundary : IsCyclicChain (fun a b => b = rotation.toRotationSystem.phi a) r)
    (distinct : r.Nodup)
    (triangles : ∀ d, d ∉ r → rotation.toRotationSystem.phi
      (rotation.toRotationSystem.phi (rotation.toRotationSystem.phi d)) = d)
    (ports : Fin 11 → W) (ordered : r.map (fun d => d.fst) = List.ofFn ports)
    (s : Bool) (C : H.Coloring Color)
    (initial : ∀ i, C (ports i) = StripSixConnection.input s i) :
    ∃ D : H.Coloring Color, ∃ k : input0099.graph.Coloring Color,
      ∀ i, k (port i) = D (ports i) := by
  have closed := PlanarGraphBoundaryClosure.rotation_closed rotation cyclic planar
    r boundary distinct triangles
  rw [ordered] at closed
  have start : GraphTrace H (List.ofFn ports) (trace (List.ofFn (StripSixConnection.input s))) := by
    refine ⟨C, ?_⟩
    simp only [List.map_ofFn, Function.comp_def, initial]
  obtain ⟨D,k,agree,_⟩ := compatible_changed s H ports closed start
  exact ⟨D,k,agree⟩

/-- Exact source stars and exterior coverage turn the local repair into a
colouring of the whole graph, preserving the entire repaired exterior.
Boundary identifications are allowed and their shared colours are retained. -/
theorem whole_repair_of_core_injective {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : input0099.graph →g G)
    (injective : Set.InjOn f {i : Fin 19 | 11 ≤ i.val})
    (no_capture : ∀ a : Fin 19, ¬11 ≤ a.val → f a ∉ f '' {i : Fin 19 | 11 ≤ i.val})
    (e : H ↪g G)
    (outside : ∀ w, e w ∉ f '' {i : Fin 19 | 11 ≤ i.val})
    (covers : ∀ v, v ∉ f '' {i : Fin 19 | 11 ≤ i.val} → ∃ w, e w = v)
    (stars : ∀ i : Fin 19, 11 ≤ i.val → ∀ v, G.Adj (f i) v →
      ∃ j, input0099.graph.Adj i j ∧ f j = v)
    (ports : Fin 11 → W) (boundary : ∀ i, e (ports i) = f (port i))
    (closed : KempeClosed (GraphTrace H (List.ofFn ports)))
    (s : Bool) (C : H.Coloring Color)
    (initial : ∀ i, C (ports i) = StripSixConnection.input s i) :
    Fintype.card W < Fintype.card V ∧
      ∃ D : H.Coloring Color, ∃ K : G.Coloring Color, ∀ w, K (e w) = D w := by
  classical
  have start : GraphTrace H (List.ofFn ports) (trace (List.ofFn (StripSixConnection.input s))) := by
    refine ⟨C, ?_⟩
    simp only [List.map_ofFn, Function.comp_def, initial]
  obtain ⟨D,k,agree,_⟩ := compatible_changed s H ports closed start
  let interior : Set (Fin 19) := {i | 11 ≤ i.val}
  let assignment (v : V) : Color := if h : v ∉ f '' interior then D (covers v h).choose else c0
  have read (w : W) : assignment (e w) = D w := by
    dsimp only [assignment]
    rw [dite_eq_left (outside w)]
    exact congrArg D (e.injective (covers _ (outside w)).choose_spec)
  have valid {v w} (hv : v ∉ f '' interior) (hw : w ∉ f '' interior)
      (edge : G.Adj v w) : assignment v ≠ assignment w := by
    obtain ⟨a,rfl⟩ := covers v hv
    obtain ⟨b,rfl⟩ := covers w hw
    rw [read,read]
    exact D.valid (e.map_adj_iff.mp edge)
  have agreement (a) (ha : a ∉ interior) : k a = assignment (f a) := by
    have h : a.val < 11 := by change ¬11 ≤ a.val at ha; omega
    let i : Fin 11 := ⟨a.val,h⟩
    have same : port i = a := Fin.ext rfl
    rw [← same, ← boundary, read]
    exact agree i
  obtain ⟨K,_,hK⟩ := PatchBoundaryGluing.reconstruct f interior injective
    no_capture stars k assignment valid agreement
  refine ⟨?_,D,K,fun w => (hK _ (outside w)).trans (read w)⟩
  apply Fintype.card_lt_of_injective_of_notMem e e.injective (b := f 11)
  rintro ⟨w,hw⟩
  exact outside w ⟨11,by decide,hw.symm⟩

/-- The globally injective specialization of the boundary-identification theorem. -/
theorem whole_repair {V W : Type*} [Fintype V] [Fintype W]
    {G : SimpleGraph V} {H : SimpleGraph W}
    (f : input0099.graph →g G) (injective : Function.Injective f)
    (e : H ↪g G)
    (outside : ∀ w, e w ∉ f '' {i : Fin 19 | 11 ≤ i.val})
    (covers : ∀ v, v ∉ f '' {i : Fin 19 | 11 ≤ i.val} → ∃ w, e w = v)
    (stars : ∀ i : Fin 19, 11 ≤ i.val → ∀ v, G.Adj (f i) v →
      ∃ j, input0099.graph.Adj i j ∧ f j = v)
    (ports : Fin 11 → W) (boundary : ∀ i, e (ports i) = f (port i))
    (closed : KempeClosed (GraphTrace H (List.ofFn ports)))
    (s : Bool) (C : H.Coloring Color)
    (initial : ∀ i, C (ports i) = StripSixConnection.input s i) :
    Fintype.card W < Fintype.card V ∧
      ∃ D : H.Coloring Color, ∃ K : G.Coloring Color, ∀ w, K (e w) = D w := by
  apply whole_repair_of_core_injective f injective.injOn ?_ e outside covers stars
    ports boundary closed s C initial
  intro a ha
  rintro ⟨i,hi,eq⟩
  exact ha (injective eq ▸ hi)

/-- A complete planar-disk consumer: closure is derived from its rotation,
then the repaired source and exterior reconstruct the ambient graph. -/
theorem disk_whole_repair {V : Type*} {W : Type} [Fintype V] [Fintype W] [DecidableEq W]
    {G : SimpleGraph V} {H : SimpleGraph W} [DecidableRel H.Adj]
    (f : input0099.graph →g G) (injective : Function.Injective f)
    (e : H ↪g G)
    (outside : ∀ w, e w ∉ f '' {i : Fin 19 | 11 ≤ i.val})
    (covers : ∀ v, v ∉ f '' {i : Fin 19 | 11 ≤ i.val} → ∃ w, e w = v)
    (stars : ∀ i : Fin 19, 11 ≤ i.val → ∀ v, G.Adj (f i) v →
      ∃ j, input0099.graph.Adj i j ∧ f j = v)
    (ports : Fin 11 → W) (port_boundary : ∀ i, e (ports i) = f (port i))
    (rotation : Data H) (cyclic : rotation.IsVertexwiseCyclic)
    (planar : (SimpleGraphBridge.rotationHypermap rotation).Planar)
    (r : List H.Dart)
    (boundary : IsCyclicChain (fun a b => b = rotation.toRotationSystem.phi a) r)
    (distinct : r.Nodup)
    (triangles : ∀ d, d ∉ r → rotation.toRotationSystem.phi
      (rotation.toRotationSystem.phi (rotation.toRotationSystem.phi d)) = d)
    (ordered : r.map (fun d => d.fst) = List.ofFn ports)
    (s : Bool) (C : H.Coloring Color)
    (initial : ∀ i, C (ports i) = StripSixConnection.input s i) :
    Fintype.card W < Fintype.card V ∧
      ∃ D : H.Coloring Color, ∃ K : G.Coloring Color, ∀ w, K (e w) = D w := by
  have closed := PlanarGraphBoundaryClosure.rotation_closed rotation cyclic planar
    r boundary distinct triangles
  rw [ordered] at closed
  exact whole_repair f injective e outside covers stars ports port_boundary closed s C initial

end FourColor.StripSixJointRepair
