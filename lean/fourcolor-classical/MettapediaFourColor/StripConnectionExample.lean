import MettapediaFourColor.StripConnectionRepair
import MettapediaFourColor.GraphSphericalEuler
import MettapediaFourColor.GraphTriangulationEuler
import MettapediaFourColor.PatchBoundaryGluing

/-!
# A spherical consumer of the geometric connection repair

An exterior edge flip creates the connection excluded by singleton repair.
Two initial colourings on this sphere consume the same separation theorem
and core formula. Only initial data and the short connecting path are
checked; the complementary component and final colouring are derived.
-/

namespace FourColor.StripConnectionExample

open Color SimpleGraph StripResponseSummary
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate
set_option maxRecDepth 10000

def star : Fin 24 → List (Fin 24) := ![[1,13,15,11,10,23],
    [0,23,21,2,13],
    [1,21,3,12,13],
    [2,21,18,4,14,12],
    [3,18,19,5,14],
    [4,19,6,11,14],
    [5,19,16,7,11],
    [6,16,8,9,10,11],
    [7,16,17,20,9],
    [7,8,20,22,10],
    [0,11,7,9,22,23],
    [0,15,14,5,6,7,10],
    [2,3,14,15,13],
    [0,1,2,12,15],
    [3,4,5,11,15,12],
    [0,13,12,14,11],
    [6,19,17,8,7],
    [8,16,19,18,20],
    [3,21,22,20,17,19,4],
    [4,18,17,16,6,5],
    [8,17,18,22,9],
    [1,23,22,18,3,2],
    [9,20,18,21,23,10],
    [0,10,22,21,1]]
theorem row_nodup : ∀ v, (star v).Nodup := by decide +kernel
theorem row_symm : ∀ u v, v ∈ star u → u ∈ star v := by decide +kernel
theorem row_loopless : ∀ v, v ∉ star v := by decide +kernel

def ambient : SimpleGraph (Fin 24) where
  Adj u v := v ∈ star u
  symm := ⟨row_symm⟩
  loopless := ⟨row_loopless⟩
instance : DecidableRel ambient.Adj := by unfold ambient; infer_instance

def rows : GraphRotationRows.Rows ambient := ⟨star,row_nodup,fun _ _ => Iff.rfl⟩
def rotation := rows.rotation (⟨(0,(star 0).head!), by decide +kernel⟩ : ambient.Dart)
theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _
def faceStep (p : Fin 24 × Fin 24) := (p.2,rows.next p.2 p.1)
theorem face_check : ∀ u, (star u).all (fun v => decide
    (faceStep (faceStep (faceStep (u,v))) = (u,v))) = true := by decide +kernel

theorem triangular : ExceptionalOverlap.Triangular rotation := by
  intro d
  apply Dart.ext
  change faceStep (faceStep (faceStep d.toProd)) = d.toProd
  exact of_decide_eq_true (List.all_eq_true.mp (face_check d.fst) d.snd d.adj)

def tour : List (Fin 24) :=
  [0,1,23,10,11,15,13,2,21,22,9,7,6,5,4,3,18,20,8,16,19,17,19,16,
   8,20,18,3,14,12,14,3,4,5,6,7,9,22,21,2,13,15,11,10,23,1,0]
theorem tour_chain : tour.IsChain ambient.Adj := by decide +kernel
theorem tour_covers : ∀ v : Fin 24, v ∈ tour := by decide +kernel

theorem connected : ambient.Connected := by
  let p := Walk.ofSupport tour (by decide +kernel) tour_chain
  have reach (v : Fin 24) : ambient.Reachable (tour.head (by decide +kernel)) v := by
    refine ⟨p.takeUntil v ?_⟩
    simpa only [p, Walk.support_ofSupport] using tour_covers v
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

theorem dart_count : Nat.card ambient.Dart = 132 := by
  rw [rows.dart_count]
  decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar :=
  (GraphTriangulationEuler.planar_iff_balance rotation cyclic connected
    (GraphTriangulationEuler.covered connected) triangular).mpr
      (by rw [Nat.card_fin, dart_count])

theorem degree_eq (v : Fin 24) : ambient.degree v = (star v).length := by
  have same : ambient.degree v =
      @SimpleGraph.degree (Fin 24) ambient v (Subtype.fintype _) :=
    congrArg (@SimpleGraph.degree (Fin 24) ambient v) (Subsingleton.elim _ _)
  exact same.trans (rows.degree v)

theorem minimum_degree (v : Fin 24) : 5 ≤ ambient.degree v := by
  rw [degree_eq]
  exact (by decide +kernel : ∀ v : Fin 24, 5 ≤ (star v).length) v

theorem maximum_degree (v : Fin 24) : ambient.degree v ≤ 7 := by
  rw [degree_eq]
  exact (by decide +kernel : ∀ v : Fin 24, (star v).length ≤ 7) v

def neighbours : Fin 16 → List (Fin 16) := ![[1,10,11,13,15],
    [0,2,13],
    [1,3,12,13],
    [2,4,12,14],
    [3,5,14],
    [4,6,11,14],
    [5,7,11],
    [6,8,9,10,11],
    [7,9],
    [7,8,10],
    [0,7,9,11],
    [0,5,6,7,10,14,15],
    [2,3,13,14,15],
    [0,1,2,12,15],
    [3,4,5,11,12,15],
    [0,11,12,13,14]]
theorem neighbours_symm : ∀ u v, v ∈ neighbours u → u ∈ neighbours v := by decide +kernel
theorem neighbours_loopless : ∀ v, v ∉ neighbours v := by decide +kernel

def exterior : SimpleGraph (Fin 16) where
  Adj u v := v ∈ neighbours u
  symm := ⟨neighbours_symm⟩
  loopless := ⟨neighbours_loopless⟩
instance : DecidableRel exterior.Adj := by unfold exterior; infer_instance

def includeExterior (v : Fin 16) : Fin 24 := v.castAdd 8
theorem exterior_adj : ∀ u v, exterior.Adj u v ↔
    ambient.Adj (includeExterior u) (includeExterior v) := by decide +kernel

def port (i : Fin 11) : Fin 16 := i.castLE (by decide)
def sourceVertex (v : Fin 19) : Fin 24 :=
  Fin.addCases (m := 11) (n := 8) (motive := fun _ => Fin 24)
    (fun i => i.castLE (by decide)) (fun i => i.natAdd 16) v

theorem source_edges : ∀ u v, TriangleStripAnchors.input0099.graph.Adj u v →
    ambient.Adj (sourceVertex u) (sourceVertex v) := by decide +kernel
theorem source_injective : Function.Injective sourceVertex := by decide +kernel
theorem core_stars : ∀ i : Fin 8, ∀ v : Fin 24,
    ambient.Adj (i.natAdd 16) v ↔ ∃ j : Fin 19,
      TriangleStripAnchors.input0099.graph.Adj (i.natAdd 11) j ∧
        sourceVertex j = v := by decide +kernel
theorem boundary_aligned : ∀ i, sourceVertex (StripResponseSummary.port i) =
    includeExterior (port i) := by decide +kernel


open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open GoertzelV24SimpleGraphFaceDualConnectedness

theorem face_data : ∀ a b c, (a,b,c) ∈ StripConnectionGeometry.triangles →
    ambient.Adj (sourceVertex a) (sourceVertex b) ∧
    ambient.Adj (sourceVertex b) (sourceVertex c) ∧
    ambient.Adj (sourceVertex c) (sourceVertex a) ∧
    faceStep (sourceVertex a,sourceVertex b) = (sourceVertex b,sourceVertex c) ∧
    faceStep (sourceVertex b,sourceVertex c) = (sourceVertex c,sourceVertex a) ∧
    faceStep (sourceVertex c,sourceVertex a) = (sourceVertex a,sourceVertex b) := by
  decide +kernel

def patch : StripConnectionGeometry.Patch rotation where
  point := sourceVertex
  injective := source_injective
  adjacent := source_edges
  facial := by
    intro a b c h
    obtain ⟨ab,bc,ca,hab,hbc,hca⟩ := face_data a b c h
    refine ⟨ab,bc,ca,?_,?_,?_⟩
    · apply Dart.ext; exact hab
    · apply Dart.ext; exact hbc
    · apply Dart.ext; exact hca

def exteriorEmbedding : exterior ↪g ambient where
  toFun := includeExterior
  inj' := by intro u v h; exact Fin.ext (congrArg (fun x : Fin 24 => x.val) h)
  map_rel_iff' := fun {_ _} => (exterior_adj _ _).symm

def reading : StripConnectionGeometry.ExteriorReading patch exterior where
  embedding := exteriorEmbedding
  outside := by
    intro w i hi h
    change includeExterior w = sourceVertex i at h
    have shape : ∀ i : Fin 19, 11 ≤ i.val → 16 ≤ (sourceVertex i).val := by decide +kernel
    have eq := congrArg (fun x : Fin 24 => x.val) h
    have bound := shape i hi
    change w.val = (sourceVertex i).val at eq
    omega
  ports := port
  boundary := fun i => (boundary_aligned i).symm

def values : Fin 2 → Fin 16 → Color
  | 0 => ![c0,c1,c0,c2,c3,c1,c2,c0,c1,c3,c1,c3,c1,c3,c0,c2]
  | 1 => ![c0,c1,c0,c3,c2,c1,c2,c0,c1,c3,c1,c3,c1,c3,c0,c2]
theorem proper : ∀ s u v, exterior.Adj u v → values s u ≠ values s v := by decide +kernel
def initial (s : Fin 2) : exterior.Coloring Color := .mk (values s) (fun h => proper s _ _ h)
theorem ready : ∀ s i, initial s (port i) ∈ StripSingletonRepair.before i := by decide +kernel

def connection : exterior.Walk (port 8) (port 10) :=
  .cons (by decide +kernel : exterior.Adj (port 8) 7)
    (.cons (by decide +kernel) .nil)
theorem active : ∀ s x, x ∈ connection.support → initial s x = c0 ∨ initial s x = c1 := by
  decide +kernel

theorem source (s : Fin 2) : ∃ D : exterior.Coloring Color, ∃ h : History (initial s) D,
    h.length = 1 ∧ ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      ∀ i, k (StripResponseSummary.port i) = D (port i) := by
  exact reading.repair_of_path
    (hasCyclicVertexRotations_implies_vertexRotationCyclic
      ambient rotation cyclic)
    (GoertzelV24NonisolatedFaceDualConnectedness.orbitFaceInteriorDual_connected_of_simpleGraph
      rotation connected cyclic)
    connected
    (GraphSphericalEuler.balance rotation cyclic connected
      (GraphTriangulationEuler.covered connected) planar)
    (initial s) connection (active s) (ready s)

def sourceHom : TriangleStripAnchors.input0099.graph →g ambient := ⟨sourceVertex,fun h =>
  source_edges _ _ h⟩
def interior : Set (Fin 19) := {v | 11 ≤ v.val}
def exteriorVertex (v : Fin 24) : Fin 16 := ⟨v.val % 16,Nat.mod_lt _ (by decide)⟩

instance (v : Fin 24) : Decidable (v ∈ sourceHom '' interior) :=
  inferInstanceAs (Decidable (∃ a : Fin 19, 11 ≤ a.val ∧ sourceVertex a = v))

theorem source_core (i : Fin 8) : sourceHom (i.natAdd 11) = i.natAdd 16 := by
  simp [sourceHom,sourceVertex]

theorem no_capture (a : Fin 19) (ha : a ∉ interior) : sourceHom a ∉ sourceHom '' interior := by
  rintro ⟨i,hi,heq⟩
  exact ha ((source_injective heq) ▸ hi)

theorem covers (i : Fin 19) (hi : i ∈ interior) (v : Fin 24)
    (edge : ambient.Adj (sourceHom i) v) :
    ∃ a, TriangleStripAnchors.input0099.graph.Adj i a ∧ sourceHom a = v := by
  revert hi edge
  refine Fin.addCases (m := 11) (n := 8)
    (motive := fun i => i ∈ interior → ambient.Adj (sourceHom i) v →
      ∃ a, TriangleStripAnchors.input0099.graph.Adj i a ∧ sourceHom a = v)
    (fun j hj _ => ?_) (fun j _ edge => ?_) i
  · have h : 11 ≤ j.val := hj
    omega
  · rw [source_core] at edge
    exact (core_stars j v).mp edge

theorem exterior_edges : ∀ v w,
    v ∉ sourceHom '' interior → w ∉ sourceHom '' interior → ambient.Adj v w →
      exterior.Adj (exteriorVertex v) (exteriorVertex w) := by decide +kernel
theorem boundary_position : ∀ i,
    exteriorVertex (sourceHom (StripResponseSummary.port i)) = port i := by decide +kernel
theorem exterior_position : ∀ v, exteriorVertex (includeExterior v) = v := by decide +kernel
theorem exterior_outside : ∀ v, includeExterior v ∉ sourceHom '' interior := by decide +kernel

/-- Every source witness fitting an actual exterior colours the whole sphere. -/
theorem assemble (D : exterior.Coloring Color)
    (k : TriangleStripAnchors.input0099.graph.Coloring Color)
    (agree : ∀ i, k (StripResponseSummary.port i) = D (port i)) :
    ∃ whole : ambient.Coloring Color, ∀ v, whole (includeExterior v) = D v := by
  obtain ⟨whole,_,outside⟩ := PatchBoundaryGluing.reconstruct sourceHom interior
    source_injective.injOn no_capture covers k (fun v => D (exteriorVertex v))
    (fun hv hw edge => D.valid (exterior_edges _ _ hv hw edge)) (by
      intro a
      refine Fin.addCases (m := 11) (n := 8)
        (motive := fun a => a ∉ interior → k a = D (exteriorVertex (sourceHom a)))
        (fun i _ => ?_) (fun i hi => ?_) a
      · have eq : Fin.castAdd 8 i = StripResponseSummary.port i := by ext; rfl
        rw [eq,boundary_position]
        exact agree i
      · exact (hi (by change 11 ≤ 11 + i.val; omega)).elim)
  refine ⟨whole,fun v => ?_⟩
  rw [outside _ (exterior_outside v),exterior_position]


/-- Two actual initial colourings use the same geometric alternative. -/
theorem reconstructed (s : Fin 2) : ∃ D : exterior.Coloring Color,
    ∃ h : History (initial s) D, h.length = 1 ∧
      ∃ whole : ambient.Coloring Color, ∀ v, whole (includeExterior v) = D v := by
  obtain ⟨D,h,one,k,agree⟩ := source s
  exact ⟨D,h,one,assemble D k agree⟩

end FourColor.StripConnectionExample
