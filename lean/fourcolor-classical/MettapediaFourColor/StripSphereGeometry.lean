import MettapediaFourColor.StripSpherePhase

/-! # Exact exterior deletion and spherical geometry for the phase example -/

namespace FourColor.StripSpherePhase

open SimpleGraph
set_option maxRecDepth 10000

def Outside (v : Fin 162) : Prop := ∀ i : Fin 8, v ≠ image (i.natAdd 11)
instance (v) : Decidable (Outside v) := by unfold Outside; infer_instance

def position : Fin 162 → Fin 154 := ![0,1,2,3,4,5,6,7,8,9,10,0,11,12,13,14,0,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,0,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,0,94,95,0,96,97,98,99,100,0,101,102,103,104,105,106,107,108,0,0,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127,128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153]

theorem position_include : ∀ v, position (includeExterior v) = v := by decide +kernel
theorem outside_include : ∀ v, Outside (includeExterior v) := by decide +kernel
theorem include_position : ∀ v, Outside v → includeExterior (position v) = v := by decide +kernel

theorem include_injective : Function.Injective includeExterior :=
  Function.LeftInverse.injective position_include

theorem outside_iff (v : Fin 162) : Outside v ↔ ∃ w, includeExterior w = v :=
  ⟨fun h => ⟨position v, include_position v h⟩, fun ⟨w,h⟩ => h ▸ outside_include w⟩

theorem forward : ∀ u, (neighbors u).all (fun v => decide (ambient.Adj (includeExterior u) (includeExterior v))) = true := by decide +kernel
theorem reverse : ∀ u, (star (includeExterior u)).all (fun v => decide (Outside v → exterior.Adj u (position v))) = true := by decide +kernel

theorem exterior_adj (u v : Fin 154) : exterior.Adj u v ↔ ambient.Adj (includeExterior u) (includeExterior v) := by
  constructor
  · intro h
    exact of_decide_eq_true (List.all_eq_true.mp (forward u) v h)
  · intro h
    have hv := of_decide_eq_true (List.all_eq_true.mp (reverse u) (includeExterior v) h) (outside_include v)
    simpa only [position_include] using hv

def embedding : exterior ↪g ambient where
  toFun := includeExterior
  inj' := include_injective
  map_rel_iff' := fun {_ _} => (exterior_adj _ _).symm

theorem source_edges : ∀ i j, TriangleStripAnchors.input0099.graph.Adj i j → ambient.Adj (image i) (image j) := by decide +kernel
theorem source_injective : Function.Injective image := by decide +kernel
theorem core_stars : ∀ i : Fin 8, ∀ v : Fin 162,
    ambient.Adj (image (i.natAdd 11)) v ↔ ∃ j : Fin 19,
      TriangleStripAnchors.input0099.graph.Adj (i.natAdd 11) j ∧ image j = v := by decide +kernel
theorem boundary_aligned : ∀ j, includeExterior (ports j) = image (j.castAdd 8) := by decide +kernel

theorem row_nodup : ∀ v, (star v).Nodup := by decide +kernel

def rows : GraphRotationRows.Rows ambient := ⟨star,row_nodup,fun _ _ => Iff.rfl⟩
def rotation := rows.rotation (⟨(0,(star 0).head!), by decide +kernel⟩ : ambient.Dart)
theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _

def faceStep (p : Fin 162 × Fin 162) := (p.2,rows.next p.2 p.1)
theorem face_check : ∀ u, (star u).all (fun v => decide
    (faceStep (faceStep (faceStep (u,v))) = (u,v))) = true := by decide +kernel

theorem triangular : ExceptionalOverlap.Triangular rotation := by
  intro d
  apply Dart.ext
  change faceStep (faceStep (faceStep d.toProd)) = d.toProd
  exact of_decide_eq_true (List.all_eq_true.mp (face_check d.fst) d.snd d.adj)

def tour : List (Fin 162) := [0,13,43,42,45,14,44,46,16,106,108,34,69,5,67,68,33,70,146,29,63,32,66,4,30,62,25,58,3,59,26,57,21,53,22,2,54,52,17,1,48,118,20,83,82,8,84,23,24,87,9,27,28,61,136,92,10,93,31,65,138,142,138,65,31,149,150,96,41,100,11,97,38,37,80,79,36,81,7,77,109,15,12,47,49,18,104,102,103,102,107,122,121,19,50,51,105,113,114,35,78,111,78,153,156,85,86,131,132,39,89,90,134,90,157,91,40,88,141,95,94,159,155,159,94,160,161,160,94,95,141,143,141,88,40,91,157,90,89,154,89,39,132,131,86,85,156,153,78,35,114,113,105,51,50,117,119,6,72,76,75,73,74,130,126,128,126,130,74,139,135,137,135,139,74,73,75,148,64,144,64,148,75,76,124,76,72,123,72,6,119,117,50,19,121,122,107,102,104,18,49,47,12,15,109,77,112,110,116,115,99,98,101,152,151,145,147,145,151,152,101,98,99,115,116,110,112,158,112,77,7,81,36,79,80,37,38,97,11,100,41,96,150,149,31,93,10,92,136,61,140,60,133,129,56,55,120,125,120,55,56,127,56,129,133,60,140,61,28,27,9,87,24,23,84,8,82,83,20,118,48,1,17,52,54,2,22,53,21,57,26,59,3,58,25,62,30,4,66,32,63,29,146,70,33,68,67,71,67,5,69,34,108,106,16,46,44,14,45,42,43,13,0]

theorem tour_chain : tour.IsChain ambient.Adj := by decide +kernel
theorem tour_covers : ∀ v : Fin 162, v ∈ tour := by decide +kernel

theorem connected : ambient.Connected := by
  let p := Walk.ofSupport tour (by decide +kernel) tour_chain
  have reach (v : Fin 162) : ambient.Reachable (tour.head (by decide +kernel)) v := by
    refine ⟨p.takeUntil v ?_⟩
    simpa only [p, Walk.support_ofSupport] using tour_covers v
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

theorem dart_count : Nat.card ambient.Dart = 960 := by
  rw [rows.dart_count]
  decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar :=
  (GraphTriangulationEuler.planar_iff_balance rotation cyclic connected
    (GraphTriangulationEuler.covered connected) triangular).mpr
      (by rw [Nat.card_fin, dart_count])

theorem degree_bounds (v : Fin 162) : 5 ≤ ambient.degree v ∧ ambient.degree v ≤ 7 := by
  have degree : ambient.degree v = (star v).length := by
    have same : ambient.degree v =
        @SimpleGraph.degree (Fin 162) ambient v (Subtype.fintype _) :=
      congrArg (@SimpleGraph.degree (Fin 162) ambient v) (Subsingleton.elim _ _)
    exact same.trans (rows.degree v)
  rw [degree]
  exact (by decide +kernel : ∀ v : Fin 162, 5 ≤ (star v).length ∧ (star v).length ≤ 7) v

/-- The source witness is glued to the same actual exterior after two
physical switches; all 162 vertices have a proper colour. -/
theorem whole_repair : ∃ D : exterior.Coloring Color, ∃ history :
    Mettapedia.GraphTheory.FourColor.KempeChainCertificate.History (state 0) D,
      history.length = 2 ∧ ∃ k : ambient.Coloring Color,
        ∀ v, k (includeExterior v) = D v :=
  ⟨state 2, repairHistory, repair_length, finalColouring, reconstructed⟩

/-- The lower bound applies to any proposed full ambient reconstruction. -/
theorem no_phase_reconstruction (a b : Color) (D : exterior.Coloring Color)
    (phase : Relation.ReflTransGen (KempePairHistory.Step a b) (state 0) D)
    (K : ambient.Coloring Color) (fixed : ∀ v, K (includeExterior v) = D v) : False := by
  let k : (TriangleStripAnchors.input0099.graph.induce
      {v | StripPartialColouring.Live ∅ v}).Coloring Color :=
    .mk (fun v => K (image v.val)) (fun edge => K.valid (source_edges _ _ edge))
  have boundary : ∀ i, k ⟨StripResponseSummary.port i,
      StripPartialColouring.live_port ∅ i⟩ = D (ports i) := by
    intro i
    change K (image (i.castAdd 8)) = D (ports i)
    rw [← boundary_aligned, fixed]
  obtain ⟨f,hf⟩ := StripPartialColouring.validExcept_of_source
    (fun i => D (ports i)) ∅ k boundary
  have impossible := any_phase_requires_two a b D phase hf
  simp at impossible

/-- Two mixed-pair switches attain the exact physical lower bound. -/
theorem history_needs_two (D : exterior.Coloring Color)
    (history : Mettapedia.GraphTheory.FourColor.KempeChainCertificate.History (state 0) D)
    (K : ambient.Coloring Color) (fixed : ∀ v, K (includeExterior v) = D v) :
    2 ≤ history.length := by
  cases history with
  | refl => exact (no_phase_reconstruction Color.c0 Color.c1 _ .refl K fixed).elim
  | cons step rest =>
      cases rest with
      | refl =>
          obtain ⟨a,b,component,rfl⟩ := step.toKempeStep
          exact (no_phase_reconstruction a b _ (.single ⟨component,rfl⟩) K fixed).elim
      | cons next tail =>
          simp only [Mettapedia.GSLT.Ultrainfinite.Route.length]
          omega

end FourColor.StripSpherePhase
