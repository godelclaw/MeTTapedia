import MettapediaFourColor.PatchDiskRepair

/-! # A spherical example with two source boundary ports identified

Source ports zero and two name the same actual vertex. The core remains
injective and all its cyclic rows are preserved. Deletion leaves an eleven-
dart facial boundary on ten distinct boundary vertices, including a bridge.
This tests geometry and closure, not supply of the two-form repair colouring.
-/

namespace FourColor.PatchDiskFoldedExample

open SimpleGraph PatchDisk PatchDiskSources TriangleStripAnchors

set_option maxRecDepth 10000

def fold (i : Fin 19) : Fin 19 := if i = 2 then 0 else i

def star (v : Fin 19) : List (Fin 19) :=
  if v = 0 then [10,18,1,16,3,2]
  else if v = 1 then [0,18,16]
  else if v = 2 then [0,3,4,5,6,7,8,9,10]
  else if h : v.val < 11 then (fan0099 ⟨v.val,h⟩).map fold ++ [2]
  else (input0099.internalStar v).reverse.map fold

private theorem symmetric : ∀ u v : Fin 19, v ∈ star u → u ∈ star v := by decide +kernel
private theorem loopless : ∀ v : Fin 19, v ∉ star v := by decide +kernel

def graph : SimpleGraph (Fin 19) where
  Adj u v := v ∈ star u
  symm := ⟨symmetric⟩
  loopless := ⟨loopless⟩

instance : DecidableRel graph.Adj := fun _ _ => inferInstanceAs (Decidable (_ ∈ _))

def rows : GraphRotationRows.Rows graph :=
  ⟨star, by decide +kernel, fun _ _ => Iff.rfl⟩

def rotation := rows.rotation (⟨(0,1), by decide +kernel⟩ : graph.Dart)

theorem cyclic : rotation.IsVertexwiseCyclic := rows.cyclic _

theorem triangular : ExceptionalOverlap.Triangular rotation := by
  unfold ExceptionalOverlap.Triangular
  decide +kernel

def hom : input0099.graph →g graph where
  toFun := fold
  map_rel' := by decide +kernel

theorem core_turn : ∀ i j k, StripCyclicReading.Turn i j k →
    ExceptionalCoreOrientation.Corner rotation (hom i) (hom k) (hom j) := by
  have h : ∀ i j k : Fin 19, StripCyclicReading.Turn i j k →
      graph.Adj (hom i) (hom k) ∧ graph.Adj (hom i) (hom j) ∧
        rows.next (hom i) (hom k) = hom j := by decide +kernel
  intro i j k ht
  obtain ⟨hik, hij, step⟩ := h i j k ht
  exact ⟨hik, hij, Dart.ext _ _ (Prod.ext rfl step)⟩


theorem degrees : ∀ i : Fin 19, 11 ≤ i.val →
    graph.degree (hom i) = input0099.graph.degree i := by
  have h : ∀ i : Fin 19, 11 ≤ i.val → (star (hom i)).length =
      @SimpleGraph.degree (Fin 19) input0099.graph i (Subtype.fintype _) := by
    decide +kernel
  intro i hi
  have ambient : graph.degree (hom i) =
      @SimpleGraph.degree (Fin 19) graph (hom i) (Subtype.fintype _) :=
    congrArg (@SimpleGraph.degree (Fin 19) graph (hom i)) (Subsingleton.elim _ _)
  have source : input0099.graph.degree i =
      @SimpleGraph.degree (Fin 19) input0099.graph i (Subtype.fintype _) :=
    congrArg (@SimpleGraph.degree (Fin 19) input0099.graph i) (Subsingleton.elim _ _)
  exact ambient.trans ((rows.degree (hom i)).trans ((h i hi).trans source.symm))

def source : StripCyclicReading.Reading rotation := ⟨hom,core_turn⟩

theorem fold_core (i : Fin 19) (hi : 11 ≤ i.val) : fold i = i := by
  have ne : i ≠ 2 := by intro h; subst i; contradiction
  simp only [fold, ite_eq_right_iff.mpr (fun h => False.elim (ne h))]

theorem fold_boundary (i : Fin 19) (hi : i.val < 11) : (fold i).val < 11 := by
  by_cases h : i = 2
  · subst i; decide +kernel
  · simpa only [fold, ite_eq_right_iff.mpr (fun eq => False.elim (h eq))] using hi

def reading : Reading d0099 rotation := of_d0099 source cyclic
  (by
    intro i hi j hj eq
    change fold i = fold j at eq
    rwa [fold_core i hi, fold_core j hj] at eq)
  (by
    intro a ha
    rintro ⟨i,hi,eq⟩
    change fold i = fold a at eq
    rw [fold_core i hi] at eq
    have low := fold_boundary a (Nat.lt_of_not_ge ha)
    rw [← eq] at low
    exact (Nat.not_lt_of_ge hi) low)
  degrees

theorem identified : reading.hom 0 = reading.hom 2 := rfl

theorem not_injective : ¬ Function.Injective reading.hom := by
  intro h
  exact (by decide : (0 : Fin 19) ≠ 2) (h identified)

def tour : List (Fin 19) :=
  [0,10,9,8,7,6,5,4,3,16,1,18,17,15,12,11,14,13,14,11,12,15,17,18,
   1,16,3,2,3,4,5,6,7,8,9,10,0]

theorem tour_chain : tour.IsChain graph.Adj := by decide +kernel
theorem tour_covers : ∀ v : Fin 19, v ∈ tour := by decide +kernel

theorem connected : graph.Connected := by
  let p := Walk.ofSupport tour (by decide +kernel) tour_chain
  have reach (v : Fin 19) : graph.Reachable (tour.head (by decide +kernel)) v := by
    refine ⟨p.takeUntil v ?_⟩
    simpa only [p, Walk.support_ofSupport] using tour_covers v
  exact ⟨fun u v => (reach u).symm.trans (reach v)⟩

theorem dart_count : Nat.card graph.Dart = 102 := by
  rw [rows.dart_count]
  decide +kernel

theorem planar : (SimpleGraphBridge.rotationHypermap rotation).Planar :=
  (GraphTriangulationEuler.planar_iff_balance rotation cyclic connected
    (GraphTriangulationEuler.covered connected) triangular).mpr
      (by rw [Nat.card_fin,dart_count])

theorem deleted_planar :
    (SimpleGraphBridge.rotationHypermap (reading.outsideRotation)).Planar :=
  reading.outside_planar triangular cyclic connected planar

theorem deleted_vertices : Nat.card (reading.keep) = 11 := by
  have h := reading.deletion_vertex_count
  rw [Nat.card_fin] at h
  omega

theorem boundary_distinct : reading.outsideRing.Nodup :=
  reading.outside_distinct triangular

theorem boundary_order : reading.outsideRing.map (fun d => d.fst) =
    List.ofFn (reading.port) := reading.outside_order

theorem closed : KempeClosed
    (KempeBoundarySplit.GraphTrace (graph.induce reading.keep) (List.ofFn reading.port)) :=
  reading.exterior_closed triangular cyclic connected planar

end FourColor.PatchDiskFoldedExample
