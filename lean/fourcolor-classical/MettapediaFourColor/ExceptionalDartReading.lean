import MettapediaFourColor.ExceptionalBoundaryOccurrence
import MettapediaFourColor.ExceptionalConstruction
import MettapediaFourColor.DualGraphQuery
import MettapediaFourColor.FaithfulKernelEmbedding

/-!
# Faithful exceptional core darts from the completed cyclic stars

The complete nineteen-vertex reading determines every source dart by its
ordered endpoints. Core injectivity and the full cyclic stars preserve core
dart identity. Ring vertices remain outside the core, even when different
ring labels have the same image. This excludes precisely the extra edge
identifications relevant to the local embedding contract.
-/

namespace FourColor.ExceptionalDartReading

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCore ExceptionalCoreOrientation ExceptionalOverlap
open ExceptionalBoundaryCompletion ExceptionalBoundaryOccurrence
open ExceptionalConstruction FaithfulKernelEmbedding

set_option maxRecDepth 32768

theorem source_edge : ∀ d : Fin 86,
    input.graph.Adj (ExceptionalConstruction.vertex d)
      (ExceptionalConstruction.vertex (table.map.edge d)) := by decide +kernel

theorem source_plain : table.map.Plain := by constructor <;> decide +kernel

theorem endpoints_injective : Function.Injective (fun d : Fin 86 =>
    (ExceptionalConstruction.vertex d, ExceptionalConstruction.vertex (table.map.edge d))) := by
  decide +kernel

theorem same_face_iff (d e : Fin 86) :
    table.map.CFace d e ↔ ExceptionalConstruction.vertex d = ExceptionalConstruction.vertex e := by
  constructor
  · exact congr_of_sameCycle faces.vertex_face
  · intro eq
    apply (faces.same_face d).trans
    change table.map.CFace (representative (ExceptionalConstruction.vertex d)) e
    rw [eq]
    exact (faces.same_face e).symm

theorem kernel_iff (d : Fin 86) :
    table.map.Kernel ring.reverse d ↔ 11 ≤ (ExceptionalConstruction.vertex d).val := by
  simp only [Hypermap.Kernel, Hypermap.Fband, same_face_iff]
  revert d
  decide +kernel

/-- Finite incidence locates a dart in one full core star and retains its
next step, including edges to the completed ring. -/
theorem source_position : ∀ (i : Fin 8) (d : Fin 86),
    ExceptionalConstruction.vertex d = i.natAdd 11 →
      ∃ p : Fin (coreDegree i),
        ExceptionalConstruction.vertex (table.map.edge d) = fullSpoke i p ∧
        ExceptionalConstruction.vertex (table.map.face d) = i.natAdd 11 ∧
        ExceptionalConstruction.vertex (table.map.edge (table.map.face d)) =
          fullSpoke i (nextPos i p) := by decide +kernel

set_option maxHeartbeats 8000000 in
-- Enumerate only the eight complete cyclic stars, not ambient graphs.
theorem source_cycles : ∀ (i : Fin 8) (d : Fin 86),
    ExceptionalConstruction.vertex d = i.natAdd 11 →
      IsCyclicChain (fun u v => v = table.map.face u)
        (ConfigurationFaceGraph.faceCycle table.map d (coreDegree i)) ∧
      (ConfigurationFaceGraph.faceCycle table.map d (coreDegree i)).Nodup ∧
      ConfigurationFaceGraph.faceCycle table.map d (coreDegree i) ≠ [] ∧
      (ConfigurationFaceGraph.faceCycle table.map d (coreDegree i)).headD d = d := by
  unfold IsCyclicChain
  decide +kernel

theorem source_arity (i : Fin 8) (d : Fin 86)
    (hi : ExceptionalConstruction.vertex d = i.natAdd 11) :
    table.map.arity d = coreDegree i := by
  obtain ⟨hc, hn, he, hh⟩ := source_cycles i d hi
  have eq := ConfigurationFaceGraph.faceCycle_eq_orbit (M := table.map) d (coreDegree i) hc hn he hh
  have len := congrArg List.length eq
  simpa [ConfigurationFaceGraph.faceCycle, length_orbitList, Hypermap.arity] using len.symm

theorem core_label {d : Fin 86} (hk : table.map.Kernel ring.reverse d) :
    ∃ i : Fin 8, ExceptionalConstruction.vertex d = i.natAdd 11 := by
  have bound := (kernel_iff d).mp hk
  refine ⟨⟨(ExceptionalConstruction.vertex d).val - 11, by omega⟩, ?_⟩
  apply Fin.ext
  simp only [Fin.val_natAdd]
  omega

variable {V : Type*} [Finite V] {G : SimpleGraph V} [G.LocallyFinite]
  {rotation : Data G} (r : JointReading rotation)
  (tri : Triangular rotation) (cyclic : rotation.IsVertexwiseCyclic)

def reading (d : Fin 86) : G.Dart :=
  ⟨(ExceptionalBoundaryCompletion.vertex r (ExceptionalConstruction.vertex d),
    ExceptionalBoundaryCompletion.vertex r (ExceptionalConstruction.vertex (table.map.edge d))),
    (hom r tri cyclic).map_adj (source_edge d)⟩

theorem edge (d : Fin 86) :
    reading r tri cyclic (table.map.edge d) =
      (DualGraphQuery.map rotation).edge (reading r tri cyclic d) := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · rfl
  · change ExceptionalBoundaryCompletion.vertex r
      (ExceptionalConstruction.vertex (table.map.edge (table.map.edge d))) = _
    rw [source_plain.edge_edge]
    rfl

theorem face {d : Fin 86} (hk : table.map.Kernel ring.reverse d) :
    reading r tri cyclic (table.map.face d) =
      (DualGraphQuery.map rotation).face (reading r tri cyclic d) := by
  obtain ⟨i, hi⟩ := core_label hk
  obtain ⟨p, hp, hf, hn⟩ := source_position i d hi
  obtain ⟨a, b, step⟩ := full_turn r tri cyclic i p
  have first : reading r tri cyclic d =
      (⟨(ExceptionalBoundaryCompletion.vertex r (i.natAdd 11),
        ExceptionalBoundaryCompletion.vertex r (fullSpoke i p)), a⟩ : G.Dart) := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext (congrArg (ExceptionalBoundaryCompletion.vertex r) hi)
      (congrArg (ExceptionalBoundaryCompletion.vertex r) hp)
  have second : reading r tri cyclic (table.map.face d) =
      (⟨(ExceptionalBoundaryCompletion.vertex r (i.natAdd 11),
        ExceptionalBoundaryCompletion.vertex r (fullSpoke i (nextPos i p))), b⟩ : G.Dart) := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext (congrArg (ExceptionalBoundaryCompletion.vertex r) hf)
      (congrArg (ExceptionalBoundaryCompletion.vertex r) hn)
  change _ = rotation.vertexRotation _
  rw [first, second]
  exact step.symm

theorem arity {d : Fin 86} (hk : table.map.Kernel ring.reverse d) :
    (DualGraphQuery.map rotation).arity (reading r tri cyclic d) = table.map.arity d := by
  obtain ⟨i, hi⟩ := core_label hk
  rw [DualGraphQuery.arity_eq_degree rotation cyclic, source_arity i d hi]
  change G.degree (ExceptionalBoundaryCompletion.vertex r (ExceptionalConstruction.vertex d)) = _
  rw [hi, vertex_core, r.core.degree]

/-- A whole core star is read with its cyclic position intact. -/
theorem at_position (i : Fin 8) (d : Fin 86)
    (hi : ExceptionalConstruction.vertex d = i.natAdd 11)
    (p : Fin (coreDegree i))
    (hp : ExceptionalConstruction.vertex (table.map.edge d) = fullSpoke i p) :
    reading r tri cyclic d = around r i p.val := by
  apply SimpleGraph.Dart.ext
  apply Prod.ext
  · change ExceptionalBoundaryCompletion.vertex r (ExceptionalConstruction.vertex d) = _
    rw [hi, vertex_core, around_fst]
  · change ExceptionalBoundaryCompletion.vertex r
      (ExceptionalConstruction.vertex (table.map.edge d)) = _
    rw [hp, row_agrees r tri cyclic]

/-- No core dart collision survives core vertex injectivity and the full
star-position law. No ring-vertex injectivity is required. -/
theorem kernel_injective (injective : Function.Injective r.core.map) :
    Set.InjOn (reading r tri cyclic) {d | table.map.Kernel ring.reverse d} := by
  intro d hk e he eq
  obtain ⟨i, hi⟩ := core_label hk
  obtain ⟨j, hj⟩ := core_label he
  have ij : i = j := by
    apply injective
    have h := congrArg (fun z : G.Dart => z.fst) eq
    change ExceptionalBoundaryCompletion.vertex r (ExceptionalConstruction.vertex d) =
      ExceptionalBoundaryCompletion.vertex r (ExceptionalConstruction.vertex e) at h
    simpa only [hi, hj, vertex_core] using h
  subst j
  obtain ⟨p, hp, _, _⟩ := source_position i d hi
  obtain ⟨q, hq, _, _⟩ := source_position i e hj
  have pq : p = q := by
    apply around_injective r tri cyclic i
    exact congrArg (fun z : G.Dart => z.snd)
      ((at_position r tri cyclic i d hi p hp).symm.trans
        (eq.trans (at_position r tri cyclic i e hj q hq)))
  apply endpoints_injective
  exact Prod.ext (hi.trans hj.symm) (hp.trans (pq ▸ hq.symm))

/-- The core cannot acquire an unaccounted-for reversed dart. A boundary
image lying on the core would be the only remaining way for this to happen. -/
theorem faithful (injective : Function.Injective r.core.map)
    (outside : ∀ (p : Fin 11) (i : Fin 8),
      ExceptionalBoundaryCompletion.vertex r (p.castAdd 8) ≠ r.core.map i) :
    FaithfulKernel table.map (DualGraphQuery.map rotation) ring.reverse (reading r tri cyclic) := by
  refine ⟨kernel_injective r tri cyclic injective, ?_⟩
  intro d e hd he eq
  have heq : reading r tri cyclic (table.map.edge d) = reading r tri cyclic e :=
    (edge r tri cyclic d).trans eq
  have hk : table.map.Kernel ring.reverse (table.map.edge d) := by
    rw [kernel_iff]
    by_contra h
    have bound : (ExceptionalConstruction.vertex (table.map.edge d)).val < 11 := by omega
    let p : Fin 11 := ⟨(ExceptionalConstruction.vertex (table.map.edge d)).val, bound⟩
    have ep : ExceptionalConstruction.vertex (table.map.edge d) = p.castAdd 8 := by
      apply Fin.ext; rfl
    obtain ⟨i, hi⟩ := core_label he
    apply outside p i
    have h := congrArg (fun z : G.Dart => z.fst) heq
    change ExceptionalBoundaryCompletion.vertex r
        (ExceptionalConstruction.vertex (table.map.edge d)) =
      ExceptionalBoundaryCompletion.vertex r (ExceptionalConstruction.vertex e) at h
    simpa only [ep, hi, vertex_core] using h
  exact kernel_injective r tri cyclic injective hk he heq

noncomputable section

variable {W : Type*} [Fintype W] [DecidableEq W]
  {H : SimpleGraph W} [DecidableRel H.Adj]
  (original : Data H)
  (minimal : GoertzelV24TwoEdgeCutMinimality.GraphBackedVertexMinimalTaitCounterexample original)
  (s : JointReading (MinimalExceptionalEmbedding.rotation original minimal))

local instance : (MinimalExceptionalEmbedding.graph original minimal).LocallyFinite :=
  fun _ => Fintype.ofFinite _

/-- The actual minimal dual supplies both local faithfulness fields from
the retained joint occurrence and its proved induced core. -/
theorem actual_faithful :
    FaithfulKernel table.map
      (DualGraphQuery.map (MinimalExceptionalEmbedding.rotation original minimal)) ring.reverse
      (reading s (MinimalExceptionalEmbedding.triangular original minimal)
        (MinimalExceptionalEmbedding.cyclic original minimal)) := by
  classical
  apply faithful s _ _ (MinimalExceptionalEmbedding.joint_injective original minimal s)
  exact ring_outside_core s (MinimalExceptionalEmbedding.triangular original minimal)
    (MinimalExceptionalEmbedding.cyclic original minimal)
    (fun i j => (ExceptionalCoreInduced.joint_induced original minimal s i j).mp)

end
end FourColor.ExceptionalDartReading
