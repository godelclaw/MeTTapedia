import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceWalk
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCyclicOrder
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceTwoSided

/-!
# Ordered arcs of an orbit-face walk

The face orbit of a rotation system is cyclic, but the sector walls in the
closed-web argument need an *open* facial arc between two specified darts.
This module cuts the canonical cyclic dart enumeration immediately before a
target dart.  The resulting graph walk starts at the root dart's first vertex
and ends at the target dart's first vertex.

No two-sidedness is required.  This matters at the annular interface: a stub
edge is traversed twice by its hole face, so that face need not have a simple
edge boundary even though its dart orbit remains a perfectly good walk.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24OrbitFaceArcWalk

open GoertzelV24HexFaceRungType
open GoertzelV24OrbitFaceCyclicOrder
open GoertzelV24OrbitFaceTwoSided
open GoertzelV24OrbitFaceWalk
open SimpleGraph
open SimpleGraphDartRotation

variable {V : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]

noncomputable section

/-- The unique cyclic position of `target`, measured forward from `root`. -/
def faceArcPosition (graphData : Data G) (root target : G.Dart)
    (htarget : target ∈ graphData.toRotationSystem.faceOrbit root) :
    Fin (graphData.toRotationSystem.faceOrbit root).card :=
  (faceOrbitDartEquiv graphData.toRotationSystem root).symm
    ⟨target, htarget⟩

/-- The target really is the dart at its relative cyclic position. -/
theorem faceCycleDart_faceArcPosition
    (graphData : Data G) (root target : G.Dart)
    (htarget : target ∈ graphData.toRotationSystem.faceOrbit root) :
    faceCycleDart graphData.toRotationSystem root
        (faceArcPosition graphData root target htarget) = target := by
  have happly := Equiv.apply_symm_apply
    (faceOrbitDartEquiv graphData.toRotationSystem root)
    (⟨target, htarget⟩ :
      {dart // dart ∈ graphData.toRotationSystem.faceOrbit root})
  exact congrArg Subtype.val happly

/-- The ordered facial darts strictly before `target`, beginning at `root`.
When `root = target`, this is the empty list. -/
def faceArcDarts (graphData : Data G) (root target : G.Dart)
    (htarget : target ∈ graphData.toRotationSystem.faceOrbit root) :
    List G.Dart :=
  let position := faceArcPosition graphData root target htarget
  List.ofFn fun index : Fin position.val =>
    faceCycleDart graphData.toRotationSystem root
      ⟨index.val, lt_trans index.isLt position.isLt⟩

@[simp] theorem length_faceArcDarts
    (graphData : Data G) (root target : G.Dart)
    (htarget : target ∈ graphData.toRotationSystem.faceOrbit root) :
    (faceArcDarts graphData root target htarget).length =
      (faceArcPosition graphData root target htarget).val := by
  simp [faceArcDarts]

/-- Every retained dart belongs to the same face orbit as the root. -/
theorem mem_faceOrbit_of_mem_faceArcDarts
    (graphData : Data G) (root target dart : G.Dart)
    (htarget : target ∈ graphData.toRotationSystem.faceOrbit root)
    (hdart : dart ∈ faceArcDarts graphData root target htarget) :
    dart ∈ graphData.toRotationSystem.faceOrbit root := by
  simp only [faceArcDarts, List.mem_ofFn] at hdart
  rcases hdart with ⟨index, rfl⟩
  exact faceCycleDart_mem graphData.toRotationSystem root _

/-- The target is the first omitted dart, hence is not itself retained. -/
theorem target_not_mem_faceArcDarts
    (graphData : Data G) (root target : G.Dart)
    (htarget : target ∈ graphData.toRotationSystem.faceOrbit root) :
    target ∉ faceArcDarts graphData root target htarget := by
  intro hmem
  simp only [faceArcDarts, List.mem_ofFn] at hmem
  rcases hmem with ⟨index, hindex⟩
  have htargetAt := faceCycleDart_faceArcPosition
    graphData root target htarget
  have hpositions := faceCycleDart_injective
    graphData.toRotationSystem root (hindex.trans htargetAt.symm)
  have hvals := congrArg Fin.val hpositions
  exact (Nat.ne_of_lt index.isLt) hvals

/-- A strict facial prefix cannot contain a predecessor of its root. -/
theorem predecessor_not_mem_faceArcDarts
    (graphData : Data G) (root target predecessor : G.Dart)
    (htarget : target ∈ graphData.toRotationSystem.faceOrbit root)
    (hpredecessor : graphData.toRotationSystem.phi predecessor = root) :
    predecessor ∉ faceArcDarts graphData root target htarget := by
  intro hmem
  simp only [faceArcDarts, List.mem_ofFn] at hmem
  rcases hmem with ⟨index, hindex⟩
  have hnextLt : index.val + 1 <
      (graphData.toRotationSystem.faceOrbit root).card :=
    lt_of_le_of_lt (Nat.succ_le_of_lt index.isLt)
      (faceArcPosition graphData root target htarget).isLt
  let next : Fin (graphData.toRotationSystem.faceOrbit root).card :=
    ⟨index.val + 1, hnextLt⟩
  have hnext : faceCycleDart graphData.toRotationSystem root next = root := by
    calc
      faceCycleDart graphData.toRotationSystem root next =
          graphData.toRotationSystem.phi
            (faceCycleDart graphData.toRotationSystem root
              ⟨index.val, lt_trans index.isLt
                (faceArcPosition graphData root target htarget).isLt⟩) := by
        simp only [faceCycleDart, next, pow_succ', Equiv.Perm.coe_mul,
          Function.comp_apply]
      _ = graphData.toRotationSystem.phi predecessor :=
        congrArg graphData.toRotationSystem.phi hindex
      _ = root := hpredecessor
  have hpositive : 0 <
      (graphData.toRotationSystem.faceOrbit root).card :=
    Finset.card_pos.mpr
      ⟨root, graphData.toRotationSystem.mem_faceOrbit_self root⟩
  let zero : Fin (graphData.toRotationSystem.faceOrbit root).card :=
    ⟨0, hpositive⟩
  have hzero : faceCycleDart graphData.toRotationSystem root zero = root := by
    simp [faceCycleDart, zero]
  have hpositions := faceCycleDart_injective
    graphData.toRotationSystem root (hnext.trans hzero.symm)
  have hvals := congrArg Fin.val hpositions
  change index.val + 1 = 0 at hvals
  omega

/-- A retained facial dart keeps its successor in the prefix unless that
successor is exactly the omitted target. -/
theorem phi_mem_faceArcDarts_of_mem_of_ne_target
    (graphData : Data G) (root target dart : G.Dart)
    (htarget : target ∈ graphData.toRotationSystem.faceOrbit root)
    (hdart : dart ∈ faceArcDarts graphData root target htarget)
    (hne : graphData.toRotationSystem.phi dart ≠ target) :
    graphData.toRotationSystem.phi dart ∈
      faceArcDarts graphData root target htarget := by
  simp only [faceArcDarts, List.mem_ofFn] at hdart
  rcases hdart with ⟨index, hindex⟩
  have hstrict : index.val + 1 <
      (faceArcPosition graphData root target htarget).val := by
    have hle := Nat.succ_le_of_lt index.isLt
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      apply hne
      calc
        graphData.toRotationSystem.phi dart =
            graphData.toRotationSystem.phi
              (faceCycleDart graphData.toRotationSystem root
                ⟨index.val, lt_trans index.isLt
                  (faceArcPosition graphData root target htarget).isLt⟩) :=
          congrArg graphData.toRotationSystem.phi hindex.symm
        _ = faceCycleDart graphData.toRotationSystem root
              (faceArcPosition graphData root target htarget) := by
          simp only [faceCycleDart, ← heq, pow_succ',
            Equiv.Perm.coe_mul, Function.comp_apply]
        _ = target := faceCycleDart_faceArcPosition
          graphData root target htarget
  change graphData.toRotationSystem.phi dart ∈
    List.ofFn (fun successor :
        Fin (faceArcPosition graphData root target htarget).val =>
      faceCycleDart graphData.toRotationSystem root
        ⟨successor.val, lt_trans successor.isLt
          (faceArcPosition graphData root target htarget).isLt⟩)
  apply List.mem_ofFn.mpr
  refine ⟨⟨index.val + 1, hstrict⟩, ?_⟩
  calc
    faceCycleDart graphData.toRotationSystem root
        ⟨index.val + 1,
          lt_trans hstrict
            (faceArcPosition graphData root target htarget).isLt⟩ =
      graphData.toRotationSystem.phi
        (faceCycleDart graphData.toRotationSystem root
          ⟨index.val, lt_trans index.isLt
            (faceArcPosition graphData root target htarget).isLt⟩) := by
      simp only [faceCycleDart, pow_succ', Equiv.Perm.coe_mul,
        Function.comp_apply]
    _ = graphData.toRotationSystem.phi dart :=
      congrArg graphData.toRotationSystem.phi hindex

/-- Provided it does not wrap to the root, the target's successor lies after
the cut and is absent from the retained prefix. -/
theorem phi_target_not_mem_faceArcDarts
    (graphData : Data G) (root target : G.Dart)
    (htarget : target ∈ graphData.toRotationSystem.faceOrbit root)
    (hnowrap : graphData.toRotationSystem.phi target ≠ root) :
    graphData.toRotationSystem.phi target ∉
      faceArcDarts graphData root target htarget := by
  let position := faceArcPosition graphData root target htarget
  have hsuccessorLt : position.val + 1 <
      (graphData.toRotationSystem.faceOrbit root).card := by
    have hle := Nat.succ_le_of_lt position.isLt
    rcases Nat.lt_or_eq_of_le hle with hlt | heq
    · exact hlt
    · exfalso
      apply hnowrap
      have htargetAt := faceCycleDart_faceArcPosition
        graphData root target htarget
      have hwrap := (faceOrbit_isCycleOn
        graphData.toRotationSystem root).pow_card_apply
          (graphData.toRotationSystem.mem_faceOrbit_self root)
      calc
        graphData.toRotationSystem.phi target =
            graphData.toRotationSystem.phi
              (faceCycleDart graphData.toRotationSystem root position) := by
          rw [htargetAt]
        _ = (graphData.toRotationSystem.phi ^ (position.val + 1)) root := by
          simp only [faceCycleDart, pow_succ', Equiv.Perm.coe_mul,
            Function.comp_apply]
        _ = (graphData.toRotationSystem.phi ^
              (graphData.toRotationSystem.faceOrbit root).card) root := by
          have heq' : position.val + 1 =
              (graphData.toRotationSystem.faceOrbit root).card := by omega
          rw [heq']
        _ = root := hwrap
  intro hmem
  change graphData.toRotationSystem.phi target ∈
    List.ofFn (fun index : Fin position.val =>
      faceCycleDart graphData.toRotationSystem root
        ⟨index.val, lt_trans index.isLt position.isLt⟩) at hmem
  simp only [List.mem_ofFn] at hmem
  rcases hmem with ⟨index, hindex⟩
  let successor : Fin
      (graphData.toRotationSystem.faceOrbit root).card :=
    ⟨position.val + 1, hsuccessorLt⟩
  have hsuccessor :
      faceCycleDart graphData.toRotationSystem root successor =
        graphData.toRotationSystem.phi target := by
    rw [← faceCycleDart_faceArcPosition graphData root target htarget]
    simp only [faceCycleDart, successor, position, pow_succ',
      Equiv.Perm.coe_mul, Function.comp_apply]
  have hpositions := faceCycleDart_injective
    graphData.toRotationSystem root (hindex.trans hsuccessor.symm)
  have hvals := congrArg Fin.val hpositions
  have := index.isLt
  change index.val = position.val + 1 at hvals
  omega

/-- The retained facial darts form a graph-dart chain. -/
theorem faceArcDarts_isChain
    (graphData : Data G) (root target : G.Dart)
    (htarget : target ∈ graphData.toRotationSystem.faceOrbit root) :
    List.IsChain G.DartAdj
      (faceArcDarts graphData root target htarget) := by
  rw [faceArcDarts, List.isChain_ofFn]
  intro index hnext
  have hsuccessor :
      faceCycleDart graphData.toRotationSystem root
          ⟨index + 1,
            lt_trans hnext
              (faceArcPosition graphData root target htarget).isLt⟩ =
        graphData.toRotationSystem.phi
          (faceCycleDart graphData.toRotationSystem root
            ⟨index, lt_trans (Nat.lt_of_succ_lt hnext)
              (faceArcPosition graphData root target htarget).isLt⟩) := by
    simp only [faceCycleDart, pow_succ', Equiv.Perm.coe_mul,
      Function.comp_apply]
  rw [hsuccessor]
  exact dartAdj_phi graphData _

/-! Under local two-sidedness, the strict facial prefix has no repeated
underlying edge.  This is the prefix form of
`GoertzelV24OrbitFaceWalk.map_edge_faceOrbitDarts_nodup`; it is the exact
graph-side fact needed to upgrade a canonical hole arc from a walk to a
trail, without asserting vertex simplicity or Jordan separation. -/

theorem map_edge_faceArcDarts_nodup
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (root target : G.Dart)
    (htarget : target ∈ graphData.toRotationSystem.faceOrbit root) :
    ((faceArcDarts graphData root target htarget).map
      fun dart => dart.edge).Nodup := by
  rw [faceArcDarts, List.map_ofFn, List.nodup_ofFn]
  intro left right hedge
  let left' : Fin (graphData.toRotationSystem.faceOrbit root).card :=
    ⟨left.val, lt_trans left.isLt
      (faceArcPosition graphData root target htarget).isLt⟩
  let right' : Fin (graphData.toRotationSystem.faceOrbit root).card :=
    ⟨right.val, lt_trans right.isLt
      (faceArcPosition graphData root target htarget).isLt⟩
  have hedge' : faceCycleEdge graphData.toRotationSystem root left' =
      faceCycleEdge graphData.toRotationSystem root right' := by
    apply Subtype.ext
    simpa [left', right', faceCycleEdge] using hedge
  have hpositions : left' = right' :=
    faceCycleEdge_injective graphData.toRotationSystem htwoSided root hedge'
  apply Fin.ext
  simpa [left', right'] using congrArg Fin.val hpositions

/-- Cutting a face orbit immediately before a target dart gives an actual
walk between the two dart roots.  Its length is the target's forward cyclic
position and its darts are exactly the retained facial segment. -/
theorem exists_faceArcWalk
    (graphData : Data G) (root target : G.Dart)
    (htarget : target ∈ graphData.toRotationSystem.faceOrbit root) :
    ∃ arc : G.Walk root.fst target.fst,
      arc.darts = faceArcDarts graphData root target htarget ∧
      arc.length = (faceArcPosition graphData root target htarget).val ∧
      ∀ dart ∈ arc.darts,
        dart ∈ graphData.toRotationSystem.faceOrbit root := by
  let position := faceArcPosition graphData root target htarget
  by_cases hzero : position.val = 0
  · have htargetEq : target = root := by
      have htargetAt := faceCycleDart_faceArcPosition
        graphData root target htarget
      change (graphData.toRotationSystem.phi ^ position.val) root = target at htargetAt
      rw [hzero] at htargetAt
      change root = target at htargetAt
      exact htargetAt.symm
    let arc : G.Walk root.fst target.fst :=
      Walk.nil.copy rfl (congrArg (fun dart : G.Dart => dart.fst) htargetEq.symm)
    refine ⟨arc, ?_, ?_, ?_⟩
    · have hempty : faceArcDarts graphData root target htarget = [] := by
        rw [← List.length_eq_zero_iff]
        rw [length_faceArcDarts]
        exact hzero
      simp [arc, hempty]
    · simp [arc, show (faceArcPosition graphData root target htarget).val = 0
        from hzero]
    · intro dart hdart
      simp [arc] at hdart
  · have hpositive : 0 < position.val := Nat.pos_of_ne_zero hzero
    let darts := faceArcDarts graphData root target htarget
    have hdartsNe : darts ≠ [] := by
      rw [← List.length_pos_iff]
      simpa [darts, position] using hpositive
    have hchain : List.IsChain G.DartAdj darts :=
      faceArcDarts_isChain graphData root target htarget
    have hhead : darts.head hdartsNe = root := by
      obtain ⟨last, hlast⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      simp [darts, faceArcDarts, position, hlast, faceCycleDart]
    have hlastAdj : G.DartAdj (darts.getLast hdartsNe) target := by
      obtain ⟨last, hlast⟩ := Nat.exists_eq_succ_of_ne_zero hzero
      have hlastLt : last <
          (graphData.toRotationSystem.faceOrbit root).card := by
        have := position.isLt
        omega
      have htargetAt := faceCycleDart_faceArcPosition
        graphData root target htarget
      have hlastValue :
          darts.getLast hdartsNe =
            faceCycleDart graphData.toRotationSystem root
              ⟨last, hlastLt⟩ := by
        rw [List.getLast_eq_getElem]
        have hdartsLength : darts.length = last + 1 := by
          simpa [darts, position] using hlast
        simp only [hdartsLength, Nat.add_sub_cancel]
        simp [darts, faceArcDarts]
      rw [hlastValue]
      have hstep :
          graphData.toRotationSystem.phi
              (faceCycleDart graphData.toRotationSystem root
                ⟨last, hlastLt⟩) = target := by
        rw [← htargetAt]
        change graphData.toRotationSystem.phi
            ((graphData.toRotationSystem.phi ^ last) root) =
          (graphData.toRotationSystem.phi ^ position.val) root
        rw [hlast]
        simp only [pow_succ', Equiv.Perm.coe_mul, Function.comp_apply]
      change
        (faceCycleDart graphData.toRotationSystem root
          ⟨last, hlastLt⟩).snd = target.fst
      calc
        _ = (graphData.toRotationSystem.phi
              (faceCycleDart graphData.toRotationSystem root
                ⟨last, hlastLt⟩)).fst :=
            dartAdj_phi graphData _
        _ = target.fst := congrArg (fun dart : G.Dart => dart.fst) hstep
    let raw : G.Walk (darts.head hdartsNe).fst
        (darts.getLast hdartsNe).snd :=
      Walk.ofDarts darts hdartsNe hchain
    let arc : G.Walk root.fst target.fst :=
      raw.copy (congrArg (fun dart : G.Dart => dart.fst) hhead)
        hlastAdj
    have hdarts : arc.darts = darts := by simp [arc, raw]
    refine ⟨arc, hdarts, ?_, ?_⟩
    · rw [← arc.length_darts, hdarts]
      exact length_faceArcDarts graphData root target htarget
    · intro dart hdart
      rw [hdarts] at hdart
      exact mem_faceOrbit_of_mem_faceArcDarts
        graphData root target dart htarget hdart

/-! A two-sided face turns the canonical arc into a trail.  The endpoint and
face-orbit facts are retained from `exists_faceArcWalk`; the only new input
is the edge-injectivity calculation above. -/

theorem exists_faceArcWalk_isTrail
    (graphData : Data G)
    (htwoSided : OrbitFacesTwoSided graphData.toRotationSystem)
    (root target : G.Dart)
    (htarget : target ∈ graphData.toRotationSystem.faceOrbit root) :
    ∃ arc : G.Walk root.fst target.fst,
      arc.IsTrail ∧
      arc.darts = faceArcDarts graphData root target htarget ∧
      arc.length = (faceArcPosition graphData root target htarget).val ∧
      ∀ dart ∈ arc.darts,
        dart ∈ graphData.toRotationSystem.faceOrbit root := by
  rcases exists_faceArcWalk graphData root target htarget with
    ⟨arc, hdarts, hlength, hface⟩
  refine ⟨arc, ?_, hdarts, hlength, hface⟩
  refine ⟨?_⟩
  rw [SimpleGraph.Walk.edges, hdarts]
  exact map_edge_faceArcDarts_nodup graphData htwoSided root target htarget

end

end GoertzelV24OrbitFaceArcWalk

end Mettapedia.GraphTheory.FourColor
