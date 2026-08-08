import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceWalk
import Mettapedia.GraphTheory.FourColor.GoertzelV24OrbitFaceCyclicOrder

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

end

end GoertzelV24OrbitFaceArcWalk

end Mettapedia.GraphTheory.FourColor
