import Mettapedia.GraphTheory.FourColor.PlanarBoundaryOrderedEmbedding
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem

namespace Mettapedia.GraphTheory.FourColor

variable {V : Type*} [DecidableEq V]
variable {G : SimpleGraph V}

/-- A successor-cycle boundary source strengthened with the exact global data
needed to realize a `SimpleGraph.Dart` rotation system.

The existing `PlanarBoundaryDartSuccessorCycleEmbeddingData` is intentionally
face-local: each face has a local successor function constrained only on that
face's dart list.  A rotation system needs one global permutation on all darts.
This package records that extra global successor, its endpoint condition, an
outer dart, and its agreement with every listed local face successor. -/
structure PlanarBoundaryGlobalFaceSuccessorEmbeddingData
    (emb : PlaneEmbeddingWithBoundary G)
    extends PlanarBoundaryDartSuccessorCycleEmbeddingData emb where
  /-- The global face successor on all oriented darts. -/
  faceSuccessor : Equiv.Perm G.Dart
  /-- Face successors end where the current dart points, so they start at the
  terminal vertex of the current dart. -/
  faceSuccessor_fst : ∀ d : G.Dart, (faceSuccessor d).fst = d.snd
  /-- The distinguished outer face whose dart supplies the rotation-system
  outer dart. -/
  outerFace : {f // f ∈ emb.faces}
  /-- The distinguished outer dart. -/
  outerDart : G.Dart
  /-- The outer dart is really listed on the chosen outer face. -/
  outerDart_mem :
    outerDart ∈ (faceBoundaryDartSuccessorCycle outerFace).darts
  /-- The global successor agrees with the local face successor on every dart
  listed by every face.  This is the exact coverage/compatibility obligation
  missing from the face-local successor-cycle source. -/
  faceSuccessor_agrees :
    ∀ (f : {f // f ∈ emb.faces}) (d : G.Dart),
      d ∈ (faceBoundaryDartSuccessorCycle f).darts →
        faceSuccessor d = (faceBoundaryDartSuccessorCycle f).successor d

/-- Function/predecessor version of
`PlanarBoundaryGlobalFaceSuccessorEmbeddingData`.  This is the practical
constructor surface for concrete finite examples: provide explicit global
successor and predecessor functions, prove the inverse laws, and prove
agreement with the listed face-local successors. -/
structure PlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData
    (emb : PlaneEmbeddingWithBoundary G)
    extends PlanarBoundaryDartSuccessorCycleEmbeddingData emb where
  faceSuccessor : G.Dart → G.Dart
  facePredecessor : G.Dart → G.Dart
  left_inv : Function.LeftInverse facePredecessor faceSuccessor
  right_inv : Function.RightInverse facePredecessor faceSuccessor
  faceSuccessor_fst : ∀ d : G.Dart, (faceSuccessor d).fst = d.snd
  outerFace : {f // f ∈ emb.faces}
  outerDart : G.Dart
  outerDart_mem :
    outerDart ∈ (faceBoundaryDartSuccessorCycle outerFace).darts
  faceSuccessor_agrees :
    ∀ (f : {f // f ∈ emb.faces}) (d : G.Dart),
      d ∈ (faceBoundaryDartSuccessorCycle f).darts →
        faceSuccessor d = (faceBoundaryDartSuccessorCycle f).successor d

namespace PlanarBoundaryGlobalFaceSuccessorEmbeddingData

variable {emb : PlaneEmbeddingWithBoundary G}
variable (data : PlanarBoundaryGlobalFaceSuccessorEmbeddingData (G := G) emb)

/-- Forget the global face-successor data and retain the existing face-local
successor-cycle boundary source. -/
def toPlanarBoundaryDartSuccessorCycleEmbeddingData :
    PlanarBoundaryDartSuccessorCycleEmbeddingData emb where
  faceBoundaryDartSuccessorCycle := data.faceBoundaryDartSuccessorCycle

/-- The global face-successor package required by the SimpleGraph dart
rotation-system bridge. -/
def toFaceSuccessorData : SimpleGraphDartRotation.FaceSuccessorData G where
  faceSuccessor := data.faceSuccessor
  faceSuccessor_fst := data.faceSuccessor_fst
  outer := data.outerDart

@[simp]
theorem toFaceSuccessorData_faceSuccessor (d : G.Dart) :
    data.toFaceSuccessorData.faceSuccessor d = data.faceSuccessor d :=
  rfl

@[simp]
theorem toFaceSuccessorData_outer :
    data.toFaceSuccessorData.outer = data.outerDart :=
  rfl

theorem faceSuccessor_eq_local_successor
    (f : {f // f ∈ emb.faces}) {d : G.Dart}
    (hd : d ∈ (data.faceBoundaryDartSuccessorCycle f).darts) :
    data.faceSuccessor d =
      (data.faceBoundaryDartSuccessorCycle f).successor d :=
  data.faceSuccessor_agrees f d hd

variable [Fintype V] [DecidableRel G.Adj]

/-- The bare rotation system determined by globally compatible boundary dart
successors.  This is not yet `RotationSystem.PlanarGeometry`: planarity fields
remain separate obligations. -/
noncomputable def toRotationSystem : RotationSystem V G.edgeSet :=
  data.toFaceSuccessorData.toRotationSystem

@[simp]
theorem toRotationSystem_phi (d : G.Dart) :
    data.toRotationSystem.phi d = data.faceSuccessor d := by
  exact SimpleGraphDartRotation.FaceSuccessorData.toRotationSystem_phi
    (G := G) data.toFaceSuccessorData d

end PlanarBoundaryGlobalFaceSuccessorEmbeddingData

namespace PlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData

variable {emb : PlaneEmbeddingWithBoundary G}
variable (data :
  PlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData (G := G) emb)

/-- Forget explicit global successor/predecessor data and retain the existing
face-local successor-cycle boundary source. -/
def toPlanarBoundaryDartSuccessorCycleEmbeddingData :
    PlanarBoundaryDartSuccessorCycleEmbeddingData emb where
  faceBoundaryDartSuccessorCycle := data.faceBoundaryDartSuccessorCycle

/-- The graph-level function/predecessor face-successor package. -/
def toFaceSuccessorFunctionData :
    SimpleGraphDartRotation.FaceSuccessorFunctionData G where
  faceSuccessor := data.faceSuccessor
  facePredecessor := data.facePredecessor
  left_inv := data.left_inv
  right_inv := data.right_inv
  faceSuccessor_fst := data.faceSuccessor_fst
  outer := data.outerDart

@[simp]
theorem toFaceSuccessorFunctionData_faceSuccessor (d : G.Dart) :
    data.toFaceSuccessorFunctionData.faceSuccessor d = data.faceSuccessor d :=
  rfl

/-- Certificate that the listed face-local successor cycles cover every
oriented dart.  The global successor package already stores compatibility
between local cycles and the global function; this extra certificate records
the coverage hypothesis separately, so later proofs do not have to pretend it
follows from face-local incidence alone. -/
structure CoversAllDarts : Prop where
  dart_cover :
    ∀ d : G.Dart, ∃ f : {f // f ∈ emb.faces},
      d ∈ (data.faceBoundaryDartSuccessorCycle f).darts

/-- Certificate that the listed face-local successor cycles cover every dart
and assign each dart to at most one face. -/
structure CoversAllDartsDisjoint : Prop where
  dart_cover :
    ∀ d : G.Dart, ∃ f : {f // f ∈ emb.faces},
      d ∈ (data.faceBoundaryDartSuccessorCycle f).darts
  dart_unique :
    ∀ (f g : {f // f ∈ emb.faces}) (d : G.Dart),
      d ∈ (data.faceBoundaryDartSuccessorCycle f).darts →
      d ∈ (data.faceBoundaryDartSuccessorCycle g).darts →
        f = g

/-- Forget disjointness and retain only coverage. -/
def CoversAllDartsDisjoint.toCoversAllDarts
    (hcover : data.CoversAllDartsDisjoint) : data.CoversAllDarts where
  dart_cover := hcover.dart_cover

/-- If the face-local cycles cover all darts, then every dart has a local face
cycle whose successor agrees with the global successor. -/
theorem exists_local_successor_eq_of_covers
    (hcover : data.CoversAllDarts) (d : G.Dart) :
    ∃ f : {f // f ∈ emb.faces},
      d ∈ (data.faceBoundaryDartSuccessorCycle f).darts ∧
        data.faceSuccessor d =
          (data.faceBoundaryDartSuccessorCycle f).successor d := by
  rcases hcover.dart_cover d with ⟨f, hd⟩
  exact ⟨f, hd, data.faceSuccessor_agrees f d hd⟩

/-- Under disjoint coverage, a dart cannot be assigned to two different
face-local cycles. -/
theorem face_eq_of_mem_of_covers_disjoint
    (hcover : data.CoversAllDartsDisjoint)
    {f g : {f // f ∈ emb.faces}} {d : G.Dart}
    (hf : d ∈ (data.faceBoundaryDartSuccessorCycle f).darts)
    (hg : d ∈ (data.faceBoundaryDartSuccessorCycle g).darts) :
    f = g :=
  hcover.dart_unique f g d hf hg

/-- Promote explicit successor/predecessor boundary data to the permutation
version. -/
def toPlanarBoundaryGlobalFaceSuccessorEmbeddingData :
    PlanarBoundaryGlobalFaceSuccessorEmbeddingData emb where
  faceBoundaryDartSuccessorCycle := data.faceBoundaryDartSuccessorCycle
  faceSuccessor := data.toFaceSuccessorFunctionData.toFaceSuccessorData.faceSuccessor
  faceSuccessor_fst := data.faceSuccessor_fst
  outerFace := data.outerFace
  outerDart := data.outerDart
  outerDart_mem := data.outerDart_mem
  faceSuccessor_agrees := by
    intro f d hd
    exact data.faceSuccessor_agrees f d hd

variable [Fintype V] [DecidableRel G.Adj]

/-- The bare rotation system determined by explicit globally compatible
boundary successor/predecessor functions. -/
noncomputable def toRotationSystem : RotationSystem V G.edgeSet :=
  data.toPlanarBoundaryGlobalFaceSuccessorEmbeddingData.toRotationSystem

@[simp]
theorem toRotationSystem_phi (d : G.Dart) :
    data.toRotationSystem.phi d = data.faceSuccessor d := by
  exact
    PlanarBoundaryGlobalFaceSuccessorEmbeddingData.toRotationSystem_phi
      (G := G) data.toPlanarBoundaryGlobalFaceSuccessorEmbeddingData d

end PlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData

/-- Graph-level existence form of globally compatible face-successor boundary
data. -/
def AdmitsPlanarBoundaryGlobalFaceSuccessorEmbeddingData (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryGlobalFaceSuccessorEmbeddingData emb)

/-- Graph-level existence form of explicit function/predecessor global
face-successor boundary data. -/
def AdmitsPlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData
    (G : SimpleGraph V) : Prop :=
  ∃ emb : PlaneEmbeddingWithBoundary G,
    Nonempty (PlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData emb)

/-- Explicit function/predecessor global boundary data promotes to the
permutation-based global successor package. -/
theorem
    admitsPlanarBoundaryGlobalFaceSuccessorEmbeddingData_of_admitsPlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData G) :
    AdmitsPlanarBoundaryGlobalFaceSuccessorEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryGlobalFaceSuccessorEmbeddingData⟩⟩

/-- A globally compatible face-successor source forgets to the existing
face-local successor-cycle source. -/
theorem
    admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_of_admitsPlanarBoundaryGlobalFaceSuccessorEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryGlobalFaceSuccessorEmbeddingData G) :
    AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryDartSuccessorCycleEmbeddingData⟩⟩

/-- Explicit function/predecessor global boundary data forgets directly to the
existing face-local successor-cycle source. -/
theorem
    admitsPlanarBoundaryDartSuccessorCycleEmbeddingData_of_admitsPlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData
    {G : SimpleGraph V}
    (hG : AdmitsPlanarBoundaryGlobalFaceSuccessorFunctionEmbeddingData G) :
    AdmitsPlanarBoundaryDartSuccessorCycleEmbeddingData G := by
  rcases hG with ⟨emb, ⟨data⟩⟩
  exact ⟨emb, ⟨data.toPlanarBoundaryDartSuccessorCycleEmbeddingData⟩⟩

end Mettapedia.GraphTheory.FourColor
