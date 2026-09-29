import MettapediaFourColor.ExecutableConfiguration
import FourColor.CfContract

/-!
# Retaining the selected edges of a configuration

The executable construction retains the kernel-edge transversal in the same
order as the reference decoder. Equality includes both the pointed hypermap
and its marked darts, so subsequent contract selection preserves edge identity.
-/

namespace FourColor.ExecutableConfiguration

/-- The construction injection, with all newly introduced darts kept distinct. -/
def Step.inject (s : Step) (M : PointedMap) : M.Dart → (s.apply M).Dart :=
  match s with
  | .rotate _ => id
  | .add => EcpDart.icp
  | .fork => EcpDart.icp ∘ EcpDart.icp
  | .join => EcpDart.icp ∘ EcpDart.icp ∘ EcpDart.icp

/-- The reference kernel-edge order, computed with the executable maps. -/
def kernelEdges : (p : List Step) → List (evaluate p).Dart
  | [] => []
  | .rotate _ :: p => kernelEdges p
  | .add :: _ => []
  | .fork :: [] => []
  | .fork :: s :: p =>
      ((evaluate (s :: p)).map.node (evaluate (s :: p)).point :: kernelEdges (s :: p)).map
        (Step.inject .fork (evaluate (s :: p)))
  | .join :: p =>
      (evaluate (.join :: p)).map.face (evaluate (.join :: p)).point ::
        ((evaluate p).map.node (evaluate p).point :: (evaluate p).point :: kernelEdges p).map
          (Step.inject .join (evaluate p))

/-- Package the map with the darts whose interpretation depends on that map. -/
def marked (p : List Step) : Σ M : PointedMap, List M.Dart :=
  ⟨evaluate p, kernelEdges p⟩

private def markedStep (s : Step) (nonempty : Bool)
    (state : Σ M : PointedMap, List M.Dart) : Σ M : PointedMap, List M.Dart :=
  let M := state.1
  let darts := state.2
  ⟨s.apply M, match s with
    | .rotate _ => darts
    | .add => []
    | .fork => if nonempty then
        (M.map.node M.point :: darts).map (Step.inject .fork M) else []
    | .join => (Step.join.apply M).map.face (Step.join.apply M).point ::
        (M.map.node M.point :: M.point :: darts).map (Step.inject .join M)⟩

private theorem marked_cons (s : Step) (p : List Step) :
    marked (s :: p) = markedStep s (!p.isEmpty) (marked p) := by
  cases s <;> cases p <;> rfl

/-- The transversal is equal to the reference one on the actual decoded map. -/
theorem marked_eq (p : List Step) :
    marked p = ⟨cpmap (p.map Step.reference), ctrenum (p.map Step.reference)⟩ := by
  induction p with
  | nil =>
    simp only [marked, evaluate, kernelEdges]
    exact congrArg (fun M : PointedMap => (⟨M, []⟩ : Σ M : PointedMap, List M.Dart)) zero_eq
  | cons s p ih =>
    rw [marked_cons, ih]
    cases s <;> cases p <;>
      simp [markedStep, Step.apply, Step.inject, Step.reference, List.map_cons, List.map_nil,
        cpmap, rotate_eq, add_eq, close_eq, PointedMap.ecpY, PointedMap.ecpH] <;> rfl

theorem kernelEdges_heq (p : List Step) :
    HEq (kernelEdges p) (ctrenum (p.map Step.reference)) :=
  (Sigma.mk.inj_iff.mp (marked_eq p)).2

/-- Kernel edges in the same finite dart coordinates as the graph tables. -/
def numberedKernelEdges (p : List Step) : List (Fin (size p)) :=
  (kernelEdges p).map (index p).symm

end FourColor.ExecutableConfiguration
