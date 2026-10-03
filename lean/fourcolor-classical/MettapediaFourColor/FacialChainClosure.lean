import MettapediaFourColor.FacialStarCompletion

/-! Completing a chain of actual facial corners using the ambient degree.
The closing law retains the same vertices throughout and does not assume
that the supplied labels are globally distinct. -/

namespace FourColor.FacialChainClosure

open Mettapedia.GraphTheory.FourColor SimpleGraphDartRotation
open ExceptionalCoreOrientation ExceptionalOverlap

variable {V : Type*} {G : SimpleGraph V} [G.LocallyFinite]
  (rotation : Data G)

/-- Attach the next actual facial corner to a directed edge. -/
def extend (a b : V) (edge : G.Adj a b) : V :=
  (rotation.vertexRotation ⟨(a,b),edge⟩).snd

omit [G.LocallyFinite] in
theorem extend_corner (a b : V) (edge : G.Adj a b) :
    Corner rotation a b (extend rotation a b edge) := by
  let d : G.Dart := ⟨(a,b),edge⟩
  have adj : G.Adj a (extend rotation a b edge) := by
    unfold extend
    have h := (rotation.vertexRotation (⟨(a,b),edge⟩ : G.Dart)).adj
    rw [rotation.vertexRotation_fst] at h
    exact h
  refine ⟨edge,adj,?_⟩
  apply SimpleGraph.Dart.ext
  exact Prod.ext (rotation.vertexRotation_fst d) rfl

variable [Finite V]

/-- A chain with one corner missing closes at the actual degree.
All corners are read in the same cyclic orientation. -/
theorem close (cyclic : rotation.IsVertexwiseCyclic) {n : ℕ} (positive : 0 < n)
    (v : V) (row : Fin (n + 1) → V)
    (steps : ∀ i : Fin n, Corner rotation v
      (row ⟨i.val,Nat.lt_succ_of_lt i.isLt⟩)
      (row ⟨i.val+1,Nat.succ_lt_succ i.isLt⟩))
    (degree : G.degree v = n+1) :
    Corner rotation v (row ⟨n,Nat.lt_succ_self n⟩) (row 0) := by
  let base : G.Dart := ⟨(v,row 0),(steps ⟨0,positive⟩).choose⟩
  have follows (k : ℕ) (bound : k < n+1) :
      ((rotation.vertexRotation ^ k) base).snd = row ⟨k,bound⟩ := by
    induction k with
    | zero => rfl
    | succ k ih =>
        have h := steps ⟨k,by omega⟩
        have eq : (rotation.vertexRotation ^ k) base =
            (⟨(v,row ⟨k,by omega⟩),h.choose⟩ : G.Dart) := by
          apply SimpleGraph.Dart.ext
          exact Prod.ext (FacialStarCompletion.pow_fst rotation base k) (ih (by omega))
        rw [pow_succ',Equiv.Perm.mul_apply,eq]
        exact congrArg (fun d : G.Dart => d.snd) h.choose_spec.choose_spec
  let last : G.Dart := (rotation.vertexRotation ^ n) base
  have first : last.fst = v := FacialStarCompletion.pow_fst rotation base n
  have final : last.snd = row ⟨n,Nat.lt_succ_self n⟩ := follows n (Nat.lt_succ_self n)
  have adj : G.Adj v (row ⟨n,Nat.lt_succ_self n⟩) := by
    rw [← first,← final]
    exact last.adj
  refine ⟨adj,base.adj,?_⟩
  have eq : (⟨(v,row ⟨n,Nat.lt_succ_self n⟩),adj⟩ : G.Dart) = last := by
    apply SimpleGraph.Dart.ext
    exact Prod.ext first.symm final.symm
  rw [eq]
  change rotation.vertexRotation ((rotation.vertexRotation ^ n) base) = base
  rw [← Equiv.Perm.mul_apply,← pow_succ']
  have period := FacialStarCompletion.pow_degree rotation cyclic base
  change (rotation.vertexRotation ^ G.degree v) base = base at period
  rwa [degree] at period

end FourColor.FacialChainClosure
