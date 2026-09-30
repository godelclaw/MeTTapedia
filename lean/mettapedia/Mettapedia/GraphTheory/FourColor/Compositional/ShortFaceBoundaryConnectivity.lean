import Mettapedia.GraphTheory.FourColor.Compositional.ShortFacePortExclusion
import Mettapedia.GraphTheory.FourColor.SimpleGraphRotationSystem
import Mettapedia.GraphTheory.FourColor.RootedCutSaturation

/-!
# Short seam faces connect the complementary shore

Consecutive outside endpoints of a cyclic boundary are joined by one or
two actual exterior edges. Completeness of the boundary and connectedness
of the ambient graph then force the entire exterior to be connected.
No colouring or cut-size assumption is used.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional.ShortFaceBoundaryConnectivity

open Equiv Equiv.Perm Fin.NatCast SimpleGraph
open GoertzelV24CyclicThreeCutConnectedSides

noncomputable section
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj]
  (rotation : SimpleGraphDartRotation.Data G) (inside : V → Prop)
  {n : ℕ} [NeZero n] (port : Fin n → G.Dart)

local instance edgeFintype : Fintype G.edgeSet := SimpleGraph.fintypeEdgeSet G
local instance edgeDecidableEq : DecidableEq G.edgeSet := Subtype.instDecidableEq

variable (houtside : ∀ i, ¬ inside (port i).snd)
  (complete : ∀ d : G.Dart, inside d.fst → ¬ inside d.snd → ∃ i, port i = d)
  (forward : ∀ i, inside (rotation.vertexRotation (port i)).snd)
  (arc : ∀ i, (rotation.toRotationSystem.phi ^ 2)
    (rotation.vertexRotation (port i)) = port (i-1))
  (short : ∀ i, (rotation.toRotationSystem.faceOrbit (port i)).card = 5 ∨
    (rotation.toRotationSystem.faceOrbit (port i)).card = 6)

/-- The outside endpoint retains its actual ambient vertex. -/
def endpoint (i : Fin n) : {v : V // ¬ inside v} := ⟨(port i).snd, houtside i⟩

private theorem next_fst (d : G.Dart) :
    (rotation.toRotationSystem.phi d).fst = d.snd :=
  rotation.vertexRotation_fst d.symm

private theorem next_adj (d : G.Dart) :
    G.Adj d.fst (rotation.toRotationSystem.phi d).fst := by
  rw [next_fst]
  exact d.adj

include complete forward arc short in
/-- The complementary face arc stays outside: one edge for a pentagon,
two for a hexagon. A return at the hexagonal intermediate vertex would
make its next vertex interior, contradicting the final outside endpoint. -/
theorem consecutive_reachable (i : Fin n) :
    (G.induce (fun v => ¬ inside v)).Reachable
      (endpoint inside port houtside (i-1)) (endpoint inside port houtside i) := by
  let RS := rotation.toRotationSystem
  let a := RS.phi (port (i-1))
  let b := RS.phi a
  let c := RS.phi b
  have ha : a.fst = (port (i-1)).snd := next_fst rotation _
  have hb : b.fst = a.snd := next_fst rotation _
  have hc : c.fst = b.snd := next_fst rotation _
  have haOutside : ¬ inside a.fst := by rw [ha]; exact houtside (i-1)
  rcases ShortFacePortExclusion.exterior_arc RS port arc short i with hp | hh
  · have he : b = (port i).symm := by
      change b = RS.alpha (port i) at hp
      exact hp
    have hend : b.fst = (port i).snd := by rw [he]; rfl
    have hadj : (G.induce (fun v => ¬ inside v)).Adj
        (endpoint inside port houtside (i-1)) (endpoint inside port houtside i) := by
      change G.Adj (port (i-1)).snd (port i).snd
      rw [← ha, ← hend]
      exact next_adj rotation a
    exact hadj.reachable
  · have he : c = (port i).symm := by
      change c = RS.alpha (port i) at hh
      exact hh
    have hend : c.fst = (port i).snd := by rw [he]; rfl
    have hcOutside : ¬ inside c.fst := by rw [hend]; exact houtside i
    have hbOutside : ¬ inside b.fst := by
      intro hbin
      obtain ⟨j,hj⟩ := complete a.symm (by
        change inside a.snd
        rw [← hb]
        exact hbin) haOutside
      have hbRot : b = rotation.vertexRotation (port j) := by
        change rotation.vertexRotation a.symm = _
        rw [hj]
      apply hcOutside
      rw [hc, hbRot]
      exact forward j
    have hab : (G.induce (fun v => ¬ inside v)).Adj
        (endpoint inside port houtside (i-1)) ⟨b.fst, hbOutside⟩ := by
      change G.Adj (port (i-1)).snd b.fst
      rw [← ha]
      exact next_adj rotation a
    have hbc : (G.induce (fun v => ¬ inside v)).Adj
        ⟨b.fst, hbOutside⟩ (endpoint inside port houtside i) := by
      change G.Adj b.fst (port i).snd
      rw [← hend]
      exact next_adj rotation b
    exact hab.reachable.trans hbc.reachable

include complete forward arc short in
/-- All boundary endpoints lie in the same actual exterior component. -/
theorem endpoints_reachable (i : Fin n) :
    (G.induce (fun v => ¬ inside v)).Reachable
      (endpoint inside port houtside 0) (endpoint inside port houtside i) := by
  have hn : ∀ k : ℕ, (G.induce (fun v => ¬ inside v)).Reachable
      (endpoint inside port houtside 0) (endpoint inside port houtside (k : Fin n)) := by
    intro k
    induction k with
    | zero => exact .rfl
    | succ k ih =>
      have hs := consecutive_reachable rotation inside port houtside complete forward arc short
        ((k : Fin n)+1)
      rw [add_sub_cancel_right] at hs
      simpa only [Nat.cast_add, Nat.cast_one] using ih.trans hs
  simpa only [Fin.cast_val_eq_self] using hn i.val

include houtside complete forward arc short in
/-- Connected ambient geometry and the complete cyclic boundary exclude
an exterior component with no path to the boundary endpoints. -/
theorem exterior_connected (hconnected : G.Connected) :
    (G.induce (fun v => ¬ inside v)).Connected := by
  let root := endpoint inside port houtside 0
  have hall : ∀ v : {v : V // ¬ inside v},
      (G.induce (fun w => ¬ inside w)).Reachable root v := by
    intro v
    by_contra hnot
    let other := inducedReachableSide G (fun w => ¬ inside w) v.1 v.2
    have hv : other v.1 := inducedReachableSide_root _ _ _
    have hroot : ¬ other root.1 := by
      rintro ⟨_,hr⟩
      exact hnot hr.symm
    rcases hconnected v.1 root.1 with ⟨walk⟩
    rcases exists_edgeCrossesVertexSide_of_walk_endpoint_sides other walk hv hroot with
      ⟨edge,_,inner,outer,hinnerEdge,houterEdge,hinnerOther,houterOther⟩
    have hne : inner ≠ outer := by
      intro he
      exact houterOther (he ▸ hinnerOther)
    have hedge : (edge : Sym2 V) = s(inner,outer) :=
      sym2_eq_mk_of_mem_of_mem_of_ne hinnerEdge houterEdge hne
    have hadj : G.Adj inner outer :=
      (SimpleGraph.mem_edgeSet G).mp (by simpa [hedge] using edge.2)
    have hin : ¬ inside inner := hinnerOther.choose
    have hout : inside outer := by
      by_contra hout
      have hstep : (G.induce (fun w => ¬ inside w)).Adj ⟨inner,hin⟩ ⟨outer,hout⟩ := hadj
      exact houterOther ⟨hout,hinnerOther.choose_spec.trans hstep.reachable⟩
    let d : G.Dart := ⟨(outer,inner),hadj.symm⟩
    obtain ⟨i,hi⟩ := complete d hout hin
    have hp := endpoints_reachable rotation inside port houtside complete forward arc short i
    have he : endpoint inside port houtside i = (⟨inner,hin⟩ : {w // ¬ inside w}) := by
      apply Subtype.ext
      exact congrArg (fun d : G.Dart => d.snd) hi
    rw [he] at hp
    exact hnot (hp.trans hinnerOther.choose_spec.symm)
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  exact ⟨root,hall⟩

end
end Mettapedia.GraphTheory.FourColor.Compositional.ShortFaceBoundaryConnectivity
