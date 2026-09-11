import Mettapedia.GraphTheory.FourColor.BoundedCubicColourTrace
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite

/-!
# Topology checks on bounded incidence traces

Connectivity and deletion of a single edge identifier are computable from the
incidence trace. Their correspondence with the original rotation system is
proved, including parallel edges. The resulting filter covers every bounded
bridgeless connected cubic map. Spherical admissibility is not checked here.
-/

namespace Mettapedia.GraphTheory.FourColor.BoundedCubicColourTrace

open GoertzelV24FaceDualConnectedness GoertzelV24RotationEdgeBridge

/-- The primal graph after retaining a specified set of edge identifiers. -/
def primalOn {n m : Nat} (code : Code n m) (keep : Fin m → Bool) :
    SimpleGraph (Fin n) where
  Adj u v := u ≠ v ∧ ∃ e, keep e = true ∧
    u ∈ endpoints code e ∧ v ∈ endpoints code e
  symm := ⟨by
    rintro u v ⟨hne, e, he, hu, hv⟩
    exact ⟨hne.symm, e, he, hv, hu⟩⟩
  loopless := ⟨fun _ h => h.1 rfl⟩

instance {n m : Nat} (code : Code n m) (keep : Fin m → Bool) :
    DecidableRel (primalOn code keep).Adj := fun _ _ => by
  change Decidable (_ ≠ _ ∧ ∃ e, keep e = true ∧ _ ∈ endpoints code e ∧
    _ ∈ endpoints code e)
  infer_instance

def connected {n m : Nat} (code : Code n m) : Bool :=
  decide (primalOn code (fun _ => true)).Connected

/-- Delete one edge identifier, retaining all parallel edges with other indices. -/
def deletedPrimal {n m : Nat} (code : Code n m) (e : Fin m) :
    SimpleGraph (Fin n) := primalOn code (fun f => decide (f ≠ e))

instance {n m : Nat} (code : Code n m) (e : Fin m) :
    DecidableRel (deletedPrimal code e).Adj :=
  inferInstanceAs (DecidableRel (primalOn code _).Adj)

def BridgeFree {n m : Nat} (code : Code n m) : Prop :=
  ∀ e u v, u ∈ endpoints code e → v ∈ endpoints code e →
    (deletedPrimal code e).Reachable u v

instance {n m : Nat} (code : Code n m) : Decidable (BridgeFree code) := by
  unfold BridgeFree
  infer_instance

def bridgeFree {n m : Nat} (code : Code n m) : Bool := decide (BridgeFree code)

section Encoding

universe u v
variable {V : Type u} {E : Type v} [Fintype V] [DecidableEq V]
  [Fintype E] [DecidableEq E]
variable (RS : RotationSystem V E) (hc : RS.IsCubic)

private theorem oriented_endpoints {e : E} {u v : V} (hne : u ≠ v)
    (hu : u ∈ RS.endpoints e) (hv : v ∈ RS.endpoints e) :
    ∃ d : RS.D, RS.edgeOf d = e ∧ RS.vertOf d = u ∧
      RS.vertOf (RS.alpha d) = v := by
  obtain ⟨d, hd, hdu⟩ := RS.mem_endpoints_iff.1 hu
  rw [RS.endpoints_eq_pair_of_mem hd] at hv
  rcases Finset.mem_insert.1 hv with hv | hv
  · exact False.elim (hne (hdu.symm.trans hv.symm))
  · exact ⟨d, by simpa [RotationSystem.dartsOn] using hd,
      hdu, (Finset.mem_singleton.1 hv).symm⟩

theorem primalOn_encode_adj (keep : Fin (Fintype.card E) → Bool) (u v : V) :
    (primalOn (encode RS hc) keep).Adj
      (Fintype.equivFin V u) (Fintype.equivFin V v) ↔
    ∃ d : RS.D, keep (Fintype.equivFin E (RS.edgeOf d)) = true ∧
      RS.vertOf d = u ∧ RS.vertOf (RS.alpha d) = v := by
  change (_ ≠ _ ∧ ∃ e, keep e = true ∧ _ ∈ endpoints _ e ∧
    _ ∈ endpoints _ e) ↔ _
  simp only [mem_endpoints_encode, Equiv.symm_apply_apply, ne_eq, Equiv.apply_eq_iff_eq]
  constructor
  · rintro ⟨hne, e, he, hu, hv⟩
    obtain ⟨d, hd, hdu, hdv⟩ := oriented_endpoints RS hne hu hv
    refine ⟨d, ?_, hdu, hdv⟩
    simpa [hd] using he
  · rintro ⟨d, he, rfl, rfl⟩
    refine ⟨RS.no_self_loops d, Fintype.equivFin E (RS.edgeOf d), he, ?_, ?_⟩
    all_goals
      simp only [Equiv.symm_apply_apply]
      rw [RS.endpoints_eq_pair_of_mem (e := RS.edgeOf d) (d := d)
        (by simp [RotationSystem.dartsOn])]
      simp

/-- The code's full primal graph is isomorphic to the original primal graph. -/
noncomputable def primalIso :
    rotationPrimalGraph RS ≃g primalOn (encode RS hc) (fun _ => true) where
  toEquiv := Fintype.equivFin V
  map_rel_iff' := by
    intro u v
    simpa only [true_and, rotationPrimalGraph_adj_iff] using
      primalOn_encode_adj RS hc (fun _ => true) u v

/-- The same isomorphism holds after deleting one numbered edge. -/
noncomputable def deletedIso (e : E) :
    edgeDeletedPrimalGraph RS e ≃g
      deletedPrimal (encode RS hc) (Fintype.equivFin E e) where
  toEquiv := Fintype.equivFin V
  map_rel_iff' := by
    intro u v
    simpa only [deletedPrimal, edgeDeletedPrimalGraph_adj_iff,
      decide_eq_true_eq, ne_eq, Equiv.apply_eq_iff_eq] using
      primalOn_encode_adj RS hc (fun f => decide (f ≠ Fintype.equivFin E e)) u v

theorem connected_encode_iff :
    connected (encode RS hc) = true ↔ (rotationPrimalGraph RS).Connected := by
  simp only [connected, decide_eq_true_eq]
  exact (primalIso RS hc).connected_iff.symm

theorem bridgeFree_encode_iff :
    bridgeFree (encode RS hc) = true ↔ EdgeBridgeFree RS := by
  simp only [bridgeFree, decide_eq_true_eq]
  constructor
  · intro h d
    apply (deletedIso RS hc (RS.edgeOf d)).reachable_iff.1
    apply h
    all_goals
      rw [mem_endpoints_encode]
      simp only [deletedIso, Equiv.symm_apply_apply]
      rw [RS.endpoints_eq_pair_of_mem (e := RS.edgeOf d) (d := d)
        (by simp [RotationSystem.dartsOn])]
      simp
  · intro h e u v hu hv
    have hu' := (mem_endpoints_encode RS hc e u).1 hu
    have hv' := (mem_endpoints_encode RS hc e v).1 hv
    by_cases huv : u = v
    · subst v
      exact SimpleGraph.Reachable.rfl
    obtain ⟨d, hd, hdu, hdv⟩ := oriented_endpoints RS
      (fun heq => huv ((Fintype.equivFin V).symm.injective heq)) hu' hv'
    have hr := (deletedIso RS hc (RS.edgeOf d)).reachable_iff.2 (h d)
    change (deletedPrimal (encode RS hc) (Fintype.equivFin E (RS.edgeOf d))).Reachable
      (Fintype.equivFin V (RS.vertOf d))
      (Fintype.equivFin V (RS.vertOf (RS.alpha d))) at hr
    simpa only [hd, hdu, hdv, Equiv.apply_symm_apply] using hr

end Encoding

def BoundedCode.topologyValid {bound : Nat} (code : BoundedCode bound) : Bool :=
  code.valid && connected code.2.2 && bridgeFree code.2.2

/-- Connectivity/bridge refinement only; this is not a planarity filter. -/
def topologicalEnvelope (bound : Nat) : Finset (BoundedCode bound) :=
  Finset.univ.filter fun code => code.topologyValid = true

theorem topologicalEnvelope_subset_structuralEnvelope (bound : Nat) :
    topologicalEnvelope bound ⊆ structuralEnvelope bound := by
  intro code h
  simp only [topologicalEnvelope, Finset.mem_filter, Finset.mem_univ, true_and,
    BoundedCode.topologyValid, Bool.and_eq_true] at h
  exact Finset.mem_filter.2 ⟨Finset.mem_univ code, h.1.1⟩

theorem trace_mem_topologicalEnvelope
    {V E : Type*} [Fintype V] [DecidableEq V] [Fintype E] [DecidableEq E]
    (RS : RotationSystem V E) (hc : RS.IsCubic)
    (hconnected : (rotationPrimalGraph RS).Connected) (hfree : EdgeBridgeFree RS)
    {bound : Nat} (hb : Fintype.card V ≤ bound) :
    trace RS hc hb ∈ topologicalEnvelope bound := by
  simp only [topologicalEnvelope, Finset.mem_filter, Finset.mem_univ, true_and,
    BoundedCode.topologyValid, Bool.and_eq_true]
  exact ⟨⟨decide_eq_true (encode_valid RS hc),
    (connected_encode_iff RS hc).2 hconnected⟩, (bridgeFree_encode_iff RS hc).2 hfree⟩

namespace Controls

theorem tetrahedron_connected : connected tetrahedron = true := by decide +kernel

theorem tetrahedron_bridgeFree : bridgeFree tetrahedron = true := by decide +kernel

def parallelTriple : Code 2 3 := ![![0, 1, 2], ![0, 1, 2]]

theorem parallelTriple_bridgeFree : bridgeFree parallelTriple = true := by decide +kernel

theorem bridged_connected : connected bridged = true := by decide +kernel

theorem bridged_not_bridgeFree : bridgeFree bridged = false := by decide +kernel

def disconnectedTriples : Code 4 6 :=
  ![![0, 1, 2], ![0, 1, 2], ![3, 4, 5], ![3, 4, 5]]

theorem disconnectedTriples_not_connected : connected disconnectedTriples = false := by
  decide +kernel

theorem disconnectedTriples_bridgeFree : bridgeFree disconnectedTriples = true := by
  decide +kernel

/-- The connectivity/bridge filter removes the earlier bad structural control. -/
theorem bridged_not_in_topologicalEnvelope {bound : Nat} (hb : 6 ≤ bound) :
    (⟨⟨6, by omega⟩, ⟨9, by omega⟩, bridged⟩ : BoundedCode bound) ∉
      topologicalEnvelope bound := by
  simp [topologicalEnvelope, BoundedCode.topologyValid, bridged_not_bridgeFree]

end Controls

end Mettapedia.GraphTheory.FourColor.BoundedCubicColourTrace
