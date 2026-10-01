import MettapediaFourColor.KempeBoundarySplit

/-!
# Transporting joint boundary repair between graph presentations

An exact graph isomorphism transports actual colouring witnesses and arbitrary
joint observations. A checked cyclic alignment of the ports also transports
Kempe repair. The theorem does not identify repair with an executable sequence
of recolourings or assert that independently chosen repairs compose.
-/

namespace FourColor.BoundaryRepairTransport

open KempeBoundarySplit

variable {V W C : Type*} {G : SimpleGraph V} {H : SimpleGraph W}

def coloring (e : G ≃g H) : G.Coloring C ≃ H.Coloring C :=
  SimpleGraph.coloringCongr e (Equiv.refl C)

@[simp] theorem coloring_apply (e : G ≃g H) (k : G.Coloring C) (v : V) :
    coloring e k (e v) = k v := by
  change k (e.symm (e v)) = k v
  rw [e.symm_apply_apply]

/-- Retain the entire boundary assignment, rather than its separate marginals. -/
theorem boundary_iff (e : G ≃g H) {Port : Type*} (ports : Port → V)
    (accepts : (Port → C) → Prop) :
    (∃ k : G.Coloring C, accepts (fun p => k (ports p))) ↔
      ∃ k : H.Coloring C, accepts (fun p => k (e (ports p))) := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨coloring e k, by simpa using hk⟩
  · rintro ⟨k, hk⟩
    exact ⟨coloring e.symm k, hk⟩

theorem trace_iff (e : G ≃g H) (ports : List V) (et : List Color) :
    GraphTrace G ports et ↔ GraphTrace H (ports.map e) et := by
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨coloring e k, ?_⟩
    simpa only [List.map_map, Function.comp_def, coloring_apply] using hk
  · rintro ⟨k, hk⟩
    refine ⟨coloring e.symm k, ?_⟩
    change et = trace (ports.map (fun v => k (e v)))
    simpa only [List.map_map, Function.comp_def] using hk

/-- A boundary relabelling and cyclic alignment transfer the same repair law. -/
theorem repairs (e : G ≃g H) (ports : List V) (target : List W) (shift : ℕ)
    (alignment : (ports.map e).rotate shift = target) {n : ℕ}
    (base : Repairs (GraphTrace H target) n) : Repairs (GraphTrace G ports) n := by
  intro et hlen hzero hsum Q hQ hq
  have repaired : KempeCoclosure (GraphTrace H (ports.map e)) et := by
    apply graph_rotate_back shift
    rw [alignment]
    apply base
    · simpa using hlen
    · exact fun h => hzero (List.mem_rotate.mp h)
    · rwa [(List.rotate_perm et shift).sum_eq]
  obtain ⟨es, hs, hqs⟩ := repaired Q hQ hq
  exact ⟨es, (trace_iff e ports es).mpr hs, hqs⟩

end FourColor.BoundaryRepairTransport
