import MettapediaFourColor.ConfigurationRealization
import MettapediaFourColor.ConfigurationFaceGraph

/-!
# Exact contract-colouring transport

Contract colourings impose equality on the selected edges and inequality on
every other edge. Relabelling darts and naming face classes preserve these
constraints and their ordered boundary observations in both directions.
-/

namespace FourColor

namespace Hypermap

variable {D E : Type*} (G : Hypermap D) (e : D ≃ E)

theorem insertE_relabel (cc : List D) :
    (G.relabel e).insertE (cc.map e) = (G.insertE cc).map e := by
  induction cc with
  | nil => rfl
  | cons d cc ih => simp [ih]

theorem ccColoring_relabel (cc : List D) (k : E → Color) :
    (G.relabel e).CcColoring (cc.map e) k ↔ G.CcColoring cc (k ∘ e) := by
  have mem (d : D) : e d ∈ (G.relabel e).insertE (cc.map e) ↔ d ∈ G.insertE cc := by
    rw [insertE_relabel, List.mem_map_of_injective e.injective]
  constructor
  · intro h
    refine ⟨fun d => ?_, fun d => ?_⟩
    · simpa only [relabel_edge, mem, Function.comp_apply] using h.edge (e d)
    · simpa only [relabel_face, Function.comp_apply] using h.face (e d)
  · intro h
    constructor
    · intro d
      obtain ⟨d, rfl⟩ := e.surjective d
      simpa only [relabel_edge, mem, Function.comp_apply] using h.edge d
    · intro d
      obtain ⟨d, rfl⟩ := e.surjective d
      simpa only [relabel_face, Function.comp_apply] using h.face d

theorem ccRingTrace_relabel (cc r : List D) (et : List Color) :
    (G.relabel e).CcRingTrace (cc.map e) (r.map e) et ↔ G.CcRingTrace cc r et := by
  constructor
  · rintro ⟨k, hk, htrace⟩
    exact ⟨k ∘ e, (ccColoring_relabel G e cc k).mp hk, by simpa using htrace⟩
  · rintro ⟨k, hk, htrace⟩
    refine ⟨k ∘ e.symm, (ccColoring_relabel G e cc _).mpr ?_, ?_⟩
    · simpa [Function.comp_def] using hk
    · simpa [List.map_map, Function.comp_def] using htrace

end Hypermap

namespace ConfigurationTable

variable {M : PointedMap} {n : ℕ} [NeZero n] {t : Data n} {p : Fin n}
    (R : Realization M t p)

/-- Marked darts retain their numbers when the complete pointed map is transported. -/
theorem Realization.map_numbering_of_heq {N : PointedMap} (h : M = N)
    {cc : List M.Dart} {dd : List N.Dart} (hh : HEq cc dd) :
    dd.map (h ▸ R).numbering = cc.map R.numbering := by
  cases h
  cases hh
  rfl

theorem Realization.ccRingTrace (cc r : List M.Dart) (et : List Color) :
    M.map.CcRingTrace cc r et ↔
      t.map.CcRingTrace (cc.map R.numbering) (r.map R.numbering) et := by
  rw [← R.map_eq]
  exact (Hypermap.ccRingTrace_relabel M.map R.numbering cc r et).symm

end ConfigurationTable

namespace ConfigurationFaceGraph.Presentation

variable {D V : Type*} {M : Hypermap D} {G : SimpleGraph V}
    (P : Presentation M G)

/-- Vertex assignments satisfying exactly the selected edge equalities. -/
def ContractAssignment (cc : List D) :=
  {k : V → Color // ∀ d,
    k (P.vertex (M.edge d)) = k (P.vertex d) ↔ d ∈ M.insertE cc}

/-- Face naming preserves every contract-colouring witness. -/
def contractColoringEquiv (cc : List D) :
    P.ContractAssignment cc ≃ {k : D → Color // M.CcColoring cc k} where
  toFun k := ⟨fun d => k.val (P.vertex d),
    ⟨k.property, fun d => congrArg k.val (P.vertex_face d)⟩⟩
  invFun k := ⟨fun v => k.val (P.representative v), by
    intro d
    change k.val (P.representative (P.vertex (M.edge d))) =
      k.val (P.representative (P.vertex d)) ↔ d ∈ M.insertE cc
    rw [← k.property.cface (P.same_face (M.edge d)),
      ← k.property.cface (P.same_face d)]
    exact k.property.edge d⟩
  left_inv k := by
    apply Subtype.ext
    funext v
    exact congrArg k.val (P.vertex_rep v)
  right_inv k := by
    apply Subtype.ext
    funext d
    exact (k.property.cface (P.same_face d)).symm

theorem ccRingTrace_iff (cc r : List D) (et : List Color) :
    M.CcRingTrace cc r et ↔ ∃ k : P.ContractAssignment cc,
      et = trace (r.map fun d => k.val (P.vertex d)) := by
  constructor
  · rintro ⟨k, hk, htrace⟩
    refine ⟨(P.contractColoringEquiv cc).symm ⟨k, hk⟩, ?_⟩
    convert htrace using 1
    congr 1
    apply List.map_congr_left
    intro d _
    exact (hk.cface (P.same_face d)).symm
  · rintro ⟨k, htrace⟩
    exact ⟨(P.contractColoringEquiv cc k).val,
      (P.contractColoringEquiv cc k).property, htrace⟩

end ConfigurationFaceGraph.Presentation
end FourColor
