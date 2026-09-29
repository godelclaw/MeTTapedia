import MettapediaFourColor.ConfigurationTable

/-!
# Transport from reference configurations to finite presentations

A realization is a dart bijection preserving the complete hypermap and its
reference point. It transports ordered rings and their actual colouring
traces, not merely the existence of some colouring.
-/

namespace FourColor

private theorem cyclicChain_map {D E : Type*} {r : D → D → Prop} {s : E → E → Prop}
    (f : D → E) (h : ∀ x y, r x y → s (f x) (f y)) {p : List D}
    (hp : IsCyclicChain r p) : IsCyclicChain s (p.map f) := by
  constructor
  · exact (List.isChain_map f).mpr (hp.1.imp (fun {a b} hab => h a b hab))
  · intro x hx y hy
    rw [List.getLast?_map] at hx
    rw [List.head?_map] at hy
    obtain ⟨a, ha, rfl⟩ := Option.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Option.mem_map.mp hy
    exact h a b (hp.2 a ha b hb)

theorem Hypermap.cpring_relabel {D E : Type*} [Finite D] [Finite E]
    (G : Hypermap D) (e : D ≃ E) (p : D) :
    (G.relabel e).cpring (e p) = (G.cpring p).map e := by
  apply Hypermap.cpring_eq
  · exact cyclicChain_map e (fun x y h => by rw [relabel_node, h])
      Hypermap.isCyclicChain_cpring
  · exact List.Nodup.map e.injective Hypermap.nodup_cpring
  · simpa using (Hypermap.cpring_ne_nil (G := G) (x₀ := p))
  · rw [relabel_node, List.headD_map, Hypermap.headD_cpring]

theorem Hypermap.ringTrace_relabel {D E : Type*} (G : Hypermap D) (e : D ≃ E)
    (r : List D) (et : List Color) :
    (G.relabel e).RingTrace (r.map e) et ↔ G.RingTrace r et := by
  constructor
  · rintro ⟨k, hk, htrace⟩
    exact ⟨k ∘ e, (coloring_relabel G e k).mp hk, by simpa using htrace⟩
  · rintro ⟨k, hk, htrace⟩
    refine ⟨k ∘ e.symm, (coloring_relabel G e _).mpr ?_, ?_⟩
    · simpa [Function.comp_def] using hk
    · simpa [List.map_map, Function.comp_def] using htrace

namespace ConfigurationTable

structure Realization (M : PointedMap) {n : ℕ} [NeZero n] (t : Data n) (p : Fin n) where
  numbering : M.Dart ≃ Fin n
  map_eq : M.map.relabel numbering = t.map
  point_eq : numbering M.point = p

variable {M : PointedMap} {n : ℕ} [NeZero n] {t : Data n} {p : Fin n}
    (R : Realization M t p)

/-- Transport the full colouring function in both directions. -/
def Realization.coloringEquiv : {k : M.Dart → Color // M.map.Coloring k} ≃
    {k : Fin n → Color // t.map.Coloring k} where
  toFun k := ⟨k.val ∘ R.numbering.symm, by
    rw [← R.map_eq, Hypermap.coloring_relabel]
    simpa [Function.comp_def] using k.property⟩
  invFun k := ⟨k.val ∘ R.numbering, by
    apply (Hypermap.coloring_relabel M.map R.numbering _).mp
    rw [R.map_eq]
    exact k.property⟩
  left_inv k := by
    apply Subtype.ext
    funext d
    simp [Function.comp_def]
  right_inv k := by
    apply Subtype.ext
    funext d
    simp [Function.comp_def]

theorem Realization.ring : M.cpring.map R.numbering = t.map.cpring p := by
  rw [PointedMap.cpring, ← Hypermap.cpring_relabel, R.map_eq, R.point_eq]

include R in
theorem Realization.forwardRingTrace (et : List Color) :
    M.map.RingTrace M.cpring et ↔ t.map.RingTrace (t.map.cpring p) et := by
  rw [← R.ring, ← R.map_eq]
  exact (Hypermap.ringTrace_relabel M.map R.numbering _ et).symm

include R in
theorem Realization.ringTrace (et : List Color) :
    M.map.RingTrace M.cpring.reverse et ↔
      t.map.RingTrace (t.map.cpring p).reverse et := by
  rw [← R.ring, ← List.map_reverse, ← R.map_eq]
  exact (Hypermap.ringTrace_relabel M.map R.numbering _ et).symm

end ConfigurationTable
end FourColor
