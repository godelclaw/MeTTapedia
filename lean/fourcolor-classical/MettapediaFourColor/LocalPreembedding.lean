import MettapediaFourColor.FaithfulKernelEmbedding
import MettapediaFourColor.HypermapTransport

/-!
# Preembeddings from complete local stars

A face-closed radius-two kernel is connected by ring links. Consequently a
map preserving its complete cyclic stars and every edge is a preembedding.
Relabelling the source preserves both the kernel and all arity observations.
-/

namespace FourColor.Hypermap

variable {D E : Type*}

theorem kernel_relabel (G : Hypermap D) (e : D ≃ E) (r : List D) (x : D) :
    (G.relabel e).Kernel (r.map e) (e x) ↔ G.Kernel r x := by
  simp only [Kernel, Fband, List.mem_map]
  apply not_congr
  constructor
  · rintro ⟨_, ⟨y, hy, rfl⟩, h⟩
    exact ⟨y, hy, (sameCycle_relabel e G.face x y).mp h⟩
  · rintro ⟨y, hy, h⟩
    exact ⟨e y, ⟨y, hy, rfl⟩, (sameCycle_relabel e G.face x y).mpr h⟩

theorem arity_relabel (G : Hypermap D) (e : D ≃ E) (x : D) :
    (G.relabel e).arity (e x) = G.arity x := by
  apply Function.minimalPeriod_eq_minimalPeriod_iff.mpr
  intro n
  change ((e.permCongr G.face)^[n]) (e x) = e x ↔ G.face^[n] x = x
  simp only [Equiv.Perm.iterate_eq_pow]
  change (e.permCongrHom G.face ^ n) (e x) = e x ↔ (G.face ^ n) x = x
  rw [← map_pow e.permCongrHom]
  simp

end FourColor.Hypermap

namespace FourColor.LocalPreembedding

open Hypermap

variable {D E : Type*} {G : Hypermap D} {H : Hypermap E} {A : Set D}

/-- The radius-two witness supplies an explicit four-dart connecting path. -/
theorem rlinkConnected (plain : G.Plain)
    (closed : ∀ z, G.face z ∈ A ↔ z ∈ A) (radius : G.Radius2 A) :
    G.RlinkConnected A := by
  have along {u v : D} (h : G.CFace u v) : u ∈ A ↔ v ∈ A :=
    (congr_of_sameCycle (fun z => propext (closed z)) h).to_iff
  obtain ⟨root, hr, reach⟩ := radius
  intro x hx y hy
  obtain ⟨u, v, hru, hxv, heu, huv⟩ := (atRadius2_iff closed).mp (reach x hx)
  obtain ⟨u', v', hru', hyv', heu', hu'v'⟩ := (atRadius2_iff closed).mp (reach y hy)
  refine ⟨[v, G.edge u, u', G.edge v'], ?_, ?_⟩
  · rw [plain.node_face]
    have a : G.Rlink (G.edge x) v := by simpa [Rlink, plain.edge_edge] using hxv
    have b : G.Rlink v (G.edge u) := huv.symm
    have c : G.Rlink (G.edge u) u' := by
      simpa [Rlink, plain.edge_edge] using hru.symm.trans hru'
    have d : G.Rlink u' (G.edge v') := hu'v'
    have e : G.Rlink (G.edge v') y := by
      simpa [Rlink, plain.edge_edge] using hyv'.symm
    simpa only [List.cons_append, List.nil_append, List.isChain_cons_cons,
      List.isChain_singleton, and_true] using And.intro a ⟨b, c, d, e⟩
  · intro z hz
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact (along hxv).mp hx
    · exact heu
    · exact (along hru').mp hr
    · exact (along hu'v').mp heu'

/-- Complete edge preservation makes the radius-two paths edge-central. -/
theorem of_radius2 (plain : G.Plain)
    (closed : ∀ z, G.face z ∈ A ↔ z ∈ A) (radius : G.Radius2 A)
    (f : D → E) (edge : ∀ x, f (G.edge x) = H.edge (f x))
    (face : ∀ x ∈ A, f (G.face x) = H.face (f x))
    (arity : ∀ x ∈ A, H.arity (f x) = G.arity x) :
    Preembedding G H f A := by
  refine ⟨face, arity, ?_, ?_⟩
  · intro x _
    exact ⟨x, Equiv.Perm.SameCycle.rfl, edge x⟩
  · have eq : {x | x ∈ A ∧ EdgeCentral G H f x} = A := by
      ext x
      exact ⟨And.left, fun hx => ⟨hx, edge x⟩⟩
    rw [eq]
    exact rlinkConnected plain closed radius

end FourColor.LocalPreembedding
