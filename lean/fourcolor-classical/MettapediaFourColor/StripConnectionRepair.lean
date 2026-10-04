import MettapediaFourColor.StripConnectionGeometry
import MettapediaFourColor.StripSingletonRepair

/-!
# A failed component guard supplies a different D0099 repair

A zero/one connection between ports eight and ten geometrically isolates
port nine in the complementary component. Switching that component repairs
the entire boundary-list domain. Its internal size is unrestricted.
The core witness depends only on the colour at port three.
-/

namespace FourColor.StripConnectionRepair

open SimpleGraph Color StripResponseSummary StripSourceExtension
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

def coreColour (a : Color) : Fin 8 → Color :=
  ![c3,c2,c1,c0,c3,if a = c2 then c3 else c2,c0,if a = c2 then c2 else c3]

theorem core_edges : ∀ a ∈ ({c2,c3} : Finset Color), ∀ e ∈ edges,
    coreColour a e.1 ≠ coreColour a e.2 := by decide +kernel

theorem core_lists : ∀ a ∈ ({c2,c3} : Finset Color), ∀ v i, i ∈ attachments v →
    ∀ x ∈ StripSingletonRepair.before i, (i = 3 → x = a) →
      coreColour a v ≠ (if i = 9 then c2 else x) := by decide +kernel

/-- One common formula gives the core after changing only port nine. -/
theorem core_valid (b : Boundary) (initial : ∀ i, b i ∈ StripSingletonRepair.before i) :
    ValidCore (fun i => if i = 9 then c2 else b i) (coreColour (b 3)) := by
  have a : b 3 ∈ ({c2,c3} : Finset Color) := by simpa [StripSingletonRepair.before] using initial 3
  exact ⟨fun v i hi => core_lists _ a v i hi _ (initial i) (fun h => h ▸ rfl),core_edges _ a⟩

theorem repair_of_isolated_port {W : Type*} {H : SimpleGraph W}
    (C : H.Coloring Color) (ports : Fin 11 → W)
    (initial : ∀ i, C (ports i) ∈ StripSingletonRepair.before i)
    (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
      H.Adj (ports i) (ports j))
    (K : (C.bicoloredSubgraph c2 c3).ConnectedComponent)
    (membership : ∀ i, ports i ∈ C.kempeComponentSet c2 c3 K ↔ i = 9) :
    ∃ D : H.Coloring Color, ∃ h : History C D, h.length = 1 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (port i) = D (ports i) := by
  classical
  let D := C.swapOnKempeComponent c2 c3 K
  have b9 : C (ports 9) = c3 := by simpa [StripSingletonRepair.before] using initial 9
  have boundary : ∀ i, D (ports i) = if i = 9 then c2 else C (ports i) := by
    intro i
    change (if ports i ∈ C.kempeComponentSet c2 c3 K then
      Equiv.swap c2 c3 (C (ports i)) else C (ports i)) = _
    rw [membership]
    by_cases h : i = 9
    · subst i; simp [b9]
    · simp [h]
  have core := core_valid (fun i => C (ports i)) initial
  have actual : ValidCore (fun i => D (ports i)) (coreColour (C (ports 3))) := by
    simpa only [boundary] using core
  let k := colouring (fun i => D (ports i)) _
    (fun i j edge => D.valid (embedding i j edge)) actual
  refine ⟨D,.cons (.switch C c2 c3 K) (.refl D),rfl,k,?_⟩
  intro i
  change completeColour (fun j => D (ports j)) (coreColour (C (ports 3))) (port i) = _
  exact colour_port _ _ i

end FourColor.StripConnectionRepair

namespace FourColor.StripConnectionGeometry

open SimpleGraph Mettapedia.GraphTheory.FourColor
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open SimpleGraphDartRotation Color
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate
noncomputable section

private theorem component_walk {W : Type*} {H : SimpleGraph W}
    (C : H.Coloring Color) (a b : Color)
    (K : (C.bicoloredSubgraph a b).ConnectedComponent)
    {u v : W} (hu : u ∈ C.kempeComponentSet a b K)
    (hv : v ∈ C.kempeComponentSet a b K) :
    ∃ walk : H.Walk u v, ∀ w ∈ walk.support, C w = a ∨ C w = b := by
  obtain ⟨hua,huK⟩ := hu
  obtain ⟨hva,hvK⟩ := hv
  obtain ⟨q⟩ := ConnectedComponent.exact (huK.trans hvK.symm)
  let forget : C.bicoloredSubgraph a b →g H := ⟨Subtype.val,fun h => h⟩
  refine ⟨q.map forget,?_⟩
  intro w hw
  rw [Walk.support_map,List.mem_map] at hw
  obtain ⟨z,_,rfl⟩ := hw
  exact z.property

variable {V W : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} {data : Data G}

structure ExteriorReading (s : Patch data) (H : SimpleGraph W) where
  embedding : H ↪g G
  outside : ∀ w, s.Exterior (embedding w)
  ports : Fin 11 → W
  boundary : ∀ j, embedding (ports j) = s.point (StripResponseSummary.port j)

namespace ExteriorReading
variable {s : Patch data} (e : ExteriorReading s H)

theorem port_adj (i j : Fin 11)
    (h : TriangleStripAnchors.input0099.graph.Adj (StripResponseSummary.port i)
      (StripResponseSummary.port j)) : H.Adj (e.ports i) (e.ports j) := by
  apply e.embedding.map_adj_iff.mp
  rw [e.boundary,e.boundary]
  exact s.adjacent _ _ h

variable (rotation : VertexRotationCyclic data.toRotationSystem)
  (dual : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
    (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
  (connected : G.Connected)
  (euler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
    Fintype.card (OrbitFace data.toRotationSystem) = 2)
  (C : H.Coloring Color)
  (p : H.Walk (e.ports 8) (e.ports 10))
  (active : ∀ x ∈ p.support, C x = c0 ∨ C x = c1)

include rotation dual connected euler active in
/-- The complementary component has no other active boundary port. -/
theorem excludes_middle (K : (C.bicoloredSubgraph c2 c3).ConnectedComponent)
    (m9 : e.ports 9 ∈ C.kempeComponentSet c2 c3 K) :
    ∀ i : Fin 5, e.ports ⟨i.val+3,by omega⟩ ∉ C.kempeComponentSet c2 c3 K := by
  intro i member
  obtain ⟨q,hq⟩ := component_walk C c2 c3 K m9 member
  let P := (p.map e.embedding.toHom).copy (e.boundary 8) (e.boundary 10)
  let Q := (q.map e.embedding.toHom).copy (e.boundary 9) (e.boundary ⟨i.val+3,by omega⟩)
  have image {u v : W} (r : H.Walk u v) {u' v' : V}
      (hu : e.embedding u = u') (hv : e.embedding v = v') (x : V) :
      x ∈ ((r.map e.embedding.toHom).copy hu hv).support ↔
        ∃ y ∈ r.support, e.embedding y = x := by
    simp [Walk.support_copy,Walk.support_map]
  have outsideP : ∀ x ∈ P.support, s.Exterior x := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := (image p _ _ x).mp hx
    exact e.outside y
  have outsideQ : ∀ x ∈ Q.support, s.Exterior x := by
    intro x hx
    obtain ⟨y,_,rfl⟩ := (image q _ _ x).mp hx
    exact e.outside y
  have disjoint : ∀ x ∈ Q.support, x ∉ P.support := by
    intro x hx hp
    obtain ⟨y,hy,ey⟩ := (image q _ _ x).mp hx
    obtain ⟨z,hz,ez⟩ := (image p _ _ x).mp hp
    have same := e.embedding.injective (ey.trans ez.symm)
    subst z
    rcases hq y hy with h | h <;> rcases active y hz with h' | h' <;>
      cases h.symm.trans h'
  exact s.no_crossing_paths rotation dual connected euler P outsideP i Q outsideQ disjoint

include rotation dual connected euler active in
/-- An actual path supplies separation and a one-switch source repair. -/
theorem repair_of_path
    (initial : ∀ i, C (e.ports i) ∈ StripSingletonRepair.before i) :
    ∃ D : H.Coloring Color, ∃ h : History C D, h.length = 1 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (StripResponseSummary.port i) = D (e.ports i) := by
  classical
  have b9 : C (e.ports 9) = c3 := by simpa [StripSingletonRepair.before] using initial 9
  let K := (C.bicoloredSubgraph c2 c3).connectedComponentMk ⟨e.ports 9,Or.inr b9⟩
  have m9 : e.ports 9 ∈ C.kempeComponentSet c2 c3 K := C.mem_kempeComponentSet_self (Or.inr b9)
  have excluded := e.excludes_middle rotation dual connected euler C p active K m9
  have inactive : ∀ i : Fin 11, i ∈ ([0,1,2,8,10] : List (Fin 11)) →
      e.ports i ∉ C.kempeComponentSet c2 c3 K := by
    intro i hi member
    have a := C.mem_bicoloredSet_of_mem_kempeComponentSet member
    have checks : ∀ i ∈ ([0,1,2,8,10] : List (Fin 11)),
        ∀ c ∈ StripSingletonRepair.before i, c ≠ c2 ∧ c ≠ c3 := by decide +kernel
    exact a.elim (checks i hi _ (initial i)).1 (checks i hi _ (initial i)).2
  have membership : ∀ i, e.ports i ∈ C.kempeComponentSet c2 c3 K ↔ i = 9 := by
    intro i
    by_cases h9 : i = 9
    · subst i; exact iff_of_true m9 rfl
    · apply iff_of_false _ h9
      by_cases middle : 3 ≤ i.val ∧ i.val < 8
      · let j : Fin 5 := ⟨i.val-3,by omega⟩
        have eq : (⟨j.val+3,by omega⟩ : Fin 11) = i := Fin.ext (by dsimp [j]; omega)
        exact eq ▸ excluded j
      · apply inactive i
        simp only [List.mem_cons,List.not_mem_nil,or_false]
        have val9 : i.val ≠ 9 := fun h => h9 (Fin.ext h)
        have choices : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 8 ∨ i.val = 10 := by omega
        simp only [Fin.ext_iff]
        change i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 8 ∨ i.val = 10
        exact choices
  exact StripConnectionRepair.repair_of_isolated_port C e.ports initial e.port_adj K membership

include rotation dual connected euler in
/-- The formerly excluded connection supplies a certified alternative. -/
theorem repair_of_component
    (initial : ∀ i, C (e.ports i) ∈ StripSingletonRepair.before i)
    (K : (C.bicoloredSubgraph c0 c1).ConnectedComponent)
    (m8 : e.ports 8 ∈ C.kempeComponentSet c0 c1 K)
    (m10 : e.ports 10 ∈ C.kempeComponentSet c0 c1 K) :
    ∃ D : H.Coloring Color, ∃ h : History C D, h.length = 1 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (StripResponseSummary.port i) = D (e.ports i) := by
  obtain ⟨walk,hw⟩ := component_walk C c0 c1 K m8 m10
  exact e.repair_of_path rotation dual connected euler C walk hw initial

end ExteriorReading
end
end FourColor.StripConnectionGeometry
