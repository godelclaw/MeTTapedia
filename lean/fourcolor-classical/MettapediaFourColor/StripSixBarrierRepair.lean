import MettapediaFourColor.StripSixBarrierGeometry
import MettapediaFourColor.StripSixRelease

/-!
# A preserved path supplies a two-stage repair

Switch the zero/one component at port eight. An old zero/two path from
port two to four or seven, disjoint from that component, survives.
Planarity then protects ports one, nine and ten from the one/three
component at port three. Ports five and six move together. One core
formula handles either choice, on arbitrary exteriors satisfying the path
hypothesis. Existence of that path is a separate obligation.
-/

namespace FourColor.StripSixBarrierRepair

open SimpleGraph Color StripResponseSummary StripSourceExtension
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

def middle : Boundary := ![c0,c1,c0,c3,c2,c3,c1,c2,c0,c3,c1]
def selected (b : Bool) : List (Fin 11) := if b then [3,5,6] else [3]
def boundary (b : Bool) (i : Fin 11) : Color :=
  if i ∈ selected b then Equiv.swap c1 c3 (middle i) else middle i
theorem selected_mem : ∀ b i, i ∈ selected b ↔ i = 3 ∨ (b = true ∧ (i = 5 ∨ i = 6)) := by
  decide +kernel

def coreColour (b : Bool) : Fin 8 → Color :=
  ![if b then c1 else c3,if b then c2 else c1,c3,c0,if b then c1 else c2,c2,c0,c3]

theorem core_valid : ∀ b, ValidCore (boundary b) (coreColour b) := by
  unfold ValidCore
  decide +kernel

theorem middle_check : ∀ i,
    (if i = 8 then Equiv.swap c0 c1 (StripSixConnection.input true i)
      else StripSixConnection.input true i) = middle i := by decide +kernel

variable {W : Type*} {H : SimpleGraph W}

/-- The original component fixes the entire boundary footprint of the other
component: only port eight remains. -/
theorem eight_members [DecidableEq W]
    (C : H.Coloring Color) (ports : Fin 11 → W)
    (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
      H.Adj (ports i) (ports j))
    (initial : ∀ i, C (ports i) = StripSixConnection.input true i)
    (K L : (C.bicoloredSubgraph c0 c1).ConnectedComponent)
    (m1 : ports 1 ∈ C.kempeComponentSet c0 c1 K)
    (m6 : ports 6 ∈ C.kempeComponentSet c0 c1 K)
    (n8 : ports 8 ∉ C.kempeComponentSet c0 c1 K)
    (m8 : ports 8 ∈ C.kempeComponentSet c0 c1 L) :
    ∀ i, ports i ∈ C.kempeComponentSet c0 c1 L ↔ i = 8 := by
  intro i
  constructor
  · intro hi
    by_contra h8
    have active := C.mem_bicoloredSet_of_mem_kempeComponentSet hi
    rw [initial] at active
    have selected : i ∈ StripSixRelease.switchedPorts := by
      by_contra outside
      exact h8 (StripSixRelease.active_ports i outside active)
    have same := (StripSixRelease.first_members C ports embedding initial K m1 m6 n8 i).mpr selected
    have eq : K = L := same.choose_spec.symm.trans hi.choose_spec
    exact n8 (eq.symm ▸ m8)
  · rintro rfl; exact m8

/-- Closure along the rim retains the shared choice of ports five and six. -/
theorem footprint (C : H.Coloring Color) (ports : Fin 11 → W)
    (initial : ∀ i, C (ports i) = middle i)
    (edge : H.Adj (ports 5) (ports 6))
    (L : (C.bicoloredSubgraph c1 c3).ConnectedComponent)
    (m3 : ports 3 ∈ C.kempeComponentSet c1 c3 L)
    (avoid : ∀ i ∈ ([1,9,10] : List (Fin 11)), ports i ∉ C.kempeComponentSet c1 c3 L) :
    ∃ b, ∀ i, ports i ∈ C.kempeComponentSet c1 c3 L ↔ i ∈ selected b := by
  classical
  have pair : ports 5 ∈ C.kempeComponentSet c1 c3 L ↔
      ports 6 ∈ C.kempeComponentSet c1 c3 L :=
    ⟨fun h => C.mem_kempeComponentSet_of_adj h edge (Or.inl (initial 6)),
     fun h => C.mem_kempeComponentSet_of_adj h edge.symm (Or.inr (initial 5))⟩
  have inactive (i : Fin 11) (h : middle i ≠ c1 ∧ middle i ≠ c3) :
      ports i ∉ C.kempeComponentSet c1 c3 L := by
    intro hi
    have active := C.mem_bicoloredSet_of_mem_kempeComponentSet hi
    rw [initial] at active
    exact active.elim h.1 h.2
  let b := decide (ports 5 ∈ C.kempeComponentSet c1 c3 L)
  have five : ports 5 ∈ C.kempeComponentSet c1 c3 L ↔ b = true := by simp [b]
  refine ⟨b,?_⟩
  intro i
  rw [selected_mem]
  fin_cases i
  · simp [inactive 0 (by decide)]
  · simp [avoid 1 (by decide)]
  · simp [inactive 2 (by decide)]
  · simp [m3]
  · simp [inactive 4 (by decide)]
  · simp [← five]
  · simp [← pair,← five]
  · simp [inactive 7 (by decide)]
  · simp [inactive 8 (by decide)]
  · simp [avoid 9 (by decide)]
  · simp [avoid 10 (by decide)]

theorem repair_after (C : H.Coloring Color) (ports : Fin 11 → W)
    (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
      H.Adj (ports i) (ports j))
    (initial : ∀ i, C (ports i) = middle i)
    (L : (C.bicoloredSubgraph c1 c3).ConnectedComponent)
    (m3 : ports 3 ∈ C.kempeComponentSet c1 c3 L)
    (avoid : ∀ i ∈ ([1,9,10] : List (Fin 11)), ports i ∉ C.kempeComponentSet c1 c3 L) :
    ∃ D : H.Coloring Color, ∃ h : History C D, h.length = 1 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (port i) = D (ports i) := by
  classical
  obtain ⟨b,members⟩ := footprint C ports initial (embedding 5 6 (by decide +kernel)) L m3 avoid
  let D := C.swapOnKempeComponent c1 c3 L
  have values (i : Fin 11) : D (ports i) = boundary b i := by
    change (if ports i ∈ C.kempeComponentSet c1 c3 L then
      Equiv.swap c1 c3 (C (ports i)) else C (ports i)) = _
    simp only [members,initial,boundary]
  have core : ValidCore (fun i => D (ports i)) (coreColour b) := by
    simpa only [values] using core_valid b
  let k := colouring (fun i => D (ports i)) _
    (fun i j h => D.valid (embedding i j h)) core
  exact ⟨D,.cons (.switch C c1 c3 L) (.refl D),rfl,k,fun i => colour_port (fun j => D (ports j)) (coreColour b) i⟩

end FourColor.StripSixBarrierRepair

namespace FourColor.StripSixBarrierGeometry

open SimpleGraph Mettapedia.GraphTheory.FourColor
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open SimpleGraphDartRotation Color
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate
noncomputable section

def targetPort (long : Bool) : Fin 11 := if long then 7 else 4
def protectedPort : Fin 3 → Fin 11 := ![1,9,10]

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
  (C : H.Coloring Color) (long : Bool)
  (p : H.Walk (e.ports 2) (e.ports (targetPort long)))
  (active : ∀ x ∈ p.support, C x = c0 ∨ C x = c2)

include rotation dual connected euler active in
theorem protects_outer (L : (C.bicoloredSubgraph c1 c3).ConnectedComponent)
    (m3 : e.ports 3 ∈ C.kempeComponentSet c1 c3 L) :
    ∀ i : Fin 3, e.ports (protectedPort i) ∉ C.kempeComponentSet c1 c3 L := by
  intro i member
  obtain ⟨q,hq⟩ := component_walk C c1 c3 L m3 member
  have endP : e.embedding (e.ports (targetPort long)) = s.point (target long) := by
    cases long <;> exact e.boundary _
  have endQ : e.embedding (e.ports (protectedPort i)) = s.point (otherPort i) := by
    fin_cases i <;> exact e.boundary _
  let P := (p.map e.embedding.toHom).copy (e.boundary 2) endP
  let Q := (q.map e.embedding.toHom).copy (e.boundary 3) endQ
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
  exact s.no_crossing_paths rotation dual connected euler long P outsideP i Q outsideQ disjoint

include rotation dual connected euler active in
/-- Preserve the old separating path, then derive the second switch's footprint. -/
theorem repair_of_preserved_path
    (initial : ∀ i, C (e.ports i) = StripSixConnection.input true i)
    (K : (C.bicoloredSubgraph c0 c1).ConnectedComponent)
    (membership : ∀ i, e.ports i ∈ C.kempeComponentSet c0 c1 K ↔ i = 8)
    (apart : ∀ x ∈ p.support, x ∉ C.kempeComponentSet c0 c1 K) :
    ∃ D : H.Coloring Color, ∃ h : History C D, h.length = 2 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (StripResponseSummary.port i) = D (e.ports i) := by
  classical
  let M := C.swapOnKempeComponent c0 c1 K
  have values (i : Fin 11) : M (e.ports i) = StripSixBarrierRepair.middle i := by
    change (if e.ports i ∈ C.kempeComponentSet c0 c1 K then
      Equiv.swap c0 c1 (C (e.ports i)) else C (e.ports i)) = _
    simpa only [membership,initial] using StripSixBarrierRepair.middle_check i
  have survives : ∀ x ∈ p.support, M x = c0 ∨ M x = c2 := by
    intro x hx
    simpa only [M,C.swapOnKempeComponent_apply_of_not_mem (apart x hx)] using active x hx
  have colour3 : M (e.ports 3) = c3 := values 3
  let L := (M.bicoloredSubgraph c1 c3).connectedComponentMk ⟨e.ports 3,Or.inr colour3⟩
  have m3 : e.ports 3 ∈ M.kempeComponentSet c1 c3 L :=
    M.mem_kempeComponentSet_self (Or.inr colour3)
  have avoids := e.protects_outer rotation dual connected euler M long p survives L m3
  have avoided : ∀ i ∈ ([1,9,10] : List (Fin 11)), e.ports i ∉ M.kempeComponentSet c1 c3 L := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact avoids 0
    · exact avoids 1
    · exact avoids 2
  obtain ⟨D,h,len,k,agree⟩ := StripSixBarrierRepair.repair_after M e.ports e.port_adj values L m3 avoided
  exact ⟨D,.cons (.switch C c0 c1 K) h,by change h.length + 1 = 2; omega,k,agree⟩

end ExteriorReading
end
end FourColor.StripSixBarrierGeometry
