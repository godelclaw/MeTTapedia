import MettapediaFourColor.StripComplementaryGeometry

/-! # A planar choice supplies a one-switch repair

For the stated boundary word, compare the zero/one components at ports
six and eight. If they differ, one avoids port one and repairs the source.
If they agree, their exterior path separates the two/three components at
ports seven and nine, and that complementary switch repairs the source.
No component-avoidance hypothesis is assumed by the geometric consumer.
-/

namespace FourColor.StripComplementaryRepair

set_option maxRecDepth 10000

open SimpleGraph Color StripResponseSummary StripSourceExtension
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

def input : Boundary := ![c0,c1,c3,c0,c2,c3,c1,c2,c1,c3,c1]
def chosen (s : Bool) : Fin 11 := if s then 8 else 6
def other (s : Bool) : Fin 11 := if s then 6 else 8
def mask01 (s t : Bool) (i : Fin 11) : Prop := i = chosen s ∨ (t = true ∧ i = 3)
instance (s t i) : Decidable (mask01 s t i) := by unfold mask01; infer_instance

def boundary01 (s t : Bool) (i : Fin 11) : Color :=
  if mask01 s t i then Equiv.swap c0 c1 (input i) else input i

def core01 (s : Bool) : Fin 8 → Color :=
  ![c3,if s then c1 else c0,c3,if s then c0 else c1,c2,c2,c0,c3]

def mask23 (a b : Bool) (i : Fin 11) : Prop :=
  i = 7 ∨ (a = true ∧ i = 2) ∨ (b = true ∧ (i = 4 ∨ i = 5))
instance (a b i) : Decidable (mask23 a b i) := by unfold mask23; infer_instance

def boundary23 (a b : Bool) (i : Fin 11) : Color :=
  if mask23 a b i then Equiv.swap c2 c3 (input i) else input i

def core23 (a : Bool) : Fin 8 → Color :=
  ![c2,c3,c1,c0,c2,if a then c3 else c2,c0,if a then c2 else c3]

theorem core01_valid : ∀ s t, ValidCore (boundary01 s t) (core01 s) := by
  intro a b
  cases a <;> cases b <;> unfold ValidCore <;> decide +kernel

theorem core23_valid : ∀ a b, ValidCore (boundary23 a b) (core23 a) := by
  intro a b
  cases a <;> cases b <;> unfold ValidCore <;> decide +kernel

variable {W : Type*} {H : SimpleGraph W}
  (C : H.Coloring Color) (ports : Fin 11 → W)
  (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
    H.Adj (ports i) (ports j))
  (initial : ∀ i, C (ports i) = input i)

include embedding initial in
theorem repair01 (s : Bool)
    (K : (C.bicoloredSubgraph c0 c1).ConnectedComponent)
    (root : ports (chosen s) ∈ C.kempeComponentSet c0 c1 K)
    (avoid1 : ports 1 ∉ C.kempeComponentSet c0 c1 K)
    (avoidOther : ports (other s) ∉ C.kempeComponentSet c0 c1 K) :
    ∃ D : H.Coloring Color, ∃ h : History C D, h.length = 1 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (port i) = D (ports i) := by
  classical
  have avoid0 : ports 0 ∉ C.kempeComponentSet c0 c1 K := fun h =>
    avoid1 (C.mem_kempeComponentSet_of_adj h (embedding 0 1 (by decide +kernel))
      (Or.inr (initial 1)))
  have avoid10 : ports 10 ∉ C.kempeComponentSet c0 c1 K := fun h =>
    avoid0 (C.mem_kempeComponentSet_of_adj h (embedding 10 0 (by decide +kernel))
      (Or.inl (initial 0)))
  have inactive (i : Fin 11) (hi : input i ≠ c0 ∧ input i ≠ c1) :
      ports i ∉ C.kempeComponentSet c0 c1 K := by
    intro h
    have active := C.mem_bicoloredSet_of_mem_kempeComponentSet h
    rw [initial] at active
    exact active.elim hi.1 hi.2
  let t := decide (ports 3 ∈ C.kempeComponentSet c0 c1 K)
  have three : ports 3 ∈ C.kempeComponentSet c0 c1 K ↔ t = true := by simp [t]
  have members : ∀ i, ports i ∈ C.kempeComponentSet c0 c1 K ↔ mask01 s t i := by
    cases s <;> simp only [chosen,other,Bool.false_eq_true,ite_false,ite_true] at root avoidOther
    all_goals
      intro i
      fin_cases i <;> first
        | simpa [mask01,chosen] using avoid0
        | simpa [mask01,chosen] using avoid1
        | simpa [mask01,chosen] using avoid10
        | simpa [mask01,chosen] using root
        | simpa [mask01,chosen] using avoidOther
        | simpa [mask01,chosen] using three
        | simpa [mask01,chosen] using inactive 2 (by decide)
        | simpa [mask01,chosen] using inactive 4 (by decide)
        | simpa [mask01,chosen] using inactive 5 (by decide)
        | simpa [mask01,chosen] using inactive 7 (by decide)
        | simpa [mask01,chosen] using inactive 9 (by decide)
  let D := C.swapOnKempeComponent c0 c1 K
  have values (i : Fin 11) : D (ports i) = boundary01 s t i := by
    change (if ports i ∈ C.kempeComponentSet c0 c1 K then
      Equiv.swap c0 c1 (C (ports i)) else C (ports i)) = _
    simp only [members,initial,boundary01]
  have actual : ValidCore (fun i => D (ports i)) (core01 s) := by
    simpa only [values] using core01_valid s t
  let k := colouring (fun i => D (ports i)) _
    (fun i j h => D.valid (embedding i j h)) actual
  exact ⟨D,.cons (.switch C c0 c1 K) (.refl D),rfl,k,
    fun i => colour_port (fun j => D (ports j)) _ i⟩

include embedding initial in
theorem repair23
    (K : (C.bicoloredSubgraph c2 c3).ConnectedComponent)
    (root : ports 7 ∈ C.kempeComponentSet c2 c3 K)
    (avoid9 : ports 9 ∉ C.kempeComponentSet c2 c3 K) :
    ∃ D : H.Coloring Color, ∃ h : History C D, h.length = 1 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (port i) = D (ports i) := by
  classical
  have linked : ports 4 ∈ C.kempeComponentSet c2 c3 K ↔
      ports 5 ∈ C.kempeComponentSet c2 c3 K :=
    ⟨fun h => C.mem_kempeComponentSet_of_adj h (embedding 4 5 (by decide +kernel))
      (Or.inr (initial 5)),
     fun h => C.mem_kempeComponentSet_of_adj h (embedding 5 4 (by decide +kernel))
      (Or.inl (initial 4))⟩
  have inactive (i : Fin 11) (hi : input i ≠ c2 ∧ input i ≠ c3) :
      ports i ∉ C.kempeComponentSet c2 c3 K := by
    intro h
    have active := C.mem_bicoloredSet_of_mem_kempeComponentSet h
    rw [initial] at active
    exact active.elim hi.1 hi.2
  let a := decide (ports 2 ∈ C.kempeComponentSet c2 c3 K)
  let b := decide (ports 4 ∈ C.kempeComponentSet c2 c3 K)
  have two : ports 2 ∈ C.kempeComponentSet c2 c3 K ↔ a = true := by simp [a]
  have four : ports 4 ∈ C.kempeComponentSet c2 c3 K ↔ b = true := by simp [b]
  have members : ∀ i, ports i ∈ C.kempeComponentSet c2 c3 K ↔ mask23 a b i := by
    intro i
    fin_cases i <;> simp [mask23,root,avoid9,← two,← four,← linked,
      inactive 0 (by decide),inactive 1 (by decide),inactive 3 (by decide),
      inactive 6 (by decide),inactive 8 (by decide),inactive 10 (by decide)]
  let D := C.swapOnKempeComponent c2 c3 K
  have values (i : Fin 11) : D (ports i) = boundary23 a b i := by
    change (if ports i ∈ C.kempeComponentSet c2 c3 K then
      Equiv.swap c2 c3 (C (ports i)) else C (ports i)) = _
    simp only [members,initial,boundary23]
  have actual : ValidCore (fun i => D (ports i)) (core23 a) := by
    simpa only [values] using core23_valid a b
  let k := colouring (fun i => D (ports i)) _
    (fun i j h => D.valid (embedding i j h)) actual
  exact ⟨D,.cons (.switch C c2 c3 K) (.refl D),rfl,k,
    fun i => colour_port (fun j => D (ports j)) _ i⟩

end FourColor.StripComplementaryRepair

namespace FourColor.StripComplementaryGeometry

open SimpleGraph Color Mettapedia.GraphTheory.FourColor
open GoertzelV24FaceOrbitIncidence GoertzelV24FaceDualConnectedness
open SimpleGraphDartRotation StripSixBarrierGeometry
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate
noncomputable section

variable {V W : Type*} [Fintype V] [DecidableEq V]
  {G : SimpleGraph V} [DecidableRel G.Adj] {H : SimpleGraph W} {data : Data G}

/-- Geometry supplies one of the complementary repair choices. No separation
of actual Kempe components is an input hypothesis. -/
theorem repair (s : StripSixBarrierGeometry.Patch data) (sides : EarSides s)
    (rotation : VertexRotationCyclic data.toRotationSystem)
    (dual : (interiorDualGraph (orbitFaceBoundary data.toRotationSystem)
      (Finset.univ : Finset (OrbitFace data.toRotationSystem))).Connected)
    (connected : G.Connected)
    (euler : (Fintype.card V : Int) - Fintype.card G.edgeSet +
      Fintype.card (OrbitFace data.toRotationSystem) = 2)
    (e : ExteriorReading s H) (C : H.Coloring Color)
    (initial : ∀ i, C (e.ports i) = StripComplementaryRepair.input i) :
    ∃ D : H.Coloring Color, ∃ h : History C D, h.length = 1 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (StripResponseSummary.port i) = D (e.ports i) := by
  classical
  let K := (C.bicoloredSubgraph c0 c1).connectedComponentMk
    ⟨e.ports 6,Or.inr (initial 6)⟩
  have m6 : e.ports 6 ∈ C.kempeComponentSet c0 c1 K := C.mem_kempeComponentSet_self _
  by_cases m8 : e.ports 8 ∈ C.kempeComponentSet c0 c1 K
  · let L := (C.bicoloredSubgraph c2 c3).connectedComponentMk
      ⟨e.ports 7,Or.inl (initial 7)⟩
    have m7 : e.ports 7 ∈ C.kempeComponentSet c2 c3 L := C.mem_kempeComponentSet_self _
    exact StripComplementaryRepair.repair23 C e.ports e.port_adj initial L m7
      (complementary_separation s sides rotation dual connected euler e C K m6 m8 L m7)
  · by_cases m1 : e.ports 1 ∈ C.kempeComponentSet c0 c1 K
    · let L := (C.bicoloredSubgraph c0 c1).connectedComponentMk
        ⟨e.ports 8,Or.inr (initial 8)⟩
      have m8L : e.ports 8 ∈ C.kempeComponentSet c0 c1 L := C.mem_kempeComponentSet_self _
      have apart {v : W} (hv : v ∈ C.kempeComponentSet c0 c1 K) :
          v ∉ C.kempeComponentSet c0 c1 L := by
        intro hL
        have same : K = L := hv.choose_spec.symm.trans hL.choose_spec
        exact m8 (same.symm ▸ m8L)
      exact StripComplementaryRepair.repair01 C e.ports e.port_adj initial true L
        m8L (apart m1) (apart m6)
    · exact StripComplementaryRepair.repair01 C e.ports e.port_adj initial false K m6 m1 m8

end
end FourColor.StripComplementaryGeometry
