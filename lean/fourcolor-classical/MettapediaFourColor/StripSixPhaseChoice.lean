import MettapediaFourColor.StripSixBarrierRepair
import Mettapedia.GraphTheory.Kempe.PhaseBoundary

/-!
# Exact repair criterion for a fixed-pair phase

After the first switch, a one/three phase repairs the D0099 boundary exactly
when one of its two central components avoids the outer ports. In that case
one physical component switch suffices, regardless of exterior or phase size.
-/

namespace FourColor.StripSixPhaseChoice

set_option maxRecDepth 10000

open SimpleGraph Color StripResponseSummary StripSourceExtension
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

def mask (a b c d : Bool) : Fin 11 → Bool :=
  ![false,a,false,b,false,c,c,false,false,d,d]
def boundary (a b c d : Bool) (i : Fin 11) : Color :=
  if mask a b c d i then Equiv.swap c1 c3 (StripSixBarrierRepair.middle i)
  else StripSixBarrierRepair.middle i

def Good (a b c d : Bool) : Prop := a = d ∧ (b ≠ a ∨ c ≠ a)
instance (a b c d : Bool) : Decidable (Good a b c d) := by unfold Good; infer_instance

def coreColour (a b c : Bool) (i : Fin 8) : Color :=
  let x := b != a
  let y := c != a
  let f : Fin 8 → Color :=
    ![if x && !y then c3 else c1,
      if x then (if y then c2 else c1) else c3,
      if x then c3 else c1,c0,if x && y then c1 else c2,c2,c0,c3]
  if a then Equiv.swap c1 c3 (f i) else f i

theorem core_valid : ∀ a b c d, Good a b c d →
    ValidCore (boundary a b c d) (coreColour a b c) := by
  intro a b c d h
  cases a <;> cases b <;> cases c <;> cases d <;> simp_all [Good]
  all_goals unfold ValidCore; decide +kernel

theorem terminal_necessary : ∀ a b c d, (∃ x y, r5 (boundary a b c d) x y) →
    Good a b c d := by decide +kernel

def outer : List (Fin 11) := [1,9,10]

theorem changed_iff : ∀ a b c d i,
    (StripSixBarrierRepair.middle i = c1 ∨ StripSixBarrierRepair.middle i = c3) →
    (boundary a b c d i ≠ StripSixBarrierRepair.middle i ↔ mask a b c d i = true) := by
  decide +kernel

theorem good_witness : ∀ a b c d, Good a b c d →
    ∃ r : Fin 11, (r = 3 ∨ r = 6) ∧ ∀ o ∈ outer,
      mask a b c d r ≠ mask a b c d o := by decide +kernel

variable {W : Type*} {H : SimpleGraph W}

theorem normal_form (C D : H.Coloring Color) (ports : Fin 11 → W)
    (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
      H.Adj (ports i) (ports j))
    (initial : ∀ i, C (ports i) = StripSixBarrierRepair.middle i)
    (pair : ∀ v, D v = C v ∨ D v = Equiv.swap c1 c3 (C v)) :
    ∃ a b c d, ∀ i, D (ports i) = boundary a b c d i := by
  classical
  let changed (i : Fin 11) := decide (D (ports i) ≠ C (ports i))
  have value (i : Fin 11) : D (ports i) =
      if changed i then Equiv.swap c1 c3 (C (ports i)) else C (ports i) := by
    by_cases h : D (ports i) = C (ports i)
    · simp [changed,h]
    · simpa [changed,h] using (pair (ports i)).resolve_left h
  have linked (i j : Fin 11) (edge : H.Adj (ports i) (ports j))
      (ai : C (ports i) = c1 ∨ C (ports i) = c3)
      (aj : C (ports j) = c1 ∨ C (ports j) = c3) : changed i = changed j := by
    by_cases hi : D (ports i) = C (ports i) <;>
      by_cases hj : D (ports j) = C (ports j)
    · simp [changed,hi,hj]
    · exact (C.changed_neighbour_of_pointwise_swap D c1 c3 pair hj edge.symm ai hi).elim
    · exact (C.changed_neighbour_of_pointwise_swap D c1 c3 pair hi edge aj hj).elim
    · simp [changed,hi,hj]
  have h56 := linked 5 6 (embedding 5 6 (by decide +kernel))
    (Or.inr (initial 5)) (Or.inl (initial 6))
  have h910 := linked 9 10 (embedding 9 10 (by decide +kernel))
    (Or.inr (initial 9)) (Or.inl (initial 10))
  refine ⟨changed 1,changed 3,changed 6,changed 10,?_⟩
  intro i
  rw [value,initial]
  have s0 : Equiv.swap c1 c3 (0 : Color) = 0 := by decide +kernel
  have s2 : Equiv.swap c1 c3 c2 = c2 := by decide +kernel
  fin_cases i <;> simp [boundary,mask,StripSixBarrierRepair.middle,h56,h910,s0,s2]

private theorem same_change (C D : H.Coloring Color)
    (pair : ∀ v, D v = C v ∨ D v = Equiv.swap c1 c3 (C v))
    (K : (C.bicoloredSubgraph c1 c3).ConnectedComponent)
    {u v : W} (hu : u ∈ C.kempeComponentSet c1 c3 K)
    (hv : v ∈ C.kempeComponentSet c1 c3 K) :
    D u ≠ C u ↔ D v ≠ C v := by
  have along {x y : W} (hx : x ∈ C.kempeComponentSet c1 c3 K)
      (hy : y ∈ C.kempeComponentSet c1 c3 K) (h : D x ≠ C x) : D y ≠ C y := by
    obtain ⟨active,eq⟩ := hx
    have all := C.component_changed_of_pointwise_swap D c1 c3 pair h active
    rw [eq] at all
    exact all hy
  exact ⟨along hu hv,along hv hu⟩

/-- A free central component is a complete criterion, retaining the actual
component shared by both inner ports when they are connected. -/
def Free (C : H.Coloring Color) (ports : Fin 11 → W) : Prop :=
  ∃ r : Fin 11, (r = 3 ∨ r = 6) ∧
    ∃ K : (C.bicoloredSubgraph c1 c3).ConnectedComponent,
      ports r ∈ C.kempeComponentSet c1 c3 K ∧
      ∀ o ∈ outer, ports o ∉ C.kempeComponentSet c1 c3 K

theorem free_of_phase (C D : H.Coloring Color) (ports : Fin 11 → W)
    (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
      H.Adj (ports i) (ports j))
    (initial : ∀ i, C (ports i) = StripSixBarrierRepair.middle i)
    (pair : ∀ v, D v = C v ∨ D v = Equiv.swap c1 c3 (C v))
    (k : TriangleStripAnchors.input0099.graph.Coloring Color)
    (agree : ∀ i, k (port i) = D (ports i)) : Free C ports := by
  classical
  obtain ⟨a,b,c,d,values⟩ := normal_form C D ports embedding initial pair
  have valid := valid_of_colouring (boundary a b c d) k
    (fun i => (agree i).trans (values i))
  have good := terminal_necessary a b c d ((terminal_iff _).mpr ⟨_,valid⟩)
  obtain ⟨r,central,separate⟩ := good_witness a b c d good
  have active : C (ports r) = c1 ∨ C (ports r) = c3 := by
    rcases central with h | h <;> subst r
    · exact Or.inr (initial 3)
    · exact Or.inl (initial 6)
  let K := (C.bicoloredSubgraph c1 c3).connectedComponentMk ⟨ports r,active⟩
  have mr : ports r ∈ C.kempeComponentSet c1 c3 K := C.mem_kempeComponentSet_self active
  refine ⟨r,central,K,mr,?_⟩
  intro o ho member
  have ao : C (ports o) = c1 ∨ C (ports o) = c3 :=
    C.mem_bicoloredSet_of_mem_kempeComponentSet member
  have same := same_change C D pair K mr member
  have change (i : Fin 11) (h : C (ports i) = c1 ∨ C (ports i) = c3) :
      D (ports i) ≠ C (ports i) ↔ mask a b c d i = true := by
    rw [values,initial]
    exact changed_iff a b c d i (by simpa only [initial] using h)
  rw [change r active,change o ao] at same
  have neq := separate o ho
  cases hr : mask a b c d r <;> cases ho : mask a b c d o <;> simp_all

theorem single_repair (C : H.Coloring Color) (ports : Fin 11 → W)
    (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
      H.Adj (ports i) (ports j))
    (initial : ∀ i, C (ports i) = StripSixBarrierRepair.middle i)
    (free : Free C ports) :
    ∃ D : H.Coloring Color, ∃ h : History C D, h.length = 1 ∧
      KempePairHistory.Step c1 c3 C D ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (port i) = D (ports i) := by
  classical
  obtain ⟨r,central,K,mr,avoid⟩ := free
  let D := C.swapOnKempeComponent c1 c3 K
  have pair (v : W) : D v = C v ∨ D v = Equiv.swap c1 c3 (C v) := by
    by_cases h : v ∈ C.kempeComponentSet c1 c3 K
    · exact Or.inr (C.swapOnKempeComponent_apply_of_mem h)
    · exact Or.inl (C.swapOnKempeComponent_apply_of_not_mem h)
  obtain ⟨a,b,c,d,values⟩ := normal_form C D ports embedding initial pair
  have fixed1 : boundary a b c d 1 = StripSixBarrierRepair.middle 1 :=
    (values 1).symm.trans ((C.swapOnKempeComponent_apply_of_not_mem (avoid 1 (by decide))).trans (initial 1))
  have fixed10 : boundary a b c d 10 = StripSixBarrierRepair.middle 10 :=
    (values 10).symm.trans ((C.swapOnKempeComponent_apply_of_not_mem (avoid 10 (by decide))).trans (initial 10))
  have changed : boundary a b c d r ≠ StripSixBarrierRepair.middle r := by
    rw [← values,← initial]
    change D (ports r) ≠ C (ports r)
    rw [C.swapOnKempeComponent_apply_of_mem mr]
    rcases central with h | h <;> subst r <;> rw [initial] <;> decide
  have good : Good a b c d := by
    rcases central with h | h <;> subst r <;>
      cases a <;> cases b <;> cases c <;> cases d <;>
      simp_all [Good,boundary,mask,StripSixBarrierRepair.middle,Equiv.swap_apply_def]
  have core : ValidCore (fun i => D (ports i)) (coreColour a b c) := by
    simpa only [values] using core_valid a b c d good
  let k := colouring (fun i => D (ports i)) _
    (fun i j h => D.valid (embedding i j h)) core
  exact ⟨D,.cons (.switch C c1 c3 K) (.refl D),rfl,⟨K,rfl⟩,
    k,fun i => colour_port (fun j => D (ports j)) _ i⟩

/-- Any successful phase of this pair can be replaced by one actual
component switch. Its resulting colouring need not equal the old endpoint. -/
theorem compress_phase (C D : H.Coloring Color) (ports : Fin 11 → W)
    (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
      H.Adj (ports i) (ports j))
    (initial : ∀ i, C (ports i) = StripSixBarrierRepair.middle i)
    (phase : Relation.ReflTransGen (KempePairHistory.Step c1 c3) C D)
    (k : TriangleStripAnchors.input0099.graph.Coloring Color)
    (agree : ∀ i, k (port i) = D (ports i)) :
    ∃ E : H.Coloring Color, ∃ h : History C E, h.length = 1 ∧
      KempePairHistory.Step c1 c3 C E ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (port i) = E (ports i) :=
  single_repair C ports embedding initial
    (free_of_phase C D ports embedding initial (KempePairHistory.pointwise phase) k agree)

theorem phase_iff_free (C : H.Coloring Color) (ports : Fin 11 → W)
    (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
      H.Adj (ports i) (ports j))
    (initial : ∀ i, C (ports i) = StripSixBarrierRepair.middle i) :
    (∃ D : H.Coloring Color,
      Relation.ReflTransGen (KempePairHistory.Step c1 c3) C D ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (port i) = D (ports i)) ↔ Free C ports := by
  constructor
  · rintro ⟨D,phase,k,agree⟩
    exact free_of_phase C D ports embedding initial (KempePairHistory.pointwise phase) k agree
  · intro free
    obtain ⟨D,_,_,step,k,agree⟩ := single_repair C ports embedding initial free
    exact ⟨D,.single step,k,agree⟩

end FourColor.StripSixPhaseChoice
