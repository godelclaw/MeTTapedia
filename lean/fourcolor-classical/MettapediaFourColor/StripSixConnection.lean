import MettapediaFourColor.StripSingletonRim

/-!
# Direct repair or a joint connection in the port-six branch

The failed zero/one separation guard forces one of two boundary forms.
For both forms, switching the zero/two component at port seven gives an
explicit core colouring unless that same component contains two marked
ports. The two connections are retained jointly in the actual exterior.
The arbitrary exterior size and component size are not bounded.
-/

namespace FourColor.StripSixConnection

open SimpleGraph Color StripResponseSummary StripSourceExtension
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

def input (s : Bool) : Boundary :=
  ![c0,c1,c0,if s then c3 else c2,if s then c2 else c3,
    if s then c3 else c2,c1,c2,c1,c3,c1]
def anchor (s : Bool) : Fin 11 := if s then 2 else 0
def middle (s : Bool) : Fin 11 := if s then 4 else 5
def freePort (s : Bool) : Fin 11 := if s then 0 else 2

def mask (s x y z : Bool) : Fin 11 → Bool :=
  if s then ![z,false,x,false,y,false,false,true,false,false,false]
  else ![x,false,z,z,false,y,false,true,false,false,false]
def boundary (s x y z : Bool) (i : Fin 11) : Color :=
  if mask s x y z i then Equiv.swap c0 c2 (input s i) else input s i

def coreColour (s x y : Bool) : Fin 8 → Color :=
  ![if x || y then c3 else c2,if x then c2 else if y then c0 else c3,
    c1,if y then c2 else c0,if x then c0 else c2,
    if s then (if x then c0 else c2) else c3,
    if x then c2 else c0,if s then c3 else (if x then c0 else c2)]

theorem core_edges : ∀ s x y, (x && y) = false → ∀ e ∈ edges,
    coreColour s x y e.1 ≠ coreColour s x y e.2 := by decide +kernel
theorem core_lists : ∀ s x y z, (x && y) = false → ∀ v i, i ∈ attachments v →
    coreColour s x y v ≠ boundary s x y z i := by decide +kernel

theorem core_valid (s x y z : Bool) (guard : (x && y) = false) :
    ValidCore (boundary s x y z) (coreColour s x y) :=
  ⟨fun v i hi => core_lists s x y z guard v i hi,core_edges s x y guard⟩

theorem local_form : ∀ (s : Bool) (a b c : Color),
    a = (if s then c3 else c2) → b ∈ ({c2,c3} : Finset Color) →
    c ∈ ({c1,c2,c3} : Finset Color) → a ≠ b → b ≠ c → c ≠ c1 →
    b = (if s then c2 else c3) ∧ c = (if s then c3 else c2) := by decide +kernel

/-- Boundary incidences determine the complete component footprint from
three bits. No table of colourings or component partitions is used. -/
theorem mask_exact (s : Bool) (bits : Fin 11 → Bool)
    (inactive : ∀ i, input s i ≠ c0 → input s i ≠ c2 → bits i = false)
    (at7 : bits 7 = true) (at23 : s = false → bits 2 = bits 3) :
    bits = mask s (bits (anchor s)) (bits (middle s)) (bits (freePort s)) := by
  have h1 := inactive 1 (by cases s <;> decide) (by cases s <;> decide)
  have h6 := inactive 6 (by cases s <;> decide) (by cases s <;> decide)
  have h8 := inactive 8 (by cases s <;> decide) (by cases s <;> decide)
  have h9 := inactive 9 (by cases s <;> decide) (by cases s <;> decide)
  have h10 := inactive 10 (by cases s <;> decide) (by cases s <;> decide)
  cases s with
  | false =>
    have h4 := inactive 4 (by decide) (by decide)
    have h23 := at23 rfl
    funext i
    fin_cases i <;> simp [mask,anchor,middle,freePort,h1,h4,h6,h8,h9,h10,at7,h23]
  | true =>
    have h3 := inactive 3 (by decide) (by decide)
    have h5 := inactive 5 (by decide) (by decide)
    funext i
    fin_cases i <;> simp [mask,anchor,middle,freePort,h1,h3,h5,h6,h8,h9,h10,at7]

variable {V : Type*} {G : SimpleGraph V}
  (C : G.Coloring Color) (ports : Fin 11 → V)
  (embedding : ∀ i j, TriangleStripAnchors.input0099.graph.Adj (port i) (port j) →
    G.Adj (ports i) (ports j))

include embedding

/-- Every actual component switch in the permitted branch uses the same
core formula; all exterior colouring constraints are preserved. -/
theorem direct (s : Bool) (initial : ∀ i, C (ports i) = input s i)
    (K : (C.bicoloredSubgraph c0 c2).ConnectedComponent)
    (m7 : ports 7 ∈ C.kempeComponentSet c0 c2 K)
    (guard : ¬ (ports (anchor s) ∈ C.kempeComponentSet c0 c2 K ∧
      ports (middle s) ∈ C.kempeComponentSet c0 c2 K)) :
    ∃ D : G.Coloring Color, ∃ h : History C D, h.length = 1 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (port i) = D (ports i) := by
  classical
  let bits (i : Fin 11) : Bool := decide (ports i ∈ C.kempeComponentSet c0 c2 K)
  have inactive (i : Fin 11) (h0 : input s i ≠ c0) (h2 : input s i ≠ c2) :
      bits i = false := by
    apply decide_eq_false
    intro h
    have active := C.mem_bicoloredSet_of_mem_kempeComponentSet h
    rw [initial] at active
    exact active.elim h0 h2
  have at7 : bits 7 = true := decide_eq_true m7
  have at23 : s = false → bits 2 = bits 3 := by
    intro hs; subst s
    have h2 : C (ports 2) = c0 := initial 2
    have h3 : C (ports 3) = c2 := initial 3
    have edge := embedding 2 3 (by decide +kernel)
    by_cases m2 : ports 2 ∈ C.kempeComponentSet c0 c2 K
    · have m3 := C.mem_kempeComponentSet_of_adj m2 edge (Or.inr h3)
      exact (decide_eq_true m2).trans (decide_eq_true m3).symm
    · have m3 : ports 3 ∉ C.kempeComponentSet c0 c2 K :=
        fun h => m2 (C.mem_kempeComponentSet_of_adj h edge.symm (Or.inl h2))
      exact (decide_eq_false m2).trans (decide_eq_false m3).symm
  have hm := mask_exact s bits inactive at7 at23
  let D := C.swapOnKempeComponent c0 c2 K
  have end_values (i : Fin 11) : D (ports i) =
      boundary s (bits (anchor s)) (bits (middle s)) (bits (freePort s)) i := by
    change (if ports i ∈ C.kempeComponentSet c0 c2 K then
      Equiv.swap c0 c2 (C (ports i)) else C (ports i)) = _
    rw [initial]
    have eq := congrFun hm i
    simp only [boundary,← eq,bits,decide_eq_true_eq]
  have good : (bits (anchor s) && bits (middle s)) = false := by
    simpa [bits] using guard
  have valid := core_valid s (bits (anchor s)) (bits (middle s)) (bits (freePort s)) good
  have actual : ValidCore (fun i => D (ports i))
      (coreColour s (bits (anchor s)) (bits (middle s))) := by
    simpa only [end_values] using valid
  let k := colouring (fun i => D (ports i)) _
    (fun i j edge => D.valid (embedding i j edge)) actual
  refine ⟨D,.cons (.switch C c0 c2 K) (.refl D),rfl,k,?_⟩
  intro i
  change completeColour (fun j => D (ports j)) _ (port i) = _
  exact colour_port _ _ i

/-- Failure to supply this direct repair retains both marked ports in one
actual component, not two independent possible connections. -/
theorem repair_or_joint (s : Bool) (initial : ∀ i, C (ports i) = input s i) :
    (∃ D : G.Coloring Color, ∃ h : History C D, h.length = 1 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
        ∀ i, k (port i) = D (ports i)) ∨
    ∃ K : (C.bicoloredSubgraph c0 c2).ConnectedComponent,
      ports 7 ∈ C.kempeComponentSet c0 c2 K ∧
      ports (anchor s) ∈ C.kempeComponentSet c0 c2 K ∧
      ports (middle s) ∈ C.kempeComponentSet c0 c2 K := by
  classical
  have c7 : C (ports 7) = c2 := by simpa [input] using initial 7
  let K := (C.bicoloredSubgraph c0 c2).connectedComponentMk ⟨ports 7,Or.inr c7⟩
  have m7 : ports 7 ∈ C.kempeComponentSet c0 c2 K :=
    C.mem_kempeComponentSet_self (Or.inr c7)
  by_cases both : ports (anchor s) ∈ C.kempeComponentSet c0 c2 K ∧
      ports (middle s) ∈ C.kempeComponentSet c0 c2 K
  · exact Or.inr ⟨K,m7,both⟩
  · exact Or.inl (direct C ports embedding s initial K m7 both)

/-- The original component hitting port six but missing port eight forces
one of the two inputs; the forms are derived from proper rim edges. -/
theorem classified
    (initial : ∀ i, C (ports i) ∈ StripSingletonRepair.before i)
    (K : (C.bicoloredSubgraph c0 c1).ConnectedComponent)
    (m6 : ports 6 ∈ C.kempeComponentSet c0 c1 K)
    (n8 : ports 8 ∉ C.kempeComponentSet c0 c1 K) :
    ∃ s : Bool, ∀ i, C (ports i) = input s i := by
  have a6 := C.mem_bicoloredSet_of_mem_kempeComponentSet m6
  have l6 : C (ports 6) = c1 ∨ C (ports 6) = c2 := by
    simpa [StripSingletonRepair.before] using initial 6
  have h6 : C (ports 6) = c1 := by
    rcases l6 with h | h
    · exact h
    · rcases a6 with a | a <;> simp_all
  have h8 : C (ports 8) = c1 := by
    simpa [StripSingletonRepair.before] using initial 8
  have l7 : C (ports 7) = c0 ∨ C (ports 7) = c1 ∨ C (ports 7) = c2 := by
    simpa [StripSingletonRepair.before] using initial 7
  have h7 : C (ports 7) = c2 := by
    rcases l7 with h | h | h
    · have m7 := C.mem_kempeComponentSet_of_adj m6
        (embedding 6 7 (by decide +kernel)) (Or.inl h)
      exact (n8 (C.mem_kempeComponentSet_of_adj m7
        (embedding 7 8 (by decide +kernel)) (Or.inr h8))).elim
    · exact (C.valid (embedding 6 7 (by decide +kernel)) (h6.trans h.symm)).elim
    · exact h
  have l3 : C (ports 3) = c2 ∨ C (ports 3) = c3 := by
    simpa [StripSingletonRepair.before] using initial 3
  obtain ⟨s,hs⟩ : ∃ s : Bool, C (ports 3) = (if s then c3 else c2) := by
    rcases l3 with h | h
    · exact ⟨false,h⟩
    · exact ⟨true,h⟩
  have l4 : C (ports 4) ∈ ({c2,c3} : Finset Color) := by
    simpa [StripSingletonRepair.before] using initial 4
  have l5 : C (ports 5) ∈ ({c1,c2,c3} : Finset Color) := by
    simpa [StripSingletonRepair.before] using initial 5
  have h45 := local_form s _ _ _ hs l4 l5
    (C.valid (embedding 3 4 (by decide +kernel)))
    (C.valid (embedding 4 5 (by decide +kernel)))
    (fun h => C.valid (embedding 5 6 (by decide +kernel)) (h.trans h6.symm))
  refine ⟨s,fun i => ?_⟩
  fin_cases i
  · simpa [input,StripSingletonRepair.before] using initial 0
  · simpa [input,StripSingletonRepair.before] using initial 1
  · simpa [input,StripSingletonRepair.before] using initial 2
  · simpa [input] using hs
  · simpa [input] using h45.1
  · simpa [input] using h45.2
  · simpa [input] using h6
  · simpa [input] using h7
  · simpa [input] using h8
  · simpa [input,StripSingletonRepair.before] using initial 9
  · simpa [input,StripSingletonRepair.before] using initial 10

/-- An actual failure of the first separation test supplies the direct
repair or two marked connections in the same complementary component. -/
theorem of_port_six
    (initial : ∀ i, C (ports i) ∈ StripSingletonRepair.before i)
    (K : (C.bicoloredSubgraph c0 c1).ConnectedComponent)
    (m6 : ports 6 ∈ C.kempeComponentSet c0 c1 K)
    (n8 : ports 8 ∉ C.kempeComponentSet c0 c1 K) :
    ∃ s : Bool, (∀ i, C (ports i) = input s i) ∧
      ((∃ D : G.Coloring Color, ∃ h : History C D, h.length = 1 ∧
        ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
          ∀ i, k (port i) = D (ports i)) ∨
      ∃ L : (C.bicoloredSubgraph c0 c2).ConnectedComponent,
        ports 7 ∈ C.kempeComponentSet c0 c2 L ∧
        ports (anchor s) ∈ C.kempeComponentSet c0 c2 L ∧
        ports (middle s) ∈ C.kempeComponentSet c0 c2 L) := by
  obtain ⟨s,form⟩ := classified C ports embedding initial K m6 n8
  exact ⟨s,form,repair_or_joint C ports embedding s form⟩

omit embedding in
/-- Both residual connections are walks in the same actual bicoloured
graph, based at the same port and retained before any recolouring. -/
theorem joint_walks (s : Bool)
    (K : (C.bicoloredSubgraph c0 c2).ConnectedComponent)
    (m7 : ports 7 ∈ C.kempeComponentSet c0 c2 K)
    (ma : ports (anchor s) ∈ C.kempeComponentSet c0 c2 K)
    (mm : ports (middle s) ∈ C.kempeComponentSet c0 c2 K) :
    ∃ h7 : C (ports 7) = c0 ∨ C (ports 7) = c2,
    ∃ ha : C (ports (anchor s)) = c0 ∨ C (ports (anchor s)) = c2,
    ∃ hm : C (ports (middle s)) = c0 ∨ C (ports (middle s)) = c2,
      Nonempty ((C.bicoloredSubgraph c0 c2).Walk ⟨ports 7,h7⟩ ⟨ports (anchor s),ha⟩) ∧
      Nonempty ((C.bicoloredSubgraph c0 c2).Walk ⟨ports 7,h7⟩ ⟨ports (middle s),hm⟩) := by
  obtain ⟨h7,e7⟩ := m7
  obtain ⟨ha,ea⟩ := ma
  obtain ⟨hm,em⟩ := mm
  exact ⟨h7,ha,hm,ConnectedComponent.exact (e7.trans ea.symm),
    ConnectedComponent.exact (e7.trans em.symm)⟩

end FourColor.StripSixConnection
