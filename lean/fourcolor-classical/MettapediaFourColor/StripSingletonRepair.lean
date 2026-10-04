import MettapediaFourColor.StripSourceExtension
import Mettapedia.GraphTheory.Kempe.SingletonRelease

/-!
# A two-stage D0099 repair over arbitrary exteriors

One a/b component joins ports zero, one, two and ten. If it avoids the
three retained ports five, six and eight, and colour c is absent around
port one, its switch permits a singleton second switch. Local colour
lists then supply one common core witness for the entire boundary domain.
No table of whole boundary colourings or repair histories is used.

The failed separation branch retains an actual two-colour connection to
one of those three ports. Its exclusion or alternative repair is open.
-/

namespace FourColor.StripSingletonRepair

open SimpleGraph Color StripResponseSummary StripSourceExtension
open Mettapedia.GraphTheory.FourColor.KempeChainCertificate

def before : Fin 11 → Finset Color :=
  ![{c0},{c1},{c0},{c2,c3},{c2,c3},{c1,c2,c3},{c1,c2},
    {c0,c1,c2},{c1},{c3},{c1}]
def after : Fin 11 → Finset Color :=
  ![{c1},{c2},{c1},{c2,c3},{c2,c3},{c1,c2,c3},{c1,c2},
    {c0,c1,c2},{c1},{c3},{c0}]
def moves : List (Fin 11) := [0,2,10]
def retainedPorts : List (Fin 11) := [5,6,8]
def coreColour : Fin 8 → Color := ![c3,c2,c1,c0,c0,c0,c2,c3]

theorem list_step : ∀ (i : Fin 11) (x : Color) (moving : Bool),
    i ≠ 1 → x ∈ before i → (i ∈ moves → moving = true) →
    (i ∈ retainedPorts → moving = false) →
    (if moving then Equiv.swap c0 c1 x else x) ∈ after i := by decide +kernel

theorem core_edges : ∀ e ∈ edges, coreColour e.1 ≠ coreColour e.2 := by decide +kernel
theorem core_lists : ∀ v i, i ∈ attachments v →
    ∀ x ∈ after i, coreColour v ≠ x := by decide +kernel

theorem core_valid (b : Boundary) (fits : ∀ i, b i ∈ after i) : ValidCore b coreColour :=
  ⟨fun v i hi => core_lists v i hi _ (fits i),core_edges⟩

variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]
  (C : G.Coloring Color) (ports : Fin 11 → V)
  (K : (C.bicoloredSubgraph c0 c1).ConnectedComponent)
  (initial : ∀ i, C (ports i) ∈ before i)
  (member : ports 1 ∈ C.kempeComponentSet c0 c1 K)
  (missing : ∀ y, G.Adj (ports 1) y → C y ≠ c2)

include initial in
omit [DecidableEq V] in
theorem root_colour : C (ports 1) = c1 := by simpa [before] using initial 1

noncomputable def released : G.Coloring Color :=
  (KempeSingletonRelease.second C c0 c1 c2 K (ports 1)
    (root_colour C ports initial) member (by decide) (by decide) missing).swap

noncomputable def history : History C (released C ports K initial member missing) :=
  KempeSingletonRelease.history C c0 c1 c2 K (ports 1)
    (root_colour C ports initial) member (by decide) (by decide) missing

omit [DecidableEq V] in
theorem history_length : (history C ports K initial member missing).length = 2 := rfl

theorem released_apply (x : V) : released C ports K initial member missing x =
    if x = ports 1 then c2 else (C.swapOnKempeComponent c0 c1 K) x :=
  KempeSingletonRelease.endpoint C c0 c1 c2 K (ports 1)
    (root_colour C ports initial) member (by decide) (by decide) missing x

variable (embedding : ∀ i j,
  TriangleStripAnchors.input0099.graph.Adj (port i) (port j) → G.Adj (ports i) (ports j))

include initial member embedding in
omit [DecidableEq V] in
theorem forced (i : Fin 11) (hi : i ∈ moves) :
    ports i ∈ C.kempeComponentSet c0 c1 K := by
  have h0 : C (ports 0) = c0 := by simpa [before] using initial 0
  have h2 : C (ports 2) = c0 := by simpa [before] using initial 2
  have h10 : C (ports 10) = c1 := by simpa [before] using initial 10
  have m0 := C.mem_kempeComponentSet_of_adj member
    (embedding 1 0 (by decide +kernel)) (Or.inl h0)
  have m2 := C.mem_kempeComponentSet_of_adj member
    (embedding 1 2 (by decide +kernel)) (Or.inl h2)
  have m10 := C.mem_kempeComponentSet_of_adj m0
    (embedding 0 10 (by decide +kernel)) (Or.inr h10)
  simp only [moves,List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl | rfl | rfl
  · exact m0
  · exact m2
  · exact m10

variable (injective : Function.Injective ports)
  (separated : ∀ i ∈ retainedPorts, ports i ∉ C.kempeComponentSet c0 c1 K)

include embedding injective separated in
omit [DecidableEq V] in
theorem after_lists : ∀ i, released C ports K initial member missing (ports i) ∈ after i := by
  classical
  intro i
  by_cases hi : i = 1
  · subst i
    simp only [released_apply,ite_true]
    simp [after]
  · have ne : ports i ≠ ports 1 := fun h => hi (injective h)
    rw [released_apply,ite_eq_right ne]
    by_cases hm : ports i ∈ C.kempeComponentSet c0 c1 K
    · rw [C.swapOnKempeComponent_apply_of_mem hm]
      exact list_step i _ true hi (initial i) (fun _ => rfl)
        (fun hp => (separated i hp hm).elim)
    · rw [C.swapOnKempeComponent_apply_of_not_mem hm]
      exact list_step i _ false hi (initial i)
        (fun hp => (hm (forced C ports K initial member embedding i hp)).elim) (fun _ => rfl)

include embedding injective separated in
omit [DecidableEq V] in
/-- The same core witness reconstructs for every boundary in the stated domain. -/
theorem source : ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
    ∀ i, k (port i) = released C ports K initial member missing (ports i) := by
  classical
  let D := released C ports K initial member missing
  have fit := after_lists C ports K initial member missing embedding injective separated
  have proper : ProperBoundary (fun i => D (ports i)) :=
    fun i j edge => D.valid (embedding i j edge)
  refine ⟨colouring _ coreColour proper (core_valid _ fit),?_⟩
  intro i
  change completeColour (fun j => D (ports j)) coreColour (port i) = D (ports i)
  exact colour_port (fun j => D (ports j)) coreColour i

include initial member missing embedding injective separated in
omit [DecidableEq V] in
theorem repair : ∃ D : G.Coloring Color, ∃ h : History C D, h.length = 2 ∧
    ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color, ∀ i, k (port i) = D (ports i) := by
  classical
  exact ⟨released C ports K initial member missing,history C ports K initial member missing,rfl,
    source C ports K initial member missing embedding injective separated⟩

include initial member missing embedding injective in
omit [DecidableEq V] in
/-- Failure of this repair guard retains an actual two-colour connection. -/
theorem repair_or_connection :
    (∃ D : G.Coloring Color, ∃ h : History C D, h.length = 2 ∧
      ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color, ∀ i, k (port i) = D (ports i)) ∨
    ∃ i ∈ retainedPorts, ports i ∈ C.kempeComponentSet c0 c1 K := by
  classical
  by_cases hs : ∀ i ∈ retainedPorts, ports i ∉ C.kempeComponentSet c0 c1 K
  · exact Or.inl (repair C ports K initial member missing embedding injective hs)
  · exact Or.inr (by simpa only [not_forall,not_not,exists_prop] using hs)

include initial member in
omit [DecidableEq V] in
/-- The retained connection supplies a walk in the actual two-colour graph. -/
theorem connection_walk (i : Fin 11) (hit : ports i ∈ C.kempeComponentSet c0 c1 K) :
    ∃ hi : C (ports i) = c0 ∨ C (ports i) = c1,
      Nonempty ((C.bicoloredSubgraph c0 c1).Walk
        ⟨ports 1,Or.inr (root_colour C ports initial)⟩ ⟨ports i,hi⟩) := by
  obtain ⟨active,heq⟩ := hit
  obtain ⟨_,hroot⟩ := member
  exact ⟨active,ConnectedComponent.exact (hroot.trans heq.symm)⟩

end FourColor.StripSingletonRepair
