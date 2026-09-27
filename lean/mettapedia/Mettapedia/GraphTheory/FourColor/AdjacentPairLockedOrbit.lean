import Mettapedia.GraphTheory.FourColor.MatchingCapThreeSwitchGeometry
import Mettapedia.GraphTheory.FourColor.LockedKempeOrbit

/-!
# A trapped Kempe class after deleting an adjacent vertex pair

Delete vertices zero and one from the explicit thirty-vertex spherical
cubic graph. Six representatives and colour permutations describe a family
closed under every physical component switch on the retained graph. Every
member requests the same colour at the two neighbours of vertex zero, so
none extends across the deleted pair, after any finite switch history.

The ambient graph has an explicit proper colouring. Thus the obstruction
concerns arbitrary prescribed starting choices, not existence of a
successful colouring or construction.
-/

namespace Mettapedia.GraphTheory.FourColor.AdjacentPairLockedOrbit

open GoertzelV24ForkInterfaceSupport IncidenceKempeSwitch KempeChainCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 8000000

abbrev Vertex := MatchingCapThreeSwitch.Vertex
abbrev Edge := MatchingCapThreeSwitch.Edge
abbrev inc := MatchingCapThreeSwitch.inc

def old : Finset Edge := Finset.univ \ {0, 1, 2, 3, 4}

/-- These are exactly the original edges avoiding the two deleted vertices. -/
theorem retained_iff (e : Edge) : e ∈ old ↔ (0 : Vertex) ∉ inc e ∧ (1 : Vertex) ∉ inc e := by
  revert e
  decide +kernel

abbrev palette := LockedKempeOrbit.palette

def representative : Fin 6 → Edge → Fin 3 :=
  ![![0,0,0,0,0,0,1,0,1,0,1,1,0,2,2,0,1,2,2,0,1,2,1,0,1,2,0,2,0,1,1,2,0,2,1,0,0,2,1,2,0,1,2,1,0],
    ![0,0,0,0,0,0,1,0,1,0,1,1,0,2,2,0,1,2,2,0,1,2,1,0,2,1,2,0,0,1,1,2,0,1,0,2,0,2,1,2,2,0,1,0,1],
    ![0,0,0,0,0,0,1,0,1,0,2,2,0,1,2,0,1,2,1,0,2,1,2,0,2,1,0,2,0,1,2,1,0,1,2,0,0,1,2,1,0,2,1,2,0],
    ![0,0,0,0,0,0,1,0,1,0,2,2,0,1,2,0,1,2,1,0,2,1,2,0,2,1,2,0,0,1,2,1,0,1,0,2,0,1,2,1,2,0,1,0,2],
    ![0,0,0,0,0,0,1,0,1,2,1,1,2,2,2,0,1,0,0,2,1,0,1,0,1,2,0,2,2,1,1,0,2,2,1,0,2,0,1,0,0,1,2,1,2],
    ![0,0,0,0,0,0,1,0,1,2,1,1,2,2,2,0,1,0,0,2,1,0,1,0,2,1,0,2,2,1,1,0,2,1,2,0,2,0,1,0,0,2,1,2,1]]

def assignment (t p : Fin 6) (e : Edge) : Fin 3 := palette p (representative t e)

theorem assignment_proper (t p : Fin 6) : Proper inc old (assignment t p) := by
  revert t p
  decide +kernel

def base : (graph inc old).Coloring (Fin 3) :=
  colouring inc old (assignment 0 0) (assignment_proper 0 0)

/-- Unretained edge identifiers are isolated and their colours are irrelevant. -/
def Locked (C : (graph inc old).Coloring (Fin 3)) : Prop :=
  ∃ t p, ∀ e ∈ old, C e = assignment t p e

theorem base_locked : Locked base := ⟨0, 0, fun _ _ => rfl⟩

private def channel00 : Fin 6 → List Edge :=
  ![[5,6,15,24,23,22,32,38,36,30,28,29,35,43,44,41,40,34,26,16,7,8,9,10,19,20,12,11],
    [5,6,15,25,34,42,43,44,41,33,23,22,32,38,36,30,28,29,27,16,7,8,9,10,19,20,12,11],
    [9,8,7,16,26,25,15,6,5,13,23,33,40,42,35,29,28,18,19,31,36,37,44,39,32,21,12],
    [9,8,7,16,27,29,28,18,19,31,36,37,43,42,34,25,15,6,5,13,23,33,41,39,32,21,12],
    [10,18,30,37,43,35,29,17,8,7,16,26,34,40,41,39,38,31,20,21,22,23,24,15,6,5,11],
    [10,18,30,37,44,39,38,31,20,21,22,23,33,40,42,35,29,17,8,7,16,26,25,15,6,5,11]]

private def channel10 : Fin 6 → List Edge :=
  ![[5,13,23,33,40,42,35,27,26,25,15,14,7],
    [5,13,23,24,15,14,7],
    [5,11,12,20,19,10,9,17,28,30,36,38,32,22,23,24,15,14,7],
    [5,11,12,20,19,10,9,17,28,30,36,38,32,22,23,24,15,14,7],
    [5,13,23,33,40,42,35,27,26,25,15,14,7],
    [5,13,23,24,15,14,7]]

private def channel11 : Fin 6 → List Edge :=
  ![[9,17,28,18,19,31,36,37,44,39,32,21,12],
    [9,17,28,18,19,31,36,37,43,35,27,26,34,40,41,39,32,21,12],
    [26,27,35,43,44,41,40,34],
    [26,27,35,43,44,41,40,34],
    [9,17,28,18,19,31,36,37,44,39,32,21,12],
    [9,17,28,18,19,31,36,37,43,35,27,26,34,40,41,39,32,21,12]]

private def channel20 : Fin 6 → List Edge :=
  ![[6,14,16,27,29,17,8],
    [6,14,16,26,25,24,33,40,42,35,29,17,8],
    [6,14,16,27,29,17,8],
    [6,14,16,26,25,24,33,40,42,35,29,17,8],
    [6,14,16,27,29,28,30,36,38,32,22,13,11,12,20,19,10,9,8],
    [6,14,16,27,29,28,30,36,38,32,22,13,11,12,20,19,10,9,8]]

private def channel21 : Fin 6 → List Edge :=
  ![[10,18,30,37,43,42,34,25,24,33,41,39,38,31,20,21,22,13,11],
    [10,18,30,37,44,39,38,31,20,21,22,13,11],
    [10,18,30,37,43,42,34,25,24,33,41,39,38,31,20,21,22,13,11],
    [10,18,30,37,44,39,38,31,20,21,22,13,11],
    [24,25,34,42,43,44,41,33],
    [24,25,34,42,43,44,41,33]]

private def channel (t : Fin 6) : Fin 5 → List Edge :=
  ![channel00 t, channel10 t, channel11 t, channel20 t, channel21 t]

private def pair : Fin 5 → Fin 3 × Fin 3 := ![(0,1), (0,2), (0,2), (1,2), (1,2)]

private theorem palette_injective (p : Fin 6) : Function.Injective (palette p) := by
  revert p
  decide +kernel

set_option synthInstance.maxSize 1024 in
/-- Each physical component is checked once before palette transport. -/
private theorem channel_certificate : ∀ t j,
    (channel t j).IsChain (graph inc old).Adj ∧
      (∀ y ∈ channel t j, y ∈ old ∧
        (representative t y = (pair j).1 ∨ representative t y = (pair j).2)) ∧
      (∀ y ∈ channel t j, ∀ z, (graph inc old).Adj y z →
        (representative t z = (pair j).1 ∨ representative t z = (pair j).2) →
          z ∈ channel t j) := by
  decide +kernel

private theorem channel_coverage : ∀ t p r s x, r ≠ s → x ∈ old →
    (assignment t p x = r ∨ assignment t p x = s) →
    ∃ j, x ∈ channel t j ∧
      ((palette p (pair j).1 = r ∧ palette p (pair j).2 = s) ∨
        (palette p (pair j).1 = s ∧ palette p (pair j).2 = r)) := by
  decide +kernel

private theorem switch_certificate : ∀ t p j,
    ∃ u q, ∀ y ∈ old,
      (if y ∈ channel t j then
        Equiv.swap (palette p (pair j).1) (palette p (pair j).2) (assignment t p y)
       else assignment t p y) =
        assignment u q y := by
  decide +kernel

/-- Closure under every actual component, including isolated unused identifiers. -/
theorem locked_switch (C : (graph inc old).Coloring (Fin 3))
    (r s : Fin 3) (K : (C.bicoloredSubgraph r s).ConnectedComponent)
    (hC : Locked C) : Locked (C.swapOnKempeComponent r s K) := by
  classical
  obtain ⟨t, p, hC⟩ := hC
  by_cases hrs : r = s
  · subst s
    refine ⟨t, p, ?_⟩
    intro y hy
    by_cases hmem : y ∈ C.kempeComponentSet r r K
    · simpa using (C.swapOnKempeComponent_apply_of_mem hmem).trans (by simpa using hC y hy)
    · rw [C.swapOnKempeComponent_apply_of_not_mem hmem]
      exact hC y hy
  by_cases htouch : ∃ x ∈ old, x ∈ C.kempeComponentSet r s K
  · obtain ⟨x, hx, hxK⟩ := htouch
    have ha := C.mem_bicoloredSet_of_mem_kempeComponentSet hxK
    rw [hC x hx] at ha
    obtain ⟨j, hxc, hp⟩ := channel_coverage t p r s x hrs hx ha
    obtain ⟨hc, hca, hcc⟩ := channel_certificate t j
    have active_iff (z : Edge) :
        (assignment t p z = r ∨ assignment t p z = s) ↔
          (representative t z = (pair j).1 ∨ representative t z = (pair j).2) := by
      rcases hp with ⟨hr, hs⟩ | ⟨hs, hr⟩
      · simp only [assignment, ← hr, ← hs, (palette_injective p).eq_iff]
      · simp only [assignment, ← hr, ← hs, (palette_injective p).eq_iff, or_comm]
    have active : ∀ y ∈ channel t j, C y = r ∨ C y = s := by
      intro y hy
      rw [hC y (hca y hy).1]
      exact (active_iff y).mpr (hca y hy).2
    have closed : ∀ y ∈ channel t j, ∀ z,
        (graph inc old).Adj y z → (C z = r ∨ C z = s) → z ∈ channel t j := by
      intro y hy z hyz hz
      rw [hC z hyz.2.2.1] at hz
      exact hcc y hy z hyz ((active_iff z).mp hz)
    have hswap : Equiv.swap r s = Equiv.swap (palette p (pair j).1) (palette p (pair j).2) := by
      rcases hp with ⟨hr, hs⟩ | ⟨hs, hr⟩
      · rw [hr, hs]
      · rw [hr, hs, Equiv.swap_comm]
    obtain ⟨u, q, huq⟩ := switch_certificate t p j
    refine ⟨u, q, ?_⟩
    intro y hy
    rw [C.swap_apply_of_chain r s K _ hc active closed hxc hxK y, hC y hy, hswap]
    exact huq y hy
  · refine ⟨t, p, ?_⟩
    intro y hy
    rw [C.swapOnKempeComponent_apply_of_not_mem (fun h => htouch ⟨y, hy, h⟩)]
    exact hC y hy

def Extends (a : Edge → Fin 3) : Prop :=
  ∃ d : Edge → Fin 3, Proper inc Finset.univ d ∧ ∀ x ∈ old, d x = a x

private theorem request_certificate : ∀ t p,
    (∀ q, q ∉ profile inc old (assignment t p) 2 ↔ q = palette p 2) ∧
    (∀ q, q ∉ profile inc old (assignment t p) 3 ↔ q = palette p 2) := by
  decide +kernel

/-- The two restored edges at vertex zero would have the same colour. -/
theorem locked_no_extension (C : (graph inc old).Coloring (Fin 3))
    (hC : Locked C) : ¬ Extends C := by
  obtain ⟨t, p, hC⟩ := hC
  rintro ⟨d, hd, hext⟩
  have missing {e : Edge} {v : Vertex} (he : e ∉ old) (hv : v ∈ inc e) :
      d e ∉ profile inc old (assignment t p) v := by
    intro h
    obtain ⟨y, hy, hval⟩ := Finset.mem_image.mp h
    obtain ⟨hy, hyv⟩ := Finset.mem_filter.mp hy
    have hne : e ≠ y := fun h => he (h ▸ hy)
    have hproper := hd e (Finset.mem_univ _) y (Finset.mem_univ _) hne
      ⟨v, Finset.mem_inter.mpr ⟨hv, hyv⟩⟩
    exact hproper ((hext y hy).trans ((hC y hy).trans hval)).symm
  have h1 : d 1 = palette p 2 := ((request_certificate t p).1 _).mp
    (missing (by decide : (1 : Edge) ∉ old) (by decide : (2 : Vertex) ∈ inc 1))
  have h2 : d 2 = palette p 2 := ((request_certificate t p).2 _).mp
    (missing (by decide : (2 : Edge) ∉ old) (by decide : (3 : Vertex) ∈ inc 2))
  exact (hd 1 (Finset.mem_univ _) 2 (Finset.mem_univ _) (by decide) (by decide))
    (h1.trans h2.symm)

/-- No length of physical Kempe repair on this deletion reaches an extension. -/
theorem no_history_extension {D : (graph inc old).Coloring (Fin 3)}
    (p : History base D) : ¬ Extends D :=
  locked_no_extension D (history_preserves Locked locked_switch p base_locked)

theorem no_closure_extension {D : (graph inc old).Coloring (Fin 3)}
    (hD : D ∈ (graph inc old).KempeClosure base) : ¬ Extends D := by
  obtain ⟨p⟩ := nonempty_history_iff.mpr hD
  exact no_history_extension p

def fullAssignment : Edge → Fin 3 :=
  ![0,1,2,1,2,0,2,1,0,2,0,1,0,2,0,1,2,1,1,2,1,2,0,1,0,2,0,1,0,2,2,0,1,2,1,0,1,0,2,0,0,1,2,1,2]

theorem full_proper : Proper inc Finset.univ fullAssignment := by decide +kernel

/-- There is nevertheless a successful old choice, witnessed by literal extension. -/
theorem successful_choice : ∃ a : Edge → Fin 3, Proper inc old a ∧ Extends a := by
  refine ⟨fullAssignment, ?_, fullAssignment, full_proper, fun _ _ => rfl⟩
  intro x hx y hy hne hmeet
  exact full_proper x (Finset.mem_univ _) y (Finset.mem_univ _) hne hmeet

end Mettapedia.GraphTheory.FourColor.AdjacentPairLockedOrbit
