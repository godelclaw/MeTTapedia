import Mettapedia.GraphTheory.FourColor.KempeChainCertificate
import Mettapedia.GraphTheory.FourColor.IncidenceKempeSwitch
import Mathlib.Tactic.FinCases

/-!
# A physical Kempe orbit with no strict extension

The incidence data has twelve vertices and eighteen ambient edges. Retain
all but edges {3,9} and {6,10}. A closed family of old colourings is described
by two representatives and colour permutations. Saturated chains
certify closure under every actual component switch; induction therefore
rules out every strict extension after any finite recolouring history.

A different old colouring extends to the whole ambient incidence graph.
The obstruction concerns repair of a prescribed history, not colourability.
-/

namespace Mettapedia.GraphTheory.FourColor.LockedKempeOrbit

open GoertzelV24ForkInterfaceSupport IncidenceKempeSwitch KempeChainCertificate

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

abbrev Vertex := Fin 12
abbrev Edge := Fin 18

def inc : Edge → Finset Vertex :=
  ![{0,4}, {0,7}, {0,8}, {1,3}, {1,6}, {1,7}, {2,3}, {2,5}, {2,7},
    {3,9}, {4,6}, {4,10}, {5,9}, {5,11}, {6,10}, {8,10}, {8,11}, {9,11}]

def old : Finset Edge := Finset.univ \ {9, 14}
def enlarged : Finset Edge := Finset.univ.erase 14

def palette : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2], ![0,2,1], ![1,0,2], ![1,2,0], ![2,0,1], ![2,1,0]]

def representative : Fin 2 → Edge → Fin 3 :=
  ![![0,1,2,0,1,2,1,2,0,0,2,1,1,0,0,0,1,2],
    ![0,1,2,2,1,0,1,0,2,0,2,1,1,2,0,0,1,0]]

def assignment (t : Fin 2) (p : Fin 6) (x : Edge) : Fin 3 :=
  palette p (representative t x)

theorem cubic_incidence :
    (∀ x : Edge, (inc x).card = 2) ∧
      ∀ v : Vertex, (Finset.univ.filter fun x => v ∈ inc x).card = 3 := by decide +kernel

theorem assignment_proper (t : Fin 2) (p : Fin 6) : Proper inc old (assignment t p) := by
  revert t p
  decide +kernel

def base : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3) :=
  colouring inc old (assignment 1 0) (assignment_proper 1 0)

/-- The observation concerns retained edges only. Isolated ambient edge
identifiers may have arbitrary colours and may themselves be switched. -/
def Locked (C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3)) : Prop :=
  ∃ t p, ∀ x ∈ old, C x = assignment t p x

theorem base_locked : Locked base := ⟨1, 0, fun _ _ => rfl⟩

private def channel01 : Fin 2 → List Edge :=
  ![[4,3,6,8,1,0,11,15,16,13,12], [6,7,12,17,16,15,11,0,1,5,4]]
private def channel12 : Fin 2 → List Edge :=
  ![[6,7,12,17,16,2,1,5,4,10,11], [12,13,16,2,1,8,6,3,4,10,11]]
private def channel02a : List Edge := [10,0,2,15]
private def channel02b : List Edge := [3,5,8,7,13,17]

/-- The physical chain through the specified active old edge. -/
private def chain (t : Fin 2) (p : Fin 6) (r s : Fin 3) (x : Edge) : List Edge :=
  if r = s then [x]
  else if (palette p 0 = r ∨ palette p 0 = s) ∧
      (palette p 1 = r ∨ palette p 1 = s) then channel01 t
  else if (palette p 0 = r ∨ palette p 0 = s) ∧
      (palette p 2 = r ∨ palette p 2 = s) then
    if x ∈ channel02a then channel02a else channel02b
  else channel12 t

private theorem chain_certificate : ∀ t p r s x, x ∈ old →
    (assignment t p x = r ∨ assignment t p x = s) →
    x ∈ chain t p r s x ∧
      (chain t p r s x).IsChain (IncidenceKempeSwitch.graph inc old).Adj ∧
      (∀ y ∈ chain t p r s x, y ∈ old ∧ (assignment t p y = r ∨ assignment t p y = s)) ∧
      (∀ y ∈ chain t p r s x, ∀ z, (IncidenceKempeSwitch.graph inc old).Adj y z →
        (assignment t p z = r ∨ assignment t p z = s) → z ∈ chain t p r s x) := by
  decide +kernel

private theorem switch_certificate : ∀ t p r s x, x ∈ old →
    (assignment t p x = r ∨ assignment t p x = s) →
    ∃ u q, ∀ y ∈ old,
      (if y ∈ chain t p r s x then Equiv.swap r s (assignment t p y) else assignment t p y) =
        assignment u q y := by
  decide +kernel

/-- The displayed finite family is closed under every literal component
switch, including switches on isolated, unretained identifiers. -/
theorem locked_switch (C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3))
    (r s : Fin 3) (K : (C.bicoloredSubgraph r s).ConnectedComponent)
    (hC : Locked C) : Locked (C.swapOnKempeComponent r s K) := by
  classical
  obtain ⟨t, p, hC⟩ := hC
  by_cases htouch : ∃ x ∈ old, x ∈ C.kempeComponentSet r s K
  · obtain ⟨x, hx, hxK⟩ := htouch
    have ha := C.mem_bicoloredSet_of_mem_kempeComponentSet hxK
    rw [hC x hx] at ha
    obtain ⟨hxc, hc, hca, hcc⟩ := chain_certificate t p r s x hx ha
    have active : ∀ y ∈ chain t p r s x, C y = r ∨ C y = s := by
      intro y hy
      rw [hC y (hca y hy).1]
      exact (hca y hy).2
    have closed : ∀ y ∈ chain t p r s x, ∀ z,
        (IncidenceKempeSwitch.graph inc old).Adj y z → (C z = r ∨ C z = s) →
          z ∈ chain t p r s x := by
      intro y hy z hyz hz
      rw [hC z hyz.2.2.1] at hz
      exact hcc y hy z hyz hz
    obtain ⟨u, q, huq⟩ := switch_certificate t p r s x hx ha
    refine ⟨u, q, ?_⟩
    intro y hy
    rw [C.swap_apply_of_chain r s K _ hc active closed hxc hxK y, hC y hy]
    exact huq y hy
  · refine ⟨t, p, ?_⟩
    intro y hy
    rw [C.swapOnKempeComponent_apply_of_not_mem (fun h => htouch ⟨y, hy, h⟩)]
    exact hC y hy

def Extends (a : Edge → Fin 3) : Prop :=
  ∃ d : Edge → Fin 3, Proper inc enlarged d ∧ ∀ x ∈ old, d x = a x

private def attachments (e : Edge) : Vertex × Vertex := if e = 9 then (3, 9) else (6, 10)

private theorem missing_certificate : ∀ t p e, e ∉ old → ∃ m n : Fin 3, m ≠ n ∧
    (attachments e).1 ∈ inc e ∧ (attachments e).2 ∈ inc e ∧
    (∀ q, q ∉ profile inc old (assignment t p) (attachments e).1 ↔ q = m) ∧
    (∀ q, q ∉ profile inc old (assignment t p) (attachments e).2 ↔ q = n) := by decide +kernel

/-- Every fresh ambient edge is blocked throughout the closed family.
Changing the order of additions cannot escape from this old patch. -/
theorem locked_no_strict_extension (C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3))
    (hC : Locked C) {S : Finset Edge} (hS : old ⊂ S) :
    ¬ ∃ d : Edge → Fin 3, Proper inc S d ∧ ∀ x ∈ old, d x = C x := by
  obtain ⟨t, p, hC⟩ := hC
  obtain ⟨e, heS, heold⟩ := Finset.exists_of_ssubset hS
  obtain ⟨m, n, hne, hu, hv, hm, hn⟩ := missing_certificate t p e heold
  rintro ⟨d, hd, hext⟩
  have avoid (v : Vertex) (hv : v ∈ inc e) :
      d e ∉ profile inc old (assignment t p) v := by
    intro h
    obtain ⟨y, hy, hval⟩ := Finset.mem_image.mp h
    obtain ⟨hyold, hvy⟩ := Finset.mem_filter.mp hy
    have hynew : y ∈ S := hS.1 hyold
    have hey : e ≠ y := by rintro rfl; exact heold hyold
    exact hd e heS y hynew hey ⟨v, Finset.mem_inter.mpr ⟨hv, hvy⟩⟩
      ((hext y hyold).trans ((hC y hyold).trans hval)).symm
  exact hne (((hm _).mp (avoid _ hu)).symm.trans ((hn _).mp (avoid _ hv)))

theorem locked_does_not_extend (C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3))
    (hC : Locked C) : ¬ Extends C :=
  locked_no_strict_extension C hC (by decide : old ⊂ enlarged)

/-- Arbitrarily long physical Kempe histories leave every strict future
edge set uncolourable while retaining their final old assignment. -/
theorem no_history_strict_extension {C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3)}
    (p : History base C) {S : Finset Edge} (hS : old ⊂ S) :
    ¬ ∃ d : Edge → Fin 3, Proper inc S d ∧ ∀ x ∈ old, d x = C x :=
  locked_no_strict_extension C (history_preserves Locked locked_switch p base_locked) hS

/-- No finite sequence of actual Kempe component switches repairs the
specified colouring. The route length is unrestricted. -/
theorem no_history_extends {C : (IncidenceKempeSwitch.graph inc old).Coloring (Fin 3)}
    (p : History base C) : ¬ Extends C :=
  locked_does_not_extend C (history_preserves Locked locked_switch p base_locked)

/-- The entire ambient incidence graph has this explicit proper colouring,
whose restriction is outside the locked family. -/
def globalAssignment : Edge → Fin 3 :=
  ![0,1,2,1,2,0,0,1,2,2,1,2,0,2,0,1,0,1]

theorem global_proper : Proper inc Finset.univ globalAssignment := by decide +kernel

theorem another_assignment_extends : Extends globalAssignment := by
  refine ⟨globalAssignment, ?_, fun _ _ => rfl⟩
  intro x hx y hy hxy hm
  exact global_proper x (Finset.mem_univ _) y (Finset.mem_univ _) hxy hm

end Mettapedia.GraphTheory.FourColor.LockedKempeOrbit
