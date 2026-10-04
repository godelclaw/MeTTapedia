import MettapediaFourColor.KempeShortBlock

/-!
# A majority cut with a balanced remainder

A six-port majority in a ten-port matching supplies an adjacent component.
Three positions give a direct repair. At either of the two remaining cuts,
the exact complement has a balanced reading. Its ear gives a direct repair;
its nested case either gives another direct repair or two specified joint
components. No list of matching layouts is inspected.
-/

namespace FourColor.StripLoopMatching

open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

def good (a b : Fin 10) : Prop :=
  (a,b) ∈ ([(0,3),(2,3),(2,5),(3,6),(4,7),(4,9),(5,6),(5,8),(6,7)] :
    List (Fin 10 × Fin 10))

instance (a b) : Decidable (good a b) := by unfold good; infer_instance

def block : Finset (Fin 10) := {2,3,4,5,6,7}
def cut : Bool → Fin 10 | false => 3 | true => 4
def right : Bool → Fin 10 | false => 4 | true => 5
def embed : Bool → Fin 8 → Fin 10
  | false => ![2,5,6,7,8,9,0,1]
  | true => ![2,3,6,7,8,9,0,1]

theorem coordinates : ∀ s,
    Function.Injective (embed s) ∧
    (∀ i, embed s i ≠ cut s ∧ embed s i ≠ right s) ∧
    (∀ v, v ≠ cut s → v ≠ right s → ∃ i, embed s i = v) ∧
    (∀ a b c, KempeBalancedBlock.cyclic a b c →
      KempeBalancedBlock.cyclic (embed s a) (embed s b) (embed s c)) := by
  decide +kernel

theorem small_ears : ∀ s (i j : Fin 8), i.val < 4 → j.val < 4 →
    j.val = i.val + 1 → good (embed s i) (embed s j) := by decide +kernel

/-- One supplied matching yields a ready component or a compatible pair.
The same matching is retained through restriction and reconstruction. -/
theorem select (mate : Fin 10 → Fin 10)
    (inv : Function.Involutive mate) (free : ∀ i, mate i ≠ i)
    (planar : IsNoncrossingMatching mate) :
    (∃ a b, good a b ∧ mate a = b) ∨ (mate 0 = 5 ∧ mate 1 = 2) := by
  have puncture (s : Bool) (edge : mate (cut s) = right s) :
      (∃ a b, good a b ∧ mate a = b) ∨ (mate 0 = 5 ∧ mate 1 = 2) := by
    obtain ⟨inject,avoids,covers,cycles⟩ := coordinates s
    obtain ⟨small,lift,si,sf,sp⟩ := KempeShortBlock.restrict_pair mate inv free planar
      (cut s) (right s) edge (embed s) inject avoids covers
      (KempeBalancedBlock.noncross_of_cyclic (embed s) cycles)
    rcases KempeBalancedBlock.ear_or_nested (k := 4) small si sf sp with
      ⟨i,hi,hj,adj⟩ | nested
    · exact Or.inl ⟨embed s i,embed s (small i),small_ears s i _ hi hj adj,(lift i).symm⟩
    · have rigid (i : Fin 8) : mate (embed s i) = embed s i.rev :=
        (lift i).symm.trans (congrArg (embed s) (nested i))
      cases s with
      | false =>
        right
        have h0 := rigid 1
        have h1 := rigid 0
        have r0 : mate 5 = 0 := by simpa [embed] using h0
        have r1 : mate 2 = 1 := by simpa [embed] using h1
        exact ⟨by rw [← r0,inv],by rw [← r1,inv]⟩
      | true =>
        have h := rigid 1
        have r : mate 3 = 0 := by simpa [embed] using h
        exact Or.inl ⟨0,3,by decide +kernel,by rw [← r,inv]⟩
  obtain ⟨a,ha,hb,adj⟩ := exists_adjacent_majority mate inv free planar block
    (by decide +kernel) (by decide +kernel)
  have pos : a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by
    have bounds : ∀ a b : Fin 10, a ∈ block → b ∈ block → b.val = a.val + 1 →
        a = 2 ∨ a = 3 ∨ a = 4 ∨ a = 5 ∨ a = 6 := by decide +kernel
    exact bounds a (mate a) ha hb adj
  rcases pos with rfl | rfl | rfl | rfl | rfl
  · exact Or.inl ⟨2,3,by decide +kernel,Fin.ext adj⟩
  · exact puncture false (Fin.ext adj)
  · exact puncture true (Fin.ext adj)
  · exact Or.inl ⟨5,6,by decide +kernel,Fin.ext adj⟩
  · exact Or.inl ⟨6,7,by decide +kernel,Fin.ext adj⟩

/-- The selected components preserve one supplied exterior chromogram.
Both switches in the exceptional branch use that same original matching. -/
theorem coclosure {P : List Color → Prop} (c : Fin 10 → Color)
    (active : ∀ i, c i ≠ Color.c1)
    (single : ∀ a b, good a b →
      KempeCoclosure P (List.ofFn (KempeIntervalRepair.switch c a b)))
    (paired : KempeCoclosure P (List.ofFn
      (KempeIntervalRepair.switch (KempeIntervalRepair.switch c 0 5) 1 2))) :
    KempeCoclosure P (List.ofFn c) := by
  intro outside closed held
  obtain ⟨_,w,hw,keep⟩ := closed _ held
  obtain ⟨mate,inv,planar,fixed,stable⟩ := KempeChromogramMatching.recover_stable c w hw
  have free (i) : mate i ≠ i := fun h => active i ((fixed i).mp h)
  rcases select mate inv free planar with ⟨a,b,good,edge⟩ | ⟨first,second⟩
  · apply single a b good outside closed
    apply keep
    simpa only [edge] using stable c hw a (active a)
  · apply paired outside closed
    apply keep
    have step := stable c hw 0 (active 0)
    rw [first] at step
    simpa only [second] using stable _ step 1 (active 1)

end FourColor.StripLoopMatching
