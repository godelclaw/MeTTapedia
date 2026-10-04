import MettapediaFourColor.KempeChromogramMatching
import MettapediaFourColor.StripSymbolicRepair

/-!
# Five critical source inputs repaired by one majority law

All five inputs use the same structural selection and symbolic source
reconstruction. The recovered exterior matching has six or eight active
ports. No list of matching layouts or stored source colourings is used.
These are input repairs; the ensuing full-source closure is not asserted.
-/

namespace FourColor.StripCriticalRepair

open Color StripSymbolicRepair
open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

def source : Fin 5 → Fin 11 → Color :=
  ![![c1,c2,c3,c2,c2,c2,c1,c2,c3,c1,c3],
    ![c1,c2,c3,c2,c2,c2,c2,c3,c1,c3,c1],
    ![c1,c2,c3,c2,c3,c2,c1,c1,c2,c3,c2],
    ![c1,c2,c3,c2,c3,c3,c2,c1,c2,c2,c1],
    ![c1,c2,c3,c3,c2,c1,c3,c2,c2,c2,c1]]

def palette : Fin 5 → EdgePerm := ![.e213,.e123,.e321,.e123,.e123]
def colour (s : Fin 5) (i : Fin 11) : Color := palette s (source s i)
def arity (s : Fin 5) : ℕ := if s = 0 then 6 else 8

def positions : Fin 5 → List (Fin 11) :=
  ![[9,10,0,2,6,8], [4,5,6,7,9,1,2,3], [5,6,7,8,10,0,1,3],
    [4,5,6,8,9,1,2,3], [3,4,6,7,8,9,1,2]]

def embed (s : Fin 5) (i : Fin (arity s)) : Fin 11 :=
  (positions s)[i.val]?.getD 0

def rank (s : Fin 5) (i : Fin 11) : Fin (arity s) :=
  ⟨(positions s).idxOf i % arity s, Nat.mod_lt _ (by unfold arity; split <;> omega)⟩

theorem coordinates : ∀ s,
    (∀ i, rank s (embed s i) = i) ∧
    (∀ i, colour s i ≠ c1 → embed s (rank s i) = i) ∧
    (∀ i, colour s (embed s i) ≠ c1) := by decide +kernel

private instance {n : ℕ} (a b c d : Fin n) : Decidable (ChordsCross a b c d) := by
  unfold ChordsCross
  infer_instance

theorem order : ∀ s a b x y,
    ¬ ChordsCross (embed s a) (embed s x) (embed s b) (embed s y) →
      ¬ ChordsCross a x b y := by decide +kernel

def block (s : Fin 5) : Finset (Fin (arity s)) :=
  Finset.univ.filter fun i => i.val ≤ arity s / 2

theorem convex : ∀ s, ∀ a ∈ block s, ∀ b ∈ block s, ∀ x,
    a < x → x < b → x ∈ block s := by
  intro s a ha b hb x hax hxb
  simp only [block, Finset.mem_filter, Finset.mem_univ, true_and] at *
  have h : x.val < b.val := hxb
  omega

theorem majority : ∀ s, arity s < 2 * (block s).card := by decide +kernel

/-- Only the source-coordinate and terminal relation checks depend on the
five inputs. Selection from every possible exterior is the uniform theorem. -/
theorem direct_pairs : ∀ s, ∀ a ∈ block s, ∀ b ∈ block s,
    b.val = a.val + 1 →
    Direct ((List.ofFn (KempeIntervalRepair.switch (colour s) (embed s a) (embed s b))).map
      (palette s)) := by decide +kernel

theorem source_repair (s : Fin 5) : KempeCoclosure Terminal (List.ofFn (source s)) := by
  apply kempeCoclosure_of_map (palette s)
  change KempeCoclosure Terminal (List.ofFn (colour s))
  apply KempeChromogramMatching.majority_coclosure (colour s) (embed s) (rank s)
    (coordinates s).1 (coordinates s).2.1 (coordinates s).2.2
    (order s) (block s) (convex s) (majority s)
  intro a ha b hb hadj
  apply kempeCoclosure_of_map (palette s)
  exact direct_coclosure (direct_pairs s a ha b hb hadj)

end FourColor.StripCriticalRepair
