import MettapediaFourColor.KempeMajorityRepair
import MettapediaFourColor.StripIntervalRepair

/-!
# A single majority-block law for the two source repairs

In each source input, four consecutive active ports have successful pair
choices along their three intervening edges. The same majority theorem
therefore supplies a whole actual component, replacing both interval checks.
The full source colouring witnesses are reused unchanged.
-/

namespace FourColor.StripMajorityRepair

open Color KempeMatchingChromogram KempeBoundarySplit
open StripIntervalRepair
open Mettapedia.GraphTheory.FourColor.Compositional.CyclicBoundaryMatching

def embed : Bool → Fin 6 → Fin 11
  | false => ![3,5,6,7,8,9]
  | true => ![7,8,9,3,5,6]

def rank : Bool → Fin 11 → Fin 6
  | false => ![0,0,0,0,0,1,2,3,4,5,0]
  | true => ![0,0,0,3,0,4,5,0,1,2,0]

theorem rank_embed : ∀ s i, rank s (embed s i) = i := by decide +kernel

theorem embed_rank : ∀ s i, StripIntervalRepair.word s i ≠ c1 → embed s (rank s i) = i := by
  decide +kernel

theorem active : ∀ s i, StripIntervalRepair.word s (embed s i) ≠ c1 := by decide +kernel

private instance {n : ℕ} (a b c d : Fin n) : Decidable (ChordsCross a b c d) := by
  unfold ChordsCross
  infer_instance

/-- These coordinates retain the cyclic order, including the second input's rotation. -/
theorem order : ∀ s a b x y,
    ¬ ChordsCross (embed s a) (embed s x) (embed s b) (embed s y) →
      ¬ ChordsCross a x b y := by decide +kernel

def block : Finset (Fin 6) := {0,1,2,3}

theorem convex : ∀ a ∈ block, ∀ b ∈ block, ∀ x, a < x → x < b → x ∈ block := by
  decide +kernel

theorem majority : 6 < 2 * block.card := by decide +kernel

theorem successful : ∀ s, ∀ a ∈ block, ∀ b ∈ block, b.val = a.val + 1 →
    good s (embed s a) (embed s b) = true := by decide +kernel

/-- Both specified source inputs consume the same majority law. The original
component matching and genuine source colouring are retained. -/
theorem source_repair (s : Bool) (mate : Fin 11 → Fin 11)
    (hinv : Function.Involutive mate) (hnc : Noncrossing mate)
    (hf : ∀ i, mate i = i ↔ StripIntervalRepair.word s i = c1) :
    ∃ k : TriangleStripAnchors.input0099.graph.Coloring Color,
      matchg [] (trace (TriangleStripAnchors.input0099.boundary.map k))
        (gram mate (StripIntervalRepair.word s)) := by
  have terminal : ∀ a b, good s a b = true →
      GraphTrace TriangleStripAnchors.input0099.graph TriangleStripAnchors.input0099.boundary
        (List.ofFn (KempeIntervalRepair.switch (StripIntervalRepair.word s) a b)) := by
    intro a b h
    obtain ⟨i,hi⟩ := answers s a b h
    exact ⟨colouring s i,hi⟩
  have lift := (KempeMajorityRepair.active_mate (StripIntervalRepair.word s) mate hinv hf
    (embed s) (rank s) (rank_embed s) (embed_rank s) (active s)).1
  have horder : IsNoncrossingMatching (fun i => rank s (mate (embed s i))) := by
    intro a b
    apply order s a b
    rw [lift, lift]
    exact hnc (embed s a) (embed s b)
  obtain ⟨_,_,⟨k,hk⟩,hm⟩ := KempeMajorityRepair.answer
    (StripIntervalRepair.word s) (good s) _ terminal
    (embed s) (rank s) (rank_embed s) (embed_rank s) (active s)
    block convex majority (successful s) mate hinv hnc (nonzero s) hf horder
  exact ⟨k,hk ▸ hm⟩

end FourColor.StripMajorityRepair
