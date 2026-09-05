import Mettapedia.GraphTheory.FourColor.KempeDerivation

/-!
# Certificates of derivability, decided in the kernel

A derivation certificate is a sequence of nodes; each node's word is derivable
once every active noncrossing matching admits a component-union switch into
the words known so far (the target and the earlier nodes).  For a fixed word
and pair the step condition is decidable (all port maps, all port subsets), so
each node is one kernel decision (`Derivable.of_known`); the sequence assembles
into `Derivable` for every node word.
-/

namespace Mettapedia.GraphTheory.FourColor
namespace KempeDerivation

open Compositional.BoundaryKempeSwitch Compositional.CyclicBoundaryMatching
open GoertzelV24PortTangleCommonKempeWeb GoertzelV24HexagonPairingTargetAwareBoundary

variable {n : Nat}

instance instDecidablePairActiveColor (pair : TaitColorPair) (c : Color) :
    Decidable (pairActiveColor pair c) :=
  decidable_of_iff (c = pair.colors.1 ∨ c = pair.colors.2) (by simp [pairActiveColor, Color.twoColor])

instance instDecidableActiveAt (w : Word n) (pair : TaitColorPair) (i : Fin n) :
    Decidable (activeAt w pair i) := by
  unfold activeAt; infer_instance

instance instDecidableIsActiveMatching (w : Word n) (pair : TaitColorPair) (mate : Fin n → Fin n) :
    Decidable (IsActiveMatching w pair mate) := by
  unfold IsActiveMatching; infer_instance

instance instDecidableChordsCross (a b c d : Fin n) :
    Decidable (Compositional.CyclicBoundaryMatching.ChordsCross a b c d) := by
  unfold Compositional.CyclicBoundaryMatching.ChordsCross; infer_instance

instance instDecidableIsNoncrossingMatching (mate : Fin n → Fin n) :
    Decidable (Compositional.CyclicBoundaryMatching.IsNoncrossingMatching mate) := by
  unfold Compositional.CyclicBoundaryMatching.IsNoncrossingMatching; infer_instance

instance instDecidableIsComponentUnion (mate : Fin n → Fin n) (selected : Finset (Fin n)) :
    Decidable (IsComponentUnion mate selected) := by
  unfold IsComponentUnion; infer_instance

/-- the step condition of a node against a finite set of known words -/
def StepOk (w : Word n) (pair : TaitColorPair) (known : Finset (Word n)) : Prop :=
  ∀ mate : Fin n → Fin n, IsActiveMatching w pair mate → IsNoncrossingMatching mate →
    ∃ selected : Finset (Fin n), IsComponentUnion mate selected ∧
      switchBoundaryWord w pair selected ∈ known

instance instDecidableStepOk (w : Word n) (pair : TaitColorPair) (known : Finset (Word n)) :
    Decidable (StepOk w pair known) := by
  unfold StepOk; infer_instance

/-- the step from a classical existence of switches -/
theorem Derivable.step_of_forall {target : Set (Word n)} {w : Word n} (pair : TaitColorPair)
    (h : ∀ mate : Fin n → Fin n, IsActiveMatching w pair mate → IsNoncrossingMatching mate →
      ∃ selected : Finset (Fin n), IsComponentUnion mate selected ∧
        Derivable target (switchBoundaryWord w pair selected)) :
    Derivable target w :=
  Derivable.step pair (fun mate ha hn => Classical.choose (h mate ha hn))
    (fun mate ha hn => (Classical.choose_spec (h mate ha hn)).1)
    (fun mate ha hn => (Classical.choose_spec (h mate ha hn)).2)

/-- **one node**: a decided step into known-derivable words is a derivation -/
theorem Derivable.of_known {target : Set (Word n)} {w : Word n} (pair : TaitColorPair)
    {known : Finset (Word n)} (hknown : ∀ u ∈ known, Derivable target u)
    (hstep : StepOk w pair known) : Derivable target w :=
  Derivable.step_of_forall pair fun mate ha hn =>
    let ⟨selected, hsel, hmem⟩ := hstep mate ha hn
    ⟨selected, hsel, hknown _ hmem⟩

/-- a certificate: words with their pairs, in derivation order -/
structure Certificate (n : Nat) where
  nodes : List (Word n × TaitColorPair)

/-- the words known after the first `k` nodes: the target words and the earlier node words -/
def Certificate.knownAt (base : Finset (Word n)) (c : Certificate n) (k : Nat) : Finset (Word n) :=
  base ∪ ((c.nodes.take k).map Prod.fst).toFinset

/-- the whole certificate checks -/
def Certificate.Ok (base : Finset (Word n)) (c : Certificate n) : Prop :=
  ∀ k (h : k < c.nodes.length), StepOk (c.nodes[k]).1 (c.nodes[k]).2 (c.knownAt base k)

instance (base : Finset (Word n)) (c : Certificate n) : Decidable (c.Ok base) := by
  unfold Certificate.Ok; infer_instance

/-- **soundness of certificates**: every node word of a checked certificate is derivable into
any target containing the base words -/
theorem Certificate.derivable_of_ok {target : Set (Word n)} {base : Finset (Word n)}
    (hbase : ∀ u ∈ base, u ∈ target) (c : Certificate n) (hok : c.Ok base) :
    ∀ k (h : k < c.nodes.length), Derivable target (c.nodes[k]).1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h
    refine Derivable.of_known (c.nodes[k]).2 (known := c.knownAt base k) ?_ (hok k h)
    intro u hu
    simp only [Certificate.knownAt, Finset.mem_union, List.mem_toFinset, List.mem_map] at hu
    rcases hu with hu | ⟨⟨u', p⟩, hmem, rfl⟩
    · exact Derivable.base (hbase u hu)
    · obtain ⟨j, hj, hjk⟩ := List.getElem_of_mem hmem
      rw [List.getElem_take] at hjk
      have hjlt : j < k := by
        have := hj; simp only [List.length_take] at this; omega
      have := ih j hjlt (by simp only [List.length_take] at hj; omega)
      rw [hjk] at this
      exact this

/-! ## a kernel check of the step condition at width three -/

/-- red, blue, purple as Tait colours -/
def tc (i : Fin 3) : {color : Color // color ≠ 0} :=
  match i with
  | 0 => ⟨red, by decide⟩
  | 1 => ⟨blue, by decide⟩
  | 2 => ⟨purple, by decide⟩

/-- the word red, blue, red: two red-blue-active ports must be mated -/
example : StepOk (n := 3) (![tc 0, tc 1, tc 2]) TaitColorPair.redBlue
    {![tc 1, tc 0, tc 2], ![tc 0, tc 1, tc 2]} := by decide

end KempeDerivation
end Mettapedia.GraphTheory.FourColor
