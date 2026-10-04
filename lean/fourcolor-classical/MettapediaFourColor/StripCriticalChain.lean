import MettapediaFourColor.StripPuncturedExtension

/-!
# A shared forced chain invisible to every proper core restriction

Two proper boundaries of the decoded D0099 source admit a colouring after
any nonempty set of core vertices is deleted. Neither boundary extends to
the entire source. The common obstruction propagates a colour through a
path and then forces both ends of a triangle edge to agree.

The path lemma has arbitrary length and colour type. The two consumers
retain the actual source edges and every ordered boundary colour. This
refutes independent local extension as a gluing criterion; it does not
refute composition using compatible witnesses or allow conclusions about
Kempe repair when the boundary may change.
-/

namespace FourColor.StripCriticalChain

open Color StripResponseSummary StripSourceExtension StripPartialColouring
open TriangleStripAnchors

/-- Pair-valued constraints propagate a pinned colour along any proper path. -/
theorem forced_path {C : Type*} {n : ℕ} (x a : Fin (n+1) → C)
    (start : x 0 = a 0)
    (choices : ∀ i : Fin n, x i.succ = a i.castSucc ∨ x i.succ = a i.succ)
    (edges : ∀ i : Fin n, x i.castSucc ≠ x i.succ) : ∀ i, x i = a i := by
  refine Fin.induction start ?_
  intro i ih
  exact (choices i).resolve_left (fun h => edges i (ih.trans h.symm))

def boundary : Bool → Boundary
  | false => ![c0,c1,c3,c1,c0,c1,c0,c2,c3,c2,c3]
  | true => ![c0,c1,c3,c0,c3,c0,c3,c2,c1,c2,c1]

def step (s : Bool) : Color := if s then c3 else c0
def anchor (s : Bool) : Color := if s then c0 else c1
def last (s : Bool) : Color := if s then c1 else c3

def path (s : Bool) : Fin 4 → Fin 8 :=
  ![if s then 5 else 7, if s then 7 else 5, 6, 4]

def forced (s : Bool) : Fin 4 → Color := ![c2,step s,anchor s,step s]

theorem proper : ∀ s, ProperBoundary (boundary s) := by decide +kernel

theorem start_allowed : ∀ s a, unary (boundary s) (path s 0) a → a = forced s 0 := by
  decide +kernel

theorem path_allowed : ∀ s (i : Fin 3) a, unary (boundary s) (path s i.succ) a →
    a = forced s i.castSucc ∨ a = forced s i.succ := by decide +kernel

theorem path_edges : ∀ s (i : Fin 3),
    (path s i.castSucc, path s i.succ) ∈ edges ∨
      (path s i.succ, path s i.castSucc) ∈ edges := by decide +kernel

theorem terminal_allowed : ∀ s,
    (∀ a, unary (boundary s) 0 a → a = anchor s) ∧
    (∀ a, unary (boundary s) 1 a → a = c2 ∨ a = step s ∨ a = anchor s) ∧
    (∀ a, unary (boundary s) 2 a → a = c2 ∨ a = last s) ∧
    (∀ a, unary (boundary s) 3 a → a = c2 ∨ a = last s) := by decide +kernel

/-- One propagation argument covers both boundaries. No full-colouring
enumeration is used to reject extension. -/
theorem no_core (s : Bool) : ¬ ∃ f, ValidCore (boundary s) f := by
  rintro ⟨f,hf⟩
  have e {u v : Fin 8} (h : (u,v) ∈ edges ∨ (v,u) ∈ edges) : f u ≠ f v := by
    rcases h with h | h
    · exact hf.2 _ h
    · exact (hf.2 _ h).symm
  have hp := forced_path (fun i => f (path s i)) (forced s)
    (start_allowed s _ (hf.1 _))
    (fun i => path_allowed s i _ (hf.1 _)) (fun i => e (path_edges s i))
  have h4 : f 4 = step s := hp 3
  obtain ⟨a0,a1,a2,a3⟩ := terminal_allowed s
  have h0 : f 0 = anchor s := a0 _ (hf.1 _)
  have e01 := e (u := 0) (v := 1) (by decide)
  have e14 := e (u := 1) (v := 4) (by decide)
  have e12 := e (u := 1) (v := 2) (by decide)
  have e13 := e (u := 1) (v := 3) (by decide)
  have e23 := e (u := 2) (v := 3) (by decide)
  have h1 : f 1 = c2 := by
    rcases a1 _ (hf.1 _) with h | h | h
    · exact h
    · exact (e14 (h.trans h4.symm)).elim
    · exact (e01 (h0.trans h.symm)).elim
  have h2 : f 2 = last s :=
    (a2 _ (hf.1 _)).resolve_left (fun h => e12 (h1.trans h.symm))
  have h3 : f 3 = last s :=
    (a3 _ (hf.1 _)).resolve_left (fun h => e13 (h1.trans h.symm))
  exact e23 (h2.trans h3.symm)

/-- The same exact symbolic triangle joins reconstruct all sixteen
single-deletion cases. No list of colouring witnesses is stored. -/
theorem punctured_joins : ∀ s (h : Fin 8),
    ∃ a c, StripPuncturedExtension.r5 {h} (boundary s) a c := by decide +kernel

theorem every_proper_core (s : Bool) (h : Finset (Fin 8)) (nonempty : h.Nonempty) :
    ∃ f, ValidExcept (boundary s) h f := by
  obtain ⟨v,hv⟩ := nonempty
  obtain ⟨f,hf⟩ := (StripPuncturedExtension.terminal_iff {v} (boundary s)).mp
    (punctured_joins s v)
  have subset : ({v} : Finset (Fin 8)) ⊆ h := by simpa using hv
  exact ⟨f,fun i hi => hf.1 i (fun hm => hi (subset hm)),
    fun e he hu hw => hf.2 e he (fun hm => hu (subset hm)) (fun hm => hw (subset hm))⟩

/-- Every nonempty core deletion has a genuine induced-source colouring,
fixing the entire ordered eleven-port boundary. -/
theorem every_proper_source (s : Bool) (h : Finset (Fin 8)) (nonempty : h.Nonempty) :
    ∃ k : (input0099.graph.induce {v | Live h v}).Coloring Color,
      ∀ i, k ⟨port i,live_port h i⟩ = boundary s i := by
  obtain ⟨f,hf⟩ := every_proper_core s h nonempty
  exact ⟨.mk (fun v => completeColour (boundary s) f v.val)
    (fun {u v} he => partial_valid (boundary s) h f (proper s) hf
      u.val v.val u.property v.property he), fun i => colour_port _ _ i⟩

theorem no_source (s : Bool) : ¬ ∃ k : input0099.graph.Coloring Color,
    ∀ i, k (port i) = boundary s i := by
  rintro ⟨k,hk⟩
  exact no_core s ⟨_,valid_of_colouring _ k hk⟩

/-- Even the existence of all eight maximal proper views is insufficient.
Their independently chosen witnesses need not agree on the overlaps. -/
theorem local_extension_not_sufficient : ¬ (∀ b : Boundary, ProperBoundary b →
    (∀ h : Fin 8, ∃ k : (input0099.graph.induce {v | Live {h} v}).Coloring Color,
      ∀ i, k ⟨port i,live_port {h} i⟩ = b i) →
    ∃ k : input0099.graph.Coloring Color, ∀ i, k (port i) = b i) := by
  intro h
  exact no_source false (h (boundary false) (proper false)
    (fun v => every_proper_source false {v} (by simp)))

end FourColor.StripCriticalChain
