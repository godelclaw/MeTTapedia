import Mettapedia.GraphTheory.FourColor.GoertzelV24NormalizedTaitSupport

/-!
# A Myhill--Nerode lower bound for exact support semantics

The Boolean support carried by a cut is a finite set of boundary words.  Its
raw carrier has `2^(3^k)` elements at width `k`.  This file proves that this is
not merely an inefficient representation when the observer is allowed every
abstract suffix support: two different prefix supports are distinguished by
the singleton suffix containing a word on which they differ.

Consequently every deterministic code which answers all suffix-intersection
experiments exactly is injective on the full powerset carrier.  The theorem is
deliberately scoped to the unrestricted support algebra.  A smaller quotient
may still be exact on the subset of supports and suffixes physically realized
by planar cubic tangles; proving that restriction is a separate reachability
theorem.
-/

namespace Mettapedia.GraphTheory.FourColor

namespace GoertzelV24SupportNerodeLowerBound

open GoertzelV24BoundaryEssentialGluing
open GoertzelV24NormalizedTaitSupport
open GoertzelV24RawNooseCountPumping

universe u v

/-- An abstract suffix accepts a prefix support exactly when the two supports
share at least one boundary word. -/
def SupportAccepts {Word : Type u} [DecidableEq Word]
    (support suffix : Finset Word) : Prop :=
  (support ∩ suffix).Nonempty

@[simp] theorem supportAccepts_singleton_iff
    {Word : Type u} [DecidableEq Word]
    (support : Finset Word) (word : Word) :
    SupportAccepts support {word} ↔ word ∈ support := by
  constructor
  · rintro ⟨found, hfound⟩
    have hparts := Finset.mem_inter.mp hfound
    have hfound_eq : found = word := Finset.mem_singleton.mp hparts.2
    simpa [hfound_eq] using hparts.1
  · intro hword
    exact ⟨word, Finset.mem_inter.mpr ⟨hword, by simp⟩⟩

/-- Distinct raw supports have different right languages: a singleton suffix
at any word in their symmetric difference distinguishes them. -/
theorem exists_suffix_distinguishing
    {Word : Type u} [DecidableEq Word]
    {left right : Finset Word} (hne : left ≠ right) :
    ∃ suffix : Finset Word,
      ¬ (SupportAccepts left suffix ↔ SupportAccepts right suffix) := by
  classical
  by_contra hnone
  apply hne
  ext word
  by_contra hword
  apply hnone
  exact ⟨{word}, by simpa using hword⟩

/-- Any deterministic code which preserves every abstract suffix experiment
is injective on raw supports.  The observer may be encoded however one likes;
only exact agreement with support intersection is required. -/
theorem code_injective_of_exact_suffix_experiments
    {Word : Type u} [DecidableEq Word]
    {Code : Type v}
    (encode : Finset Word → Code)
    (observe : Code → Finset Word → Prop)
    (hexact : ∀ support suffix,
      observe (encode support) suffix ↔ SupportAccepts support suffix) :
    Function.Injective encode := by
  intro left right hcode
  classical
  ext word
  have hleft := hexact left {word}
  have hright := hexact right {word}
  rw [hcode] at hleft
  have haccept :
      SupportAccepts left {word} ↔ SupportAccepts right {word} := by
    exact hleft.symm.trans hright
  simpa using haccept

/-- Cardinal form of the unrestricted Myhill--Nerode lower bound. -/
theorem card_raw_support_le_of_exact_suffix_experiments
    {Word : Type u} [Fintype Word] [DecidableEq Word]
    {Code : Type v} [Fintype Code]
    (encode : Finset Word → Code)
    (observe : Code → Finset Word → Prop)
    (hexact : ∀ support suffix,
      observe (encode support) suffix ↔ SupportAccepts support suffix) :
    Fintype.card (Finset Word) ≤ Fintype.card Code := by
  exact Fintype.card_le_of_injective encode
    (code_injective_of_exact_suffix_experiments encode observe hexact)

/-- At a literal `k`-port Tait interface, unrestricted exact suffix semantics
requires at least `2^(3^k)` deterministic states. -/
theorem two_pow_three_pow_le_card_code
    (k : Nat) {Code : Type v} [Fintype Code]
    (encode : Finset (CutWord (StandardPort.{u} k)) → Code)
    (observe : Code → Finset (CutWord (StandardPort.{u} k)) → Prop)
    (hexact : ∀ support suffix,
      observe (encode support) suffix ↔ SupportAccepts support suffix) :
    2 ^ (3 ^ k) ≤ Fintype.card Code := by
  rw [← card_normalizedSupportType]
  exact card_raw_support_le_of_exact_suffix_experiments
    encode observe hexact

end GoertzelV24SupportNerodeLowerBound

end Mettapedia.GraphTheory.FourColor
