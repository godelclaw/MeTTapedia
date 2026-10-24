import Mettapedia.GSLT.LanguageDef.MatchDecisionContract
import Mettapedia.Machines.MatchIndexProjection

/-!
# Bounded selector observations before exact comparison

The exact comparator observes opaque payloads; the bounded observer reads
only their declared class. The observer reserves child tokens using the same
expansion algebra as the ordinary indexes. Different fingerprints refute
equality, while collisions retain the original exact comparison.

The model counts visited nodes, including cuts. Native leaf encoding, metadata
truthfulness and C memory conformance remain separate implementation duties.
No claim of optimal overall dispatch or physical running time is made.
-/

set_option autoImplicit false
namespace Mettapedia.Machines.SelectorFingerprint

open Mettapedia.GSLT.LanguageDef.MatchDecisionContract
open ExpansionBudget

mutual
inductive Tree where
  | atom (words : List Nat)
  | hidden (kind : List Nat) (payload : Nat)
  | node (children : Forest)
inductive Forest where
  | nil
  | cons (first : Tree) (rest : Forest)
end

def Forest.length : Forest → Nat
  | .nil => 0
  | .cons _ rest => rest.length + 1

mutual
def exact (payloadEqual : Nat → Nat → Bool) : Tree → Tree → Bool
  | .atom a, .atom b => decide (a = b)
  | .hidden a x, .hidden b y => decide (a = b) && payloadEqual x y
  | .node a, .node b => exactForest payloadEqual a b
  | _, _ => false
def exactForest (payloadEqual : Nat → Nat → Bool) : Forest → Forest → Bool
  | .nil, .nil => true
  | .cons a as, .cons b bs => exact payloadEqual a b && exactForest payloadEqual as bs
  | _, _ => false
end

mutual
inductive Same (payloadEqual : Nat → Nat → Bool) : Tree → Tree → Prop where
  | atom (words) : Same payloadEqual (.atom words) (.atom words)
  | hidden (kind) {x y} : payloadEqual x y = true →
      Same payloadEqual (.hidden kind x) (.hidden kind y)
  | node {a b} : SameForest payloadEqual a b → Same payloadEqual (.node a) (.node b)
inductive SameForest (payloadEqual : Nat → Nat → Bool) : Forest → Forest → Prop where
  | nil : SameForest payloadEqual .nil .nil
  | cons {a b as bs} : Same payloadEqual a b → SameForest payloadEqual as bs →
      SameForest payloadEqual (.cons a as) (.cons b bs)
end

mutual
theorem exact_sound (eq : Nat → Nat → Bool) (a b : Tree)
    (accepted : exact eq a b = true) : Same eq a b := by
  cases a with
  | atom a =>
      cases b with
      | atom b =>
          have h : a = b := by simpa [exact] using accepted
          subst b
          exact .atom a
      | hidden _ _ => simp [exact] at accepted
      | node _ => simp [exact] at accepted
  | hidden a x =>
      cases b with
      | hidden b y =>
          have h : a = b ∧ eq x y = true := by simpa [exact] using accepted
          rcases h with ⟨rfl, h⟩
          exact .hidden a h
      | atom _ => simp [exact] at accepted
      | node _ => simp [exact] at accepted
  | node a =>
      cases b with
      | node b => exact .node (exactForest_sound eq a b accepted)
      | atom _ => simp [exact] at accepted
      | hidden _ _ => simp [exact] at accepted
theorem exactForest_sound (eq : Nat → Nat → Bool) (a b : Forest)
    (accepted : exactForest eq a b = true) : SameForest eq a b := by
  cases a with
  | nil =>
      cases b with
      | nil => exact .nil
      | cons _ _ => simp [exactForest] at accepted
  | cons a as =>
      cases b with
      | nil => simp [exactForest] at accepted
      | cons b bs =>
          have h : exact eq a b = true ∧ exactForest eq as bs = true := by
            simpa [exactForest] using accepted
          exact .cons (exact_sound eq a b h.1) (exactForest_sound eq as bs h.2)
end

theorem SameForest.length_eq {eq : Nat → Nat → Bool} {a b : Forest}
    (same : SameForest eq a b) : a.length = b.length := by
  cases same with
  | nil => rfl
  | cons _ tail => simp [Forest.length, SameForest.length_eq tail]

structure Observation where
  remaining : Budget
  words : List Nat
  reads : Nat

mutual
def observe (limit depth : Nat) (budget : Budget) : Tree → Observation
  | .atom words => ⟨budget, 0 :: words, 1⟩
  | .hidden kind _ => ⟨budget, 1 :: kind, 1⟩
  | .node children =>
      match reserve limit depth children.length budget with
      | none => ⟨budget, [2, children.length, 3], 1⟩
      | some middle =>
          let rest := observeForest limit (depth + 1) middle children
          ⟨rest.remaining, 2 :: children.length :: rest.words, 1 + rest.reads⟩
def observeForest (limit depth : Nat) (budget : Budget) : Forest → Observation
  | .nil => ⟨budget, [], 0⟩
  | .cons first rest =>
      let head := observe limit depth budget first
      let tail := observeForest limit depth head.remaining rest
      ⟨tail.remaining, head.words ++ tail.words, head.reads + tail.reads⟩
end

mutual
theorem Same.observation {eq : Nat → Nat → Bool} {a b : Tree}
    (same : Same eq a b) (limit depth : Nat) (budget : Budget) :
    observe limit depth budget a = observe limit depth budget b := by
  cases same with
  | atom _ => rfl
  | hidden _ _ => rfl
  | node children =>
      simp only [observe, children.length_eq]
      split
      · rfl
      · rw [SameForest.observation children]
theorem SameForest.observation {eq : Nat → Nat → Bool} {a b : Forest}
    (same : SameForest eq a b) (limit depth : Nat) (budget : Budget) :
    observeForest limit depth budget a = observeForest limit depth budget b := by
  cases same with
  | nil => rfl
  | cons head tail =>
      simp only [observeForest]
      rw [Same.observation head, SameForest.observation tail]
end

mutual
theorem reads_conservation (limit depth : Nat) (budget : Budget) (term : Tree) :
    (observe limit depth budget term).reads +
      (observe limit depth budget term).remaining.childTokens = budget.childTokens + 1 := by
  cases term with
  | atom _ => simp [observe]; omega
  | hidden _ _ => simp [observe]; omega
  | node children =>
      cases accepted : reserve limit depth children.length budget with
      | none => simp [observe, accepted]; omega
      | some middle =>
          have first := reserve_conservation accepted
          have rest := forest_reads_conservation limit (depth + 1) middle children
          simp only [observe, accepted]
          omega
theorem forest_reads_conservation (limit depth : Nat) (budget : Budget) (terms : Forest) :
    (observeForest limit depth budget terms).reads +
      (observeForest limit depth budget terms).remaining.childTokens =
        budget.childTokens + terms.length := by
  cases terms with
  | nil => simp [observeForest, Forest.length]
  | cons first rest =>
      have head := reads_conservation limit depth budget first
      have tail := forest_reads_conservation limit depth
        (observe limit depth budget first).remaining rest
      simp only [observeForest, Forest.length]
      omega
end

theorem reads_bounded (limit depth : Nat) (budget : Budget) (term : Tree) :
    (observe limit depth budget term).reads ≤ budget.childTokens + 1 := by
  have account := reads_conservation limit depth budget term
  omega

def fingerprint {Key : Type} (hash : List Nat → Key) (limit : Nat)
    (budget : Budget) (term : Tree) : Key :=
  hash (observe limit 0 budget term).words

theorem fingerprint_agrees {Key : Type} (hash : List Nat → Key) (limit : Nat)
    (budget : Budget) (eq : Nat → Nat → Bool) (a b : Tree)
    (accepted : exact eq a b = true) :
    fingerprint hash limit budget a = fingerprint hash limit budget b := by
  unfold fingerprint
  rw [(exact_sound eq a b accepted).observation]

theorem filter_exact {Key : Type} [DecidableEq Key] (hash : List Nat → Key)
    (limit : Nat) (budget : Budget) (eq : Nat → Nat → Bool)
    (query : Tree) (rows : List Tree) :
    (rows.filter (fun row => decide (fingerprint hash limit budget query =
      fingerprint hash limit budget row))).filter (exact eq query) =
        rows.filter (exact eq query) := by
  apply MatchIndexProjection.filter_candidates
  intro row accepted
  simpa using fingerprint_agrees hash limit budget eq query row accepted

example (term : Tree) : (observe 8 0 ⟨128, 511⟩ term).reads ≤ 512 :=
  reads_bounded 8 0 ⟨128, 511⟩ term

example : fingerprint (fun _ => 0) 8 ⟨128, 511⟩ (.atom [7]) =
    fingerprint (fun _ => 0) 8 ⟨128, 511⟩ (.atom [9]) ∧
    exact (fun x y => decide (x = y)) (.atom [7]) (.atom [9]) = false := by decide

example : fingerprint id 8 ⟨128, 511⟩ (.hidden [5] 7) =
    fingerprint id 8 ⟨128, 511⟩ (.hidden [5] 9) ∧
    exact (fun x y => decide (x = y)) (.hidden [5] 7) (.hidden [5] 9) = false := by decide

end Mettapedia.Machines.SelectorFingerprint
