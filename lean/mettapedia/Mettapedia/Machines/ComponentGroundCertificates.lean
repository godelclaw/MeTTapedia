import Mettapedia.Machines.BindingClosedCertificates

/-!
# Independent closed-component certificates

A finite conservative inspection retains certificates for completed closed
components even when a sibling is open. The semantic relation is independent
of the checker. A memo is sound for the current store; forward extension
preserves it, while rollback in general does not.

This is a certificate-extraction model, not a verification of native graph
marks, pending-stack indices, allocator behavior or pointer lifetime.
-/
namespace Mettapedia.Machines.ComponentGroundCertificates
open ContextualCarrierSupport BindingClosedCertificates

deriving instance DecidableEq for Term

variable {Cell : Type} [DecidableEq Cell]

structure Summary (Cell : Type) where
  closed : Bool
  facts : List (Term Cell)

def MemoSound (store : Store Cell) (memo : List (Term Cell)) : Prop :=
  ∀ term ∈ memo, Ground store term

/-- Finite conservative inspection; failure to certify is not non-groundness. -/
def inspect (store : Store Cell) (memo : List (Term Cell)) : Nat → Term Cell → Summary Cell
  | 0, _ => ⟨false, []⟩
  | fuel + 1, term =>
      if term ∈ memo then ⟨true, []⟩
      else match term with
        | .literal _ => ⟨true, []⟩
        | .var cell => match store cell with
            | none => ⟨false, []⟩
            | some image => inspect store memo fuel image
        | .pair left right =>
            let l := inspect store memo fuel left
            let r := inspect store memo fuel right
            let closed := l.closed && r.closed
            ⟨closed, l.facts ++ r.facts ++ if closed then [term] else []⟩

theorem inspect_sound (store : Store Cell) (memo : List (Term Cell))
    (sound : MemoSound store memo) (fuel : Nat) (term : Term Cell) :
    ((inspect store memo fuel term).closed = true → Ground store term) ∧
    (∀ component ∈ (inspect store memo fuel term).facts, Ground store component) := by
  induction fuel generalizing term with
  | zero => simp [inspect]
  | succ fuel ih =>
      by_cases remembered : term ∈ memo
      · simpa [inspect, remembered] using sound term remembered
      · cases term with
        | literal flag => simpa [inspect, remembered] using Ground.literal (store := store) flag
        | var cell =>
            cases bound : store cell with
            | none => simp [inspect, remembered, bound]
            | some image =>
                have summary := ih image
                constructor
                · intro accepted
                  exact .boundCell bound (summary.1 (by simpa [inspect, remembered, bound] using accepted))
                · simpa [inspect, remembered, bound] using summary.2
        | pair left right =>
            have l := ih left
            have r := ih right
            simp only [inspect, if_neg remembered]
            constructor
            · intro accepted
              simp only [Bool.and_eq_true] at accepted
              exact .pair (l.1 accepted.1) (r.1 accepted.2)
            · intro component member
              rcases List.mem_append.mp member with prior | last
              · rcases List.mem_append.mp prior with hl | hr
                · exact l.2 component hl
                · exact r.2 component hr
              · split at last
                next closed =>
                  have same : component = Term.pair left right := by simpa using last
                  subst component
                  simp only [Bool.and_eq_true] at closed
                  exact .pair (l.1 closed.1) (r.1 closed.2)
                next => simp at last

/-- New memo entries are justified independently of whether the root closed. -/
theorem remember_sound (store : Store Cell) (memo : List (Term Cell))
    (sound : MemoSound store memo) (fuel : Nat) (term : Term Cell) :
    MemoSound store ((inspect store memo fuel term).facts ++ memo) := by
  intro component member
  rcases List.mem_append.mp member with fresh | prior
  · exact (inspect_sound store memo sound fuel term).2 component fresh
  · exact sound component prior

omit [DecidableEq Cell] in
theorem memo_forward {before after : Store Cell} (stable : Extends before after)
    {memo : List (Term Cell)} (sound : MemoSound before memo) : MemoSound after memo := by
  intro term member
  exact (sound term member).mono stable

structure CounterSummary (Cell : Type) where
  counter : Nat
  facts : List (Term Cell)

/-- A counter-based completion check. Unresolved shared nodes are conservative
barriers; their classification needs no semantic assumption. -/
def inspectCounter (store : Store Cell) (memo : List (Term Cell))
    (unresolved : Term Cell → Bool) : Nat → Term Cell → Nat → CounterSummary Cell
  | 0, _, before => ⟨before + 1, []⟩
  | fuel + 1, term, before =>
      if term ∈ memo then ⟨before, []⟩
      else if unresolved term then ⟨before + 1, []⟩
      else match term with
        | .literal _ => ⟨before, []⟩
        | .var cell => match store cell with
            | none => ⟨before + 1, []⟩
            | some image => inspectCounter store memo unresolved fuel image before
        | .pair left right =>
            let l := inspectCounter store memo unresolved fuel left before
            let r := inspectCounter store memo unresolved fuel right l.counter
            ⟨r.counter, l.facts ++ r.facts ++ if r.counter = before then [term] else []⟩

/-- Equality of a completion counter with its entry mark certifies the
component, independently of counter changes outside that component. -/
theorem inspectCounter_sound (store : Store Cell) (memo : List (Term Cell))
    (sound : MemoSound store memo) (unresolved : Term Cell → Bool)
    (fuel : Nat) (term : Term Cell) (before : Nat) :
    before ≤ (inspectCounter store memo unresolved fuel term before).counter ∧
    ((inspectCounter store memo unresolved fuel term before).counter = before →
      Ground store term) ∧
    (∀ component ∈ (inspectCounter store memo unresolved fuel term before).facts,
      Ground store component) := by
  induction fuel generalizing term before with
  | zero => simp [inspectCounter]
  | succ fuel ih =>
      by_cases remembered : term ∈ memo
      · simpa [inspectCounter, remembered] using sound term remembered
      · by_cases blocked : unresolved term = true
        · simp [inspectCounter, remembered, blocked]
        · have clear : unresolved term = false := by
            cases h : unresolved term <;> simp_all
          cases term with
          | literal flag =>
              simpa [inspectCounter, remembered, clear] using Ground.literal (store := store) flag
          | var cell =>
              cases bound : store cell with
              | none => simp [inspectCounter, remembered, clear, bound]
              | some image =>
                  have result := ih image before
                  refine ⟨?_, ?_, ?_⟩
                  · simpa [inspectCounter, remembered, clear, bound] using result.1
                  · intro same
                    exact .boundCell bound (result.2.1 (by
                      simpa [inspectCounter, remembered, clear, bound] using same))
                  · simpa [inspectCounter, remembered, clear, bound] using result.2.2
          | pair left right =>
              let l := inspectCounter store memo unresolved fuel left before
              let r := inspectCounter store memo unresolved fuel right l.counter
              have hl := ih left before
              have hr := ih right l.counter
              have ordered : before ≤ r.counter := Nat.le_trans hl.1 hr.1
              have completed : r.counter = before → Ground store (.pair left right) := by
                intro same
                have middle : l.counter = before :=
                  Nat.le_antisymm (same ▸ hr.1) hl.1
                exact .pair (hl.2.1 middle) (hr.2.1 (same.trans middle.symm))
              simp only [inspectCounter, if_neg remembered, clear, Bool.false_eq_true,
                ↓reduceIte]
              refine ⟨ordered, completed, ?_⟩
              intro component member
              rcases List.mem_append.mp member with prior | last
              · rcases List.mem_append.mp prior with inLeft | inRight
                · exact hl.2.2 component inLeft
                · exact hr.2.2 component inRight
              · split at last
                next same =>
                  have equal : component = Term.pair left right := by simpa using last
                  subst component
                  exact completed same
                next => simp at last

namespace Controls

def empty : Store Nat := fun _ => none
def closedPart : Term Nat := .pair (.literal false) (.literal true)
def openRoot : Term Nat := .pair closedPart (.var 0)

theorem open_root_not_certified : (inspect empty [] 4 openRoot).closed = false := by decide

theorem closed_component_retained :
    closedPart ∈ (inspect empty [] 4 openRoot).facts := by decide

theorem open_root_not_remembered :
    openRoot ∉ (inspect empty [] 4 openRoot).facts := by decide

theorem extracted_components_sound : MemoSound empty (inspect empty [] 4 openRoot).facts := by
  have sound : MemoSound empty [] := by intro term member; simp at member
  simpa using remember_sound empty [] sound 4 openRoot

def bound : Store Nat := fun cell => if cell = 0 then some (.literal false) else none
def laterGround : Term Nat := .pair (.var 0) (.literal false)

theorem earned_before_rollback : MemoSound bound [laterGround] := by
  intro term member
  have same : term = laterGround := by simpa using member
  subst term
  exact .pair (.boundCell (by simp [bound]) (.literal false)) (.literal false)

theorem rollback_invalidates : ¬ MemoSound empty [laterGround] := by
  intro sound
  have ground := sound laterGround (by simp)
  cases ground with
  | pair left _ =>
      cases left with
      | boundCell impossible _ => simp [empty] at impossible

end Controls
end Mettapedia.Machines.ComponentGroundCertificates
