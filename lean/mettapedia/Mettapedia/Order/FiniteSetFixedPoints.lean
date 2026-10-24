import Mettapedia.Order.PredicateFixedPointEncodings
import Mathlib.Data.Set.Card
import Mathlib.Order.Hom.Set
import Mathlib.Order.Iterate

/-!
# Finite fixed points, approximation stages, and De Morgan duality

Iteration from `∅` discovers the least fixed point; iteration from `Set.univ`
eliminates states outside the greatest. Complementation identifies elimination
with discovery for the De Morgan dual operator, including the first such stage.
On a finite carrier both sequences stabilize within `Nat.card S` rounds.
A repeated approximation certifies the answer even before that bound.

Ranks count rounds of a monotone set operator, not the work of implementing a
round. The quantified predicates and executable finite-set strategies remain
separate interpretations of these fixed points.
-/

namespace Mettapedia.Order.FiniteSetFixedPoints

variable {S : Type*}

/-- Iteration commutes with De Morgan duality.  The empty/universal fixed-point
approximations are the two boundary instances of this generic semiconjugacy
fact. -/
theorem iterate_dual
    (original dual : Set S → Set S)
    (dualEq : ∀ states, dual states = (original statesᶜ)ᶜ)
    (index : Nat) (states : Set S) :
    dual^[index] statesᶜ = (original^[index] states)ᶜ := by
  have semiconjugate : Function.Semiconj (fun states : Set S => statesᶜ)
      original dual := by
    intro states
    rw [dualEq]
    simp
  exact (semiconjugate.iterate_right index states).symm

/-- An increasing chain of subsets of a finite carrier that stays constant
after its first repeated step has stabilized by `Nat.card S`. -/
theorem monotone_chain_stabilizes_at_card [Finite S]
    (chain : Nat → Set S) (monotone : Monotone chain)
    (stable : ∀ index,
      chain index = chain (index + 1) →
        chain (index + 1) = chain (index + 2)) :
    chain (Nat.card S) = chain (Nat.card S + 1) := by
  have cardinalityMonotone : Monotone fun index => (chain index).ncard := by
    intro left right ordered
    exact Set.ncard_le_ncard (monotone ordered) (Set.toFinite _)
  have cardinalityBound : ∀ index, (chain index).ncard ≤ Nat.card S :=
    fun index => (chain index).ncard_le_card
  have cardinalityStable : ∀ index,
      (chain index).ncard = (chain (index + 1)).ncard →
        (chain (index + 1)).ncard = (chain (index + 2)).ncard := by
    intro index equalCardinality
    have equalSets : chain index = chain (index + 1) :=
      Set.eq_of_subset_of_ncard_le (monotone (by omega))
        (by omega) (Set.toFinite _)
    exact congrArg Set.ncard (stable index equalSets)
  have equalCardinality := Nat.stabilises_of_monotone
    cardinalityMonotone cardinalityBound cardinalityStable
    (show Nat.card S ≤ Nat.card S + 1 by omega)
  exact Set.eq_of_subset_of_ncard_le (monotone (by omega))
    (by omega) (Set.toFinite _)

/-- A decreasing chain obeying the same stability condition has also
stabilized by `Nat.card S`. -/
theorem antitone_chain_stabilizes_at_card [Finite S]
    (chain : Nat → Set S) (antitone : Antitone chain)
    (stable : ∀ index,
      chain index = chain (index + 1) →
        chain (index + 1) = chain (index + 2)) :
    chain (Nat.card S) = chain (Nat.card S + 1) := by
  apply compl_inj_iff.mp
  exact monotone_chain_stabilizes_at_card (fun index => (chain index)ᶜ)
    (fun _ _ ordered => Set.compl_subset_compl.mpr (antitone ordered))
    (fun index equal => congrArg (fun states : Set S => statesᶜ)
      (stable index (compl_inj_iff.mp equal)))

/-- The monotone operator whose discoveries are the original operator's eliminations. -/
def deMorganDual (transformer : Set S →o Set S) : Set S →o Set S where
  toFun states := (transformer statesᶜ)ᶜ
  monotone' _ _ subset := compl_le_compl (transformer.monotone (compl_le_compl subset))

variable (transformer : Set S →o Set S)

@[simp] theorem deMorganDual_apply (states : Set S) :
    deMorganDual transformer states = (transformer statesᶜ)ᶜ := rfl

@[simp] theorem deMorganDual_involutive : deMorganDual (deMorganDual transformer) = transformer := by
  ext states
  simp only [deMorganDual_apply, compl_compl]

@[simp] theorem lfp_deMorganDual : (deMorganDual transformer).lfp = transformer.gfpᶜ := by
  exact (FixedPointTransport.gfp_comparison (OrderIso.compl (Set S)) transformer
    (deMorganDual transformer).dual (by
      intro states
      change (transformer states)ᶜ = (transformer statesᶜᶜ)ᶜ
      rw [compl_compl])).symm

/-- The increasing approximation sequence for a least fixed point. -/
def lowerApproximation (index : Nat) : Set S := transformer^[index] ∅

/-- The decreasing approximation sequence for a greatest fixed point. -/
def upperApproximation (index : Nat) : Set S := transformer^[index] Set.univ

@[simp] theorem lowerApproximation_zero : lowerApproximation transformer 0 = ∅ := rfl

@[simp] theorem lowerApproximation_succ (index : Nat) :
    lowerApproximation transformer (index + 1) = transformer (lowerApproximation transformer index) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem upperApproximation_zero : upperApproximation transformer 0 = Set.univ := rfl

@[simp] theorem upperApproximation_succ (index : Nat) :
    upperApproximation transformer (index + 1) = transformer (upperApproximation transformer index) :=
  Function.iterate_succ_apply' _ _ _

@[simp] theorem lowerApproximation_deMorganDual (index : Nat) :
    lowerApproximation (deMorganDual transformer) index = (upperApproximation transformer index)ᶜ := by
  simpa only [lowerApproximation, upperApproximation, Set.compl_univ] using
    iterate_dual transformer (deMorganDual transformer) (fun _ => rfl) index Set.univ

theorem lowerApproximation_mono : Monotone (lowerApproximation transformer) :=
  transformer.monotone.monotone_iterate_of_le_map bot_le

theorem upperApproximation_antitone : Antitone (upperApproximation transformer) :=
  transformer.monotone.antitone_iterate_of_map_le le_top

/-- Every lower approximation lies below the least fixed point. -/
theorem lowerApproximation_le_lfp (index : Nat) :
    lowerApproximation transformer index ≤ transformer.lfp :=
  (transformer.monotone.iterate index bot_le).trans_eq (transformer.isFixedPt_lfp.iterate index)

/-- The greatest fixed point lies below every upper approximation. -/
theorem gfp_le_upperApproximation (index : Nat) :
    transformer.gfp ≤ upperApproximation transformer index := by
  simpa only [lowerApproximation_deMorganDual, lfp_deMorganDual, compl_le_compl_iff_le] using
    lowerApproximation_le_lfp (deMorganDual transformer) index

/-- Equality of successive lower approximations certifies the least fixed point. -/
theorem lfp_eq_lowerApproximation_of_stable (index : Nat)
    (stable : lowerApproximation transformer index = lowerApproximation transformer (index + 1)) :
    transformer.lfp = lowerApproximation transformer index :=
  le_antisymm (transformer.lfp_le_fixed ((lowerApproximation_succ transformer index).symm.trans
    stable.symm)) (lowerApproximation_le_lfp transformer index)

/-- Equality of successive upper approximations certifies the greatest fixed point. -/
theorem gfp_eq_upperApproximation_of_stable (index : Nat)
    (stable : upperApproximation transformer index = upperApproximation transformer (index + 1)) :
    transformer.gfp = upperApproximation transformer index := by
  have dualStable := congrArg (fun states : Set S => statesᶜ) stable
  simpa only [lowerApproximation_deMorganDual, lfp_deMorganDual, compl_inj_iff] using
    lfp_eq_lowerApproximation_of_stable (deMorganDual transformer) index
      (by simpa only [lowerApproximation_deMorganDual] using dualStable)

section Finite

variable [Finite S]

/-- The least fixed point is reached within the carrier-cardinality bound. -/
theorem lfp_eq_iterate_empty :
    transformer.lfp = transformer^[Nat.card S] (∅ : Set S) := by
  apply lfp_eq_lowerApproximation_of_stable
  exact monotone_chain_stabilizes_at_card (lowerApproximation transformer)
    (lowerApproximation_mono transformer) (fun index equal => by
      simpa only [lowerApproximation_succ] using congrArg transformer equal)

/-- The greatest fixed point satisfies the same bound, by De Morgan duality. -/
theorem gfp_eq_iterate_univ :
    transformer.gfp = transformer^[Nat.card S] (Set.univ : Set S) := by
  change transformer.gfp = upperApproximation transformer (Nat.card S)
  have bound : (deMorganDual transformer).lfp =
      lowerApproximation (deMorganDual transformer) (Nat.card S) :=
    lfp_eq_iterate_empty (deMorganDual transformer)
  simpa only [lfp_deMorganDual, lowerApproximation_deMorganDual, compl_inj_iff] using bound

/-! ## Canonical finite semantic ranks -/

variable (state : S)

/-- Every member enters the lower approximation sequence by the cardinality bound. -/
theorem exists_lowerApproximation_of_mem_lfp (member : state ∈ transformer.lfp) :
    ∃ index, state ∈ lowerApproximation transformer index :=
  ⟨Nat.card S, by simpa [lowerApproximation, ← lfp_eq_iterate_empty transformer] using member⟩

/-- The first discovery stage. Stage zero is empty, so every entry rank is positive. -/
noncomputable def lfpEntryRank (member : state ∈ transformer.lfp) : Nat := by
  classical
  exact Nat.find (exists_lowerApproximation_of_mem_lfp transformer state member)

theorem lfpEntryRank_mem (member : state ∈ transformer.lfp) :
    state ∈ lowerApproximation transformer (lfpEntryRank transformer state member) := by
  classical
  exact Nat.find_spec (exists_lowerApproximation_of_mem_lfp transformer state member)

theorem lfpEntryRank_min (member : state ∈ transformer.lfp) {index : Nat}
    (atIndex : state ∈ lowerApproximation transformer index) :
    lfpEntryRank transformer state member ≤ index := by
  classical
  exact Nat.find_min' (exists_lowerApproximation_of_mem_lfp transformer state member) atIndex

theorem lfpEntryRank_le_card (member : state ∈ transformer.lfp) :
    lfpEntryRank transformer state member ≤ Nat.card S := by
  apply lfpEntryRank_min
  simpa [lowerApproximation, ← lfp_eq_iterate_empty transformer] using member

theorem lfpEntryRank_pos (member : state ∈ transformer.lfp) :
    0 < lfpEntryRank transformer state member := by
  have enters := lfpEntryRank_mem transformer state member
  apply Nat.pos_of_ne_zero
  intro zero
  simp [zero] at enters

/-- Every excluded state is eliminated from the upper approximation sequence. -/
theorem exists_not_mem_upperApproximation_of_not_mem_gfp (missing : state ∉ transformer.gfp) :
    ∃ index, state ∉ upperApproximation transformer index := by
  simpa only [lowerApproximation_deMorganDual, Set.mem_compl_iff] using
    exists_lowerApproximation_of_mem_lfp (deMorganDual transformer) state (by simpa using missing)

/-- The first elimination stage, computed as a discovery stage in the dual. -/
noncomputable def gfpExitRank (missing : state ∉ transformer.gfp) : Nat :=
  lfpEntryRank (deMorganDual transformer) state (by simpa using missing)

theorem gfpExitRank_not_mem (missing : state ∉ transformer.gfp) :
    state ∉ upperApproximation transformer (gfpExitRank transformer state missing) := by
  simpa only [gfpExitRank, lowerApproximation_deMorganDual, Set.mem_compl_iff] using
    lfpEntryRank_mem (deMorganDual transformer) state (by simpa using missing)

theorem gfpExitRank_min (missing : state ∉ transformer.gfp) {index : Nat}
    (notAtIndex : state ∉ upperApproximation transformer index) :
    gfpExitRank transformer state missing ≤ index :=
  lfpEntryRank_min (deMorganDual transformer) state (by simpa using missing) (by simpa using notAtIndex)

theorem gfpExitRank_le_card (missing : state ∉ transformer.gfp) :
    gfpExitRank transformer state missing ≤ Nat.card S :=
  lfpEntryRank_le_card (deMorganDual transformer) state (by simpa using missing)

theorem gfpExitRank_pos (missing : state ∉ transformer.gfp) :
    0 < gfpExitRank transformer state missing :=
  lfpEntryRank_pos (deMorganDual transformer) state (by simpa using missing)

/-- The dual rank is exactly the original least elimination index. -/
theorem gfpExitRank_eq_find (missing : state ∉ transformer.gfp) :
    gfpExitRank transformer state missing = (by
      classical
      exact Nat.find (exists_not_mem_upperApproximation_of_not_mem_gfp transformer state missing)) := by
  classical
  apply Nat.find_congr'
  intro index
  simp only [lowerApproximation_deMorganDual, Set.mem_compl_iff]

end Finite

/-! ## Executable boundary examples -/

namespace Canary

def forceUnit : Set Unit →o Set Unit := OrderHom.const _ Set.univ

def eraseUnit : Set Unit →o Set Unit := OrderHom.const _ ∅

theorem forceUnit_lfp : forceUnit.lfp = Set.univ := by
  simpa [forceUnit] using lfp_eq_iterate_empty forceUnit

theorem eraseUnit_gfp : eraseUnit.gfp = ∅ := by
  simpa [eraseUnit] using gfp_eq_iterate_univ eraseUnit

theorem forceUnit_entryRank :
    lfpEntryRank forceUnit () (by simp [forceUnit_lfp]) = 1 := by
  apply Nat.le_antisymm
  · simpa only [Nat.card_unique] using
      lfpEntryRank_le_card forceUnit () (by simp [forceUnit_lfp])
  · exact lfpEntryRank_pos forceUnit () (by simp [forceUnit_lfp])

theorem eraseUnit_exitRank :
    gfpExitRank eraseUnit () (by simp [eraseUnit_gfp]) = 1 := by
  have dual : deMorganDual eraseUnit = forceUnit := by
    ext states x
    simp [eraseUnit, forceUnit]
  simpa only [gfpExitRank, dual] using forceUnit_entryRank

/-- On an empty carrier both endpoints are reached at round zero. -/
theorem empty_carrier (operator : Set Empty →o Set Empty) :
    operator.lfp = lowerApproximation operator 0 ∧ operator.gfp = upperApproximation operator 0 :=
  ⟨Subsingleton.elim _ _, Subsingleton.elim _ _⟩

/-- A nonempty carrier need not require even one round. -/
theorem identity_stops_at_zero :
    (OrderHom.id : Set Unit →o Set Unit).lfp = ∅ ∧ OrderHom.id.gfp = (Set.univ : Set Unit) :=
  ⟨lfp_eq_lowerApproximation_of_stable _ 0 rfl, gfp_eq_upperApproximation_of_stable _ 0 rfl⟩

/-- Complement oscillates; its failure of monotonicity is essential. -/
theorem complement_not_monotone : ¬ Monotone (fun states : Set Unit => statesᶜ) := by
  intro monotone
  have impossible := monotone (Set.empty_subset (Set.univ : Set Unit))
  simp at impossible

theorem complement_two_rounds :
    (compl : Set Unit → Set Unit)^[2] ∅ = ∅ ∧ (∅ : Set Unit)ᶜ ≠ ∅ := by simp

def delayedChain (index : Nat) : Set Unit := { _state | 2 ≤ index }

/-- Monotonicity alone permits a plateau before a later change. -/
theorem delayed_chain_not_stable :
    Monotone delayedChain ∧ delayedChain 0 = delayedChain 1 ∧ delayedChain 1 ≠ delayedChain 2 := by
  refine ⟨fun _ _ ordered _ member => member.trans ordered, ?_, ?_⟩ <;>
    simp [delayedChain, Set.empty_ne_univ]

end Canary

end Mettapedia.Order.FiniteSetFixedPoints
