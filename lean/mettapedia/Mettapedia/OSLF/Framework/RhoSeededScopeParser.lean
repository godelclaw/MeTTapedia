import Mettapedia.OSLF.Framework.RhoSeededScopeInterpretation

/-!
# Recursive depth readout for actual seeded rho scopes

The recognizer reads the independent canonical syntax. It accepts the two
atomic names and binary bags of dropped accepted names, preserving repeated
children. Its depth calculation follows both children of a compound. The
subsequent correctness comparison concerns actual source equation classes.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoSeededScopeParser

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoCanonicalNamePairs RhoIntrinsicReadback
open RhoSchema.IntrinsicEncoding
open MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open RhoSeededScopeStages RhoSeededScopeInterpretation

def depth : Pattern → Option Nat
  | .apply "NQuote" [.apply "PZero" []] => some 0
  | .apply "NQuote" [.apply "POutput"
      [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []]] => some 0
  | .apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [first], .apply "PDrop" [second]] none] =>
      (depth first).bind fun firstDepth =>
        (depth second).map fun secondDepth => max firstDepth secondDepth + 1
  | _ => none
termination_by pattern => sizeOf pattern

theorem depth_null_seed : depth (encodeEquationClass (quote (zero []))) = some 0 := by
  change depth (.apply "NQuote" [.apply "PZero" []]) = some 0
  rw [depth]

theorem depth_output_seed : depth (encodeEquationClass (quote visible)) = some 0 := by
  change depth (.apply "NQuote" [.apply "POutput"
    [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []]]) = some 0
  rw [depth]

theorem depth_pair (first second : Pattern) :
    depth (.apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [first], .apply "PDrop" [second]] none]) =
      (depth first).bind fun firstDepth =>
        (depth second).map fun secondDepth => max firstDepth secondDepth + 1 := by
  rw [depth]

theorem canonicalize_pair (first second : Pattern) :
    canonicalize (.apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [first], .apply "PDrop" [second]] none]) =
      .apply "NQuote" [.collection .hashBag
        (sortPatterns [.apply "PDrop" [canonicalize first],
          .apply "PDrop" [canonicalize second]]) none] := by
  change normalizeQuote (collapseBag (normalizeBagElements
    [canonicalize (.apply "PDrop" [first]), canonicalize (.apply "PDrop" [second])])) = _
  rw [canonicalize_apply_general "PDrop" [first] (by simp),
    canonicalize_apply_general "PDrop" [second] (by simp)]
  change normalizeQuote (collapseBag (normalizeBagElements
    [.apply "PDrop" [canonicalize first], .apply "PDrop" [canonicalize second]])) = _
  rw [normalize_drop_pair]
  have length : 2 ≤ (sortPatterns [.apply "PDrop" [canonicalize first],
      .apply "PDrop" [canonicalize second]]).length := by
    rw [← (sortPatterns_perm _).length_eq]
    exact Nat.le_refl _
  rw [collapseBag_eq_bag_of_length_ge_two length]
  rfl

theorem depth_combine_some {first second : Name []} {firstDepth secondDepth : Nat}
    (left : depth (encodeEquationClass first) = some firstDepth)
    (right : depth (encodeEquationClass second) = some secondDepth) :
    depth (encodeEquationClass (combine first second)) = some (max firstDepth secondDepth + 1) := by
  rw [combine_encoding]
  rcases sort_pair_cases (.apply "PDrop" [encodeEquationClass first])
      (.apply "PDrop" [encodeEquationClass second]) with direct | swapped
  · rw [direct, depth_pair, left, right]
    rfl
  · rw [swapped, depth_pair, right, left]
    simp only [Option.bind_some, Option.map_some, Nat.max_comm]

theorem stage_depth_complete (limit : Nat) {name : Name []} (member : name ∈ stage limit) :
    ∃ actual, depth (encodeEquationClass name) = some actual ∧ actual ≤ limit := by
  induction limit generalizing name with
  | zero =>
    rcases (mem_seeds _).mp member with rfl | rfl
    · exact ⟨0, depth_null_seed, Nat.le_refl 0⟩
    · exact ⟨0, depth_output_seed, Nat.le_refl 0⟩
  | succ limit ih =>
    rcases (mem_stage_succ _ _).mp member with rfl | rfl |
      ⟨first, second, firstMember, secondMember, rfl⟩
    · exact ⟨0, depth_null_seed, Nat.zero_le _⟩
    · exact ⟨0, depth_output_seed, Nat.zero_le _⟩
    · obtain ⟨firstDepth, left, leftBound⟩ := ih firstMember
      obtain ⟨secondDepth, right, rightBound⟩ := ih secondMember
      exact ⟨max firstDepth secondDepth + 1, depth_combine_some left right,
        Nat.add_le_add_right (max_le leftBound rightBound) 1⟩

theorem pattern_depth_sound (pattern : Pattern) : ∀ actual,
    depth pattern = some actual → ∃ name : Name [],
      name ∈ stage actual ∧ encodeEquationClass name = canonicalize pattern := by
  induction pattern using depth.induct with
  | case1 =>
    intro actual readout
    rw [depth] at readout
    have equal : actual = 0 := (Option.some.inj readout).symm
    subst actual
    exact ⟨quote (zero []), (mem_seeds _).mpr (Or.inl rfl), rfl⟩
  | case2 =>
    intro actual readout
    rw [depth] at readout
    have equal : actual = 0 := (Option.some.inj readout).symm
    subst actual
    exact ⟨quote visible, (mem_seeds _).mpr (Or.inr rfl), rfl⟩
  | case3 first second firstIH secondIH =>
    intro actual readout
    rw [depth_pair] at readout
    obtain ⟨firstDepth, firstReadout, secondReadout⟩ := Option.bind_eq_some_iff.mp readout
    obtain ⟨secondDepth, secondReadout, depthEqual⟩ := Option.map_eq_some_iff.mp secondReadout
    obtain ⟨firstName, firstMember, firstEncoding⟩ := firstIH _ firstReadout
    obtain ⟨secondName, secondMember, secondEncoding⟩ := secondIH _ secondReadout
    subst actual
    refine ⟨combine firstName secondName, (mem_stage_succ _ _).mpr
      (Or.inr (Or.inr ⟨firstName, secondName,
        stage_monotone (Nat.le_max_left _ _) firstMember,
        stage_monotone (Nat.le_max_right _ _) secondMember, rfl⟩)), ?_⟩
    rw [combine_encoding, canonicalize_pair, firstEncoding, secondEncoding]
  | case4 pattern notNull notOutput notPair =>
    intro actual readout
    rw [depth] at readout
    · cases readout
    · exact notNull
    · exact notOutput
    · exact notPair

theorem class_depth_sound {name : Name []} {actual : Nat}
    (readout : depth (encodeEquationClass name) = some actual) : name ∈ stage actual := by
  obtain ⟨decoded, member, encoded⟩ := pattern_depth_sound _ actual readout
  rw [encoded_class_canonical] at encoded
  have same := canonical_encoding_injective [] Srt.nm encoded
  exact same ▸ member

theorem depth_stage_iff (name : Name []) (limit : Nat) :
    name ∈ stage limit ↔ ∃ actual,
      depth (encodeEquationClass name) = some actual ∧ actual ≤ limit :=
  ⟨stage_depth_complete limit, fun ⟨_, readout, bound⟩ =>
    stage_monotone bound (class_depth_sound readout)⟩

theorem depth_is_minimum {name : Name []} {actual : Nat}
    (readout : depth (encodeEquationClass name) = some actual) (limit : Nat) :
    name ∈ stage limit ↔ actual ≤ limit := by
  rw [depth_stage_iff]
  constructor
  · rintro ⟨candidate, otherReadout, bound⟩
    have same : actual = candidate := Option.some.inj (readout.symm.trans otherReadout)
    exact same ▸ bound
  · intro bound
    exact ⟨actual, readout, bound⟩

theorem depth_none_iff (name : Name []) :
    depth (encodeEquationClass name) = none ↔ ¬ finiteScope name := by
  constructor
  · intro absent ⟨limit, member⟩
    obtain ⟨_, readout, _⟩ := stage_depth_complete limit member
    rw [absent] at readout
    cases readout
  · intro excluded
    cases readout : depth (encodeEquationClass name) with
    | none => rfl
    | some actual => exact (excluded ⟨actual, class_depth_sound readout⟩).elim

theorem depth_actual_scope_iff (env : RhoScopeExpression.Environment []) (name : Name []) :
    (depth (encodeEquationClass name)).isSome ↔ RhoScopeExpression.denote RhoScopeSeedReadings.atoms
      RhoScopeSeedReadings.seeded env name := by
  rw [seeded_membership_iff]
  constructor
  · intro accepted
    cases readout : depth (encodeEquationClass name) with
    | none => simp [readout] at accepted
    | some actual => exact ⟨actual, class_depth_sound readout⟩
  · rintro ⟨limit, member⟩
    obtain ⟨actual, readout, _⟩ := stage_depth_complete limit member
    simp only [readout, Option.isSome_some]

def scopeDecision (name : Name []) : Decidable (finiteScope name) :=
  match readout : depth (encodeEquationClass name) with
  | some actual => isTrue ⟨actual, class_depth_sound readout⟩
  | none => isFalse ((depth_none_iff name).mp readout)

def stageDecision (name : Name []) (limit : Nat) : Decidable (name ∈ stage limit) :=
  match readout : depth (encodeEquationClass name) with
  | some actual =>
      if bound : actual ≤ limit then
        isTrue ((depth_is_minimum readout limit).mpr bound)
      else isFalse (fun member => bound ((depth_is_minimum readout limit).mp member))
  | none => isFalse (fun member => (depth_none_iff name).mp readout ⟨limit, member⟩)

end Mettapedia.OSLF.Framework.RhoSeededScopeParser
