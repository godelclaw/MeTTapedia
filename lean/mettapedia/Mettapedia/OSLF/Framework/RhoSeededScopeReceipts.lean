import Mettapedia.OSLF.Framework.RhoSeededScopeParser

/-!
# Retained derivations and constructive receipts for the seeded rho scope

An ordered derivation retains each atomic premise and both child positions.
Its interpretation is an actual source name class. Recognition constructs
that derivation as data; the interpretation proof earns a dependent receipt
for the supplied equation class. Equal names need not have equal receipts.
Their generation depths nevertheless agree, as proved through the independent
finite-stage characterization and the canonical depth readout.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Framework.RhoSeededScopeReceipts

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoCanonicalNamePairs RhoIntrinsicReadback
open RhoSchema.IntrinsicEncoding
open MeTTaIL.Syntax
open Mettapedia.Languages.ProcessCalculi.RhoCalculus.Canonical
open RhoSeededScopeStages RhoSeededScopeInterpretation RhoSeededScopeParser

inductive Derivation where
  | nullSeed
  | outputSeed
  | pair (first second : Derivation)
  deriving DecidableEq

def Derivation.readout : Derivation → Name []
  | .nullSeed => quote (zero [])
  | .outputSeed => quote visible
  | .pair first second => combine first.readout second.readout

def Derivation.height : Derivation → Nat
  | .nullSeed | .outputSeed => 0
  | .pair first second => max first.height second.height + 1

def Derivation.atomicOrigins : Derivation → List (Name [])
  | .nullSeed => [quote (zero [])]
  | .outputSeed => [quote visible]
  | .pair first second => first.atomicOrigins ++ second.atomicOrigins

theorem Derivation.depth_readout (derivation : Derivation) :
    depth (encodeEquationClass derivation.readout) = some derivation.height := by
  induction derivation with
  | nullSeed => exact depth_null_seed
  | outputSeed => exact depth_output_seed
  | pair first second firstIH secondIH => exact depth_combine_some firstIH secondIH

theorem Derivation.stage_member (derivation : Derivation) :
    derivation.readout ∈ stage derivation.height := class_depth_sound derivation.depth_readout

theorem Derivation.height_eq_of_readout_eq {first second : Derivation}
    (same : first.readout = second.readout) : first.height = second.height := by
  have left := first.depth_readout
  rw [same] at left
  exact Option.some.inj (left.symm.trans second.depth_readout)

def recognize : Pattern → Option Derivation
  | .apply "NQuote" [.apply "PZero" []] => some .nullSeed
  | .apply "NQuote" [.apply "POutput"
      [.apply "NQuote" [.apply "PZero" []], .apply "PZero" []]] => some .outputSeed
  | .apply "NQuote" [.collection .hashBag
      [.apply "PDrop" [first], .apply "PDrop" [second]] none] =>
      (recognize first).bind fun firstDerivation =>
        (recognize second).map fun secondDerivation => .pair firstDerivation secondDerivation
  | _ => none
termination_by pattern => sizeOf pattern

theorem recognize_depth (pattern : Pattern) :
    (recognize pattern).map Derivation.height = depth pattern := by
  induction pattern using recognize.induct with
  | case1 => rw [recognize, depth]; rfl
  | case2 => rw [recognize, depth]; rfl
  | case3 first second firstIH secondIH =>
    rw [recognize, depth_pair, ← firstIH, ← secondIH]
    cases recognize first <;> cases recognize second <;> rfl
  | case4 pattern notNull notOutput notPair =>
    rw [recognize, depth]
    · rfl
    all_goals assumption

theorem recognize_encoding (pattern : Pattern) : ∀ derivation,
    recognize pattern = some derivation →
      encodeEquationClass derivation.readout = canonicalize pattern := by
  induction pattern using recognize.induct with
  | case1 =>
    intro derivation readout
    rw [recognize] at readout
    have same : derivation = .nullSeed := (Option.some.inj readout).symm
    subst derivation
    rfl
  | case2 =>
    intro derivation readout
    rw [recognize] at readout
    have same : derivation = .outputSeed := (Option.some.inj readout).symm
    subst derivation
    rfl
  | case3 first second firstIH secondIH =>
    intro derivation readout
    rw [recognize] at readout
    obtain ⟨firstDerivation, firstReadout, secondReadout⟩ := Option.bind_eq_some_iff.mp readout
    obtain ⟨secondDerivation, rightRecognized, same⟩ := Option.map_eq_some_iff.mp secondReadout
    subst derivation
    change encodeEquationClass (combine firstDerivation.readout secondDerivation.readout) = _
    rw [combine_encoding, canonicalize_pair, firstIH _ firstReadout, secondIH _ rightRecognized]
  | case4 pattern notNull notOutput notPair =>
    intro derivation readout
    rw [recognize] at readout
    · cases readout
    all_goals assumption

def Receipt (name : Name []) := {derivation : Derivation // derivation.readout = name}

theorem recognize_class_readout {name : Name []} {derivation : Derivation}
    (readout : recognize (encodeEquationClass name) = some derivation) : derivation.readout = name := by
  apply canonical_encoding_injective [] Srt.nm
  exact (recognize_encoding _ _ readout).trans (encoded_class_canonical name)

def receipt? (name : Name []) : Option (Receipt name) :=
  match readout : recognize (encodeEquationClass name) with
  | none => none
  | some derivation => some ⟨derivation, recognize_class_readout readout⟩

theorem receipt?_isSome (name : Name []) :
    (receipt? name).isSome = (depth (encodeEquationClass name)).isSome := by
  unfold receipt?
  rw [← recognize_depth]
  split <;> simp_all
  rfl

theorem receipt?_none_iff (name : Name []) : receipt? name = none ↔ ¬ finiteScope name := by
  rw [← depth_none_iff]
  have same := receipt?_isSome name
  cases left : receipt? name <;> cases right : depth (encodeEquationClass name) <;> simp_all

theorem receipt_depth_readout (name : Name []) (receipt : Receipt name) :
    depth (encodeEquationClass name) = some receipt.val.height := by
  have same := receipt.val.depth_readout
  rw [receipt.property] at same
  exact same

theorem receipt_depth_is_minimum (name : Name []) (receipt : Receipt name) (limit : Nat) :
    name ∈ stage limit ↔ receipt.val.height ≤ limit := by
  have same := receipt.val.depth_readout
  rw [receipt.property] at same
  exact depth_is_minimum same limit

theorem receipt_actual_scope (name : Name []) (receipt : Receipt name)
    (env : RhoScopeExpression.Environment []) :
    RhoScopeExpression.denote RhoScopeSeedReadings.atoms RhoScopeSeedReadings.seeded env name := by
  apply stage_members_are_actual_scope env receipt.val.height
  have member := receipt.val.stage_member
  rw [receipt.property] at member
  exact member

theorem ordered_pair_readouts_agree :
    (Derivation.pair .nullSeed .outputSeed).readout =
      (Derivation.pair .outputSeed .nullSeed).readout := combine_commutes _ _

theorem ordered_pair_derivations_differ :
    Derivation.pair .nullSeed .outputSeed ≠ .pair .outputSeed .nullSeed := by
  intro same
  cases same

theorem ordered_pair_origins_differ :
    (Derivation.pair .nullSeed .outputSeed).atomicOrigins ≠
      (Derivation.pair .outputSeed .nullSeed).atomicOrigins := by
  intro same
  exact RhoScopeSeedReadings.seed_names_distinct (List.cons.inj same).1

end Mettapedia.OSLF.Framework.RhoSeededScopeReceipts
