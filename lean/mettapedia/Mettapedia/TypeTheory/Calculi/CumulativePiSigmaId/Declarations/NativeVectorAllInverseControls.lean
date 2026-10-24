import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeVectorAllInverse

/-!
# Neutral-vector controls for the All inverse program

The source context has unknown length, vector and supplied evidence. Both
universe directions instantiate the complete proof program there. The proof
has an eliminator application as syntax; the control does not claim raw
convertibility of its endpoints or equality reflection.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation TypedEquality

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllInverseControls
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeVectorIdentityComparison
open NativeVectorAllTypedMaps
open NativeVectorAllMapComputation
open NativeVectorAllMapInverse

def context (direction : Direction) : Tower.Ctx 5 :=
  .snoc NativeVectorAll.Universes.context
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) (.var 3) (.var 2) (.var 1) (.var 0))

theorem context_formed (direction : Direction) : Normalization.CtxFormed rules (context direction) :=
  .snoc all_context_formed ⟨_, .sort _, source_all_formed direction
    (context := NativeVectorAll.Universes.context) (element := .var 3) (predicate := .var 2)
    (number := .var 1) (vector := .var 0) (.var 3) (.var 2) (.var 1) (.var 0)⟩

theorem evidence_typed (direction : Direction) : Typed rules (context direction) (.var 0)
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) (.var 4) (.var 3) (.var 2) (.var 1)) := by
  have checked := Derivable.var (R := rules) (Γ := context direction) 0
  change Typed rules (context direction) (.var 0)
    (rename wk (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source direction) (.var 3) (.var 2) (.var 1) (.var 0))) at checked
  rw [NativeVectorAllInverseMotive.rename_all] at checked
  exact checked

theorem forward_neutral_inverse : Typed rules (context .forward)
    (NativeVectorAllInverse.inverse .forward (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
    (.id (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source .forward) (.var 4) (.var 3) (.var 2) (.var 1))
      (roundtrip .forward (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)) (.var 0)) :=
  NativeVectorAllInverse.inverse_typed .forward (context := context .forward)
    (element := .var 4) (predicate := .var 3) (number := .var 2) (vector := .var 1) (evidence := .var 0)
    (.var 4) (.var 3) (.var 2) (.var 1) (evidence_typed .forward)

theorem backward_neutral_inverse : Typed rules (context .backward)
    (NativeVectorAllInverse.inverse .backward (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
    (.id (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source .backward) (.var 4) (.var 3) (.var 2) (.var 1))
      (roundtrip .backward (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)) (.var 0)) :=
  NativeVectorAllInverse.inverse_typed .backward (context := context .backward)
    (element := .var 4) (predicate := .var 3) (number := .var 2) (vector := .var 1) (evidence := .var 0)
    (.var 4) (.var 3) (.var 2) (.var 1) (evidence_typed .backward)

theorem forward_nil_inverse : Typed rules (NativeVectorAllInverseMethods.nilContext .forward)
    (.refl (.var 0))
    (.id (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source .forward) (.var 4) (.var 3)
      NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp (.var 4)))
      (roundtrip .forward (.var 4) (.var 3) NativeNaturalVectorFamilies.zeroTm
        (NativeNaturalVectorFamilies.vnilApp (.var 4)) (.var 0)) (.var 0)) :=
  NativeVectorAllInverseMethods.nil_identity_at .forward (context := NativeVectorAllInverseMethods.nilContext .forward)
    (element := .var 4) (predicate := .var 3) (.var 4) (.var 3)
    (NativeVectorAllInverseMethods.nil_variable_typed .forward)

theorem forward_cons_context_formed :
    Normalization.CtxFormed rules (NativeVectorAllInverseMethods.bodyContext .forward) :=
  NativeVectorAllInverseMethods.body_context_formed .forward

theorem forward_cons_inverse :
    Typed rules (NativeVectorAllInverseMethods.bodyContext .forward) (NativeVectorAllInverseMethods.consBody .forward)
      (.id (consCarrier (source .forward) (.var 8) (.var 7) (.var 4) (.var 3) (.var 2))
        (roundtrip .forward (.var 8) (.var 7) (NativeNaturalVectorFamilies.succApp (.var 4))
          (NativeNaturalVectorFamilies.vconsApp (.var 8) (.var 4) (.var 3) (.var 2)) (.var 0)) (.var 0)) :=
  NativeVectorAllInverseMethods.cons_identity_at .forward
    (context := NativeVectorAllInverseMethods.bodyContext .forward)
    (element := .var 8) (predicate := .var 7) (number := .var 4) (head := .var 3) (tail := .var 2)
    (.var 8) (.var 7) (.var 4) (.var 3) (.var 2)
    (NativeVectorAllInverseMethods.body_evidence_typed .forward)
    (NativeVectorAllInverseMethods.body_hypothesis_typed .forward)

theorem forward_neutral_roundtrip_typed : Typed rules (context .forward)
    (roundtrip .forward (.var 4) (.var 3) (.var 2) (.var 1) (.var 0))
    (NativeVectorAll.Universes.Canonical.allTypeAtUniverse (source .forward) (.var 4) (.var 3) (.var 2) (.var 1)) :=
  roundtrip_typed .forward (context := context .forward)
    (element := .var 4) (predicate := .var 3) (number := .var 2) (vector := .var 1)
    (.var 4) (.var 3) (.var 2) (.var 1) (evidence_typed .forward)

theorem forward_cons_roundtrip : Equal rules (NativeVectorAllInverseMethods.bodyContext .forward)
    (roundtrip .forward (.var 8) (.var 7) (NativeNaturalVectorFamilies.succApp (.var 4))
      (NativeNaturalVectorFamilies.vconsApp (.var 8) (.var 4) (.var 3) (.var 2)) (.var 0))
    (.pair (.fst (.var 0)) (roundtrip .forward (.var 8) (.var 7) (.var 4) (.var 2) (.snd (.var 0))))
    (consCarrier (source .forward) (.var 8) (.var 7) (.var 4) (.var 3) (.var 2)) :=
  roundtrip_cons_equal .forward (context := NativeVectorAllInverseMethods.bodyContext .forward)
    (element := .var 8) (predicate := .var 7) (number := .var 4) (head := .var 3) (tail := .var 2)
    (.var 8) (.var 7) (.var 4) (.var 3) (.var 2)
    (NativeVectorAllInverseMethods.body_evidence_typed .forward)

theorem inverse_not_refl_syntax {n : Nat} (direction : Direction)
    (element predicate number vector evidence : Tower.Tm n) :
    NativeVectorAllInverse.inverse direction element predicate number vector evidence ≠ .refl evidence := by
  intro same
  cases same

#print axioms context_formed
#print axioms forward_neutral_inverse
#print axioms backward_neutral_inverse
#print axioms inverse_not_refl_syntax

end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAllInverseControls
