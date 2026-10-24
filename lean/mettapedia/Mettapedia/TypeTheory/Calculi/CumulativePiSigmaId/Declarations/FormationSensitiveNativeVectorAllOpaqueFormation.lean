import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllUniverses
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveConstantInterpretation

/-!
# Native Vector All formation without declared computation

The common-upper declaration entries are retained exactly while their native
computation family is empty. Both existing All type programs are independently
checked at their original neutral inputs and universe bounds in this profile.
Core beta/projection conversion and universe comparison remain those of the
tower. The four-input context contains no pointwise predicate witness.

The profile includes into the existing computation-enabled signature. A native
Vector nil root separates their computation authority. These formation results
are the root-free input to subsequent parameter interpretation, not a transfer
to typed equality or a normalization result for the full native signature.
-/

set_option autoImplicit false
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel
open Presentation Declaration RussellTarski
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeVectorAll.Universes.CumulativeElimination (upperLevel)
namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes.OpaqueFormation

def signature : Signature Tower.Head where
  entries := NativeVectorAll.Universes.CumulativeElimination.signature.entries

abbrev rules := extendRules Tower.rules signature

theorem value_none (name : DeclName) : signature.valueOf? name = none := by
  change NativeVectorAll.Universes.CumulativeElimination.signature.valueOf? name = none
  simp only [LevelInstance.signature, Signature.valueOf_instantiateLevels,
    NativeNaturalVectorFamilies.rawSignature_valueOf_none, Option.map_none]

theorem root_free : ConstantSubstitution.RootFree rules.computation := by
  intro n left right root
  cases root with
  | inherited impossible => cases impossible
  | delta known => rw [value_none] at known; cases known
  | declared impossible => exact impossible.elim

def decoder : StructuralConversionCode.RootDecoder rules.computation :=
  DeclarationConversionCode.rootDecoder (base := Tower.rules) (signature := signature)
    (.ofEmpty _ rfl) (.ofEmpty _ rfl)

local instance : DecidableRel rules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred rules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (rules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel rules.cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))

local instance : DecidableRel rules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def choices : FormationSensitiveElaboration.Choices Tower.Head decoder.Code where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (Tower.rules.cumulative first second)
  normalize fuel term := match StructuralConversionSearch.normalize decoder (fun _ => none)
      (headEq := rules.headEq) fuel term with
    | none => term
    | some result => result.term
  conversion fuel left right := StructuralConversionSearch.compare decoder (fun _ => none)
    (headEq := rules.headEq) fuel left right

def lowerAccepted : Bool := (FormationSensitiveElaboration.elaborate rules decoder choices 128
  NativeVectorAll.Universes.context NativeVectorAll.Universes.subject
    (sortTm NativeVectorAll.Universes.resultLevel)).isSome

def upperAccepted : Bool := (FormationSensitiveElaboration.elaborate rules decoder choices 128
  NativeVectorAll.Universes.context
    (NativeVectorAll.Universes.Canonical.typeProgramAtUniverse upperLevel) (sortTm upperLevel)).isSome

theorem lower_accepted : lowerAccepted = true := by decide +kernel
theorem upper_accepted : upperAccepted = true := by decide +kernel

theorem lower_formed : FormationSensitive.Judgment rules NativeVectorAll.Universes.context
    NativeVectorAll.Universes.subject (sortTm NativeVectorAll.Universes.resultLevel) := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp lower_accepted
  exact FormationSensitiveElaboration.elaborate_sound rules decoder choices 128 _ _ _ submission produced

theorem upper_formed : FormationSensitive.Judgment rules NativeVectorAll.Universes.context
    (NativeVectorAll.Universes.Canonical.typeProgramAtUniverse upperLevel) (sortTm upperLevel) := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp upper_accepted
  exact FormationSensitiveElaboration.elaborate_sound rules decoder choices 128 _ _ _ submission produced

theorem includes : signature.Extends CumulativeElimination.signature where
  entries := fun known => known
  computation := fun impossible => impossible.elim

theorem lower_in_full : FormationSensitive.Judgment CumulativeElimination.rules Universes.context
    Universes.subject (sortTm resultLevel) := lower_formed.monoSignature includes

theorem upper_in_full : FormationSensitive.Judgment CumulativeElimination.rules Universes.context
    (Canonical.typeProgramAtUniverse upperLevel) (sortTm upperLevel) :=
  upper_formed.monoSignature includes

theorem full_nil_root {n : Nat} (element motive nilCase consCase : Tower.Tm n) :
    CumulativeElimination.rules.computation.step
      (NativeNaturalVectorFamilies.vecEliminateApp element motive nilCase consCase
        NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp element)) nilCase :=
  RootStep.declared ⟨NativeNaturalVectorFamilies.IotaEvidence.vecNil element motive nilCase consCase⟩

theorem opaque_nil_no_root {n : Nat} (element motive nilCase consCase : Tower.Tm n) :
    ¬ rules.computation.step
      (NativeNaturalVectorFamilies.vecEliminateApp element motive nilCase consCase
        NativeNaturalVectorFamilies.zeroTm (NativeNaturalVectorFamilies.vnilApp element)) nilCase :=
  fun step => root_free step

#print axioms lower_in_full
#print axioms upper_in_full
#print axioms full_nil_root
#print axioms opaque_nil_no_root

#print axioms root_free
#print axioms lower_formed
#print axioms upper_formed
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeVectorAll.Universes.OpaqueFormation
