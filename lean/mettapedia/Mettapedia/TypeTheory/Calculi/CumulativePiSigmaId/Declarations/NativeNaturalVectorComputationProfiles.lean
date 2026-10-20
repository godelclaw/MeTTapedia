import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.NativeNaturalVectorProgramChecking

/-!
# Different computation requirements for checking and using append

Every selection retains the same declarations, heads and universe instance.
Only permissions for the four original iota rows change. The independently
emitted append evidence checks with the two natural rows alone; removing
either required row makes that submission fail. The vector rows remain
separately available for computation of eliminator applications.

These are actual restrictions with inclusions into the original calculus.
They establish no globally smallest checker, proof-fragment conservativity,
normalization, uniform computation admission or native performance guarantee.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
namespace Programs.ComputationProfiles

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation

abbrev Selection := Fin Checking.table.length → Bool

def signature (enabled : Selection) : Declaration.Signature Tower.Head :=
  { Programs.signature with computation := SchemaTableConversionCode.root Checking.table enabled }

abbrev rules (enabled : Selection) := Declaration.extendRules Tower.rules (signature enabled)

def decoder (enabled : Selection) : StructuralConversionCode.RootDecoder (rules enabled).computation :=
  DeclarationConversionCode.rootDecoder
    (base := Tower.rules) (signature := signature enabled)
    (.ofEmpty _ rfl) (SchemaTableConversionCode.rootDecoder Checking.table enabled)

/-- The original declaration identity survives; only its permitted roots
are restricted. The source's independently defined iota witnesses justify
the inclusion. -/
theorem includes_original (enabled : Selection) : (signature enabled).Extends Programs.signature where
  entries := fun selected => selected
  computation := by
    intro n left right step
    obtain ⟨evidence⟩ := step
    exact ⟨Declaration.IndexedFamily.Checking.realizeEvidence Checking.schemas evidence⟩

theorem permissions_mono {small large : Selection}
    (included : ∀ index, small index = true → large index = true) :
    (signature small).Extends (signature large) where
  entries := fun selected => selected
  computation := SchemaTableConversionCode.root_mono included

theorem judgment_inclusion (enabled : Selection) {n : Nat} {context : Tower.Ctx n}
    {term type : Tower.Tm n} (judgment : FormationSensitive.Judgment (rules enabled) context term type) :
    FormationSensitive.Judgment Programs.rules context term type := by
  change FormationSensitive.Judgment
    (Declaration.extendRules Tower.rules Programs.signature) context term type
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
    judgment.mapHead (Declaration.extensionMorphism Tower.rules (includes_original enabled))

local instance (enabled : Selection) : DecidableRel (rules enabled).headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance (enabled : Selection) : DecidablePred (rules enabled).isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance (enabled : Selection) : ∀ u v w, Decidable ((rules enabled).join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance (enabled : Selection) : DecidableRel (rules enabled).cumulative :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.cumulative h u))
local instance (enabled : Selection) : DecidableRel (rules enabled).headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

def replay (enabled : Selection) : Bool :=
  FormationSensitiveElaboration.replay (rules enabled) (decoder enabled)
    .nil appendTerm appendType appendEvidence

def naturalOnly (index : Fin Checking.table.length) : Bool := decide (index.val < 2)
def zeroOnly (index : Fin Checking.table.length) : Bool := index.val == 0
def succOnly (index : Fin Checking.table.length) : Bool := index.val == 1

theorem append_checked_naturalOnly : replay naturalOnly = true := by decide +kernel

/-- The same full dependent program is typed by the actual smaller policy.
This replays the existing evidence; it is not merely a predicate on a
higher-policy typing proof supplied by the caller. -/
theorem append_typed_naturalOnly :
    FormationSensitive.Judgment (rules naturalOnly) .nil appendTerm appendType :=
  FormationSensitiveElaboration.replay_sound _ _ append_checked_naturalOnly

def vectorNilCode : (decoder naturalOnly).Code 0 :=
  .declared ⟨2, [.const `consCase, .const `nilCase, .const `motive, .const `element]⟩

def verdicts : List (String × Bool) := [
  ("append typing checks with natural iota only", replay naturalOnly),
  ("append typing evidence needs natural successor", !(replay zeroOnly)),
  ("append typing evidence needs natural zero", !(replay succOnly)),
  ("append typing evidence refuses no iota", !(replay (fun _ => false))),
  ("append typing also checks with all four iota rows", replay (fun _ => true)),
  ("natural-only policy refuses vector nil citation", ((decoder naturalOnly).decode vectorNilCode).isNone),
  ("full policy replays the same vector nil citation", ((decoder (fun _ => true)).decode vectorNilCode).isSome)]

theorem all_verdicts : verdicts.all (·.2) = true := by decide +kernel

end Programs.ComputationProfiles
end Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.NativeNaturalVectorFamilies
