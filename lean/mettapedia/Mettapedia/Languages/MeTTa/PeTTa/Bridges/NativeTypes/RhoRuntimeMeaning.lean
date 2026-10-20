import Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.RhoProfile
import Mettapedia.OSLF.NativeTypes.Instances.Normalized.Meaning

/-!
# Returned rho packets denote native membership at the original source

The runtime searches the committed source. Native meaning instead uses the
original source and the independent quotient relation, including quote-drop.
The comparison below connects these two judgments through actual primitive
receipts. Checking the complete returned packet also retains its operational
history; quotient endpoint correspondence alone does not establish a bijection
between histories at distinct presentations.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime

open Mettapedia.OSLF.MeTTaIL Syntax
open Mettapedia.OSLF.Framework GSLTTypeSynthesis
open Mettapedia.OSLF.NativeTypes.Instances.Normalized
open Mettapedia.OSLF.NativeTypes.Decision.Reference.Core
open Mettapedia.Languages.MeTTa.OSLFCore (Atom)

/-- A target observation is interpreted after the certified model normalizer. -/
def targetProfile (selected : Pattern) : Profile RhoProfile.generated [] RhoProfile.proc :=
  { RhoProfile.profile with
    observations := [⟨"Target", ⟨3, by decide⟩, fun candidate => candidate == selected⟩] }

def NativeMeaning (source selected : Pattern) : Prop :=
  (gsltOSLF ((targetProfile selected).policy.sourceSystem RhoProfile.generated [] RhoProfile.proc)).satisfies
    source ((targetProfile selected).sourceNativeType (.possibility (.atom ⟨0, by change 0 < 1; decide⟩))).pred

theorem native_iff_receipt (source selected : Pattern) :
    NativeMeaning source selected ↔
      ∃ receipt ∈ RhoPrimitive.receipts (RhoProfile.form source), RhoProfile.form receipt.target = selected := by
  change gsltDiamond ((targetProfile selected).policy.sourceSystem RhoProfile.generated [] RhoProfile.proc)
    ((targetProfile selected).sourceTests ⟨0, by change 0 < 1; decide⟩).predicate source ↔ _
  refine (gsltDiamond_spec
    ((targetProfile selected).policy.sourceSystem RhoProfile.generated [] RhoProfile.proc)
    ((targetProfile selected).sourceTests ⟨0, by change 0 < 1; decide⟩).predicate source).trans ?_
  change (∃ target, (Complete.QuoteDropCoherence.gslt RhoProfile.plan [] RhoProfile.proc
    RhoProfile.presentation).Step source target ∧ ((RhoProfile.form target) == selected) = true) ↔ _
  simp only [beq_iff_eq]
  exact RhoProfile.possibility_iff_receipt source selected

private theorem equations_trivial {first second : Pattern}
    (related : Relation.EqvGen (GeneralOccurrenceSemantics.Equation spec.plan spec.bound spec.expected)
      first second) : first = second := by
  induction related with
  | rel _ _ equation => exact absurd equation (Complete.RhoPresented.noEquations _ _ _ _)
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ left right => exact left.trans right

theorem committed_eq_form (source : Pattern) : committed source = RhoProfile.form source :=
  Complete.QuoteDropCoherence.commit_reflective Complete.RhoPresented.extrusions_eq source

theorem meaning_iff_native (source selected : Pattern) :
    Meaning source selected ↔ NativeMeaning source selected := by
  rw [native_iff_receipt]
  constructor
  · rintro ⟨target, ⟨representative, receipt, before, fired, after⟩, same⟩
    have sourceEq := equations_trivial before
    have targetEq := equations_trivial after
    subst representative
    refine ⟨receipt, (RhoPrimitive.receipts_exact _ _).mpr (by simpa only [committed_eq_form, spec, RhoPrimitive.plan, RhoPrimitive.proc] using fired), ?_⟩
    simpa only [committed_eq_form] using (congrArg committed targetEq).trans same
  · rintro ⟨receipt, member, same⟩
    exact ⟨receipt.target, ⟨committed source, receipt, .refl _,
      by simpa only [committed_eq_form, spec, RhoPrimitive.plan, RhoPrimitive.proc] using (RhoPrimitive.receipts_exact _ _).mp member,
      .refl _⟩, by simpa only [committed_eq_form] using same⟩

theorem proved_native (fixture : Fixture)
    (positive : verdict fixture.target fixture.state = .proved) :
    NativeMeaning fixture.source fixture.target :=
  (meaning_iff_native _ _).mp (proved_sound fixture positive)

theorem refuted_native (fixture : Fixture)
    (negative : verdict fixture.target fixture.state = .refuted) :
    ¬ NativeMeaning fixture.source fixture.target :=
  fun holds => refuted_sound fixture negative ((meaning_iff_native _ _).mpr holds)

def packetVerdict : Atom → Option Verdict
  | .expression [.symbol "RhoNativeReadout", _, _, _, _, _, _, _, .symbol "RhoProved"] => some .proved
  | .expression [.symbol "RhoNativeReadout", _, _, _, _, _, _, _, .symbol "RhoRefuted"] => some .refuted
  | .expression [.symbol "RhoNativeReadout", _, _, _, _, _, _, _, .symbol "RhoUnknown"] => some .unknown
  | _ => none

theorem packetVerdict_exact (fixture : Fixture) :
    packetVerdict fixture.packet = some (verdict fixture.target fixture.state) := by
  unfold Fixture.packet
  cases verdict fixture.target fixture.state <;> rfl

/-- The packet is checked in its entirety, not just its displayed verdict. -/
def acceptsPacket (fixture : Fixture) (packet : Atom) : Bool := packet == fixture.packet

theorem accepted_packet_proved (fixture : Fixture) (packet : Atom)
    (accepted : acceptsPacket fixture packet = true) (positive : packetVerdict packet = some .proved) :
    NativeMeaning fixture.source fixture.target := by
  have same : packet = fixture.packet := Atom.eq_of_beq_eq_true accepted
  rw [same, packetVerdict_exact] at positive
  exact proved_native fixture (Option.some.inj positive)

theorem accepted_packet_refuted (fixture : Fixture) (packet : Atom)
    (accepted : acceptsPacket fixture packet = true) (negative : packetVerdict packet = some .refuted) :
    ¬ NativeMeaning fixture.source fixture.target := by
  have same : packet = fixture.packet := Atom.eq_of_beq_eq_true accepted
  rw [same, packetVerdict_exact] at negative
  exact refuted_native fixture (Option.some.inj negative)

/-- An admitted positive packet is also a positive judgment of the existing
native runtime interface, including original-source typing. -/
theorem accepted_admitted_proved (fixture : Fixture) (packet : Atom)
    (admitted : Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted
      spec.plan.snapshot.language spec.plan.snapshot.free spec.bound spec.expected fixture.source = true)
    (accepted : acceptsPacket fixture packet = true) (positive : packetVerdict packet = some .proved) :
    Mettapedia.OSLF.NativeTypes.Runtime.Description.Meaning (targetProfile fixture.target).driver
      (.possibility (.atom ⟨0, by change 0 < 1; decide⟩)) fixture.source := by
  apply ((targetProfile fixture.target).meaning_iff_source _ _).mpr
  refine ⟨?_, accepted_packet_proved fixture packet accepted positive⟩
  unfold Source
  rw [RhoProfile.generated_snapshot]
  exact Mettapedia.GSLT.LanguageDef.WellSorted.checkOpenPatternWellSorted_sound admitted

end Mettapedia.Languages.MeTTa.PeTTa.Bridges.NativeTypes.RhoRuntime
