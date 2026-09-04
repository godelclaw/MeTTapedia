import Mettapedia.GraphTheory.FourColor.Compositional.PhasedNoncrossingSweep

/-!
# Canonical open-wire interfaces at equal noncrossing sweep states

A sweep cut exposes, for every matching family, the ordered list of arcs open
across that cut.  Equality of raw sweep states makes the lengths of those
lists equal family by family, hence canonically identifies their ordered
slots.

This is deliberately a structural interface only.  It does not assert that
the corresponding arcs are the same graph edges or carry equal colouring
profiles; those are additional semantic fields required by a physical
splice.
-/

namespace Mettapedia.GraphTheory.FourColor.Compositional

namespace NoncrossingSweepInterface

open GoertzelV24NoncrossingSweepLifo
open PhasedNoncrossingSweep

universe u v

/-- The finite ordered open-wire interface exposed at one sweep cut. -/
def OpenArcInterface {A : Type u} {K : Type v} {r n : Nat}
    (data : SweepData A K r n) (cut : Fin n) :=
  Σ family : Fin r, Fin ((data.family family).openArcs cut).length

/-- Raw-state equality gives equality of open-arc counts in every matching
family. -/
theorem openArcs_length_eq_of_rawState_eq
    {A : Type u} {K : Type v} {r n : Nat}
    (data : SweepData A K r n) {first second : Fin n}
    (heq : data.rawState first = data.rawState second)
    (family : Fin r) :
    ((data.family family).openArcs first).length =
      ((data.family family).openArcs second).length := by
  have hstack : (data.family family).stackAt first =
      (data.family family).stackAt second := by
    simpa only [SweepData.rawState] using
      congrFun (congrArg Prod.snd heq) family
  have hlength := congrArg List.length hstack
  simpa [NoncrossingMatching.stackAt] using hlength

/-- Equal raw sweep states canonically identify the ordered open-wire slots
family by family. -/
def openArcInterfaceEquivOfRawStateEq
    {A : Type u} {K : Type v} {r n : Nat}
    (data : SweepData A K r n) {first second : Fin n}
    (heq : data.rawState first = data.rawState second) :
    OpenArcInterface data first ≃ OpenArcInterface data second :=
  Equiv.sigmaCongrRight fun family =>
    finCongr (openArcs_length_eq_of_rawState_eq data heq family)

@[simp]
theorem openArcInterfaceEquivOfRawStateEq_family
    {A : Type u} {K : Type v} {r n : Nat}
    (data : SweepData A K r n) {first second : Fin n}
    (heq : data.rawState first = data.rawState second)
    (wire : OpenArcInterface data first) :
    (openArcInterfaceEquivOfRawStateEq data heq wire).1 = wire.1 :=
  rfl

@[simp]
theorem openArcInterfaceEquivOfRawStateEq_slot
    {A : Type u} {K : Type v} {r n : Nat}
    (data : SweepData A K r n) {first second : Fin n}
    (heq : data.rawState first = data.rawState second)
    (wire : OpenArcInterface data first) :
    (openArcInterfaceEquivOfRawStateEq data heq wire).2.val = wire.2.val :=
  rfl

/-- Equality of phased states gives the same canonical interface equivalence
after forgetting the spacing phase. -/
def openArcInterfaceEquivOfPhasedRawStateEq
    {A : Type u} {K : Type v} {r n : Nat}
    (data : SweepData A K r n) (spacing : Nat)
    {first second : Fin n}
    (heq : (PhasedNoncrossingSweep.SweepData.withPositionPhase data spacing
        ).rawState first =
      (PhasedNoncrossingSweep.SweepData.withPositionPhase data spacing
        ).rawState second) :
    OpenArcInterface data first ≃ OpenArcInterface data second :=
  openArcInterfaceEquivOfRawStateEq data
    (PhasedNoncrossingSweep.SweepData.rawState_eq_of_withPositionPhase_rawState_eq
      data spacing heq)

end NoncrossingSweepInterface

end Mettapedia.GraphTheory.FourColor.Compositional
