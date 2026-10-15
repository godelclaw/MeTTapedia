import Mettapedia.OSLF.Framework.RhoScopeMinimumReceipts
import Mettapedia.OSLF.Framework.RhoGeneratedScopeSubstitution

/-!
# Minimum scope grades and complete supplied receipt transport

Actual quotient-valued substitution transports a supplied certificate with
its depth and ordered atomic origins. A newly searched target minimum can
be smaller. Positive atomic premise maps earn the one-sided grade bound;
maps in both directions with an actual name roundtrip earn equality of
minimum depths. They do not identify the independently selected receipts.
-/

set_option autoImplicit false

noncomputable section

namespace Mettapedia.OSLF.Framework.RhoScopeMinimumReceiptTransport

open Mettapedia.OSLF.Binding
open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls BindingSubstitutionAlgebra
open RhoEquationGeneratedScope RhoGeneratedScopeSubstitution RhoScopeMinimumReceipts

variable {source target : Ctx sig}
variable {left right : Process source → Prop} {left' right' : Process target → Prop}

theorem supplied_transport_readouts
    (env : Environment sig (TermQ rhoSourceE) source target)
    (leftMap : ∀ process, left process → left' (model.substitution.substitute env process))
    (rightMap : ∀ process, right process → right' (model.substitution.substitute env process))
    {name : Name source} (receipt : Certificate left right name) :
    (transport env leftMap rightMap receipt).depth = receipt.depth ∧
      (transport env leftMap rightMap receipt).atomicOrigins =
        receipt.atomicOrigins.map (Sum.map (model.substitution.substitute env)
          (model.substitution.substitute env)) :=
  ⟨transport_depth env leftMap rightMap receipt, transport_atomicOrigins env leftMap rightMap receipt⟩

variable [DecidablePred left'] [DecidablePred right']

theorem target_receipt_presence
    (env : Environment sig (TermQ rhoSourceE) source target)
    (leftMap : ∀ process, left process → left' (model.substitution.substitute env process))
    (rightMap : ∀ process, right process → right' (model.substitution.substitute env process))
    {name : Name source} (receipt : Certificate left right name) :
    (minimumReceipt? left' right' (model.substitution.substitute env name)).isSome = true :=
  (minimumReceipt?_presence _ _ _).mpr (certificate_sound (transport env leftMap rightMap receipt))

theorem target_minimum_no_greater
    (env : Environment sig (TermQ rhoSourceE) source target)
    (leftMap : ∀ process, left process → left' (model.substitution.substitute env process))
    (rightMap : ∀ process, right process → right' (model.substitution.substitute env process))
    {name : Name source} (supplied : Certificate left right name)
    {selected : Certificate left' right' (model.substitution.substitute env name)}
    (readout : minimumReceipt? left' right' (model.substitution.substitute env name) = some selected) :
    selected.depth ≤ supplied.depth := by
  have least := minimumReceipt?_least left' right' _ readout (transport env leftMap rightMap supplied)
  rw [transport_depth] at least
  exact least

variable [DecidablePred left] [DecidablePred right]

theorem roundtrip_minimum_depths
    (forward : Environment sig (TermQ rhoSourceE) source target)
    (backward : Environment sig (TermQ rhoSourceE) target source)
    (forwardLeft : ∀ process, left process → left' (model.substitution.substitute forward process))
    (forwardRight : ∀ process, right process → right' (model.substitution.substitute forward process))
    (backwardLeft : ∀ process, left' process → left (model.substitution.substitute backward process))
    (backwardRight : ∀ process, right' process → right (model.substitution.substitute backward process))
    {name : Name source}
    (roundtrip : model.substitution.substitute backward (model.substitution.substitute forward name) = name)
    {sourceReceipt : Certificate left right name}
    {targetReceipt : Certificate left' right' (model.substitution.substitute forward name)}
    (sourceReadout : minimumReceipt? left right name = some sourceReceipt)
    (targetReadout : minimumReceipt? left' right' (model.substitution.substitute forward name) = some targetReceipt) :
    sourceReceipt.depth = targetReceipt.depth := by
  have forwardBound := target_minimum_no_greater forward forwardLeft forwardRight sourceReceipt targetReadout
  let broughtBack : Certificate left right name :=
    roundtrip ▸ transport backward backwardLeft backwardRight targetReceipt
  have backwardBound := minimumReceipt?_least left right name sourceReadout broughtBack
  have preserved : broughtBack.depth = targetReceipt.depth := by
    simp only [broughtBack, depth_cast, transport_depth]
  rw [preserved] at backwardBound
  exact Nat.le_antisymm backwardBound forwardBound

end Mettapedia.OSLF.Framework.RhoScopeMinimumReceiptTransport
