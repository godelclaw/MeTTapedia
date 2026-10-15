import Mettapedia.OSLF.Syntax.RhoScopedEquationContextControls
import Mettapedia.OSLF.Syntax.RhoQuotationClassFibres
import Mettapedia.GSLT.Causality.ComplementaryAssay

/-!
# Boolean guard descent and representative-sensitive races

A Boolean guard descends to the actual rho name quotient exactly when it
respects the source equations. Its two fibres then remain disjoint even
when each guard is allowed to use an independently chosen representative.

The literal test for a quotation of null fails this condition. Quote/drop
gives two equivalent closed names on which that test returns different
answers. Equation-saturating its two branches enables both at one name
class. This separator concerns representative-based guarding; it does not
claim that evaluating one Boolean on one literal spelling returns two bits.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.RhoBooleanGuardDescent

open RhoSchema RhoQuotationClassFibres RhoEquationConstructorControls
open RhoScopedEquationContextControls
open Mettapedia.GSLT.Causality.ComplementaryAssay (Verdict)

noncomputable section

def EquationInvariant {context : Ctx sig}
    (test : Term sig context Srt.nm → Bool) : Prop :=
  ∀ first second, EqClosure rhoSourceE first second → test first = test second

def descend {context : Ctx sig} (test : Term sig context Srt.nm → Bool)
    (invariant : EquationInvariant test) : Name context → Bool :=
  Quotient.lift test (fun first second related => invariant first second related)

theorem descend_readout {context : Ctx sig} (test : Term sig context Srt.nm → Bool)
    (invariant : EquationInvariant test) (term : Term sig context Srt.nm) :
    descend test invariant (project term) = test term := rfl

theorem descent_iff {context : Ctx sig} (test : Term sig context Srt.nm → Bool) :
    (∃ guard : Name context → Bool, ∀ term, guard (project term) = test term) ↔
      EquationInvariant test := by
  constructor
  · rintro ⟨guard, readout⟩ first second related
    exact (readout first).symm.trans
      ((congrArg guard (Quotient.sound related)).trans (readout second))
  · intro invariant
    exact ⟨descend test invariant, descend_readout test invariant⟩

theorem descent_unique {context : Ctx sig} (test : Term sig context Srt.nm → Bool)
    (invariant : EquationInvariant test) (guard : Name context → Bool)
    (readout : ∀ term, guard (project term) = test term) :
    guard = descend test invariant := by
  funext value
  induction value using Quotient.inductionOn with
  | _ term => exact readout term

def GuardedRepresentative {context : Ctx sig}
    (test : Term sig context Srt.nm → Bool) (name : Name context) (branch : Verdict) :=
  {term : Term sig context Srt.nm // project term = name ∧ test term = branch.bit}

theorem invariant_branches_do_not_race {context : Ctx sig}
    (test : Term sig context Srt.nm → Bool) (invariant : EquationInvariant test)
    {name : Name context} {first last : Verdict}
    (positive : GuardedRepresentative test name first)
    (negative : GuardedRepresentative test name last) : first = last := by
  have same : project positive.val = project negative.val :=
    positive.property.1.trans negative.property.1.symm
  have bits := invariant _ _ (Quotient.exact same)
  rw [positive.property.2, negative.property.2] at bits
  exact Mettapedia.GSLT.Causality.ComplementaryAssay.verdict_eq_of_bit bits

def literalNull : Term sig [] Srt.nm := quoteRaw null

def wrappedNull : Term sig [] Srt.nm := quoteRaw (dropRaw literalNull)

def literalNullTest : Term sig [] Srt.nm → Bool
  | .op .quo (.cons (.op .nil .nil) .nil) => true
  | _ => false

theorem equivalent_closed_spellings : EqClosure rhoSourceE wrappedNull literalNull :=
  quote_drop_open_equation literalNull

theorem distinct_literal_answers :
    literalNullTest literalNull = true ∧ literalNullTest wrappedNull = false := ⟨rfl, rfl⟩

theorem literal_test_does_not_descend : ¬ EquationInvariant literalNullTest := by
  intro invariant
  have impossible := invariant wrappedNull literalNull equivalent_closed_spellings
  change false = true at impossible
  cases impossible

def acceptingSpelling : GuardedRepresentative literalNullTest (project literalNull) .confirm :=
  ⟨literalNull, rfl, rfl⟩

def rejectingSpelling : GuardedRepresentative literalNullTest (project literalNull) .refute :=
  ⟨wrappedNull, Quotient.sound equivalent_closed_spellings, rfl⟩

theorem equation_saturated_branches_can_race :
    Nonempty (GuardedRepresentative literalNullTest (project literalNull) .confirm) ∧
      Nonempty (GuardedRepresentative literalNullTest (project literalNull) .refute) :=
  ⟨⟨acceptingSpelling⟩, ⟨rejectingSpelling⟩⟩

end

end Mettapedia.OSLF.Binding.RhoBooleanGuardDescent
