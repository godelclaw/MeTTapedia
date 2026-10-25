import Mettapedia.Languages.MM0.Kernel.BoundRenaming
import Mettapedia.Languages.MM0.Translation.VariableIdentificationObstruction
import Mettapedia.Languages.MM0.HOLSyntaxWire
import Mettapedia.Logic.HOL.Embedding.HypersetHenkinInterpretation

/-!
# Bound names and material values in the HOL reading of MM0 contexts

The actual MM0 substitution guard constrains names, while an HOL valuation
assigns values to context positions. Distinct bound names may denote the same
set or hyperset. Conversely, identifying two positions is an ordinary HOL
renaming even though the two-bound MM0 guard refuses it.

The comparison below uses the common material signature and the existing
MM0 variable-identification counterexample. It records exactly the extra
apartness information a reflecting host must retain; it does not assert a
complete proof translation into the maintained `hol.mm0` theory.
-/

set_option autoImplicit false
namespace Mettapedia.Languages.MM0.HOLContextRenaming
open Mettapedia.Logic.HOL
open Embedding.ZFSetHenkinInterpretation (Symbol set member)

abbrev pairContext : Ctx Unit := [set, set]
abbrev singletonContext : Ctx Unit := [set]

/-- Identifying positions is a legal intrinsic HOL renaming. -/
def identify : Rename Unit pairContext singletonContext
  | _, .vz => .vz
  | _, .vs .vz => .vz

/-- Renaming acts on the actual member term, not just on an untyped pair. -/
theorem identify_member :
    rename (Const := Symbol) identify (member (.var .vz) (.var (.vs .vz))) =
      member (.var .vz) (.var .vz) := rfl

/-- MM0 refuses that same identification of two bound positions. -/
theorem identified_names_refused (signature : Kernel.TermSignature) :
    Kernel.Substitution.checkAdmissible signature [.bound 0, .bound 0]
      [.bound 0] [.var 0, .var 0] = false := by
  have refusal := Kernel.Substitution.two_bound_check_iff signature [.bound 0] 0 0 0 rfl rfl
  exact Bool.eq_false_iff.mpr (by simpa using refusal)

/-- The identity and transposition preserve MM0's two bound names. -/
theorem distinct_names_accepted (signature : Kernel.TermSignature) :
    Kernel.Substitution.checkAdmissible signature [.bound 0, .bound 0]
      [.bound 0, .bound 0] [.var 0, .var 1] = true ∧
    Kernel.Substitution.checkAdmissible signature [.bound 0, .bound 0]
      [.bound 0, .bound 0] [.var 1, .var 0] = true := by
  constructor
  · exact (Kernel.Substitution.two_bound_check_iff signature _ 0 0 1 rfl rfl).mpr (by decide)
  · exact (Kernel.Substitution.two_bound_check_iff signature _ 0 1 0 rfl rfl).mpr (by decide)

universe u

noncomputable def sameSet : Embedding.ZFSetHenkinInterpretation.model.{u}.Valuation pairContext
  | _, .vz => (∅ : ZFSet.{u})
  | _, .vs .vz => (∅ : ZFSet.{u})

def sameHyperset (presentation : Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.Presentation.{u}) :
    (Embedding.HypersetHenkinInterpretation.model presentation).Valuation pairContext
  | _, .vz => (∅ : Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.{u})
  | _, .vs .vz => (∅ : Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.{u})

/-- A real set valuation witnesses that bound-name independence is not
inequality of interpreted values. All values are in the model's domains. -/
theorem independent_names_equal_sets (signature : Kernel.TermSignature) :
    Kernel.Substitution.checkAdmissible signature [.bound 0, .bound 0]
      [.bound 0, .bound 0] [.var 0, .var 1] = true ∧
    Embedding.ZFSetHenkinInterpretation.model.ValuationAdmissible sameSet.{u} ∧
    sameSet.{u} .vz = sameSet.{u} (.vs .vz) :=
  ⟨(distinct_names_accepted signature).1, (by intro type index; trivial), rfl⟩

/-- The same separation holds in the cyclic material model; name freshness
is independent of the choice of material foundation. -/
theorem independent_names_equal_hypersets (signature : Kernel.TermSignature)
    (presentation : Mettapedia.TypeTheory.MaterialSets.Hypersets.HSet.Presentation.{u}) :
    Kernel.Substitution.checkAdmissible signature [.bound 0, .bound 0]
      [.bound 0, .bound 0] [.var 0, .var 1] = true ∧
    (Embedding.HypersetHenkinInterpretation.model presentation).ValuationAdmissible
      (sameHyperset presentation) ∧
    sameHyperset presentation .vz = sameHyperset presentation (.vs .vz) :=
  ⟨(distinct_names_accepted signature).1, (by intro type index; trivial), rfl⟩

/-- Replacing MM0's two-bound axiom by an unrestricted HOL binary axiom
permits the coincident instance, exactly the native obstruction. -/
def unguardedAxiom : ClosedFormula Symbol :=
  .all (.all (member (.var (.vs .vz)) (.var .vz)))

def coincidentProof : ProofSyntax Symbol [weakenCtx singletonContext unguardedAxiom]
    (member (.var .vz) (.var .vz)) :=
  by
    let premise : ProofSyntax Symbol [weakenCtx singletonContext unguardedAxiom]
        (weakenCtx singletonContext unguardedAxiom) := .hyp ⟨0, by decide⟩
    have first := ProofSyntax.allE (.var .vz : Term Symbol singletonContext set) premise
    have second := ProofSyntax.allE (.var .vz : Term Symbol singletonContext set) first
    exact second

/-- The attempted unguarded interpretation has a concrete false instance. -/
theorem unguarded_axiom_false_in_sets :
    ¬ Embedding.ZFSetHenkinInterpretation.model.{u}.models unguardedAxiom := by
  intro claimed
  exact ZFSet.notMem_empty _ (claimed (∅ : ZFSet.{u}) trivial (∅ : ZFSet.{u}) trivial)

/-- An actual retained HOL proof of the collapsed reading coexists with
native nonderivability of the collapsed bound-name judgment. -/
theorem unguarded_reading_loses_reflection :
    Nonempty (ProofSyntax Symbol [weakenCtx singletonContext unguardedAxiom]
      (member (.var .vz) (.var .vz))) ∧
    ¬ Kernel.Derives Kernel.SubstitutionStabilityControls.signature
      Kernel.SubstitutionStabilityControls.noDefinitions Kernel.SubstitutionStabilityControls.theorems
      Kernel.SubstitutionStabilityControls.twoBound []
      (Kernel.SubstitutionStabilityControls.distinct 0 0) :=
  ⟨⟨coincidentProof⟩, Kernel.SubstitutionStabilityControls.independence_required.2.2.2.1⟩

end Mettapedia.Languages.MM0.HOLContextRenaming
