import Mettapedia.Languages.MM0.MeTTa.Kernel.Resumption
import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativePeTTaConfigurations

/-!
# The actual authored MM0 checker on native typed configuration data

The request retains the existing MM0 tables, context and proof witness. Its
native explicit-state path is equivalent to the independently checked MM0
judgment, including the exact claimed conclusion. Both endpoints have native
Data formation and the established constructor-algebra meaning.

These are operational paths over typed data, not dependent conversion paths
or native proof terms inhabiting the represented MM0 proposition. Execution
of the translated C program is a separate qualification boundary.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.MeTTa.Proof.NativeExecution

open Mettapedia.Languages.MeTTa.PeTTa
open Kernel (Context Preterm ProofWitness)
open Presentation.ComputationalTyping (signatureOf)
open ProofResults (resultValue)

open Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased

/-- The complete request and response stores are represented explicitly.
Target support cannot be dropped merely because the printed claim agrees. -/
def Returns (tables : Tables) (context : Context) (witness : ProofWitness)
    (before : Effects.State) (names : List String) (claim : Preterm) : Prop :=
  ∃ after finalNames,
    (NativePeTTaConfigurations.theory program).MultiStep
      (NativePeTTaConfigurations.encode (requestConfiguration before tables context witness) names)
      (NativePeTTaConfigurations.encode (Eval.finished after [resultValue (some claim)] [] []) finalNames) ∧
    NamedSpaces.Store.EmptyTail after [] ∧
    (∀ name, name ∉ finalNames → after.cells name = none)

/-- Every exact MM0 checking judgment constructs a native state path; every
such path reflects execution of the actual authored checker and that claim. -/
theorem checks_iff_returns (tables : Tables) (context : Context) (witness : ProofWitness)
    (before : Effects.State) (ready : Ready tables before) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none) (claim : Preterm) :
    ProofWitness.Checks (signatureOf tables.entries)
      (Unfolding.definitionSignature tables.bodies) (theoremSignature tables.declarations)
      context tables.values witness claim ↔ Returns tables context witness before names claim := by
  rw [checks_iff_gslt_path tables context witness before ready claim]
  constructor
  · rintro ⟨after, sourcePath⟩
    obtain ⟨finalNames, path, targetVacant, targetCovers⟩ :=
      NativePeTTaConfigurations.path_lifts sourcePath names vacant covers
    exact ⟨after, finalNames, path, targetVacant, targetCovers⟩
  · rintro ⟨after, finalNames, path, targetVacant, targetCovers⟩
    obtain ⟨decodedAfter, decoded, sourcePath⟩ := NativePeTTaConfigurations.path_reflects path
      (requestConfiguration before tables context witness)
      (NativePeTTaConfigurations.decode_encode _ names vacant covers)
    rw [NativePeTTaConfigurations.decode_encode _ finalNames targetVacant targetCovers] at decoded
    have same := Option.some.inj decoded
    subst decodedAfter
    exact ⟨after, sourcePath⟩

/-- The existing certificate calculus admits exactly these native state
paths, after actual theory-table correspondence and store authorization. -/
theorem certificate_accepted_iff_returns (theory : Kernel.Theory)
    (tables : Tables) (terms : tables.entries = theory.terms)
    (definitions : tables.bodies = theory.definitions)
    (theorems : tables.declarations = theory.theorems)
    (context : Context) (witness : ProofWitness) (before : Effects.State)
    (ready : Ready tables before) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none) (claim : Preterm) :
    (∃ fuel, Mettapedia.GSLT.LanguageDef.InferenceComputedLeaves.check
      Presentation.Calculus.kernelCalculus (Presentation.Calculus.family theory).evaluate
      (Presentation.Calculus.derivesJ context tables.values claim)
      (Presentation.Calculus.Witness.translate theory fuel context tables.values witness) = true) ↔
    Returns tables context witness before names claim := by
  rw [certificate_accepted_iff_petta_judgment theory tables terms definitions theorems
    context witness before ready claim]
  exact (checks_iff_petta_judgment tables context witness before ready claim).symm.trans
    (checks_iff_returns tables context witness before ready names vacant covers claim)

/-- A path cannot substitute a different dependent conclusion for the one
earned by this request. The computational MM0 checker is single-valued. -/
theorem returns_unique_claim (tables : Tables) (context : Context) (witness : ProofWitness)
    (before : Effects.State) (ready : Ready tables before) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none)
    (first second : Preterm)
    (one : Returns tables context witness before names first)
    (two : Returns tables context witness before names second) : first = second := by
  have firstChecked := (checks_iff_returns tables context witness before ready names vacant covers first).mpr one
  have secondChecked := (checks_iff_returns tables context witness before ready names vacant covers second).mpr two
  exact Option.some.inj (firstChecked.eval.symm.trans secondChecked.eval)

theorem wrong_claim_refused (tables : Tables) (context : Context) (witness : ProofWitness)
    (before : Effects.State) (ready : Ready tables before) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none)
    (first second : Preterm) (different : first ≠ second)
    (one : Returns tables context witness before names first) :
    ¬ Returns tables context witness before names second :=
  fun two => different (returns_unique_claim tables context witness before ready names vacant covers
    first second one two)

/-- A real hypothesis occurrence produces the corresponding native path.
Its index is checked against the supplied ordered hypothesis vector. -/
theorem stored_hypothesis_returns (tables : Tables) (context : Context)
    (before : Effects.State) (ready : Ready tables before) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none)
    (index : Nat) (claim : Preterm) (found : tables.values[index]? = some claim) :
    Returns tables context (.hyp index) before names claim :=
  (checks_iff_returns tables context (.hyp index) before ready names vacant covers claim).mp
    (.hyp found)

/-- Empty or out-of-range hypothesis input cannot earn an arbitrary claim,
even though every request and alleged response remains well-formed Data. -/
theorem missing_hypothesis_refused (tables : Tables) (context : Context)
    (before : Effects.State) (ready : Ready tables before) (names : List String)
    (vacant : NamedSpaces.Store.EmptyTail before [])
    (covers : ∀ name, name ∉ names → before.cells name = none)
    (index : Nat) (claim : Preterm) (missing : tables.values[index]? = none) :
    ¬ Returns tables context (.hyp index) before names claim := by
  intro accepted
  have computed := ((checks_iff_returns tables context (.hyp index) before ready names
    vacant covers claim).mpr accepted).eval
  simp only [ProofWitness.proof?, missing] at computed
  cases computed

end Mettapedia.Languages.MM0.MeTTa.Proof.NativeExecution
