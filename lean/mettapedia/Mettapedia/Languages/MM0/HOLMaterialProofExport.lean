import Mettapedia.Languages.MM0.HOLProofExport
import Mettapedia.Logic.HOL.Embedding.HypersetHenkinInterpretation
import Mettapedia.Logic.HOL.Embedding.CodedHypersetInterpretation

/-!
# Material HOL deductions for the maintained MM0 proof exporter

The union deduction uses the ordinary common HOL law. Its self-membership
premise is realizable by a cyclic hyperset and unrealizable by a well-founded
set. Exporting the proof therefore requires neither global foundation nor a
change to the proof kernel. Codes retain a separate interpreted membership.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.HOLMaterialProofExport

open Mettapedia.Logic.HOL
open Embedding.ZFSetHenkinInterpretation
open Mettapedia.TypeTheory.MaterialSets.Hypersets
open HSet

universe u

/-- Self-membership implies membership in the union, in the common theory. -/
def cyclicUnion : ClosedFormula Symbol :=
  .all (.imp (member (.var .vz) (.var .vz))
    (member (.var .vz) (.app (.const .union) (.var .vz))))

/-- The proof is a genuine deduction from union, with both uses of its
self-membership hypothesis retained in the source proof tree. -/
def cyclicUnionProof : ProofSyntax Symbol [unionLaw] cyclicUnion := by
  apply ProofSyntax.allI
  apply ProofSyntax.impI
  have law : ProofSyntax Symbol
      [member (.var .vz) (.var .vz), weaken unionLaw] (weaken unionLaw) := .hyp 1
  have instanceProof := ProofSyntax.andER
    (ProofSyntax.allE (Term.var .vz) (ProofSyntax.allE (Term.var .vz) law))
  apply ProofSyntax.impE instanceProof
  exact ProofSyntax.exI (.var .vz) (ProofSyntax.andI (.hyp 0) (.hyp 0))

theorem cyclicUnion_valid_in_sets : Embedding.ZFSetHenkinInterpretation.model.{u}.models cyclicUnion := by
  intro value _ self
  exact ZFSet.mem_sUnion.mpr ⟨value, self, self⟩

theorem cyclicUnion_valid_in_hypersets (presentation : HSet.Presentation.{u}) :
    (Embedding.HypersetHenkinInterpretation.model presentation).models cyclicUnion := by
  intro value _ self
  exact HSet.mem_sUnion.mpr ⟨value, self, self⟩

/-- The premise of the shared deduction is impossible in the well-founded
reading. This is a statement about that membership relation. -/
theorem wellFounded_has_no_cycle : ¬ ∃ value : ZFSet.{u}, value ∈ value := by
  rintro ⟨value, self⟩
  exact ZFSet.mem_irrefl value self

/-- The very same deduction has a nonvacuous cyclic instance in HSet. -/
theorem hyperset_cycle_instance :
    ∃ value : HSet.{u}, value ∈ value ∧ value ∈ HSet.sUnion value := by
  refine ⟨quineAtom, ?_, ?_⟩
  · exact quineAtom_mem_self
  · exact HSet.mem_sUnion.mpr ⟨quineAtom, quineAtom_mem_self, quineAtom_mem_self⟩

def cyclicUnionWitness : ClosedFormula Symbol :=
  .ex (.and (member (.var .vz) (.var .vz))
    (member (.var .vz) (.app (.const .union) (.var .vz))))

/-- The cyclic premise is retained as a distinct source assumption. -/
def cyclicUnionWitnessProof : ProofSyntax Symbol
    [unionLaw, Embedding.HypersetHenkinInterpretation.selfMember] cyclicUnionWitness := by
  apply ProofSyntax.exE (.hyp 1)
  have lifted := ProofSyntax.rename (Rename.weaken (σ := set)) cyclicUnionProof
  let transport : ProofSyntax.OccurrenceMap (weakenHyps (σ := set) [unionLaw])
      (member (.var .vz) (.var .vz) ::
        weakenHyps (σ := set) [unionLaw, Embedding.HypersetHenkinInterpretation.selfMember]) :=
    ⟨fun _ => 1, fun index => by
      rcases index with ⟨number, bound⟩
      have small : number < 1 := by
        simpa only [weakenHyps, List.length_map, List.length_cons, List.length_nil] using bound
      have same : number = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ small)
      subst number
      rfl⟩
  have specialized := ProofSyntax.allE (Term.var .vz) (ProofSyntax.mono transport lifted)
  exact ProofSyntax.exI (.var .vz) (ProofSyntax.andI (.hyp 0) (ProofSyntax.impE specialized (.hyp 0)))

/-- Relative to the union law, the displayed cyclic-union witness has
exactly the logical strength of the existence of a self-member. -/
def cyclicUnionEquivalenceProof : ProofSyntax Symbol [unionLaw]
    (iffFormula Embedding.HypersetHenkinInterpretation.selfMember cyclicUnionWitness) := by
  apply ProofSyntax.andI
  · apply ProofSyntax.impI
    let exchange : ProofSyntax.OccurrenceMap
        [unionLaw, Embedding.HypersetHenkinInterpretation.selfMember]
        [Embedding.HypersetHenkinInterpretation.selfMember, unionLaw] :=
      ⟨fun index => Fin.cases 1 (fun _ => 0) index, by
        intro index
        rcases index with ⟨number, bound⟩
        cases number with
        | zero => rfl
        | succ number =>
          cases number with
          | zero => rfl
          | succ number => simp only [List.length_cons, List.length_nil] at bound; omega⟩
    exact ProofSyntax.mono exchange cyclicUnionWitnessProof
  · apply ProofSyntax.impI
    exact ProofSyntax.exE (.hyp 0)
      (ProofSyntax.exI (.var .vz) (ProofSyntax.andEL (.hyp 0)))

/-- A statement over the actual HOL model interface: no full-domain, choice,
foundation or extensional-function assumption is needed for this equivalence. -/
theorem cyclicUnionWitness_iff_selfMember
    (model : HenkinModel.{0, 0, u} Unit Symbol) (union : model.models unionLaw) :
    model.models cyclicUnionWitness ↔ model.models Embedding.HypersetHenkinInterpretation.selfMember := by
  constructor
  · rintro ⟨value, admitted, self, _⟩
    exact ⟨value, admitted, self⟩
  · rintro ⟨value, admitted, self⟩
    exact ⟨value, admitted, self, (union value admitted value admitted).2
      ⟨value, admitted, self, self⟩⟩

/-- The new conclusion cannot be obtained by silently dropping the cyclic
premise. An actual well-founded model refutes it. -/
theorem cycle_premise_cannot_be_dropped : IsEmpty (ProofSyntax Symbol [unionLaw] cyclicUnionWitness) := by
  refine ⟨fun proof => ?_⟩
  have truth := Soundness.extDerivation_sound (M := Embedding.ZFSetHenkinInterpretation.model.{0})
    proof.erase Embedding.ZFSetHenkinInterpretation.functionsRespectEqv
    (fun index => nomatch index) (by
      intro formula present
      have same : formula = unionLaw := by simpa using present
      subst formula
      exact Embedding.ZFSetHenkinInterpretation.unionLaw_valid)
  obtain ⟨value, _, self, _⟩ := truth
  exact ZFSet.mem_irrefl value self

theorem cyclicUnionWitness_valid_in_hypersets (presentation : HSet.Presentation.{u}) :
    (Embedding.HypersetHenkinInterpretation.model presentation).models cyclicUnionWitness := by
  refine ⟨quineAtom, trivial, quineAtom_mem_self, ?_⟩
  exact HSet.mem_sUnion.mpr ⟨quineAtom, quineAtom_mem_self, quineAtom_mem_self⟩

theorem cyclicUnion_valid_in_codes (presentation : HSet.Presentation.{u}) :
    (Embedding.CodedHypersetInterpretation.model presentation).models cyclicUnion :=
  (Embedding.CodedHypersetInterpretation.models_iff presentation cyclicUnion).mpr
    (cyclicUnion_valid_in_hypersets presentation)

theorem cyclicUnionWitness_valid_in_codes (presentation : HSet.Presentation.{u}) :
    (Embedding.CodedHypersetInterpretation.model presentation).models cyclicUnionWitness :=
  (Embedding.CodedHypersetInterpretation.models_iff presentation cyclicUnionWitness).mpr
    (cyclicUnionWitness_valid_in_hypersets presentation)

/-- The cyclic guest and its union live on valid codes whose host membership
remains irreflexive. The interpreted relation has its declared container-first order. -/
theorem coded_cycle_instance :
    ∃ value : CodedFamilies.Code.{u},
      codeMem value.1 value.1 ∧
      codeMem (CodedFamilies.encode (HSet.sUnion (CodedFamilies.decode value))).1 value.1 ∧
      value.1 ∉ value.1 := by
  refine ⟨CodedFamilies.encode quineAtom, CodedFamilies.quine_codeMem_self,
    ?_, CodedFamilies.hostCode_not_mem_self _⟩
  simpa only [CodedFamilies.decode, CodedFamilies.encode, decodeHSet_code] using
    (codeMem_code.mpr (HSet.mem_sUnion.mpr
      ⟨quineAtom, quineAtom_mem_self, quineAtom_mem_self⟩))

end Mettapedia.Languages.MM0.HOLMaterialProofExport
