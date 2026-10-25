import Mettapedia.Languages.MM0.Kernel.ProofChecking

/-!
# The theorem-table dependencies of a submitted MM0 witness

The ordered reference list records every theorem application in the actual
witness, including applications in child proofs. Checking depends only on
the declarations at those references. Restricting a theorem table preserves
checking precisely when every used reference remains licensed.

Term declarations, definition bodies, variable-independence conditions and
local hypotheses are fixed throughout this comparison. A theorem reference
may name an axiom or a previously admitted theorem; its transitive theory
justification is a separate admission obligation. These results isolate the
policy needed before source-theory reflection can be considered.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MM0.Kernel.ProofWitness

mutual

def theoremReferences : ProofWitness → List Nat
  | .hyp _ => []
  | .theoremApp index _ children => index :: childrenTheoremReferences children
  | .conversion _ child => theoremReferences child
termination_by witness => sizeOf witness

def childrenTheoremReferences : List ProofWitness → List Nat
  | [] => []
  | child :: children => theoremReferences child ++ childrenTheoremReferences children
termination_by children => sizeOf children

end

variable {signature : TermSignature} {definitions : Definition.Signature}
variable {theorems : TheoremSignature} {context : Context} {hypotheses : List Preterm}

/-- Changing unused declarations preserves the particular submitted proof. -/
theorem Checks.transportTheorems {witness : ProofWitness} {expression : Preterm}
    (checked : Checks signature definitions theorems context hypotheses witness expression) :
    ∀ (other : TheoremSignature),
      (∀ index ∈ theoremReferences witness, other index = theorems index) →
      Checks signature definitions other context hypotheses witness expression := by
  induction checked using Checks.rec
      (motive_2 := fun children expressions _ => ∀ (other : TheoremSignature),
        (∀ index ∈ childrenTheoremReferences children, other index = theorems index) →
        ChecksList signature definitions other context hypotheses children expressions) with
  | hyp lookup => exact fun _ _ => .hyp lookup
  | @theoremApp index declaration arguments children instantiation lookup instantiated _ ih =>
      intro other agreement
      apply Checks.theoremApp (declaration := declaration) (instantiation := instantiation)
      · rw [agreement index (by simp [theoremReferences])]
        exact lookup
      · exact instantiated
      · apply ih other
        intro used member
        exact agreement used (by simp [theoremReferences, member])
  | conversion converted _ ih =>
      intro other agreement
      exact .conversion converted (ih other (by simpa only [theoremReferences] using agreement))
  | nil => exact .nil
  | @cons child children expression expressions _ _ ihChild ihTail =>
      rename_i other agreement
      exact .cons
        (ihChild other (fun used member => agreement used (by simp [childrenTheoremReferences, member])))
        (ihTail other (fun used member => agreement used (by simp [childrenTheoremReferences, member])))

/-- Every reference in an accepted witness has an actual declaration. -/
theorem Checks.theoremReferences_present {witness : ProofWitness} {expression : Preterm}
    (checked : Checks signature definitions theorems context hypotheses witness expression) :
    ∀ index ∈ theoremReferences witness, ∃ declaration, theorems index = some declaration := by
  induction checked using Checks.rec
      (motive_2 := fun children _ _ => ∀ index ∈ childrenTheoremReferences children,
        ∃ declaration, theorems index = some declaration) with
  | hyp _ => simp [theoremReferences]
  | @theoremApp index declaration arguments children instantiation lookup _ _ ih =>
      intro used member
      simp only [theoremReferences, List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨declaration, lookup⟩
      · exact ih used member
  | conversion _ _ ih => simpa only [theoremReferences] using ih
  | nil => simp_all [childrenTheoremReferences]
  | cons _ _ ihChild ihTail =>
      rename_i used member
      simp only [childrenTheoremReferences, List.mem_append] at member
      exact member.elim (ihChild used) (ihTail used)

/-- Acceptance has the same exact conclusion under tables agreeing on the
submitted witness's references, including agreement on absent entries. -/
theorem check_iff_of_theorem_agreement (other : TheoremSignature)
    (witness : ProofWitness) (expression : Preterm)
    (agreement : ∀ index ∈ theoremReferences witness, other index = theorems index) :
    check signature definitions other context hypotheses witness expression = true ↔
      check signature definitions theorems context hypotheses witness expression = true := by
  rw [check_iff, check_iff]
  exact ⟨fun checked => checked.transportTheorems _ (fun index member => (agreement index member).symm),
    fun checked => checked.transportTheorems _ agreement⟩

/-- A local theorem policy leaves all term and conversion interfaces intact. -/
def restrictedTheorems (allowed : Nat → Bool) (theorems : TheoremSignature) : TheoremSignature :=
  fun index => if allowed index then theorems index else none

theorem restricted_check_iff (allowed : Nat → Bool) (witness : ProofWitness) (expression : Preterm) :
    check signature definitions (restrictedTheorems allowed theorems) context hypotheses witness expression = true ↔
      check signature definitions theorems context hypotheses witness expression = true ∧
        ∀ index ∈ theoremReferences witness, allowed index = true := by
  constructor
  · intro accepted
    have checked := (check_iff _ _ _ _ _ _ _).mp accepted
    have licensed : ∀ index ∈ theoremReferences witness, allowed index = true := by
      intro index member
      obtain ⟨declaration, present⟩ := checked.theoremReferences_present index member
      cases permission : allowed index with
      | false => simp [restrictedTheorems, permission] at present
      | true => rfl
    refine ⟨?_, licensed⟩
    exact (check_iff _ _ _ _ _ _ _).mpr (checked.transportTheorems _ (by
      intro index member
      simp only [restrictedTheorems, licensed index member, ↓reduceIte]))
  · rintro ⟨accepted, licensed⟩
    exact (check_iff_of_theorem_agreement (restrictedTheorems allowed theorems) witness expression
      (by intro index member; simp only [restrictedTheorems, licensed index member, ↓reduceIte])).mpr accepted

theorem disallowed_reference_refused (allowed : Nat → Bool) (witness : ProofWitness)
    (expression : Preterm) {index : Nat} (used : index ∈ theoremReferences witness)
    (denied : allowed index = false) :
    check signature definitions (restrictedTheorems allowed theorems) context hypotheses witness expression = false := by
  cases result : check signature definitions (restrictedTheorems allowed theorems) context hypotheses witness expression with
  | false => rfl
  | true =>
      have licensed := ((restricted_check_iff allowed witness expression).mp result).2 index used
      simp [denied] at licensed

#print axioms Checks.transportTheorems
#print axioms Checks.theoremReferences_present
#print axioms check_iff_of_theorem_agreement
#print axioms restricted_check_iff
#print axioms disallowed_reference_refused

end Mettapedia.Languages.MM0.Kernel.ProofWitness
