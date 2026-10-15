import Mettapedia.OSLF.NativeTypes.Certificates.RefinementChecking
import Mathlib.Data.List.OfFn

/-!+# Vocabulary selection for the complete native grammar

Selection inspects every annotation, bound body and ordered primitive argument.
It also inspects every node of a supplied certificate, including intermediate
judgments. Refusal is an explicit result distinct from a failed certificate.
The underlying independent native rules and their derivations are unchanged.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeLogic

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.NativeTypes.Certificates

inductive Feature where
  | propositions | functions | sums | comprehension | reification
  | truth | falsehood | conjunction | disjunction | implication
  | universal | existential | image
  deriving DecidableEq, Repr

structure Fragment where
  enabled : List Feature
  deriving DecidableEq, Repr

def full : Fragment :=
  ⟨[.propositions, .functions, .sums, .comprehension, .reification,
    .truth, .falsehood, .conjunction, .disjunction, .implication,
    .universal, .existential, .image]⟩

variable {S : Symbols}

mutual
def typeFeatures : {n : Nat} → TypeExpr S n → List Feature
  | _, .family _ arguments => (List.ofFn fun i => termFeatures (arguments i)).flatten
  | _, .propositions => [.propositions]
  | _, .pi domain body => .functions :: (typeFeatures domain ++ typeFeatures body)
  | _, .sigma domain body => .sums :: (typeFeatures domain ++ typeFeatures body)
  | _, .comprehension domain predicate =>
      .comprehension :: (typeFeatures domain ++ propFeatures predicate)

def termFeatures : {n : Nat} → TermExpr S n → List Feature
  | _, .var _ => []
  | _, .primitive _ arguments => (List.ofFn fun i => termFeatures (arguments i)).flatten
  | _, .lam domain codomain body =>
      .functions :: (typeFeatures domain ++ typeFeatures codomain ++ termFeatures body)
  | _, .app domain body function argument =>
      .functions :: (typeFeatures domain ++ typeFeatures body ++ termFeatures function ++ termFeatures argument)
  | _, .pair domain body first second =>
      .sums :: (typeFeatures domain ++ typeFeatures body ++ termFeatures first ++ termFeatures second)
  | _, .fst domain body pair | _, .snd domain body pair =>
      .sums :: (typeFeatures domain ++ typeFeatures body ++ termFeatures pair)
  | _, .sigmaElim domain body motive branch pair =>
      .sums :: (typeFeatures domain ++ typeFeatures body ++ typeFeatures motive ++
        termFeatures branch ++ termFeatures pair)
  | _, .quote predicate => .reification :: propFeatures predicate
  | _, .refine domain predicate value | _, .forget domain predicate value =>
      .comprehension :: (typeFeatures domain ++ propFeatures predicate ++ termFeatures value)

def propFeatures : {n : Nat} → PropExpr S n → List Feature
  | _, .atom _ arguments => (List.ofFn fun i => termFeatures (arguments i)).flatten
  | _, .truth => [.truth]
  | _, .falsehood => [.falsehood]
  | _, .and first second => .conjunction :: (propFeatures first ++ propFeatures second)
  | _, .or first second => .disjunction :: (propFeatures first ++ propFeatures second)
  | _, .implies first second => .implication :: (propFeatures first ++ propFeatures second)
  | _, .all domain predicate => .universal :: (typeFeatures domain ++ propFeatures predicate)
  | _, .exists domain predicate => .existential :: (typeFeatures domain ++ propFeatures predicate)
  | _, .holds term => .reification :: termFeatures term
  | _, .image type => .image :: typeFeatures type
end

def contextFeatures : {n : Nat} → ContextExpr S n → List Feature
  | _, .nil => []
  | _, .snoc context type => contextFeatures context ++ typeFeatures type
  | _, .assume context predicate => contextFeatures context ++ propFeatures predicate

def substitutionFeatures {n m : Nat} (substitution : Substitution S n m) : List Feature :=
  (List.ofFn fun i => termFeatures (substitution i)).flatten

def judgmentFeatures : Judgment S → List Feature
  | .context context => contextFeatures context
  | .type context type => contextFeatures context ++ typeFeatures type
  | .term context term type => contextFeatures context ++ termFeatures term ++ typeFeatures type
  | .substitution source target substitution =>
      contextFeatures source ++ contextFeatures target ++ substitutionFeatures substitution
  | .contextEq first second => contextFeatures first ++ contextFeatures second
  | .typeEq context first second => contextFeatures context ++ typeFeatures first ++ typeFeatures second
  | .termEq context first second type =>
      contextFeatures context ++ termFeatures first ++ termFeatures second ++ typeFeatures type
  | .substitutionEq source target first second =>
      contextFeatures source ++ contextFeatures target ++ substitutionFeatures first ++ substitutionFeatures second
  | .predicate context predicate | .entails context predicate =>
      contextFeatures context ++ propFeatures predicate
  | .predicateEq context first second =>
      contextFeatures context ++ propFeatures first ++ propFeatures second

def Fragment.permits (fragment : Fragment) (judgment : Judgment S) : Prop :=
  ∀ feature ∈ judgmentFeatures judgment, feature ∈ fragment.enabled

def Fragment.accepts (fragment : Fragment) (judgment : Judgment S) : Bool :=
  (judgmentFeatures judgment).all (fragment.enabled.contains ·)

theorem accepts_exact (fragment : Fragment) (judgment : Judgment S) :
    fragment.accepts judgment = true ↔ fragment.permits judgment := by
  simp only [Fragment.accepts, Fragment.permits, List.all_eq_true, List.contains_iff_mem]

theorem full_permits (judgment : Judgment S) : full.permits judgment := by
  intro feature _
  cases feature <;> simp [full]

theorem full_accepts (judgment : Judgment S) : full.accepts judgment = true :=
  (accepts_exact full judgment).mpr (full_permits judgment)

variable {D : Signature S}

/-- All intermediate conclusions must obey the selected vocabulary. Child
premises are separately checked by the original native certificate checker. -/
def certificateAllowed (fragment : Fragment) : Certificates.Refinement.Certificate D → Bool
  | .node rule children => fragment.accepts rule.conclusion &&
      decide (∀ i, certificateAllowed fragment (children i) = true)

inductive CertificatePermitted (fragment : Fragment) : Certificates.Refinement.Certificate D → Prop where
  | node (rule : RuleCode D) (children : Fin rule.premises.length → Certificates.Refinement.Certificate D)
      (root : fragment.permits rule.conclusion)
      (premises : ∀ i, CertificatePermitted fragment (children i)) :
      CertificatePermitted fragment (.node rule children)

theorem certificateAllowed_exact (fragment : Fragment)
    (certificate : Certificates.Refinement.Certificate D) :
    certificateAllowed fragment certificate = true ↔ CertificatePermitted fragment certificate := by
  induction certificate with
  | node rule children ih =>
      simp only [certificateAllowed, Bool.and_eq_true, accepts_exact, decide_eq_true_eq]
      constructor
      · rintro ⟨root, premises⟩
        exact .node rule children root (fun i => (ih i).mp (premises i))
      · intro permitted
        cases permitted with
        | node _ _ root premises => exact ⟨root, fun i => (ih i).mpr (premises i)⟩

theorem full_certificatePermitted (certificate : Certificates.Refinement.Certificate D) :
    CertificatePermitted full certificate := by
  induction certificate with
  | node rule children ih => exact .node rule children (full_permits rule.conclusion) ih

theorem full_certificateAllowed (certificate : Certificates.Refinement.Certificate D) :
    certificateAllowed full certificate = true :=
  (certificateAllowed_exact full certificate).mpr (full_certificatePermitted certificate)

def certificateAllowedFast (fragment : Fragment)
    (certificate : Certificates.Refinement.Certificate D) : Bool :=
  if fragment = full then true else certificateAllowed fragment certificate

theorem certificateAllowedFast_eq (fragment : Fragment)
    (certificate : Certificates.Refinement.Certificate D) :
    certificateAllowedFast fragment certificate = certificateAllowed fragment certificate := by
  unfold certificateAllowedFast
  split
  · rename_i same
    subst fragment
    exact (full_certificateAllowed certificate).symm
  · rfl

theorem certificateAllowedFast_exact (fragment : Fragment)
    (certificate : Certificates.Refinement.Certificate D) :
    certificateAllowedFast fragment certificate = true ↔ CertificatePermitted fragment certificate := by
  rw [certificateAllowedFast_eq]
  exact certificateAllowed_exact fragment certificate

inductive CheckResult where
  | vocabularyRefused
  | certificateRejected
  | accepted
  deriving DecidableEq, Repr

variable [DecidableEq S.TypeSymbol] [DecidableEq S.TermSymbol] [DecidableEq S.PredicateSymbol]

def checkedVocabulary (fragment : Fragment) (certificate : Certificates.Refinement.Certificate D)
    (judgment : Judgment S) : CheckResult :=
  if fragment.accepts judgment && certificateAllowed fragment certificate then
    if Certificates.Refinement.check certificate judgment then .accepted else .certificateRejected
  else .vocabularyRefused

/-- Full vocabulary admission is proved once for every native syntax and
certificate node. The independently specified certificate check still runs. -/
def check (fragment : Fragment) (certificate : Certificates.Refinement.Certificate D)
    (judgment : Judgment S) : CheckResult :=
  if fragment = full then
    if Certificates.Refinement.check certificate judgment then .accepted else .certificateRejected
  else checkedVocabulary fragment certificate judgment

theorem check_vocabulary_exact (fragment : Fragment)
    (certificate : Certificates.Refinement.Certificate D) (judgment : Judgment S) :
    check fragment certificate judgment = checkedVocabulary fragment certificate judgment := by
  unfold check
  split
  · rename_i same
    subst fragment
    simp only [checkedVocabulary, full_accepts, full_certificateAllowed, Bool.true_and, if_true]
  · rfl

theorem check_exact (fragment : Fragment) (certificate : Certificates.Refinement.Certificate D)
    (judgment : Judgment S) :
    check fragment certificate judgment = .accepted ↔
      fragment.permits judgment ∧ CertificatePermitted fragment certificate ∧
        ∃ derivation : Derivation D judgment, Certificates.Refinement.erase derivation = certificate := by
  rw [check_vocabulary_exact]
  simp only [checkedVocabulary]
  split
  · rename_i selected
    have clauses : fragment.accepts judgment = true ∧ certificateAllowed fragment certificate = true := by
      simpa only [Bool.and_eq_true] using selected
    have permitted : fragment.permits judgment ∧ CertificatePermitted fragment certificate :=
      ⟨(accepts_exact _ _).mp clauses.1, (certificateAllowed_exact _ _).mp clauses.2⟩
    split
    · rename_i checked
      exact ⟨fun _ => ⟨permitted.1, permitted.2, (Certificates.Refinement.check_exact _ _).mp checked⟩,
        fun _ => rfl⟩
    · rename_i rejected
      constructor
      · intro impossible; cases impossible
      · rintro ⟨_, _, derived⟩
        exact False.elim (rejected ((Certificates.Refinement.check_exact _ _).mpr derived))
  · rename_i refused
    constructor
    · intro impossible; cases impossible
    · rintro ⟨judgmentPermitted, certificatePermitted, _⟩
      apply False.elim
      apply refused
      simp only [Bool.and_eq_true]
      exact ⟨(accepts_exact _ _).mpr judgmentPermitted,
        (certificateAllowed_exact _ _).mpr certificatePermitted⟩

end Mettapedia.OSLF.NativeTypes.Generation.NativeLogic
