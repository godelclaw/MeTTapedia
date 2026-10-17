import Foundation.Propositional.Hilbert.Standard.Basic
import Mettapedia.Logic.DerivationGraph.CheckedCursor
import Mettapedia.GSLT.LanguageDef.KernelCheckingClasses
import Mettapedia.Machines.Cursor.ProofChecking
import Mettapedia.GSLT.Distinction.SimulationComposition
import Mettapedia.Logic.ModalCompanion.Derivations

/-!
# Native finite checking for intuitionistic and classical Hilbert logic

The source relations are Foundation's standard intuitionistic and classical
Hilbert calculi. Finite rule codes carry the actual formula instances;
checking compares their ordered premises and conclusion. Classical excluded
middle is enabled only in the classical profile. No Boolean decision
procedure or external prover is trusted as an inference rule.

Finite proof trees and chronological DAGs reuse the existing witness checker.
Coverage is proved against the independent Hilbert derivability relation,
including its arbitrary schematic substitutions. It is a certificate
checking result, not yet an intuitionistic proof-search decision procedure or
a proof-complexity comparison with extended Frege.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.PropositionalHilbertChecking

open LO.Propositional

abbrev Formula := LO.Propositional.Formula Nat

inductive Profile where
  | intuitionistic
  | classical
  deriving DecidableEq, Repr

def sourceAxioms : Profile → Axiom Nat
  | .intuitionistic => LO.Propositional.Int.axioms
  | .classical => LO.Propositional.Cl.axioms

def Source (profile : Profile) : Formula → Prop := Hilbert.Standard (sourceAxioms profile)

/-- The source rule instances, independently of their executable codes. -/
inductive Rule (profile : Profile) : List Formula → Formula → Prop where
  | truth : Rule profile [] (.imp .falsum .falsum)
  | k (a b : Formula) : Rule profile [] (.imp a (.imp b a))
  | s (a b c : Formula) : Rule profile []
      (.imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c)))
  | andLeft (a b : Formula) : Rule profile [] (.imp (.and a b) a)
  | andRight (a b : Formula) : Rule profile [] (.imp (.and a b) b)
  | andIntro (a b : Formula) : Rule profile [] (.imp a (.imp b (.and a b)))
  | orLeft (a b : Formula) : Rule profile [] (.imp a (.or a b))
  | orRight (a b : Formula) : Rule profile [] (.imp b (.or a b))
  | orElim (a b c : Formula) : Rule profile []
      (.imp (.imp a c) (.imp (.imp b c) (.imp (.or a b) c)))
  | explosion (a : Formula) : Rule profile [] (.imp .falsum a)
  | excludedMiddle (classical : profile = .classical) (a : Formula) :
      Rule profile [] (.or a (.imp a .falsum))
  | mp (a b : Formula) : Rule profile [.imp a b, a] b

inductive Code where
  | truth
  | k (a b : Formula)
  | s (a b c : Formula)
  | andLeft (a b : Formula)
  | andRight (a b : Formula)
  | andIntro (a b : Formula)
  | orLeft (a b : Formula)
  | orRight (a b : Formula)
  | orElim (a b c : Formula)
  | explosion (a : Formula)
  | excludedMiddle (a : Formula)
  | mp (a b : Formula)
  deriving DecidableEq

def Code.conclusion : Code → Formula
  | .truth => .imp .falsum .falsum
  | .k a b => .imp a (.imp b a)
  | .s a b c => .imp (.imp a (.imp b c)) (.imp (.imp a b) (.imp a c))
  | .andLeft a b => .imp (.and a b) a
  | .andRight a b => .imp (.and a b) b
  | .andIntro a b => .imp a (.imp b (.and a b))
  | .orLeft a b => .imp a (.or a b)
  | .orRight a b => .imp b (.or a b)
  | .orElim a b c => .imp (.imp a c) (.imp (.imp b c) (.imp (.or a b) c))
  | .explosion a => .imp .falsum a
  | .excludedMiddle a => .or a (.imp a .falsum)
  | .mp _ b => b

def Code.premises : Code → List Formula
  | .mp a b => [.imp a b, a]
  | _ => []

def Code.allowed (profile : Profile) : Code → Bool
  | .excludedMiddle _ => decide (profile = .classical)
  | _ => true

theorem Code.rule (profile : Profile) (code : Code) (allowed : code.allowed profile = true) :
    Rule profile code.premises code.conclusion := by
  cases code with
  | truth => exact .truth
  | k a b => exact .k a b
  | s a b c => exact .s a b c
  | andLeft a b => exact .andLeft a b
  | andRight a b => exact .andRight a b
  | andIntro a b => exact .andIntro a b
  | orLeft a b => exact .orLeft a b
  | orRight a b => exact .orRight a b
  | orElim a b c => exact .orElim a b c
  | explosion a => exact .explosion a
  | excludedMiddle a => exact .excludedMiddle (of_decide_eq_true allowed) a
  | mp a b => exact .mp a b

def checkRule (profile : Profile) (code : Code) (premises : List Formula) (conclusion : Formula) : Bool :=
  code.allowed profile && decide (premises = code.premises) && decide (conclusion = code.conclusion)

theorem checkRule_sound (profile : Profile) (code : Code) (premises : List Formula) (conclusion : Formula)
    (accepted : checkRule profile code premises conclusion = true) : Rule profile premises conclusion := by
  simp only [checkRule, Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨⟨allowed, rfl⟩, rfl⟩ := accepted
  exact code.rule profile allowed

theorem checkRule_complete (profile : Profile) (premises : List Formula) (conclusion : Formula)
    (rule : Rule profile premises conclusion) : ∃ code, checkRule profile code premises conclusion = true := by
  cases rule with
  | truth => exact ⟨.truth, rfl⟩
  | k a b => exact ⟨.k a b, by simp [checkRule, Code.allowed, Code.premises, Code.conclusion]⟩
  | s a b c => exact ⟨.s a b c, by simp [checkRule, Code.allowed, Code.premises, Code.conclusion]⟩
  | andLeft a b => exact ⟨.andLeft a b, by simp [checkRule, Code.allowed, Code.premises, Code.conclusion]⟩
  | andRight a b => exact ⟨.andRight a b, by simp [checkRule, Code.allowed, Code.premises, Code.conclusion]⟩
  | andIntro a b => exact ⟨.andIntro a b, by simp [checkRule, Code.allowed, Code.premises, Code.conclusion]⟩
  | orLeft a b => exact ⟨.orLeft a b, by simp [checkRule, Code.allowed, Code.premises, Code.conclusion]⟩
  | orRight a b => exact ⟨.orRight a b, by simp [checkRule, Code.allowed, Code.premises, Code.conclusion]⟩
  | orElim a b c => exact ⟨.orElim a b c, by simp [checkRule, Code.allowed, Code.premises, Code.conclusion]⟩
  | explosion a => exact ⟨.explosion a, by simp [checkRule, Code.allowed, Code.premises, Code.conclusion]⟩
  | excludedMiddle classical a => exact ⟨.excludedMiddle a, by simp [checkRule, Code.allowed, Code.premises, Code.conclusion, classical]⟩
  | mp a => exact ⟨.mp a conclusion, by simp [checkRule, Code.allowed, Code.premises, Code.conclusion]⟩

def interface (profile : Profile) : RuleWitness (Rule profile) where
  W := Code
  isInstance := checkRule profile
  sound := checkRule_sound profile
  complete := checkRule_complete profile

theorem rule_source (profile : Profile) {premises : List Formula} {conclusion : Formula}
    (rule : Rule profile premises conclusion) (earlier : ∀ premise ∈ premises, Source profile premise) :
    Source profile conclusion := by
  cases rule with
  | truth => exact Hilbert.Standard.verum
  | k a b => exact Hilbert.Standard.implyS a b
  | s a b c => exact Hilbert.Standard.implyK a b c
  | andLeft a b => exact Hilbert.Standard.andElimL a b
  | andRight a b => exact Hilbert.Standard.andElimR a b
  | andIntro a b => exact Hilbert.Standard.andIntro a b
  | orLeft a b => exact Hilbert.Standard.orIntroL a b
  | orRight a b => exact Hilbert.Standard.orIntroR a b
  | orElim a b c => exact Hilbert.Standard.orElim a b c
  | explosion a =>
      have member : LO.Axioms.EFQ (.atom 0) ∈ sourceAxioms profile := by cases profile <;> simp [sourceAxioms]
      exact Hilbert.Standard.axm (fun _ => a) member
  | excludedMiddle classical a =>
      subst profile
      exact Hilbert.Standard.axm (φ := LO.Axioms.LEM (.atom 0)) (fun _ => a) (by simp [sourceAxioms])
  | mp a => exact Hilbert.Standard.mdp (earlier (.imp a conclusion) (by simp)) (earlier a (by simp))

theorem derives_source (profile : Profile) {formula : Formula} :
    Derives (Rule profile) formula → Source profile formula :=
  Derives.least (Source profile) (fun _ _ rule earlier => rule_source profile rule earlier)

private theorem leaf (profile : Profile) {formula : Formula} (rule : Rule profile [] formula) :
    Derives (Rule profile) formula := .node [] formula rule (by simp)

theorem source_derives (profile : Profile) {formula : Formula} (source : Source profile formula) :
    Derives (Rule profile) formula := by
  induction source with
  | axm substitution member =>
      cases profile with
      | intuitionistic =>
          simp only [sourceAxioms, Set.mem_singleton_iff] at member
          subst_vars
          exact leaf _ (.explosion (substitution 0))
      | classical =>
          simp only [sourceAxioms, Set.mem_insert_iff, Set.mem_singleton_iff] at member
          rcases member with rfl | rfl
          · exact leaf _ (.explosion (substitution 0))
          · exact leaf _ (.excludedMiddle rfl (substitution 0))
  | @mdp a b implication premise ihImp ihPrem =>
      exact .node [.imp a b, a] b (.mp a b) (by
        intro wanted member
        rcases List.mem_cons.mp member with same | tail
        · cases same
          exact ihImp
        · have same : wanted = a := List.mem_singleton.mp tail
          cases same
          exact ihPrem)
  | verum => exact leaf _ .truth
  | implyS a b => exact leaf _ (.k a b)
  | implyK a b c => exact leaf _ (.s a b c)
  | andElimL a b => exact leaf _ (.andLeft a b)
  | andElimR a b => exact leaf _ (.andRight a b)
  | andIntro a b => exact leaf _ (.andIntro a b)
  | orIntroL a b => exact leaf _ (.orLeft a b)
  | orIntroR a b => exact leaf _ (.orRight a b)
  | orElim a b c => exact leaf _ (.orElim a b c)

theorem source_iff_derives (profile : Profile) (formula : Formula) :
    Source profile formula ↔ Derives (Rule profile) formula :=
  ⟨source_derives profile, derives_source profile⟩

abbrev Certificate := Derivation Formula Code

def checker (profile : Profile) : Mettapedia.GSLT.LanguageDef.KernelAuthority.Checker Formula Certificate where
  check formula certificate := decide (certificate.concl = formula) && certificate.valid (interface profile)

theorem check_sound (profile : Profile) (formula : Formula) (certificate : Certificate)
    (accepted : (checker profile).check formula certificate = true) : Source profile formula := by
  simp only [checker, Bool.and_eq_true, decide_eq_true_eq] at accepted
  exact accepted.1 ▸ derives_source profile (certificate.valid_sound (interface profile) accepted.2)

theorem check_coverage (profile : Profile) (formula : Formula) :
    (∃ certificate, (checker profile).check formula certificate = true) ↔ Source profile formula := by
  constructor
  · rintro ⟨certificate, accepted⟩
    exact check_sound profile formula certificate accepted
  · intro source
    obtain ⟨certificate, valid, conclusion⟩ :=
      Derives.exists_derivation (interface profile) (source_derives profile source)
    refine ⟨certificate, ?_⟩
    change (decide (certificate.concl = formula) && certificate.valid (interface profile)) = true
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true conclusion, valid⟩

/-- The source-address worker retains this calculus's literal formulas and
rule codes. Its report concerns the checked schedule; selecting a theorem
also requires finding its root in the retained checked cache. -/
def object {Origin : Type} (profile : Profile)
    (store : DerivationGraph.BorrowedCursor.Store Formula Code Origin) :=
  Mettapedia.GSLT.Distinction.ProductiveBlocks.ObservedMachine.of
    (Mettapedia.Machines.Cursor.ProofChecking.machine (interface profile) store)

theorem dag_coverage {Origin : Type} (profile : Profile) (origin : Origin) (formula : Formula) :
    Source profile formula ↔
      ∃ (nodes : List (DerivationGraph.Node Formula Code Origin)) (cache : Array Formula) (root : Nat),
        DerivationGraph.replay (interface profile) nodes = some cache ∧ cache[root]? = some formula := by
  constructor
  · intro source
    exact DerivationGraph.exists_replay_of_derives (interface profile) origin (source_derives profile source)
  · rintro ⟨nodes, cache, root, replayed, found⟩
    exact derives_source profile (DerivationGraph.root_sound (interface profile) replayed found)

/-! ## Computable retained proof terms -/

def Profile.isClassical : Profile → Bool
  | .intuitionistic => false
  | .classical => true

/-- The existing native Hilbert proof-term family, with the classical
constructor available exactly in the classical profile. -/
abbrev ProofTerm (profile : Profile) (formula : Formula) :=
  ModalCompanion.PropDeriv profile.isClassical [] formula

def Code.realize (profile : Profile) (code : Code)
    (allowed : code.allowed profile = true)
    (earlier : ∀ formula ∈ code.premises, ProofTerm profile formula) :
    ProofTerm profile code.conclusion := by
  cases code with
  | truth => exact ModalCompanion.PropDeriv.selfImp .falsum
  | k a b => exact .implyK a b
  | s a b c => exact .implyS a b c
  | andLeft a b => exact .andElimL a b
  | andRight a b => exact .andElimR a b
  | andIntro a b => exact .andIntro a b
  | orLeft a b => exact .orIntroL a b
  | orRight a b => exact .orIntroR a b
  | orElim a b c => exact .orElim a b c
  | explosion a => exact .efq a
  | excludedMiddle a =>
      have classical : profile = .classical := of_decide_eq_true allowed
      subst profile
      exact .lem a rfl
  | mp a b =>
      exact .mdp (earlier (.imp a b) (by simp [premises]))
        (earlier a (by simp [premises]))

/-- Construct the retained term from the supplied certificate's children.
The finite index lookup is computed; no choice of an existential derivation
is used to obtain executable evidence. -/
def elaborateChecked (profile : Profile) : (certificate : Certificate) →
    certificate.valid (interface profile) = true → ProofTerm profile certificate.concl
  | .node conclusion code arity children, accepted => by
      have parts : checkRule profile code (List.ofFn fun i => (children i).concl) conclusion = true ∧
          ∀ i, (children i).valid (interface profile) = true := by
        simpa only [Derivation.valid, interface, Bool.and_eq_true, List.all_eq_true,
          List.forall_mem_ofFn_iff, id] using accepted
      have shape : (code.allowed profile = true ∧
          (List.ofFn fun i => (children i).concl) = code.premises) ∧ conclusion = code.conclusion := by
        simpa only [checkRule, Bool.and_eq_true, decide_eq_true_eq] using parts.1
      have previous : ∀ formula ∈ code.premises, ProofTerm profile formula := by
        intro formula member
        let claims := List.ofFn fun i => (children i).concl
        have present : formula ∈ claims := by
          change formula ∈ List.ofFn (fun i => (children i).concl)
          rw [shape.1.2]
          exact member
        let index : Fin arity := ⟨claims.idxOf formula, by
          simpa only [claims, List.length_ofFn] using List.idxOf_lt_length_of_mem present⟩
        have selected : (children index).concl = formula := by
          simpa only [claims, List.getElem_ofFn, index] using
            List.getElem_idxOf (List.idxOf_lt_length_of_mem present)
        exact selected ▸ elaborateChecked profile (children index) (parts.2 index)
      exact shape.2.symm ▸ code.realize profile shape.1.1 previous

/-- Check before publishing the retained proof term. Refused input yields
no term, including a correctly typed proof of a different requested claim. -/
def elaborate? (profile : Profile) (formula : Formula) (certificate : Certificate) :
    Option (ProofTerm profile formula) :=
  if accepted : (checker profile).check formula certificate = true then
    have parts : certificate.concl = formula ∧ certificate.valid (interface profile) = true := by
      simpa only [checker, Bool.and_eq_true, decide_eq_true_eq] using accepted
    some (parts.1 ▸ elaborateChecked profile certificate parts.2)
  else none

theorem elaborate?_isSome (profile : Profile) (formula : Formula) (certificate : Certificate) :
    (elaborate? profile formula certificate).isSome = true ↔
      (checker profile).check formula certificate = true := by
  by_cases accepted : (checker profile).check formula certificate = true <;>
    simp [elaborate?, accepted]

theorem retained_coverage (profile : Profile) (formula : Formula) :
    (∃ certificate, (elaborate? profile formula certificate).isSome = true) ↔ Source profile formula := by
  simp only [elaborate?_isSome]
  exact check_coverage profile formula

namespace Controls

def atom : Formula := .atom 0
def em : Formula := .or atom (.imp atom .falsum)
def emCertificate : Certificate := .node em (.excludedMiddle atom) 0 Fin.elim0

theorem classical_em_accepted : (checker .classical).check em emCertificate = true := by decide
theorem intuitionistic_em_rule_refused : (checker .intuitionistic).check em emCertificate = false := by decide

theorem missing_mp_premise : checkRule .classical (.mp atom atom) [atom] atom = false := by decide
theorem false_root_refused : (checker .classical).check .falsum emCertificate = false := by decide

end Controls
end Mettapedia.Logic.PropositionalHilbertChecking
