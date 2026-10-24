import Mettapedia.Languages.Megalodon.HenkinProofSoundness

/-!
# Recognition of the monomorphic native proof grammar

The recognizer excludes prefix type abstraction/application and `gpa`.
In an environment with plain term lookup types, it characterizes precisely
the existing proof fragment used by Henkin replay soundness. Recognition is
independent of successful inference and of the truth of declared axioms.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.Megalodon.HenkinTermInterpretation.NativeProof

open MathdataKernel HenkinTermInterpretation

def monomorphic : Pf → Bool
  | .hyp _ | .known _ => true
  | .proofApp function argument => monomorphic function && monomorphic argument
  | .termApp function argument => monomorphic function && supported argument
  | .proofLam proposition body => supported proposition && monomorphic body
  | .termLam _ body => monomorphic body
  | .gpa _ | .typeApp _ _ | .typeLam _ => false

theorem monomorphic_of_fragment {environment : Environment} {depth : Nat} {program : Pf}
    (fragment : Fragment environment depth program) : monomorphic program = true := by
  induction fragment <;> simp_all [monomorphic]

theorem fragment_of_monomorphic {environment : Environment} {depth : Nat}
    (plain : PlainEnvironment environment depth) {program : Pf}
    (ordinary : monomorphic program = true) : Fragment environment depth program := by
  induction program with
  | hyp index => exact .hyp index
  | known name => exact .known name
  | proofApp function argument ihf iha =>
      obtain ⟨one, two⟩ := Bool.and_eq_true_iff.mp ordinary
      exact .proofApp (ihf one) (iha two)
  | termApp function argument ih =>
      obtain ⟨one, two⟩ := Bool.and_eq_true_iff.mp ordinary
      exact .termApp (ih one) two (plain.plainLookups two)
  | proofLam proposition body ih =>
      obtain ⟨one, two⟩ := Bool.and_eq_true_iff.mp ordinary
      exact .proofLam one (plain.plainLookups one) (ih two)
  | termLam type body ih => exact .termLam (ih ordinary)
  | gpa | typeApp | typeLam => simp [monomorphic] at ordinary

theorem fragment_iff_monomorphic {environment : Environment} {depth : Nat}
    (plain : PlainEnvironment environment depth) (program : Pf) :
    Fragment environment depth program ↔ monomorphic program = true :=
  ⟨monomorphic_of_fragment, fragment_of_monomorphic plain⟩

#print axioms fragment_iff_monomorphic

end Mettapedia.Languages.Megalodon.HenkinTermInterpretation.NativeProof
