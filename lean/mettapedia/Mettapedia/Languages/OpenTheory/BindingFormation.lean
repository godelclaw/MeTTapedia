import Mettapedia.Languages.OpenTheory.SignatureFormation
import Mettapedia.Languages.OpenTheory.SourceBinding

/-!
# Declaration formation through binder closing and opening

These operations preserve admitted constant and type annotations. Their
binding and typing laws remain the existing shared STT constructions.
Opening requires formation of the actual replacement, including occurrences
under nested binders.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.OpenTheory.SignatureFormation

theorem AnnotationsFormed.closeFreeAt (signature : Signature) (needle : SourceVar)
    {term : DBTerm} (formed : AnnotationsFormed signature term) (depth : Nat) :
    AnnotationsFormed signature (DBTerm.closeFreeAt needle depth term) := by
  induction formed generalizing depth with
  | constant annotation declared => simpa only [DBTerm.closeFreeAt] using AnnotationsFormed.constant annotation declared
  | @free sourceVar annotation =>
      simp only [DBTerm.closeFreeAt]
      split
      · exact .bound depth
      · exact .free annotation
  | bound index => simpa only [DBTerm.closeFreeAt] using AnnotationsFormed.bound (signature := signature) index
  | app _ _ functionIH argumentIH => simpa only [DBTerm.closeFreeAt] using AnnotationsFormed.app (functionIH depth) (argumentIH depth)
  | abs domain _ bodyIH => simpa only [DBTerm.closeFreeAt] using AnnotationsFormed.abs domain (bodyIH (depth + 1))

theorem AnnotationsFormed.instantiateAt (signature : Signature) (replacement : DBTerm)
    (replacementFormed : AnnotationsFormed signature replacement)
    {term : DBTerm} (formed : AnnotationsFormed signature term) (depth : Nat) :
    AnnotationsFormed signature (DBTerm.instantiateAt replacement depth term) := by
  induction formed generalizing depth with
  | constant annotation declared => simpa only [DBTerm.instantiateAt] using AnnotationsFormed.constant annotation declared
  | free annotation => simpa only [DBTerm.instantiateAt] using AnnotationsFormed.free annotation
  | bound index =>
      simp only [DBTerm.instantiateAt]
      split
      · exact replacementFormed
      · exact .bound index
  | app _ _ functionIH argumentIH => simpa only [DBTerm.instantiateAt] using AnnotationsFormed.app (functionIH depth) (argumentIH depth)
  | abs domain _ bodyIH => simpa only [DBTerm.instantiateAt] using AnnotationsFormed.abs domain (bodyIH (depth + 1))

theorem AnnotationsFormed.abstractFree (signature : Signature) (needle : SourceVar)
    (needleFormed : TypeFormed signature needle.ty) (body : CanonicalTerm)
    (formed : AnnotationsFormed signature body.term) :
    AnnotationsFormed signature (body.abstractFree needle).term :=
by
  simpa only [CanonicalTerm.abstractFree] using
    AnnotationsFormed.abs needleFormed (formed.closeFreeAt signature needle 0)

end Mettapedia.Languages.OpenTheory.SignatureFormation
