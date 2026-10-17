import Mettapedia.GSLT.LanguageDef.ResourceExecution

/-!
# Policy-indexed preorders of executed authority translations

Objects retain the original theory family, authority and physical encoding.
An arrow carries a uniform polynomial machine. A comparison policy may also
require exact refusal behavior or reflection of arbitrary target proofs.
Existence of such arrows is a preorder; mutual simulation is an equivalence
relation. No meet, join, linear ordering, or p-optimal proof system is asserted.
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.ResourceTranslation

open SemanticEvidence HeterogeneousTheory

/-- A physical presentation of an independently qualified authority family. -/
structure EncodedAuthority where
  Kind : Type
  theory : TheoryFamily Kind
  authority : AuthorityContract theory
  Alphabet : Type
  [finite : Fintype Alphabet]
  [inhabited : Inhabited Alphabet]
  encoding : Computability.Encoding (Packet authority) Alphabet

attribute [instance] EncodedAuthority.finite EncodedAuthority.inhabited

/-- Replay of rejected certificates and global proof reflection are independent
requirements. Both are in addition to acceptance and semantic preservation. -/
structure ComparisonPolicy where
  exactReplay : Bool
  reflectScope : Bool
deriving DecidableEq

def ComparisonPolicy.Accepts (policy : ComparisonPolicy)
    {S T : EncodedAuthority}
    (f : OperationalTranslation S.authority T.authority S.encoding T.encoding) : Prop :=
  (policy.exactReplay = true → f.toTranslation.Exact) ∧
  (policy.reflectScope = true → f.toTranslation.toTheoryTranslation.ScopeReflecting)

/-- Existential comparison forgets which compiler and proof of its cost were
chosen. The witness-carrying operational arrow remains available separately. -/
def CanTranslate (policy : ComparisonPolicy) (S T : EncodedAuthority) : Prop :=
  ∃ f : OperationalTranslation S.authority T.authority S.encoding T.encoding,
    policy.Accepts f

theorem canTranslate_refl (policy : ComparisonPolicy) (S : EncodedAuthority) :
    CanTranslate policy S S := by
  refine ⟨OperationalTranslation.identity S.authority S.encoding, ?_, ?_⟩
  · intro _
    exact Translation.exact_identity
  · intro _ _ _ h
    exact h

theorem canTranslate_trans (policy : ComparisonPolicy) {S M T : EncodedAuthority}
    (first : CanTranslate policy S M) (second : CanTranslate policy M T) :
    CanTranslate policy S T := by
  obtain ⟨f, fe, fr⟩ := first
  obtain ⟨g, ge, gr⟩ := second
  refine ⟨f.comp g, ?_, ?_⟩
  · intro h
    exact OperationalTranslation.comp_exact f g (fe h) (ge h)
  · intro h kind claim proof
    exact fr h kind claim (gr h (f.mapKind kind) (f.mapClaim kind claim) proof)

/-- This is a preorder at a fixed policy and polynomial execution class. -/
abbrev comparisonPreorder (policy : ComparisonPolicy) : Preorder EncodedAuthority where
  le := CanTranslate policy
  le_refl := canTranslate_refl policy
  le_trans := fun _ _ _ => canTranslate_trans policy

/-- Mutual simulation identifies presentations only under the chosen policy.
It does not equate their axioms, models, exact proof lengths or search costs. -/
def mutualSimulation (policy : ComparisonPolicy) : Setoid EncodedAuthority where
  r S T := CanTranslate policy S T ∧ CanTranslate policy T S
  iseqv :=
    { refl := fun S => ⟨canTranslate_refl policy S, canTranslate_refl policy S⟩
      symm := fun h => ⟨h.2, h.1⟩
      trans := fun h k =>
        ⟨canTranslate_trans policy h.1 k.1, canTranslate_trans policy k.2 h.2⟩ }

/-- Dropping a requirement can enlarge the relation; it cannot remove routes. -/
theorem weakenPolicy {strong weak : ComparisonPolicy}
    (exactRequired : weak.exactReplay = true → strong.exactReplay = true)
    (reflectionRequired : weak.reflectScope = true → strong.reflectScope = true)
    {S T : EncodedAuthority} (route : CanTranslate strong S T) :
    CanTranslate weak S T := by
  obtain ⟨f, fe, fr⟩ := route
  exact ⟨f, fun h => fe (exactRequired h), fun h => fr (reflectionRequired h)⟩

/-- Polynomial checking is a property of an executed authority, separate from
the polynomial translation relation. No choice of axioms is fixed by it. -/
def PolynomialChecking (S : EncodedAuthority) : Prop :=
  ∃ implementation : CheckerExecution S.authority S.encoding,
    ProofSystems.PolyBoundedBy implementation.time (fun p => (S.encoding.encode p).length)

/-- Exact operational translation into a polynomial checker supplies a
polynomial checker for the source, including its refused certificates. -/
theorem polynomialChecking_of_exact_route {S T : EncodedAuthority}
    (f : OperationalTranslation S.authority T.authority S.encoding T.encoding)
    (exactReplay : f.toTranslation.Exact) (checked : PolynomialChecking T) :
    PolynomialChecking S := by
  obtain ⟨implementation, bound⟩ := checked
  exact ⟨CheckerExecution.via f exactReplay implementation,
    CheckerExecution.via_polynomial f exactReplay implementation bound⟩

theorem polynomialChecking_of_comparison {policy : ComparisonPolicy}
    (requiresExact : policy.exactReplay = true) {S T : EncodedAuthority}
    (route : CanTranslate policy S T) (checked : PolynomialChecking T) :
    PolynomialChecking S := by
  obtain ⟨f, exactReplay, _⟩ := route
  exact polynomialChecking_of_exact_route f (exactReplay requiresExact) checked

end Mettapedia.GSLT.LanguageDef.ResourceTranslation
