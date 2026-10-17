import Mettapedia.Languages.MeTTa.HE.HOLContract.Backend
import Mettapedia.Logic.InstitutionBorrowing

/-!
# Replaceable backends are conservative routes

A backend of the contract (`Backend`) is admitted with two laws, preservation and reflection.
Read as theories of typing judgments, the two laws say exactly that the backend is a
conservative route from the contract's judgments to its own judgments (`Backend.route`,
`Backend.route_conservative`): preservation makes the translation a route, and reflection makes
it conservative.  The calculus of routes of `Logic.InstitutionBorrowing` then applies to
backends:

* the judgments a backend certifies about contract terms are exactly the contract's
  (`Backend.borrowed_eq`), so two admitted backends accept the same translated judgments
  (`Backend.agree`);
* a route into the contract's judgments borrows the same theory through every admitted backend
  (`Backend.borrowed_comp`, `Backend.borrowed_comp_eq`): replacing the backend changes no
  conclusion a client draws through the contract and adds no commitment.

What stays stable when an admitted backend is replaced is therefore the contract's judgments and
everything borrowed through them.  What a backend says beyond the image of the contract is its
own and may differ between backends (`dependentCore_exceeds_contract`).

Control: a checker that accepts every judgment carries the contract's judgments to its own, so
it is a route, but it is not conservative.  It certifies `⊤` at a base type
(`acceptAll_certifies_wrong_type`), which the contract refutes: preservation without reflection
adds commitments.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.HE.HOLContract

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.Logic.HOL
open Mettapedia.Logic.InstitutionBorrowing

universe u v uS

/-- A typing judgment about a closed intrinsic term of the contract: the term, the type it is
formed at, and a type it is claimed to have. -/
structure TypingJudgment (Const : Ty Atom → Type) where
  /-- The type the term is formed at. -/
  type : Ty Atom
  /-- The closed intrinsic term. -/
  term : Term Const [] type
  /-- The type the judgment claims for the term. -/
  claimed : Ty Atom

/-- The contract's judgments: a closed intrinsic term has its own type. -/
def contractJudgments (Const : Ty Atom → Type) : Set (TypingJudgment Const) :=
  {judgment | judgment.claimed = judgment.type}

namespace Backend

variable {Const : Ty Atom → Type}

/-- The judgments a backend accepts. -/
def judgments (backend : Backend.{u} Const) :
    Set (backend.BackendTerm × backend.BackendType) :=
  {judgment | backend.HasType judgment.1 judgment.2}

/-- **An admitted backend is a route of typing judgments**, by preservation. -/
def route (backend : Backend.{u} Const) :
    TheoryRoute (contractJudgments Const) backend.judgments where
  translate judgment :=
    (backend.translateTerm judgment.term, backend.translateType judgment.claimed)
  preserves := by
    rintro ⟨type, term, claimed⟩ (claimedEq : claimed = type)
    subst claimedEq
    exact backend.preserves term

/-- **The route of an admitted backend is conservative**, by reflection. -/
theorem route_conservative (backend : Backend.{u} Const) : backend.route.Conservative := by
  rintro ⟨type, term, claimed⟩ accepted
  exact backend.reflects term accepted

/-- The judgments a backend certifies about contract terms are the contract's judgments. -/
theorem borrowed_eq (backend : Backend.{u} Const) :
    backend.route.borrowed = contractJudgments Const :=
  (TheoryRoute.conservative_iff_borrowed_eq backend.route).mp backend.route_conservative

/-- **Admitted backends agree on the image of the contract.** -/
theorem agree (first : Backend.{u} Const) (second : Backend.{v} Const)
    (judgment : TypingJudgment Const) :
    first.HasType (first.translateTerm judgment.term) (first.translateType judgment.claimed) ↔
      second.HasType (second.translateTerm judgment.term)
        (second.translateType judgment.claimed) := by
  have firstEq : judgment ∈ first.route.borrowed ↔ judgment ∈ contractJudgments Const := by
    rw [first.borrowed_eq]
  have secondEq : judgment ∈ second.route.borrowed ↔ judgment ∈ contractJudgments Const := by
    rw [second.borrowed_eq]
  exact firstEq.trans secondEq.symm

/-- **Replacing a backend changes no borrowed theory**: a route into the contract's judgments
borrows through an admitted backend exactly what it borrows from the contract. -/
theorem borrowed_comp {Sentence : Type uS} {theory : Set Sentence}
    (client : TheoryRoute theory (contractJudgments Const)) (backend : Backend.{u} Const) :
    (client.comp backend.route).borrowed = client.borrowed :=
  TheoryRoute.borrowed_comp_of_conservative client backend.route_conservative

/-- Two admitted backends give a client route the same borrowed theory. -/
theorem borrowed_comp_eq {Sentence : Type uS} {theory : Set Sentence}
    (client : TheoryRoute theory (contractJudgments Const))
    (first : Backend.{u} Const) (second : Backend.{v} Const) :
    (client.comp first.route).borrowed = (client.comp second.route).borrowed := by
  rw [borrowed_comp, borrowed_comp]

/-- Two admitted backends add the same commitments to a client route. -/
theorem addedCommitments_comp_eq {Sentence : Type uS} {theory : Set Sentence}
    (client : TheoryRoute theory (contractJudgments Const))
    (first : Backend.{u} Const) (second : Backend.{v} Const) :
    (client.comp first.route).addedCommitments =
      (client.comp second.route).addedCommitments := by
  simp only [TheoryRoute.addedCommitments, borrowed_comp_eq client first second]

end Backend

/-! ## Control: preservation without reflection -/

/-- A checker that accepts every judgment, as a route from the contract's judgments. -/
def acceptAll (Const : Ty Atom → Type) :
    TheoryRoute (contractJudgments Const) (Set.univ : Set (TypingJudgment Const)) where
  translate judgment := judgment
  preserves _ _ := Set.mem_univ _

/-- The checker that accepts every judgment certifies `⊤` at a base type, a judgment the
contract refutes. -/
theorem acceptAll_certifies_wrong_type {Const : Ty Atom → Type} (atom : Atom) :
    (⟨.prop, .top, .base atom⟩ : TypingJudgment Const) ∈ (acceptAll Const).addedCommitments :=
  ⟨Set.mem_univ _, fun claimedEq => by
    have wrong : (Ty.base atom : Ty Atom) = Ty.prop := claimedEq
    cases wrong⟩

/-- **Preservation alone is not enough**: the checker that accepts every judgment is a route
that is not conservative. -/
theorem acceptAll_not_conservative {Const : Ty Atom → Type} (atom : Atom) :
    ¬ (acceptAll Const).Conservative := by
  rw [TheoryRoute.conservative_iff_addedCommitments_eq_empty]
  intro empty
  have member := acceptAll_certifies_wrong_type (Const := Const) atom
  rw [empty] at member
  exact member

#print axioms Backend.route_conservative
#print axioms Backend.borrowed_eq
#print axioms Backend.agree
#print axioms Backend.borrowed_comp
#print axioms Backend.borrowed_comp_eq
#print axioms Backend.addedCommitments_comp_eq
#print axioms acceptAll_certifies_wrong_type
#print axioms acceptAll_not_conservative

end Mettapedia.Languages.MeTTa.HE.HOLContract
