import Mettapedia.GSLT.Dedukti.ConfluenceApplied
import Mettapedia.GSLT.Dedukti.NormalFormFiber
import Mettapedia.GSLT.Dedukti.TwoRoutes

/-!
# Transporting the checker's decision along a translation into Dedukti

A translation of a logic into the λΠ-calculus modulo rewriting lets the
checker of the target decide the source's conversion under three conditions,
each a separate obligation of the translation:

1. **preservation**: source conversions become target conversions;
2. **reflection**: target conversions of translations come from source
   conversions (conservativity of conversion);
3. **the image is in the normal-form fiber** of the target: the translations
   have normal forms, and the target decides its conversion by them there.

`Mettapedia.Logic.Relation.DecidedOn.transport` states the general fact.  This
module instantiates it on the embedding of pure type systems of Cousineau and
Dowek (`CousineauDowek`), where the tree already proves the first two:

* preservation, `translate_conv`;
* reflection up to the erasure of sort annotations, `translate_reflects`.

The theory of the embedding is orthogonal, hence confluent
(`ConfluenceApplied.cdTheory_confluent`), so the third condition is exactly
weak normalization of the target on the translations
(`cd_decidedOn_iff`).  Under it, a source conversion forces the target normal
forms of the translations to be equal, and equal normal forms force
beta conversion of the erased source terms (`cd_transport`).  Normalization
of the translations is not proved here for any system beyond small controls
(`cd_transport_separates_vars`): it is the open obligation of this route.

The encoding of higher-order logic of Holide (`TwoRoutes.holTheory`) has one
rule, `term (arr a b) ↪ term a → term b`, which passes the orthogonality test
(`holTheory_check`); the encoding is therefore confluent
(`holTheory_confluent`), its conversion is decided by normal forms exactly
where it normalizes (`holTheory_decidedOn_iff`), and the confluence hypothesis
of `TwoRoutes.eta_statement_not_conv` is discharged
(`holTheory_eta_statement_not_conv`).

The six rules of the STTfa hub of Logipedia, transcribed from its theory file
(Logipedia, `theories/sttfa/sttfa.dk` at commit `0bcb193`; `STTfa.rules`):
`eta` is a defined symbol, `eta --> t => etap (p t)`, then `etap` at function
and at polymorphic codes, and `eps` at `forall`, `impl` and `forallP`.  They
pass the orthogonality test (`STTfa.check`), so they are confluent
(`STTfa.confluent`) and decide conversion by normal forms exactly where they
normalize (`STTfa.decidedOn_iff`).  On the translations of higher-order logic
they normalize (`HOLHubTransport`).

An earlier version of this module stated two of the six rules in another form:
`eta (arrow l r) ↪ eta l → eta r` in place of the definition of `eta`, and
`etap (p l) ↪ eta l` in place of the rule of `etap` at a function code.  That
variant agrees with the source on the translations of higher-order logic but
is a different theory: it does not convert `eta` with `λ t. etap (p t)`.

A translation fails the third condition whenever its image contains a
symmetric conversion between terms with free variables: a theory that
converts `f x y` with `f y x` and keeps `f u x` apart from `f v x` decides no
set containing both by normal forms (`Commutativity.not_decidedOn_of_commutative`).
-/

set_option autoImplicit false

namespace Mettapedia.GSLT.Dedukti.TranslationTransport

open Mettapedia.GSLT.LanguageDef
open Mettapedia.GSLT.LanguageDef.LF
open Mettapedia.GSLT.LanguageDef.LFProfile (Profile)
open Mettapedia.Logic.Relation (DecidedOn IsNormalFormOf WeaklyNormalizingOn)

/-- **The checker decides the translations of a pure type system by normal
forms exactly where they normalize.** -/
theorem cd_decidedOn_iff (profile : Profile) (S : Set PTerm) :
    DecidedOn (Step (cdTheory profile)) (translate '' S) ↔
      WeaklyNormalizingOn (Step (cdTheory profile)) (translate '' S) :=
  NormalFormFiber.decidedOn_iff_weaklyNormalizingOn_of_confluent (cdTheory_confluent profile) _

/-- **The checker's decision on translations, read back in the source.**
Where the translations normalize: a source conversion makes the target normal
forms equal, and equal normal forms give beta conversion of the erased source
terms. -/
theorem cd_transport (profile : Profile) {S : Set PTerm}
    (normalizing : WeaklyNormalizingOn (Step (cdTheory profile)) (translate '' S))
    {first second : PTerm} (firstMember : first ∈ S) (secondMember : second ∈ S)
    {firstNormal secondNormal : Term}
    (firstNormalForm : IsNormalFormOf (Step (cdTheory profile)) (translate first) firstNormal)
    (secondNormalForm : IsNormalFormOf (Step (cdTheory profile)) (translate second) secondNormal) :
    (PTerm.Conv first second → firstNormal = secondNormal) ∧
      (firstNormal = secondNormal → Conv Theory.empty first.erase second.erase) :=
  DecidedOn.transport translate (fun _ _ converted => translate_conv profile converted)
    (fun _ _ converted => translate_reflects profile converted)
    ((cd_decidedOn_iff profile S).mpr normalizing) firstMember secondMember firstNormalForm
    secondNormalForm

/-- The translation of a variable is the variable, which is normal. -/
theorem translate_var_normalForm (profile : Profile) (index : Nat) :
    IsNormalFormOf (Step (cdTheory profile)) (translate (.var index)) (.var index) :=
  ⟨.refl, var_normal (cdTheory_headed profile) index⟩

/-- The translations of two variables of the simply typed calculus have normal
forms. -/
theorem cd_normalizing_vars :
    WeaklyNormalizingOn (Step (cdTheory simplyTyped)) (translate '' {PTerm.var 0, PTerm.var 1}) := by
  rintro _ ⟨term, member, rfl⟩
  rcases member with rfl | rfl
  · exact ⟨_, translate_var_normalForm simplyTyped 0⟩
  · exact ⟨_, translate_var_normalForm simplyTyped 1⟩

/-- **A control**: on two variables of the simply typed calculus the
translations normalize, so the checker's decision separates them, and the
source does not convert them. -/
theorem cd_transport_separates_vars : ¬ PTerm.Conv (.var 0) (.var 1) := fun converted =>
  absurd ((cd_transport simplyTyped cd_normalizing_vars (Or.inl rfl) (Or.inr rfl)
    (translate_var_normalForm simplyTyped 0) (translate_var_normalForm simplyTyped 1)).1 converted)
    (by simp)

/-- A variable of a pure type system has no step. -/
theorem pterm_var_normal (index : Nat) :
    Mettapedia.Logic.Relation.IsNormal PTerm.Step (.var index) := by
  intro target step
  cases step

/-- **A control through simulation**: the translations of two variables of the
simply typed calculus are decided by normal forms, through
`decidedOn_image_of_simulation` (steps of the source are nonempty reductions
of the target, `translate_transGen`). -/
theorem cd_decidedOn_vars :
    DecidedOn (Step (cdTheory simplyTyped)) (translate '' {PTerm.var 0, PTerm.var 1}) := by
  refine Mettapedia.Logic.Relation.decidedOn_image_of_simulation translate
    (fun _ _ step => (translate_transGen simplyTyped step).to_reflTransGen) ?_
    (cdTheory_confluent simplyTyped) ?_
  · rintro a (rfl | rfl) n normalForm
    · rw [(pterm_var_normal 0).reflTransGen_eq normalForm.1]
      exact ⟨_, translate_var_normalForm simplyTyped 0⟩
    · rw [(pterm_var_normal 1).reflTransGen_eq normalForm.1]
      exact ⟨_, translate_var_normalForm simplyTyped 1⟩
  · rintro a (rfl | rfl)
    · exact ⟨_, .refl, pterm_var_normal 0⟩
    · exact ⟨_, .refl, pterm_var_normal 1⟩

/-! ## The encoding of higher-order logic of Holide -/

/-- **The rule of the Holide encoding passes the orthogonality test.** -/
theorem holTheory_check : orthogonalCheck [TwoRoutes.termArrow] = true := by decide

theorem holTheory_orthogonal : TwoRoutes.holTheory.Orthogonal :=
  orthogonal_of_check [TwoRoutes.termArrow] (fun _ member => member)
    (fun name => by simp [TwoRoutes.holTheory, Theory.ofSig, TwoRoutes.holSig,
      Mettapedia.GSLT.LanguageDef.LFTyping.lookupBody]) holTheory_check

/-- **The Holide encoding is confluent**, so its conversion is decided by
normal forms exactly where its reduction normalizes. -/
theorem holTheory_confluent : Mettapedia.Logic.Relation.Confluent (Step TwoRoutes.holTheory) :=
  confluent_of_orthogonal holTheory_orthogonal

theorem holTheory_decidedOn_iff (S : Set Term) :
    DecidedOn (Step TwoRoutes.holTheory) S ↔ WeaklyNormalizingOn (Step TwoRoutes.holTheory) S :=
  NormalFormFiber.decidedOn_iff_weaklyNormalizingOn_of_orthogonal holTheory_orthogonal S

/-- With the confluence hypothesis of `TwoRoutes.eta_statement_not_conv`
discharged: in the Holide encoding, the eta statement is not convertible with
the reflexivity statement. -/
theorem holTheory_eta_statement_not_conv :
    ¬ Conv TwoRoutes.holTheory TwoRoutes.etaAtVariable TwoRoutes.reflAtVariable :=
  TwoRoutes.eta_statement_not_conv holTheory_confluent

/-! ## The rules of the STTfa hub -/

namespace STTfa

/-- `eta a`: the type of the terms of a type code `a`. -/
def eta (code : Term) : Term := .app (.con "eta") code
/-- `etap a`: the type of the terms of a polymorphic type code. -/
def etap (code : Term) : Term := .app (.con "etap") code
/-- `eps p`: the type of the proofs of a proposition `p`. -/
def eps (proposition : Term) : Term := .app (.con "eps") proposition

def binary (name : String) (first second : Term) : Term := .app (.app (.con name) first) second

/-- `[] eta --> t => etap (p t)`: `eta` is defined as `λ t : type. etap (p t)`.
The source leaves the type of the bound variable implicit; it is `type`. -/
def etaDef : RewriteRule := ⟨.con "eta", .lam (.con "type") (etap (.app (.con "p") (.var 0)))⟩
/-- `[l,r] etap (p (arrow l r)) --> eta l -> eta r`. -/
def etapArrow : RewriteRule :=
  ⟨etap (.app (.con "p") (binary "arrow" (.var 1) (.var 0))), .pi (eta (.var 1)) (eta (.var 1))⟩
/-- `[f] etap (forallK f) --> x : type -> etap (f x)`. -/
def etapForall : RewriteRule :=
  ⟨etap (.app (.con "forallK") (.var 0)), .pi (.con "type") (etap (.app (.var 1) (.var 0)))⟩
/-- `[t,f] eps (forall t f) --> x : eta t -> eps (f x)`. -/
def epsForall : RewriteRule :=
  ⟨eps (binary "forall" (.var 1) (.var 0)), .pi (eta (.var 1)) (eps (.app (.var 1) (.var 0)))⟩
/-- `[l,r] eps (impl l r) --> eps l -> eps r`. -/
def epsImpl : RewriteRule := ⟨eps (binary "impl" (.var 1) (.var 0)), .pi (eps (.var 1)) (eps (.var 1))⟩
/-- `[f] eps (forallP f) --> x : type -> eps (f x)`. -/
def epsForallP : RewriteRule :=
  ⟨eps (.app (.con "forallP") (.var 0)), .pi (.con "type") (eps (.app (.var 1) (.var 0)))⟩

/-- **The six rules of the STTfa hub**, transcribed from Logipedia's theory file
`theories/sttfa/sttfa.dk` (commit `0bcb193`, 2019-11-05), in its order: the
definition of `eta`, the rule of `etap` at a function code and at a
polymorphic code, and the rules of `eps` at `forall`, `impl` and `forallP`. -/
def rules : List RewriteRule := [etaDef, etapArrow, etapForall, epsForall, epsImpl, epsForallP]

/-- The theory of these rules, with no definition and no declared types. -/
def theory : Theory := Theory.ofSig [] rules

/-- **The six rules pass the orthogonality test.** -/
theorem check : orthogonalCheck rules = true := by decide

theorem orthogonal : theory.Orthogonal :=
  orthogonal_of_check rules (fun _ member => member)
    (fun name => by simp [theory, Theory.ofSig, Mettapedia.GSLT.LanguageDef.LFTyping.lookupBody]) check

/-- **The rules of the hub are confluent**, so its conversion is decided by
normal forms exactly where it normalizes. -/
theorem confluent : Mettapedia.Logic.Relation.Confluent (Step theory) :=
  confluent_of_orthogonal orthogonal

theorem decidedOn_iff (S : Set Term) :
    DecidedOn (Step theory) S ↔ WeaklyNormalizingOn (Step theory) S :=
  NormalFormFiber.decidedOn_iff_weaklyNormalizingOn_of_orthogonal orthogonal S

end STTfa

#print axioms cd_decidedOn_iff
#print axioms cd_transport
#print axioms cd_transport_separates_vars
#print axioms cd_decidedOn_vars
#print axioms holTheory_check
#print axioms holTheory_confluent
#print axioms holTheory_eta_statement_not_conv
#print axioms STTfa.check
#print axioms STTfa.confluent

end Mettapedia.GSLT.Dedukti.TranslationTransport
