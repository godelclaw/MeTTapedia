import Mettapedia.OSLF.Syntax.EquationalQuotient

/-!
# Executable, finite evidence for the existing binding-signature equations

This module uses `Term`, `Args`, `EqAxiom`, contextual metavariable
instantiation and capture-avoiding `bind` from the shipped binding layer.
There is no normalization oracle. Transitivity checks its intermediate term;
congruence checks each argument in exactly its declared extended context.

Certificates contain finite substitution vectors and finite metavariable
body tables, not executable substitution/provider callbacks or proof fields.
The replay result carries a proof constructed by the evaluator. The proof is
erased at execution; its construction is the soundness argument, rather than
a condition a certificate producer is asked to supply.

This is the intrinsically sorted/scoped replay layer. A raw `LanguageDef` wire
parser and a HOL-emission refinement are separate obligations. In particular,
no decision procedure for the existential equational theory is asserted.

-/

namespace Mettapedia.OSLF.Binding.EqualityCertificates

open Mettapedia.OSLF.Binding
set_option autoImplicit false

variable {S : Signature}

/-- One finite term per source-context variable. -/
inductive Substitution (S : Signature) : Ctx S → Ctx S → Type where
  | nil {Δ : Ctx S} : Substitution S [] Δ
  | cons {Γ Δ : Ctx S} {s : S.Srt} (head : Term S Δ s)
      (tail : Substitution S Γ Δ) : Substitution S (s :: Γ) Δ

namespace Substitution

def read : {Γ Δ : Ctx S} → Substitution S Γ Δ → Sub S Γ Δ
  | [], _, .nil, _, v => nomatch v
  | _ :: _, _, .cons head _, _, .zero => head
  | _ :: _, _, .cons _ tail, _, .succ v => read tail _ v

/-- A semantic finite substitution can be quoted by traversing its finite
source context. This construction does not enumerate terms or equations. -/
def quote {Δ : Ctx S} : (Γ : Ctx S) → Sub S Γ Δ → Substitution S Γ Δ
  | [], _ => .nil
  | _ :: Γ, sigma => .cons (sigma _ .zero)
      (quote Γ (fun s v => sigma s (.succ v)))

theorem read_quote {Δ : Ctx S} :
    (Γ : Ctx S) → (sigma : Sub S Γ Δ) → read (quote Γ sigma) = sigma
  | [], sigma => by
      funext s v
      exact nomatch v
  | _ :: Γ, sigma => by
      funext s v
      cases v with
      | zero => rfl
      | succ v =>
          exact congrFun (congrFun
            (read_quote Γ (fun s v => sigma s (.succ v))) s) v

/-- The finite-vector implementation denotes the original simultaneous
substitution, including every binder lift in that implementation. -/
theorem bind_quote {Γ Δ : Ctx S} {s : S.Srt}
    (sigma : Sub S Γ Δ) (term : Term S Γ s) :
    bind (read (quote Γ sigma)) term = bind sigma term := by
  rw [read_quote]

end Substitution

/-- Each metavariable body is stored once, in its dependency prefix followed
by the separate ambient context. This is a data list, not a provider call. -/
inductive Bodies (S : Signature) (Θ : Ctx S) : List (MetaArity S) → Type where
  | nil : Bodies S Θ []
  | cons {bs : Ctx S} {s : S.Srt} {rest : List (MetaArity S)}
      (head : Term S (bs ++ Θ) s) (tail : Bodies S Θ rest) :
      Bodies S Θ ((bs, s) :: rest)

namespace Bodies

def read {Θ : Ctx S} : {M : List (MetaArity S)} →
    Bodies S Θ M → ContextualAssignment S M Θ
  | [], .nil, i => Fin.elim0 i
  | _ :: _, .cons head _, ⟨0, _⟩ => head
  | _ :: _, .cons _ tail, ⟨n + 1, hn⟩ =>
      read tail ⟨n, Nat.lt_of_succ_lt_succ hn⟩

/-- Quote every contextual metavariable body in its declared finite slot. -/
def quote {Θ : Ctx S} : (M : List (MetaArity S)) →
    ContextualAssignment S M Θ → Bodies S Θ M
  | [], _ => .nil
  | _ :: rest, assignment => .cons (assignment ⟨0, by simp⟩)
      (quote rest (fun position => assignment position.succ))

theorem read_quote {Θ : Ctx S} : (M : List (MetaArity S)) →
    (assignment : ContextualAssignment S M Θ) → read (quote M assignment) = assignment
  | [], assignment => by funext position; exact Fin.elim0 position
  | _ :: rest, assignment => by
      funext position
      refine Fin.cases ?_ (fun smaller => ?_) position
      · rfl
      · exact congrFun (read_quote rest (fun i => assignment i.succ)) smaller

end Bodies

variable {M : List (MetaArity S)}

mutual
/-- All syntax in a certificate is finite. Context indices rule out dangling
variables before replay; they do not replace the runtime equality check in
`trans`, which can still fail for two individually valid proofs. -/
inductive Certificate (S : Signature) (M : List (MetaArity S))
    (E : List (EqAxiom S M)) : Ctx S → S.Srt → Type where
  | axiom (i : Fin E.length) {Θ Γ : Ctx S}
      (bodies : Bodies S Θ M) (ambient : Substitution S Θ Γ)
      (ordinary : Substitution S (E.get i).ctx Γ) :
      Certificate S M E Γ (E.get i).sort
  | refl {Γ : Ctx S} {s : S.Srt} (term : Term S Γ s) :
      Certificate S M E Γ s
  | symm {Γ : Ctx S} {s : S.Srt} (proof : Certificate S M E Γ s) :
      Certificate S M E Γ s
  | trans {Γ : Ctx S} {s : S.Srt}
      (first second : Certificate S M E Γ s) : Certificate S M E Γ s
  | cong {Γ : Ctx S} {s : S.Srt} (op : S.Op s)
      (arguments : ArgumentCertificates S M E (S.arity op) Γ) :
      Certificate S M E Γ s
  | substitute {Γ Δ : Ctx S} {s : S.Srt} (sigma : Substitution S Γ Δ)
      (proof : Certificate S M E Γ s) : Certificate S M E Δ s

inductive ArgumentCertificates (S : Signature) (M : List (MetaArity S))
    (E : List (EqAxiom S M)) : List (List S.Srt × S.Srt) → Ctx S → Type where
  | nil {Γ : Ctx S} : ArgumentCertificates S M E [] Γ
  | cons {Γ : Ctx S} {bs : List S.Srt} {s : S.Srt}
      {rest : List (List S.Srt × S.Srt)}
      (head : Certificate S M E (bs ++ Γ) s)
      (tail : ArgumentCertificates S M E rest Γ) :
      ArgumentCertificates S M E ((bs, s) :: rest) Γ
end

/-- A replay result, not a producer-supplied certificate. -/
structure Result (E : List (EqAxiom S M)) (Γ : Ctx S) (s : S.Srt) where
  left : Term S Γ s
  right : Term S Γ s
  evidence : EqClosure E left right

structure ArgumentResult (E : List (EqAxiom S M))
    (arity : List (List S.Srt × S.Srt)) (Γ : Ctx S) where
  left : Args S arity Γ
  right : Args S arity Γ
  evidence : EqArgs E left right

variable [opDec : ∀ s : S.Srt, DecidableEq (S.Op s)]

mutual
/-- Structural replay. There is no search for missing equality evidence. -/
def replay {E : List (EqAxiom S M)} : {Γ : Ctx S} → {s : S.Srt} →
    Certificate S M E Γ s → Option (Result E Γ s)
  | _, _, .axiom i bodies ambient ordinary =>
      some ⟨ContextualAssignment.instantiate bodies.read ambient.read ordinary.read
          (E.get i).lhs,
        ContextualAssignment.instantiate bodies.read ambient.read ordinary.read
          (E.get i).rhs,
        EqClosure.ax i bodies.read ambient.read ordinary.read⟩
  | _, _, .refl term => some ⟨term, term, EqClosure.refl term⟩
  | _, _, .symm certificate => do
      let result ← replay certificate
      pure ⟨result.right, result.left, EqClosure.symm result.evidence⟩
  | _, _, .trans first second => do
      let before ← replay first
      let after ← replay second
      if same : before.right = after.left then
        pure ⟨before.left, after.right,
          EqClosure.trans before.evidence (same.symm ▸ after.evidence)⟩
      else none
  | _, _, .cong op arguments => do
      let result ← replayArguments arguments
      pure ⟨Term.op op result.left, Term.op op result.right,
        EqClosure.cong op result.evidence⟩
  | _, _, .substitute sigma certificate => do
      let result ← replay certificate
      pure ⟨bind sigma.read result.left, bind sigma.read result.right,
        eqClosure_bind sigma.read result.evidence⟩

def replayArguments {E : List (EqAxiom S M)} :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    ArgumentCertificates S M E arity Γ → Option (ArgumentResult E arity Γ)
  | _, _, .nil => some ⟨Args.nil, Args.nil, EqArgs.nil⟩
  | _, _, .cons head tail => do
      let headResult ← replay head
      let tailResult ← replayArguments tail
      pure ⟨Args.cons headResult.left tailResult.left,
        Args.cons headResult.right tailResult.right,
        EqArgs.cons headResult.evidence tailResult.evidence⟩
end

def check {E : List (EqAxiom S M)} {Γ : Ctx S} {s : S.Srt}
    (certificate : Certificate S M E Γ s) (left right : Term S Γ s) : Bool :=
  match replay certificate with
  | none => false
  | some result => decide (result.left = left ∧ result.right = right)

/-- Accepted evidence proves the *existing* generated equational theory,
not a fresh relation defined to mean that this checker accepts. -/
theorem check_sound {E : List (EqAxiom S M)} {Γ : Ctx S} {s : S.Srt}
    (certificate : Certificate S M E Γ s) (left right : Term S Γ s)
    (accepted : check certificate left right = true) : EqClosure E left right := by
  cases outcome : replay certificate with
  | none => simp [check, outcome] at accepted
  | some result =>
      have endpoints : result.left = left ∧ result.right = right := by
        simpa [check, outcome] using accepted
      simpa only [endpoints.1, endpoints.2] using result.evidence

/-- Substitution does not silently use sequential, unlifted replacement. -/
theorem substitute_replays {E : List (EqAxiom S M)}
    {Γ Δ : Ctx S} {s : S.Srt} (sigma : Substitution S Γ Δ)
    (certificate : Certificate S M E Γ s) (result : Result E Γ s)
    (replayed : replay certificate = some result) :
    replay (.substitute sigma certificate) =
      some ⟨bind sigma.read result.left, bind sigma.read result.right,
        eqClosure_bind sigma.read result.evidence⟩ := by
  simp [replay, replayed]

/-- Two successful local proofs need not compose. The checker refuses a
mismatched intermediate term instead of asking a normalizer to identify it. -/
theorem trans_refuses_mismatch {E : List (EqAxiom S M)}
    {Γ : Ctx S} {s : S.Srt}
    (first second : Certificate S M E Γ s) (a b : Result E Γ s)
    (firstChecked : replay first = some a) (secondChecked : replay second = some b)
    (different : a.right ≠ b.left) : replay (.trans first second) = none := by
  simp [replay, firstChecked, secondChecked, different]

theorem refl_checked {E : List (EqAxiom S M)} {Γ : Ctx S} {s : S.Srt}
    (term : Term S Γ s) : check (Certificate.refl (E := E) term) term term = true := by
  simp [check, replay]

mutual
/-- Every derivation of the original generated equality has finite evidence.
This constructs evidence for an existing equality, rather than deciding equality. -/
theorem replay_complete {E : List (EqAxiom S M)} :
    {Γ : Ctx S} → {s : S.Srt} → {left right : Term S Γ s} →
    (derivation : EqClosure E left right) →
      ∃ certificate : Certificate S M E Γ s,
        replay certificate = some ⟨left, right, derivation⟩
  | _, _, _, _, .ax i bodies ambient ordinary => by
      refine ⟨.axiom i (Bodies.quote M bodies)
        (Substitution.quote _ ambient) (Substitution.quote _ ordinary), ?_⟩
      simp only [replay, Bodies.read_quote, Substitution.read_quote]
  | _, _, _, _, .refl term => ⟨.refl term, rfl⟩
  | _, _, _, _, .symm before => by
      obtain ⟨certificate, checked⟩ := replay_complete before
      exact ⟨.symm certificate, by simp [replay, checked]⟩
  | _, _, _, _, .trans before after => by
      obtain ⟨first, checkedFirst⟩ := replay_complete before
      obtain ⟨second, checkedSecond⟩ := replay_complete after
      exact ⟨.trans first second, by simp [replay, checkedFirst, checkedSecond]⟩
  | _, _, _, _, .cong operator arguments => by
      obtain ⟨certificates, checked⟩ := replayArguments_complete arguments
      exact ⟨.cong operator certificates, by simp [replay, checked]⟩

theorem replayArguments_complete {E : List (EqAxiom S M)} :
    {arity : List (List S.Srt × S.Srt)} → {Γ : Ctx S} →
    {left right : Args S arity Γ} → (derivation : EqArgs E left right) →
      ∃ certificates : ArgumentCertificates S M E arity Γ,
        replayArguments certificates = some ⟨left, right, derivation⟩
  | _, _, _, _, .nil => ⟨.nil, rfl⟩
  | _, _, _, _, .cons head tail => by
      obtain ⟨first, checkedFirst⟩ := replay_complete head
      obtain ⟨rest, checkedRest⟩ := replayArguments_complete tail
      exact ⟨.cons first rest, by simp [replayArguments, checkedFirst, checkedRest]⟩
end

theorem check_complete {E : List (EqAxiom S M)} {Γ : Ctx S} {s : S.Srt}
    (left right : Term S Γ s) :
    EqClosure E left right ↔ ∃ certificate : Certificate S M E Γ s,
      check certificate left right = true := by
  constructor
  · intro derivation
    obtain ⟨certificate, accepted⟩ := replay_complete derivation
    exact ⟨certificate, by simp [check, accepted]⟩
  · rintro ⟨certificate, accepted⟩
    exact check_sound certificate left right accepted

end Mettapedia.OSLF.Binding.EqualityCertificates
