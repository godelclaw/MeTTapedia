import Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.NativeDependentSourceWire
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TelescopeFormationReadback
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationCheckedTelescopePrograms
import Mettapedia.Languages.MeTTa.OSLFCore.Atom

/-!
# Named contextual requests and the existing dependent telescope

The named reader covers the explicit Pi/Sigma/Id constructor notation used
by the judgment experiment. Its output is the existing annotated native
syntax. The checked universe reader is a parameter; no typing judgment is
inferred from parsing. Unknown symbol names remain declaration references.

Context rows are supplied oldest first. Internally they are reversed so the
nearest name is de Bruijn position zero. Closing a contextual request with
named lambdas or products agrees with reading its complete telescope first.
This is a syntax contract for the prototype, not verification of C parsing.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ContextualJudgmentReadback

open Mettapedia.Languages.MeTTa.OSLFCore (Atom)
open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Presentation
open TypedEquality.Normalization.ExecutableWrittenChecking (SourceContext)

variable {Head : Type}

def readRaw (head : Atom → Option Head) (names : List String) : Atom → Option (NativeSyntax.Raw Head)
  | .symbol name =>
      if name ∈ names then some (.var (names.idxOf name)) else some (.const (.mkSimple name))
  | .expression [.symbol "u", level] => NativeSyntax.Raw.head <$> head level
  | .expression [.symbol "->", .expression [.symbol name, .symbol ":", domain], body] => do
      return .pi (← readRaw head names domain) (← readRaw head (name :: names) body)
  | .expression [.symbol "sigma", .expression [.symbol name, .symbol ":", domain], body] => do
      return .sigma (← readRaw head names domain) (← readRaw head (name :: names) body)
  | .expression [.symbol "lam", .expression [.symbol name, .symbol ":", domain], body] => do
      return .lamTyped (← readRaw head names domain) (← readRaw head (name :: names) body)
  | .expression [.symbol "lam", .symbol name, body] =>
      NativeSyntax.Raw.lamBare <$> readRaw head (name :: names) body
  | .expression [.symbol "id", carrier, left, right] => do
      return .id (← readRaw head names carrier) (← readRaw head names left) (← readRaw head names right)
  | .expression [.symbol "app", function, argument] => do
      return .app (← readRaw head names function) (← readRaw head names argument)
  | .expression [.symbol "pair", first, second] => do
      return .pair (← readRaw head names first) (← readRaw head names second)
  | .expression [.symbol "fst", pair] => NativeSyntax.Raw.fst <$> readRaw head names pair
  | .expression [.symbol "snd", pair] => NativeSyntax.Raw.snd <$> readRaw head names pair
  | .expression [.symbol "refl", subject] => NativeSyntax.Raw.refl <$> readRaw head names subject
  | _ => none
termination_by term => sizeOf term

def readTerm (head : Atom → Option Head) (names : List String) (term : Atom) :
    Option (ATm Head names.length) := do
  NativeSyntax.decode names.length (← readRaw head names term)

/-- A displayed local name resolves to its nearest occurrence. Formation
and type lookup remain obligations of the subsequent judgment checker. -/
theorem local_name_readback (head : Atom → Option Head) (names : List String)
    (name : String) (present : name ∈ names) :
    readTerm head names (.symbol name) =
      some (.var ⟨names.idxOf name, List.idxOf_lt_length_iff.mpr present⟩) := by
  simp [readTerm, readRaw, present, NativeSyntax.decode, List.idxOf_lt_length_iff.mpr present]

abbrev Rows := List (String × Atom)

def readRow : Atom → Option (String × Atom)
  | .expression [.symbol ":", .symbol name, domain] => some (name, domain)
  | _ => none

def readRows : Atom → Option Rows
  | .expression rows => rows.mapM readRow
  | _ => none

/-- Newest-first working representation. Every domain is read outside its
own binder, including domains of variables unused by the conclusion. -/
def readTelescope (head : Atom → Option Head) : (rows : Rows) → Option (SourceContext Head (rows.map Prod.fst).length)
  | [] => some .nil
  | (name, domain) :: rest => do
      if name ∈ rest.map Prod.fst then none else do
        let prior ← readTelescope head rest
        let domain ← readTerm head (rest.map Prod.fst) domain
        return .snoc prior domain

def bindNamed (operation name : String) (domain body : Atom) : Atom :=
  .expression [.symbol operation, .expression [.symbol name, .symbol ":", domain], body]

def closeNamed (operation : String) : Rows → Atom → Atom
  | [], body => body
  | (name, domain) :: rest, body => closeNamed operation rest (bindNamed operation name domain body)

def closeTerm : {n : Nat} → SourceContext Head n → ATm Head n → ATm Head 0
  | _, .nil, term => term
  | _, .snoc prior domain, term => closeTerm prior (.lamTyped domain term)

def closeType : {n : Nat} → SourceContext Head n → ATm Head n → ATm Head 0
  | _, .nil, type => type
  | _, .snoc prior domain, type => closeType prior (.pi domain type)

theorem erase_closeTerm {n : Nat} (context : SourceContext Head n) (body : ATm Head n) :
    (closeTerm context body).erase = TelescopeAbstraction.closeTerm context.erase body.erase := by
  induction context with
  | nil => rfl
  | snoc prior domain ih => exact ih (.lamTyped domain body)

theorem erase_closeType {n : Nat} (context : SourceContext Head n) (type : ATm Head n) :
    (closeType context type).erase = TelescopeAbstraction.closeType context.erase type.erase := by
  induction context with
  | nil => rfl
  | snoc prior domain ih => exact ih (.pi domain type)

private theorem readTerm_bind (head : Atom → Option Head) (names : List String)
    (name : String) (domain body : Atom) :
    readTerm head names (bindNamed "lam" name domain body) =
      (do let domain ← readTerm head names domain
          let body ← readTerm head (name :: names) body
          return .lamTyped domain body) ∧
    readTerm head names (bindNamed "->" name domain body) =
      (do let domain ← readTerm head names domain
          let body ← readTerm head (name :: names) body
          return .pi domain body) := by
  simp only [readTerm, bindNamed, readRaw]
  cases hd : readRaw head names domain <;> cases hb : readRaw head (name :: names) body <;>
    simp [NativeSyntax.decode]

/-- The complete named lambda chain and independently decoded telescope
produce the same annotated term. Duplicate names are explicitly outside
this experiment's context-display contract. -/
theorem read_closed_term (head : Atom → Option Head) (rows : Rows)
    (distinct : (rows.map Prod.fst).Nodup) (body : Atom) :
    readTerm head [] (closeNamed "lam" rows body) =
      (do let context ← readTelescope head rows
          let term ← readTerm head (rows.map Prod.fst) body
          return closeTerm context term) := by
  induction rows generalizing body with
  | nil =>
      dsimp [closeNamed, readTelescope]
      cases found : readTerm head [] _ <;> simp_all [List.map, closeTerm]
  | cons row rest ih =>
      rcases row with ⟨name, domain⟩
      have parts : name ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by simpa using distinct
      rw [closeNamed, ih parts.2, (readTerm_bind head (rest.map Prod.fst) name domain body).1]
      simp only [readTelescope, parts.1, ↓reduceIte]
      cases hp : readTelescope head rest <;>
        cases hd : readTerm head (rest.map Prod.fst) domain <;>
        cases hb : readTerm head (name :: rest.map Prod.fst) body <;> simp_all [closeTerm, List.map]

theorem read_closed_type (head : Atom → Option Head) (rows : Rows)
    (distinct : (rows.map Prod.fst).Nodup) (type : Atom) :
    readTerm head [] (closeNamed "->" rows type) =
      (do let context ← readTelescope head rows
          let term ← readTerm head (rows.map Prod.fst) type
          return closeType context term) := by
  induction rows generalizing type with
  | nil =>
      dsimp [closeNamed, readTelescope]
      cases found : readTerm head [] _ <;> simp_all [List.map, closeType]
  | cons row rest ih =>
      rcases row with ⟨name, domain⟩
      have parts : name ∉ rest.map Prod.fst ∧ (rest.map Prod.fst).Nodup := by simpa using distinct
      rw [closeNamed, ih parts.2, (readTerm_bind head (rest.map Prod.fst) name domain type).2]
      simp only [readTelescope, parts.1, ↓reduceIte]
      cases hp : readTelescope head rest <;>
        cases hd : readTerm head (rest.map Prod.fst) domain <;>
        cases hb : readTerm head (name :: rest.map Prod.fst) type <;> simp_all [closeType, List.map]

theorem duplicate_context_refused (head : Atom → Option Head) (name : String) (first second : Atom) :
    readTelescope head [(name, first), (name, second)] = none := by
  simp [readTelescope]

theorem malformed_unused_row_refused (domain : Atom) :
    readRows (.expression [.expression [.symbol ":", .expression [], domain]]) = none := rfl

/-- After the named readback, application uses the existing annotated
capture-avoiding substitution, including written domains. -/
theorem substitution_after_read {n : Nat} (argument : ATm Head n) (body : ATm Head (n+1)) :
    NativeSyntax.decode n (NativeSyntax.substituteZero (NativeSyntax.encode argument) 0
      (NativeSyntax.encode body)) = some (ATm.inst0 argument body) :=
  NativeSyntax.substituteZero_decodes argument body

theorem renaming_after_read {n m : Nat} (term : ATm Head n)
    (rho : Ren n m) (raw : Nat → Nat)
    (agreement : ∀ index : Fin n, raw index.val = (rho index).val) :
    NativeSyntax.decode m (NativeSyntax.renameRaw raw (NativeSyntax.encode term)) =
      some (term.rename rho) := by
  rw [← NativeSyntax.encode_rename rho raw agreement, NativeSyntax.decode_encode]

/-- A successfully read rule becomes the existing typed telescope program.
The argument assignment types the actual application, whose beta result is
the same capture-avoiding substitution into the original body. -/
theorem read_rule_application (head : Atom → Option Head) (rows : Rows)
    (distinct : (rows.map Prod.fst).Nodup) (body : Atom)
    (context : SourceContext Head (rows.map Prod.fst).length)
    (term : ATm Head (rows.map Prod.fst).length)
    (contextRead : readTelescope head rows = some context)
    (termRead : readTerm head (rows.map Prod.fst) body = some term)
    {R : Rules Head} (universes : FormationSensitive.UniverseRegularity R)
    (joins : ∀ {u v}, R.isUniverse u → R.isUniverse v →
      ∃ w, R.isUniverse w ∧ R.join u v w)
    {type : Tm Head (rows.map Prod.fst).length}
    (source : FormationSensitive.Judgment R context.erase term.erase type)
    {m : Nat} {target : Ctx Head m} {arguments : Sub Head (rows.map Prod.fst).length m}
    (typed : FormationSensitive.CtxMor R context.erase target arguments) :
    ∃ written,
      readTerm head [] (closeNamed "lam" rows body) = some written ∧
      FormationSensitive.Typing R target
        (TelescopeAbstraction.applyClosed context.erase arguments (liftClosed written.erase))
        (subst arguments type) ∧
      TelescopeAbstraction.BetaSteps
        (TelescopeAbstraction.applyClosed context.erase arguments (liftClosed written.erase))
        (subst arguments term.erase) := by
  refine ⟨closeTerm context term, ?_, ?_, ?_⟩
  · rw [read_closed_term head rows distinct, contextRead, termRead]
    rfl
  · rw [erase_closeTerm]
    exact FormationCheckedTelescopePrograms.apply_typed typed
      (FormationCheckedTelescopePrograms.close_into_target universes joins source)
  · rw [erase_closeTerm]
    exact TelescopeAbstraction.applyClosed_beta context.erase arguments term.erase

def nativeClosed (head : Atom → Option Tower.Head) (rows : Rows) (body : Atom) := do
  let term ← readTerm head [] (closeNamed "lam" rows body)
  NativeDependentSourceWire.lower term

/-- The downstream native wire decoder reads precisely the annotated term
supplied by the named adapter. Successful output cannot drop a domain. -/
theorem nativeClosed_exact (head : Atom → Option Tower.Head) (rows : Rows) (body : Atom)
    {wire : NativeDependentSourceWire.Wire}
    (produced : nativeClosed head rows body = some wire) :
    ∃ term, readTerm head [] (closeNamed "lam" rows body) = some term ∧
      NativeDependentSourceWire.decodeScoped 0 wire = some term := by
  cases read : readTerm head [] (closeNamed "lam" rows body) with
  | none => simp [nativeClosed, read] at produced
  | some term =>
      exact ⟨term, rfl, NativeDependentSourceWire.lower_decode
        (by simpa [nativeClosed, read] using produced)⟩

#print axioms read_closed_term
#print axioms read_closed_type
#print axioms erase_closeTerm
#print axioms substitution_after_read
#print axioms renaming_after_read
#print axioms read_rule_application
#print axioms nativeClosed_exact

end Mettapedia.Languages.MeTTa.PrimeCandidates.DeclarationBased.ContextualJudgmentReadback
