import Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeEnrichment
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureSumFormation
import Mettapedia.OSLF.NativeTypes.Certificates.NativeEnumeration

/-!
# Cube-gated native code and kind-evidence declarations

The enrichment adds code carriers, the two sort constants, generated former
codes and proof-relevant typing/kinding families. Formation operations consume
actual evidence at the chosen input slots and return evidence at the chosen
output slot. They are ordinary declarations in the common native grammar.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeDeclarations

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.Framework.ModalHypercube (HSort)
open CubeEnrichment

variable (D : CubeEnrichment.Signature)

inductive TypeSymbol where
  | code (carrier : D.Carrier)
  | typing (carrier : D.Carrier)

inductive TermSymbol where
  | sort (carrier : D.Carrier) (sort : HSort)
  | former (declaration : D.Former)
  | starBox (carrier : D.Carrier)
  | formation (declaration : D.Former)

abbrev symbols : Symbols where
  TypeSymbol := TypeSymbol D
  TermSymbol := TermSymbol D
  PredicateSymbol := Empty
  typeArity := fun symbol => match symbol with
    | .code _ => 0
    | .typing _ => 2
  termArity := fun symbol => match symbol with
    | .sort _ _ | .starBox _ => 0
    | .former declaration | .formation declaration => D.arity declaration
  predicateArity symbol := nomatch symbol

variable {D}

def codeType (carrier : D.Carrier) (n : Nat) : TypeExpr (symbols D) n :=
  .family (.code carrier) Fin.elim0

def sortCode (carrier : D.Carrier) (sort : HSort) (n : Nat) : TermExpr (symbols D) n :=
  .primitive (.sort carrier sort) Fin.elim0

def typingType (carrier : D.Carrier) {n : Nat} (value type : TermExpr (symbols D) n) :
    TypeExpr (symbols D) n :=
  .family (.typing carrier) (Fin.cases value (fun _ => type))

/-- Typing is inhabited-fibre readout, not a supplied predicate oracle. -/
def typing (carrier : D.Carrier) {n : Nat} (value type : TermExpr (symbols D) n) :
    PropExpr (symbols D) n := .image (typingType carrier value type)

def certifiedCode (carrier : D.Carrier) (sort : HSort) (n : Nat) : TypeExpr (symbols D) n :=
  .sigma (codeType carrier n) (typingType carrier (.var 0) (sortCode carrier sort (n + 1)))

/-- Newest-variable order is the same as the authored argument order. -/
def telescope (types : List (TypeExpr (symbols D) 0)) : ContextExpr (symbols D) types.length :=
  match types with
  | [] => .nil
  | type :: types => .snoc (telescope types) (type.rename Fin.elim0)

def inputs (declaration : D.Former) : List D.Carrier :=
  List.ofFn (D.input declaration)

def inputTypes (declaration : D.Former) : List (TypeExpr (symbols D) 0) :=
  (inputs declaration).map (fun carrier => codeType carrier 0)

def inputEvidenceTypes (vertex : Vertex D) (declaration : D.Former) : List (TypeExpr (symbols D) 0) :=
  List.ofFn fun position => certifiedCode (D.input declaration position) (inputSort D vertex declaration position) 0

@[simp] theorem inputTypes_length (declaration : D.Former) :
    (inputTypes declaration).length = D.arity declaration := by simp [inputTypes, inputs]

@[simp] theorem inputEvidenceTypes_length (vertex : Vertex D) (declaration : D.Former) :
    (inputEvidenceTypes vertex declaration).length = D.arity declaration := by simp [inputEvidenceTypes]

def vectorTelescope : {n : Nat} → (Fin n → TypeExpr (symbols D) 0) → ContextExpr (symbols D) n
  | 0, _ => .nil
  | n + 1, types => .snoc (vectorTelescope (fun position : Fin n => types position.succ))
      ((types 0).rename Fin.elim0)

def parameterContext (declaration : D.Former) : ContextExpr (symbols D) (D.arity declaration) :=
  vectorTelescope (fun position => codeType (D.input declaration position) 0)

def formationContext (vertex : Vertex D) (declaration : D.Former) :
    ContextExpr (symbols D) (D.arity declaration) :=
  vectorTelescope (fun position => certifiedCode (D.input declaration position)
    (inputSort D vertex declaration position) 0)

def typingContext (carrier : D.Carrier) : ContextExpr (symbols D) 2 :=
  .snoc (.snoc .nil (codeType carrier 0)) (codeType carrier 1)

def codeArguments (vertex : Vertex D) (declaration : D.Former) :
    Substitution (symbols D) (D.arity declaration) (D.arity declaration) :=
  fun position => .fst (codeType (D.input declaration position) _) 
    (typingType (D.input declaration position) (.var 0)
      (sortCode (D.input declaration position) (inputSort D vertex declaration position) _)) (.var position)

def formedCode (vertex : Vertex D) (declaration : D.Former) :
    TermExpr (symbols D) (D.arity declaration) :=
  .primitive (.former declaration) (codeArguments vertex declaration)

def formationResult (vertex : Vertex D) (declaration : D.Former) :
    TypeExpr (symbols D) (D.arity declaration) :=
  typingType (D.output declaration) (formedCode vertex declaration)
    (sortCode (D.output declaration) (outputSort D vertex declaration) _)

def ranks : SignatureSum.Ranks (symbols D) :=
  ⟨(fun symbol => match symbol with | .code _ => 0 | .typing _ => 2),
   (fun symbol => match symbol with | .sort _ _ | .former _ => 1 | .starBox _ | .formation _ => 3),
   (fun symbol => nomatch symbol)⟩

@[simp] theorem codeType_before (carrier : D.Carrier) (n bound : Nat) (positive : 0 < bound) :
    (codeType carrier n).before (ranks (D := D)).typeRank ranks.termRank ranks.predicateRank bound :=
  ⟨positive, fun position => Fin.elim0 position⟩

@[simp] theorem sortCode_before (carrier : D.Carrier) (sort : HSort) (n bound : Nat) (positive : 1 < bound) :
    (sortCode carrier sort n).before (ranks (D := D)).typeRank ranks.termRank ranks.predicateRank bound :=
  ⟨positive, fun position => Fin.elim0 position⟩

theorem certifiedCode_before (carrier : D.Carrier) (sort : HSort) (n bound : Nat) (positive : 2 < bound) :
    (certifiedCode carrier sort n).before (ranks (D := D)).typeRank ranks.termRank ranks.predicateRank bound := by
  refine ⟨codeType_before carrier n bound (Nat.lt_trans (by decide) positive), positive, ?_⟩
  intro position
  cases position using Fin.cases with
  | zero => trivial
  | succ _ => exact sortCode_before carrier sort _ bound (Nat.lt_trans (by decide) positive)

@[simp] theorem codeType_rename (carrier : D.Carrier) {n m : Nat} (mapping : Renaming n m) :
    (codeType carrier n).rename mapping = codeType carrier m := by
  apply congrArg (TypeExpr.family (S := symbols D) (.code carrier))
  funext position
  exact Fin.elim0 position

@[simp] theorem sortCode_rename (carrier : D.Carrier) (sort : HSort) {n m : Nat} (mapping : Renaming n m) :
    (sortCode carrier sort n).rename mapping = sortCode carrier sort m := by
  apply congrArg (TermExpr.primitive (S := symbols D) (.sort carrier sort))
  funext position
  exact Fin.elim0 position

@[simp] theorem certifiedCode_rename (carrier : D.Carrier) (sort : HSort) {n m : Nat} (mapping : Renaming n m) :
    (certifiedCode carrier sort n).rename mapping = certifiedCode carrier sort m := by
  simp only [certifiedCode, TypeExpr.rename, codeType_rename, typingType]
  apply congrArg (TypeExpr.sigma (codeType carrier m))
  apply congrArg (TypeExpr.family (S := symbols D) (.typing carrier))
  funext position
  cases position using Fin.cases with
  | zero => simp only [Fin.cases_zero, TermExpr.rename, liftRenaming_zero]
  | succ _ => exact sortCode_rename carrier sort _

theorem telescope_before (types : List (TypeExpr (symbols D) 0)) (bound : Nat)
    (formed : ∀ type ∈ types, ∀ n, (type.rename (Fin.elim0 : Renaming 0 n)).before
      (ranks (D := D)).typeRank ranks.termRank ranks.predicateRank bound) :
    (telescope types).before (ranks (D := D)).typeRank ranks.termRank ranks.predicateRank bound := by
  induction types with
  | nil => trivial
  | cons type types hypotheses =>
      exact ⟨hypotheses (fun item member => formed item (by simp [member])),
        formed type (by simp) _⟩

@[simp] theorem context_cast_before {n m : Nat} (equal : n = m)
    (context : ContextExpr (symbols D) n) (bound : Nat) :
    (cast (congrArg (ContextExpr (symbols D)) equal) context).before
      (ranks (D := D)).typeRank ranks.termRank ranks.predicateRank bound ↔
    context.before ranks.typeRank ranks.termRank ranks.predicateRank bound := by
  cases equal
  rfl

theorem vectorTelescope_before {n : Nat} (types : Fin n → TypeExpr (symbols D) 0) (bound : Nat)
    (formed : ∀ position m, ((types position).rename (Fin.elim0 : Renaming 0 m)).before
      (ranks (D := D)).typeRank ranks.termRank ranks.predicateRank bound) :
    (vectorTelescope types).before ranks.typeRank ranks.termRank ranks.predicateRank bound := by
  induction n with
  | zero => trivial
  | succ n hypotheses =>
      exact ⟨hypotheses (fun position => types position.succ) (fun position => formed position.succ),
        formed 0 _⟩

def signature (vertex : Vertex D) : Signature (symbols D) where
  typeRank := ranks.typeRank
  termRank := ranks.termRank
  predicateRank := ranks.predicateRank
  typeParameters symbol := match symbol with
    | .code _ => .nil
    | .typing carrier => typingContext carrier
  termParameters symbol := match symbol with
    | .sort _ _ | .starBox _ => .nil
    | .former declaration => parameterContext declaration
    | .formation declaration => formationContext vertex declaration
  predicateParameters symbol := nomatch symbol
  termResult symbol := match symbol with
    | .sort carrier _ => codeType carrier 0
    | .former declaration => codeType (D.output declaration) _
    | .starBox carrier => typingType carrier (sortCode carrier .star 0) (sortCode carrier .box 0)
    | .formation declaration => formationResult vertex declaration
  typeParameters_before := by
    intro symbol
    cases symbol with
    | code => trivial
    | typing carrier => exact ⟨⟨True.intro, codeType_before carrier 0 2 (by decide)⟩,
        codeType_before carrier 1 2 (by decide)⟩
  termParameters_before := by
    intro symbol
    cases symbol with
    | sort => trivial
    | starBox => trivial
    | former declaration =>
        exact vectorTelescope_before _ 1 (by
          intro position n
          rw [codeType_rename]
          exact codeType_before _ _ 1 (by decide))
    | formation declaration =>
        exact vectorTelescope_before _ 3 (by
          intro position n
          rw [certifiedCode_rename]
          exact certifiedCode_before _ _ n 3 (by decide))
  predicateParameters_before symbol := nomatch symbol
  termResult_before := by
    intro symbol
    cases symbol with
    | sort carrier sort => exact codeType_before carrier 0 1 (by decide)
    | former declaration => exact codeType_before _ _ 1 (by decide)
    | starBox carrier =>
        exact ⟨Nat.lt_succ_self 2, fun position => by
          cases position using Fin.cases with
          | zero => exact sortCode_before carrier .star 0 3 (by decide)
          | succ _ => exact sortCode_before carrier .box 0 3 (by decide)⟩
    | formation declaration =>
        refine ⟨Nat.lt_succ_self 2, ?_⟩
        intro position
        cases position using Fin.cases with
        | zero =>
            refine ⟨(show 1 < 3 by decide), ?_⟩
            intro index
            refine ⟨codeType_before _ _ 3 (by decide), ?_, True.intro⟩
            exact ⟨Nat.lt_succ_self 2, fun index => by
              cases index using Fin.cases with
              | zero => trivial
              | succ _ => exact sortCode_before _ _ _ 3 (by decide)⟩
        | succ _ => exact sortCode_before _ _ _ 3 (by decide)

end Mettapedia.OSLF.NativeTypes.Semantics.Presheaf.CubeNativeDeclarations
