import Mettapedia.OSLF.NativeTypes.Generation.NativeModalHeaders
import Mettapedia.TypeTheory.Calculi.NativeDependent.RefinementSignatureExtensionFormation

/-!
# Native operational declarations sharing authored program carriers

The extension preserves every authored constructor header. Each generated
modal event is indexed by its actual input; source, specified target and focus
projections use the independently decoded authored native carriers.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.Generation.NativeModalSignature

open Mettapedia.TypeTheory.Calculi.NativeDependent.Refinement
open Mettapedia.OSLF.MeTTaIL.GeneralExecutionAdmission
open NativeSignature SignatureSum

variable (plan : Plan) (installed : Installation plan.snapshot.language)
    (modal : List (NativeModalHeaders.Header plan))

abbrev Index (count : Nat) := Fin count

inductive TypeSymbol (count : Nat) where
  | input (index : Index count)
  | event (index : Index count)
  deriving DecidableEq, Encodable

inductive TermSymbol (count : Nat) (rely matched : Fin count → Nat) where
  | source (index : Index count)
  | target (index : Index count)
  | focus (index : Index count)
  | rely (index : Index count) (position : Fin (rely index))
  | matched (index : Index count) (position : Fin (matched index))
  deriving DecidableEq

abbrev TermSymbol.Code (count : Nat) (rely matched : Fin count → Nat) :=
  Fin count ⊕ (Fin count ⊕ (Fin count ⊕
    ((Sigma fun index => Fin (rely index)) ⊕ (Sigma fun index => Fin (matched index)))))

def TermSymbol.code {count : Nat} {rely matched : Fin count → Nat} :
    TermSymbol count rely matched → TermSymbol.Code count rely matched
  | .source index => .inl index
  | .target index => .inr (.inl index)
  | .focus index => .inr (.inr (.inl index))
  | .rely index position => .inr (.inr (.inr (.inl ⟨index, position⟩)))
  | .matched index position => .inr (.inr (.inr (.inr ⟨index, position⟩)))

def TermSymbol.ofCode {count : Nat} {rely matched : Fin count → Nat} :
    TermSymbol.Code count rely matched → TermSymbol count rely matched
  | .inl index => .source index
  | .inr (.inl index) => .target index
  | .inr (.inr (.inl index)) => .focus index
  | .inr (.inr (.inr (.inl ⟨index, position⟩))) => .rely index position
  | .inr (.inr (.inr (.inr ⟨index, position⟩))) => .matched index position

@[simp] theorem TermSymbol.ofCode_code {count : Nat} {rely matched : Fin count → Nat}
    (symbol : TermSymbol count rely matched) : TermSymbol.ofCode symbol.code = symbol := by
  cases symbol <;> rfl

instance {count : Nat} {rely matched : Fin count → Nat} : Encodable (TermSymbol count rely matched) :=
  Encodable.ofLeftInjection TermSymbol.code (fun code => some (TermSymbol.ofCode code))
    (fun symbol => congrArg some (TermSymbol.ofCode_code symbol))

abbrev Projection := TermSymbol modal.length (fun index => modal[index].rely.length)
  (fun index => modal[index].matched.length)

def TermSymbol.index {count : Nat} {rely matched : Fin count → Nat} : TermSymbol count rely matched → Fin count
  | .source index | .target index | .focus index | .rely index _ | .matched index _ => index

abbrev extraSymbols (modal : List (NativeModalHeaders.Header plan)) : Symbols where
  TypeSymbol := TypeSymbol modal.length
  TermSymbol := Projection plan modal
  PredicateSymbol := Empty
  typeArity := fun symbol => match symbol with | .input _ => 0 | .event _ => 1
  termArity _ := 2
  predicateArity symbol := nomatch symbol

abbrev symbols := SignatureSum.symbols installed.symbols (extraSymbols plan modal)

def extraRanks (modal : List (NativeModalHeaders.Header plan)) : Ranks (extraSymbols plan modal) :=
  ⟨fun symbol => match symbol with | .input _ => 1 | .event _ => 2,
    fun _ => 3, fun symbol => nomatch symbol⟩

def inputType (index : Fin modal.length) (n : Nat) : TypeExpr (symbols plan installed modal) n :=
  .family (.inr (.input index)) Fin.elim0

def inputContext (index : Fin modal.length) : ContextExpr (symbols plan installed modal) 1 :=
  .snoc .nil (inputType plan installed modal index 0)

def singletonArgument {n : Nat} (value : TermExpr (symbols plan installed modal) n) :
    Substitution (symbols plan installed modal) 1 n := extendSubstitution Fin.elim0 value

def eventType (index : Fin modal.length) {n : Nat} (input : TermExpr (symbols plan installed modal) n) :
    TypeExpr (symbols plan installed modal) n :=
  .family (.inr (.event index)) (singletonArgument plan installed modal input)

def eventContext (index : Fin modal.length) : ContextExpr (symbols plan installed modal) 2 :=
  .snoc (inputContext plan installed modal index)
    (eventType plan installed modal index (.var 0))

def authoredType (carrier : Carrier plan.snapshot.language) (n : Nat) :
    TypeExpr (symbols plan installed modal) n :=
  typeLeft (carrier.native (headers := installed.headers))

def projectionCarrier (projection : Projection plan modal) : Carrier plan.snapshot.language :=
  match projection with
  | .source index | .target index => modal[index].program
  | .focus index => (modal[index]).focusArgument
  | .rely index position => (modal[index]).rely[position].carrier
  | .matched index position => (modal[index]).matched[position].carrier

def projections : List (Projection plan modal) :=
  (List.finRange modal.length).flatMap fun index =>
    [.source index, .target index, .focus index] ++
      ((List.finRange modal[index].rely.length).map (TermSymbol.rely index)) ++
      ((List.finRange modal[index].matched.length).map (TermSymbol.matched index))

theorem projection_member (projection : Projection plan modal) :
    projection ∈ projections plan modal := by
  cases projection with
  | source index => exact List.mem_flatMap.mpr ⟨index, List.mem_finRange index, by simp⟩
  | target index => exact List.mem_flatMap.mpr ⟨index, List.mem_finRange index, by simp⟩
  | focus index => exact List.mem_flatMap.mpr ⟨index, List.mem_finRange index, by simp⟩
  | rely index position => exact List.mem_flatMap.mpr ⟨index, List.mem_finRange index, by simp⟩
  | matched index position => exact List.mem_flatMap.mpr ⟨index, List.mem_finRange index, by simp⟩

def signature : Signature (symbols plan installed modal) where
  typeRank := (sumRanks (ranks installed.signature) (extraRanks plan modal)).typeRank
  termRank := (sumRanks (ranks installed.signature) (extraRanks plan modal)).termRank
  predicateRank := (sumRanks (ranks installed.signature) (extraRanks plan modal)).predicateRank
  typeParameters := fun symbol => match symbol with
    | .inl symbol => contextLeft (installed.signature.typeParameters symbol)
    | .inr (.input _) => .nil
    | .inr (.event index) => inputContext plan installed modal index
  termParameters := fun symbol => match symbol with
    | .inl symbol => contextLeft (installed.signature.termParameters symbol)
    | .inr projection => eventContext plan installed modal projection.index
  predicateParameters symbol := match symbol with
    | .inl symbol => nomatch symbol
    | .inr symbol => nomatch symbol
  termResult := fun symbol => match symbol with
    | .inl symbol => typeLeft (installed.signature.termResult symbol)
    | .inr projection => authoredType plan installed modal (projectionCarrier plan modal projection) 2
  typeParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (contextLeft_before (ranks installed.signature) (extraRanks plan modal) _ _).mpr
          (installed.signature.typeParameters_before symbol)
    | inr symbol =>
        cases symbol with
        | input => trivial
        | event index => exact ⟨True.intro, Nat.lt_succ_self 1, fun position => Fin.elim0 position⟩
  termParameters_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (contextLeft_before (ranks installed.signature) (extraRanks plan modal) _ _).mpr
          (installed.signature.termParameters_before symbol)
    | inr symbol =>
        exact
          ⟨⟨True.intro, (show 1 < 3 from by decide), fun position => Fin.elim0 position⟩,
            (show 2 < 3 from by decide), fun position => by
              cases position using Fin.cases with
              | zero => trivial
              | succ impossible => exact Fin.elim0 impossible⟩
  predicateParameters_before symbol := by
    cases symbol with
    | inl symbol => exact Empty.elim symbol
    | inr symbol => exact Empty.elim symbol
  termResult_before := by
    intro symbol
    cases symbol with
    | inl symbol =>
        exact (typeLeft_before (ranks installed.signature) (extraRanks plan modal) _ _).mpr
          (installed.signature.termResult_before symbol)
    | inr projection =>
        exact (typeLeft_before (ranks installed.signature) (extraRanks plan modal) _ _).mpr
          ((projectionCarrier plan modal projection).native_before 2 3 (by decide))

theorem preserves : SignatureExtension.Preserves installed.signature (signature plan installed modal) where
  typeParameters _ := rfl
  termParameters _ := rfl
  predicateParameters symbol := nomatch symbol
  termResult _ := rfl
  typeRank _ := rfl
  termRank _ := rfl
  predicateRank symbol := nomatch symbol

def constructorDerivation {judgment : Judgment installed.symbols}
    (tree : Derivation installed.signature judgment) :
    Derivation (signature plan installed modal) (judgmentLeft judgment) :=
  SignatureExtension.derivation installed.signature (signature plan installed modal)
    (preserves plan installed modal) tree

theorem constructorDerivation_before {judgment : Judgment installed.symbols}
    (tree : Derivation installed.signature judgment) (bound : Nat) (earlier : tree.before bound) :
    (constructorDerivation plan installed modal tree).before bound :=
  SignatureExtension.derivation_before _ _ _ tree bound earlier

end Mettapedia.OSLF.NativeTypes.Generation.NativeModalSignature
