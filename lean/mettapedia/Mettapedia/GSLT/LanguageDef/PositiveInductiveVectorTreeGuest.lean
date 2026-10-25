import Mettapedia.GSLT.LanguageDef.ModuleSource.IndexedPositiveVectorLowering
import Mettapedia.GSLT.LanguageDef.IndexedInductiveGuestDeclarations
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAll
import Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId.Declarations.FormationSensitiveNativeVectorAllResults
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionSearch

/-!
# A length-indexed VectorTree guest in the cumulative calculus

The accepted textual source has two constructors:

* `solved (answer : Answer)`;
* `branch (arity : Nat) (children : Vec VectorTree arity)`.

This module generates their object-language declaration types and a dependent
eliminator.  The branch method receives the exact
`NativeVectorAll.allType P arity children`.  Its iota target constructs that
evidence by a native Vec elimination whose pointwise witness recursively calls
the VectorTree eliminator.

The declaration and endpoint checkers are executable data here.  Their
proof-producing qualification and typed receipts live in the companion
controls module.
-/

open Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
open Mettapedia.TypeTheory.UniverseLevel

set_option autoImplicit false

namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest

open Presentation Presentation.Declaration
open Presentation.Declaration.ComputationAuthority
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies

abbrev level : LevelExpr Nat := NativeVectorAll.motiveLevel
abbrev baseRules : Rules Tower.Head := NativeVectorAll.rules
abbrev baseDecoder := NativeVectorAll.decoder

def answerName : DeclName := `Generated.VectorTree.Answer
def treeName : DeclName := `Generated.VectorTree
def solvedName : DeclName := `Generated.VectorTree.solved
def branchName : DeclName := `Generated.VectorTree.branch
def eliminateName : DeclName := `Generated.VectorTree.eliminate

def answerTm {n : Nat} : Tower.Tm n := .const answerName
def treeTm {n : Nat} : Tower.Tm n := .const treeName

def solvedApp {n : Nat} (answer : Tower.Tm n) : Tower.Tm n :=
  .app (.const solvedName) answer

def branchApp {n : Nat} (length children : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.const branchName) length) children

def eliminateApp {n : Nat}
    (motive solvedCase branchCase tree : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.const eliminateName) motive)
    solvedCase) branchCase) tree

def recursiveWitness {n : Nat}
    (motive solvedCase branchCase : Tower.Tm n) : Tower.Tm n :=
  .lam (eliminateApp (rename wk motive) (rename wk solvedCase)
    (rename wk branchCase) (.var 0))

def liftChildren {n : Nat}
    (motive solvedCase branchCase length children : Tower.Tm n) : Tower.Tm n :=
  NativeVectorAll.allEvidence treeTm motive
    (recursiveWitness motive solvedCase branchCase) length children

@[simp] theorem rename_weaken1 {n m : Nat} (rho : Ren n m)
    (term : Tower.Tm n) :
    rename (liftRen rho) (rename wk term) = rename wk (rename rho term) := by
  rw [rename_comp, rename_comp]
  apply rename_ext
  intro index
  rfl

@[simp] theorem subst_weaken1 {n m : Nat} (sigma : Sub Tower.Head n m)
    (term : Tower.Tm n) :
    subst (liftSub sigma) (rename wk term) = rename wk (subst sigma term) := by
  rw [subst_rename, rename_subst]
  apply subst_ext
  intro index
  rfl

@[simp] theorem rename_treeTm {n m : Nat} (rho : Ren n m) :
    rename rho (treeTm : Tower.Tm n) = (treeTm : Tower.Tm m) := rfl

@[simp] theorem subst_treeTm {n m : Nat} (sigma : Sub Tower.Head n m) :
    subst sigma (treeTm : Tower.Tm n) = (treeTm : Tower.Tm m) := rfl

@[simp] theorem rename_recursiveWitness {n m : Nat} (rho : Ren n m)
    (motive solvedCase branchCase : Tower.Tm n) :
    rename rho (recursiveWitness motive solvedCase branchCase) =
      recursiveWitness (rename rho motive) (rename rho solvedCase)
        (rename rho branchCase) := by
  unfold recursiveWitness eliminateApp
  simp only [Presentation.rename]
  rw [rename_weaken1, rename_weaken1, rename_weaken1]
  rfl

@[simp] theorem subst_recursiveWitness {n m : Nat}
    (sigma : Sub Tower.Head n m)
    (motive solvedCase branchCase : Tower.Tm n) :
    subst sigma (recursiveWitness motive solvedCase branchCase) =
      recursiveWitness (subst sigma motive) (subst sigma solvedCase)
        (subst sigma branchCase) := by
  simp [recursiveWitness, eliminateApp, Presentation.subst]

@[simp] theorem rename_liftChildren {n m : Nat} (rho : Ren n m)
    (motive solvedCase branchCase length children : Tower.Tm n) :
    rename rho (liftChildren motive solvedCase branchCase length children) =
      liftChildren (rename rho motive) (rename rho solvedCase)
        (rename rho branchCase) (rename rho length) (rename rho children) := by
  simp [liftChildren, treeTm, Presentation.rename]

@[simp] theorem subst_liftChildren {n m : Nat}
    (sigma : Sub Tower.Head n m)
    (motive solvedCase branchCase length children : Tower.Tm n) :
    subst sigma (liftChildren motive solvedCase branchCase length children) =
      liftChildren (subst sigma motive) (subst sigma solvedCase)
        (subst sigma branchCase) (subst sigma length) (subst sigma children) := by
  simp [liftChildren, treeTm, Presentation.subst]

/-! ## Generated declaration types -/

def answerType : Tower.Tm 0 := sortTm level
def familyType : Tower.Tm 0 := sortTm level

def solvedType : Tower.Tm 0 :=
  .pi answerTm treeTm

def branchType : Tower.Tm 0 :=
  .pi natTm (.pi (vecApp treeTm (.var 0)) treeTm)

def motiveType : Tower.Tm 0 :=
  .pi treeTm (sortTm level)

def solvedCaseType : Tower.Tm 1 :=
  .pi answerTm (.app (.var 1) (solvedApp (.var 0)))

def branchCaseType : Tower.Tm 2 :=
  .pi natTm
    (.pi (vecApp treeTm (.var 0))
      (.pi (NativeVectorAll.allType treeTm (.var 3) (.var 1) (.var 0))
        (.app (.var 4) (branchApp (.var 2) (.var 1)))))

def eliminateResultType : Tower.Tm 3 :=
  .pi treeTm (.app (.var 3) (.var 0))

def eliminateType : Tower.Tm 0 :=
  .pi motiveType
    (.pi solvedCaseType
      (.pi branchCaseType eliminateResultType))

def entries : List (DeclName × Entry Tower.Head) :=
  [(answerName, ⟨answerType, none⟩),
   (treeName, ⟨familyType, none⟩),
   (solvedName, ⟨solvedType, none⟩),
   (branchName, ⟨branchType, none⟩),
   (eliminateName, ⟨eliminateType, none⟩)]

/-! ## Exact connection to the accepted textual source -/

def shiftLengths
    {context : List ModuleSource.IndexedPositiveVectorLowering.DataSort} {n : Nat}
    (lengths : ModuleSource.IndexedPositiveVectorLowering.LengthExpr context → Tower.Tm n) :
    ModuleSource.IndexedPositiveVectorLowering.LengthExpr context → Tower.Tm (n + 1) :=
  fun expression => rename wk (lengths expression)

def bindPayloadLengths
    {context : List ModuleSource.IndexedPositiveVectorLowering.DataSort} {n : Nat}
    (lengths : ModuleSource.IndexedPositiveVectorLowering.LengthExpr context → Tower.Tm n) :
    ModuleSource.IndexedPositiveVectorLowering.LengthExpr (.payload :: context) →
      Tower.Tm (n + 1)
  | .there expression => rename wk (lengths expression)

def bindLengthLengths
    {context : List ModuleSource.IndexedPositiveVectorLowering.DataSort} {n : Nat}
    (lengths : ModuleSource.IndexedPositiveVectorLowering.LengthExpr context → Tower.Tm n) :
    ModuleSource.IndexedPositiveVectorLowering.LengthExpr (.length :: context) →
      Tower.Tm (n + 1)
  | .here => .var 0
  | .there expression => rename wk (lengths expression)

def sourceConstructorBody
    {context : List ModuleSource.IndexedPositiveVectorLowering.DataSort}
    {names : List String} {n : Nat}
    (lengths : ModuleSource.IndexedPositiveVectorLowering.LengthExpr context → Tower.Tm n) :
    ModuleSource.IndexedPositiveVectorLowering.Code context names →
      Option (Tower.Tm n)
  | .result => some treeTm
  | .data _ .payload _ rest =>
      (sourceConstructorBody (bindPayloadLengths lengths) rest).map
        (.pi answerTm)
  | .data _ .length _ rest =>
      (sourceConstructorBody (bindLengthLengths lengths) rest).map
        (.pi natTm)
  | .recursive _ rest =>
      (sourceConstructorBody (shiftLengths lengths) rest).map
        (.pi treeTm)
  | .vector _ length rest =>
      (sourceConstructorBody (shiftLengths lengths) rest).map
        (.pi (vecApp treeTm (lengths length)))

def emptyLengths {n : Nat} :
    ModuleSource.IndexedPositiveVectorLowering.LengthExpr [] → Tower.Tm n := by
  intro expression
  cases expression

def sourceConstructorEntry
    (constructor : ModuleSource.IndexedPositiveVectorLowering.ResolvedConstructor) :
    Option (DeclName × Entry Tower.Head) := do
  let body ← sourceConstructorBody emptyLengths
    constructor.body
  pure (.str treeName constructor.name, ⟨body, none⟩)

def sourceConstructorEntries : Option (List (DeclName × Entry Tower.Head)) :=
  ModuleSource.IndexedPositiveVectorLowering.Controls.family.constructors.mapM
    sourceConstructorEntry

theorem sourceConstructorEntries_eq :
    sourceConstructorEntries =
      some [(solvedName, ⟨solvedType, none⟩),
        (branchName, ⟨branchType, none⟩)] := by
  rfl

theorem textual_source_roundtrip :
    ModuleSource.IndexedPositiveVectorLowering.lowerModule
        ModuleSource.IndexedPositiveVectorLowering.Controls.textualModule =
      some ModuleSource.IndexedPositiveVectorLowering.Controls.resolvedModule :=
  ModuleSource.IndexedPositiveVectorLowering.Controls.module_roundtrip

/-! ## Declaration and endpoint checkers -/

local instance : DecidableRel baseRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred baseRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (baseRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel baseRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel baseRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

/-- Declaration-prefix checking adds a root-code summand for equations from
the prefix.  The generated declarations are opaque, so existing base
conversion certificates embed through the inherited summand. -/
def liftBaseStepCode : {n : Nat} →
    StructuralConversionCode.StepCode Tower.Head baseDecoder.Code n →
      StructuralConversionCode.StepCode Tower.Head
        (DeclarationConversionCode.RootCode baseDecoder.Code (fun _ => Empty)) n
  | _, .betaPi body argument => .betaPi body argument
  | _, .betaSigmaFst first second => .betaSigmaFst first second
  | _, .betaSigmaSnd first second => .betaSigmaSnd first second
  | _, .head left right => .head left right
  | _, .root code => .root (.inherited code)
  | _, .congPiDom code codomain => .congPiDom (liftBaseStepCode code) codomain
  | _, .congPiCod domain code => .congPiCod domain (liftBaseStepCode code)
  | _, .congSigmaDom code codomain => .congSigmaDom (liftBaseStepCode code) codomain
  | _, .congSigmaCod domain code => .congSigmaCod domain (liftBaseStepCode code)
  | _, .congIdTy code left right => .congIdTy (liftBaseStepCode code) left right
  | _, .congIdLeft type code right => .congIdLeft type (liftBaseStepCode code) right
  | _, .congIdRight type left code => .congIdRight type left (liftBaseStepCode code)
  | _, .congLam code => .congLam (liftBaseStepCode code)
  | _, .congAppFun code argument => .congAppFun (liftBaseStepCode code) argument
  | _, .congAppArg function code => .congAppArg function (liftBaseStepCode code)
  | _, .congPairFst code second => .congPairFst (liftBaseStepCode code) second
  | _, .congPairSnd first code => .congPairSnd first (liftBaseStepCode code)
  | _, .congFst code => .congFst (liftBaseStepCode code)
  | _, .congSnd code => .congSnd (liftBaseStepCode code)
  | _, .congRefl code => .congRefl (liftBaseStepCode code)

def liftBaseConversionCode : {n : Nat} →
    StructuralConversionCode.Code Tower.Head baseDecoder.Code n →
      StructuralConversionCode.Code Tower.Head
        (DeclarationConversionCode.RootCode baseDecoder.Code (fun _ => Empty)) n
  | _, .single step => .single (liftBaseStepCode step)
  | _, .refl term => .refl term
  | _, .symm code => .symm (liftBaseConversionCode code)
  | _, .trans first second =>
      .trans (liftBaseConversionCode first) (liftBaseConversionCode second)

def declarationChoices :
    IndexedInductive.Guest.Declarations.Choices baseRules baseDecoder where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (baseRules.cumulative first second)
  normalize := NativeVectorAll.choices.normalize
  conversion := fun fuel left right =>
    (NativeVectorAll.choices.conversion fuel left right).map
      liftBaseConversionCode

def inventoryCertificates :=
  IndexedInductive.Guest.Declarations.elaborate baseRules baseDecoder
    declarationChoices 256 [] entries

def inventoryAccepted : Bool := inventoryCertificates.isSome

def inventorySignature : Signature Tower.Head := Signature.ofList entries
abbrev inventoryRules : Rules Tower.Head := extendRules baseRules inventorySignature
def inventoryDecoder := DeclarationConversionCode.ofList baseRules baseDecoder entries

local instance : DecidableRel inventoryRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (baseRules.headTyping h u))
local instance : DecidablePred inventoryRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (baseRules.isUniverse h))
local instance : ∀ u v w, Decidable (inventoryRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (baseRules.join u v w))
local instance : DecidableRel inventoryRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (baseRules.cumulative u v))
local instance : DecidableRel inventoryRules.headEq :=
  fun h u => inferInstanceAs (Decidable (baseRules.headEq h u))

def inventorySearchRoot {n : Nat}
    (term : Tower.Tm n) : Option (inventoryDecoder.Code n) :=
  (NativeVectorAll.searchRoot term).map .inherited

def inventoryChoices : FormationSensitiveElaboration.Choices Tower.Head
    inventoryDecoder.Code where
  headType head := some (StructuralTypingReplay.TowerDecisions.headTarget head)
  join first second := match first, second with
    | .sort first, .sort second => some (.sort (.max first second))
    | _, _ => none
  cumulative first second := decide (inventoryRules.cumulative first second)
  normalize := fun fuel term =>
    match StructuralConversionSearch.normalize inventoryDecoder inventorySearchRoot
        (headEq := inventoryRules.headEq) fuel term with
    | none => term
    | some candidate => candidate.term
  conversion := fun fuel left right =>
    StructuralConversionSearch.compare inventoryDecoder inventorySearchRoot
      (headEq := inventoryRules.headEq) fuel left right

def endpointAccepted {n : Nat} (context : Tower.Ctx n)
    (term type : Tower.Tm n) : Bool :=
  (FormationSensitiveElaboration.elaborate inventoryRules inventoryDecoder
    inventoryChoices 256 context term type).isSome

theorem endpointAccepted_sound {n : Nat} {context : Tower.Ctx n}
    {term type : Tower.Tm n} (checked : endpointAccepted context term type = true) :
    FormationSensitive.Judgment inventoryRules context term type := by
  obtain ⟨submission, produced⟩ := Option.isSome_iff_exists.mp checked
  exact FormationSensitiveElaboration.elaborate_sound inventoryRules
    inventoryDecoder inventoryChoices 256 context term type submission produced

/-! ## Iota endpoints and retained evidence -/

def contextP : Tower.Ctx 1 := .snoc .nil motiveType
def contextPZ : Tower.Ctx 2 := .snoc contextP solvedCaseType
def contextPZB : Tower.Ctx 3 := .snoc contextPZ branchCaseType
def solvedContext : Tower.Ctx 4 := .snoc contextPZB answerTm
def branchContextN : Tower.Ctx 4 := .snoc contextPZB natTm
def branchContext : Tower.Ctx 5 :=
  .snoc branchContextN (vecApp treeTm (.var 0))

def solvedLeft : Tower.Tm 4 :=
  eliminateApp (.var 3) (.var 2) (.var 1) (solvedApp (.var 0))
def solvedRight : Tower.Tm 4 := .app (.var 2) (.var 0)
def solvedIotaType : Tower.Tm 4 :=
  .app (.var 3) (solvedApp (.var 0))

def branchBundle : Tower.Tm 5 :=
  liftChildren (.var 4) (.var 3) (.var 2) (.var 1) (.var 0)

def branchBundleType : Tower.Tm 5 :=
  NativeVectorAll.allType treeTm (.var 4) (.var 1) (.var 0)

def branchLeft : Tower.Tm 5 :=
  eliminateApp (.var 4) (.var 3) (.var 2)
    (branchApp (.var 1) (.var 0))
def branchRight : Tower.Tm 5 :=
  .app (.app (.app (.var 2) (.var 1)) (.var 0)) branchBundle
def branchIotaType : Tower.Tm 5 :=
  .app (.var 4) (branchApp (.var 1) (.var 0))

inductive IotaEvidence (n : Nat) : Tower.Tm n → Tower.Tm n → Type where
  | solved (motive solvedCase branchCase answer : Tower.Tm n) :
      IotaEvidence n
        (eliminateApp motive solvedCase branchCase (solvedApp answer))
        (.app solvedCase answer)
  | branch (motive solvedCase branchCase length children : Tower.Tm n) :
      IotaEvidence n
        (eliminateApp motive solvedCase branchCase (branchApp length children))
        (.app (.app (.app branchCase length) children)
          (liftChildren motive solvedCase branchCase length children))

def IotaEvidence.rename {n m : Nat} {left right : Tower.Tm n}
    (evidence : IotaEvidence n left right) (rho : Ren n m) :
    IotaEvidence m (rename rho left) (rename rho right) := by
  cases evidence with
  | solved => exact .solved _ _ _ _
  | branch motive solvedCase branchCase length children =>
      simpa [eliminateApp, branchApp, Presentation.rename] using
        (IotaEvidence.branch
          (Presentation.rename rho motive)
          (Presentation.rename rho solvedCase)
          (Presentation.rename rho branchCase)
          (Presentation.rename rho length)
          (Presentation.rename rho children))

def IotaEvidence.substitute {n m : Nat} {left right : Tower.Tm n}
    (evidence : IotaEvidence n left right) (sigma : Sub Tower.Head n m) :
    IotaEvidence m (subst sigma left) (subst sigma right) := by
  cases evidence with
  | solved => exact .solved _ _ _ _
  | branch motive solvedCase branchCase length children =>
      simpa [eliminateApp, branchApp, Presentation.subst] using
        (IotaEvidence.branch
          (Presentation.subst sigma motive)
          (Presentation.subst sigma solvedCase)
          (Presentation.subst sigma branchCase)
          (Presentation.subst sigma length)
          (Presentation.subst sigma children))

def iotaComputation : ProofRelevantRootComputation Tower.Head where
  Evidence := IotaEvidence _
  rename := by
    intro n m rho left right evidence
    exact evidence.rename rho
  substitute := by
    intro n m sigma left right evidence
    exact evidence.substitute sigma

def signature : Signature Tower.Head :=
  { inventorySignature with computation := iotaComputation.support }

abbrev rules : Rules Tower.Head := extendRules baseRules signature

theorem inventory_extends_signature : inventorySignature.Extends signature where
  entries := fun selected => selected
  computation := by
    intro n left right impossible
    change (Signature.ofList entries).computation.step left right at impossible
    rw [Signature.computation_ofList] at impossible
    exact impossible.elim

theorem liftJudgment {n : Nat} {context : Tower.Ctx n}
    {term type : Tower.Tm n}
    (judgment : FormationSensitive.Judgment inventoryRules context term type) :
    FormationSensitive.Judgment rules context term type := by
  simpa only [Ctx.mapHead_id, Tm.mapHead_id] using
    judgment.mapHead (extensionMorphism baseRules inventory_extends_signature)

#print axioms sourceConstructorEntries_eq
#print axioms textual_source_roundtrip
#print axioms rename_liftChildren
#print axioms subst_liftChildren
#print axioms endpointAccepted_sound
#print axioms IotaEvidence.rename
#print axioms IotaEvidence.substitute

end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest

/-!
## Constant-motive folds through a checked result definition

The full dependent bundle remains an argument of the Tree eliminator. The
branch adapter calls an ordinary transparent definition of the existing Vector
result program. Its name, actual type and actual body are explicit data;
formation and source receipt transport are qualified downstream.
-/
namespace Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest
namespace ResultFold
open Presentation Presentation.Declaration
open Mettapedia.TypeTheory.Calculi.CumulativePiSigmaId
open NativeNaturalVectorFamilies

def projectionName : DeclName := `Generated.VectorTree.results

def library : List (DeclName × Entry Tower.Head) :=
  PositiveInductiveVectorTreeGuest.entries ++
    [(projectionName, ⟨NativeVectorAll.ResultView.programType, some NativeVectorAll.ResultView.program⟩)]

def checkingSignature : Signature Tower.Head := Signature.ofList library
abbrev checkingRules := extendRules baseRules checkingSignature
def checkingDecoder := DeclarationConversionCode.ofList baseRules baseDecoder library

def projection {n : Nat} (result arity children bundle : Tower.Tm n) : Tower.Tm n :=
  .app (.app (.app (.app (.app (.const projectionName) treeTm) result) arity) children) bundle

def weaken3 {n : Nat} (term : Tower.Tm n) : Tower.Tm (n + 3) :=
  rename wk (NativeVectorAll.weaken2 term)

def solvedMethod {n : Nat} (leaf : Tower.Tm n) : Tower.Tm n :=
  .lam (.app (rename wk leaf) (.var 0))

def branchMethod {n : Nat} (result node : Tower.Tm n) : Tower.Tm n :=
  .lam (.lam (.lam (.app (.app (.app (weaken3 node) (.var 2)) (.var 1))
    (projection (weaken3 result) (.var 2) (.var 1) (.var 0)))))

def fold {n : Nat} (result leaf node input : Tower.Tm n) : Tower.Tm n :=
  eliminateApp (NativeVectorAll.ResultView.predicate result) (solvedMethod leaf)
    (branchMethod result node) input

def childrenBundle {n : Nat} (result leaf node length children : Tower.Tm n) : Tower.Tm n :=
  liftChildren (NativeVectorAll.ResultView.predicate result) (solvedMethod leaf)
    (branchMethod result node) length children

def childrenResults {n : Nat} (result leaf node length children : Tower.Tm n) : Tower.Tm n :=
  projection result length children
    (childrenBundle result leaf node length children)

def leafType {n : Nat} (result : Tower.Tm n) : Tower.Tm n :=
  .pi answerTm (rename wk result)

def nodeType {n : Nat} (result : Tower.Tm n) : Tower.Tm n :=
  .pi natTm (.pi (vecApp treeTm (.var 0))
    (.pi (vecApp (NativeVectorAll.weaken2 result) (.var 1)) (weaken3 result)))

def foldType : Tower.Tm 0 :=
  .pi (sortTm level) (.pi (leafType (.var 0))
    (.pi (nodeType (.var 1)) (.pi treeTm (.var 3))))

def foldTerm : Tower.Tm 0 :=
  .lam (.lam (.lam (.lam (fold (.var 3) (.var 2) (.var 1) (.var 0)))))

def contextR : Tower.Ctx 1 := .snoc .nil (sortTm level)
def contextRS : Tower.Ctx 2 := .snoc contextR (leafType (.var 0))
def contextRSB : Tower.Ctx 3 := .snoc contextRS (nodeType (.var 1))
def contextRSBN : Tower.Ctx 4 := .snoc contextRSB natTm
def context : Tower.Ctx 5 := .snoc contextRSBN (vecApp treeTm (.var 0))

def assignment : Sub Tower.Head 5 5 :=
  consSub (.var 0) (consSub (.var 1)
    (consSub (branchMethod (.var 4) (.var 2))
      (consSub (solvedMethod (.var 3))
        (consSub (NativeVectorAll.ResultView.predicate (.var 4)) Fin.elim0))))

local instance : DecidableRel checkingRules.headTyping :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headTyping h u))
local instance : DecidablePred checkingRules.isUniverse :=
  fun h => inferInstanceAs (Decidable (Tower.rules.isUniverse h))
local instance : ∀ u v w, Decidable (checkingRules.join u v w) :=
  fun u v w => inferInstanceAs (Decidable (Tower.rules.join u v w))
local instance : DecidableRel checkingRules.cumulative :=
  fun u v => inferInstanceAs (Decidable (Tower.rules.cumulative u v))
local instance : DecidableRel checkingRules.headEq :=
  fun h u => inferInstanceAs (Decidable (Tower.rules.headEq h u))

@[noinline] def accepted {n : Nat} (ambient : Tower.Ctx n) (term type : Tower.Tm n) : Bool :=
  (FormationSensitiveElaboration.elaborate checkingRules checkingDecoder declarationChoices
    256 ambient term type).isSome

def slotChecked (index : Fin 5) : Bool :=
  accepted context (assignment index) (subst assignment (Ctx.lookup branchContext index))

def wrongBranchMethod : Tower.Tm 5 :=
  .lam (.lam (.lam (.app (.app (.app (weaken3 (.var 2)) (.var 2)) (.var 1)) (.var 1))))


def executionSignature : Signature Tower.Head :=
  { checkingSignature with computation := PositiveInductiveVectorTreeGuest.iotaComputation.support }

abbrev rules := extendRules baseRules executionSignature

end ResultFold
end Mettapedia.GSLT.LanguageDef.PositiveInductiveVectorTreeGuest
