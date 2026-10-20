import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveRuleSignature
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.FormationSensitiveJudgmentReplay
import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.StructuralConversionCode
import Mettapedia.Logic.DerivationGraph

/-!
# Finite checking of formation-sensitive dependent judgments

Proof-free local codes decode to the independently authored fourteen-rule
signature. Conversion uses finite structural conversion codes, not a conversion
oracle. The common tree, shared-graph and checked-judgment interfaces then
supply replay and logical LCF construction for precisely the original typing
judgment. Context formation is checked separately, because raw variable rules
do not require a formed telescope.

Executable use requires decidable local head/universe policies and an
executable declaration-root decoder. No universe profile is selected here.
The logical checked-judgment invariant does not implement a native capability.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
namespace FormationSensitiveChecking

open FormationSensitiveRuleSignature
open Mettapedia.Logic

variable {Head : Type}

inductive Code (RootCode : Nat → Type) : Judgment Head → Type where
  | headType {n : Nat} {Γ : Ctx Head n} {h u : Head} :
      Code RootCode (judgment Γ (.head h) (.head u))
  | var {n : Nat} {Γ : Ctx Head n} (i : Fin n) :
      Code RootCode (judgment Γ (.var i) (Ctx.lookup Γ i))
  | const {n : Nat} {Γ : Ctx Head n} {name : DeclName} {type : Tm Head 0} {u : Head} :
      Code RootCode (judgment Γ (.const name) (liftClosed type))
  | piForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
      {u v w : Head} : Code RootCode (judgment Γ (.pi A B) (.head w))
  | sigmaForm {n : Nat} {Γ : Ctx Head n} {A : Tm Head n} {B : Tm Head (n + 1)}
      {u v w : Head} : Code RootCode (judgment Γ (.sigma A B) (.head w))
  | lamIntro {n : Nat} {Γ : Ctx Head n} {A : Tm Head n}
      {body B : Tm Head (n + 1)} {u : Head} :
      Code RootCode (judgment Γ (.lam body) (.pi A B))
  | appElim {n : Nat} {Γ : Ctx Head n} {g a A : Tm Head n} {B : Tm Head (n + 1)} :
      Code RootCode (judgment Γ (.app g a) (inst0 a B))
  | pairIntro {n : Nat} {Γ : Ctx Head n} {a b A : Tm Head n}
      {B : Tm Head (n + 1)} {u : Head} :
      Code RootCode (judgment Γ (.pair a b) (.sigma A B))
  | fstElim {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)} :
      Code RootCode (judgment Γ (.fst p) A)
  | sndElim {n : Nat} {Γ : Ctx Head n} {p A : Tm Head n} {B : Tm Head (n + 1)} :
      Code RootCode (judgment Γ (.snd p) (inst0 (.fst p) B))
  | idForm {n : Nat} {Γ : Ctx Head n} {A a b : Tm Head n} {u : Head}
      : Code RootCode (judgment Γ (.id A a b) (.head u))
  | reflIntro {n : Nat} {Γ : Ctx Head n} {a A : Tm Head n} :
      Code RootCode (judgment Γ (.refl a) (.id A a a))
  | cumul {n : Nat} {Γ : Ctx Head n} {t : Tm Head n} {u v : Head} : Code RootCode (judgment Γ t (.head v))
  | convert {n : Nat} {Γ : Ctx Head n} {t A B : Tm Head n} {u : Head}
      (conversion : StructuralConversionCode.Code Head RootCode n) :
      Code RootCode (judgment Γ t B)


/-- The local relation is the original rule signature with its actual premise
positions listed in order. It does not define typing through the checker. -/
def rules (R : Rules Head) (premises : List (Judgment Head)) (conclusion : Judgment Head) :
    Prop := ∃ rule : Rule R conclusion, premises = List.ofFn (hypothesis rule)

variable {R : Rules Head}

/-- Rule-algebra interpretation connects common finite derivability to the
independently defined formation-sensitive typing relation. -/
theorem derives_sound {j : Judgment Head} (derived : Derives (rules R) j) :
    FormationSensitive.Typing R j.context j.subject j.type := by
  induction derived with
  | node premises conclusion rule children ih =>
      obtain ⟨rule, rfl⟩ := rule
      exact ((typingAlgebra R).conclude rule (fun i =>
        ⟨ih _ (List.mem_ofFn.mpr ⟨i, rfl⟩)⟩)).down

def derivabilityAlgebra (R : Rules Head) : JudgmentDerivation.Algebra (signature R) where
  Carrier j := PLift (Derives (rules R) j)
  conclude rule premises := ⟨.node (List.ofFn (hypothesis rule)) _ ⟨rule, rfl⟩ (by
    intro premise member
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp member
    exact (premises i).down)⟩

theorem tree_derives {j : Judgment Head} (tree : Tree R j) : Derives (rules R) j :=
  (JudgmentDerivation.interpret (derivabilityAlgebra R) tree).down

theorem typing_iff_derives (j : Judgment Head) :
    FormationSensitive.Typing R j.context j.subject j.type ↔ Derives (rules R) j := by
  constructor
  · intro typed
    obtain ⟨tree⟩ := FormationSensitiveRuleSignature.complete typed
    exact tree_derives tree
  · exact derives_sound

section Checking

variable [DecidableEq Head] [DecidableRel R.headTyping] [DecidablePred R.isUniverse]
    [∀ u v w, Decidable (R.join u v w)] [DecidableRel R.cumulative]
    [DecidableRel R.headEq]

/-- Decode local data by checking each independently specified side condition.
Typing premises are subsequently checked by the common replay algorithm. -/
def decode (decoder : StructuralConversionCode.RootDecoder R.computation)
    {j : Judgment Head} : Code decoder.Code j → Option (Rule R j)
  | @Code.headType _ _ n Γ h u =>
      if typed : R.headTyping h u then some (.headType typed) else none
  | .var i => some (.var i)
  | @Code.const _ _ n Γ name type u => if h : R.constantType name = some type then
      if hu : R.isUniverse u then some (.const h hu) else none else none
  | @Code.piForm _ _ n Γ A B u v w => if hu : R.isUniverse u then
      if hv : R.isUniverse v then if hw : R.join u v w then
        some (.piForm hu hv hw) else none else none else none
  | @Code.sigmaForm _ _ n Γ A B u v w => if hu : R.isUniverse u then
      if hv : R.isUniverse v then if hw : R.join u v w then
        some (.sigmaForm hu hv hw) else none else none else none
  | @Code.lamIntro _ _ n Γ A body B u =>
      if hu : R.isUniverse u then some (.lamIntro hu) else none
  | @Code.appElim _ _ n Γ g a A B => some (.appElim (A := A) (B := B))
  | @Code.pairIntro _ _ n Γ a b A B u =>
      if hu : R.isUniverse u then some (.pairIntro hu) else none
  | @Code.fstElim _ _ n Γ p A B => some (.fstElim (B := B))
  | @Code.sndElim _ _ n Γ p A B => some (.sndElim (A := A) (B := B))
  | @Code.idForm _ _ n Γ A a b u =>
      if hu : R.isUniverse u then some (.idForm hu) else none
  | .reflIntro => some .reflIntro
  | @Code.cumul _ _ n Γ t u v =>
      if h : R.cumulative u v then some (.cumul h) else none
  | @Code.convert _ _ n Γ t A B u code => if hu : R.isUniverse u then
      if h : code.check R.headEq decoder.decode A B = true then
        some (.convert hu (StructuralConversionCode.Code.check_sound decoder h))
      else none else none

theorem decode_complete (decoder : StructuralConversionCode.RootDecoder R.computation)
    {j : Judgment Head} (rule : Rule R j) :
    ∃ code, decode decoder code = some rule := by
  cases rule with
  | headType h => exact ⟨.headType, by simp [decode, h]⟩
  | var i => exact ⟨.var i, rfl⟩
  | @const n Γ name type u h hu =>
      exact ⟨.const (u := u), by simp [decode, h, hu]⟩
  | @piForm n Γ A B u v w hu hv hw =>
      exact ⟨.piForm (u := u) (v := v), by simp [decode, hu, hv, hw]⟩
  | @sigmaForm n Γ A B u v w hu hv hw =>
      exact ⟨.sigmaForm (u := u) (v := v), by simp [decode, hu, hv, hw]⟩
  | @lamIntro n Γ A body B u hu =>
      exact ⟨.lamIntro (u := u), by simp [decode, hu]⟩
  | @appElim n Γ g a A B => exact ⟨.appElim (A := A) (B := B), rfl⟩
  | @pairIntro n Γ a b A B u hu =>
      exact ⟨.pairIntro (u := u), by simp [decode, hu]⟩
  | @fstElim n Γ p A B => exact ⟨.fstElim (B := B), rfl⟩
  | @sndElim n Γ p A B => exact ⟨.sndElim (A := A) (B := B), rfl⟩
  | idForm hu => exact ⟨.idForm, by simp [decode, hu]⟩
  | reflIntro => exact ⟨.reflIntro, rfl⟩
  | @cumul n Γ t u v h => exact ⟨.cumul (u := u), by simp [decode, h]⟩
  | @convert n Γ t A B u hu converted =>
      obtain ⟨code, checked⟩ :=
        (StructuralConversionCode.Code.conversion_iff_checked decoder).mp converted
      exact ⟨.convert (A := A) (u := u) code, by simp [decode, hu, checked]⟩

/-- Exact finite witnesses for the common checking interfaces. Codes contain
no typing or conversion proofs. Only independently decidable side policies
and the finite conversion decoder participate in the computation. -/
def interface (decoder : StructuralConversionCode.RootDecoder R.computation) :
    RuleWitness (rules R) where
  W := (j : Judgment Head) × Code decoder.Code j
  isInstance witness premises conclusion :=
    match decode decoder witness.2 with
    | none => false
    | some rule => decide (conclusion = witness.1 ∧ premises = List.ofFn (hypothesis rule))
  sound := by
    intro ⟨j, code⟩ premises conclusion accepted
    simp only at accepted
    cases decoded : decode decoder code with
    | none => simp [decoded] at accepted
    | some rule =>
        simp only [decoded, decide_eq_true_eq] at accepted
        obtain ⟨rfl, same⟩ := accepted
        exact ⟨rule, same⟩
  complete := by
    rintro premises conclusion ⟨rule, rfl⟩
    obtain ⟨code, decoded⟩ := decode_complete decoder rule
    exact ⟨⟨conclusion, code⟩, by simp [decoded]⟩

theorem typing_iff_checked_tree (decoder : StructuralConversionCode.RootDecoder R.computation)
    (j : Judgment Head) :
    FormationSensitive.Typing R j.context j.subject j.type ↔
      ∃ certificate : Logic.Derivation (Judgment Head) (interface decoder).W,
        certificate.valid (interface decoder) = true ∧ certificate.concl = j := by
  rw [typing_iff_derives]
  exact ⟨Derives.exists_derivation (interface decoder), by
    rintro ⟨certificate, accepted, rfl⟩
    exact certificate.valid_sound (interface decoder) accepted⟩

theorem typing_iff_checked_graph (decoder : StructuralConversionCode.RootDecoder R.computation)
    (j : Judgment Head) :
    FormationSensitive.Typing R j.context j.subject j.type ↔
      ∃ (nodes : List (DerivationGraph.Node (Judgment Head) (interface decoder).W Unit))
        (cache : Array (Judgment Head)) (root : Nat),
        DerivationGraph.replay (interface decoder) nodes = some cache ∧ cache[root]? = some j :=
  (typing_iff_derives j).trans (DerivationGraph.derives_iff_checked_graph (interface decoder) () j)

/-- Logical LCF values and replayed evidence have the same native authority.
This does not reconstruct erased certificates at runtime. -/
theorem typing_iff_minted (decoder : StructuralConversionCode.RootDecoder R.computation)
    (j : Judgment Head) :
    FormationSensitive.Typing R j.context j.subject j.type ↔
      ∃ (nodes : List (DerivationGraph.Node (Judgment Head) (interface decoder).W Unit))
        (root : Nat),
        (DerivationGraph.CheckedJudgment.mint (interface decoder) nodes root).map
          DerivationGraph.CheckedJudgment.judgment = some j :=
  (typing_iff_derives j).trans
    (DerivationGraph.CheckedJudgment.exists_mint_iff (interface decoder) () j).symm

/-- Reuse the maintained telescope certificate and structural tree replay.
The common graph connection does not introduce a second context checker. -/
abbrev ContextCode (decoder : StructuralConversionCode.RootDecoder R.computation)
    {n : Nat} (_context : Ctx Head n) :=
  StructuralTypingReplay.ContextCode Head (StructuralConversionCode.Code Head decoder.Code) n

def conversionCheck (decoder : StructuralConversionCode.RootDecoder R.computation)
    {n : Nat} (code : StructuralConversionCode.Code Head decoder.Code n)
    (left right : Tm Head n) : Bool := code.check R.headEq decoder.decode left right

def ContextCode.check (decoder : StructuralConversionCode.RootDecoder R.computation)
    {n : Nat} {Γ : Ctx Head n} (code : ContextCode decoder Γ) : Bool :=
  StructuralTypingReplay.checkContext R (conversionCheck decoder) Γ code

theorem ContextCode.check_sound (decoder : StructuralConversionCode.RootDecoder R.computation)
    {n : Nat} {Γ : Ctx Head n} (code : ContextCode decoder Γ)
    (accepted : ContextCode.check decoder (Γ := Γ) code = true) :
    FormationSensitive.ContextFormation R Γ :=
  StructuralTypingReplay.checkContext_sound R (conversionCheck decoder)
    (fun checked => StructuralConversionCode.Code.check_sound decoder checked) code accepted

theorem ContextCode.complete (decoder : StructuralConversionCode.RootDecoder R.computation)
    {n : Nat} {Γ : Ctx Head n} (formed : FormationSensitive.ContextFormation R Γ) :
    ∃ code : ContextCode decoder Γ, ContextCode.check decoder (Γ := Γ) code = true :=
  StructuralTypingReplay.checkContext_complete R (conversionCheck decoder)
    (fun converted => (StructuralConversionCode.Code.conversion_iff_checked decoder).mp converted) formed

/-- The existing authored replay checker can publish the same logical LCF
value directly. The executable input remains its original finite tree. -/
def mintReplay (decoder : StructuralConversionCode.RootDecoder R.computation)
    (j : Judgment Head)
    (code : StructuralTypingReplay.Code Head
      (StructuralConversionCode.Code Head decoder.Code) j.arity) :
    Option (DerivationGraph.CheckedJudgment (rules R)) :=
  if accepted : StructuralTypingReplay.check R (conversionCheck decoder)
      j.context j.subject j.type code = true then
    some (DerivationGraph.CheckedJudgment.ofDerivation j ((typing_iff_derives j).mp
      (StructuralTypingReplay.check_sound R (conversionCheck decoder)
        (fun checked => StructuralConversionCode.Code.check_sound decoder checked) code accepted)))
  else none

theorem mintReplay_iff (decoder : StructuralConversionCode.RootDecoder R.computation)
    (j : Judgment Head)
    (code : StructuralTypingReplay.Code Head
      (StructuralConversionCode.Code Head decoder.Code) j.arity) :
    (mintReplay decoder j code).map DerivationGraph.CheckedJudgment.judgment = some j ↔
      StructuralTypingReplay.check R (conversionCheck decoder) j.context j.subject j.type code = true := by
  unfold mintReplay
  split <;> simp_all [DerivationGraph.CheckedJudgment.ofDerivation]

/-- A public formed request checks the telescope, all graph rows, the root
address and the requested conclusion. Metadata alone cannot authorize it. -/
def checkRequest (decoder : StructuralConversionCode.RootDecoder R.computation)
    (j : Judgment Head) (context : ContextCode decoder j.context)
    (nodes : List (DerivationGraph.Node (Judgment Head) (interface decoder).W Unit))
    (root : Nat) : Bool :=
  ContextCode.check decoder (Γ := j.context) context && decide
    ((DerivationGraph.CheckedJudgment.mint (interface decoder) nodes root).map
      DerivationGraph.CheckedJudgment.judgment = some j)

theorem checkRequest_sound (decoder : StructuralConversionCode.RootDecoder R.computation)
    (j : Judgment Head) (context : ContextCode decoder j.context)
    (nodes : List (DerivationGraph.Node (Judgment Head) (interface decoder).W Unit))
    (root : Nat) (accepted : checkRequest decoder j context nodes root = true) :
    FormationSensitive.Judgment R j.context j.subject j.type := by
  simp only [checkRequest, Bool.and_eq_true, decide_eq_true_eq] at accepted
  obtain ⟨cache, replayed, found⟩ :=
    (DerivationGraph.CheckedJudgment.mint_iff (interface decoder) nodes root j).mp accepted.2
  exact ⟨ContextCode.check_sound decoder context accepted.1,
    derives_sound (DerivationGraph.root_sound (interface decoder) replayed found)⟩

/-- Completeness is existence of finite evidence for the source judgment;
it is not termination of proof search or inference from an unannotated term. -/
theorem judgment_iff_checked (decoder : StructuralConversionCode.RootDecoder R.computation)
    (j : Judgment Head) :
    FormationSensitive.Judgment R j.context j.subject j.type ↔
      ∃ (context : ContextCode decoder j.context)
        (nodes : List (DerivationGraph.Node (Judgment Head) (interface decoder).W Unit))
        (root : Nat), checkRequest decoder j context nodes root = true := by
  constructor
  · intro derived
    obtain ⟨context, checkedContext⟩ := ContextCode.complete decoder derived.context
    obtain ⟨nodes, root, minted⟩ := (typing_iff_minted decoder j).mp derived.typing
    exact ⟨context, nodes, root, by simp [checkRequest, checkedContext, minted]⟩
  · rintro ⟨context, nodes, root, checked⟩
    exact checkRequest_sound decoder j context nodes root checked

/-- The original substitution theorem yields checkable evidence after an
admitted substitution. The target telescope remains an explicit obligation. -/
theorem checked_substitute (decoder : StructuralConversionCode.RootDecoder R.computation)
    {n m : Nat} {Γ : Ctx Head n} {Δ : Ctx Head m} {term type : Tm Head n}
    (context : ContextCode decoder Γ)
    (nodes : List (DerivationGraph.Node (Judgment Head) (interface decoder).W Unit))
    (root : Nat) (accepted : checkRequest decoder (judgment Γ term type) context nodes root = true)
    {substitution : Sub Head n m} (typed : FormationSensitive.CtxMor R Γ Δ substitution)
    (targetFormed : FormationSensitive.ContextFormation R Δ) :
    ∃ (targetContext : ContextCode decoder Δ)
      (targetNodes : List (DerivationGraph.Node (Judgment Head) (interface decoder).W Unit))
      (targetRoot : Nat),
      checkRequest decoder (judgment Δ (subst substitution term) (subst substitution type))
        targetContext targetNodes targetRoot = true :=
  (judgment_iff_checked decoder
    (judgment Δ (subst substitution term) (subst substitution type))).mp ⟨targetFormed,
    (checkRequest_sound decoder (judgment Γ term type) context nodes root accepted).typing.substitute typed⟩

/-- A request retains its finite evidence; logical theorem authority can be
published separately by the existing checked-judgment interface. -/
structure Request (decoder : StructuralConversionCode.RootDecoder R.computation)
    (claim : Judgment Head) where
  context : ContextCode decoder claim.context
  nodes : List (DerivationGraph.Node (Judgment Head) (interface decoder).W Unit)
  root : Nat

def Request.check (decoder : StructuralConversionCode.RootDecoder R.computation)
    {claim : Judgment Head} (request : Request decoder claim) : Bool :=
  checkRequest decoder claim request.context request.nodes request.root

theorem Request.sound (decoder : StructuralConversionCode.RootDecoder R.computation)
    {claim : Judgment Head} (request : Request decoder claim)
    (accepted : request.check decoder = true) :
    FormationSensitive.Judgment R claim.context claim.subject claim.type :=
  checkRequest_sound decoder claim request.context request.nodes request.root accepted

/-- Finite evidence for a simultaneous substitution. The target telescope is
checked once, including when the source has no variables. Each argument is
checked at the substituted type from its exact source-context lookup. -/
structure SubstitutionRequest (decoder : StructuralConversionCode.RootDecoder R.computation)
    {n m : Nat} (_source : Ctx Head n) (target : Ctx Head m)
    (_substitution : Sub Head n m) where
  context : ContextCode decoder target
  arguments : Fin n → StructuralTypingReplay.Code Head
    (StructuralConversionCode.Code Head decoder.Code) m

def SubstitutionRequest.check (decoder : StructuralConversionCode.RootDecoder R.computation)
    {n m : Nat} {source : Ctx Head n} {target : Ctx Head m}
    {substitution : Sub Head n m}
    (request : SubstitutionRequest decoder source target substitution) : Bool :=
  ContextCode.check decoder request.context &&
    (List.finRange n).all fun index =>
      StructuralTypingReplay.check R (conversionCheck decoder) target (substitution index)
        (subst substitution (Ctx.lookup source index)) (request.arguments index)

/-- A successful substitution request establishes actual context formation
and the maintained formation-sensitive context-morphism judgment. -/
theorem SubstitutionRequest.sound (decoder : StructuralConversionCode.RootDecoder R.computation)
    {n m : Nat} {source : Ctx Head n} {target : Ctx Head m}
    {substitution : Sub Head n m}
    (request : SubstitutionRequest decoder source target substitution)
    (accepted : request.check decoder = true) :
    FormationSensitive.ContextFormation R target ∧
      FormationSensitive.CtxMor R source target substitution := by
  simp only [SubstitutionRequest.check, Bool.and_eq_true, List.all_eq_true] at accepted
  refine ⟨ContextCode.check_sound decoder request.context accepted.1, ?_⟩
  intro index
  exact StructuralTypingReplay.check_sound R (conversionCheck decoder)
    (fun checked => StructuralConversionCode.Code.check_sound decoder checked)
    (request.arguments index) (accepted.2 index (by simp))

/-- Every admitted context morphism has finite checking evidence. This is
existence of certificates, not a substitution-inference algorithm. -/
theorem SubstitutionRequest.complete (decoder : StructuralConversionCode.RootDecoder R.computation)
    {n m : Nat} {source : Ctx Head n} {target : Ctx Head m}
    {substitution : Sub Head n m}
    (formed : FormationSensitive.ContextFormation R target)
    (typed : FormationSensitive.CtxMor R source target substitution) :
    ∃ request : SubstitutionRequest decoder source target substitution,
      request.check decoder = true := by
  classical
  obtain ⟨context, contextAccepted⟩ := ContextCode.complete decoder formed
  have each := fun index => StructuralTypingReplay.check_complete R (conversionCheck decoder)
    (fun converted => (StructuralConversionCode.Code.conversion_iff_checked decoder).mp converted)
    (typed index)
  choose arguments argumentsAccepted using each
  refine ⟨⟨context, arguments⟩, ?_⟩
  simp only [SubstitutionRequest.check, contextAccepted, Bool.true_and, List.all_eq_true]
  exact fun index _ => argumentsAccepted index

end Checking
end FormationSensitiveChecking
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation
