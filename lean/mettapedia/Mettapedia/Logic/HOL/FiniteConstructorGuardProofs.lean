import Mettapedia.Logic.HOL.FiniteConstructorGuards
import Mettapedia.Logic.HOL.FiniteConstructorSubstitution
import Mettapedia.Logic.HOL.ProofSyntaxStructural

/-!
# Retained proofs for constructor-data guards

The argument binder is natural under typed substitution. Its beta program and
existential introduction use the actual emitted guard syntax and explicit
proof constructors. No conversion or datatype membership axiom is added.
-/

set_option autoImplicit false

namespace Mettapedia.Logic.HOL.FiniteConstructorEncoding

universe u v
variable {Base : Type u} {Const : Ty Base → Type v}
variable {Γ Δ Ξ : Ctx Base}

abbrev ArgumentBody (Const : Ty Base → Type v) (Γ : Ctx Base) (fields : List (Ty Base)) :=
  ∀ {Δ : Ctx Base}, Subst Const Γ Δ → Arguments Const Δ fields → Formula Const Δ

def NaturalBody {fields : List (Ty Base)} (body : ArgumentBody Const Γ fields) : Prop :=
  ∀ {Δ Ξ : Ctx Base} (earlier : Subst Const Γ Δ) (later : Subst Const Δ Ξ)
    (arguments : Arguments Const Δ fields),
    subst later (body earlier arguments) =
      body (fun index => subst later (earlier index)) (substituteArguments later fields arguments)

def bindHead {type : Ty Base} {fields : List (Ty Base)}
    (body : ArgumentBody Const Γ (type :: fields)) : ArgumentBody Const (type :: Γ) fields :=
  fun substitution arguments => body (fun index => substitution (.vs index)) (substitution .vz, arguments)

theorem bindHead_natural {type : Ty Base} {fields : List (Ty Base)}
    (body : ArgumentBody Const Γ (type :: fields)) (natural : NaturalBody body) :
    NaturalBody (bindHead body) := by
  intro Δ Ξ earlier later arguments
  exact natural (fun index => earlier (.vs index)) later (earlier .vz, arguments)

theorem abstractArguments_subst (substitution : Subst Const Γ Δ)
    (fields : List (Ty Base)) (body : ArgumentBody Const Γ fields) (natural : NaturalBody body) :
    subst substitution (abstractArguments fields body) =
      abstractArguments fields (fun later arguments =>
        body (fun index => subst later (substitution index)) arguments) := by
  induction fields generalizing Γ Δ with
  | nil =>
      have reduced := natural (fun index => .var index) substitution PUnit.unit
      apply reduced.trans
      change body substitution PUnit.unit =
        body (fun index => subst (fun index => .var index) (substitution index)) PUnit.unit
      apply congrArg (fun images : Subst Const Γ Δ => body images PUnit.unit)
      funext type index
      exact (subst_id (substitution index)).symm
  | cons type rest hypotheses =>
      change Term.lam (subst (Subst.lift substitution)
        (abstractArguments rest (bindHead body))) = _
      rw [hypotheses (Subst.lift substitution) (bindHead body) (bindHead_natural body natural)]
      apply congrArg Term.lam
      apply congrArg (abstractArguments rest)
      funext laterContext later arguments
      unfold bindHead
      change body (fun index => subst later (weaken (substitution index))) (later .vz, arguments) =
        body (fun index => subst (fun index => later (.vs index)) (substitution index))
          (later .vz, arguments)
      apply congrArg (fun images : Subst Const Γ laterContext => body images (later .vz, arguments))
      funext result index
      exact subst_rename later Rename.weaken (substitution index)

def supplyHead {type : Ty Base} {fields : List (Ty Base)}
    (body : ArgumentBody Const Γ (type :: fields)) (argument : Term Const Γ type) :
    ArgumentBody Const Γ fields :=
  fun substitution arguments => body substitution (subst substitution argument, arguments)

theorem supplyHead_natural {type : Ty Base} {fields : List (Ty Base)}
    (body : ArgumentBody Const Γ (type :: fields)) (natural : NaturalBody body)
    (argument : Term Const Γ type) : NaturalBody (supplyHead body argument) := by
  intro Δ Ξ earlier later arguments
  apply (natural earlier later (subst earlier argument, arguments)).trans
  exact congrArg (fun first => body (fun index => subst later (earlier index))
    (first, substituteArguments later fields arguments)) (subst_comp later earlier argument)

theorem abstractArguments_instantiate {type : Ty Base} {fields : List (Ty Base)}
    (body : ArgumentBody Const Γ (type :: fields)) (natural : NaturalBody body)
    (argument : Term Const Γ type) :
    instantiate argument (abstractArguments fields (bindHead body)) =
      abstractArguments fields (supplyHead body argument) := by
  rw [instantiate, abstractArguments_subst _ _ _ (bindHead_natural body natural)]
  rfl

def applyArguments_congr {assumptions : List (Formula Const Γ)}
    (fields : List (Ty Base)) (first second : Term Const Γ (handlerType fields))
    (arguments : Arguments Const Γ fields) (proof : ProofSyntax Const assumptions (.eq first second)) :
    ProofSyntax Const assumptions (.eq (applyArguments fields first arguments)
      (applyArguments fields second arguments)) := by
  induction fields with
  | nil => exact proof
  | cons type rest hypotheses =>
      exact hypotheses (.app first arguments.1) (.app second arguments.1)
        arguments.2 (.eqApp arguments.1 proof)

theorem applyArguments_congr_free {assumptions : List (Formula Const Γ)}
    (fields : List (Ty Base)) (first second : Term Const Γ (handlerType fields))
    (arguments : Arguments Const Γ fields) (proof : ProofSyntax Const assumptions (.eq first second))
    (free : proof.FunctionExtensionalityFree) :
    (applyArguments_congr fields first second arguments proof).FunctionExtensionalityFree := by
  induction fields with
  | nil => exact free
  | cons type rest hypotheses =>
      exact hypotheses (.app first arguments.1) (.app second arguments.1)
        arguments.2 (.eqApp arguments.1 proof) free

def abstractArguments_beta {assumptions : List (Formula Const Γ)}
    (fields : List (Ty Base)) (body : ArgumentBody Const Γ fields) (natural : NaturalBody body)
    (arguments : Arguments Const Γ fields) :
    ProofSyntax Const assumptions (.eq (applyArguments fields (abstractArguments fields body) arguments)
      (body (fun index => .var index) arguments)) := by
  induction fields with
  | nil => cases arguments; exact .eqRefl _
  | cons type rest hypotheses =>
      have first := applyArguments_congr (assumptions := assumptions) rest _ _ arguments.2
        (ProofSyntax.beta (Δ := assumptions) arguments.1 (abstractArguments rest (bindHead body)))
      have programs := abstractArguments_instantiate body natural arguments.1
      have first' := ProofSyntax.castIndices rfl
        (congrArg (fun target => Term.eq
          (applyArguments rest (.app (.lam (abstractArguments rest (bindHead body))) arguments.1) arguments.2)
          (applyArguments rest target arguments.2)) programs) first
      have remaining := hypotheses (supplyHead body arguments.1) (supplyHead_natural body natural arguments.1) arguments.2
      apply ProofSyntax.castIndices rfl ?_ (.eqTrans first' remaining)
      apply congrArg (Term.eq _)
      unfold supplyHead
      exact congrArg (fun first => body (fun index => .var index) (first, arguments.2)) (subst_id arguments.1)

set_option backward.isDefEq.respectTransparency false in
theorem abstractArguments_beta_free {assumptions : List (Formula Const Γ)}
    (fields : List (Ty Base)) (body : ArgumentBody Const Γ fields) (natural : NaturalBody body)
    (arguments : Arguments Const Γ fields) :
    (abstractArguments_beta (assumptions := assumptions) fields body natural arguments).FunctionExtensionalityFree := by
  induction fields with
  | nil => cases arguments; trivial
  | cons type rest hypotheses =>
      unfold abstractArguments_beta
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      constructor
      · apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
        exact applyArguments_congr_free rest _ _ arguments.2 _ True.intro
      · exact hypotheses _ (supplyHead_natural body natural arguments.1) arguments.2

theorem existsArguments_subst (substitution : Subst Const Γ Δ)
    (fields : List (Ty Base)) (predicate : Term Const Γ (handlerType fields)) :
    subst substitution (existsArguments fields predicate) =
      existsArguments fields (subst substitution predicate) := by
  induction fields generalizing Γ Δ with
  | nil => rfl
  | cons type rest hypotheses =>
      change Term.ex (subst (Subst.lift substitution)
        (existsArguments rest (.app (weaken predicate) (.var .vz)))) = _
      rw [hypotheses]
      apply congrArg Term.ex
      apply congrArg (existsArguments rest)
      exact congrArg (fun function => Term.app function (.var .vz)) (subst_weaken substitution predicate)

def existsArguments_intro {assumptions : List (Formula Const Γ)}
    (fields : List (Ty Base)) (predicate : Term Const Γ (handlerType fields))
    (arguments : Arguments Const Γ fields)
    (proof : ProofSyntax Const assumptions (applyArguments fields predicate arguments)) :
    ProofSyntax Const assumptions (existsArguments fields predicate) := by
  induction fields with
  | nil => exact proof
  | cons type rest hypotheses =>
      apply ProofSyntax.exI arguments.1
      have remaining := hypotheses (.app predicate arguments.1) arguments.2 proof
      apply ProofSyntax.castIndices rfl ?_ remaining
      simp only [instantiate, existsArguments_subst, subst, Subst.single]
      exact congrArg (fun function => existsArguments rest (.app function arguments.1))
        (instantiate_weaken arguments.1 predicate).symm

theorem existsArguments_intro_free {assumptions : List (Formula Const Γ)}
    (fields : List (Ty Base)) (predicate : Term Const Γ (handlerType fields))
    (arguments : Arguments Const Γ fields)
    (proof : ProofSyntax Const assumptions (applyArguments fields predicate arguments))
    (free : proof.FunctionExtensionalityFree) :
    (existsArguments_intro fields predicate arguments proof).FunctionExtensionalityFree := by
  induction fields with
  | nil => exact free
  | cons type rest hypotheses =>
      change (ProofSyntax.castIndices _ _ _).FunctionExtensionalityFree
      apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
      exact hypotheses (.app predicate arguments.1) arguments.2 proof free

theorem constructorBody_natural (signature : List (List (Ty Base)))
    (occurrence : Fin signature.length) (payload : Term Const Γ (payloadType signature)) :
    NaturalBody (fun substitution arguments =>
      Term.eq (subst substitution payload) (encode signature occurrence arguments)) := by
  intro Δ Ξ earlier later arguments
  change Term.eq (subst later (subst earlier payload)) (subst later (encode signature occurrence arguments)) = _
  rw [subst_comp, encode_subst]
  rfl

theorem constructorPredicate_subst (substitution : Subst Const Γ Δ)
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (payload : Term Const Γ (payloadType signature)) :
    subst substitution (constructorPredicate signature occurrence payload) =
      constructorPredicate signature occurrence (subst substitution payload) := by
  unfold constructorPredicate
  rw [abstractArguments_subst _ _ _ (constructorBody_natural signature occurrence payload)]
  apply congrArg (abstractArguments (signature.get occurrence))
  funext target later arguments
  exact congrArg (fun value => Term.eq value (encode signature occurrence arguments))
    (subst_comp later substitution payload).symm

theorem constructorGuard_subst (substitution : Subst Const Γ Δ)
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (payload : Term Const Γ (payloadType signature)) :
    subst substitution (constructorGuard signature occurrence payload) =
      constructorGuard signature occurrence (subst substitution payload) := by
  unfold constructorGuard
  rw [existsArguments_subst, constructorPredicate_subst]

theorem any_subst (substitution : Subst Const Γ Δ) (formulas : List (Formula Const Γ)) :
    subst substitution (any formulas) = any (formulas.map (subst substitution)) := by
  induction formulas with
  | nil => rfl
  | cons first rest hypotheses => exact congrArg (Term.or (subst substitution first)) hypotheses

theorem validGuard_subst (substitution : Subst Const Γ Δ)
    (signature : List (List (Ty Base))) (payload : Term Const Γ (payloadType signature)) :
    subst substitution (validGuard signature payload) =
      validGuard signature (subst substitution payload) := by
  unfold validGuard
  rw [any_subst, List.map_ofFn]
  apply congrArg any
  apply congrArg List.ofFn
  funext occurrence
  exact constructorGuard_subst substitution signature occurrence payload

def constructorPredicate_beta {assumptions : List (Formula Const Γ)}
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (payload : Term Const Γ (payloadType signature))
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    ProofSyntax Const assumptions
      (.eq (applyArguments (signature.get occurrence) (constructorPredicate signature occurrence payload) arguments)
        (.eq payload (encode signature occurrence arguments))) := by
  have beta := abstractArguments_beta (assumptions := assumptions) (signature.get occurrence)
    (fun substitution arguments => .eq (subst substitution payload) (encode signature occurrence arguments))
    (constructorBody_natural signature occurrence payload) arguments
  apply ProofSyntax.castIndices rfl ?_ beta
  exact congrArg (Term.eq _) (congrArg (fun value => Term.eq value (encode signature occurrence arguments))
    (subst_id payload))

set_option backward.isDefEq.respectTransparency false in
theorem constructorPredicate_beta_free {assumptions : List (Formula Const Γ)}
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (payload : Term Const Γ (payloadType signature))
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    (constructorPredicate_beta (assumptions := assumptions) signature occurrence payload arguments).FunctionExtensionalityFree := by
  unfold constructorPredicate_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact abstractArguments_beta_free _ _ _ _

def constructorGuard_intro {assumptions : List (Formula Const Γ)}
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    ProofSyntax Const assumptions (constructorGuard signature occurrence (encode signature occurrence arguments)) :=
  existsArguments_intro (signature.get occurrence)
    (constructorPredicate signature occurrence (encode signature occurrence arguments)) arguments
    (.impE (.eqPropER (constructorPredicate_beta signature occurrence (encode signature occurrence arguments) arguments))
      (.eqRefl (encode signature occurrence arguments)))

theorem constructorGuard_intro_free {assumptions : List (Formula Const Γ)}
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    (constructorGuard_intro (assumptions := assumptions) signature occurrence arguments).FunctionExtensionalityFree := by
  apply existsArguments_intro_free
  exact ⟨constructorPredicate_beta_free _ _ _ _, True.intro⟩

def any_introAt {assumptions : List (Formula Const Γ)} :
    (formulas : List (Formula Const Γ)) → (occurrence : Fin formulas.length) →
    ProofSyntax Const assumptions (formulas.get occurrence) → ProofSyntax Const assumptions (any formulas)
  | [], occurrence, _ => Fin.elim0 occurrence
  | _ :: _, ⟨0, _⟩, proof => .orIL proof
  | _ :: rest, ⟨n + 1, bound⟩, proof =>
      .orIR (any_introAt rest ⟨n, Nat.lt_of_succ_lt_succ bound⟩ proof)

theorem any_introAt_free {assumptions : List (Formula Const Γ)}
    (formulas : List (Formula Const Γ)) (occurrence : Fin formulas.length)
    (proof : ProofSyntax Const assumptions (formulas.get occurrence))
    (free : proof.FunctionExtensionalityFree) :
    (any_introAt formulas occurrence proof).FunctionExtensionalityFree := by
  induction formulas with
  | nil => exact Fin.elim0 occurrence
  | cons first rest hypotheses =>
      rcases occurrence with ⟨n, bound⟩
      cases n with
      | zero => exact free
      | succ n => exact hypotheses ⟨n, Nat.lt_of_succ_lt_succ bound⟩ proof free

def validGuard_intro {assumptions : List (Formula Const Γ)}
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    ProofSyntax Const assumptions (validGuard signature (encode signature occurrence arguments)) := by
  let formulas := List.ofFn (fun selected => constructorGuard signature selected (encode signature occurrence arguments))
  have bound : occurrence.val < formulas.length := by simpa only [formulas, List.length_ofFn] using occurrence.isLt
  apply any_introAt formulas ⟨occurrence.val, bound⟩
  apply ProofSyntax.castIndices rfl ?_ (constructorGuard_intro (assumptions := assumptions) signature occurrence arguments)
  simp only [formulas, List.get_eq_getElem, List.getElem_ofFn]

set_option backward.isDefEq.respectTransparency false in
theorem validGuard_intro_free {assumptions : List (Formula Const Γ)}
    (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const Γ (signature.get occurrence)) :
    (validGuard_intro (assumptions := assumptions) signature occurrence arguments).FunctionExtensionalityFree := by
  unfold validGuard_intro
  apply any_introAt_free
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  exact constructorGuard_intro_free _ _ _

def predicate (signature : List (List (Ty Base))) : ClosedTerm Const (payloadType signature ⇒ .prop) :=
  .lam (validGuard signature (.var .vz))

def predicate_beta (signature : List (List (Ty Base)))
    (payload : ClosedTerm Const (payloadType signature)) :
    ProofSyntax Const [] (.eq (.app (predicate signature) payload) (validGuard signature payload)) := by
  apply ProofSyntax.castIndices rfl ?_ (ProofSyntax.beta (Δ := []) payload (validGuard signature (.var .vz)))
  simp [predicate, instantiate, validGuard_subst, subst, Subst.single]

def predicate_intro (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const [] (signature.get occurrence)) :
    ProofSyntax Const [] (.app (predicate signature) (encode signature occurrence arguments)) :=
  .impE (.eqPropER (predicate_beta signature (encode signature occurrence arguments)))
    (validGuard_intro signature occurrence arguments)

set_option backward.isDefEq.respectTransparency false in
theorem predicate_intro_free (signature : List (List (Ty Base))) (occurrence : Fin signature.length)
    (arguments : Arguments Const [] (signature.get occurrence)) :
    (predicate_intro signature occurrence arguments).FunctionExtensionalityFree := by
  refine ⟨?_, validGuard_intro_free _ _ _⟩
  change (predicate_beta signature (encode signature occurrence arguments)).FunctionExtensionalityFree
  unfold predicate_beta
  apply (ProofSyntax.functionExtensionalityFree_castIndices _ _ _).mpr
  trivial

#print axioms abstractArguments_beta
#print axioms constructorGuard_intro
#print axioms constructorGuard_intro_free
#print axioms validGuard_intro
#print axioms validGuard_intro_free
#print axioms predicate_intro

end Mettapedia.Logic.HOL.FiniteConstructorEncoding
