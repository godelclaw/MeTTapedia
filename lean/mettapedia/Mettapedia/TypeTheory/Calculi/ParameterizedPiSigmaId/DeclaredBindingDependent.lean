import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.PrivateIdentityContexts

/-!
# Dependent typing of scope-resolved declared bindings

The authored lambda, where and result forms have independent introduction
rules. Core payloads reuse the established Pi/Sigma/identity syntax and its
formation-sensitive judgment. Private references are resolved against the
actual named telescope. A where value is outside the introduced scope.

The translation sends where to abstraction/application and result to its
payload. Hygienic substitution allocates private binder identities in the
destination frame. It preserves the original occurrence tree; identity and
composition are exact at the translated term and do not assert equality of
fresh allocation receipts.
-/

set_option autoImplicit false

namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
namespace DeclaredBindingDependent

open Presentation PrivateIdentityContexts

variable {Head : Type}

inductive Source (Head : Type) : Nat → Type where
  | core {n : Nat} : Tm Head n → Source Head n
  | reference {n : Nat} : Name → Fin n → Source Head n
  | lambda {n : Nat} : Name → Source Head (n + 1) → Source Head n
  | whereBinding {n : Nat} : Name → Source Head n → Source Head (n + 1) → Source Head n
  | result {n : Nat} : Source Head n → Source Head n
  | app {n : Nat} : Source Head n → Source Head n → Source Head n

def translate : {n : Nat} → Source Head n → Tm Head n
  | _, .core term => term
  | _, .reference _ index => .var index
  | _, .lambda _ body => .lam (translate body)
  | _, .whereBinding _ value body => .app (.lam (translate body)) (translate value)
  | _, .result payload => translate payload
  | _, .app function argument => .app (translate function) (translate argument)

def referenceAt {n : Nat} (frame : Frame n) (name : Name) : Option (Source Head n) :=
  (resolve frame name.identity).map (Source.reference name)

def rekey (map : Nat → Nat) : {n : Nat} → Source Head n → Source Head n
  | _, .core term => .core term
  | _, .reference name index => .reference ⟨map name.identity, name.spelling⟩ index
  | _, .lambda name body => .lambda ⟨map name.identity, name.spelling⟩ (rekey map body)
  | _, .whereBinding name value body =>
      .whereBinding ⟨map name.identity, name.spelling⟩ (rekey map value) (rekey map body)
  | _, .result payload => .result (rekey map payload)
  | _, .app function argument => .app (rekey map function) (rekey map argument)

theorem translate_rekey (map : Nat → Nat) : ∀ {n : Nat} (source : Source Head n),
    translate (rekey map source) = translate source
  | _, .core _ => rfl
  | _, .reference _ _ => rfl
  | _, .lambda name body => by simp only [rekey, translate, translate_rekey]
  | _, .whereBinding name value body => by simp only [rekey, translate, translate_rekey]
  | _, .result payload => translate_rekey map payload
  | _, .app function argument => by simp only [rekey, translate, translate_rekey]

def refresh : {n : Nat} → Frame n → Source Head n → Source Head n
  | _, _, .core term => .core term
  | _, frame, .reference _ index => .reference (frame index) index
  | _, frame, .lambda name body =>
      let chosen := frame.freshName name.spelling
      .lambda chosen (refresh (frame.extend chosen) body)
  | _, frame, .whereBinding name value body =>
      let chosen := frame.freshName name.spelling
      .whereBinding chosen (refresh frame value) (refresh (frame.extend chosen) body)
  | _, frame, .result payload => .result (refresh frame payload)
  | _, frame, .app function argument => .app (refresh frame function) (refresh frame argument)

theorem translate_refresh : ∀ {n : Nat} (frame : Frame n) (source : Source Head n),
    translate (refresh frame source) = translate source
  | _, _, .core _ => rfl
  | _, _, .reference _ _ => rfl
  | _, frame, .lambda name body => by
      simp only [refresh, translate, translate_refresh]
  | _, frame, .whereBinding name value body => by
      simp only [refresh, translate, translate_refresh]
  | _, frame, .result payload => translate_refresh frame payload
  | _, frame, .app function argument => by
      simp only [refresh, translate, translate_refresh]

def substitute : {n m : Nat} → Sub Head n m → Source Head n → Source Head m
  | _, _, sigma, .core term => .core (subst sigma term)
  | _, _, sigma, .reference _ index => .core (sigma index)
  | _, _, sigma, .lambda name body => .lambda name (substitute (liftSub sigma) body)
  | _, _, sigma, .whereBinding name value body =>
      .whereBinding name (substitute sigma value) (substitute (liftSub sigma) body)
  | _, _, sigma, .result payload => .result (substitute sigma payload)
  | _, _, sigma, .app function argument =>
      .app (substitute sigma function) (substitute sigma argument)

theorem translate_substitute : ∀ {n m : Nat} (sigma : Sub Head n m) (source : Source Head n),
    translate (substitute sigma source) = subst sigma (translate source)
  | _, _, _, .core _ => rfl
  | _, _, _, .reference _ _ => rfl
  | _, _, sigma, .lambda name body => by
      simp only [substitute, translate, subst, translate_substitute]
  | _, _, sigma, .whereBinding name value body => by
      simp only [substitute, translate, subst, translate_substitute]
  | _, _, sigma, .result payload => translate_substitute sigma payload
  | _, _, sigma, .app function argument => by
      simp only [substitute, translate, subst, translate_substitute]

def substituteInto {n m : Nat} (destination : Frame m) (sigma : Sub Head n m)
    (source : Source Head n) : Source Head m := refresh destination (substitute sigma source)

theorem substitution_square {n m : Nat} (destination : Frame m) (sigma : Sub Head n m)
    (source : Source Head n) :
    translate (substituteInto destination sigma source) = subst sigma (translate source) := by
  rw [substituteInto, translate_refresh, translate_substitute]

theorem substitution_identity {n : Nat} (frame : Frame n) (source : Source Head n) :
    translate (substituteInto frame ids source) = translate source := by
  rw [substitution_square, subst_ids]

theorem substitution_composition {n m k : Nat} (middle : Frame m) (destination : Frame k)
    (first : Sub Head n m) (second : Sub Head m k) (source : Source Head n) :
    translate (substituteInto destination second (substituteInto middle first source)) =
      translate (substituteInto destination (subComp second first) source) := by
  rw [substitution_square, substitution_square, substitution_square, subst_subComp]

theorem substitution_lift {n m : Nat} (destination : Frame m) (name : Name)
    (sigma : Sub Head n m) (body : Source Head (n + 1)) :
    translate (substituteInto destination sigma (.lambda name body)) =
      .lam (subst (liftSub sigma) (translate body)) := by
  rw [substitution_square]
  rfl

theorem renaming_square {n m : Nat} (destination : Frame m) (rho : Ren n m)
    (source : Source Head n) :
    translate (substituteInto destination (renSub rho) source) = rename rho (translate source) := by
  rw [substitution_square, subst_renSub]

theorem where_beta (rules : Rules Head) {n : Nat} (name : Name)
    (value : Source Head n) (body : Source Head (n + 1)) :
    Step rules.headEq (translate (.whereBinding name value body))
      (inst0 (translate value) (translate body)) rules.computation :=
  .betaPi _ _

theorem unbound_reference_not_resolved {n : Nat} (frame : Frame n) (name : Name)
    (absent : ∀ index, (frame index).identity ≠ name.identity) :
    referenceAt (Head := Head) frame name = none := by
  rw [referenceAt, resolve_absent frame name.identity absent]
  rfl

def bindingOccurrences : {n : Nat} → Source Head n → List (List Nat)
  | _, .core _ | _, .reference _ _ => []
  | _, .lambda _ body => [] :: (bindingOccurrences body).map (1 :: ·)
  | _, .whereBinding _ value body => [] ::
      ((bindingOccurrences value).map (1 :: ·) ++ (bindingOccurrences body).map (2 :: ·))
  | _, .result payload => (bindingOccurrences payload).map (0 :: ·)
  | _, .app function argument =>
      (bindingOccurrences function).map (0 :: ·) ++ (bindingOccurrences argument).map (1 :: ·)

theorem bindingOccurrences_substitute : ∀ {n m : Nat} (sigma : Sub Head n m)
    (source : Source Head n), bindingOccurrences (substitute sigma source) = bindingOccurrences source
  | _, _, _, .core _ => rfl
  | _, _, _, .reference _ _ => rfl
  | _, _, sigma, .lambda name body => by
      simp only [substitute, bindingOccurrences, bindingOccurrences_substitute]
  | _, _, sigma, .whereBinding name value body => by
      simp only [substitute, bindingOccurrences, bindingOccurrences_substitute]
  | _, _, sigma, .result payload => by
      simp only [substitute, bindingOccurrences, bindingOccurrences_substitute]
  | _, _, sigma, .app function argument => by
      simp only [substitute, bindingOccurrences, bindingOccurrences_substitute]

theorem bindingOccurrences_refresh : ∀ {n : Nat} (frame : Frame n) (source : Source Head n),
    bindingOccurrences (refresh frame source) = bindingOccurrences source
  | _, _, .core _ => rfl
  | _, _, .reference _ _ => rfl
  | _, frame, .lambda name body => by
      simp only [refresh, bindingOccurrences, bindingOccurrences_refresh]
  | _, frame, .whereBinding name value body => by
      simp only [refresh, bindingOccurrences, bindingOccurrences_refresh]
  | _, frame, .result payload => by
      simp only [refresh, bindingOccurrences, bindingOccurrences_refresh]
  | _, frame, .app function argument => by
      simp only [refresh, bindingOccurrences, bindingOccurrences_refresh]

theorem substitution_retains_occurrences {n m : Nat} (destination : Frame m)
    (sigma : Sub Head n m) (source : Source Head n) :
    bindingOccurrences (substituteInto destination sigma source) = bindingOccurrences source := by
  rw [substituteInto, bindingOccurrences_refresh, bindingOccurrences_substitute]

/-- The source rules quantify over the actual named telescope. None has
translation acceptance as its premise. Core payloads are the existing calculus. -/
inductive Typing (rules : Rules Head) : {n : Nat} → Context Head n →
    Source Head n → Tm Head n → Prop where
  | core {n : Nat} {context : Context Head n} {term type : Tm Head n} :
      FormationSensitive.Typing rules context.erase term type →
      Typing rules context (.core term) type
  | reference {n : Nat} {context : Context Head n} {name : Name} (index : Fin n) :
      (context.frame index).identity = name.identity →
      Typing rules context (.reference name index) (Ctx.lookup context.erase index)
  | lambda {n : Nat} {context : Context Head n} {name : Name} {domain : Tm Head n}
      {body : Source Head (n + 1)} {family : Tm Head (n + 1)} {level : Head} :
      context.frame.Fresh name →
      FormationSensitive.Typing rules context.erase (.pi domain family) (.head level) →
      rules.isUniverse level → Typing rules (.snoc context name domain) body family →
      Typing rules context (.lambda name body) (.pi domain family)
  | whereBinding {n : Nat} {context : Context Head n} {name : Name} {domain : Tm Head n}
      {value : Source Head n} {body : Source Head (n + 1)} {family : Tm Head (n + 1)}
      {level : Head} :
      context.frame.Fresh name →
      FormationSensitive.Typing rules context.erase (.pi domain family) (.head level) →
      rules.isUniverse level → Typing rules context value domain →
      Typing rules (.snoc context name domain) body family →
      Typing rules context (.whereBinding name value body) (inst0 (translate value) family)
  | result {n : Nat} {context : Context Head n} {payload : Source Head n} {type : Tm Head n} :
      Typing rules context payload type → Typing rules context (.result payload) type
  | app {n : Nat} {context : Context Head n} {function argument : Source Head n}
      {domain : Tm Head n} {family : Tm Head (n + 1)} :
      Typing rules context function (.pi domain family) → Typing rules context argument domain →
      Typing rules context (.app function argument) (inst0 (translate argument) family)
  | conv {n : Nat} {context : Context Head n} {source : Source Head n}
      {first second : Tm Head n} {level : Head} :
      Typing rules context source first →
      FormationSensitive.Typing rules context.erase second (.head level) → rules.isUniverse level →
      Conv rules.headEq first second rules.computation → Typing rules context source second

theorem typing_preservation {rules : Rules Head} {n : Nat} {context : Context Head n}
    {source : Source Head n} {type : Tm Head n} (typed : Typing rules context source type) :
    FormationSensitive.Typing rules context.erase (translate source) type := by
  induction typed with
  | core typed => exact typed
  | reference index _ => exact .var index
  | lambda _ formed universeWitness _ ih => exact .lamIntro formed universeWitness ih
  | whereBinding _ formed universeWitness _ _ ihValue ihBody =>
      exact .appElim (.lamIntro formed universeWitness ihBody) ihValue
  | result _ ih => exact ih
  | app _ _ ihFunction ihArgument => exact .appElim ihFunction ihArgument
  | conv _ formed universeWitness equality ih => exact .conv ih formed universeWitness equality

theorem referenceAt_typed {rules : Rules Head} {n : Nat} (context : Context Head n)
    (name : Name) (index : Fin n) (found : resolve context.frame name.identity = some index) :
    referenceAt (Head := Head) context.frame name = some (.reference name index) ∧
      Typing rules context (.reference name index) (Ctx.lookup context.erase index) := by
  exact ⟨by rw [referenceAt, found]; rfl,
    .reference index (resolve_sound context.frame name.identity index found)⟩

theorem Typing.rekey {rules : Rules Head} {n : Nat} {context : Context Head n}
    {source : Source Head n} {type : Tm Head n} (typed : Typing rules context source type)
    (map : Nat → Nat) (injective : Function.Injective map) :
    Typing rules (context.rekey map) (rekey map source) type := by
  induction typed with
  | core typed => exact .core (by simpa only [Context.erase_rekey] using typed)
  | @reference n context name index matching =>
      have matching' : ((context.rekey map).frame index).identity = map name.identity := by
        rw [Context.frame_rekey]
        exact congrArg map matching
      simpa only [DeclaredBindingDependent.rekey, Context.erase_rekey] using
        (Typing.reference (rules := rules) (context := context.rekey map)
          (name := ⟨map name.identity, name.spelling⟩) index matching')
  | @lambda n context name domain body family level fresh formed universeWitness _ ih =>
      apply Typing.lambda
      · intro index same
        rw [Context.frame_rekey] at same
        exact fresh index (injective same)
      · simpa only [Context.erase_rekey] using formed
      · exact universeWitness
      · exact ih
  | @whereBinding n context name domain value body family level fresh formed universeWitness _ _ ihValue ihBody =>
      have fresh' : (context.rekey map).frame.Fresh ⟨map name.identity, name.spelling⟩ := by
        intro index same
        rw [Context.frame_rekey] at same
        exact fresh index (injective same)
      have formed' : FormationSensitive.Typing rules (context.rekey map).erase
          (.pi domain family) (.head level) := by simpa only [Context.erase_rekey] using formed
      simpa only [DeclaredBindingDependent.rekey, translate_rekey] using
        (Typing.whereBinding fresh' formed' universeWitness ihValue ihBody)
  | result _ ih => exact .result ih
  | app _ _ ihFunction ihArgument =>
      simpa only [DeclaredBindingDependent.rekey, translate_rekey] using (Typing.app ihFunction ihArgument)
  | conv _ formed universeWitness equality ih =>
      exact .conv ih (by simpa only [Context.erase_rekey] using formed) universeWitness equality

theorem Typing.reference_identity {rules : Rules Head} {n : Nat} {context : Context Head n}
    {source : Source Head n} {type : Tm Head n} (typed : Typing rules context source type) :
    ∀ {name : Name} {index : Fin n}, source = .reference name index →
      (context.frame index).identity = name.identity := by
  induction typed with
  | reference index matching => intro name other same; cases same; exact matching
  | conv _ _ _ _ ih => exact ih
  | _ => intro name index same; cases same

theorem wrong_identity_not_typed {rules : Rules Head} {n : Nat} {context : Context Head n}
    {name : Name} {index : Fin n} (different : (context.frame index).identity ≠ name.identity)
    (type : Tm Head n) : ¬ Typing rules context (.reference name index) type := by
  intro typed
  exact different (typed.reference_identity rfl)

theorem Typing.substitute {rules : Rules Head} {n : Nat} {context : Context Head n}
    {source : Source Head n} {type : Tm Head n} (typed : Typing rules context source type) :
    ∀ {m : Nat} (destination : Context Head m) (sigma : Sub Head n m),
      FormationSensitive.CtxMor rules context.erase destination.erase sigma →
      Typing rules destination (substituteInto destination.frame sigma source) (subst sigma type) := by
  induction typed with
  | core typed =>
      intro m destination sigma morphism
      exact .core (typed.substitute morphism)
  | reference index _ =>
      intro m destination sigma morphism
      exact .core (morphism index)
  | @lambda n context name domain body family level _ formed universeWitness _ ih =>
      intro m destination sigma morphism
      let chosen := destination.frame.freshName name.spelling
      apply Typing.lambda (destination.frame.freshName_fresh name.spelling)
        (formed.substitute morphism) universeWitness
      exact ih (.snoc destination chosen (subst sigma domain)) (liftSub sigma) (morphism.lift domain)
  | @whereBinding n context name domain value body family level _ formed universeWitness _ _ ihValue ihBody =>
      intro m destination sigma morphism
      let chosen := destination.frame.freshName name.spelling
      have valueTyped := ihValue destination sigma morphism
      have bodyTyped := ihBody (.snoc destination chosen (subst sigma domain))
        (liftSub sigma) (morphism.lift domain)
      have result := Typing.whereBinding (destination.frame.freshName_fresh name.spelling)
        (formed.substitute morphism) universeWitness valueTyped bodyTyped
      change Typing rules destination
        (.whereBinding chosen (substituteInto destination.frame sigma value)
          (substituteInto (destination.frame.extend chosen) (liftSub sigma) body))
        (subst sigma (inst0 (translate value) family))
      simpa only [substitution_square, subst_inst0, Context.frame] using result
  | result _ ih =>
      intro m destination sigma morphism
      exact .result (ih destination sigma morphism)
  | @app n context function argument domain family _ _ ihFunction ihArgument =>
      intro m destination sigma morphism
      have result := Typing.app (ihFunction destination sigma morphism)
        (ihArgument destination sigma morphism)
      change Typing rules destination
        (.app (substituteInto destination.frame sigma function)
          (substituteInto destination.frame sigma argument))
        (subst sigma (inst0 (translate argument) family))
      simpa only [substitution_square, subst_inst0] using result
  | conv _ formed universeWitness equality ih =>
      intro m destination sigma morphism
      exact .conv (ih destination sigma morphism) (formed.substitute morphism)
        universeWitness (equality.substitute sigma)

theorem formed_typing_preservation {rules : Rules Head} {n : Nat} {context : Context Head n}
    {source : Source Head n} {type : Tm Head n}
    (formed : WellFormed rules context) (typed : Typing rules context source type) :
    FormationSensitive.Judgment rules context.erase (translate source) type :=
  ⟨formed.erase, typing_preservation typed⟩

end DeclaredBindingDependent
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId
