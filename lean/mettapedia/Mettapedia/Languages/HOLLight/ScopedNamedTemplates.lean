import Mettapedia.Languages.HOLLight.TemplateInstantiationMachine

/-!
# Named templates for changing scoped rule bodies

A fixed authored de Bruijn body compiles once around an independently encoded
finite vector of closed data arguments. The original ordered instantiation and
named representative remain authoritative, including binder names, escaping
indices and repeated operands. Dynamic argument bytes do not enter finite control.
-/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Mettapedia.Languages.HOLLight.ScopedNamedTemplates
open Mettapedia.Languages.OpenTheory
open Mettapedia.Languages.OpenTheory.SyntaxEncoding
open Mettapedia.OSLF.Binding.WireCodec
open Mettapedia.OSLF.Binding.WireCodec.Binary
open Mettapedia.Computability.WordTemplateMachine
open PrimitiveTransport

/-- Closed data leaves the original fresh-name input unchanged. -/
theorem freeNames_sequence (arguments : List CanonicalTerm)
    (empty : ∀ argument ∈ arguments, freeNames argument.term = [])
    (depth : Nat) (body : DBTerm) :
    freeNames (TemplateInstantiationMachine.Indexed.sequence arguments depth body) = freeNames body := by
  induction arguments generalizing depth with
  | nil => rfl
  | cons argument rest ih =>
      rw [TemplateInstantiationMachine.Indexed.sequence,
        TemplateInstantiationMachine.Named.freeNames_instantiateAt argument.term (empty argument (by simp)),
        ih (fun value member => empty value (by simp [member]))]

/-- Holes are the original formal interval; every other bound index retains
its actual named-context lookup, including refusal if unavailable. -/
def compile (arity depth : Nat) : DBTerm → List SourceVar → Option (Indexed.Template Alphabet arity)
  | .const symbol annotation, _ => some (Templates.literal (putSourceTerm (.const symbol annotation)))
  | .free value, _ => some (Templates.literal (putSourceTerm (.var value.name value.ty)))
  | .bound index, binders =>
      if inside : depth ≤ index ∧ index < depth + arity then some [.inr ⟨index-depth, by omega⟩]
      else do
        let binder ← binders[index]?
        pure (Templates.literal (putSourceTerm (.var binder.name binder.ty)))
  | .app function argument, binders => do
      let first ← compile arity depth function binders
      let second ← compile arity depth argument binders
      pure (Templates.sourceApplication first second)
  | .abs domain body, binders => do
      let name := ReverseTranslation.freshName (binders.map Var.name ++ freeNames body)
      let bodyTemplate ← compile arity (depth+1) body (⟨name,domain⟩::binders)
      pure (Templates.sourceAbstraction name domain bodyTemplate)
termination_by term => sizeOf term

/-- Every field is an original complete source-term codec image. -/
def sourceWords (arguments : List CanonicalTerm) (sources : Fin arguments.length → SourceTerm) :
    Fin arguments.length → List Alphabet := fun index => encodeWith sourceTermCodec (sources index)

/-- Compile once, retaining exactly the original named substitution result. -/
theorem compile_exact (arguments : List CanonicalTerm) (sources : Fin arguments.length → SourceTerm)
    (empty : ∀ argument ∈ arguments, freeNames argument.term = [])
    (independent : ∀ index binders, named? (arguments[index]).term binders = some (sources index))
    (depth : Nat) (body : DBTerm) (binders : List SourceVar) :
    (compile arguments.length depth body binders).map
      (fun template => Indexed.instantiate template (sourceWords arguments sources)) =
    (named? (TemplateInstantiationMachine.Indexed.sequence arguments depth body) binders).map
      (encodeWith sourceTermCodec) := by
  induction body generalizing depth binders with
  | const symbol annotation =>
      simp [compile, TemplateInstantiationMachine.Indexed.sequence_const, named?, encodeWith, sourceTermCodec]
  | free binder =>
      simp [compile, TemplateInstantiationMachine.Indexed.sequence_free, named?, encodeWith, sourceTermCodec]
  | bound index =>
      rw [TemplateInstantiationMachine.Indexed.sequence_bound]
      by_cases inside : depth ≤ index ∧ index < depth+arguments.length
      · simp [compile, inside, sourceWords]
        refine ⟨sources ⟨index-depth,by omega⟩, ?_, rfl⟩
        exact independent ⟨index-depth,by omega⟩ binders
      · simp only [compile, dif_neg inside, named?]
        cases binders[index]? <;> simp [Templates.literal_exact, encodeWith, sourceTermCodec]
  | app function argument first second =>
      have firstExact := first depth binders
      have secondExact := second depth binders
      rw [TemplateInstantiationMachine.Indexed.sequence_app]
      cases firstCompiled : compile arguments.length depth function binders <;>
        cases firstNamed : named? (TemplateInstantiationMachine.Indexed.sequence arguments depth function) binders <;>
        cases secondCompiled : compile arguments.length depth argument binders <;>
        cases secondNamed : named? (TemplateInstantiationMachine.Indexed.sequence arguments depth argument) binders
      all_goals simp only [firstCompiled,firstNamed,secondCompiled,secondNamed,Option.map_none,Option.map_some,
        Option.some.injEq] at firstExact secondExact
      all_goals try contradiction
      all_goals simp [compile,named?,firstCompiled,firstNamed,secondCompiled,secondNamed,
        Templates.sourceApplication,Templates.pair_exact,Templates.literal_exact,firstExact,secondExact,
        encodeWith,sourceTermCodec,putSourceTerm,encodeData_pair]
  | abs domain body ih =>
      have names := freeNames_sequence arguments empty (depth+1) body
      let name := ReverseTranslation.freshName (binders.map Var.name ++ freeNames body)
      have bodyExact := ih (depth+1) (⟨name,domain⟩::binders)
      rw [TemplateInstantiationMachine.Indexed.sequence_abs]
      cases bodyCompiled : compile arguments.length (depth+1) body (⟨name,domain⟩::binders) <;>
        cases bodyNamed : named? (TemplateInstantiationMachine.Indexed.sequence arguments (depth+1) body) (⟨name,domain⟩::binders)
      all_goals simp only [bodyCompiled,bodyNamed,Option.map_none,Option.map_some,Option.some.injEq] at bodyExact
      all_goals dsimp only [name] at bodyCompiled bodyNamed bodyExact
      all_goals try contradiction
      all_goals simp [compile,named?,names,bodyCompiled,bodyNamed,
        Templates.sourceAbstraction,Templates.pair_exact,Templates.literal_exact,bodyExact,
        encodeWith,sourceTermCodec,putSourceTerm,nameCodec,encodeData_pair]

/-- Scoped authored syntax has a finite plan without consulting arguments. -/
theorem compile_isSome (arity : Nat) (body : DBTerm) (binders : List SourceVar)
    (scope : body.LooseBelow (binders.length+arity)) :
    (compile arity binders.length body binders).isSome = true := by
  induction body generalizing binders with
  | const => simp [compile]
  | free => simp [compile]
  | bound index =>
      change index < binders.length+arity at scope
      unfold compile
      split
      · rfl
      · rename_i outside
        have small : index < binders.length := by omega
        have found : binders[index]? = some (binders[index]'small) := by simp
        simp [found]
  | app function argument first second =>
      obtain ⟨firstScope,secondScope⟩ := scope
      obtain ⟨firstTemplate,firstFound⟩ := Option.isSome_iff_exists.mp (first binders firstScope)
      obtain ⟨secondTemplate,secondFound⟩ := Option.isSome_iff_exists.mp (second binders secondScope)
      simp [compile,firstFound,secondFound]
  | abs domain body ih =>
      let name := ReverseTranslation.freshName (binders.map Var.name ++ freeNames body)
      have nested : body.LooseBelow ((⟨name,domain⟩::binders).length+arity) := by
        simpa only [DBTerm.LooseBelow,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using scope
      have result := ih (⟨name,domain⟩::binders) nested
      obtain ⟨template,found⟩ := Option.isSome_iff_exists.mp result
      simp only [List.length_cons] at found
      simp [compile,name,found]




/-- An independently earned argument count fixes the finite control arity. -/
theorem compile_exact_arity (arity : Nat) (arguments : List CanonicalTerm)
    (length : arguments.length=arity) (sources : Fin arity → SourceTerm)
    (empty : ∀ argument ∈ arguments, freeNames argument.term = [])
    (independent : ∀ index : Fin arity, ∀ binders,
      named? (arguments[index.val]'(by omega)).term binders = some (sources index))
    (depth : Nat) (body : DBTerm) (binders : List SourceVar) :
    (compile arity depth body binders).map
      (fun template => Indexed.instantiate template (fun index => encodeWith sourceTermCodec (sources index))) =
    (named? (TemplateInstantiationMachine.Indexed.sequence arguments depth body) binders).map
      (encodeWith sourceTermCodec) := by
  subst arity
  exact compile_exact arguments sources empty (by
    intro index binders
    simpa only [Fin.getElem_fin] using independent index binders) depth body binders

/-- Finite tuple fields retain their independent order without baking them
into the descriptor. -/
theorem compile_exact_values (arity : Nat) (values : Fin arity → CanonicalTerm)
    (sources : Fin arity → SourceTerm)
    (empty : ∀ index, freeNames (values index).term = [])
    (independent : ∀ index binders, named? (values index).term binders = some (sources index))
    (depth : Nat) (body : DBTerm) (binders : List SourceVar) :
    (compile arity depth body binders).map
      (fun template => Indexed.instantiate template (fun index => encodeWith sourceTermCodec (sources index))) =
    (named? (TemplateInstantiationMachine.Indexed.sequence (List.ofFn values) depth body) binders).map
      (encodeWith sourceTermCodec) := by
  apply compile_exact_arity arity (List.ofFn values) (List.length_ofFn) sources _ _ depth body binders
  · intro argument member
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp member
    exact empty index
  · intro index binders
    simpa only [List.getElem_ofFn] using independent index binders

/-- The plan is computed solely from the scoped authored body and context. -/
def plan (arity : Nat) (body : DBTerm) (binders : List SourceVar)
    (scope : body.LooseBelow (binders.length+arity)) : Indexed.Template Alphabet arity :=
  (compile arity binders.length body binders).get (compile_isSome arity body binders scope)

theorem plan_computed (arity : Nat) (body : DBTerm) (binders : List SourceVar)
    (scope : body.LooseBelow (binders.length+arity)) :
    compile arity binders.length body binders = some (plan arity body binders scope) :=
  (Option.some_get _).symm

/-- Successful original naming fixes every emitted source byte. -/
theorem plan_exact (arguments : List CanonicalTerm) (sources : Fin arguments.length → SourceTerm)
    (empty : ∀ argument ∈ arguments, freeNames argument.term = [])
    (independent : ∀ index binders, named? (arguments[index]).term binders = some (sources index))
    (body : DBTerm) (binders : List SourceVar)
    (scope : body.LooseBelow (binders.length+arguments.length))
    (source : SourceTerm)
    (named : named? (TemplateInstantiationMachine.Indexed.sequence arguments binders.length body) binders = some source) :
    Indexed.instantiate (plan arguments.length body binders scope) (sourceWords arguments sources) =
      encodeWith sourceTermCodec source := by
  have exactResult := compile_exact arguments sources empty independent binders.length body binders
  rw [plan_computed arguments.length body binders scope,named] at exactResult
  exact Option.some.inj exactResult

/-- Actual finite copying emits the original representative with its own step
count. The complete compiled descriptor is charged by its plan length. -/
def outputs (arguments : List CanonicalTerm) (sources : Fin arguments.length → SourceTerm)
    (empty : ∀ argument ∈ arguments, freeNames argument.term = [])
    (independent : ∀ index binders, named? (arguments[index]).term binders = some (sources index))
    (body : DBTerm) (binders : List SourceVar)
    (scope : body.LooseBelow (binders.length+arguments.length))
    (source : SourceTerm)
    (named : named? (TemplateInstantiationMachine.Indexed.sequence arguments binders.length body) binders = some source) :
    Turing.TM2OutputsInTime (Indexed.machine (plan arguments.length body binders scope))
      (Indexed.argumentWire (sourceWords arguments sources)) (some (encodeWith sourceTermCodec source))
      (4*((plan arguments.length body binders scope).length+1)*
        ((Indexed.argumentWire (sourceWords arguments sources)).length+1)) := by
  rw [← plan_exact arguments sources empty independent body binders scope source named]
  exact Indexed.outputs _ _

end Mettapedia.Languages.HOLLight.ScopedNamedTemplates
