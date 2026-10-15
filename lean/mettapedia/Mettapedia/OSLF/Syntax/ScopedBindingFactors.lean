import Mettapedia.OSLF.Syntax.ScopedBindingFrameCancellation

/-!
# Executable complete factors of raw scoped binding terms

The enumeration visits every literal constructor position. Each result
retains its actual hole scope, entire hole term, every sibling and complete
linear binder path. No enumeration of the signature's sorts or operators
is needed. These are raw syntactic factors, not factors modulo equations
or solutions of a higher-order metavariable matching problem.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.Binding.ScopedEncoding

variable {S : Binding.Signature}

local instance bindingFactorQuiver : Quiver (Scope S) := bindingFrameQuiver S

structure BindingFactor (S : Binding.Signature) (target : Scope S) where
  source : Scope S
  value : Binding.Term S source.1 source.2
  path : BindingContext S source target

def BindingFactor.fill {target : Scope S} (factor : BindingFactor S target) :
    Binding.Term S target.1 target.2 := fillContext factor.path factor.value

def BindingFactor.root {target : Scope S} (term : Binding.Term S target.1 target.2) :
    BindingFactor S target := ⟨target, term, .nil⟩

def BindingFactor.extend {middle target : Scope S}
    (frame : BindingFrame S middle target) (factor : BindingFactor S middle) :
    BindingFactor S target := ⟨factor.source, factor.value, .cons factor.path frame⟩

theorem BindingFactor.root_fill {target : Scope S}
    (term : Binding.Term S target.1 target.2) : (BindingFactor.root term).fill = term := rfl

theorem BindingFactor.extend_fill {middle target : Scope S}
    (frame : BindingFrame S middle target) (factor : BindingFactor S middle) :
    (factor.extend frame).fill = frame.fill factor.fill := rfl

mutual
  def bindingFactors : {context : Binding.Ctx S} → {sort : S.Srt} →
      Binding.Term S context sort → List (BindingFactor S (context, sort))
    | _, _, .var position => [BindingFactor.root (.var position)]
    | context, sort, .op operator arguments =>
        BindingFactor.root (.op operator arguments) ::
          bindingArgumentFactors arguments (fun position factor => factor.extend
            (.slot context sort operator position
              (fun other _ => argumentsAt arguments other)))

  def bindingArgumentFactors : {declarations : List (List S.Srt × S.Srt)} →
      {context : Binding.Ctx S} → (arguments : Binding.Args S declarations context) →
      {target : Scope S} →
      ((position : Fin declarations.length) →
        BindingFactor S ((declarations.get position).1 ++ context,
          (declarations.get position).2) → BindingFactor S target) →
      List (BindingFactor S target)
    | _, _, .nil, _, _ => []
    | _, _, .cons head tail, _, extend =>
        (bindingFactors head).map (extend 0) ++
          bindingArgumentFactors tail (fun position factor => extend position.succ factor)
end

theorem mem_bindingArgumentFactors : ∀ {declarations : List (List S.Srt × S.Srt)}
    {context : Binding.Ctx S} (arguments : Binding.Args S declarations context)
    {target : Scope S}
    (extend : (position : Fin declarations.length) →
      BindingFactor S ((declarations.get position).1 ++ context,
        (declarations.get position).2) → BindingFactor S target)
    (factor : BindingFactor S target),
    factor ∈ bindingArgumentFactors arguments extend ↔
      ∃ position child, child ∈ bindingFactors (argumentsAt arguments position) ∧
        extend position child = factor
  | _, _, .nil, _, _, _ => by
    simp only [bindingArgumentFactors, List.not_mem_nil, false_iff]
    rintro ⟨position, _, _, _⟩
    exact Fin.elim0 position
  | _, _, .cons head rest, _, extend, factor => by
    simp only [bindingArgumentFactors, List.mem_append]
    constructor
    · rintro (headMember | tailMember)
      · obtain ⟨child, member, same⟩ := List.mem_map.mp headMember
        exact ⟨0, child, member, same⟩
      · obtain ⟨position, child, member, same⟩ :=
          (mem_bindingArgumentFactors rest
            (fun position child => extend position.succ child) factor).mp tailMember
        exact ⟨position.succ, child, member, same⟩
    · rintro ⟨position, child, member, same⟩
      revert child
      refine Fin.cases ?_ (fun previous => ?_) position
      · intro child member same
        exact Or.inl (List.mem_map.mpr ⟨child, member, same⟩)
      · intro child member same
        exact Or.inr ((mem_bindingArgumentFactors rest
          (fun position child => extend position.succ child) factor).mpr
            ⟨previous, child, member, same⟩)

mutual
  theorem bindingFactors_length : ∀ {context : Binding.Ctx S} {sort : S.Srt}
      (term : Binding.Term S context sort),
      (bindingFactors term).length = Binding.termSize term
    | _, _, .var _ => rfl
    | _, _, .op _ arguments => by
        simp only [bindingFactors, List.length_cons, bindingArgumentFactors_length,
          Binding.termSize]

  theorem bindingArgumentFactors_length :
      ∀ {declarations : List (List S.Srt × S.Srt)} {context : Binding.Ctx S}
      (arguments : Binding.Args S declarations context) {target : Scope S}
      (extend : (position : Fin declarations.length) →
        BindingFactor S ((declarations.get position).1 ++ context,
          (declarations.get position).2) → BindingFactor S target),
      (bindingArgumentFactors arguments extend).length = Binding.argsSize arguments
    | _, _, .nil, _, _ => rfl
    | _, _, .cons head tail, _, extend => by
        change (List.map (extend 0) (bindingFactors head) ++
          bindingArgumentFactors tail (fun position factor => extend position.succ factor)).length =
          Binding.termSize head + Binding.argsSize tail
        rw [List.length_append]
        exact congrArg₂ Nat.add
          ((List.length_map (extend 0)).trans (bindingFactors_length head))
          (bindingArgumentFactors_length tail _)
end

theorem bindingFactors_root {context : Binding.Ctx S} {sort : S.Srt}
    (term : Binding.Term S context sort) : BindingFactor.root term ∈ bindingFactors term := by
  cases term with
  | var position => exact List.mem_singleton.mpr rfl
  | op operator arguments => exact List.mem_cons_self

mutual
  theorem bindingFactors_sound : ∀ {context : Binding.Ctx S} {sort : S.Srt}
      (term : Binding.Term S context sort) (factor : BindingFactor S (context, sort)),
      factor ∈ bindingFactors term → factor.fill = term
    | _, _, .var position, factor, member => by
        simp only [bindingFactors, List.mem_singleton] at member
        subst factor
        rfl
    | context, sort, .op operator arguments, factor, member => by
        simp only [bindingFactors, List.mem_cons] at member
        rcases member with same | childMember
        · subst factor
          rfl
        · obtain ⟨position, child, member, same⟩ :=
            (mem_bindingArgumentFactors arguments _ factor).mp childMember
          subst factor
          rw [BindingFactor.extend_fill,
            bindingArguments_sound arguments position child member]
          change Binding.Term.op operator (assembleArguments context (S.arity operator)
            (fun other => if equal : other = position then
              equal.symm ▸ argumentsAt arguments position else argumentsAt arguments other)) = _
          have family : (fun other => if equal : other = position then
              equal.symm ▸ argumentsAt arguments position else argumentsAt arguments other) =
              argumentsAt arguments := by
            funext other
            split
            · rename_i equal
              subst other
              rfl
            · rfl
          rw [family, assemble_argumentsAt]

  theorem bindingArguments_sound :
      ∀ {declarations : List (List S.Srt × S.Srt)} {context : Binding.Ctx S}
      (arguments : Binding.Args S declarations context)
      (position : Fin declarations.length)
      (factor : BindingFactor S ((declarations.get position).1 ++ context,
        (declarations.get position).2)),
      factor ∈ bindingFactors (argumentsAt arguments position) →
        factor.fill = argumentsAt arguments position
    | _, _, .nil, position, _, _ => Fin.elim0 position
    | _, _, .cons head tail, position, factor, member => by
        revert factor
        refine Fin.cases ?_ (fun previous => ?_) position
        · intro factor member
          exact bindingFactors_sound head factor member
        · intro factor member
          exact bindingArguments_sound tail previous factor member
end

theorem bindingFactors_complete {source target : Scope S}
    (path : BindingContext S source target) (value : Binding.Term S source.1 source.2) :
    (⟨source, value, path⟩ : BindingFactor S target) ∈ bindingFactors (fillContext path value) := by
  induction path with
  | nil => exact bindingFactors_root value
  | cons previous frame inductionHypothesis =>
    cases frame with
    | slot context sort operator position siblings =>
      let child : BindingFactor S (((S.arity operator).get position).1 ++ context,
        ((S.arity operator).get position).2) := ⟨source, value, previous⟩
      let arguments := assembleArguments context (S.arity operator)
        (fun other => if equal : other = position then
          equal.symm ▸ child.fill else siblings other equal)
      change (⟨source, value, .cons previous
        (.slot context sort operator position siblings)⟩ : BindingFactor S (context, sort)) ∈
        BindingFactor.root (.op operator arguments) ::
          bindingArgumentFactors arguments (fun selected factor => factor.extend
            (.slot context sort operator selected (fun other _ => argumentsAt arguments other)))
      apply List.mem_cons_of_mem
      apply (mem_bindingArgumentFactors arguments _ _).mpr
      refine ⟨position, child, ?_, ?_⟩
      · simpa only [arguments, argumentsAt_assemble, dite_true, child, BindingFactor.fill]
          using inductionHypothesis
      · have siblingReadout : (fun other (_ : other ≠ position) =>
            argumentsAt arguments other) = siblings := by
          funext other absent
          simp only [arguments, argumentsAt_assemble, dif_neg absent]
        simp only [BindingFactor.extend, siblingReadout, child]

theorem mem_bindingFactors_iff {target : Scope S}
    (term : Binding.Term S target.1 target.2) (factor : BindingFactor S target) :
    factor ∈ bindingFactors term ↔ factor.fill = term := by
  constructor
  · exact bindingFactors_sound term factor
  · intro same
    rw [← same]
    exact bindingFactors_complete factor.path factor.value

end Mettapedia.OSLF.Binding.ScopedEncoding
