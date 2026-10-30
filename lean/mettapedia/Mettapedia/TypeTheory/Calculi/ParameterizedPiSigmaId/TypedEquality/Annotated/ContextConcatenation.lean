import Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.TypedEquality.Annotated.Validity

/-!
# Independent typed contexts in one ambient context

The younger context retains its variable indices. Older variables move past
all younger binders. Types in each block are renamed with the corresponding
placement, so formation and typed judgments embed without identifying any
of the two blocks' variables.
-/

set_option autoImplicit false
namespace Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated
variable {Head : Type} {R : Rules Head} {P : ChurchRules R}

namespace CCtx

def younger (m n : Nat) : Ren n (m + n) := fun index =>
  ⟨index.val, Nat.lt_of_lt_of_le index.isLt (Nat.le_add_left _ _)⟩

def older (m n : Nat) : Ren m (m + n) := fun index =>
  ⟨index.val + n, Nat.add_lt_add_right index.isLt n⟩

theorem younger_succ (m n : Nat) : younger m (n + 1) = liftRen (younger m n) := by
  funext index
  refine Fin.cases ?_ ?_ index
  · rfl
  · intro prior
    rfl

theorem older_succ (m n : Nat) : older m (n + 1) = fun index => wk (older m n index) := rfl

def appendOlder {m : Nat} (base : CCtx Head m) : {n : Nat} → CCtx Head n → CCtx Head (m + n)
  | _, .nil => base
  | _, .snoc context domain => .snoc (appendOlder base context) (domain.rename (younger m _))

theorem younger_compatible {m n : Nat} (base : CCtx Head m) (context : CCtx Head n) :
    CCtxRen context (appendOlder base context) (younger m n) := by
  induction context with
  | nil => intro index; exact index.elim0
  | snoc prior domain ih =>
      simpa only [appendOlder, younger_succ] using ih.snoc domain

theorem older_compatible {m n : Nat} (base : CCtx Head m) (context : CCtx Head n) :
    CCtxRen base (appendOlder base context) (older m n) := by
  induction context with
  | nil =>
      intro index
      change base.lookup index = (base.lookup index).rename (fun index => index)
      exact (CTm.rename_id _).symm
  | snoc prior domain ih =>
      simpa only [appendOlder, older_succ] using placement_succ ih (domain.rename (younger m _))

theorem blocks_disjoint {m n : Nat} (first : Fin m) (second : Fin n) :
    older m n first ≠ younger m n second := by
  intro same
  have values := congrArg Fin.val same
  dsimp [older, younger] at values
  omega

end CCtx

theorem CCtxFormed.appendOlder {m n : Nat} {base : CCtx Head m} {context : CCtx Head n}
    (baseFormed : CCtxFormed P base) (formed : CCtxFormed P context) :
    CCtxFormed P (CCtx.appendOlder base context) := by
  induction formed with
  | nil => exact baseFormed
  | @snoc n context domain formed typeDomain ih =>
      obtain ⟨level, allowed, typed⟩ := typeDomain
      exact .snoc ih ⟨level, allowed, typed.rename (CCtx.younger_compatible base context)⟩

#print axioms CCtx.younger_compatible
#print axioms CCtx.older_compatible
#print axioms CCtx.blocks_disjoint
#print axioms CCtxFormed.appendOlder
end Mettapedia.TypeTheory.Calculi.ParameterizedPiSigmaId.Presentation.TypedEquality.Annotated
