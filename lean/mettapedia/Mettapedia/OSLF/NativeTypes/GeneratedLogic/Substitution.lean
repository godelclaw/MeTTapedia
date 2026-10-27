import Mettapedia.OSLF.NativeTypes.GeneratedLogic.Invariance

/-!
# Renaming and substituting fixed-point variables

Formulas keep their free fixed-point variables as indices. Two operations act on them:

- **Renaming** (`Formula.rename`) maps indices along a function and lifts it past each fixed-point binder.
  A renamed formula holds where the formula holds under the environment read through the along
  (`sat_rename`).
- **Substitution** (`Formula.subst`) replaces each free variable by a formula, weakened past each binder by
  along. A substituted formula holds where the formula holds under the environment of the substituted
  formulas' truth sets (`sat_subst`). For closed formulas this turns a formula with free atoms into a
  closed one with the same meaning (`sat_close`).
- **Fixed points unfold** (`sat_mu_unfold`, `sat_nu_unfold`): `μX. φ` and `νX. φ` hold exactly where `φ`
  holds with the fixed point itself substituted for `X`.
-/

set_option autoImplicit false

namespace Mettapedia.OSLF.NativeTypes.GeneratedLogic

universe u

/-- A along lifted past a binder: the new variable stays, the others move up. -/
def liftRenaming {n m : ℕ} (along : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1) :=
  Fin.cases 0 fun index => (along index).succ

mutual
/-- **Rename the free variables** of a formula. -/
def Formula.rename : {n m : ℕ} → (Fin n → Fin m) → Formula n → Formula m
  | _, _, _, .top => .top
  | _, _, _, .bot => .bot
  | _, _, along, .and left right => .and (left.rename along) (right.rename along)
  | _, _, along, .or left right => .or (left.rename along) (right.rename along)
  | _, _, along, .var index => .var (along index)
  | _, _, along, .mu inner => .mu (inner.rename (liftRenaming along))
  | _, _, along, .nu inner => .nu (inner.rename (liftRenaming along))
  | _, _, along, .possibly label formula => .possibly label (formula.rename along)
  | _, _, along, .necessarily label formula => .necessarily label (formula.rename along)
  | _, _, along, .sometimeBefore label formula => .sometimeBefore label (formula.rename along)
  | _, _, along, .alwaysBefore label formula => .alwaysBefore label (formula.rename along)
  | _, _, along, .atLeast count direction label formula => .atLeast count direction label (formula.rename along)
  | _, _, along, .allButFewer count direction label formula =>
    .allButFewer count direction label (formula.rename along)
  | _, _, along, .built constructor arguments => .built constructor (arguments.rename along)
  | _, _, along, .everyBuilt constructor arguments => .everyBuilt constructor (arguments.rename along)
  | _, _, along, .split kind left right => .split kind (left.rename along) (right.rename along)
  | _, _, along, .everySplit kind left right => .everySplit kind (left.rename along) (right.rename along)
  | _, _, _, .empty kind => .empty kind
  | _, _, _, .nonEmpty kind => .nonEmpty kind
  | _, _, along, .single kind formula => .single kind (formula.rename along)
  | _, _, along, .everySingle kind formula => .everySingle kind (formula.rename along)
  | _, _, along, .body formula => .body (formula.rename along)
  | _, _, along, .everyBody formula => .everyBody (formula.rename along)
  | _, _, along, .multiBody arity formula => .multiBody arity (formula.rename along)
  | _, _, along, .everyMultiBody arity formula => .everyMultiBody arity (formula.rename along)
  | _, _, _, .bound index => .bound index
  | _, _, _, .notBound index => .notBound index
  | _, _, _, .typed type => .typed type
  | _, _, _, .untyped type => .untyped type
  | _, _, _, .is term => .is term
  | _, _, _, .isNot term => .isNot term
  | _, _, _, .inRelation relation => .inRelation relation
  | _, _, _, .notInRelation relation => .notInRelation relation
  | _, _, along, .mapsAll argument result => .mapsAll (argument.rename along) (result.rename along)
  | _, _, along, .mapsSome argument result => .mapsSome (argument.rename along) (result.rename along)
  | _, _, along, .someOf type formula => .someOf type (formula.rename along)
  | _, _, along, .everyOf type formula => .everyOf type (formula.rename along)

/-- Rename the free variables of a list of formulas. -/
def Formulas.rename : {n m : ℕ} → (Fin n → Fin m) → Formulas n → Formulas m
  | _, _, _, .nil => .nil
  | _, _, along, .cons formula formulas => .cons (formula.rename along) (formulas.rename along)
end

/-- A substitution lifted past a binder: the new variable stays, the others are weakened. -/
def liftSubstitution {n m : ℕ} (substitution : Fin n → Formula m) : Fin (n + 1) → Formula (m + 1) :=
  Fin.cases (.var 0) fun index => (substitution index).rename Fin.succ

mutual
/-- **Substitute formulas for the free variables** of a formula. -/
def Formula.subst : {n m : ℕ} → (Fin n → Formula m) → Formula n → Formula m
  | _, _, _, .top => .top
  | _, _, _, .bot => .bot
  | _, _, substitution, .and left right => .and (left.subst substitution) (right.subst substitution)
  | _, _, substitution, .or left right => .or (left.subst substitution) (right.subst substitution)
  | _, _, substitution, .var index => substitution index
  | _, _, substitution, .mu inner => .mu (inner.subst (liftSubstitution substitution))
  | _, _, substitution, .nu inner => .nu (inner.subst (liftSubstitution substitution))
  | _, _, substitution, .possibly label formula => .possibly label (formula.subst substitution)
  | _, _, substitution, .necessarily label formula => .necessarily label (formula.subst substitution)
  | _, _, substitution, .sometimeBefore label formula => .sometimeBefore label (formula.subst substitution)
  | _, _, substitution, .alwaysBefore label formula => .alwaysBefore label (formula.subst substitution)
  | _, _, substitution, .atLeast count direction label formula =>
    .atLeast count direction label (formula.subst substitution)
  | _, _, substitution, .allButFewer count direction label formula =>
    .allButFewer count direction label (formula.subst substitution)
  | _, _, substitution, .built constructor arguments => .built constructor (arguments.subst substitution)
  | _, _, substitution, .everyBuilt constructor arguments => .everyBuilt constructor (arguments.subst substitution)
  | _, _, substitution, .split kind left right => .split kind (left.subst substitution) (right.subst substitution)
  | _, _, substitution, .everySplit kind left right =>
    .everySplit kind (left.subst substitution) (right.subst substitution)
  | _, _, _, .empty kind => .empty kind
  | _, _, _, .nonEmpty kind => .nonEmpty kind
  | _, _, substitution, .single kind formula => .single kind (formula.subst substitution)
  | _, _, substitution, .everySingle kind formula => .everySingle kind (formula.subst substitution)
  | _, _, substitution, .body formula => .body (formula.subst substitution)
  | _, _, substitution, .everyBody formula => .everyBody (formula.subst substitution)
  | _, _, substitution, .multiBody arity formula => .multiBody arity (formula.subst substitution)
  | _, _, substitution, .everyMultiBody arity formula => .everyMultiBody arity (formula.subst substitution)
  | _, _, _, .bound index => .bound index
  | _, _, _, .notBound index => .notBound index
  | _, _, _, .typed type => .typed type
  | _, _, _, .untyped type => .untyped type
  | _, _, _, .is term => .is term
  | _, _, _, .isNot term => .isNot term
  | _, _, _, .inRelation relation => .inRelation relation
  | _, _, _, .notInRelation relation => .notInRelation relation
  | _, _, substitution, .mapsAll argument result =>
    .mapsAll (argument.subst substitution) (result.subst substitution)
  | _, _, substitution, .mapsSome argument result =>
    .mapsSome (argument.subst substitution) (result.subst substitution)
  | _, _, substitution, .someOf type formula => .someOf type (formula.subst substitution)
  | _, _, substitution, .everyOf type formula => .everyOf type (formula.subst substitution)

/-- Substitute formulas for the free variables of a list of formulas. -/
def Formulas.subst : {n m : ℕ} → (Fin n → Formula m) → Formulas n → Formulas m
  | _, _, _, .nil => .nil
  | _, _, substitution, .cons formula formulas => .cons (formula.subst substitution) (formulas.subst substitution)
end

namespace NativeStructure

variable {Carrier : Type u} (S : NativeStructure Carrier)

theorem extend_liftRenaming {n m : ℕ} (along : Fin n → Fin m) (env : Env Carrier m) (set : Set Carrier) :
    (fun index => env.extend set (liftRenaming along index)) = Env.extend (fun index => env (along index)) set := by
  funext index
  refine Fin.cases ?_ (fun _ => ?_) index <;> rfl

mutual
/-- **A renamed formula holds** where the formula holds under the environment read through the along. -/
theorem sat_rename : ∀ {n m : ℕ} (along : Fin n → Fin m) (formula : Formula n) (env : Env Carrier m)
    (element : Carrier), S.sat env (formula.rename along) element ↔ S.sat (fun index => env (along index)) formula element
  | _, _, _, .top, _, _ => Iff.rfl
  | _, _, _, .bot, _, _ => Iff.rfl
  | _, _, along, .and left right, env, element =>
    and_congr (sat_rename along left env element) (sat_rename along right env element)
  | _, _, along, .or left right, env, element =>
    or_congr (sat_rename along left env element) (sat_rename along right env element)
  | _, _, _, .var _, _, _ => Iff.rfl
  | _, _, along, .mu inner, env, element => by
    show (∀ closed : Set Carrier, (∀ other, S.sat (env.extend closed) (inner.rename (liftRenaming along)) other →
        other ∈ closed) → element ∈ closed) ↔ _
    refine forall_congr' fun closed => imp_congr_left (forall_congr' fun other => imp_congr_left ?_)
    rw [sat_rename (liftRenaming along) inner (env.extend closed) other, extend_liftRenaming]
  | _, _, along, .nu inner, env, element => by
    show (∃ invariant : Set Carrier, element ∈ invariant ∧
        ∀ other ∈ invariant, S.sat (env.extend invariant) (inner.rename (liftRenaming along)) other) ↔ _
    refine exists_congr fun invariant => and_congr Iff.rfl (forall_congr' fun other => imp_congr_right fun _ => ?_)
    rw [sat_rename (liftRenaming along) inner (env.extend invariant) other, extend_liftRenaming]
  | _, _, along, .possibly _ formula, env, _ =>
    exists_congr fun next => and_congr Iff.rfl (sat_rename along formula env next)
  | _, _, along, .necessarily _ formula, env, _ =>
    forall_congr' fun next => imp_congr_right fun _ => sat_rename along formula env next
  | _, _, along, .sometimeBefore _ formula, env, _ =>
    exists_congr fun previous => and_congr Iff.rfl (sat_rename along formula env previous)
  | _, _, along, .alwaysBefore _ formula, env, _ =>
    forall_congr' fun previous => imp_congr_right fun _ => sat_rename along formula env previous
  | _, _, along, .atLeast _ _ _ formula, env, _ =>
    NativeStructure.AtLeast.congr fun other => and_congr Iff.rfl (sat_rename along formula env other)
  | _, _, along, .allButFewer _ _ _ formula, env, _ =>
    not_congr (NativeStructure.AtLeast.congr fun other => and_congr Iff.rfl (not_congr (sat_rename along formula env other)))
  | _, _, along, .built _ arguments, env, _ =>
    exists_congr fun parts => and_congr Iff.rfl (satAll_rename along arguments env parts)
  | _, _, along, .everyBuilt _ arguments, env, _ =>
    forall_congr' fun parts => imp_congr_right fun _ => satSome_rename along arguments env parts
  | _, _, along, .split _ left right, env, _ =>
    exists_congr fun first => exists_congr fun second =>
      and_congr Iff.rfl (and_congr (sat_rename along left env first) (sat_rename along right env second))
  | _, _, along, .everySplit _ left right, env, _ =>
    forall_congr' fun first => forall_congr' fun second => imp_congr_right fun _ =>
      or_congr (sat_rename along left env first) (sat_rename along right env second)
  | _, _, _, .empty _, _, _ => Iff.rfl
  | _, _, _, .nonEmpty _, _, _ => Iff.rfl
  | _, _, along, .single _ formula, env, _ =>
    exists_congr fun member => and_congr Iff.rfl (sat_rename along formula env member)
  | _, _, along, .everySingle _ formula, env, _ =>
    forall_congr' fun member => imp_congr_right fun _ => sat_rename along formula env member
  | _, _, along, .body formula, env, _ =>
    exists_congr fun inner => and_congr Iff.rfl (sat_rename along formula env inner)
  | _, _, along, .everyBody formula, env, _ =>
    forall_congr' fun inner => imp_congr_right fun _ => sat_rename along formula env inner
  | _, _, along, .multiBody _ formula, env, _ =>
    exists_congr fun inner => and_congr Iff.rfl (sat_rename along formula env inner)
  | _, _, along, .everyMultiBody _ formula, env, _ =>
    forall_congr' fun inner => imp_congr_right fun _ => sat_rename along formula env inner
  | _, _, _, .bound _, _, _ => Iff.rfl
  | _, _, _, .notBound _, _, _ => Iff.rfl
  | _, _, _, .typed _, _, _ => Iff.rfl
  | _, _, _, .untyped _, _, _ => Iff.rfl
  | _, _, _, .is _, _, _ => Iff.rfl
  | _, _, _, .isNot _, _, _ => Iff.rfl
  | _, _, _, .inRelation _, _, _ => Iff.rfl
  | _, _, _, .notInRelation _, _, _ => Iff.rfl
  | _, _, along, .mapsAll argument result, env, _ =>
    exists_congr fun inner => and_congr Iff.rfl (forall_congr' fun value =>
      or_congr (sat_rename along argument env value) (sat_rename along result env _))
  | _, _, along, .mapsSome argument result, env, _ =>
    forall_congr' fun inner => imp_congr_right fun _ => exists_congr fun value =>
      and_congr (sat_rename along argument env value) (sat_rename along result env _)
  | _, _, along, .someOf _ formula, env, _ =>
    exists_congr fun witness => and_congr Iff.rfl (sat_rename along formula env witness)
  | _, _, along, .everyOf _ formula, env, _ =>
    forall_congr' fun witness => imp_congr_right fun _ => sat_rename along formula env witness

theorem satAll_rename : ∀ {n m : ℕ} (along : Fin n → Fin m) (formulas : Formulas n) (env : Env Carrier m)
    (parts : List Carrier),
    S.satAll env (formulas.rename along) parts ↔ S.satAll (fun index => env (along index)) formulas parts
  | _, _, _, .nil, _, [] => Iff.rfl
  | _, _, _, .nil, _, _ :: _ => Iff.rfl
  | _, _, _, .cons _ _, _, [] => Iff.rfl
  | _, _, along, .cons formula formulas, env, part :: parts =>
    and_congr (sat_rename along formula env part) (satAll_rename along formulas env parts)

theorem satSome_rename : ∀ {n m : ℕ} (along : Fin n → Fin m) (formulas : Formulas n) (env : Env Carrier m)
    (parts : List Carrier),
    S.satSome env (formulas.rename along) parts ↔ S.satSome (fun index => env (along index)) formulas parts
  | _, _, _, .nil, _, [] => Iff.rfl
  | _, _, _, .nil, _, _ :: _ => Iff.rfl
  | _, _, _, .cons _ _, _, [] => Iff.rfl
  | _, _, along, .cons formula formulas, env, part :: parts =>
    or_congr (sat_rename along formula env part) (satSome_rename along formulas env parts)
end

/-- The truth sets of substituted formulas. -/
def truthSets {n m : ℕ} (env : Env Carrier m) (substitution : Fin n → Formula m) : Env Carrier n :=
  fun index => {element | S.sat env (substitution index) element}

theorem truthSets_lift {n m : ℕ} (env : Env Carrier m) (substitution : Fin n → Formula m) (set : Set Carrier) :
    S.truthSets (env.extend set) (liftSubstitution substitution) = (S.truthSets env substitution).extend set := by
  funext index
  refine Fin.cases ?_ (fun index => ?_) index
  · rfl
  · ext element
    show S.sat (env.extend set) ((substitution index).rename Fin.succ) element ↔ S.sat env (substitution index) element
    rw [sat_rename]
    rfl

mutual
/-- **A substituted formula holds** where the formula holds under the truth sets of the substituted
formulas. -/
theorem sat_subst : ∀ {n m : ℕ} (substitution : Fin n → Formula m) (formula : Formula n) (env : Env Carrier m)
    (element : Carrier), S.sat env (formula.subst substitution) element ↔ S.sat (S.truthSets env substitution) formula element
  | _, _, _, .top, _, _ => Iff.rfl
  | _, _, _, .bot, _, _ => Iff.rfl
  | _, _, substitution, .and left right, env, element =>
    and_congr (sat_subst substitution left env element) (sat_subst substitution right env element)
  | _, _, substitution, .or left right, env, element =>
    or_congr (sat_subst substitution left env element) (sat_subst substitution right env element)
  | _, _, _, .var _, _, _ => Iff.rfl
  | _, _, substitution, .mu inner, env, element => by
    show (∀ closed : Set Carrier, (∀ other, S.sat (env.extend closed) (inner.subst (liftSubstitution substitution))
        other → other ∈ closed) → element ∈ closed) ↔ _
    refine forall_congr' fun closed => imp_congr_left (forall_congr' fun other => imp_congr_left ?_)
    rw [sat_subst (liftSubstitution substitution) inner (env.extend closed) other, truthSets_lift]
  | _, _, substitution, .nu inner, env, element => by
    show (∃ invariant : Set Carrier, element ∈ invariant ∧
        ∀ other ∈ invariant, S.sat (env.extend invariant) (inner.subst (liftSubstitution substitution)) other) ↔ _
    refine exists_congr fun invariant => and_congr Iff.rfl (forall_congr' fun other => imp_congr_right fun _ => ?_)
    rw [sat_subst (liftSubstitution substitution) inner (env.extend invariant) other, truthSets_lift]
  | _, _, substitution, .possibly _ formula, env, _ =>
    exists_congr fun next => and_congr Iff.rfl (sat_subst substitution formula env next)
  | _, _, substitution, .necessarily _ formula, env, _ =>
    forall_congr' fun next => imp_congr_right fun _ => sat_subst substitution formula env next
  | _, _, substitution, .sometimeBefore _ formula, env, _ =>
    exists_congr fun previous => and_congr Iff.rfl (sat_subst substitution formula env previous)
  | _, _, substitution, .alwaysBefore _ formula, env, _ =>
    forall_congr' fun previous => imp_congr_right fun _ => sat_subst substitution formula env previous
  | _, _, substitution, .atLeast _ _ _ formula, env, _ =>
    NativeStructure.AtLeast.congr fun other => and_congr Iff.rfl (sat_subst substitution formula env other)
  | _, _, substitution, .allButFewer _ _ _ formula, env, _ =>
    not_congr (NativeStructure.AtLeast.congr fun other => and_congr Iff.rfl (not_congr (sat_subst substitution formula env other)))
  | _, _, substitution, .built _ arguments, env, _ =>
    exists_congr fun parts => and_congr Iff.rfl (satAll_subst substitution arguments env parts)
  | _, _, substitution, .everyBuilt _ arguments, env, _ =>
    forall_congr' fun parts => imp_congr_right fun _ => satSome_subst substitution arguments env parts
  | _, _, substitution, .split _ left right, env, _ =>
    exists_congr fun first => exists_congr fun second =>
      and_congr Iff.rfl (and_congr (sat_subst substitution left env first) (sat_subst substitution right env second))
  | _, _, substitution, .everySplit _ left right, env, _ =>
    forall_congr' fun first => forall_congr' fun second => imp_congr_right fun _ =>
      or_congr (sat_subst substitution left env first) (sat_subst substitution right env second)
  | _, _, _, .empty _, _, _ => Iff.rfl
  | _, _, _, .nonEmpty _, _, _ => Iff.rfl
  | _, _, substitution, .single _ formula, env, _ =>
    exists_congr fun member => and_congr Iff.rfl (sat_subst substitution formula env member)
  | _, _, substitution, .everySingle _ formula, env, _ =>
    forall_congr' fun member => imp_congr_right fun _ => sat_subst substitution formula env member
  | _, _, substitution, .body formula, env, _ =>
    exists_congr fun inner => and_congr Iff.rfl (sat_subst substitution formula env inner)
  | _, _, substitution, .everyBody formula, env, _ =>
    forall_congr' fun inner => imp_congr_right fun _ => sat_subst substitution formula env inner
  | _, _, substitution, .multiBody _ formula, env, _ =>
    exists_congr fun inner => and_congr Iff.rfl (sat_subst substitution formula env inner)
  | _, _, substitution, .everyMultiBody _ formula, env, _ =>
    forall_congr' fun inner => imp_congr_right fun _ => sat_subst substitution formula env inner
  | _, _, _, .bound _, _, _ => Iff.rfl
  | _, _, _, .notBound _, _, _ => Iff.rfl
  | _, _, _, .typed _, _, _ => Iff.rfl
  | _, _, _, .untyped _, _, _ => Iff.rfl
  | _, _, _, .is _, _, _ => Iff.rfl
  | _, _, _, .isNot _, _, _ => Iff.rfl
  | _, _, _, .inRelation _, _, _ => Iff.rfl
  | _, _, _, .notInRelation _, _, _ => Iff.rfl
  | _, _, substitution, .mapsAll argument result, env, _ =>
    exists_congr fun inner => and_congr Iff.rfl (forall_congr' fun value =>
      or_congr (sat_subst substitution argument env value) (sat_subst substitution result env _))
  | _, _, substitution, .mapsSome argument result, env, _ =>
    forall_congr' fun inner => imp_congr_right fun _ => exists_congr fun value =>
      and_congr (sat_subst substitution argument env value) (sat_subst substitution result env _)
  | _, _, substitution, .someOf _ formula, env, _ =>
    exists_congr fun witness => and_congr Iff.rfl (sat_subst substitution formula env witness)
  | _, _, substitution, .everyOf _ formula, env, _ =>
    forall_congr' fun witness => imp_congr_right fun _ => sat_subst substitution formula env witness

theorem satAll_subst : ∀ {n m : ℕ} (substitution : Fin n → Formula m) (formulas : Formulas n) (env : Env Carrier m)
    (parts : List Carrier),
    S.satAll env (formulas.subst substitution) parts ↔ S.satAll (S.truthSets env substitution) formulas parts
  | _, _, _, .nil, _, [] => Iff.rfl
  | _, _, _, .nil, _, _ :: _ => Iff.rfl
  | _, _, _, .cons _ _, _, [] => Iff.rfl
  | _, _, substitution, .cons formula formulas, env, part :: parts =>
    and_congr (sat_subst substitution formula env part) (satAll_subst substitution formulas env parts)

theorem satSome_subst : ∀ {n m : ℕ} (substitution : Fin n → Formula m) (formulas : Formulas n) (env : Env Carrier m)
    (parts : List Carrier),
    S.satSome env (formulas.subst substitution) parts ↔ S.satSome (S.truthSets env substitution) formulas parts
  | _, _, _, .nil, _, [] => Iff.rfl
  | _, _, _, .nil, _, _ :: _ => Iff.rfl
  | _, _, _, .cons _ _, _, [] => Iff.rfl
  | _, _, substitution, .cons formula formulas, env, part :: parts =>
    or_congr (sat_subst substitution formula env part) (satSome_subst substitution formulas env parts)
end

/-- **Closing a formula**: substituting closed formulas for its free variables gives a closed formula that
holds where the formula holds under their truth sets. -/
theorem sat_close {n : ℕ} (substitution : Fin n → Formula 0) (formula : Formula n) (element : Carrier) :
    S.sat Env.closed (formula.subst substitution) element ↔
      S.sat (fun index => {other | S.sat Env.closed (substitution index) other}) formula element :=
  S.sat_subst substitution formula Env.closed element

/-! ## Unfolding fixed points -/

/-- The substitution that unfolds a fixed point: the bound variable becomes the fixed point, the others
stay. -/
def unfolding {n : ℕ} (fixed : Formula n) : Fin (n + 1) → Formula n := Fin.cases fixed Formula.var

theorem truthSets_unfolding {n : ℕ} (env : Env Carrier n) (fixed : Formula n) :
    S.truthSets env (unfolding fixed) = env.extend {element | S.sat env fixed element} := by
  funext index
  refine Fin.cases rfl (fun _ => ?_) index
  rfl

/-- **A least fixed point unfolds.** -/
theorem sat_mu_unfold {n : ℕ} (inner : Formula (n + 1)) (env : Env Carrier n) (element : Carrier) :
    S.sat env (.mu inner) element ↔ S.sat env (inner.subst (unfolding (.mu inner))) element := by
  rw [sat_subst, truthSets_unfolding]
  let least : Set Carrier := {other | S.sat env (.mu inner) other}
  -- Each step of the body applied to the least fixed point stays inside it.
  have stays : ∀ other, S.sat (env.extend least) inner other → other ∈ least := by
    intro other holds closed prefixed
    have inside : least ⊆ closed := fun member memberHolds => memberHolds closed prefixed
    exact prefixed other (S.sat_mono inner (env.extend_sub inside) other holds)
  constructor
  · intro holds
    let applied : Set Carrier := {other | S.sat (env.extend least) inner other}
    have appliedPrefixed : ∀ other, S.sat (env.extend applied) inner other → other ∈ applied := by
      intro other holds'
      exact S.sat_mono inner (env.extend_sub fun member memberHolds => stays member memberHolds) other holds'
    exact holds applied appliedPrefixed
  · exact stays element

/-- **A greatest fixed point unfolds.** -/
theorem sat_nu_unfold {n : ℕ} (inner : Formula (n + 1)) (env : Env Carrier n) (element : Carrier) :
    S.sat env (.nu inner) element ↔ S.sat env (inner.subst (unfolding (.nu inner))) element := by
  rw [sat_subst, truthSets_unfolding]
  let greatest : Set Carrier := {other | S.sat env (.nu inner) other}
  -- The greatest fixed point is preserved by a step of the body.
  have kept : ∀ other ∈ greatest, S.sat (env.extend greatest) inner other := by
    rintro other ⟨invariant, member, preserved⟩
    have inside : invariant ⊆ greatest := fun member' memberIn => ⟨invariant, memberIn, preserved⟩
    exact S.sat_mono inner (env.extend_sub inside) other (preserved other member)
  constructor
  · exact kept element
  · intro holds
    let applied : Set Carrier := {other | S.sat (env.extend greatest) inner other}
    refine ⟨applied, holds, fun other otherHolds => ?_⟩
    have inside : greatest ⊆ applied := fun member memberIn => kept member memberIn
    exact S.sat_mono inner (env.extend_sub inside) other otherHolds

end NativeStructure

end Mettapedia.OSLF.NativeTypes.GeneratedLogic
