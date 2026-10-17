import Mettapedia.GSLT.Contexts.Expressiveness
import Mathlib.Data.List.Forall2

/-!
# Sealing is not eliminable from a transparent MeTTa core

A small deterministic core of MeTTa with one reflective space: data, `let`,
structural tests, `==` (`eq`, `ifEq`), `add-atom` (`add`), reading the whole
space (`all`), a space lookup (`assoc`, standing for a `match` that returns the
first stored `(KEY VALUE)` pair whose key is `==` to the given one), and
`quote`.  Its extension adds `new-seal`, `seal` and `unseal` with the
semantics recommended for MeTTa's seal primitive: a sealed value is an opaque
leaf compared by identity, prints without content, matches no structure, and
opens only under its own brand.

Programs cannot write seals or sealed values: literals are data.  Printing
produces data, as MeTTa prints text, so a seal-free program can show exactly
what a sealed one shows (`observe_sealed_datum`): the theorem below does not
rest on the observation seeing seals.

**Theorem** (`isEmpty_sealElimination`).  No translation into the seal-free
core that is homomorphic in the seal-free constructs and preserves the
observation of every program exists (Felleisen's eliminability, Definition
3.3), let alone a macro translation.  The proof uses three facts:

* **Abstraction in the extension** (`sealed_equiv`): `(let $k (new-seal)
  (seal $k 1))` and the same with `2` are contextually equivalent in the
  extension: every context, including contexts that use seals themselves,
  observes the same.  This is a noninterference argument over a relation that
  ignores the contents of boxes of brands no seal value can reach.
* **Transparency of the seal-free core** (`observe_readout`): one seal-free
  context reads back both the value of a program and the whole space, so
  seal-free equivalence of programs is equality of their outcomes.
* **Determinism and `let`**: the translation of `(let $k (new-seal) …)` is a
  `let` (homomorphism), so the box that the translated `seal` returns, and
  the space it leaves, determine what the translated `unseal` returns.

An elimination preserves equivalence (`Elimination.equiv_map`), so the
translated boxes for `1` and `2` would have equal outcomes, and then the
translated programs that open them would return equal values, while the
programs themselves return `1` and `2`.

**Controls.**
* `ifEq` is syntactic sugar for `cond` over `eq`; its translation is a macro
  elimination (`desugarElimination`), so the framework does not reject
  everything.
* A library emulation of seals (`emulate`, after the seal emulation of the
  seal proposal: capabilities, tickets and a registry in the space) is a
  candidate translation, homomorphic and seal-free (`emulateTranslation`), so
  the hypotheses other than preserving observations can be met.  It fails
  through the leaks pinned by the seal examples and the equation kernel's
  leak suite: reading the registry, destructuring a ticket, writing a
  registry entry, writing a capability.
* With `quote`, a context reads its hole back, so contextual equivalence is
  equality and no extension at all is eliminable
  (`isEmpty_elimination_reflective`); in particular the two sealed programs
  above are told apart (`quote_separates_sealed`).  Seals give abstraction only
  against code that cannot reflect on the program text.
-/

set_option autoImplicit false

namespace Mettapedia.Languages.MeTTa.Seal.Eliminability

open Mettapedia.GSLT.Expressiveness

/-! ## Data, values and programs -/

/-- Data a program can write: symbols (named by numbers), integers and lists. -/
inductive Datum where
  | sym (name : Nat)
  | num (value : Int)
  | nil
  | cons (head tail : Datum)
  deriving DecidableEq, Repr

/-- Runtime values: data, seals (`key brand`) and sealed values (`box brand
identity content`). -/
inductive Val where
  | sym (name : Nat)
  | num (value : Int)
  | nil
  | cons (head tail : Val)
  | key (brand : Nat)
  | box (brand identity : Nat) (content : Val)
  deriving DecidableEq, Repr

/-- A datum as a value. -/
def Datum.toVal : Datum → Val
  | .sym name => .sym name
  | .num value => .num value
  | .nil => .nil
  | .cons head tail => .cons head.toVal tail.toVal

/-- Programs of the core and its seal extension. -/
inductive Expr where
  | var (name : Nat)
  | lit (datum : Datum)
  | cons (head tail : Expr)
  | car (pair : Expr)
  | cdr (pair : Expr)
  | eq (left right : Expr)
  | cond (test yes no : Expr)
  | ifEq (left right yes no : Expr)
  | lett (name : Nat) (bound body : Expr)
  | add (value : Expr)
  | all
  | assoc (key : Expr)
  | quote (code : Expr)
  | newSeal
  | seal (sealer value : Expr)
  | unseal (unsealer value : Expr)
  deriving DecidableEq, Repr

/-! ## Evaluation -/

/-- The space and the counters for fresh brands and box identities. -/
structure State where
  store : List Val
  nextBrand : Nat
  nextBox : Nat
  deriving DecidableEq, Repr

/-- The empty space. -/
def State.init : State := ⟨[], 0, 0⟩

/-- Variable bindings, innermost first. -/
abbrev Env := List (Nat × Val)

/-- The innermost binding of a variable. -/
def lookup : Env → Nat → Option Val
  | [], _ => none
  | (name, value) :: rest, wanted => if name = wanted then some value else lookup rest wanted

/-- `True` and `False` as symbols. -/
def truth (b : Bool) : Val := if b then .sym 1 else .sym 0

/-- `==`: structural on data, by brand on seals, by identity on sealed values
(contents are not compared). -/
def same : Val → Val → Bool
  | .sym a, .sym b => decide (a = b)
  | .num a, .num b => decide (a = b)
  | .nil, .nil => true
  | .cons a b, .cons c d => same a c && same b d
  | .key a, .key b => decide (a = b)
  | .box a i _, .box b j _ => decide (a = b) && decide (i = j)
  | _, _ => false

/-- A list of values as a MeTTa list. -/
def listVal : List Val → Val
  | [] => .nil
  | value :: rest => .cons value (listVal rest)

/-- The first stored pair `(KEY . VALUE)` whose key is `==` to the given one. -/
def findEntry (wanted : Val) : List Val → Option Val
  | [] => none
  | .cons entryKey content :: rest =>
      if same entryKey wanted then some content else findEntry wanted rest
  | _ :: rest => findEntry wanted rest

/-- Program text as data, for `quote`: a tag per construct, then the parts. -/
def encode : Expr → Datum
  | .var name => .cons (.sym 1000) (.num name)
  | .lit datum => .cons (.sym 1001) datum
  | .cons head tail => .cons (.sym 1002) (.cons (encode head) (encode tail))
  | .car pair => .cons (.sym 1003) (encode pair)
  | .cdr pair => .cons (.sym 1004) (encode pair)
  | .eq left right => .cons (.sym 1005) (.cons (encode left) (encode right))
  | .cond test yes no => .cons (.sym 1006) (.cons (encode test) (.cons (encode yes) (encode no)))
  | .ifEq left right yes no =>
      .cons (.sym 1007) (.cons (encode left) (.cons (encode right) (.cons (encode yes) (encode no))))
  | .lett name bound body => .cons (.sym 1008) (.cons (.num name) (.cons (encode bound) (encode body)))
  | .add value => .cons (.sym 1009) (encode value)
  | .all => .sym 1010
  | .assoc key => .cons (.sym 1011) (encode key)
  | .quote code => .cons (.sym 1012) (encode code)
  | .newSeal => .sym 1013
  | .seal sealer value => .cons (.sym 1014) (.cons (encode sealer) (encode value))
  | .unseal unsealer value => .cons (.sym 1015) (.cons (encode unsealer) (encode value))

/-- Big-step evaluation: one result or none (MeTTa's empty result). -/
def eval : Expr → Env → State → Option (Val × State)
  | .var name, env, s => (lookup env name).map fun value => (value, s)
  | .lit datum, _, s => some (datum.toVal, s)
  | .cons head tail, env, s =>
      (eval head env s).bind fun r => (eval tail env r.2).bind fun r' => some (.cons r.1 r'.1, r'.2)
  | .car pair, env, s =>
      (eval pair env s).bind fun r =>
        match r.1 with
        | .cons head _ => some (head, r.2)
        | _ => none
  | .cdr pair, env, s =>
      (eval pair env s).bind fun r =>
        match r.1 with
        | .cons _ tail => some (tail, r.2)
        | _ => none
  | .eq left right, env, s =>
      (eval left env s).bind fun r =>
        (eval right env r.2).bind fun r' => some (truth (same r.1 r'.1), r'.2)
  | .cond test yes no, env, s =>
      (eval test env s).bind fun r => if r.1 = .sym 1 then eval yes env r.2 else eval no env r.2
  | .ifEq left right yes no, env, s =>
      (eval left env s).bind fun r =>
        (eval right env r.2).bind fun r' =>
          if same r.1 r'.1 then eval yes env r'.2 else eval no env r'.2
  | .lett name bound body, env, s =>
      (eval bound env s).bind fun r => eval body ((name, r.1) :: env) r.2
  | .add value, env, s =>
      (eval value env s).bind fun r => some (r.1, { r.2 with store := r.2.store ++ [r.1] })
  | .all, _, s => some (listVal s.store, s)
  | .assoc key, env, s =>
      (eval key env s).bind fun r => (findEntry r.1 r.2.store).map fun content => (content, r.2)
  | .quote code, _, s => some ((encode code).toVal, s)
  | .newSeal, _, s => some (.key s.nextBrand, { s with nextBrand := s.nextBrand + 1 })
  | .seal sealer value, env, s =>
      (eval sealer env s).bind fun r =>
        (eval value env r.2).bind fun r' =>
          match r.1 with
          | .key brand =>
              some (.box brand r'.2.nextBox r'.1, { r'.2 with nextBox := r'.2.nextBox + 1 })
          | _ => none
  | .unseal unsealer value, env, s =>
      (eval unsealer env s).bind fun r =>
        (eval value env r.2).bind fun r' =>
          match r.1, r'.1 with
          | .key brand, .box brand' _ content => if brand = brand' then some (content, r'.2) else none
          | _, _ => none

/-- The printed names `Seal` and `Sealed`. -/
def sealName : Nat := 3000
def sealedName : Nat := 3001

/-- What a program shows: a seal prints as `(Seal)` and a sealed value as
`(Sealed)`, without brand, identity or content.  Printing produces data, as
MeTTa prints text: a program without seals can print `(Sealed)` too, so the
observation alone does not tell the two languages apart. -/
def print : Val → Val
  | .sym name => .sym name
  | .num value => .num value
  | .nil => .nil
  | .cons head tail => .cons (print head) (print tail)
  | .key _ => .cons (.sym sealName) .nil
  | .box _ _ _ => .cons (.sym sealedName) .nil

/-- The observation of a program: what its result prints as, or no result. -/
def observe (program : Expr) : Option Val :=
  (eval program [] State.init).map fun r => print r.1

/-! ## Contexts -/

/-- Programs with holes; a hole may occur several times, or under `quote`. -/
inductive Ctx where
  | hole
  | var (name : Nat)
  | lit (datum : Datum)
  | cons (head tail : Ctx)
  | car (pair : Ctx)
  | cdr (pair : Ctx)
  | eq (left right : Ctx)
  | cond (test yes no : Ctx)
  | ifEq (left right yes no : Ctx)
  | lett (name : Nat) (bound body : Ctx)
  | add (value : Ctx)
  | all
  | assoc (key : Ctx)
  | quote (code : Ctx)
  | newSeal
  | seal (sealer value : Ctx)
  | unseal (unsealer value : Ctx)
  deriving DecidableEq, Repr

/-- Fill every hole. -/
def Ctx.plug : Ctx → Expr → Expr
  | .hole, e => e
  | .var name, _ => .var name
  | .lit datum, _ => .lit datum
  | .cons head tail, e => .cons (head.plug e) (tail.plug e)
  | .car pair, e => .car (pair.plug e)
  | .cdr pair, e => .cdr (pair.plug e)
  | .eq left right, e => .eq (left.plug e) (right.plug e)
  | .cond test yes no, e => .cond (test.plug e) (yes.plug e) (no.plug e)
  | .ifEq left right yes no, e => .ifEq (left.plug e) (right.plug e) (yes.plug e) (no.plug e)
  | .lett name bound body, e => .lett name (bound.plug e) (body.plug e)
  | .add value, e => .add (value.plug e)
  | .all, _ => .all
  | .assoc key, e => .assoc (key.plug e)
  | .quote code, e => .quote (code.plug e)
  | .newSeal, _ => .newSeal
  | .seal sealer value, e => .seal (sealer.plug e) (value.plug e)
  | .unseal unsealer value, e => .unseal (unsealer.plug e) (value.plug e)

/-! ## Fragments -/

/-- No `new-seal`, `seal` or `unseal`, also not inside quoted code. -/
def Expr.sealFree : Expr → Bool
  | .var _ | .lit _ | .all => true
  | .cons a b | .eq a b => a.sealFree && b.sealFree
  | .car a | .cdr a | .add a | .assoc a | .quote a => a.sealFree
  | .cond a b c => a.sealFree && b.sealFree && c.sealFree
  | .ifEq a b c d => a.sealFree && b.sealFree && c.sealFree && d.sealFree
  | .lett _ a b => a.sealFree && b.sealFree
  | .newSeal | .seal _ _ | .unseal _ _ => false

/-- No `quote`. -/
def Expr.quoteFree : Expr → Bool
  | .var _ | .lit _ | .all | .newSeal => true
  | .cons a b | .eq a b | .seal a b | .unseal a b => a.quoteFree && b.quoteFree
  | .car a | .cdr a | .add a | .assoc a => a.quoteFree
  | .cond a b c => a.quoteFree && b.quoteFree && c.quoteFree
  | .ifEq a b c d => a.quoteFree && b.quoteFree && c.quoteFree && d.quoteFree
  | .lett _ a b => a.quoteFree && b.quoteFree
  | .quote _ => false

/-- No `ifEq`. -/
def Expr.ifEqFree : Expr → Bool
  | .var _ | .lit _ | .all | .newSeal => true
  | .cons a b | .eq a b | .seal a b | .unseal a b => a.ifEqFree && b.ifEqFree
  | .car a | .cdr a | .add a | .assoc a | .quote a => a.ifEqFree
  | .cond a b c => a.ifEqFree && b.ifEqFree && c.ifEqFree
  | .ifEq _ _ _ _ => false
  | .lett _ a b => a.ifEqFree && b.ifEqFree

/-- No `new-seal`, `seal` or `unseal`. -/
def Ctx.sealFree : Ctx → Bool
  | .hole | .var _ | .lit _ | .all => true
  | .cons a b | .eq a b => a.sealFree && b.sealFree
  | .car a | .cdr a | .add a | .assoc a | .quote a => a.sealFree
  | .cond a b c => a.sealFree && b.sealFree && c.sealFree
  | .ifEq a b c d => a.sealFree && b.sealFree && c.sealFree && d.sealFree
  | .lett _ a b => a.sealFree && b.sealFree
  | .newSeal | .seal _ _ | .unseal _ _ => false

/-- No `quote`. -/
def Ctx.quoteFree : Ctx → Bool
  | .hole | .var _ | .lit _ | .all | .newSeal => true
  | .cons a b | .eq a b | .seal a b | .unseal a b => a.quoteFree && b.quoteFree
  | .car a | .cdr a | .add a | .assoc a => a.quoteFree
  | .cond a b c => a.quoteFree && b.quoteFree && c.quoteFree
  | .ifEq a b c d => a.quoteFree && b.quoteFree && c.quoteFree && d.quoteFree
  | .lett _ a b => a.quoteFree && b.quoteFree
  | .quote _ => false

/-- No `ifEq`. -/
def Ctx.ifEqFree : Ctx → Bool
  | .hole | .var _ | .lit _ | .all | .newSeal => true
  | .cons a b | .eq a b | .seal a b | .unseal a b => a.ifEqFree && b.ifEqFree
  | .car a | .cdr a | .add a | .assoc a | .quote a => a.ifEqFree
  | .cond a b c => a.ifEqFree && b.ifEqFree && c.ifEqFree
  | .ifEq _ _ _ _ => false
  | .lett _ a b => a.ifEqFree && b.ifEqFree

theorem Ctx.sealFree_plug {context : Ctx} {e : Expr} (hc : context.sealFree = true)
    (he : e.sealFree = true) : (context.plug e).sealFree = true := by
  induction context <;> simp_all [Ctx.sealFree, Ctx.plug, Expr.sealFree]

theorem Ctx.quoteFree_plug {context : Ctx} {e : Expr} (hc : context.quoteFree = true)
    (he : e.quoteFree = true) : (context.plug e).quoteFree = true := by
  induction context <;> simp_all [Ctx.quoteFree, Ctx.plug, Expr.quoteFree]

theorem Ctx.ifEqFree_plug {context : Ctx} {e : Expr} (hc : context.ifEqFree = true)
    (he : e.ifEqFree = true) : (context.plug e).ifEqFree = true := by
  induction context <;> simp_all [Ctx.ifEqFree, Ctx.plug, Expr.ifEqFree]

/-! ## The witnesses -/

/-- `(let $k (new-seal) (seal $k N))`: a sealed `N` whose seal nobody keeps. -/
def sealed (n : Int) : Expr := .lett 0 .newSeal (.seal (.var 0) (.lit (.num n)))

/-- `(let $k (new-seal) (let $b (seal $k N) (unseal $k $b)))`. -/
def opened (n : Int) : Expr :=
  .lett 0 .newSeal (.lett 1 (.seal (.var 0) (.lit (.num n))) (.unseal (.var 0) (.var 1)))

theorem observe_sealed (n : Int) : observe (sealed n) = some (.cons (.sym sealedName) .nil) := rfl

/-- A seal-free program shows the same: printing does not reveal a seal. -/
theorem observe_sealed_datum (n : Int) :
    observe (.lit (.cons (.sym sealedName) .nil)) = observe (sealed n) := rfl

theorem observe_opened (n : Int) : observe (opened n) = some (.num n) := rfl


/-! ## Noninterference: sealed values whose seal nobody keeps are indistinguishable

The relation `VRel secret` relates values that agree except for the contents
of sealed values whose brand is secret; a seal of a secret brand occurs in
neither.  Evaluation preserves it (`eval_rel`), the secret brands growing only
by brands created during the evaluation.  Printing hides contents
(`print_rel`), so related programs are observed alike. -/

/-- Every brand of a seal or sealed value in the value is below `bound`. -/
inductive Below (bound : Nat) : Val → Prop
  | sym (name : Nat) : Below bound (.sym name)
  | num (value : Int) : Below bound (.num value)
  | nil : Below bound .nil
  | cons {head tail : Val} : Below bound head → Below bound tail → Below bound (.cons head tail)
  | key {brand : Nat} : brand < bound → Below bound (.key brand)
  | box {brand identity : Nat} {content : Val} :
      brand < bound → Below bound content → Below bound (.box brand identity content)

theorem Below.mono {bound bound' : Nat} (le : bound ≤ bound') {v : Val} (h : Below bound v) :
    Below bound' v := by
  induction h with
  | sym name => exact .sym name
  | num value => exact .num value
  | nil => exact .nil
  | cons _ _ ihHead ihTail => exact .cons ihHead ihTail
  | key lt => exact .key (Nat.lt_of_lt_of_le lt le)
  | box lt _ ih => exact .box (Nat.lt_of_lt_of_le lt le) ih

theorem Datum.toVal_below (bound : Nat) : ∀ d : Datum, Below bound d.toVal
  | .sym name => .sym name
  | .num value => .num value
  | .nil => .nil
  | .cons head tail => .cons (Datum.toVal_below bound head) (Datum.toVal_below bound tail)

theorem below_truth (bound : Nat) (b : Bool) : Below bound (truth b) := by
  cases b <;> exact .sym _

theorem below_listVal {bound : Nat} : ∀ {values : List Val}, (∀ v ∈ values, Below bound v) →
    Below bound (listVal values)
  | [], _ => .nil
  | v :: rest, h => .cons (h v (by simp)) (below_listVal fun w hw => h w (by simp [hw]))

/-- Values that agree except for the contents of sealed values of a secret
brand, with no seal of a secret brand. -/
inductive VRel (secret : Nat → Prop) : Val → Val → Prop
  | sym (name : Nat) : VRel secret (.sym name) (.sym name)
  | num (value : Int) : VRel secret (.num value) (.num value)
  | nil : VRel secret .nil .nil
  | cons {a b c d : Val} : VRel secret a c → VRel secret b d → VRel secret (.cons a b) (.cons c d)
  | key {brand : Nat} : ¬ secret brand → VRel secret (.key brand) (.key brand)
  | box {brand identity : Nat} {c d : Val} :
      ¬ secret brand → VRel secret c d → VRel secret (.box brand identity c) (.box brand identity d)
  | secretBox {brand identity : Nat} (c d : Val) :
      secret brand → VRel secret (.box brand identity c) (.box brand identity d)

theorem VRel.datum (secret : Nat → Prop) : ∀ d : Datum, VRel secret d.toVal d.toVal
  | .sym name => .sym name
  | .num value => .num value
  | .nil => .nil
  | .cons head tail => .cons (VRel.datum secret head) (VRel.datum secret tail)

theorem VRel.truth (secret : Nat → Prop) (b : Bool) : VRel secret (truth b) (truth b) := by
  cases b <;> exact .sym _

/-- The secret brands grow from `secret` to `secret'`, and only by brands at
least `bound`. -/
def Grows (secret secret' : Nat → Prop) (bound : Nat) : Prop :=
  (∀ b, secret b → secret' b) ∧ ∀ b, secret' b → secret b ∨ bound ≤ b

theorem Grows.refl (secret : Nat → Prop) (bound : Nat) : Grows secret secret bound :=
  ⟨fun _ h => h, fun _ h => Or.inl h⟩

theorem Grows.trans {secret secret' secret'' : Nat → Prop} {bound bound' : Nat}
    (first : Grows secret secret' bound) (second : Grows secret' secret'' bound')
    (le : bound ≤ bound') : Grows secret secret'' bound :=
  ⟨fun b h => second.1 b (first.1 b h), fun b h =>
    (second.2 b h).elim (fun h' => first.2 b h') (fun h' => Or.inr (Nat.le_trans le h'))⟩

/-- Values whose brands are below `bound` stay related when the secret brands
grow by brands at least `bound`. -/
theorem VRel.extend {secret secret' : Nat → Prop} {bound : Nat} (grows : Grows secret secret' bound)
    {v w : Val} (rel : VRel secret v w) (below : Below bound v) : VRel secret' v w := by
  induction rel with
  | sym name => exact .sym name
  | num value => exact .num value
  | nil => exact .nil
  | cons _ _ ihHead ihTail =>
      cases below with
      | cons headBelow tailBelow => exact .cons (ihHead headBelow) (ihTail tailBelow)
  | @key brand notSecret =>
      cases below with
      | key lt =>
          exact .key fun isSecret =>
            (grows.2 brand isSecret).elim notSecret fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le lt le)
  | @box brand identity c d notSecret _ ih =>
      cases below with
      | box lt contentBelow =>
          exact .box (fun isSecret =>
            (grows.2 brand isSecret).elim notSecret fun le => Nat.lt_irrefl _ (Nat.lt_of_lt_of_le lt le))
            (ih contentBelow)
  | secretBox c d isSecret => exact .secretBox c d (grows.1 _ isSecret)

/-- Related values print alike: printing shows no content of a sealed value. -/
theorem print_rel {secret : Nat → Prop} {v w : Val} (rel : VRel secret v w) : print v = print w := by
  induction rel with
  | cons _ _ ihHead ihTail => simp [print, ihHead, ihTail]
  | _ => rfl

/-- `==` cannot tell related values apart. -/
theorem same_rel {secret : Nat → Prop} {a c : Val} (left : VRel secret a c) :
    ∀ {b d : Val}, VRel secret b d → same a b = same c d := by
  induction left with
  | sym name => intro b d right; cases right <;> rfl
  | num value => intro b d right; cases right <;> rfl
  | nil => intro b d right; cases right <;> rfl
  | cons _ _ ihHead ihTail =>
      intro b d right
      cases right with
      | cons rightHead rightTail => simp [same, ihHead rightHead, ihTail rightTail]
      | _ => rfl
  | key _ => intro b d right; cases right <;> rfl
  | box _ _ _ => intro b d right; cases right <;> rfl
  | secretBox _ _ _ => intro b d right; cases right <;> rfl

theorem VRel.eq_sym_one {secret : Nat → Prop} {v w : Val} (rel : VRel secret v w) :
    (v = .sym 1) ↔ (w = .sym 1) := by
  cases rel <;> simp

theorem VRel.listVal {secret : Nat → Prop} :
    ∀ {first second : List Val}, List.Forall₂ (VRel secret) first second →
      VRel secret (listVal first) (listVal second)
  | [], [], .nil => .nil
  | _ :: _, _ :: _, .cons head tail => .cons head (VRel.listVal tail)

/-- Related spaces answer a lookup with related contents. -/
theorem findEntry_rel {secret : Nat → Prop} {wanted wanted' : Val} (rel : VRel secret wanted wanted') :
    ∀ {store store' : List Val}, List.Forall₂ (VRel secret) store store' →
      (findEntry wanted store = none ∧ findEntry wanted' store' = none) ∨
        ∃ c d, findEntry wanted store = some c ∧ findEntry wanted' store' = some d ∧ VRel secret c d
  | [], [], .nil => Or.inl ⟨rfl, rfl⟩
  | _ :: _, _ :: _, .cons head tail => by
      cases head with
      | @cons entryKey content entryKey' content' keyRel contentRel =>
          have sameKey := same_rel keyRel rel
          simp only [findEntry, sameKey]
          split
          · exact Or.inr ⟨_, _, rfl, rfl, contentRel⟩
          · exact findEntry_rel rel tail
      | sym => simpa [findEntry] using findEntry_rel rel tail
      | num => simpa [findEntry] using findEntry_rel rel tail
      | nil => simpa [findEntry] using findEntry_rel rel tail
      | key => simpa [findEntry] using findEntry_rel rel tail
      | box => simpa [findEntry] using findEntry_rel rel tail
      | secretBox => simpa [findEntry] using findEntry_rel rel tail

theorem findEntry_below {bound : Nat} {wanted : Val} :
    ∀ {store : List Val} {c : Val}, (∀ v ∈ store, Below bound v) → findEntry wanted store = some c →
      Below bound c
  | [], _, _, found => by simp [findEntry] at found
  | entry :: rest, c, below, found => by
      cases entry with
      | cons entryKey content =>
          simp only [findEntry] at found
          split at found
          · cases found
            have entryBelow := below _ List.mem_cons_self
            cases entryBelow with
            | cons _ contentBelow => exact contentBelow
          · exact findEntry_below (fun v hv => below v (by simp [hv])) found
      | _ =>
          simp only [findEntry] at found
          exact findEntry_below (fun v hv => below v (by simp [hv])) found

/-- Related environments: the same names, related values. -/
def EnvRel (secret : Nat → Prop) (env env' : Env) : Prop :=
  List.Forall₂ (fun p q => p.1 = q.1 ∧ VRel secret p.2 q.2) env env'

/-- The values of an environment are below `bound`. -/
def EnvBelow (bound : Nat) (env : Env) : Prop := ∀ p ∈ env, Below bound p.2

theorem EnvBelow.mono {bound bound' : Nat} (le : bound ≤ bound') {env : Env} (h : EnvBelow bound env) :
    EnvBelow bound' env :=
  fun p hp => (h p hp).mono le

theorem EnvRel.extend {secret secret' : Nat → Prop} {bound : Nat} (grows : Grows secret secret' bound) :
    ∀ {env env' : Env}, EnvRel secret env env' → EnvBelow bound env → EnvRel secret' env env'
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons ⟨sameName, rel⟩ tail, below =>
      .cons ⟨sameName, rel.extend grows (below _ (by simp))⟩
        (EnvRel.extend grows tail fun p hp => below p (by simp [hp]))

theorem lookup_rel {secret : Nat → Prop} :
    ∀ {env env' : Env}, EnvRel secret env env' → ∀ name : Nat,
      (lookup env name = none ∧ lookup env' name = none) ∨
        ∃ v w, lookup env name = some v ∧ lookup env' name = some w ∧ VRel secret v w
  | [], [], .nil, _ => Or.inl ⟨rfl, rfl⟩
  | (n, v) :: _, (n', w) :: _, .cons ⟨sameName, rel⟩ tail, name => by
      simp only at sameName
      subst sameName
      simp only [lookup]
      split
      · exact Or.inr ⟨v, w, rfl, rfl, rel⟩
      · exact lookup_rel tail name

theorem lookup_below {bound : Nat} :
    ∀ {env : Env} {name : Nat} {v : Val}, EnvBelow bound env → lookup env name = some v → Below bound v
  | [], _, _, _, found => by simp [lookup] at found
  | (n, value) :: rest, name, v, below, found => by
      simp only [lookup] at found
      split at found
      · cases found
        exact below (n, value) (by simp)
      · exact lookup_below (fun p hp => below p (by simp [hp])) found

/-- Related states: related spaces, equal counters, every secret brand already
created, every stored brand below the next brand. -/
structure SRel (secret : Nat → Prop) (s t : State) : Prop where
  store : List.Forall₂ (VRel secret) s.store t.store
  brand : s.nextBrand = t.nextBrand
  box : s.nextBox = t.nextBox
  fresh : ∀ b, secret b → b < s.nextBrand
  below : ∀ v ∈ s.store, Below s.nextBrand v

/-- Related outcomes of two evaluations that started with brand counter
`bound`: both without result, or both with related values and states for
secret brands grown only by brands created meanwhile. -/
inductive ORel (secret : Nat → Prop) (bound : Nat) :
    Option (Val × State) → Option (Val × State) → Prop
  | none : ORel secret bound none none
  | some {v w : Val} {s t : State} (secret' : Nat → Prop) :
      Grows secret secret' bound → bound ≤ s.nextBrand → VRel secret' v w →
        Below s.nextBrand v → SRel secret' s t → ORel secret bound (some (v, s)) (some (w, t))

theorem ORel.ret {secret : Nat → Prop} {bound : Nat} {v w : Val} {s t : State}
    (le : bound ≤ s.nextBrand) (rel : VRel secret v w) (below : Below s.nextBrand v)
    (srel : SRel secret s t) : ORel secret bound (Option.some (v, s)) (Option.some (w, t)) :=
  .some secret (Grows.refl secret bound) le rel below srel

theorem ORel.weaken {secret secret' : Nat → Prop} {bound bound' : Nat} {r r' : Option (Val × State)}
    (rel : ORel secret' bound' r r') (grows : Grows secret secret' bound) (le : bound ≤ bound') :
    ORel secret bound r r' := by
  cases rel with
  | none => exact .none
  | some secret'' grows' le' vrel below srel =>
      exact .some secret'' (grows.trans grows' le) (Nat.le_trans le le') vrel below srel

/-- Sequencing: related first outcomes and related continuations give related
outcomes. -/
theorem ORel.bind {secret : Nat → Prop} {bound : Nat} {r r' : Option (Val × State)}
    (rel : ORel secret bound r r') {k k' : Val × State → Option (Val × State)}
    (cont : ∀ (secret' : Nat → Prop) (v w : Val) (s t : State), Grows secret secret' bound →
      bound ≤ s.nextBrand → VRel secret' v w → Below s.nextBrand v → SRel secret' s t →
        ORel secret' s.nextBrand (k (v, s)) (k' (w, t))) :
    ORel secret bound (r.bind k) (r'.bind k') := by
  cases rel with
  | none => exact .none
  | some secret' grows le vrel below srel =>
      exact (cont secret' _ _ _ _ grows le vrel below srel).weaken grows le

/-- Programs that agree except that some positions hold `sealed 1` on the left
and `sealed 2` on the right; quoted code agrees exactly. -/
inductive ERel : Expr → Expr → Prop
  | sealed : ERel (sealed 1) (sealed 2)
  | var (name : Nat) : ERel (.var name) (.var name)
  | lit (datum : Datum) : ERel (.lit datum) (.lit datum)
  | cons {a b c d : Expr} : ERel a c → ERel b d → ERel (.cons a b) (.cons c d)
  | car {a c : Expr} : ERel a c → ERel (.car a) (.car c)
  | cdr {a c : Expr} : ERel a c → ERel (.cdr a) (.cdr c)
  | eq {a b c d : Expr} : ERel a c → ERel b d → ERel (.eq a b) (.eq c d)
  | cond {a b c a' b' c' : Expr} : ERel a a' → ERel b b' → ERel c c' → ERel (.cond a b c) (.cond a' b' c')
  | ifEq {a b c d a' b' c' d' : Expr} : ERel a a' → ERel b b' → ERel c c' → ERel d d' →
      ERel (.ifEq a b c d) (.ifEq a' b' c' d')
  | lett (name : Nat) {a b c d : Expr} : ERel a c → ERel b d → ERel (.lett name a b) (.lett name c d)
  | add {a c : Expr} : ERel a c → ERel (.add a) (.add c)
  | all : ERel .all .all
  | assoc {a c : Expr} : ERel a c → ERel (.assoc a) (.assoc c)
  | quote (code : Expr) : ERel (.quote code) (.quote code)
  | newSeal : ERel .newSeal .newSeal
  | seal {a b c d : Expr} : ERel a c → ERel b d → ERel (.seal a b) (.seal c d)
  | unseal {a b c d : Expr} : ERel a c → ERel b d → ERel (.unseal a b) (.unseal c d)

theorem Ctx.plug_erel : ∀ context : Ctx, context.quoteFree = true →
    ERel (context.plug (sealed 1)) (context.plug (sealed 2))
  | .hole, _ => .sealed
  | .var name, _ => .var name
  | .lit datum, _ => .lit datum
  | .cons a b, h => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      exact .cons (Ctx.plug_erel a h.1) (Ctx.plug_erel b h.2)
  | .car a, h => .car (Ctx.plug_erel a h)
  | .cdr a, h => .cdr (Ctx.plug_erel a h)
  | .eq a b, h => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      exact .eq (Ctx.plug_erel a h.1) (Ctx.plug_erel b h.2)
  | .cond a b c, h => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      exact .cond (Ctx.plug_erel a h.1.1) (Ctx.plug_erel b h.1.2) (Ctx.plug_erel c h.2)
  | .ifEq a b c d, h => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      exact .ifEq (Ctx.plug_erel a h.1.1.1) (Ctx.plug_erel b h.1.1.2) (Ctx.plug_erel c h.1.2)
        (Ctx.plug_erel d h.2)
  | .lett name a b, h => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      exact .lett name (Ctx.plug_erel a h.1) (Ctx.plug_erel b h.2)
  | .add a, h => .add (Ctx.plug_erel a h)
  | .all, _ => .all
  | .assoc a, h => .assoc (Ctx.plug_erel a h)
  | .quote _, h => by simp [Ctx.quoteFree] at h
  | .newSeal, _ => .newSeal
  | .seal a b, h => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      exact .seal (Ctx.plug_erel a h.1) (Ctx.plug_erel b h.2)
  | .unseal a b, h => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      exact .unseal (Ctx.plug_erel a h.1) (Ctx.plug_erel b h.2)


theorem forall₂_extend {secret secret' : Nat → Prop} {bound : Nat} (grows : Grows secret secret' bound) :
    ∀ {first second : List Val}, List.Forall₂ (VRel secret) first second →
      (∀ v ∈ first, Below bound v) → List.Forall₂ (VRel secret') first second
  | [], [], .nil, _ => .nil
  | _ :: _, _ :: _, .cons head tail, below =>
      .cons (head.extend grows (below _ List.mem_cons_self))
        (forall₂_extend grows tail fun v hv => below v (List.mem_cons_of_mem _ hv))

theorem VRel.key_not_secret {secret : Nat → Prop} {brand brand' : Nat}
    (rel : VRel secret (.key brand) (.key brand')) : ¬ secret brand := by
  cases rel with
  | key notSecret => exact notSecret

/-- **Evaluation preserves the relation.** -/
theorem eval_rel {e e' : Expr} (rel : ERel e e') :
    ∀ (secret : Nat → Prop) (env env' : Env) (s t : State),
      EnvRel secret env env' → EnvBelow s.nextBrand env → SRel secret s t →
        ORel secret s.nextBrand (eval e env s) (eval e' env' t) := by
  induction rel with
  | sealed =>
      intro secret env env' s t _ _ srel
      have brand := srel.brand
      have box := srel.box
      show ORel secret s.nextBrand
        (Option.some (.box s.nextBrand s.nextBox (.num 1),
          { store := s.store, nextBrand := s.nextBrand + 1, nextBox := s.nextBox + 1 }))
        (Option.some (.box t.nextBrand t.nextBox (.num 2),
          { store := t.store, nextBrand := t.nextBrand + 1, nextBox := t.nextBox + 1 }))
      rw [← brand, ← box]
      have grows : Grows secret (fun b => secret b ∨ b = s.nextBrand) s.nextBrand :=
        ⟨fun _ h => Or.inl h, fun _ h => h.elim Or.inl fun equal => Or.inr (Nat.le_of_eq equal.symm)⟩
      refine .some (fun b => secret b ∨ b = s.nextBrand) grows (Nat.le_succ _)
        (.secretBox _ _ (Or.inr rfl)) (.box (Nat.lt_succ_self _) (.num 1)) ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact forall₂_extend grows srel.store srel.below
      · simp [brand]
      · simp [box]
      · intro b hb
        rcases hb with hb | hb
        · exact Nat.lt_succ_of_lt (srel.fresh b hb)
        · simp [hb]
      · intro v hv
        exact (srel.below v hv).mono (Nat.le_succ _)
  | var name =>
      intro secret env env' s t envRel envBelow srel
      rcases lookup_rel envRel name with ⟨first, second⟩ | ⟨v, w, first, second, vrel⟩
      · simp only [eval, first, second, Option.map_none]
        exact .none
      · simp only [eval, first, second, Option.map_some]
        exact .ret (Nat.le_refl _) vrel (lookup_below envBelow first) srel
  | lit datum =>
      intro secret env env' s t _ _ srel
      exact .ret (Nat.le_refl _) (VRel.datum _ datum) (Datum.toVal_below _ datum) srel
  | cons _ _ ihHead ihTail =>
      intro secret env env' s t envRel envBelow srel
      refine (ihHead secret env env' s t envRel envBelow srel).bind ?_
      intro secret₁ v w s₁ t₁ grows₁ le₁ vrel₁ below₁ srel₁
      refine (ihTail secret₁ env env' s₁ t₁ (envRel.extend grows₁ envBelow) (envBelow.mono le₁)
        srel₁).bind ?_
      intro secret₂ v' w' s₂ t₂ grows₂ le₂ vrel₂ below₂ srel₂
      exact .ret (Nat.le_refl _) (.cons (vrel₁.extend grows₂ below₁) vrel₂)
        (.cons (below₁.mono le₂) below₂) srel₂
  | car _ ih =>
      intro secret env env' s t envRel envBelow srel
      refine (ih secret env env' s t envRel envBelow srel).bind ?_
      intro secret₁ v w s₁ t₁ _ _ vrel₁ below₁ srel₁
      cases vrel₁ with
      | cons vrelHead _ =>
          cases below₁ with
          | cons belowHead _ => exact .ret (Nat.le_refl _) vrelHead belowHead srel₁
      | sym => exact .none
      | num => exact .none
      | nil => exact .none
      | key => exact .none
      | box => exact .none
      | secretBox => exact .none
  | cdr _ ih =>
      intro secret env env' s t envRel envBelow srel
      refine (ih secret env env' s t envRel envBelow srel).bind ?_
      intro secret₁ v w s₁ t₁ _ _ vrel₁ below₁ srel₁
      cases vrel₁ with
      | cons _ vrelTail =>
          cases below₁ with
          | cons _ belowTail => exact .ret (Nat.le_refl _) vrelTail belowTail srel₁
      | sym => exact .none
      | num => exact .none
      | nil => exact .none
      | key => exact .none
      | box => exact .none
      | secretBox => exact .none
  | eq _ _ ihLeft ihRight =>
      intro secret env env' s t envRel envBelow srel
      refine (ihLeft secret env env' s t envRel envBelow srel).bind ?_
      intro secret₁ v w s₁ t₁ grows₁ le₁ vrel₁ below₁ srel₁
      refine (ihRight secret₁ env env' s₁ t₁ (envRel.extend grows₁ envBelow) (envBelow.mono le₁)
        srel₁).bind ?_
      intro secret₂ v' w' s₂ t₂ grows₂ le₂ vrel₂ below₂ srel₂
      have sameValues : same v v' = same w w' := same_rel (vrel₁.extend grows₂ below₁) vrel₂
      show ORel secret₂ s₂.nextBrand (Option.some (truth (same v v'), s₂))
        (Option.some (truth (same w w'), t₂))
      rw [sameValues]
      exact .ret (Nat.le_refl _) (VRel.truth _ _) (below_truth _ _) srel₂
  | cond _ _ _ ihTest ihYes ihNo =>
      intro secret env env' s t envRel envBelow srel
      refine (ihTest secret env env' s t envRel envBelow srel).bind ?_
      intro secret₁ v w s₁ t₁ grows₁ le₁ vrel₁ _ srel₁
      show ORel secret₁ s₁.nextBrand (if v = .sym 1 then eval _ env s₁ else eval _ env s₁)
        (if w = .sym 1 then eval _ env' t₁ else eval _ env' t₁)
      by_cases isTrue : v = .sym 1
      · rw [if_pos isTrue, if_pos ((VRel.eq_sym_one vrel₁).mp isTrue)]
        exact ihYes secret₁ env env' s₁ t₁ (envRel.extend grows₁ envBelow) (envBelow.mono le₁) srel₁
      · rw [if_neg isTrue, if_neg fun h => isTrue ((VRel.eq_sym_one vrel₁).mpr h)]
        exact ihNo secret₁ env env' s₁ t₁ (envRel.extend grows₁ envBelow) (envBelow.mono le₁) srel₁
  | ifEq _ _ _ _ ihLeft ihRight ihYes ihNo =>
      intro secret env env' s t envRel envBelow srel
      refine (ihLeft secret env env' s t envRel envBelow srel).bind ?_
      intro secret₁ v w s₁ t₁ grows₁ le₁ vrel₁ below₁ srel₁
      refine (ihRight secret₁ env env' s₁ t₁ (envRel.extend grows₁ envBelow) (envBelow.mono le₁)
        srel₁).bind ?_
      intro secret₂ v' w' s₂ t₂ grows₂ le₂ vrel₂ _ srel₂
      have sameValues : same v v' = same w w' := same_rel (vrel₁.extend grows₂ below₁) vrel₂
      have envRel₂ := (envRel.extend grows₁ envBelow).extend grows₂ (envBelow.mono le₁)
      have envBelow₂ := envBelow.mono (Nat.le_trans le₁ le₂)
      show ORel secret₂ s₂.nextBrand (if same v v' then eval _ env s₂ else eval _ env s₂)
        (if same w w' then eval _ env' t₂ else eval _ env' t₂)
      rw [sameValues]
      split
      · exact ihYes secret₂ env env' s₂ t₂ envRel₂ envBelow₂ srel₂
      · exact ihNo secret₂ env env' s₂ t₂ envRel₂ envBelow₂ srel₂
  | lett name _ _ ihBound ihBody =>
      intro secret env env' s t envRel envBelow srel
      refine (ihBound secret env env' s t envRel envBelow srel).bind ?_
      intro secret₁ v w s₁ t₁ grows₁ le₁ vrel₁ below₁ srel₁
      refine ihBody secret₁ ((name, v) :: env) ((name, w) :: env') s₁ t₁
        (.cons ⟨rfl, vrel₁⟩ (envRel.extend grows₁ envBelow)) ?_ srel₁
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact below₁
      · exact envBelow.mono le₁ p hp
  | add _ ih =>
      intro secret env env' s t envRel envBelow srel
      refine (ih secret env env' s t envRel envBelow srel).bind ?_
      intro secret₁ v w s₁ t₁ _ _ vrel₁ below₁ srel₁
      refine .ret (Nat.le_refl _) vrel₁ below₁ ⟨?_, srel₁.brand, srel₁.box, srel₁.fresh, ?_⟩
      · exact List.rel_append srel₁.store (.cons vrel₁ .nil)
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact srel₁.below x hx
        · rw [List.mem_singleton.mp hx]
          exact below₁
  | all =>
      intro secret env env' s t _ _ srel
      exact .ret (Nat.le_refl _) (VRel.listVal srel.store) (below_listVal srel.below) srel
  | assoc _ ih =>
      intro secret env env' s t envRel envBelow srel
      refine (ih secret env env' s t envRel envBelow srel).bind ?_
      intro secret₁ v w s₁ t₁ _ _ vrel₁ _ srel₁
      show ORel secret₁ s₁.nextBrand ((findEntry v s₁.store).map fun c => (c, s₁))
        ((findEntry w t₁.store).map fun c => (c, t₁))
      rcases findEntry_rel vrel₁ srel₁.store with ⟨first, second⟩ | ⟨c, d, first, second, crel⟩
      · rw [first, second]
        exact .none
      · rw [first, second]
        exact .ret (Nat.le_refl _) crel (findEntry_below srel₁.below first) srel₁
  | quote code =>
      intro secret env env' s t _ _ srel
      exact .ret (Nat.le_refl _) (VRel.datum _ _) (Datum.toVal_below _ _) srel
  | newSeal =>
      intro secret env env' s t _ _ srel
      have brand := srel.brand
      show ORel secret s.nextBrand
        (Option.some (.key s.nextBrand, { s with nextBrand := s.nextBrand + 1 }))
        (Option.some (.key t.nextBrand, { t with nextBrand := t.nextBrand + 1 }))
      rw [← brand]
      refine .ret (Nat.le_succ _) (.key fun h => Nat.lt_irrefl _ (srel.fresh _ h))
        (.key (Nat.lt_succ_self _)) ⟨srel.store, by simp [brand], srel.box, ?_, ?_⟩
      · intro b hb
        exact Nat.lt_succ_of_lt (srel.fresh b hb)
      · intro v hv
        exact (srel.below v hv).mono (Nat.le_succ _)
  | «seal» _ _ ihSealer ihValue =>
      intro secret env env' s t envRel envBelow srel
      refine (ihSealer secret env env' s t envRel envBelow srel).bind ?_
      intro secret₁ v w s₁ t₁ grows₁ le₁ vrel₁ below₁ srel₁
      refine (ihValue secret₁ env env' s₁ t₁ (envRel.extend grows₁ envBelow) (envBelow.mono le₁)
        srel₁).bind ?_
      intro secret₂ v' w' s₂ t₂ grows₂ le₂ vrel₂ below₂ srel₂
      have vrel₁' := vrel₁.extend grows₂ below₁
      cases vrel₁' with
      | @key brand notSecret =>
          cases below₁ with
          | key lt =>
              show ORel secret₂ s₂.nextBrand
                (Option.some (.box brand s₂.nextBox v', { s₂ with nextBox := s₂.nextBox + 1 }))
                (Option.some (.box brand t₂.nextBox w', { t₂ with nextBox := t₂.nextBox + 1 }))
              rw [← srel₂.box]
              exact .ret (Nat.le_refl _) (.box notSecret vrel₂)
                (.box (Nat.lt_of_lt_of_le lt le₂) below₂)
                ⟨srel₂.store, srel₂.brand, by simp [srel₂.box], srel₂.fresh, srel₂.below⟩
      | sym => exact .none
      | num => exact .none
      | nil => exact .none
      | cons => exact .none
      | box => exact .none
      | secretBox => exact .none
  | «unseal» _ _ ihUnsealer ihValue =>
      intro secret env env' s t envRel envBelow srel
      refine (ihUnsealer secret env env' s t envRel envBelow srel).bind ?_
      intro secret₁ v w s₁ t₁ grows₁ le₁ vrel₁ below₁ srel₁
      refine (ihValue secret₁ env env' s₁ t₁ (envRel.extend grows₁ envBelow) (envBelow.mono le₁)
        srel₁).bind ?_
      intro secret₂ v' w' s₂ t₂ grows₂ le₂ vrel₂ below₂ srel₂
      have vrel₁' := vrel₁.extend grows₂ below₁
      cases vrel₁' with
      | @key brand notSecret =>
          cases vrel₂ with
          | @box brand' identity c d notSecret' contentRel =>
              cases below₂ with
              | box _ contentBelow =>
                  show ORel secret₂ s₂.nextBrand
                    (if brand = brand' then Option.some (c, s₂) else none)
                    (if brand = brand' then Option.some (d, t₂) else none)
                  split
                  · exact .ret (Nat.le_refl _) contentRel contentBelow srel₂
                  · exact .none
          | @secretBox brand' identity c d isSecret =>
              show ORel secret₂ s₂.nextBrand
                (if brand = brand' then Option.some (c, s₂) else none)
                (if brand = brand' then Option.some (d, t₂) else none)
              split
              · rename_i same
                subst same
                exact absurd isSecret notSecret
              · exact .none
          | sym => exact .none
          | num => exact .none
          | nil => exact .none
          | cons => exact .none
          | key => exact .none
      | sym => exact .none
      | num => exact .none
      | nil => exact .none
      | cons => exact .none
      | box => exact .none
      | secretBox => exact .none

/-- The initial states are related, with no secret brand. -/
theorem srel_init : SRel (fun _ => False) State.init State.init :=
  ⟨.nil, rfl, rfl, fun _ h => h.elim, fun _ h => by simp [State.init] at h⟩

/-- **No context tells the two sealed programs apart**, whatever it does with
seals of its own, as long as it does not quote the hole. -/
theorem observe_plug_sealed (context : Ctx) (noQuote : context.quoteFree = true) :
    observe (context.plug (sealed 1)) = observe (context.plug (sealed 2)) := by
  have rel := eval_rel (Ctx.plug_erel context noQuote) (fun _ => False) [] [] State.init State.init
    .nil (fun _ h => by simp at h) srel_init
  unfold observe
  generalize eval (context.plug (sealed 1)) [] State.init = first at rel
  generalize eval (context.plug (sealed 2)) [] State.init = second at rel
  cases rel with
  | none => rfl
  | some _ _ _ vrel _ _ => simp [print_rel vrel]


/-! ## The two languages -/

/-- The core with seals: programs and contexts without `quote`. -/
def withSeals : Language (Option Val) where
  Phrase := {e : Expr // e.quoteFree = true}
  Context := {c : Ctx // c.quoteFree = true}
  plug c e := ⟨c.1.plug e.1, Ctx.quoteFree_plug c.2 e.2⟩
  observe e := observe e.1

/-- The seal-free core: no `quote`, `new-seal`, `seal` or `unseal`. -/
def sealFreeCore : Language (Option Val) where
  Phrase := {e : Expr // e.quoteFree = true ∧ e.sealFree = true}
  Context := {c : Ctx // c.quoteFree = true ∧ c.sealFree = true}
  plug c e := ⟨c.1.plug e.1, Ctx.quoteFree_plug c.2.1 e.2.1, Ctx.sealFree_plug c.2.2 e.2.2⟩
  observe e := observe e.1

/-- Seals extend the seal-free core conservatively: the same programs behave
the same. -/
def sealExtension : Extension sealFreeCore withSeals where
  embed e := ⟨e.1, e.2.1⟩
  embedContext c := ⟨c.1, c.2.1⟩
  plug_embed _ _ := rfl
  observe_embed _ := rfl

/-- **Abstraction in the extension**: the two sealed programs are contextually
equivalent. -/
theorem sealed_equiv : withSeals.Equiv ⟨sealed 1, rfl⟩ ⟨sealed 2, rfl⟩ :=
  fun context => observe_plug_sealed context.1 context.2

/-- …while opening them shows `1` and `2`. -/
theorem opened_apart : observe (opened 1) ≠ observe (opened 2) := by
  rw [observe_opened, observe_opened]
  simp

/-! ## Transparency of the seal-free core -/

/-- Values without seals or sealed values. -/
inductive Plain : Val → Prop
  | sym (name : Nat) : Plain (.sym name)
  | num (value : Int) : Plain (.num value)
  | nil : Plain .nil
  | cons {head tail : Val} : Plain head → Plain tail → Plain (.cons head tail)

theorem print_plain {v : Val} (h : Plain v) : print v = v := by
  induction h with
  | cons _ _ ihHead ihTail => simp [print, ihHead, ihTail]
  | _ => rfl

theorem Datum.toVal_plain : ∀ d : Datum, Plain d.toVal
  | .sym name => .sym name
  | .num value => .num value
  | .nil => .nil
  | .cons head tail => .cons (Datum.toVal_plain head) (Datum.toVal_plain tail)

theorem plain_truth (b : Bool) : Plain (truth b) := by
  cases b <;> exact .sym _

theorem plain_listVal : ∀ {values : List Val}, (∀ v ∈ values, Plain v) → Plain (listVal values)
  | [], _ => .nil
  | v :: _, h => .cons (h v List.mem_cons_self)
      (plain_listVal fun w hw => h w (List.mem_cons_of_mem _ hw))

theorem listVal_injective : Function.Injective listVal := by
  intro first second equal
  induction first generalizing second with
  | nil => cases second with
    | nil => rfl
    | cons _ _ => simp [listVal] at equal
  | cons head tail ih => cases second with
    | nil => simp [listVal] at equal
    | cons head' tail' =>
        simp only [listVal, Val.cons.injEq] at equal
        rw [equal.1, ih equal.2]

theorem findEntry_plain {wanted : Val} :
    ∀ {store : List Val} {c : Val}, (∀ v ∈ store, Plain v) → findEntry wanted store = some c → Plain c
  | [], _, _, found => by simp [findEntry] at found
  | entry :: rest, c, plain, found => by
      cases entry with
      | cons entryKey content =>
          simp only [findEntry] at found
          split at found
          · cases found
            have entryPlain := plain _ List.mem_cons_self
            cases entryPlain with
            | cons _ contentPlain => exact contentPlain
          · exact findEntry_plain (fun v hv => plain v (List.mem_cons_of_mem _ hv)) found
      | _ =>
          simp only [findEntry] at found
          exact findEntry_plain (fun v hv => plain v (List.mem_cons_of_mem _ hv)) found

theorem lookup_plain : ∀ {env : Env} {name : Nat} {v : Val}, (∀ p ∈ env, Plain p.2) →
    lookup env name = some v → Plain v
  | [], _, _, _, found => by simp [lookup] at found
  | (n, value) :: _, name, v, plain, found => by
      simp only [lookup] at found
      split at found
      · cases found
        exact plain (n, value) List.mem_cons_self
      · exact lookup_plain (fun p hp => plain p (List.mem_cons_of_mem _ hp)) found

/-- A seal-free outcome from state `s`: no result, or a plain value and a plain
space with the counters of `s`. -/
inductive PlainOut (s : State) : Option (Val × State) → Prop
  | none : PlainOut s none
  | some {v : Val} {s' : State} : Plain v → (∀ x ∈ s'.store, Plain x) →
      s'.nextBrand = s.nextBrand → s'.nextBox = s.nextBox → PlainOut s (some (v, s'))

theorem PlainOut.bind {s : State} {r : Option (Val × State)} (out : PlainOut s r)
    {k : Val × State → Option (Val × State)}
    (cont : ∀ v s', Plain v → (∀ x ∈ s'.store, Plain x) → s'.nextBrand = s.nextBrand →
      s'.nextBox = s.nextBox → PlainOut s' (k (v, s'))) :
    PlainOut s (r.bind k) := by
  cases out with
  | none => exact .none
  | some plain store brand box =>
      have next := cont _ _ plain store brand box
      simp only [Option.bind_some]
      generalize k _ = result at next
      cases next with
      | none => exact .none
      | some plain' store' brand' box' =>
          exact .some plain' store' (brand'.trans brand) (box'.trans box)

/-- Seal-free programs compute plain values and leave the counters alone. -/
theorem eval_plain : ∀ (e : Expr), e.sealFree = true → ∀ (env : Env) (s : State),
    (∀ p ∈ env, Plain p.2) → (∀ x ∈ s.store, Plain x) → PlainOut s (eval e env s)
  | .var name, _, env, s, envPlain, storePlain => by
      cases found : lookup env name with
      | none => simp only [eval, found, Option.map_none]; exact .none
      | some v =>
          simp only [eval, found, Option.map_some]
          exact .some (lookup_plain envPlain found) storePlain rfl rfl
  | .lit datum, _, _, s, _, storePlain => .some (Datum.toVal_plain datum) storePlain rfl rfl
  | .cons a b, h, env, s, envPlain, storePlain => by
      simp only [Expr.sealFree, Bool.and_eq_true] at h
      refine (eval_plain a h.1 env s envPlain storePlain).bind ?_
      intro v s₁ plain₁ store₁ _ _
      refine (eval_plain b h.2 env s₁ envPlain store₁).bind ?_
      intro v' s₂ plain₂ store₂ _ _
      exact .some (.cons plain₁ plain₂) store₂ rfl rfl
  | .car a, h, env, s, envPlain, storePlain => by
      refine (eval_plain a h env s envPlain storePlain).bind ?_
      intro v s₁ plain₁ store₁ _ _
      cases plain₁ with
      | cons plainHead _ => exact .some plainHead store₁ rfl rfl
      | _ => exact .none
  | .cdr a, h, env, s, envPlain, storePlain => by
      refine (eval_plain a h env s envPlain storePlain).bind ?_
      intro v s₁ plain₁ store₁ _ _
      cases plain₁ with
      | cons _ plainTail => exact .some plainTail store₁ rfl rfl
      | _ => exact .none
  | .eq a b, h, env, s, envPlain, storePlain => by
      simp only [Expr.sealFree, Bool.and_eq_true] at h
      refine (eval_plain a h.1 env s envPlain storePlain).bind ?_
      intro v s₁ _ store₁ _ _
      refine (eval_plain b h.2 env s₁ envPlain store₁).bind ?_
      intro v' s₂ _ store₂ _ _
      exact .some (plain_truth _) store₂ rfl rfl
  | .cond a b c, h, env, s, envPlain, storePlain => by
      simp only [Expr.sealFree, Bool.and_eq_true] at h
      refine (eval_plain a h.1.1 env s envPlain storePlain).bind ?_
      intro v s₁ _ store₁ _ _
      show PlainOut s₁ (if v = .sym 1 then eval b env s₁ else eval c env s₁)
      split
      · exact eval_plain b h.1.2 env s₁ envPlain store₁
      · exact eval_plain c h.2 env s₁ envPlain store₁
  | .ifEq a b c d, h, env, s, envPlain, storePlain => by
      simp only [Expr.sealFree, Bool.and_eq_true] at h
      refine (eval_plain a h.1.1.1 env s envPlain storePlain).bind ?_
      intro v s₁ _ store₁ _ _
      refine (eval_plain b h.1.1.2 env s₁ envPlain store₁).bind ?_
      intro v' s₂ _ store₂ _ _
      show PlainOut s₂ (if same v v' then eval c env s₂ else eval d env s₂)
      split
      · exact eval_plain c h.1.2 env s₂ envPlain store₂
      · exact eval_plain d h.2 env s₂ envPlain store₂
  | .lett name a b, h, env, s, envPlain, storePlain => by
      simp only [Expr.sealFree, Bool.and_eq_true] at h
      refine (eval_plain a h.1 env s envPlain storePlain).bind ?_
      intro v s₁ plain₁ store₁ _ _
      refine eval_plain b h.2 ((name, v) :: env) s₁ ?_ store₁
      intro p hp
      rcases List.mem_cons.mp hp with rfl | hp
      · exact plain₁
      · exact envPlain p hp
  | .add a, h, env, s, envPlain, storePlain => by
      refine (eval_plain a h env s envPlain storePlain).bind ?_
      intro v s₁ plain₁ store₁ _ _
      refine .some plain₁ ?_ rfl rfl
      intro x hx
      rcases List.mem_append.mp hx with hx | hx
      · exact store₁ x hx
      · rw [List.mem_singleton.mp hx]
        exact plain₁
  | .all, _, _, s, _, storePlain => .some (plain_listVal storePlain) storePlain rfl rfl
  | .assoc a, h, env, s, envPlain, storePlain => by
      refine (eval_plain a h env s envPlain storePlain).bind ?_
      intro v s₁ _ store₁ _ _
      show PlainOut s₁ ((findEntry v s₁.store).map fun c => (c, s₁))
      cases found : findEntry v s₁.store with
      | none => exact .none
      | some c => exact .some (findEntry_plain store₁ found) store₁ rfl rfl
  | .quote code, _, _, s, _, storePlain => .some (Datum.toVal_plain _) storePlain rfl rfl
  | .newSeal, h, _, _, _, _ => by simp [Expr.sealFree] at h
  | .seal _ _, h, _, _, _, _ => by simp [Expr.sealFree] at h
  | .unseal _ _, h, _, _, _, _ => by simp [Expr.sealFree] at h

/-- `(let $r [·] ($r . (all)))`: read back the value of the hole and the whole
space. -/
def readout : Ctx := .lett 0 .hole (.cons (.var 0) .all)

theorem observe_readout (e : Expr) :
    observe (readout.plug e) =
      (eval e [] State.init).map fun r => print (.cons r.1 (listVal r.2.store)) := by
  unfold observe readout
  simp only [Ctx.plug, eval]
  cases eval e [] State.init <;> rfl

/-- **Transparency**: equivalent seal-free programs have the same outcome, value
and space. -/
theorem outcome_eq_of_equiv {p q : sealFreeCore.Phrase} (equivalent : sealFreeCore.Equiv p q) :
    eval p.1 [] State.init = eval q.1 [] State.init := by
  have observed := equivalent ⟨readout, rfl, rfl⟩
  change observe (readout.plug p.1) = observe (readout.plug q.1) at observed
  rw [observe_readout, observe_readout] at observed
  have plainP := eval_plain p.1 p.2.2 [] State.init (fun _ h => by simp at h) (fun _ h => by simp [State.init] at h)
  have plainQ := eval_plain q.1 q.2.2 [] State.init (fun _ h => by simp at h) (fun _ h => by simp [State.init] at h)
  generalize eval p.1 [] State.init = first at observed plainP ⊢
  generalize eval q.1 [] State.init = second at observed plainQ ⊢
  cases plainP with
  | none => cases plainQ with
    | none => rfl
    | some => simp at observed
  | @some v s' plain store brand box =>
    cases plainQ with
    | none => simp at observed
    | @some w t' plain' store' brand' box' =>
        simp only [Option.map_some, Option.some.injEq] at observed
        rw [print_plain (.cons plain (plain_listVal store)),
          print_plain (.cons plain' (plain_listVal store'))] at observed
        simp only [Val.cons.injEq] at observed
        have sameStore := listVal_injective observed.2
        have sameState : s' = t' := by
          cases s'
          cases t'
          simp only at sameStore brand box brand' box'
          simp [sameStore, brand, box, brand', box']
        rw [observed.1, sameState]

/-! ## No elimination -/

/-- A candidate translation of `new-seal`, `seal` and `unseal` into the
seal-free core (Felleisen's Definition 3.3, conditions E1 and E2): seal-free and
`quote`-free output, homomorphic in every construct of the core.  The
translation of the three new constructs is arbitrary, not necessarily a macro.
The library emulation is one (`emulateTranslation`). -/
structure SealTranslation where
  map : Expr → Expr
  quoteFree_map : ∀ e, e.quoteFree = true → (map e).quoteFree = true
  sealFree_map : ∀ e, e.quoteFree = true → (map e).sealFree = true
  map_var : ∀ name, map (.var name) = .var name
  map_lit : ∀ datum, map (.lit datum) = .lit datum
  map_cons : ∀ a b, map (.cons a b) = .cons (map a) (map b)
  map_car : ∀ a, map (.car a) = .car (map a)
  map_cdr : ∀ a, map (.cdr a) = .cdr (map a)
  map_eq : ∀ a b, map (.eq a b) = .eq (map a) (map b)
  map_cond : ∀ a b c, map (.cond a b c) = .cond (map a) (map b) (map c)
  map_ifEq : ∀ a b c d, map (.ifEq a b c d) = .ifEq (map a) (map b) (map c) (map d)
  map_lett : ∀ name a b, map (.lett name a b) = .lett name (map a) (map b)
  map_add : ∀ a, map (.add a) = .add (map a)
  map_all : map .all = .all
  map_assoc : ∀ a, map (.assoc a) = .assoc (map a)

/-- An elimination is a candidate translation that also preserves the
observation of every program (E3). -/
structure SealElimination extends SealTranslation where
  observe_map : ∀ e, e.quoteFree = true → observe (map e) = observe e

namespace SealElimination

variable (Φ : SealElimination)

/-- The translation is the identity on the seal-free core. -/
theorem map_id : ∀ e : Expr, e.quoteFree = true → e.sealFree = true → Φ.map e = e
  | .var name, _, _ => Φ.map_var name
  | .lit datum, _, _ => Φ.map_lit datum
  | .cons a b, hq, hs => by
      simp only [Expr.quoteFree, Expr.sealFree, Bool.and_eq_true] at hq hs
      rw [Φ.map_cons, map_id a hq.1 hs.1, map_id b hq.2 hs.2]
  | .car a, hq, hs => by rw [Φ.map_car, map_id a hq hs]
  | .cdr a, hq, hs => by rw [Φ.map_cdr, map_id a hq hs]
  | .eq a b, hq, hs => by
      simp only [Expr.quoteFree, Expr.sealFree, Bool.and_eq_true] at hq hs
      rw [Φ.map_eq, map_id a hq.1 hs.1, map_id b hq.2 hs.2]
  | .cond a b c, hq, hs => by
      simp only [Expr.quoteFree, Expr.sealFree, Bool.and_eq_true] at hq hs
      rw [Φ.map_cond, map_id a hq.1.1 hs.1.1, map_id b hq.1.2 hs.1.2, map_id c hq.2 hs.2]
  | .ifEq a b c d, hq, hs => by
      simp only [Expr.quoteFree, Expr.sealFree, Bool.and_eq_true] at hq hs
      rw [Φ.map_ifEq, map_id a hq.1.1.1 hs.1.1.1, map_id b hq.1.1.2 hs.1.1.2, map_id c hq.1.2 hs.1.2,
        map_id d hq.2 hs.2]
  | .lett name a b, hq, hs => by
      simp only [Expr.quoteFree, Expr.sealFree, Bool.and_eq_true] at hq hs
      rw [Φ.map_lett, map_id a hq.1 hs.1, map_id b hq.2 hs.2]
  | .add a, hq, hs => by rw [Φ.map_add, map_id a hq hs]
  | .all, _, _ => Φ.map_all
  | .assoc a, hq, hs => by rw [Φ.map_assoc, map_id a hq hs]
  | .quote _, hq, _ => by simp [Expr.quoteFree] at hq
  | .newSeal, _, hs => by simp [Expr.sealFree] at hs
  | .seal _ _, _, hs => by simp [Expr.sealFree] at hs
  | .unseal _ _, _, hs => by simp [Expr.sealFree] at hs

/-- The translation commutes with filling a context of the core. -/
theorem map_plug : ∀ (c : Ctx), c.quoteFree = true → c.sealFree = true → ∀ e : Expr,
    Φ.map (c.plug e) = c.plug (Φ.map e)
  | .hole, _, _, _ => rfl
  | .var name, _, _, _ => Φ.map_var name
  | .lit datum, _, _, _ => Φ.map_lit datum
  | .cons a b, hq, hs, e => by
      simp only [Ctx.quoteFree, Ctx.sealFree, Bool.and_eq_true] at hq hs
      simp only [Ctx.plug, Φ.map_cons, map_plug a hq.1 hs.1, map_plug b hq.2 hs.2]
  | .car a, hq, hs, e => by simp only [Ctx.plug, Φ.map_car, map_plug a hq hs]
  | .cdr a, hq, hs, e => by simp only [Ctx.plug, Φ.map_cdr, map_plug a hq hs]
  | .eq a b, hq, hs, e => by
      simp only [Ctx.quoteFree, Ctx.sealFree, Bool.and_eq_true] at hq hs
      simp only [Ctx.plug, Φ.map_eq, map_plug a hq.1 hs.1, map_plug b hq.2 hs.2]
  | .cond a b c, hq, hs, e => by
      simp only [Ctx.quoteFree, Ctx.sealFree, Bool.and_eq_true] at hq hs
      simp only [Ctx.plug, Φ.map_cond, map_plug a hq.1.1 hs.1.1, map_plug b hq.1.2 hs.1.2,
        map_plug c hq.2 hs.2]
  | .ifEq a b c d, hq, hs, e => by
      simp only [Ctx.quoteFree, Ctx.sealFree, Bool.and_eq_true] at hq hs
      simp only [Ctx.plug, Φ.map_ifEq, map_plug a hq.1.1.1 hs.1.1.1, map_plug b hq.1.1.2 hs.1.1.2,
        map_plug c hq.1.2 hs.1.2, map_plug d hq.2 hs.2]
  | .lett name a b, hq, hs, e => by
      simp only [Ctx.quoteFree, Ctx.sealFree, Bool.and_eq_true] at hq hs
      simp only [Ctx.plug, Φ.map_lett, map_plug a hq.1 hs.1, map_plug b hq.2 hs.2]
  | .add a, hq, hs, e => by simp only [Ctx.plug, Φ.map_add, map_plug a hq hs]
  | .all, _, _, _ => Φ.map_all
  | .assoc a, hq, hs, e => by simp only [Ctx.plug, Φ.map_assoc, map_plug a hq hs]
  | .quote _, hq, _, _ => by simp [Ctx.quoteFree] at hq
  | .newSeal, _, hs, _ => by simp [Ctx.sealFree] at hs
  | .seal _ _, _, hs, _ => by simp [Ctx.sealFree] at hs
  | .unseal _ _, _, hs, _ => by simp [Ctx.sealFree] at hs

/-- A seal elimination is an elimination in the general sense. -/
def toElimination : Elimination sealExtension where
  map e := ⟨Φ.map e.1, Φ.quoteFree_map e.1 e.2, Φ.sealFree_map e.1 e.2⟩
  map_embed p := Subtype.ext (Φ.map_id p.1 p.2.1 p.2.2)
  map_plug_embed c e := Subtype.ext (Φ.map_plug c.1 c.2.1 c.2.2 e.1)
  observe_map e := Φ.observe_map e.1 e.2

end SealElimination

/-- **Sealing is not eliminable from the seal-free core**: no translation that is
homomorphic in the constructs of the core preserves the observation of every
program.  A fortiori seals are not macro-expressible. -/
theorem isEmpty_sealElimination : IsEmpty SealElimination := by
  refine ⟨fun Φ => ?_⟩
  have outcomes := outcome_eq_of_equiv (Φ.toElimination.equiv_map sealed_equiv)
  change eval (Φ.map (sealed 1)) [] State.init = eval (Φ.map (sealed 2)) [] State.init at outcomes
  have first := Φ.observe_map (opened 1) rfl
  have second := Φ.observe_map (opened 2) rfl
  rw [observe_opened] at first second
  simp only [sealed, opened, Φ.map_lett] at outcomes first second
  unfold observe at first second
  simp only [eval] at outcomes first second
  cases key : eval (Φ.map .newSeal) [] State.init with
  | none => simp [key] at first
  | some r =>
      simp only [key, Option.bind_some] at outcomes first second
      rw [outcomes] at first
      rw [first] at second
      simp at second


/-! ## Control: a library emulation, and the leaks that defeat it

The emulation follows the seal proposal's library: a capability is the datum
`(cap . SNAPSHOT)`; `seal` writes a registry entry `((entry KEY . N) . VALUE)`
into the space and returns the ticket `(ticket . N)`; `unseal` looks the entry
up.  `SNAPSHOT` and `N` are copies of the space at the time, distinct because
the space grows.  The translation is homomorphic in the core and seal-free, so
by `isEmpty_sealElimination` it fails somewhere; each leak pinned by the seal
examples and by the equation kernel's leak suite is one concrete failure. -/

/-- `cap`, `entry`, `ticket` and the mark that makes the space grow. -/
def capTag : Datum := .sym 2001
def entryTag : Datum := .sym 2002
def ticketTag : Datum := .sym 2003
def brandMark : Datum := .sym 2004

/-- The library emulation of seals, as a translation into the core. -/
def emulate : Expr → Expr
  | .var name => .var name
  | .lit datum => .lit datum
  | .cons a b => .cons (emulate a) (emulate b)
  | .car a => .car (emulate a)
  | .cdr a => .cdr (emulate a)
  | .eq a b => .eq (emulate a) (emulate b)
  | .cond a b c => .cond (emulate a) (emulate b) (emulate c)
  | .ifEq a b c d => .ifEq (emulate a) (emulate b) (emulate c) (emulate d)
  | .lett name a b => .lett name (emulate a) (emulate b)
  | .add a => .add (emulate a)
  | .all => .all
  | .assoc a => .assoc (emulate a)
  | .quote code => .quote code
  | .newSeal =>
      .lett 1000 .all (.lett 1001 (.add (.lit brandMark)) (.cons (.lit capTag) (.var 1000)))
  | .seal sealer value =>
      .lett 1002 (emulate sealer) (.lett 1003 (emulate value) (.lett 1004 .all
        (.lett 1005 (.add (.cons (.cons (.lit entryTag) (.cons (.var 1002) (.var 1004))) (.var 1003)))
          (.cons (.lit ticketTag) (.var 1004)))))
  | .unseal unsealer value =>
      .lett 1002 (emulate unsealer) (.lett 1003 (emulate value)
        (.assoc (.cons (.lit entryTag) (.cons (.var 1002) (.cdr (.var 1003))))))

/-- On programs without `quote`, the emulation writes neither `quote` nor a seal
construct (condition E1). -/
theorem emulate_free : ∀ e : Expr, e.quoteFree = true →
    (emulate e).quoteFree = true ∧ (emulate e).sealFree = true
  | .var _, _ | .lit _, _ | .all, _ | .newSeal, _ => ⟨rfl, rfl⟩
  | .cons a b, h | .eq a b, h | .seal a b, h | .unseal a b, h => by
      simp only [Expr.quoteFree, Bool.and_eq_true] at h
      have ha := emulate_free a h.1
      have hb := emulate_free b h.2
      simp_all [emulate, Expr.quoteFree, Expr.sealFree]
  | .car a, h | .cdr a, h | .add a, h | .assoc a, h => by
      have ha := emulate_free a h
      simp_all [emulate, Expr.quoteFree, Expr.sealFree]
  | .cond a b c, h => by
      simp only [Expr.quoteFree, Bool.and_eq_true] at h
      have ha := emulate_free a h.1.1
      have hb := emulate_free b h.1.2
      have hc := emulate_free c h.2
      simp_all [emulate, Expr.quoteFree, Expr.sealFree]
  | .ifEq a b c d, h => by
      simp only [Expr.quoteFree, Bool.and_eq_true] at h
      have ha := emulate_free a h.1.1.1
      have hb := emulate_free b h.1.1.2
      have hc := emulate_free c h.1.2
      have hd := emulate_free d h.2
      simp_all [emulate, Expr.quoteFree, Expr.sealFree]
  | .lett _ a b, h => by
      simp only [Expr.quoteFree, Bool.and_eq_true] at h
      have ha := emulate_free a h.1
      have hb := emulate_free b h.2
      simp_all [emulate, Expr.quoteFree, Expr.sealFree]
  | .quote _, h => by simp [Expr.quoteFree] at h

/-- **The emulation is a candidate**: it satisfies E1 and E2, so what no
candidate satisfies is E3. -/
def emulateTranslation : SealTranslation where
  map := emulate
  quoteFree_map e h := (emulate_free e h).1
  sealFree_map e h := (emulate_free e h).2
  map_var _ := rfl
  map_lit _ := rfl
  map_cons _ _ := rfl
  map_car _ := rfl
  map_cdr _ := rfl
  map_eq _ _ := rfl
  map_cond _ _ _ := rfl
  map_ifEq _ _ _ _ := rfl
  map_lett _ _ _ := rfl
  map_add _ := rfl
  map_all := rfl
  map_assoc _ := rfl

/-- The registry probe: `(let $_ [·] (all))`, a seal-free context. -/
def readRegistry : Ctx := .lett 9 .hole .all

/-- **Registry read.** The two sealed programs are equivalent with seals, and
the probe sees the same; their emulations are told apart by reading the
registry, so the emulation does not preserve equivalence. -/
theorem leak_registry_read :
    observe (readRegistry.plug (sealed 1)) = observe (readRegistry.plug (sealed 2)) ∧
      observe (readRegistry.plug (emulate (sealed 1))) ≠
        observe (readRegistry.plug (emulate (sealed 2))) :=
  ⟨observe_plug_sealed readRegistry rfl, by decide⟩

/-- `(let $b (sealed 1) (car $b))`: take a sealed value apart. -/
def takeApart : Expr := .lett 0 (sealed 1) (.car (.var 0))

/-- **A ticket is an expression.** A sealed value has no structure; an emulated
ticket does. -/
theorem leak_ticket_structure :
    observe takeApart = none ∧ observe (emulate takeApart) = some (.sym 2003) :=
  ⟨rfl, rfl⟩

/-- A registry entry for the first capability, `(cap)`, written as data. -/
def forgedEntry : Datum :=
  .cons (.cons entryTag (.cons (.cons capTag .nil) (.num 7))) (.num 42)

/-- `(let $k (new-seal) (let $_ (add FORGED-ENTRY) (unseal $k (ticket . 7))))`. -/
def writeRegistry : Expr :=
  .lett 0 .newSeal
    (.lett 1 (.add (.lit forgedEntry)) (.unseal (.var 0) (.lit (.cons ticketTag (.num 7)))))

/-- **Registry write.** Writing an entry forges a sealed value. -/
theorem leak_registry_write :
    observe writeRegistry = none ∧ observe (emulate writeRegistry) = some (.num 42) :=
  ⟨rfl, rfl⟩

/-- `(let $b (let $k (new-seal) (seal $k 5)) (unseal (cap) $b))`: open with a
written capability. -/
def writeCapability : Expr :=
  .lett 0 (.lett 1 .newSeal (.seal (.var 1) (.lit (.num 5))))
    (.unseal (.lit (.cons capTag .nil)) (.var 0))

/-- **A capability is data.** Writing one opens a sealed value. -/
theorem leak_capability_data :
    observe writeCapability = none ∧ observe (emulate writeCapability) = some (.num 5) :=
  ⟨rfl, rfl⟩

/-! ## Control: syntactic sugar is a macro elimination -/

/-- `ifEq` as `cond` over `eq`; homomorphic elsewhere. -/
def desugar : Expr → Expr
  | .var name => .var name
  | .lit datum => .lit datum
  | .cons a b => .cons (desugar a) (desugar b)
  | .car a => .car (desugar a)
  | .cdr a => .cdr (desugar a)
  | .eq a b => .eq (desugar a) (desugar b)
  | .cond a b c => .cond (desugar a) (desugar b) (desugar c)
  | .ifEq a b c d => .cond (.eq (desugar a) (desugar b)) (desugar c) (desugar d)
  | .lett name a b => .lett name (desugar a) (desugar b)
  | .add a => .add (desugar a)
  | .all => .all
  | .assoc a => .assoc (desugar a)
  | .quote code => .quote code
  | .newSeal => .newSeal
  | .seal a b => .seal (desugar a) (desugar b)
  | .unseal a b => .unseal (desugar a) (desugar b)

/-- The same on contexts. -/
def desugarCtx : Ctx → Ctx
  | .hole => .hole
  | .var name => .var name
  | .lit datum => .lit datum
  | .cons a b => .cons (desugarCtx a) (desugarCtx b)
  | .car a => .car (desugarCtx a)
  | .cdr a => .cdr (desugarCtx a)
  | .eq a b => .eq (desugarCtx a) (desugarCtx b)
  | .cond a b c => .cond (desugarCtx a) (desugarCtx b) (desugarCtx c)
  | .ifEq a b c d => .cond (.eq (desugarCtx a) (desugarCtx b)) (desugarCtx c) (desugarCtx d)
  | .lett name a b => .lett name (desugarCtx a) (desugarCtx b)
  | .add a => .add (desugarCtx a)
  | .all => .all
  | .assoc a => .assoc (desugarCtx a)
  | .quote code => .quote code
  | .newSeal => .newSeal
  | .seal a b => .seal (desugarCtx a) (desugarCtx b)
  | .unseal a b => .unseal (desugarCtx a) (desugarCtx b)

/-- The translation computes what the sugar computes. -/
theorem eval_desugar : ∀ (e : Expr) (env : Env) (s : State), eval (desugar e) env s = eval e env s
  | .var _, _, _ | .lit _, _, _ | .all, _, _ | .quote _, _, _ | .newSeal, _, _ => rfl
  | .cons a b, env, s => by
      simp only [desugar, eval, eval_desugar a]
      congr 1
      funext r
      rw [eval_desugar b]
  | .car a, env, s => by simp only [desugar, eval, eval_desugar a]
  | .cdr a, env, s => by simp only [desugar, eval, eval_desugar a]
  | .eq a b, env, s => by
      simp only [desugar, eval, eval_desugar a]
      congr 1
      funext r
      rw [eval_desugar b]
  | .cond a b c, env, s => by
      simp only [desugar, eval, eval_desugar a]
      congr 1
      funext r
      rw [eval_desugar b, eval_desugar c]
  | .ifEq a b c d, env, s => by
      simp only [desugar, eval, eval_desugar a, Option.bind_assoc, Option.bind_some]
      congr 1
      funext r
      rw [eval_desugar b]
      congr 1
      funext r'
      rw [eval_desugar c, eval_desugar d]
      cases same r.1 r'.1 <;> simp [truth]
  | .lett name a b, env, s => by
      simp only [desugar, eval, eval_desugar a]
      congr 1
      funext r
      exact eval_desugar b _ _
  | .add a, env, s => by simp only [desugar, eval, eval_desugar a]
  | .assoc a, env, s => by simp only [desugar, eval, eval_desugar a]
  | .seal a b, env, s => by
      simp only [desugar, eval, eval_desugar a]
      congr 1
      funext r
      rw [eval_desugar b]
  | .unseal a b, env, s => by
      simp only [desugar, eval, eval_desugar a]
      congr 1
      funext r
      rw [eval_desugar b]

theorem desugar_id : ∀ e : Expr, e.ifEqFree = true → desugar e = e
  | .var _, _ | .lit _, _ | .all, _ | .quote _, _ | .newSeal, _ => rfl
  | .cons a b, h | .eq a b, h | .seal a b, h | .unseal a b, h => by
      simp only [Expr.ifEqFree, Bool.and_eq_true] at h
      simp [desugar, desugar_id a h.1, desugar_id b h.2]
  | .car a, h | .cdr a, h | .add a, h | .assoc a, h => by
      simp [desugar, desugar_id a h]
  | .cond a b c, h => by
      simp only [Expr.ifEqFree, Bool.and_eq_true] at h
      simp [desugar, desugar_id a h.1.1, desugar_id b h.1.2, desugar_id c h.2]
  | .ifEq _ _ _ _, h => by simp [Expr.ifEqFree] at h
  | .lett _ a b, h => by
      simp only [Expr.ifEqFree, Bool.and_eq_true] at h
      simp [desugar, desugar_id a h.1, desugar_id b h.2]

theorem desugarCtx_id : ∀ c : Ctx, c.ifEqFree = true → desugarCtx c = c
  | .hole, _ | .var _, _ | .lit _, _ | .all, _ | .quote _, _ | .newSeal, _ => rfl
  | .cons a b, h | .eq a b, h | .seal a b, h | .unseal a b, h => by
      simp only [Ctx.ifEqFree, Bool.and_eq_true] at h
      simp [desugarCtx, desugarCtx_id a h.1, desugarCtx_id b h.2]
  | .car a, h | .cdr a, h | .add a, h | .assoc a, h => by
      simp [desugarCtx, desugarCtx_id a h]
  | .cond a b c, h => by
      simp only [Ctx.ifEqFree, Bool.and_eq_true] at h
      simp [desugarCtx, desugarCtx_id a h.1.1, desugarCtx_id b h.1.2, desugarCtx_id c h.2]
  | .ifEq _ _ _ _, h => by simp [Ctx.ifEqFree] at h
  | .lett _ a b, h => by
      simp only [Ctx.ifEqFree, Bool.and_eq_true] at h
      simp [desugarCtx, desugarCtx_id a h.1, desugarCtx_id b h.2]

/-- The Translation Lemma for the sugar, on contexts that do not quote. -/
theorem desugar_plug : ∀ c : Ctx, c.quoteFree = true → ∀ e : Expr,
    desugar (c.plug e) = (desugarCtx c).plug (desugar e)
  | .hole, _, _ | .var _, _, _ | .lit _, _, _ | .all, _, _ | .newSeal, _, _ => rfl
  | .cons a b, h, e | .eq a b, h, e | .seal a b, h, e | .unseal a b, h, e => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      simp [Ctx.plug, desugar, desugarCtx, desugar_plug a h.1 e, desugar_plug b h.2 e]
  | .car a, h, e | .cdr a, h, e | .add a, h, e | .assoc a, h, e => by
      simp [Ctx.plug, desugar, desugarCtx, desugar_plug a h e]
  | .cond a b c, h, e => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      simp [Ctx.plug, desugar, desugarCtx, desugar_plug a h.1.1 e, desugar_plug b h.1.2 e,
        desugar_plug c h.2 e]
  | .ifEq a b c d, h, e => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      simp [Ctx.plug, desugar, desugarCtx, desugar_plug a h.1.1.1 e, desugar_plug b h.1.1.2 e,
        desugar_plug c h.1.2 e, desugar_plug d h.2 e]
  | .lett _ a b, h, e => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      simp [Ctx.plug, desugar, desugarCtx, desugar_plug a h.1 e, desugar_plug b h.2 e]
  | .quote _, h, _ => by simp [Ctx.quoteFree] at h

theorem desugar_quoteFree : ∀ e : Expr, e.quoteFree = true → (desugar e).quoteFree = true
  | .var _, _ | .lit _, _ | .all, _ | .newSeal, _ => rfl
  | .cons a b, h | .eq a b, h | .seal a b, h | .unseal a b, h => by
      simp only [Expr.quoteFree, Bool.and_eq_true] at h
      simp [desugar, Expr.quoteFree, desugar_quoteFree a h.1, desugar_quoteFree b h.2]
  | .car a, h | .cdr a, h | .add a, h | .assoc a, h => by
      simp [desugar, Expr.quoteFree, desugar_quoteFree a h]
  | .cond a b c, h => by
      simp only [Expr.quoteFree, Bool.and_eq_true] at h
      simp [desugar, Expr.quoteFree, desugar_quoteFree a h.1.1, desugar_quoteFree b h.1.2,
        desugar_quoteFree c h.2]
  | .ifEq a b c d, h => by
      simp only [Expr.quoteFree, Bool.and_eq_true] at h
      simp [desugar, Expr.quoteFree, desugar_quoteFree a h.1.1.1, desugar_quoteFree b h.1.1.2,
        desugar_quoteFree c h.1.2, desugar_quoteFree d h.2]
  | .lett _ a b, h => by
      simp only [Expr.quoteFree, Bool.and_eq_true] at h
      simp [desugar, Expr.quoteFree, desugar_quoteFree a h.1, desugar_quoteFree b h.2]
  | .quote _, h => by simp [Expr.quoteFree] at h

theorem desugar_ifEqFree : ∀ e : Expr, e.quoteFree = true → (desugar e).ifEqFree = true
  | .var _, _ | .lit _, _ | .all, _ | .newSeal, _ => rfl
  | .cons a b, h | .eq a b, h | .seal a b, h | .unseal a b, h => by
      simp only [Expr.quoteFree, Bool.and_eq_true] at h
      simp [desugar, Expr.ifEqFree, desugar_ifEqFree a h.1, desugar_ifEqFree b h.2]
  | .car a, h | .cdr a, h | .add a, h | .assoc a, h => by
      simp [desugar, Expr.ifEqFree, desugar_ifEqFree a h]
  | .cond a b c, h => by
      simp only [Expr.quoteFree, Bool.and_eq_true] at h
      simp [desugar, Expr.ifEqFree, desugar_ifEqFree a h.1.1, desugar_ifEqFree b h.1.2,
        desugar_ifEqFree c h.2]
  | .ifEq a b c d, h => by
      simp only [Expr.quoteFree, Bool.and_eq_true] at h
      simp [desugar, Expr.ifEqFree, desugar_ifEqFree a h.1.1.1, desugar_ifEqFree b h.1.1.2,
        desugar_ifEqFree c h.1.2, desugar_ifEqFree d h.2]
  | .lett _ a b, h => by
      simp only [Expr.quoteFree, Bool.and_eq_true] at h
      simp [desugar, Expr.ifEqFree, desugar_ifEqFree a h.1, desugar_ifEqFree b h.2]
  | .quote _, h => by simp [Expr.quoteFree] at h

theorem desugarCtx_free : ∀ c : Ctx, c.quoteFree = true →
    (desugarCtx c).quoteFree = true ∧ (desugarCtx c).ifEqFree = true
  | .hole, _ | .var _, _ | .lit _, _ | .all, _ | .newSeal, _ => ⟨rfl, rfl⟩
  | .cons a b, h | .eq a b, h | .seal a b, h | .unseal a b, h => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      have ha := desugarCtx_free a h.1
      have hb := desugarCtx_free b h.2
      simp_all [desugarCtx, Ctx.quoteFree, Ctx.ifEqFree]
  | .car a, h | .cdr a, h | .add a, h | .assoc a, h => by
      have ha := desugarCtx_free a h
      simp_all [desugarCtx, Ctx.quoteFree, Ctx.ifEqFree]
  | .cond a b c, h => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      have ha := desugarCtx_free a h.1.1
      have hb := desugarCtx_free b h.1.2
      have hc := desugarCtx_free c h.2
      simp_all [desugarCtx, Ctx.quoteFree, Ctx.ifEqFree]
  | .ifEq a b c d, h => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      have ha := desugarCtx_free a h.1.1.1
      have hb := desugarCtx_free b h.1.1.2
      have hc := desugarCtx_free c h.1.2
      have hd := desugarCtx_free d h.2
      simp_all [desugarCtx, Ctx.quoteFree, Ctx.ifEqFree]
  | .lett _ a b, h => by
      simp only [Ctx.quoteFree, Bool.and_eq_true] at h
      have ha := desugarCtx_free a h.1
      have hb := desugarCtx_free b h.2
      simp_all [desugarCtx, Ctx.quoteFree, Ctx.ifEqFree]
  | .quote _, h => by simp [Ctx.quoteFree] at h

/-- The language without `ifEq` (and without `quote`). -/
def sugarFree : Language (Option Val) where
  Phrase := {e : Expr // e.quoteFree = true ∧ e.ifEqFree = true}
  Context := {c : Ctx // c.quoteFree = true ∧ c.ifEqFree = true}
  plug c e := ⟨c.1.plug e.1, Ctx.quoteFree_plug c.2.1 e.2.1, Ctx.ifEqFree_plug c.2.2 e.2.2⟩
  observe e := observe e.1

/-- `ifEq` extends it conservatively. -/
def sugarExtension : Extension sugarFree withSeals where
  embed e := ⟨e.1, e.2.1⟩
  embedContext c := ⟨c.1, c.2.1⟩
  plug_embed _ _ := rfl
  observe_embed _ := rfl

/-- **Positive control**: `ifEq` is a macro elimination. -/
def desugarElimination : MacroElimination sugarExtension where
  map e := ⟨desugar e.1, desugar_quoteFree e.1 e.2, desugar_ifEqFree e.1 e.2⟩
  map_embed p := Subtype.ext (desugar_id p.1 p.2.2)
  map_plug_embed c e := Subtype.ext (by
    show desugar (c.1.plug e.1) = c.1.plug (desugar e.1)
    rw [desugar_plug c.1 c.2.1, desugarCtx_id c.1 c.2.2])
  observe_map e := by
    show observe (desugar e.1) = observe e.1
    unfold observe
    rw [eval_desugar]
  mapContext c := ⟨desugarCtx c.1, desugarCtx_free c.1 c.2⟩
  map_plug c e := Subtype.ext (desugar_plug c.1 c.2 e.1)

/-- Felleisen's Theorem 3.14(i) for the sugar: adding `ifEq` neither breaks nor
creates an equivalence. -/
theorem sugar_conservative (p q : sugarFree.Phrase) :
    withSeals.Equiv (sugarExtension.embed p) (sugarExtension.embed q) ↔ sugarFree.Equiv p q :=
  desugarElimination.embed_equiv_iff p q


/-! ## Control: reflection on program text trivialises equivalence

With `quote`, the context `(quote [·])` reads its hole back.  Contextual
equivalence is then equality of programs, the two sealed programs are told
apart, and no construct at all is eliminable, not even `ifEq`. -/

theorem Datum.toVal_injective : Function.Injective Datum.toVal := by
  intro first
  induction first with
  | sym name => intro second h; cases second <;> simp_all [Datum.toVal]
  | num value => intro second h; cases second <;> simp_all [Datum.toVal]
  | nil => intro second h; cases second <;> simp_all [Datum.toVal]
  | cons head tail ihHead ihTail =>
      intro second h
      cases second with
      | cons head' tail' =>
          simp only [Datum.toVal, Val.cons.injEq] at h
          rw [ihHead h.1, ihTail h.2]
      | _ => simp [Datum.toVal] at h

theorem encode_injective : Function.Injective encode := by
  intro first
  induction first with
  | var name =>
      intro second h
      cases second <;> simp [encode] at h
      rw [Int.ofNat_inj.mp h]
  | lit datum => intro second h; cases second <;> simp_all [encode]
  | cons a b iha ihb =>
      intro second h
      cases second <;> simp [encode] at h
      rw [iha h.1, ihb h.2]
  | car a ih => intro second h; cases second <;> simp [encode] at h; rw [ih h]
  | cdr a ih => intro second h; cases second <;> simp [encode] at h; rw [ih h]
  | eq a b iha ihb =>
      intro second h
      cases second <;> simp [encode] at h
      rw [iha h.1, ihb h.2]
  | cond a b c iha ihb ihc =>
      intro second h
      cases second <;> simp [encode] at h
      rw [iha h.1, ihb h.2.1, ihc h.2.2]
  | ifEq a b c d iha ihb ihc ihd =>
      intro second h
      cases second <;> simp [encode] at h
      rw [iha h.1, ihb h.2.1, ihc h.2.2.1, ihd h.2.2.2]
  | lett name a b iha ihb =>
      intro second h
      cases second <;> simp [encode] at h
      rw [Int.ofNat_inj.mp h.1, iha h.2.1, ihb h.2.2]
  | add a ih => intro second h; cases second <;> simp [encode] at h; rw [ih h]
  | all => intro second h; cases second <;> simp_all [encode]
  | assoc a ih => intro second h; cases second <;> simp [encode] at h; rw [ih h]
  | quote a ih => intro second h; cases second <;> simp [encode] at h; rw [ih h]
  | newSeal => intro second h; cases second <;> simp_all [encode]
  | «seal» a b iha ihb =>
      intro second h
      cases second <;> simp [encode] at h
      rw [iha h.1, ihb h.2]
  | «unseal» a b iha ihb =>
      intro second h
      cases second <;> simp [encode] at h
      rw [iha h.1, ihb h.2]

/-- What `(quote E)` shows is the text of `E`. -/
theorem observe_quote (e : Expr) : observe (.quote e) = some (encode e).toVal := by
  simp [observe, eval, print_plain (Datum.toVal_plain _)]

/-- The core with `quote`, with seals. -/
def reflective : Language (Option Val) where
  Phrase := Expr
  Context := Ctx
  plug := Ctx.plug
  observe := observe

/-- The core with `quote`, without seals. -/
def reflectiveSealFree : Language (Option Val) where
  Phrase := {e : Expr // e.sealFree = true}
  Context := {c : Ctx // c.sealFree = true}
  plug c e := ⟨c.1.plug e.1, Ctx.sealFree_plug c.2 e.2⟩
  observe e := observe e.1

def reflectiveExtension : Extension reflectiveSealFree reflective where
  embed := Subtype.val
  embedContext := Subtype.val
  plug_embed _ _ := rfl
  observe_embed _ := rfl

/-- `(quote [·])` reads its hole back. -/
theorem quote_quotes : Quotes reflectiveExtension ⟨.quote .hole, rfl⟩ := by
  intro first second h
  have observed : observe (.quote (show Expr from first)) = observe (.quote (show Expr from second)) :=
    h
  rw [observe_quote, observe_quote, Option.some.injEq] at observed
  exact encode_injective (Datum.toVal_injective observed)

/-- **With reflection, seals give no abstraction**: the two sealed programs are
told apart. -/
theorem quote_separates_sealed : ¬ reflective.Equiv (sealed 1) (sealed 2) := fun equivalent =>
  absurd (equiv_eq_of_quotes quote_quotes equivalent) (show sealed 1 ≠ sealed 2 by decide)

/-- **With reflection, nothing is eliminable**, in particular not seals. -/
theorem isEmpty_elimination_reflective : IsEmpty (Elimination reflectiveExtension) :=
  isEmpty_elimination_of_quotes quote_quotes ⟨.newSeal, fun base equal => by
    have free := base.2
    change base.1 = .newSeal at equal
    rw [equal] at free
    simp [Expr.sealFree] at free⟩

/-- The core with `quote`, without `ifEq`. -/
def reflectiveSugarFree : Language (Option Val) where
  Phrase := {e : Expr // e.ifEqFree = true}
  Context := {c : Ctx // c.ifEqFree = true}
  plug c e := ⟨c.1.plug e.1, Ctx.ifEqFree_plug c.2 e.2⟩
  observe e := observe e.1

def reflectiveSugarExtension : Extension reflectiveSugarFree reflective where
  embed := Subtype.val
  embedContext := Subtype.val
  plug_embed _ _ := rfl
  observe_embed _ := rfl

theorem quote_quotes_sugar : Quotes reflectiveSugarExtension ⟨.quote .hole, rfl⟩ := by
  intro first second h
  have observed : observe (.quote (show Expr from first)) = observe (.quote (show Expr from second)) :=
    h
  rw [observe_quote, observe_quote, Option.some.injEq] at observed
  exact encode_injective (Datum.toVal_injective observed)

/-- **With reflection, not even sugar is eliminable**: compare
`desugarElimination` without `quote`. -/
theorem isEmpty_elimination_sugar_reflective : IsEmpty (Elimination reflectiveSugarExtension) :=
  isEmpty_elimination_of_quotes quote_quotes_sugar
    ⟨.ifEq .all .all .all .all, fun base equal => by
      have free := base.2
      change base.1 = .ifEq .all .all .all .all at equal
      rw [equal] at free
      simp [Expr.ifEqFree] at free⟩

/-! ## Axiom audit -/

#print axioms sealed_equiv
#print axioms outcome_eq_of_equiv
#print axioms isEmpty_sealElimination
#print axioms leak_registry_read
#print axioms leak_ticket_structure
#print axioms leak_registry_write
#print axioms leak_capability_data
#print axioms desugarElimination
#print axioms sugar_conservative
#print axioms quote_separates_sealed
#print axioms isEmpty_elimination_reflective
#print axioms isEmpty_elimination_sugar_reflective

end Mettapedia.Languages.MeTTa.Seal.Eliminability
