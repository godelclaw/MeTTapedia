import Mathlib

#check Except.bind
#check bind
#reduce (do let x <- (Except.ok 1 : Except String Nat); Except.ok (x + 1))

universe uE uA uB

@[simp] theorem bind_ok {ε : Type uE} {α : Type uA} {β : Type uB}
    (a : α) (f : α → Except ε β) :
    Except.bind (.ok a) f = f a := rfl

@[simp] theorem monad_bind_ok {ε α β : Type uA}
    (a : α) (f : α → Except ε β) :
    ((Except.ok a : Except ε α) >>= f) = f a := rfl

example : (do let x <- (Except.ok 1 : Except String Nat); Except.ok (x + 1)) =
    Except.ok 2 := by simp
