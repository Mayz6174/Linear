/-
  R3 admission: a linear value may only be handed to a consumed (`-*`) parameter, a `-*`
  constructor field, a `casesOn` major premise, `Drop.drop`, or `escape`.
-/
import Linear

open Linear

namespace Tests.Admission

/-- Not marked `-*`, so it may not receive a linear value. -/
def ignoreArg (α : Type) (_x : α) : Nat := 0

/-- Marked `-*`, so it may. -/
def consume : Lin Nat -* Nat := fun h =>
  match h with
  | .lin n => n

-- ok: `h` is handed to a consumed parameter.
#guard_msgs in
def goodAdmission : Lin Nat -* Nat := fun h => consume h

/--
warning: linear value passed to parameter 1 of `Tests.Admission.ignoreArg`, which is not marked `-*`
-/
#guard_msgs in
def badAdmission : Lin Nat -* Nat := fun h => ignoreArg (Lin Nat) h

/-! ### Closures crossing a definition boundary

`mk` returns a plain function type, so the obligations of the value it captured are not
visible in its type; its own definition reports the escape. -/

/--
warning: closure capturing linear value `h` escapes: its type is not linear, so nothing forces it to be called exactly once
-/
#guard_msgs in
def mk : Lin Nat -* (Unit -> Nat) := fun h => fun _ => consume h

-- Calling the closure exactly once is accepted.
#guard_msgs in
def bindOnce : Lin Nat -* Nat := fun h => let f := mk h; f ()

/--
warning: linear value `h` is consumed 2 times on some path and will be copied
-/
#guard_msgs in
def bindTwice : Lin Nat -* Nat := fun h => let f := mk h; f () + f ()

-- A closure handed to an unrestricted parameter may be called any number of times.
def callTwice (g : Unit -> Nat) : Nat := g () + g ()

/--
warning: linear value passed to parameter 0 of `Tests.Admission.callTwice`, which is not marked `-*`
-/
#guard_msgs in
def throughCall : Lin Nat -* Nat := fun h => callTwice (mk h)

-- A closure handed to a function that drops it is equally illegal.
def ignoreFn (_g : Unit -> Nat) : Nat := 0

/--
warning: linear value passed to parameter 0 of `Tests.Admission.ignoreFn`, which is not marked `-*`
-/
#guard_msgs in
def throughIgnore : Lin Nat -* Nat := fun h => ignoreFn (mk h)

end Tests.Admission
