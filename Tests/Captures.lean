/-
  Closures: a closure that mentions a linear value has captured it, so calling the closure is
  what consumes the value. Such a closure behaves like Rust's `FnOnce`: it may not be handed to
  a parameter that is not `-*`, and it may not escape as the definition's result.
-/
import Linear

open Linear

namespace Tests.Captures

def consume : Lin Nat -* Nat := fun h =>
  match h with
  | .lin n => n

/--
warning: linear value passed to parameter 2 of `List.map`, which is not marked `-*`
-/
#guard_msgs in
def captureAdmission (xs : List Nat) : Lin Nat -* List Nat := fun h =>
  xs.map (fun _ => consume h)

/--
warning: closure capturing linear value `h` escapes: its type is not linear, so nothing forces it to be called exactly once
-/
#guard_msgs in
def captureEscape : Lin Nat -* (Unit -> Nat) := fun h =>
  fun _ => consume h

-- ok: the closure is applied immediately, so it is consumed exactly once.
#guard_msgs in
def appliedImmediately : Lin Nat -* Nat := fun h =>
  (fun _ => consume h) ()

/--
warning: linear value `h` is consumed 2 times on some path and will be copied
-/
#guard_msgs in
def boundLocallyTwice : Lin Nat -* Nat := fun h =>
  let g := fun _ => consume h
  g () + g ()

end Tests.Captures
