/-
  Regression tracker for constructs the linter currently accepts although they are not linear.

  Each definition here is *expected to be silent*. If one of them starts producing a
  diagnostic, the checker has improved: remove it from this file, move it to a positive test,
  and update the limitations section of `README.md`.
-/
import Linear

open Linear

namespace Tests.KnownHoles

def consume : Lin Nat -* Nat := fun h => match h with | .lin n => n

/--
warning: closure capturing linear value `h` escapes: its type is not linear, so nothing forces it to be called exactly once
-/
#guard_msgs in
def mk : Lin Nat -* (Unit -> Nat) := fun h => fun _ => consume h

-- Known hole: the closure is stored in a list. Calls through the container are not tracked.
#guard_msgs in
def listTwice : Lin Nat -* Nat := fun h =>
  let fs := [mk h]
  fs.foldl (fun acc g => acc + g () + g ()) 0

-- Known hole: the closure is stored in a list and never called at all.
#guard_msgs in
def listDrop : Lin Nat -* Nat := fun h =>
  let fs := [mk h]
  fs.length

-- Known hole: a single list element applied once is indistinguishable from one never applied.
#guard_msgs in
def listOnce : Lin Nat -* Nat := fun h =>
  let fs := [mk h]
  fs.foldl (fun acc g => acc + g ()) 0

end Tests.KnownHoles
