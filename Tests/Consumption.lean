/-
  R4: every linear binder is consumed exactly once on every path.

  Zero consuming uses is a leak (discharge it with `Drop.drop`); two or more is a copy.
  Every definition below is wrapped in `#guard_msgs`, so the test suite fails if the
  diagnostics change.
-/
import Linear

open Linear

namespace Tests.Consumption

/-! ### Basic consumption -/

-- ok: the wrapper is consumed once and so is its payload.
#guard_msgs in
def unwrap : Lin Nat -* Nat := fun h =>
  match h with
  | .lin n => n

/--
warning: linear value `n` is consumed 2 times on some path and will be copied
-/
#guard_msgs in
def copyPayload : Lin Nat -* Nat := fun h =>
  match h with
  | .lin n => n + n

/--
warning: linear value `_h` is not consumed on every path; discharge it with `Drop.drop`
-/
#guard_msgs in
def leakLin : Lin Nat -* Nat := fun _h => 7

-- ok: the payload is re-wrapped linearly.
#guard_msgs in
def rewrap : Lin Nat -* Lin Nat := fun h =>
  match h with
  | .lin n => .lin n

-- ok: `escape` is the designated one-way door to unrestricted.
#guard_msgs in
def escapeIt : Lin Nat -* Ur Nat := fun h =>
  match h with
  | .lin n => escape n

/-! ### Unrestricted values -/

-- ok: `Ur` values are unrestricted, so the payload may be copied freely.
#guard_msgs in
def useUr (u : Ur Nat) : Nat :=
  match u with
  | .ur n => n + n

/-- ok: dropping through the user-supplied `Drop` instance is not a leak. -/
instance : Drop (Lin Nat) where
  drop _ := ()

#guard_msgs in
def dropIt : Lin Nat -* Nat := fun h =>
  let _ := Drop.drop h
  42

/-! ### Branching

Usage summaries combine path-wise: occurrences in sequence add up, occurrences in mutually
exclusive branches combine with `min`/`max`. -/

-- ok: `match` branches are mutually exclusive, so one use in each branch is exactly once.
#guard_msgs in
def branchBoth (b : Bool) : Lin Nat -* Nat := fun h =>
  match b with
  | true  => match h with | .lin n => n
  | false => match h with | .lin n => n

/--
warning: linear value `h` is not consumed on every path; discharge it with `Drop.drop`
-/
#guard_msgs in
def branchLeak (b : Bool) : Lin Nat -* Nat := fun h =>
  match b with
  | true  => match h with | .lin n => n
  | false => 7

/--
warning: linear value `n` is consumed 2 times on some path and will be copied
-/
#guard_msgs in
def branchCopy (b : Bool) : Lin Nat -* Nat := fun h =>
  match b with
  | true  => match h with | .lin n => n + n
  | false => match h with | .lin n => n

end Tests.Consumption
