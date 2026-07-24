import Veil

/-!
# Regression: refresh state binders after calls embedded in guards

Lean lifts `(← call)` out of a `require`, `assert`, or `assume` expression.
The call can mutate Veil state before the guard runs, so the cached field
binders must be refreshed before a later statement reads them.
-/

set_option linter.unusedVariables false

veil module StateRefreshAfterGuardCall

individual x : Bool
individual y : Bool

#gen_state

after_init {
  x := false
  y := false
}

procedure setX {
  x := true
  return true
}

action require_call {
  require (← setX)
  y := x
}

action assert_call {
  assert (← setX)
  y := x
}

action assume_call {
  assume (← setX)
  y := x
}

invariant true

#gen_spec

/--
info: ✅ Satisfying trace found
  State 0 (via init):
    x = false
    y = false
  State 1 (via require_call):
    x = true
    y = true
-/
#guard_msgs(info, drop warning) in
sat trace {
  require_call
  assert (x ∧ y)
}

/--
info: ✅ Satisfying trace found
  State 0 (via init):
    x = false
    y = false
  State 1 (via assert_call):
    x = true
    y = true
-/
#guard_msgs(info, drop warning) in
sat trace {
  assert_call
  assert (x ∧ y)
}

/--
info: ✅ Satisfying trace found
  State 0 (via init):
    x = false
    y = false
  State 1 (via assume_call):
    x = true
    y = true
-/
#guard_msgs(info, drop warning) in
sat trace {
  assume_call
  assert (x ∧ y)
}

-- None of the three guards may leave the later assignment reading stale `x`.
/-- error: No satisfying trace exists -/
#guard_msgs(error, drop info, drop warning) in
sat trace {
  require_call
  assert (x ∧ ¬ y)
}

/-- error: No satisfying trace exists -/
#guard_msgs(error, drop info, drop warning) in
sat trace {
  assert_call
  assert (x ∧ ¬ y)
}

/-- error: No satisfying trace exists -/
#guard_msgs(error, drop info, drop warning) in
sat trace {
  assume_call
  assert (x ∧ ¬ y)
}

end StateRefreshAfterGuardCall
