import Veil

veil module FailedAssertionFinalization

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action stutter {
  pure ()
}

/-- error: Unbound uncapitalized variable: missingAssertionBody -/
#guard_msgs in
invariant [broken] missingAssertionBody

/-- error: cannot finalize the specification: the following assertion declaration(s) failed to elaborate: [broken] -/
#guard_msgs in
#gen_spec

end FailedAssertionFinalization
