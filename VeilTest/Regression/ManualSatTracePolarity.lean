import Veil

set_option linter.unusedVariables false

veil module ManualSatTracePolarity

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action set_flag {
  flag := true
}

invariant true

#gen_spec

/-- error: cannot translate Type -/
#guard_msgs in
sat trace [impossible] {
  assert False
} (by veil_bmc)

end ManualSatTracePolarity
