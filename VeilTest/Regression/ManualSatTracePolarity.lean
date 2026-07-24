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

sat trace [possible] {
} (by
  refine ⟨default, default, ?_⟩
  veil_bmc)

/-- error: unable to prove goal, either it is false or you need to provide more facts. Could not produce a counter-example. Try introducing variables into the local context to get a counter-example. -/
#guard_msgs in
sat trace [impossible] {
  assert False
} (by veil_bmc)

end ManualSatTracePolarity
