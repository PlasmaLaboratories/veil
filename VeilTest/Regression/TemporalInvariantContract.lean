import Veil
import Veil.Liveness

/-!
Temporal proofs range over the generated behavior (`Init ∧ □Next`) rather
than silently assuming that every declared invariant always holds.
-/

open TLA

veil module TemporalInvariantContract

individual flag : Bool

#gen_state

after_init {
  flag := false
}

action stutter {
  pure ()
}

-- Deliberately false and unchecked: it must not become a temporal premise.
safety [falseInvariant] False

#gen_spec

temporal [top] (⊤)

prove_temporal_by [top]
  tstart hInit hNext
  tdsimp only [top]
  intro _ _
  exact True.intro

temporal [impossible] □ ⌜ fun _ => False ⌝

/-- error: tstart expected 2 names, but got 3 -/
#guard_msgs in
prove_temporal_by [impossible]
  tstart hInit hNext hInv
  tclear hInit hNext
  tdsimp only [impossible]
  tmonotone
  unveil_temporal

end TemporalInvariantContract
