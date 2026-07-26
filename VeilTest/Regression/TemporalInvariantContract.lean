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

/-- info: ∀ {ρ σ : Type} {χ : State.Label → Type}
  [χ_rep : (__veil_f : State.Label) → FieldRepresentation __veil_f.toDomain __veil_f.toCodomain (χ __veil_f)]
  [χ_rep_lawful :
    ∀ (__veil_f : State.Label),
      LawfulFieldRepresentation __veil_f.toDomain __veil_f.toCodomain (χ __veil_f) (χ_rep __veil_f)]
  [σ_sub : IsSubStateOf (State χ) σ] [ρ_sub : IsSubReaderOf Theory ρ] [σ_inhabited : Inhabited σ] (th : ρ),
  veil_term% Assumptions → (⌜ veil_term% Init ⌝ ∧ □⟨ veil_term% NextStep ⟩) |-tla- (veil_term% impossible) : Prop -/
#guard_msgs in
#check temporal_theorem_body_of% impossible

end TemporalInvariantContract
