import HoareProgramMeasurement.Program

/-!
# Predicate-preserving service arrows, Hoare composition, and Huidu control

This formalizes the *deterministic, total* fragment of a service program, using
the original Program preservation witness. It does not model effects, exceptions,
financial transfers, host permission, customer receipt, or sheaf descent.
The context-indexed/economic extensions need independent source-qualified proofs.

A service interface is a state type with an admissibility predicate. An arrow
is a program together with a witness that it maps admitted source states to
admitted destination states. Identity and composition satisfy the category
laws by function composition and proof irrelevance; no arbitrary Hoare triple
is silently considered composable when its intermediate predicates differ.
-/

namespace HoareProgramMeasurement

universe u

/-- Admissibility is part of an interface, not merely its unrefined data type.
    Budget residuals, authority and promises may all be included in the predicate,
    but an actual adapter must supply their source-owned meanings and evidence. -/
structure ServiceInterface where
  carrier : Type u
  admits : carrier → Prop

/-- A verified total deterministic arrow between two refined interfaces. -/
structure ServiceArrow (A B : ServiceInterface.{u}) where
  move : A.carrier → B.carrier
  preserves : ∀ x, A.admits x → B.admits (move x)

namespace ServiceArrow

variable {A B C D : ServiceInterface.{u}}

/-- The identity move preserves precisely the interface predicate. -/
def identity (A : ServiceInterface.{u}) : ServiceArrow A A where
  move := fun x => x
  preserves := by
    intro x hx
    exact hx

/-- Compose only through the *same* intermediate refined interface B. -/
def compose (first : ServiceArrow A B) (second : ServiceArrow B C) :
    ServiceArrow A C where
  move := fun x => second.move (first.move x)
  preserves := by
    intro x hx
    exact second.preserves (first.move x) (first.preserves x hx)

/-- Extensional equality: two arrows with the same underlying move are
    equal, since preservation evidence is a proposition. -/
theorem extensional {first second : ServiceArrow A B}
    (h : first.move = second.move) : first = second := by
  cases first with
  | mk firstMove firstProof =>
    cases second with
    | mk secondMove secondProof =>
      cases h
      rfl

theorem identity_then (arrow : ServiceArrow A B) :
    compose (identity A) arrow = arrow := by
  apply extensional
  rfl

theorem then_identity (arrow : ServiceArrow A B) :
    compose arrow (identity B) = arrow := by
  apply extensional
  rfl

theorem associative (first : ServiceArrow A B) (second : ServiceArrow B C)
    (third : ServiceArrow C D) :
    compose (compose first second) third = compose first (compose second third) := by
  apply extensional
  rfl

/-- A predicate-entailment handoff, witnessed by a proof, not by matching
    unrefined schemas. This is the morphism between different refinements
    of *the same* intermediate carrier. -/
def handoff {X : Type u} {P Q : X → Prop}
    (entails : ∀ x, P x → Q x) :
    ServiceArrow ⟨X, P⟩ ⟨X, Q⟩ where
  move := fun x => x
  preserves := entails

end ServiceArrow

namespace Program

variable {Input Middle Output : Type u}

/-- Reuse an original Program and its original proof, choosing its actual
    precondition and postcondition as the two categorical object refinements. -/
def toServiceArrow (program : Program Input Middle) :
    ServiceArrow ⟨Input, program.precondition⟩
                 ⟨Middle, program.postcondition⟩ where
  move := program.move
  preserves := program.preserves

/-- Sequential composition of Hoare programs *requires* an explicit
    intermediate implication. Absent that witness, it is not constructed. -/
def sequential (first : Program Input Middle) (second : Program Middle Output)
    (entails : ∀ y, first.postcondition y → second.precondition y) :
    Program Input Output where
  precondition := first.precondition
  move := fun x => second.move (first.move x)
  postcondition := second.postcondition
  preserves := by
    intro x hx
    exact second.preserves (first.move x)
      (entails (first.move x) (first.preserves x hx))

/-- The composed Hoare program agrees with composing its two verified arrows
    *through the explicit predicate-entailment handoff*. -/
theorem sequential_as_service_arrows
    (first : Program Input Middle) (second : Program Middle Output)
    (entails : ∀ y, first.postcondition y → second.precondition y) :
    toServiceArrow (sequential first second entails) =
      ServiceArrow.compose
        (ServiceArrow.compose (toServiceArrow first) (ServiceArrow.handoff entails))
        (toServiceArrow second) := by
  apply ServiceArrow.extensional
  rfl

end Program

namespace Huidu

/-- A source-qualified observation plus an existing admissible setting yields
    an admissible revised setting. This is a control *obligation*, not a
    fabricated current calibration or permission to weaken binding law. -/
def controller {Observation Setting : Type u}
    (authorized : Observation → Prop) (admissible : Setting → Prop)
    (adjust : Observation → Setting → Setting)
    (safe : ∀ observation setting, authorized observation →
      admissible setting → admissible (adjust observation setting)) :
    ServiceArrow
      ⟨Observation × Setting,
        fun pair => authorized pair.1 ∧ admissible pair.2⟩
      ⟨Setting, admissible⟩ where
  move := fun pair => adjust pair.1 pair.2
  preserves := by
    intro pair hp
    exact safe pair.1 pair.2 hp.1 hp.2

/-- Each admissible configuration must satisfy the *same protected external
    postcondition*. This models one deterministic part of a RenDanHeYi
    service's promised behavior, not its monetary or independent receipt. -/
def governedOffer {Setting Input Output : Type u}
    (admissible : Setting → Prop) (P : Input → Prop) (Q : Output → Prop)
    (run : Setting → Input → Output)
    (uniform : ∀ setting input, admissible setting →
      P input → Q (run setting input))
    (setting : Setting) (hSetting : admissible setting) :
    ServiceArrow ⟨Input, P⟩ ⟨Output, Q⟩ where
  move := run setting
  preserves := by
    intro x hx
    exact uniform setting x hSetting hx

/-- Conditional safety of changing Huidu settings: if the controller keeps
    the setting admissible, the offered program still meets protected Q. -/
theorem revised_setting_preserves_promise
    {Observation Setting Input Output : Type u}
    (authorized : Observation → Prop) (admissible : Setting → Prop)
    (P : Input → Prop) (Q : Output → Prop)
    (adjust : Observation → Setting → Setting)
    (safe : ∀ observation setting, authorized observation →
      admissible setting → admissible (adjust observation setting))
    (run : Setting → Input → Output)
    (uniform : ∀ setting input, admissible setting →
      P input → Q (run setting input))
    (observation : Observation) (setting : Setting) (x : Input)
    (hAuthorized : authorized observation)
    (hSetting : admissible setting) (hInput : P x) :
    Q (run (adjust observation setting) x) := by
  exact uniform (adjust observation setting) x
    (safe observation setting hAuthorized hSetting) hInput

end Huidu

/-- Concrete counterexample: two local tasks consuming one unit each are
    separately feasible under budget 1 but infeasible together. This
    refutes naive local-to-global resource gluing; it is not a general
    sheaf-theoretic non-gluing theorem without a specified site. -/
theorem shared_budget_local_feasible_global_infeasible :
    (1 ≤ (1 : Nat)) ∧ (1 ≤ (1 : Nat)) ∧ ¬ (1 + 1 ≤ (1 : Nat)) := by
  decide

end HoareProgramMeasurement
