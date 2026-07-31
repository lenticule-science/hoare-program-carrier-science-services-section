import Obsmetrologia.AperiodicOrder.MaterialSectors.Contact.Keratin

/-!
# Hoare-program measurement carriers

This application package carries program preconditions, transitions,
postconditions, and preservation witnesses. Its keratinous specialization uses
Obsmetrologia's material-contact mathematics without extending the
Obsmetrologia library or namespace.
-/

namespace HoareProgramMeasurement

universe u v

/-- A program is a transition equipped with input and output predicates and a
preservation witness. -/
structure Program (Input : Type u) (Output : Type v) where
  precondition : Input → Prop
  move : Input → Output
  postcondition : Output → Prop
  preserves : ∀ input, precondition input → postcondition (move input)

namespace Program

variable {Input : Type u} {Output : Type v}

/-- Exposes the preservation witness for one admitted input. -/
theorem preservesPost (program : Program Input Output) (input : Input)
    (precondition : program.precondition input) :
    program.postcondition (program.move input) :=
  program.preserves input precondition

end Program

open Obsmetrologia
open AperiodicOrder.MaterialSectors.Contact

/-- An application program whose transition locks and settles a keratin
complex supplied by Obsmetrologia. -/
structure KeratinousProgram (S : Order.CompleteLattice) where
  complex : KeratinComplex S
  history : complex.Vertex → History S
  precondition : Tarski.Assign complex → Prop
  postcondition : Tarski.Assign complex → Prop
  preserves :
    ∀ seed,
      precondition seed →
        postcondition (Tarski.settle complex (lockSeed complex history seed))

namespace KeratinousProgram

variable {S : Order.CompleteLattice}

/-- The locked seed produced before settlement. -/
def lockedSeed (program : KeratinousProgram S)
    (seed : Tarski.Assign program.complex) :
    Tarski.Assign program.complex :=
  lockSeed program.complex program.history seed

/-- The program transition supplied by locking and settlement. -/
def move (program : KeratinousProgram S)
    (seed : Tarski.Assign program.complex) :
    Tarski.Assign program.complex :=
  Tarski.settle program.complex (program.lockedSeed seed)

/-- Projects the application-specific carrier to the generic program carrier. -/
def toProgram (program : KeratinousProgram S) :
    Program (Tarski.Assign program.complex) (Tarski.Assign program.complex) where
  precondition := program.precondition
  move := program.move
  postcondition := program.postcondition
  preserves := program.preserves

/-- The projected program preserves its declared postcondition. -/
theorem toProgramPreserves (program : KeratinousProgram S)
    (seed : Tarski.Assign program.complex)
    (precondition : program.precondition seed) :
    program.postcondition (program.toProgram.move seed) :=
  program.preserves seed precondition

/-- The application transition reaches the least compatible state above its
locked seed. -/
theorem moveLeastCompatible (program : KeratinousProgram S)
    (seed candidate : Tarski.Assign program.complex)
    (compatible : Tarski.IsCompatible program.complex candidate)
    (above : ∀ vertex, S.le (program.lockedSeed seed vertex) (candidate vertex)) :
    (Tarski.AssignCL S program.complex.Vertex).le (program.move seed) candidate :=
  settle_lock_is_least_compatible
    program.complex program.history seed candidate compatible above

end KeratinousProgram

end HoareProgramMeasurement
