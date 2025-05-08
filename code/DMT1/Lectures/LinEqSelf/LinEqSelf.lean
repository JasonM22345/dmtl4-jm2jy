import Mathlib.Data.Matrix.Defs
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Field.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Notation
import Mathlib.Tactic.FieldSimp

/- @@@

# Matrix M N α

An M × N matrix with entries of type α is represented
as a value of type Matrix m n α. That is then defined
to be the function type M → N → α. Indices thus range
over values of arbitrary types. For finite index sets
we will use Fin types for both rows and columns. Matrix
(Fin m) (Fin n) α is thus the type of 2 x 2 matrices,
indexing from [0, 1] in each dimension to α elements.
@@@ -/

open Matrix Finset
universe u
variable {n : Nat} {α : Type u} [Field α]

/- @@@

Here's an example of a 2 x 2 rational matrix using
standard natural number indexing and notation that
comes with Lean's Matrix types.

@@@ -/

def myMatrix : Matrix (Fin 2) (Fin 2) ℚ :=
  ![![1, 0],
    ![0, 2]]

/- @@@

## Linear Equivalences

Let's now jump stright from α matrices to linear
equivalences. A linear equivalence is a bijective
function between two linear spaces. You can think
of there being a function that maps vectors from
one module to corresponding vectors in the other,
the inverse function. That it's a bijection means
every object goes to a unique object in the other
module and comes right back under *inverse*.

For us, a linear equivalence will be between two
*modules*, where scalarscan lack multiplicative
inverses. So in general there are no fractions or
fractions of actions in modules. To make a module,
which is almost a vector space, into one, give it
multiplicative inverses.
@@@ -/

/- @@@

## Between Modules

We have already established that our *Vc* vectors
form a module, formalized as *Module α (Vc α n)]*:
the type of module with *Vc* objects as the vectors
with α scalars. They also form a vector space with
α being an *field*. As ℚ is a field, we are working
with vector spaces without that being explicit.
@@@ -/

/-- Define a simple vector type `Vc` with a `get` function -/
structure Vc (α : Type u) (n : Nat) where
  data : Fin n → α

namespace Vc

/-- Extract the value at index `i` -/
def get (v : Vc α n) (i : Fin n) : α := v.data i

/-- Create a zero vector -/
def zero (n : Nat) : Vc α n :=
  ⟨fun _ => 0⟩

/-- Vector addition -/
def add (v w : Vc α n) : Vc α n :=
  ⟨fun i => v.get i + w.get i⟩

/-- Scalar multiplication -/
def smul (a : α) (v : Vc α n) : Vc α n :=
  ⟨fun i => a * v.get i⟩

end Vc

/- @@@

## TO DO

### A. Define a LinEqSelf type

Building on what we've provided define a *LinEqSelf*
type for representing linear equivalences between a
module and itself. Parameters will probably have to
include the shared scalar type), α, the *vector* type,
for us it's *Vc α n*, and and one or two α matrices
that specify the intended map and its inverse.
@@@ -/

/-- A linear equivalence from a space to itself, represented by a pair of inverse matrices. -/
structure LinEqSelf (α : Type u) [Field α] (n : Nat) where
  forward  : Matrix (Fin n) (Fin n) α
  inverse  : Matrix (Fin n) (Fin n) α
  are_inverses : forward * inverse = 1 ∧ inverse * forward = 1

namespace LinEqSelf

/-- Apply the forward transformation to a vector. -/
def apply (le : LinEqSelf α n) (v : Vc α n) : Vc α n :=
  ⟨fun i => (Finset.univ).sum (fun j => le.forward i j * v.get j)⟩

/-- Apply the inverse transformation to a vector. -/
def applyInverse (le : LinEqSelf α n) (v : Vc α n) : Vc α n :=
  ⟨fun i => (Finset.univ).sum (fun j => le.inverse i j * v.get j)⟩

end LinEqSelf

/- @@@

### B. Give Some Examples

@@@ -/

/-- Example 1D Linear Equivalence: scaling by 2 -/
def scaling1D : LinEqSelf ℚ 1 := by
  refine
  { forward  := ![![2]],
    inverse  := ![![1/2]],
    are_inverses := ?_ }
  constructor
  · -- forward * inverse = 1
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, Matrix.one_apply]
  · -- inverse * forward = 1
    ext i j
    fin_cases i; fin_cases j
    simp [Matrix.mul_apply, Matrix.one_apply]

/-- Example 3D Linear Equivalence: uniform scaling by 3 -/
def scaling3D : LinEqSelf ℚ 3 := by
  refine
  { forward  := (3 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ),
    inverse  := (1/3 : ℚ) • (1 : Matrix (Fin 3) (Fin 3) ℚ),
    are_inverses := ?_ }

  have h₁ : ((3 : ℚ) * (1/3)) = 1 := by field_simp
  have h₂ : ((1/3 : ℚ) * 3) = 1 := by field_simp

  constructor
  · -- forward * inverse = 1
    simp [smul_mul_assoc, Matrix.mul_one, Matrix.one_mul, smul_smul, h₁]
  · -- inverse * forward = 1
    simp [smul_mul_assoc, Matrix.mul_one, Matrix.one_mul, smul_smul, h₂]

/- @@@

## Extra Credit

- Generalize to maps between different modules then
show, by instantiating your type, that there's a linear
equivalence between *Vc* and *Fin n → α* values under
all the usual operations.
- Define a function or new constructor that allows one
to create a linear equivalence by giving not a matrix
(or two) but an n-tuple of vectors, each intended to be
the image of the corresponding unit vector under the map.
- Pick any element of the problem space to formalize and
automate, do something interesting, and explain briefly
what you did, with a pointer to your code.
@@@ -/

/-- A linear equivalence between spaces possibly of different dimensions. -/
structure LinEq (α : Type u) [Field α] (m n : Nat) where
  forward  : Matrix (Fin m) (Fin n) α
  inverse  : Matrix (Fin n) (Fin m) α
  are_inverses : forward * inverse = 1 ∧ inverse * forward = 1

namespace LinEq

/-- Apply the forward transformation. -/
def apply (le : LinEq α m n) (v : Vc α n) : Vc α m :=
  ⟨fun i => (Finset.univ).sum (fun j => le.forward i j * v.get j)⟩

/-- Example of a 2×2 Linear Equivalence: 90° rotation -/
def rotation2D : LinEq ℚ 2 2 := by
  refine
  { forward  := ![![0, -1], ![1, 0]],
    inverse  := ![![0, 1], ![-1, 0]],
    are_inverses := ?_ }
  constructor
  · -- forward ∘ inverse = identity
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [Matrix.mul_apply, Fin.sum_univ_two]
  · -- inverse ∘ forward = identity
    ext i j
    fin_cases i <;> fin_cases j
    all_goals
      simp [Matrix.mul_apply, Fin.sum_univ_two]

end LinEq
