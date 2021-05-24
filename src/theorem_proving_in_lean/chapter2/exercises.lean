
def double : ℕ → ℕ := λ x, x + x
def do_twice : (ℕ → ℕ) → ℕ → ℕ := λ f x, f (f x)

/-
1. Define a function 
Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) 
which applies its argument twice, so that Do_Twice 
do_twice is a function that applies its input four times. 
Then evaluate Do_Twice do_twice double 2.
-/

def Do_Twice : ((ℕ → ℕ) → (ℕ → ℕ)) → (ℕ → ℕ) → (ℕ → ℕ) := λ F g h, (F g) (g h)
#reduce Do_Twice do_twice double 2



/-
2. Define the functions curry and uncurry
-/

def curry {α β γ : Type*} (f : α × β → γ) : α → β → γ := λ (x1 : α) (x2: β), f (x1, x2)
def uncurry {α β γ : Type*} (f : α → β → γ) : α × β → γ := λ (x : α × β), f x.fst x.snd

#check @curry
#check @uncurry

def mult : (ℕ × ℕ → ℕ) := λ x, x.fst * x.snd

#reduce mult (2,3)

def multCurried := curry mult
#check multCurried
#reduce multCurried 2 3

def multUncurried := uncurry multCurried
#check multUncurried
#reduce multUncurried (2, 3)

#reduce mult == multUncurried


/-
3. Declare a constant vec_add that could represent a function 
that adds two vectors of natural numbers of the same length, 
and a constant vec_reverse that can represent a function that 
reverses its argument. 
Use implicit arguments for parameters that can be inferred. 

Declare some variables and check some expressions involving 
the constants that you have declared.
-/

universe u
constant vec : Type u → ℕ → Type u

namespace vec
  constant empty : Π α : Type u, vec α 0
  constant cons :
    Π {α : Type u} (n : ℕ), α → vec α n → vec α (n + 1)
  constant append :
    Π {α : Type u} {n m : ℕ},  vec α m → vec α n → vec α (n + m)
  constant vec_add : 
    Π {α : Type u} {n : ℕ},  vec α n → vec α n → vec α n
  constant vec_reverse : 
    Π {α : Type u} {n : ℕ},  vec α n → vec α n
end vec

variable a : vec nat 10
variable b : vec nat 10
variable c : vec nat 20

#check vec.vec_add a b
#check vec.vec_reverse a
#check vec.vec_reverse c

/-
4. Declare a constant matrix so that matrix α m n could represent 
the type of m by n matrices. Declare some constants to represent 
functions on this type, such as matrix addition and multiplication,
and (using vec) multiplication of a matrix by a vector. Once again,
declare some variables and check some expressions involving the 
constants that you have declared.
-/

constant mat : Type u → ℕ → ℕ → Type u

namespace mat
  constant add : 
    Π {α : Type u} {n m : ℕ},  mat α n m → mat α n m → mat α n m
  constant mult : 
    Π {α : Type u} {n m k : ℕ},  mat α n m → mat α m k → mat α n k
  constant mult_vec : 
    Π {α : Type u} {n m : ℕ},  mat α n m → vec α m → vec α m
  constant add_scalar : 
    Π {α : Type u} {n m : ℕ}, α → mat α n m → mat α n m
  constant mult_scalar : 
    Π {α : Type u} {n m : ℕ}, α → mat α n m → mat α n m
  constant transpose : 
    Π {α : Type u} {n m : ℕ}, mat α n m → mat α m n
end mat


variable A : mat nat 7 5
variable B : mat nat 5 13
variable C : mat nat 7 5
variable x : vec nat 5
variable alpha : nat

#check mat.add A A
#check mat.add A C
#check mat.mult A B
#check mat.mult_vec A x
#check mat.add_scalar alpha A
#check mat.mult_scalar alpha A
#check mat.transpose A
#check mat.mult A (mat.transpose A)