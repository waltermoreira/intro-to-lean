-- # Basic Syntax

-- This is a comment

/-
This is a multi-line comment.
It can span multiple lines.
Useful for longer explanations.
-/

-- The `#check` command is used to inspect the type of
-- an expression, definition, or theorem in Lean
#check 42
#check true
#check Bool
#check 3 = 3
#check 3 = 4
#check Type
#check Type 1  -- Check the section `More About the Main Concept` to understand these
               -- numbers

#check 'h'
#check ['h', 'e', 'l', 'l', 'o']
#check "hello"

-- The `#print` command allows you to inspect
-- the definition of a function, theorem, or
-- other named value
#print Bool
#print Nat
#print Char
#print List
#print String
#print Fin

#check 42
#check -1
#check (42 : Int)      -- We can force 42 into the integers,
-- #check (3.2 : Int)  -- but we cannot force 3.2 into the integers

-- The `#eval` command evaluates an expression a display its result
#eval 42
#eval 3 + 5
#eval 3.0 / 2
#eval 3 / 2
#eval 3 / 0

#check ∃ x : Nat, x = 2
-- In general, we cannot evaluate a Prop
-- #eval ∃ x : Nat, x < 0

-- ...but sometimes we can, when there is an algorithm to "decide":
#eval 3 = 3
#eval 3 = 4

-- The `def` keyword is used to define a function or a value

-- Definition of number pi
def pi : Float := 3.1415926
#check pi
#eval pi

-- Definition of the sum of two natural numbers
def sum (a b : Nat) : Nat := a + b
-- Another completely equivalent way of define `sum`:
def sum2 : Nat → Nat → Nat := fun a b => a + b

-- An appetizer about proving theorems:
-- We can formally prove that the above definitions are exactly the same
theorem sum_eq_sum2 : sum = sum2 := by rfl
theorem sum_eq_sum2a : ∀ (n m : Nat), sum n m = sum2 n m := by
  intro n m
  rfl

-- the keyword `fun` is very similar to the keyword `lambda` in Python:
-- compare with Python: lambda x, y: x + y
#check fun (a b : Nat) => a + b

-- The function type
-- if A and B are types, then A → B is another type,
-- the type of all mappings from A to B
-- We will write `\to` to write the arrow

-- The type of all mappings from Nat to Nat
#check Nat → Nat
-- Examples of inhabitants of the type `Nat → Nat`:
#check (fun n => n : Nat → Nat)

def increment : Nat → Nat := fun n => n + 1
#check increment
-- #check (sum : Nat → Nat)    -- Fails! Why?
#check sum 3

-- More interesting functions:

def isZero : Nat → Bool := fun n =>
  match n with
  | 0 => true
  | _ => false

#eval isZero 3
#eval isZero 0
-- #eval isZero 'c'

-- Fibonacci sequence: F 0 = 0, F 1 = 1, and F (n + 2) = F (n + 1) + F (n)
def fib (n : Nat) : Nat :=
  match n with
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

#eval fib 0
#eval fib 1
#eval fib 2
#eval fib 3
#eval fib 4
#eval fib 5
--#eval fib 123456789
