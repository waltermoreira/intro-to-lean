import Mathlib

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


-- Second class

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

-- Let's review the Main Concept on the class' notes:

#check 4 = 4
#check Prop
#check Eq.refl 4

-- A bit more clarity of differences between Bool and Prop

#check (Eq.refl 4 : (4 = 4 : Prop))
#check               (true : Bool)


-- And now back to practical things...

#eval [2, 3, 5, 7]

def myList := [2, 3, 5, 7]
/- How to compute its length?
.
.
.
.
.
-/
#eval List.length myList
#eval myList.length

/- How to get the last element?
.
.
.
.
.
-/
#eval myList.getLast?

def empty : List Nat := []
#eval empty.length
#eval empty.getLast?

#eval myList.sum


-- In general, in functional programming we use lists a lot, and we process them
-- with high level operations instead of `for` or `while` loops.
-- The main operation is `map`.

#check myList.map (fun n => decide (Even n))

def checkEvens (l : List Nat) : List Bool := l.map (fun n => decide (Even n))
#eval checkEvens myList

-- Calculate the first `n` fibonacci numbers
def fibonacciUpTo (n : Nat) : List Nat :=
  (List.range n).map fib

#eval fibonacciUpTo 10


-- The other main operation is `fold`.

#check List.foldl

#eval [1, 2, 3, 4, 5].foldl (fun a b => a + b) 0

def mySum (l : List Nat) : Nat := l.foldl (fun a b => a + b) 0

theorem mySum_eq_sum (l : List Nat) : mySum l = List.sum l := by
  simp only [mySum]
  rw [List.sum_eq_foldl_nat]


-- Third class

-- Let's recap how we define functions over types such as `Nat`:

def repeatString : Nat → String → String := fun n s =>
  match n with
  | 0 => ""
  | n + 1 => s ++ repeatString n s

#eval repeatString 3 "foo"
#eval repeatString 0 "foo"

-- Similarly, we can construct functions over `List Nat` "by cases":
-- A list can be either:
-- - the empty list []
-- - or it can be of the form: `List.cons a as` (`a` is the first element, and
--   `as` is the "tail" of the list)

#eval [3, 7, 9] = List.cons 3 (List.cons 7 (List.cons 9 []))

-- Let's try to define our own version of List.length

def myLength : List Nat -> Nat := fun l =>
  match l with
  | [] => 0
  | List.cons a as => 1 + myLength as

#eval myLength [3, 7, 9]

-- Another example: find the largest number on a list

def maximum : List Nat -> Nat := fun l =>
  match l with
  | [] => 0
  | .cons a as => max a (maximum as)

#eval maximum [100, 2, 5]

-- Notice that sometimes the code we wrote works for more types than what we declared
-- in the signature. For example: `myLength`

def myLength2 : {α : Type} → List α → Nat := fun l =>
  match l with
  | [] => 0
  | .cons _ as => 1 + myLength2 as

theorem myLength2_eq_myLength : myLength2 (α := Nat) = myLength := by
  ext n
  induction n <;> simp only [myLength, myLength2, Nat.add_left_cancel_iff]
  assumption

-- Polymorphism usually allow us to apply a given piece of code to a lot more situations
-- than originally thought.
-- However, given a polymorphic type, it usually **constrains** the implementation
-- significatively.

-- Consider the following type. What implementations can we write that have such type?
def puzzle : {α : Type} → α → α := fun x => sorry

-- Similarly, let's try to write a function that returns the first element of a list,
-- in the "most polymorphic way possible":
def getFirst : {α : Type} → List α → α := fun l => sorry

/-
.
.
.
.
.
.
.
In fact, we can prove that the type is **empty**!
-/
theorem cannotWriteGetFirst : IsEmpty ({α : Type} → List α → α) := by
  simp only [isEmpty_iff]
  intro a
  specialize a ([] : List Empty)
  grind

-- Since we cannot have exceptions in the type `List α → α`, we need to represent
-- the presence of errors in the return type:

#print Option
#check (some 3 : Option Nat)
#check (none : Option Nat)

def getFirst2 : {α : Type} → List α → Option α := fun l =>
  match l with
  | [] => none
  | .cons a _ => some a

#eval getFirst2 [5, 4, 2]
#eval (getFirst2 [] : Option Nat)


-- Fourth class

-- Sometimes we want to collect a bit more information about the type of exceptional
-- condition:

#print Except
#check (.ok 3 : Except String Nat)
#check (.error "this is an error" : Except String Nat)

def division : Int → Int → Except String Rat := fun a b =>
  match b with
  | 0 => .error "division by zero"
  | _ => .ok (a / b)

#eval division 6 10
#eval division 1 0

-- Let's try to parse some strings:

#check Std.Time.PlainTime.parse
#eval Std.Time.PlainTime.parse "12:23:50"
#eval Std.Time.PlainTime.parse "foo 12:23:50"

def checkAmPm : String → String := fun s =>
  match Std.Time.PlainTime.parse s with
  | .ok result => if result.hour < 12 then "Morning" else "Afternoon"
  | .error err => s!"There was an error: {err}"

#eval checkAmPm "11:30:00"

-- Structures

-- We have seen that the main way to encode the data is by using *types*, and the
-- main way to encode the operations on the data is by using *functions*.
-- So far we have dealt with types already provided to us by the language,
-- such as `Nat`, `Bool`, `List`, `Option`.  But Lean also allows us to create our
-- own types.

-- Structures are similar to a Pydantic dataclass in Python.

-- Let's define a type to represent a point in the plane:

structure Point where
  x : Float
  y : Float

#print Point  -- `Point` becomes a bonafide type as any other we have seen
#check Point

def p1 : Point := { x := 1.0, y := 2.0 }
-- or equivalently
def p1' := Point.mk 1.0 2.0

#eval p1
#eval p1.x
#eval p1.y

def distance (p1 p2 : Point) : Float :=
  Float.sqrt ((p1.x - p2.x) ^ 2 + (p1.y - p2.y) ^ 2)

#eval distance {x := 0.0, y := 0.0} {x := 1.0, y := 1.0}


-- In general, the fields of a structure can be *any* type, including polymorphic types.

structure Pair (α : Type) (β : Type) where
  first : α
  second : β

#print Pair
#check Pair

def myPair1 := Pair.mk "foo" 3
#check myPair1.second

def myPair2 := Pair.mk 3 (fun (s : String) => "hello " ++ s)
#check myPair2.second
#eval myPair2.second "world"

-- Any of the fields can be even of type `Pair`, which we are defining:
def myPair3 := Pair.mk (Pair.mk 1 2) 3
#check myPair3
#check myPair3.first
#check myPair3.first.first

-- Structure types are call **Product types**.

-- An interesting things with pure functional languages is that we cannot modify
-- structures, as we usually do in Python (e.g., something like `obj.x = 3`)

def updateFirst {α β : Type} : α → Pair α β → Pair α β := fun x p =>
  { first := x, second := p.second}
  -- { p with first := x}

#eval myPair1
#eval updateFirst "hello" myPair1


-- The other way to construct types is called **Sum types**, or **Inductive types**

-- The simplest example:

inductive BasicColor where
  | red : BasicColor
  | green : BasicColor
  | blue : BasicColor

#check BasicColor
#print BasicColor

#check BasicColor.red

-- A simple inductive type like this is similar to an `Enum` in Python
-- We have already seen types of this form: `Bool`:

#check Bool  -- Check the definition in the source code of Lean


-- More interesting, inductive types can have polymorphic types in their fields, and
-- can even contain themselves. This is one of the key properties that allows us to
-- define "infinite" types.

inductive Either (α : Type) (β : Type) where
  | left : α → Either α β
  | right : β → Either α β

def example1 : Either Int String := .left 4
def example2 : Either Int String := .right "foo"

def printExample : Either Int String → String := fun val =>
  match val with
  | .left x => s!"a number: {x}"
  | .right y => y

#eval printExample example1
#eval printExample example2

-- Check the source code for `Option`, and `Except`:
#check Option
#check Except


-- Even more interesting: the type can be used to construct itself:

inductive myNaturalNumber where
  | zero : myNaturalNumber
  | next : myNaturalNumber → myNaturalNumber

open myNaturalNumber
#eval zero
#eval next zero
#eval next (next zero)
#eval next (next (next zero))

def one := next zero
def two := next one
def three := next two

#check Nat  -- Check again the source of Lean
