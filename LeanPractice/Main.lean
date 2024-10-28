import Mathlib.Tactic

-- 001
-- Let's first check that we can access Mathlib tactics
example: 1 + 1 = 2 := by
  ring


-- 002
-- This explores the different ways to use ∀
section q002

variable (A: Type)
variable (P: A -> Prop)
variable (b: A)

-- 002a
-- One way to solve this is to use `exact`
-- `h b` gives `b` to the `∀` so we end up with `P b`
-- Then we use `exact` because this exactly matches the goal
example (h: ∀a, P a) : P b := by
  exact h b

-- 002b
-- Another way is to use `apply`
-- Here lean works out what it should use for `a`
example (h: ∀a, P a) : P b := by
  apply h

  -- This also works:
  -- apply h a

-- 002c
-- There's also `specialize`
-- We give `b` to `h`
-- Then `exact` to close the goal
example (h: ∀a, P a) : P b := by
  specialize h b
  -- Now h is `P b`
  exact h

end q002


-- 003
-- Specialize can be used both for `∀` and for implies
-- See 002 for `∀` usage
section q003

variable (P Q R: Prop)

variable (h1: P -> Q)
variable (h2: Q -> R)

-- 003a
-- Here is an example of bringing a goal backwards using `apply`
example (p: P): R := by
  apply h2
  apply h1
  exact p

-- 003b
-- Or more compactly ...
example (p: P): R := by
  exact h2 (h1 p)

-- 003c
-- Instead, you can bring the hypotheses forwards to meet the goal using `specialize`
example (p: P): R := by
  specialize h1 p
  specialize h2 h1
  exact h2

end q003


-- 004
-- `section`s let you make a scope
-- If you declare a variable inside a `section`, when the section ends it disappears
-- This is useful for defining variables for a set of questions, without polluting the rest of the
-- file

section q004

-- P is not defined yet
variable (P: Prop)
variable (p: P)

-- P is now defined and can be used
example: P := by
  exact p

end q004
-- Now P has gone out of scope and can't be seen / used


-- 005
-- Comments

-- Single line comments start with `--` like this

/-
  Multi line comments start with `/-` and end with `-/` like this
-/


-- 006
-- `trans`
section q006

-- 006a
-- `≃` is typed `equiv`
-- Works on any equivalence relation
-- And more ...
example (α β γ: Type) (h1: α ≃ β) (h2: β ≃ γ): α ≃ γ := by
  -- Give `trans` the thing you want to split on
  trans β
  -- Now there are two goals
  exact h1
  exact h2

-- 006b
example (a b c: ℕ) (h1: a = b) (h2: b = c): a = c := by
  trans b
  exact h1
  exact h2

-- 006c
example (a b c: ℕ) (h1: a ≤ b) (h2: b ≤ c): a ≤ c := by
  trans b
  exact h1
  exact h2

-- 006d
example (a b c: ℕ) (h1: a < b) (h2: b < c): a < c := by
  trans b
  exact h1
  exact h2

-- If we have a mix of lt and le, we have to use something else ...

end q006


-- 007

-- You can use these two, but trans works too:

#check le_trans
-- a ≤ b → b ≤ c → a ≤ c
#check lt_trans
-- a < b → b < c → a < c

-- Notice how these next ones are named
-- lt means <
-- le means ≤
-- Then it goes <goal>_of_<first>_of_<second>
-- These ones can't be replaced with trans

#check lt_of_le_of_lt
-- a < b → b < c → a < c
#check lt_of_lt_of_le
-- a < b → b ≤ c → a < c


-- 008
-- This one comes up a fair amount in analysis

-- 008a
-- This works for real numbers
example (a b : ℝ) (h: a < b) : a ≤ b := by
  exact le_of_lt h

-- 008b
-- ... and obviously for natural numbers too
example (a b : ℕ) (h: a < b) : a ≤ b := by
  exact le_of_lt h

-- 008c
-- For natural numbers, there's also another weird way which exact? finds
-- a < b → a.succ ≤ b → a ≤ b
example (a b : ℕ) (h: a < b) : a ≤ b := by
  exact Nat.le_of_succ_le h


-- 009
-- This comes up in analysis too
example (a: ℝ) (h: a > 0): |a| = a := by
  exact abs_of_pos h


-- 010
-- Triangle inequality
example (a b: ℝ): |a + b| ≤ |a| + |b| := by
  exact abs_add_le a b

-- 011
-- Another kind of triangle inequality

-- 011a
-- Mathlib has a way
example (a b c: ℝ): |a - c| ≤ |a - b| + |b - c| := by
  exact abs_sub_le a b c

-- 011b
-- It's also fun to try it yourself
example (a b c: ℝ): |a - c| ≤ |a - b| + |b - c| := by
  calc
    _  = |(a - b) + (b - c)| := by ring
    _  ≤ _ := abs_add_le (a-b) (b-c)


-- 012
-- `by exact` is an antipattern and should be removed

-- We can rewrite 011a:
example (a b c: ℝ): |a - c| ≤ |a - b| + |b - c| := abs_sub_le a b c

-- But this is more relevant to calc blocks


-- 013
-- `refine`
-- `refine` is `exact` with "holes"
-- See https://www.ma.imperial.ac.uk/~buzzard/xena/formalising-mathematics-2023/Part_C/tactics/refine.html
-- The above link is for lean3, so there are some slight differences you should be aware of
section q013

variable (P Q R : Prop)
variable (p : P)
variable (q : Q)
variable (r : R)

-- 013a
example: P ∧ Q := by
  -- Here we fill in the left part of the ∧ and turn the right into a new goal
  -- Use `?_` for any "holes"
  -- IMPORTANT: in lean3 you would write `_`, but now you write `?_`
  refine ⟨p, ?_⟩
  exact q

-- 013b
-- 013a is obviously contrived. We could've just used `exact` immediately
example: P ∧ Q := by
  exact ⟨p, q⟩

-- 013c
-- `refine` is helpful when you would otherwise have a constructor with one arm that is just `exact`
-- Here's the bad way
example: P ∧ (Q ∧ R) := by
  -- (Could've done this all in one `exact` but this is to demo)
  constructor
  · exact p
  · exact ⟨q, r⟩

-- 013d
-- ... and here's a better way with `refine`
-- No nesting!
example: P ∧ (Q ∧ R) := by
  refine ⟨p, ?_⟩
  exact ⟨q, r⟩

-- 013e
-- You can also name the subgoals that get created
example: P ∧ (Q ∧ R) := by
  refine ⟨p, ⟨?h1, ?h2⟩⟩
  -- Now the inspector looks like this:
  /-
  case h1
  P Q R : Prop
  p : P
  q : Q
  r : R
  ⊢ Q

  case h2
  P Q R : Prop
  p : P
  q : Q
  r : R
  ⊢ R
  -/
  exact q
  exact r

-- 013f
-- A less contrived example
example (S T U: Prop) (t: T): S → S ∧ (U → (T ∧ U)) := by
  intro s
  refine ⟨s, ?_⟩
  intro u
  exact ⟨t, u⟩

end q013
