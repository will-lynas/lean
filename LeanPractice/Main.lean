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
-- This is useful for defining variables for a set of questions, and not polluting the rest of the
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
