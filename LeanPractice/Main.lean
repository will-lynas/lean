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
