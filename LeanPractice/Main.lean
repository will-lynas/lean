import Mathlib.Tactic

-- 001
example: 1 + 1 = 2 := by
  ring


-- 002
section q002

variable (A: Type)
variable (P: A -> Prop)
variable (b: A)

example (h: ∀a, P a) : P b := by
  exact h b

end q002
