import Mathlib.Tactic

-- 001
example: 1 + 1 = 2 := by
  ring


-- 002
section q002

example (A: Type) (P : A -> Prop) (b: A) (h: ∀a, P a) : P b := by
  exact h b

end q002
