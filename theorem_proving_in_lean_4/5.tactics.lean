-- 使用tactics重写前两章练习题
namespace Exercise3_1
  variable (p q r : Prop)

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p := sorry
  example : p ∨ q ↔ q ∨ p := sorry

  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := sorry
  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := sorry

  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := sorry
  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
  example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
  example : ¬(p ∧ ¬p) := sorry
  example : p ∧ ¬q → ¬(p → q) := sorry
  example : ¬p → (p → q) := sorry
  example : (¬p ∨ q) → (p → q) := sorry
  example : p ∨ False ↔ p := sorry
  example : p ∧ False ↔ False := sorry
  example : (p → q) → (¬q → ¬p) := sorry
end Exercise3_1


namespace Exercise3_2
  open Classical

  variable (p q r : Prop)

  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := sorry
  example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
  example : ¬(p → q) → p ∧ ¬q := sorry
  example : (p → q) → (¬p ∨ q) := sorry
  example : (¬q → ¬p) → (p → q) := sorry
  example : p ∨ ¬p := sorry
  example : (((p → q) → p) → p) := sorry
end Exercise3_2

namespace Exercise4_1
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := sorry
  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

end Exercise4_1

namespace Exercise4_2
  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ x : α, r) ↔ r) := sorry
  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry
end Exercise4_2

namespace Exercise4_3
  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := sorry
end Exercise4_3

namespace Exercise4_5
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : (∃ x : α, r) → r := sorry
  example (a : α) : r → (∃ x : α, r) := sorry
  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := sorry
  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := sorry

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := sorry
  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := sorry
  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := sorry
  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := sorry
  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := sorry
  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := sorry

end Exercise4_5
