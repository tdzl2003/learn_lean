variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
      show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
      show p ∧ q from And.intro (And.right h) (And.left h))

example : p ∧ q ↔ q ∧ p :=
  ⟨
    (fun h : p ∧ q =>
      show q ∧ p from And.intro (And.right h) (And.left h)),
    (fun h : q ∧ p =>
      show p ∧ q from And.intro (And.right h) (And.left h))
  ⟩

example : p ∧ q ↔ q ∧ p :=
  have and_swap{u v: Prop} : u∧v → v∧u :=
    fun h:u∧v  => show v∧u from And.intro (And.right h) (And.left h)
  ⟨and_swap, and_swap⟩

example : p ∨ q ↔ q ∨ p :=
  have or_swap(u v: Prop) : u∨v → v∨u :=
    fun h:u∨v => show v∨u from Or.elim h (Or.intro_right v) (Or.intro_left u)
  ⟨or_swap p q, or_swap q p⟩

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
  ⟨
    fun h => And.intro (h.left.left) (And.intro h.left.right h.right),
    fun h => And.intro (And.intro h.left h.right.left) h.right.right
  ⟩

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
  ⟨
    fun h => Or.elim h (fun h1 => Or.elim h1
      (Or.intro_left (q∨r))
      (fun h2 => Or.intro_right p (Or.intro_left r h2))
    ) fun h2 => Or.intro_right p (Or.intro_right q h2),
    fun h => Or.elim h (fun h1 => Or.intro_left r (Or.intro_left q h1)) (
      fun h1 => Or.elim h1 (fun h2 => Or.intro_left r (Or.intro_right p h2)) (Or.intro_right (p∨q))
    )
  ⟩

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
  ⟨
    fun h => Or.elim h.right
      (λh2 => Or.intro_left (p∧r) (And.intro h.left h2))
      (λh2 => Or.intro_right (p∧q) (And.intro h.left h2)),
    fun h => Or.elim h
      (λh1 => And.intro h1.left (Or.intro_left r h1.right))
      (λh1 => And.intro h1.left (Or.intro_right q h1.right))
  ⟩

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
  ⟨
    fun h => Or.elim h
      (λh1 => And.intro (Or.intro_left q h1) (Or.intro_left r h1))
      (λh2 => And.intro (Or.intro_right p h2.left) (Or.intro_right p h2.right)),
    fun h => Or.elim h.left
      (Or.intro_left (q∧r) )
      (λh1 => Or.elim h.right (Or.intro_left (q∧r))
        (λh2 => Or.intro_right p (And.intro h1 h2))
      )
  ⟩

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
  ⟨
    fun h => sorry,
    sorry,
  ⟩
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
