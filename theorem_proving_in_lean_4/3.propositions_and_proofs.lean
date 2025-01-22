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
    fun h => fun h1 => h h1.left h1.right,
    fun h => fun h1 => fun h2 => h (And.intro h1 h2),
  ⟩

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
  ⟨
    fun h => And.intro (fun hp => h (Or.intro_left q hp)) (fun hq => h (Or.intro_right p hq)),
    fun h => fun h1 => Or.elim h1 h.left h.right
  ⟩

example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
  ⟨
    fun h => And.intro
      (Not.imp h (Or.intro_left q))
      (Not.imp h (Or.intro_right p)),
    fun h => Not.intro (λh1 => Or.elim h1
      (λh2 => h.left h2)
      (λh2 => h.right h2)
    )
  ⟩

example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    fun h => Or.elim h
      (fun h1 => Not.imp h1 And.left)
      (fun h1 => Not.imp h1 And.right)

example : ¬(p ∧ ¬p) :=
  Not.intro (fun h => Not.elim h.right h.left)

example : ¬(p ∧ ¬p) :=
  Not.intro (fun h => absurd h.left h.right)

example : ¬(p ∧ ¬p) :=
  Not.intro (fun h => False.elim (h.right h.left))

example : ¬(p ∧ ¬p) :=
  Not.intro (fun h => h.right h.left)

example : p ∧ ¬q → ¬(p → q) :=
  fun h => Not.intro (fun h1 => h.right (h1 h.left))

example : ¬p → (p → q) :=
  fun h => fun h1 => Not.elim h h1

example : (¬p ∨ q) → (p → q) :=
  fun h => Or.elim h
    (fun h1 => fun h2 => Not.elim h1 h2)
    (fun h1 => fun _ => h1)

example : p ∨ False ↔ p :=
  ⟨
    fun h => Or.elim h
      (fun h1 => h1)
      (fun h1 => h1.rec),
    Or.intro_left False
  ⟩

example : p ∧ False ↔ False :=
  ⟨
    fun h => h.right,
    fun h => h.rec
  ⟩

example : (p → q) → (¬q → ¬p) :=
    fun h => fun h1 => Not.imp h1 h


open Classical

variable (p q r : Prop)

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) :=
  fun h => Or.elim (Classical.em p)
    (
      fun hp => Or.elim (h hp)
        (fun hq => Or.intro_left (p→r) (fun (_:p) => show q from hq))
        (fun hr => Or.intro_right (p→q) (fun (_:p) => show r from hr))
    )
    (
      fun hnp => Or.intro_left (p→r) (fun hp => absurd hp hnp)
    )

example : ¬(p ∧ q) → ¬p ∨ ¬q := Classical.not_and_iff_or_not_not.mp

example : ¬(p → q) → p ∧ ¬q :=
  fun h =>
    And.intro
      (
        Or.elim (Classical.em p)
          id
          (fun hnp => absurd (fun hp => absurd hp hnp) h)
      )
      (
        Or.elim (Classical.em q)
          (fun hq => absurd (fun _ => hq) h)
          id
      )

example : (p → q) → (¬p ∨ q) :=
  fun h =>
    Or.elim (Classical.em p)
      (fun h1 => Or.inr (h h1))
      Or.inl

example : (¬q → ¬p) → (p → q) :=
  fun h =>
    Or.elim (Classical.em q)
      (fun h1 => fun _ => h1)
      (fun hnq => fun hp => absurd hp (h hnq))


example : p ∨ ¬p := em p

example : (((p → q) → p) → p) :=
  fun h =>
    Or.elim (em p)
      (fun hp => hp)
      (fun hnp => h (fun hp => absurd hp hnp))
