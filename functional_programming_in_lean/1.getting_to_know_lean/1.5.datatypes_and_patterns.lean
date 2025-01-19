
-- learn

-- VSCode点进去看看每个类型！
def b: Bool := true
def n: Nat := 0
def i: Int := 0
def f: Float := 0.2

#eval Nat.zero == 0
#eval Nat.succ Nat.zero

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

structure Complex where
  real: Float
  imag: Float
deriving Repr

-- 不能这么做： match只能做结构或类型的匹配？
-- def Complex.isReal (v: Complex) :=
--   match v with
--     | {real:= r, imag:= Float.zero} => true
--     | {real:=r, imag:=t} => false

-- 可以这么做：
def isBig (n: Nat) :=
  match n with
  | Nat.zero => false
  | Nat.succ (Nat.succ k) => true
  | _ => false

#eval isBig 0
#eval isBig 1
#eval isBig 2

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')

#eval plus 3 2

-- def div (n : Nat) (k : Nat) : Nat :=
--   if n < k then
--     0
--   else Nat.succ (div (n - k) k)

-- def div (n k : Nat) (ok : k > 0) : Nat :=
--   if h : n < k then
--     0
--   else
--     1 + div (n - k) k ok
-- termination_by div n k ok => n

def div (n k : Nat) (ok : k > 0) : Nat :=
  if h : n < k then
    0
  else
    have : 0 < n := by
      cases n with
      | zero => contradiction
      | succ n' => simp_arith
    have : n - k < n := by
      apply Nat.sub_lt <;> assumption
    1 + div (n - k) k ok
termination_by n

#eval Nat.div 4 2
