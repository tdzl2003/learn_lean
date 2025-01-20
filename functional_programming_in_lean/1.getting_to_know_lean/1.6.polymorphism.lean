-- learn

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#check (replaceX)

#check replaceX Nat natOrigin

#eval replaceX Nat natOrigin 5

-- 书里这个用不了了
-- #eval replaceX natOrigin 5

-- 自动推导的方法！
#check replaceX _ natOrigin 5

def PPoint.replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

-- 书上这个还是用不了
-- #eval natOrigin.replaceX 5
#eval natOrigin.replaceX _ 5

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

def explicitPrimesUnder10 : MyList Nat :=
  MyList.cons 2 (MyList.cons 3 (MyList.cons 5 (MyList.cons 7 MyList.nil)))

def MyList.length (α : Type) (xs : MyList α) : Nat :=
  match xs with
  | MyList.nil => Nat.zero
  | MyList.cons y ys => Nat.succ (length α ys)

-- 这个却可以自动推导？
#eval explicitPrimesUnder10.length _

-- 书教错了，写法改了，类型参数不用写了

def replaceY (point : PPoint α) (newY : α) : PPoint α :=
  { point with y := newY }

#check replaceY natOrigin 5

def MyList.length1 (xs : MyList α) : Nat :=
  match xs with
  | MyList.nil => Nat.zero
  | MyList.cons y ys => Nat.succ (length α ys)

-- 可以用，但类型是错的？
#eval explicitPrimesUnder10.length1

-- exercises

def MyList.last (xs : MyList α) : Option α :=
  match xs with
  | MyList.nil => none
  | MyList.cons y MyList.nil => some y
  | MyList.cons _ ys => MyList.last ys

#eval explicitPrimesUnder10.last

def MyList.findFirst? (xs : MyList α) (predicate : α → Bool) : Option α :=
  match xs with
  | MyList.nil => none
  | MyList.cons y ys => if predicate y then some y else MyList.findFirst? ys predicate

#eval explicitPrimesUnder10.findFirst? (fun x => x > 5)

def swap(pair : α × β) : β × α :=
  {fst := pair.snd, snd := pair.fst}

#eval swap ({fst:= 1, snd:= 2 : Prod Nat Nat})
#eval swap (1,2)

def PetName : Type := String ⊕ String
