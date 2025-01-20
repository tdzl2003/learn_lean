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

-- 书教错了，写法改了，泛型参数用 {} 在下一章讲了

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


inductive PetName : Type where
  | inl (val : String) : PetName
  | inr (val : String) : PetName

def animals : List PetName :=
  [PetName.inl "Spot", PetName.inr "Tiger", PetName.inl "Fifi", PetName.inl "Rex", PetName.inr "Floof"]

def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | List.nil => List.nil
  | x::xs => match ys with
    | List.nil => List.nil
    | y::ys => (x,y)::(zip xs ys)

#eval zip [1,2,3] [4,5,6,7,8]

def take {α: Type} (list: List α) (n: Nat): List α :=
  match n with
    | 0 => List.nil
    | n+1 => match list with
        | List.nil => List.nil
        | x :: xs => x :: (take xs n)

#eval take [1,2,3,4,5] 5

def products_over_sum {α β γ : Type} (n: α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  match n.snd with
    | Sum.inl b => Sum.inl (n.fst, b)
    | Sum.inr r => Sum.inr (n.fst, r)

def multication_by_two {α: Type} (n: Bool × α) : α ⊕ α :=
  match n.fst with
    | true => Sum.inl n.snd
    | false => Sum.inr n.snd
