-- learn

def hello := "Hello"

#eval hello

def lean: String := "Lean"

#eval String.append hello (String.append "" lean)

def add1 (n: Nat) : Nat := n+1
-- def add1 (n) := n+1
-- def add1 (n: Int) := n+1

#eval add1 7

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then k else n

#eval maximum (5+8) (2*7)

-- exercises

def joinStringsWith(s1: String)(s2: String)(s3: String) :=
  String.append s2 (String.append s1 s3)

#eval joinStringsWith ", " "one" "and another"

#check joinStringsWith ": "

def volume(height: Nat)(width: Nat)(depth: Nat) :=
  height * width * depth

#eval volume 2 3 4

-- learn

def Str := String

def aStr : Str := "This is a string"
