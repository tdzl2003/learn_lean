-- learn
#check 1.2

-- 高精度？假的，后面就没了
#check -12345678901234567890123456.78901234567890123456789012345678901234567890

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }

#eval origin
#eval origin.x + origin.y

-- 没有高精度
#eval ({ x := -6.123567890123456, y := 32.200000 }:Point)

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }

structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

#check { x := 0.0, y := 0.0 : Point}

-- def zeroX (p : Point) : Point :=
--   { x := 0, y := p.y }
def zeroX (p : Point) : Point :=
  { p with x := 0 }

#eval zeroX { x := -6.123567890123456, y := 32.200000 }

#check Point.mk 1.5 2.8

#eval "one string".append " and another"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }

#eval fourAndThree.modifyBoth Float.floor

#eval Point.modifyBoth Float.floor fourAndThree

-- look this
#check fourAndThree.modifyBoth

-- exercise

structure RectangularPrism where
  width: Float
  height: Float
  depth: Float
deriving Repr

def volume (self:RectangularPrism) :=
  self.width * self.height * self.depth

#eval volume (RectangularPrism.mk 2 3 4)

structure Segment where
  p0: Point
  p1: Point
deriving Repr

def Segment.length (self: Segment) :=
  distance self.p0 self.p1

def s0 := Segment.mk { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }

#eval s0
#eval s0.length

-- names:
#check RectangularPrism.mk
#check RectangularPrism.width
#check RectangularPrism.height
#check RectangularPrism.depth

structure Hamster where
  name : String
  fluffy : Bool

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

-- names:
#check Hamster.mk
#check Hamster.name
#check Hamster.fluffy

#check Book.makeBook
#check Book.title
#check Book.author
#check Book.price
