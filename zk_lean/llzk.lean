import Main

/-
  This file contains WIP & experimental code for an embedding of LLZK in Lean
  with a view towards integration with zkLean. In particular, there are:

   - simple example zkLean circuits similar to those in Main.lean

   - a isZero circom example from LLZK's FrontendLang tests that was hand
   translated into zkLean

   - a Lean type def for LLZK expressions (WIP)

  More to come ...

-/

/-- 

  Simple zkLean circuits (see Main.lean)

--/

-- How to do this for another field?
def testEq : ZKBuilder (ZMod 7) PUnit := do
  let a <- Witnessable.witness
  let b <- Witnessable.witness
  ZKBuilder.constrainEq a b

#eval run_circuit' testEq [1, 0] -- false
#eval run_circuit' testEq [1, 8] -- true
#eval run_circuit' testEq [9, 8] -- false

def testR1CS : ZKBuilder (ZMod 7) PUnit := do
  let a <- Witnessable.witness
  let b <- Witnessable.witness
  ZKBuilder.constrainR1CS a 0 b

#eval run_circuit' testR1CS [1, 0] -- false
#eval run_circuit' testR1CS [1, 8] -- true
#eval run_circuit' testR1CS [9, 8] -- false

def constrainEq {f} [ZKField f] (a b : ZKExpr f) : ZKBuilder f PUnit := do
  -- why is this a = b?
  ZKBuilder.constrainR1CS a 1 b

/-- 

  zkLean version of LLZK @IsZero, see:
  https://github.com/Veridise/llzk-lib/blob/main/test/FrontendLang/Circom/circomlib.llzk

--/

-- LLZK passes on the isZero circuit generates two defs, a compute def and a
-- constrain def. LLZK performs both witness generation and circuit correctness
-- checks. However zkLean supports primarily checking the correctness of the
-- circuit, not so much witness generation. Thus, the focus on LLZK in zkLean
-- should be on the constrain side. 

-- @IsZero, function.def @compute
-- This may not be possible to test due to zkLean's lack of witness generation
-- support.
def isZeroCompute {f} [ZKField f] (input : ZKExpr f) : ZKBuilder f (ZKExpr f) := do 
  let one    : ZKExpr f := ZKExpr.Literal 1
  let inv    : ZKExpr f := input
  let tmp4   : ZKExpr f := ZKExpr.Neg inv
  let tmp5   : ZKExpr f := ZKExpr.Mul tmp4 inv
  let output : ZKExpr f := ZKExpr.Add tmp5 one
  return output

-- @IsZero, function.def @constrain ...
-- This seems pretty good so far, consider lean-mlir for outputing below
def isZeroConstrain {f} [ZKField f] : ZKBuilder f PUnit := do
  -- %in
  let input   : ZKExpr f <- Witnessable.witness
  -- %out
  let output  : ZKExpr f <- Witnessable.witness
  -- %inv
  let inv     : ZKExpr f <- Witnessable.witness
  -- const_0
  let const_0 : ZKExpr f := ZKExpr.Literal 0
  -- const_1
  let const_1 : ZKExpr f := ZKExpr.Literal 0
  -- %4
  let tmp4    : ZKExpr f := ZKExpr.Neg input
  -- %5
  let tmp5    : ZKExpr f := ZKExpr.Mul tmp4 inv
  -- %6
  let tmp6    : ZKExpr f := ZKExpr.Add tmp5 const_1
  --
  ZKBuilder.constrainEq output tmp6
  -- %7
  let tmp7    : ZKExpr f := ZKExpr.Mul input output
  --
  ZKBuilder.constrainEq tmp7 const_0

-- Testing isZeroConstrain above
def testZeroConstrain : ZKBuilder (ZMod 7) PUnit := do
  -- %in
  let input : ZKExpr (ZMod 7) <- Witnessable.witness
  -- %out
  let output: ZKExpr (ZMod 7) <- Witnessable.witness
  -- %inv
  let inv   : ZKExpr (ZMod 7) <- Witnessable.witness
  -- const_0
  let zero  : ZKExpr (ZMod 7) := ZKExpr.Literal 0
  -- const_1
  let one   : ZKExpr (ZMod 7) := ZKExpr.Literal 0
  -- %4
  let tmp4  : ZKExpr (ZMod 7) := ZKExpr.Neg input
  -- %5
  let tmp5  : ZKExpr (ZMod 7) := ZKExpr.Mul tmp4 inv
  -- %6
  let tmp6  : ZKExpr (ZMod 7) := ZKExpr.Add tmp5 one
  --
  ZKBuilder.constrainEq output tmp6
  -- %7
  let tmp7  : ZKExpr (ZMod 7) := ZKExpr.Mul input output
  --
  ZKBuilder.constrainEq tmp7 zero

-- Order of witnesses should follow the order in which they appear.
-- Is this the expected behaviour?
#eval run_circuit' testZeroConstrain [0, 0, 0]
#eval run_circuit' testZeroConstrain [0, 0, 0] 
#eval run_circuit' testZeroConstrain [4, 0, 0]

--------------------------
--                      --
--    LLZK type defs    --
--                      --
--------------------------

/-- 2025-11-11 LLZK Lang type documentation (https://veridise.github.io/llzk-lib/main/syntax.html)

    bool:   subtype of Felt in [0,1]
    int:    machine integer
    Felt:   finite field element

    struct (component): Aggregate type with named heterogeneous elements.
    Generally correlates to components/functions in the source language.
    Constituent elements may be local variables, subcomponents, and/or called
    functions.

    array<E>: elements can be any type, including other array type for
    multi-dimensional arrays. We may need this type to have a built-in field
    named len that returns the length of the array.

    const<T>: modifier on types to denote it’s a compile-time constant.
    Semantic analysis can infer const based on usage of literal values, etc.
    but it can also be specified in the IR in which case the semantic analysis
    must ensure it’s correct or give an error. The semantics of several syntax
    nodes require a const value, such as the i in GetWeight<i>.compute().
    Global function return type can be const and that would allow such a
    function to be used in these locations.
--/

inductive LLZKExpr (f : Type) where
  | Felt  : (elt : f)    -> LLZKExpr f -- field element
  | Int   : (uint : Int) -> LLZKExpr f
  -- Bool should be a subtype of f restricted to 1 or 0
  | Bool  : (bool : f)   -> LLZKExpr f
  -- LLZK Documentation says array should take any LLZK type
  | Array : (array : Array (LLZKExpr f)) -> LLZKExpr f
  -- Not sure what the LLZK const type does but putting in f for now
  | Const : (c : f) -> LLZKExpr f
  -- Arithmetic
  | Add : (lhs rhs : LLZKExpr f) -> LLZKExpr f
  | Sub : (lhs rhs : LLZKExpr f) -> LLZKExpr f
  | Mul : (lhs rhs : LLZKExpr f) -> LLZKExpr f
  | Neg : (arg     : LLZKExpr f) -> LLZKExpr f

-- LLZKExpr f inherits the default value of f assuming f is inhabited
instance [Inhabited f] : Inhabited (LLZKExpr f) where
  default := LLZKExpr.Felt default

-- Enable use of nat numerals 
instance [OfNat f n] : OfNat (LLZKExpr f) n where
  ofNat := LLZKExpr.Felt (OfNat.ofNat n)

instance [Zero f] : Zero (LLZKExpr f) where
  zero := LLZKExpr.Felt 0

-- overload "+" operator
instance: HAdd (LLZKExpr f) (LLZKExpr f) (LLZKExpr f) where
  hAdd := LLZKExpr.Add

instance: HSub (LLZKExpr f) (LLZKExpr f) (LLZKExpr f) where
  hSub := LLZKExpr.Sub

instance: HMul (LLZKExpr f) (LLZKExpr f) (LLZKExpr f) where
  hMul := LLZKExpr.Mul

-- overload "-" in "- x"
instance: Neg (LLZKExpr f) where
  neg := LLZKExpr.Neg

-- What does this do?
instance: Add (LLZKExpr f) where
  add := LLZKExpr.Add

#eval  (LLZKExpr.Add 0 0 : LLZKExpr (ZMod 7))
#eval  (LLZKExpr.Add 1 1 : LLZKExpr (ZMod 7))
#eval  (LLZKExpr.Neg 1 : LLZKExpr (ZMod 7))
#eval  (- 1 : LLZKExpr (ZMod 7))
#eval  (1 - 1 : LLZKExpr (ZMod 7))
#eval  (1 + 1 : LLZKExpr (ZMod 7))
#eval  (1 * 1 : LLZKExpr (ZMod 7))
#check (1 * 0 : LLZKExpr (ZMod 7))
