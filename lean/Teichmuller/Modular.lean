import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Teichmuller.Core

namespace Teichmuller

/-!
An abstract modular layer.  The purpose is to make the bridge

  group action -> quotient/moduli object -> invariant function

explicit without importing a large algebraic library in the first pass.
The analytic upper half-plane and the transformation
`(a τ + b) / (c τ + d)` are deferred to a later complex-analytic layer.
-/

structure SL2ZMatrix where
  a : Int
  b : Int
  c : Int
  d : Int
  determinantOne : a * d - b * c = 1

def SL2ZMatrix.det (A : SL2ZMatrix) : Int :=
  A.a * A.d - A.b * A.c

def SL2ZMatrix.identity : SL2ZMatrix where
  a := 1
  b := 0
  c := 0
  d := 1
  determinantOne := by decide

def SL2ZMatrix.mul (A B : SL2ZMatrix) : SL2ZMatrix where
  a := A.a * B.a + A.b * B.c
  b := A.a * B.b + A.b * B.d
  c := A.c * B.a + A.d * B.c
  d := A.c * B.b + A.d * B.d
  determinantOne := by
    calc
      (A.a * B.a + A.b * B.c) * (A.c * B.b + A.d * B.d) -
          (A.a * B.b + A.b * B.d) * (A.c * B.a + A.d * B.c) =
          (A.a * A.d - A.b * A.c) * (B.a * B.d - B.b * B.c) := by
            ring
      _ = 1 := by rw [A.determinantOne, B.determinantOne]; norm_num

@[simp] theorem SL2ZMatrix.det_eq_one (A : SL2ZMatrix) : A.det = 1 :=
  A.determinantOne

theorem SL2ZMatrix.ext {A B : SL2ZMatrix}
    (ha : A.a = B.a) (hb : A.b = B.b)
    (hc : A.c = B.c) (hd : A.d = B.d) : A = B := by
  cases A
  cases B
  simp_all

theorem SL2ZMatrix.identity_mul (A : SL2ZMatrix) :
    SL2ZMatrix.mul SL2ZMatrix.identity A = A := by
  apply SL2ZMatrix.ext <;> simp [SL2ZMatrix.mul, SL2ZMatrix.identity]

theorem SL2ZMatrix.mul_identity (A : SL2ZMatrix) :
    SL2ZMatrix.mul A SL2ZMatrix.identity = A := by
  apply SL2ZMatrix.ext <;> simp [SL2ZMatrix.mul, SL2ZMatrix.identity]

theorem SL2ZMatrix.mul_assoc (A B C : SL2ZMatrix) :
    SL2ZMatrix.mul (SL2ZMatrix.mul A B) C =
      SL2ZMatrix.mul A (SL2ZMatrix.mul B C) := by
  apply SL2ZMatrix.ext <;> simp [SL2ZMatrix.mul] <;> ring

structure MonoidSpec (G : Type) where
  one : G
  mul : G → G → G
  one_mul : ∀ g, mul one g = g
  mul_one : ∀ g, mul g one = g
  mul_assoc : ∀ g h k, mul (mul g h) k = mul g (mul h k)

def SL2ZMatrix.monoidSpec : MonoidSpec SL2ZMatrix where
  one := SL2ZMatrix.identity
  mul := SL2ZMatrix.mul
  one_mul := SL2ZMatrix.identity_mul
  mul_one := SL2ZMatrix.mul_identity
  mul_assoc := SL2ZMatrix.mul_assoc

structure ActionSpec (G X : Type) (M : MonoidSpec G) where
  act : G → X → X
  one_act : ∀ x, act M.one x = x
  mul_act : ∀ g h x, act (M.mul g h) x = act g (act h x)

/-- A function invariant under a specified monoid action. -/
structure ModularFunction (G X : Type) (Y : Type*) (M : MonoidSpec G)
    (A : ActionSpec G X M) where
  toFun : X → Y
  invariant : ∀ g x, toFun (A.act g x) = toFun x

def ModularFunction.eval {G X : Type} {Y : Type*} {M : MonoidSpec G}
    {A : ActionSpec G X M} (f : ModularFunction G X Y M A) (x : X) : Y :=
  f.toFun x

theorem ModularFunction.one_invariant {G X Y : Type} {M : MonoidSpec G}
    {A : ActionSpec G X M} (f : ModularFunction G X Y M A) (x : X) :
    f.toFun (A.act M.one x) = f.toFun x :=
  f.invariant M.one x

end Teichmuller
