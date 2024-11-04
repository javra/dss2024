import Dss2024.Syntax

namespace Imp

/-- Values stored in memory - 32-bit integers -/
abbrev Value := BitVec 32

/-- An environment maps variables names to their values (no pointers) -/
structure Env where
  get : String → Value
deriving Inhabited

namespace Env

/-- Initialize an environment, setting all uninitialized memory to `i` -/
def init (i : Value) : Env where
  get _ := i

/-- Set a value in an environment -/
def set (x : String) (v : Value) (σ : Env) : Env where
  get y := if x == y then v else σ.get y

@[simp]
theorem get_init : (Env.init v).get x = v := by rfl

@[simp]
theorem get_set_same {σ : Env} : (σ.set x v).get x = v := by
  simp [get, set]

@[simp]
theorem get_set_different {σ : Env} : x ≠ y → (σ.set x v).get y = σ.get y := by
  intros
  simp [get, set, *]

end Env

def eval (σ : Env) : Expr → Value
  | Expr.const n => n
  | Expr.var str => σ.get str
  | Expr.plus e₁ e₂ => eval σ e₁ + eval σ e₂
  | Expr.lt e₁ e₂ => if eval σ e₁ < eval σ e₂ then 1 else 0
