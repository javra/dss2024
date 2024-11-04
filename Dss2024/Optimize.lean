import Dss2024.Eval

namespace Imp

def optimize : Expr → Expr
 | .const i => .const i
 | .var x => .var x
 | .lt x y =>
  match optimize x, optimize y with
  | .const i, .const j => if i < j then .const 1 else .const 0
  | _, _ => .lt x y
 |.plus x y =>
  match optimize x, optimize y with
  | .const i, .const j => .const (i + j)
  | _, _ => .plus x y

theorem optimize_correct (σ : Env) : eval σ (optimize e) = eval σ e := by
  induction e
  case const =>
    simp [optimize]
  case var =>
    simp [optimize]
  case lt ih₁ ih₂ =>
    simp [optimize]
    split
    case h_1 he₁ he₂ =>
      simp [eval, ← ih₁, ← ih₂, he₁, he₂]
      split <;> rfl
    case h_2 =>
      rfl
  case plus =>
    simp [optimize]
    split
    · simp_all only
      simp_all [eval]
    · rfl
