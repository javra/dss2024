import Dss2024.Eval
import Dss2024.Delab

namespace Imp

inductive BigStep :  Env → Stmt → Env → Prop
  | skip : BigStep σ (imp { skip; }) σ
  | seq : BigStep σ s₁ σ' → BigStep σ' s₂ σ'' → BigStep σ (.seq s₁ s₂) σ''
  | assign: BigStep σ (.assign x e) (σ.set x (eval σ e))
  | ifThenElseFalse :
    eval σ e = 0 →
    BigStep σ s₂ σ' →
    BigStep σ (.ifThenElse e s₁ s₂) σ'
  | ifThenElseTrue :
    eval σ e ≠ 0 →
    BigStep σ s₁ σ' →
    BigStep σ (.ifThenElse e s₁ s₂) σ'
  | whileTrue :
    eval σ e ≠ 0 →
    BigStep σ s σ' →
    BigStep σ' (.while e s) σ'' →
    BigStep σ (.while e s) σ''
  | whileFalse :
    eval σ e = 0 →
    BigStep σ (.while e s) σ

/--
A first simple theorem: `skip` doesn't change the state.
-/
theorem BigStep.skip_pre_eq_post : BigStep σ (imp {skip;}) σ' ↔ (σ = σ') := by
  constructor
  . intro h
    cases h
    rfl
  . intro heq
    rw [heq]
    apply BigStep.skip

def swap : Stmt := imp {
  z := i;
  i := j;
  j := z;
}

theorem swap_swaps (σ σ' : Env) (h : BigStep σ swap σ') :
     σ'.get "i" = σ.get "j" ∧ σ'.get "j" = σ.get "i" := by
  cases h with | seq h' h =>
  cases h'
  cases h with | seq h' h =>
  cases h'
  cases h
  constructor
  · simp [eval]
  · simp [eval]
