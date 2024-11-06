namespace Imp

/- Declare an abstract syntax tree for Imp -/

inductive Expr
  | const (i : BitVec 32)
  | var (n : String)
  | plus (e₁ e₂ : Expr)
  | lt (e₁ e₂ : Expr)

inductive Stmt
  | skip
  | seq (s₁ s₂ : Stmt)
  | assign (n : String) (e : Expr)
  | ifThenElse (e : Expr) (s₁ s₂ : Stmt)
  | while (e : Expr) (s : Stmt)

/- Extend Lean's parser to parse Imp snippets -/

declare_syntax_cat expr
declare_syntax_cat stmt

syntax num : expr
syntax ident : expr
syntax:65 expr:65 "+" expr:66 : expr
syntax:45 expr:45 "<" expr:46 : expr

syntax "skip" "; " : stmt
syntax stmt stmt : stmt
syntax ident " := " expr "; " : stmt
syntax "if" "(" expr ")" "{ " stmt " }" "else" "{ " stmt " }" : stmt
syntax "while" "(" expr ")" "{ " stmt " }" : stmt

syntax "expr" "{ " expr " }" : term
syntax "imp" "{ " stmt " }" : term

open Lean

macro_rules
  | `(expr{$n:num}) => `(Expr.const $(quote n.getNat))
  | `(expr{$i:ident}) => `(Expr.var $(quote i.getId.toString))
  | `(expr{$e₁ + $e₂}) => `(Expr.plus (expr {$e₁}) (expr {$e₂}))
  | `(expr{$e₁ < $e₂}) => `(Expr.lt (expr {$e₁}) (expr {$e₂}))

macro_rules
  | `(imp{skip;}) => `(Stmt.skip)
  | `(imp{$s₁:stmt $s₂:stmt}) => `(Stmt.seq (imp {$s₁}) (imp {$s₂}))
  | `(imp{$i:ident := $e:expr;}) => `(Stmt.assign $(quote i.getId.toString) (expr {$e}))
  | `(imp{if($e) {$s₁} else {$s₂}}) => `(Stmt.ifThenElse (expr {$e}) (imp {$s₁}) (imp {$s₂}))
  | `(imp{while($e){$s}}) => `(Stmt.while (expr {$e}) (imp {$s}))

/-- info: ((Expr.var "x").plus (Expr.var "y")).lt (Expr.var "z") : Expr -/
#guard_msgs in
#check expr { x + y < z }

/-- info: ((Expr.var "x").plus (Expr.var "y")).plus (Expr.var "z") : Expr -/
#guard_msgs in
#check expr { x + y + z }

/-- info: (Stmt.assign "x" (Expr.const 4)).seq
  (Stmt.while ((Expr.var "x").lt (Expr.const 6)) (Stmt.assign "x" ((Expr.var "x").plus (Expr.const 1)))) : Stmt-/
#guard_msgs in
#check imp {
  x := 4;
  while (x < 6) {
    x := x + 1;
  }
}

#check imp {
  if (x < y) {
    min := x;
  } else {
    min := y;
  }
}
