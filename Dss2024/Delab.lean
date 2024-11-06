import Lean.PrettyPrinter.Delaborator
import Dss2024.Syntax

open Lean PrettyPrinter Delaborator SubExpr Parenthesizer

namespace Imp

def annAsTerm {any} (stx : TSyntax any) : DelabM (TSyntax any) :=
  (⟨·⟩) <$> annotateTermInfo ⟨stx.raw⟩

partial def delabExprInner : DelabM (TSyntax `expr) := do
  let e ← getExpr
  let stx : TSyntax `expr ←
    match_expr e with
    | Expr.const x =>
      match_expr x with
      | OfNat.ofNat _ n _ =>
        if let some n' := n.nat? then
          pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
        else if let .lit (.natVal n') := n then
          pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
        else failure
      | Int.ofNat n =>
        if let some n' := n.nat? then
          pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
        else if let .lit (.natVal n') := n then
          pure <| ⟨Syntax.mkNumLit (toString n') |>.raw⟩
        else failure
      | BitVec.ofNat _ _ => (⟨·.raw⟩) <$> (withAppArg <| withAppArg <| delab)
      | _ => failure
    | Expr.var i => do
      match i with
      | .lit (.strVal s) =>
        let x := mkIdent <| .mkSimple s
        `(expr| $x:ident )
      | _ => failure
    | Expr.plus _ _ =>
      let s1 ← withAppFn <| withAppArg delabExprInner
      let s2 ← withAppArg delabExprInner
      `(expr| $s1 + $s2)
    | Expr.lt _ _ =>
      let s1 ← withAppFn <| withAppArg delabExprInner
      let s2 ← withAppArg delabExprInner
      `(expr| $s1 < $s2)
    | _ => failure
  annAsTerm stx

@[delab app.Imp.Expr.const, delab app.Imp.Expr.var, delab app.Imp.Expr.plus, delab app.Imp.Expr.lt]
partial def delabExpr : Delab := do
  -- This delaborator only understands a certain arity - give up if it's incorrect
  guard <| match_expr ← getExpr with
    | Expr.const _ => true
    | Expr.var _ => true
    | Expr.plus _ _ => true
    | Expr.lt _ _ => true
    | _ => false
  match ← delabExprInner with
  | e => `(term|expr {$(⟨e⟩)})

partial def delabStmtInner : DelabM (TSyntax `stmt) := do
  let e ← getExpr
  let stx ←
    match_expr e with
    | Stmt.skip => `(stmt| skip;)
    | Stmt.seq _ _ =>
      let s1 ← withAppFn <| withAppArg delabStmtInner
      let s2 ← withAppArg delabStmtInner
      `(stmt| $s1 $s2)
    | Stmt.assign i _ =>
      match i with
      | .lit (.strVal s) =>
        let x := mkIdent <| .mkSimple s
        let e ← withAppArg delabExprInner
        `(stmt| $x:ident := $e; )
      | _ => failure
    | Stmt.while _ _ =>
      let c ← withAppFn <| withAppArg delabExprInner
      let body ← withAppArg delabStmtInner
      `(stmt| while ($c) { $body })
    | Stmt.ifThenElse _ _ _ =>
      let c ← withAppFn <| withAppFn <| withAppArg delabExprInner
      let t ← withAppFn <| withAppArg delabStmtInner
      let f ← withAppArg delabStmtInner
      `(stmt| if ($c) { $t } else { $f })
    | _ => failure
  annAsTerm stx

@[delab app.Imp.Stmt.skip, delab app.Imp.Stmt.seq, delab app.Imp.Stmt.while, delab app.Imp.Stmt.assign, delab app.Imp.Stmt.if]
partial def delabStmt : Delab := do
  -- This delaborator only understands a certain arity - bail if it's incorrect
  guard <| match_expr ← getExpr with
    | Stmt.skip => true
    | Stmt.seq _ _ => true
    | Stmt.while _ _ => true
    | Stmt.assign _ _ => true
    | Stmt.ifThenElse _ _ _ => true
    | _ => false
  try match ← delabStmtInner with
    | s => `(term|imp{ $s })
  catch _ => delab
