Inductive NExpr: Type :=
| NVar  : nat -> NExpr (* using Bruijn indices *)
| NConst: nat -> NExpr
| NPlus : NExpr -> NExpr -> NExpr
| NMinus: NExpr -> NExpr -> NExpr
| NMult : NExpr -> NExpr -> NExpr
| NLam: NExpr -> NExpr
| NApp: NExpr -> NExpr -> NExpr.
