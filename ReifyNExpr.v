Require Import Template.All.

Import MonadNotation.

Require Import NExpr.

Example Ex1 (a b c x: nat) := (fun x' => a*x'*x' + b*x' + c) x.

Definition test: TemplateMonad unit :=
  e <- tmEval cbv Ex1 ;;
    q <- tmQuote e ;;
    tmPrint q ;;
    tmReturn tt.

Run TemplateProgram test.

