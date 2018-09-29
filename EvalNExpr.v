Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Require Import NExpr.

Import MonadNotation.
Open Scope monad_scope.

Definition evalContext:Type := list nat.

Fixpoint evalNexp (st:evalContext) (e:NExpr): option nat :=
  match e with
  | NVar i => nth_error st i
  | NConst c => Some c
  | NPlus a b => liftM2 Nat.add (evalNexp st a) (evalNexp st b)
  | NMinus a b => liftM2 Nat.sub (evalNexp st a) (evalNexp st b)
  | NMult a b => liftM2 Nat.mul (evalNexp st a) (evalNexp st b)
  | NLam body => None (* top-level lambda not allowed *)
  | NApp (NLam body) p => v <- evalNexp st p ;; evalNexp (v :: st) body
  | NApp _ p => None (* applying non-lambda *)
  end.
