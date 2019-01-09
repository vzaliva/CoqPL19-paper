Require Import Coq.Lists.List.
Require Import ExtLib.Structures.Monads.
Require Import ExtLib.Data.Monads.OptionMonad.

Require Import NExpr.

Import MonadNotation.
Open Scope monad_scope.

Definition evalContext:Type := list nat.

Fixpoint evalNexp (Γ:evalContext) (e:NExpr): option nat :=
  match e with
  | NVar i => nth_error Γ i
  | NConst c => Some c
  | NPlus a b => liftM2 Nat.add (evalNexp Γ a) (evalNexp Γ b)
  | NMinus a b => liftM2 Nat.sub (evalNexp Γ a) (evalNexp Γ b)
  | NMult a b => liftM2 Nat.mul (evalNexp Γ a) (evalNexp Γ b)
  end.
