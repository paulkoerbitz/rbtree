module Data.RbTree

%default total

data Color = Red | Black

data RbTree : Color -> Nat -> Type -> Type where
  Leaf      : RbTree Black Z a
  RedNode   : RbTree Black n a -> a -> RbTree Black n a -> RbTree Red n a
  BlackNode : RbTree c1 n a -> a -> RbTree c2 n a -> RbTree Black (S n) a

depth : RbTree c n a -> Nat
depth Leaf              = Z
depth (RedNode l x r)   = S (max (depth l) (depth r))
depth (BlackNode l x r) = S (max (depth l) (depth r))
