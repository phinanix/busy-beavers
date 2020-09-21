module Util where

import Relude

showInt3Wide :: Int -> Text
showInt3Wide i@((\i -> i < 10) -> True) = "  " <> show i
showInt3Wide i@((\i -> i < 100) -> True) = " " <> show i
showInt3Wide i = show i

bind :: Monad m => (a -> m b) -> m a -> m b
bind = flip (>>=)
