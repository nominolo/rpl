-- | Utils for last wishes before dying.
module RPL.Utils.Panic where

import RPL.Utils.Pretty

panic :: PDoc -> a
panic last_wish =
    -- TODO: use some sort of async exceptions?
    error (render last_wish)

expectJust :: String -> Maybe a -> a
expectJust _ (Just x) = x
expectJust msg _ = panic (text "expectJust:" <+> wrappingText msg)
