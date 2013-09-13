module HERMIT.Primitive.WorkerWrapper.Common where

import HERMIT.Monad
import HERMIT.Kure
import HERMIT.GHC

--------------------------------------------------------------------------------------------------

data WWAssumptionTag = A | B | C deriving (Eq,Ord,Show,Read)
data WWAssumption = WWAssumption WWAssumptionTag (RewriteH CoreExpr)

--------------------------------------------------------------------------------------------------

-- Note: The current approach to WW Fusion is a hack.
-- I'm not sure what the best way to approach this is though.
-- An alternative would be to have a generate command that adds ww-fusion to the dictionary, all preconditions verified in advance.
-- That would have to exist at the Shell level though.

-- This isn't entirely safe, as a malicious the user could define a label with this name.
workLabel :: Label
workLabel = "recursive-definition-of-work-for-use-by-ww-fusion"

--------------------------------------------------------------------------------------------------
