module RPL.Typecheck.GrTy.Constraint where

import RPL.Typecheck.GrTy.Types

------------------------------------------------------------------------

-- | The origin and role of a constraint.
--
-- E.g., \"ensure that both if-branches have the same type\".
--
-- TODO: implement this
type ConstrOrigin = ()

-- | The type of a constaint.  Currently only unification and instantiation
-- constraints are supported.  Eventually we'd like to have instance
-- constraints as well.
data ConstrEdgeType = Unify | Inst deriving (Eq, Show)

-- | A constraint.  Constraints a binary and relate two types; hence they
-- can be represented by a single (possibly directed) edge in the graphical
-- type.
data ConstrEdge = ConstrEdge
  { cedge_type   :: ConstrEdgeType
  , cedge_origin :: ConstrOrigin
    -- ^ The source code origin of the frame and its role.  
  , cedge_from   :: Node
  , cedge_to     :: Node
  } deriving (Eq, Show)

-- | All the constraints in a type checking unit.
data ConstraintStore = ConstraintStore
  { cstore_root         :: Node
  , cstore_constraints  :: [ConstrEdge]
  , cstore_existentials :: [Node]
  } deriving (Eq, Show)


