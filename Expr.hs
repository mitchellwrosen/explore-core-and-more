module Expr where

import Data.Maybe (fromMaybe)
import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import qualified Data.Text as Text
import Type

data Expr
  = EApp Expr Expr [Expr]
  | ECase Expr (Maybe Text) [(Alternative, Expr)]
  | EId Ident
  | EJoin JoinPoint Expr
  | EJoinrec [JoinPoint] Expr
  | EJump
  | ELam [Var] Expr
  | ELet Text Expr Expr
  | ELit Lit
  | ETupleU [Expr]
  | ETy Type
  deriving stock (Eq, Show)

pattern EVar :: Text -> Expr
pattern EVar var <-
  (isEVar -> Just var)
  where
    EVar var = EId (Ident Nothing [] var)

isEVar :: Expr -> Maybe Text
isEVar = \case
  EId (Ident Nothing [] var) -> Just var
  _ -> Nothing

-- TODO use this in EId
data Ident = Ident
  { package :: Maybe Text,
    modules :: [Text],
    name :: Text
  }
  deriving stock (Eq, Show)

identVar :: Ident -> Text
identVar Ident {package, modules, name} =
  fromMaybe Text.empty package <> foldMap (\m -> m <> ".") modules <> name

data JoinPoint
  = JoinPoint Text [Var] Expr
  deriving stock (Eq, Show)

data Lit
  = LInt Text -- 0
  | LIntU Text -- 0#
  | LStrU Text -- "foobar"#
  | LWord64U Text -- 0##64
  deriving stock (Eq, Show)

data Var
  = Tyvar Text (Maybe Type) -- '@foo'
  | Var Text (Maybe Type) -- 'foo'
  deriving stock (Show)

instance Eq Var where
  Tyvar x _ == Tyvar y _ = x == y
  Var x _ == Var y _ = x == y
  _ == _ = False

instance Ord Var where
  compare (Tyvar x _) (Tyvar y _) = compare x y
  compare (Tyvar _ _) (Var _ _) = LT
  compare (Var x _) (Var y _) = compare x y
  compare (Var _ _) (Tyvar _ _) = GT

data Alternative
  = ACon Ident [Var]
  | ATupleU [Var]
  | ALit Lit
  | ADef
  deriving stock (Eq, Show)

alternativeBoundVars :: Alternative -> Set Var
alternativeBoundVars = \case
  ACon _ vars -> Set.fromList vars
  ATupleU vars -> Set.fromList vars
  ALit _ -> Set.empty
  ADef -> Set.empty

------------------------------------------------------------------------------------------------------------------------

optimizeExpression :: Expr -> Expr
optimizeExpression =
  exprFToExpr
    . unannotate
    . replaceUnusedVarsWithUnderscores
    . annotateUsedIdentifiers
    . exprToExprF

data ExprF a
  = EAppF a a [a]
  | ECaseF a (Maybe Text) [(Alternative, a)]
  | EIdF Ident
  | EJoinF (JoinPointF a) a
  | EJoinrecF [JoinPointF a] a
  | EJumpF
  | ELamF [Var] a
  | ELetF Text a a
  | ELitF Lit
  | ETupleUF [a]
  | ETyF Type
  deriving stock (Functor, Show)

data JoinPointF a
  = JoinPointF Text [Var] a
  deriving stock (Functor, Show)

newtype Fix f = Fix {unfix :: f (Fix f)}

bottomUp :: (Functor f) => (forall x. f x -> g x) -> Fix f -> Fix g
bottomUp f =
  Fix . f . fmap (bottomUp f) . unfix

bottomUp1 :: (Functor f) => (f (Fix f) -> f (Fix f)) -> Fix f -> Fix f
bottomUp1 f =
  Fix . f . fmap (bottomUp1 f) . unfix

exprToExprF :: Expr -> Fix ExprF
exprToExprF = \case
  EApp x y zs -> Fix (EAppF (exprToExprF x) (exprToExprF y) (map exprToExprF zs))
  ECase scrutinee whnf alternatives ->
    Fix (ECaseF (exprToExprF scrutinee) whnf (map (\(alt, body) -> (alt, exprToExprF body)) alternatives))
  EId ident -> Fix (EIdF ident)
  EJoin point body -> Fix (EJoinF (joinPointToJoinPointF point) (exprToExprF body))
  EJoinrec points body -> Fix (EJoinrecF (map joinPointToJoinPointF points) (exprToExprF body))
  EJump -> Fix EJumpF
  ELam bindings body -> Fix (ELamF bindings (exprToExprF body))
  ELet ident defn body -> Fix (ELetF ident (exprToExprF defn) (exprToExprF body))
  ELit lit -> Fix (ELitF lit)
  ETupleU exprs -> Fix (ETupleUF (map exprToExprF exprs))
  ETy ty -> Fix (ETyF ty)

exprFToExpr :: Fix ExprF -> Expr
exprFToExpr = \case
  Fix (EAppF x y zs) -> EApp (exprFToExpr x) (exprFToExpr y) (map exprFToExpr zs)
  Fix (ECaseF scrutinee whnf alternatives) ->
    ECase (exprFToExpr scrutinee) whnf (map (\(alt, body) -> (alt, exprFToExpr body)) alternatives)
  Fix (EIdF ident) -> EId ident
  Fix (EJoinF point body) -> EJoin (joinPointFToJoinPoint point) (exprFToExpr body)
  Fix (EJoinrecF points body) -> EJoinrec (map joinPointFToJoinPoint points) (exprFToExpr body)
  Fix EJumpF -> EJump
  Fix (ELamF bindings body) -> ELam bindings (exprFToExpr body)
  Fix (ELetF ident defn body) -> ELet ident (exprFToExpr defn) (exprFToExpr body)
  Fix (ELitF lit) -> ELit lit
  Fix (ETupleUF exprs) -> ETupleU (map exprFToExpr exprs)
  Fix (ETyF ty) -> ETy ty

joinPointToJoinPointF :: JoinPoint -> JoinPointF (Fix ExprF)
joinPointToJoinPointF (JoinPoint ident defn body) =
  JoinPointF ident defn (exprToExprF body)

joinPointFToJoinPoint :: JoinPointF (Fix ExprF) -> JoinPoint
joinPointFToJoinPoint (JoinPointF ident defn body) =
  JoinPoint ident defn (exprFToExpr body)

data X f x a
  = X (f a) x
  deriving stock (Functor)

unannotate :: Fix (X ExprF a) -> Fix ExprF
unannotate =
  bottomUp \(X expr _) -> expr

------------------------------------------------------------------------------------------------------------------------
-- Replace unused vars with underscores

-- Annotate each expression with all of the identifiers that are used within it
annotateUsedIdentifiers :: Fix ExprF -> Fix (X ExprF (Set Var))
annotateUsedIdentifiers expr =
  case unfix expr of
    EAppF x y zs ->
      let (x1, v1) = recur x
          (y2, v2) = recur y
          (zs1, vs) = unzip (map recur zs)
       in Fix (X (EAppF x1 y2 zs1) (Set.unions (v1 : v2 : vs)))
    ECaseF scrutinee whnf alternatives ->
      let (scrutinee1, v1) = recur scrutinee
          (alternatives1, vs) =
            unzip $
              map
                ( \(alt, body) ->
                    let bound =
                          maybe id (\v -> Set.insert (Var v Nothing)) whnf (alternativeBoundVars alt)
                     in let (body1, vs0) = recur body
                         in ((alt, body1), Set.difference vs0 bound)
                )
                alternatives
       in Fix (X (ECaseF scrutinee1 whnf alternatives1) (Set.unions (v1 : vs)))
    EIdF ident -> Fix (X (EIdF ident) (Set.singleton (Var (identVar ident) Nothing)))
    EJoinF (JoinPointF ident vars defn) body ->
      let (defn1, v1) = recur defn
          (body1, v2) = recur body
       in Fix $
            X
              (EJoinF (JoinPointF ident vars defn1) body1)
              (Set.difference v1 (Set.fromList vars) <> Set.delete (Var ident Nothing) v2)
    EJoinrecF points body ->
      let idents = Set.fromList (map (\(JoinPointF ident _ _) -> Var ident Nothing) points)
          (points1, vs) =
            unzip $
              map
                ( \(JoinPointF ident vars defn) ->
                    let (defn1, v1) = recur defn
                     in (JoinPointF ident vars defn1, Set.difference v1 (Set.fromList vars <> idents))
                )
                points
       in let (body1, v1) = recur body
           in Fix $
                X
                  (EJoinrecF points1 body1)
                  (Set.unions (Set.difference v1 idents : vs))
    EJumpF -> Fix (X EJumpF Set.empty)
    ELamF vars body ->
      let (body1, v1) = recur body
       in Fix (X (ELamF vars body1) (Set.difference v1 (Set.fromList vars)))
    ELetF ident defn body ->
      let (defn1, v1) = recur defn
          (body1, v2) = recur body
       in Fix (X (ELetF ident defn1 body1) (v1 <> Set.delete (Var ident Nothing) v2))
    ELitF lit -> Fix (X (ELitF lit) Set.empty)
    ETupleUF exprs ->
      let (exprs1, vs) = unzip (map recur exprs)
       in Fix (X (ETupleUF exprs1) (Set.unions vs))
    ETyF ty ->
      Fix $
        X
          (ETyF ty)
          ( case ty of
              TId ident -> Set.singleton (Tyvar ident Nothing)
              _ -> Set.empty
          )
  where
    recur :: Fix ExprF -> (Fix (X ExprF (Set Var)), Set Var)
    recur x =
      let y@(Fix (X _ v)) = annotateUsedIdentifiers x
       in (y, v)

replaceUnusedVarsWithUnderscores :: Fix (X ExprF (Set Var)) -> Fix (X ExprF (Set Var))
replaceUnusedVarsWithUnderscores =
  bottomUp1 \case
    X (ECaseF scrutinee whnf alternatives) usedVars ->
      let whnf1 :: Maybe Text
          whnf1 =
            case whnf of
              Nothing -> Nothing
              Just s ->
                -- we know we won't shadow whnf with a pattern, so map snd (ignoring fst) is ok
                if any (\(_, Fix (X _ vars)) -> Set.member (Var s Nothing) vars) alternatives
                  then Just s
                  else -- no pattern used whnf (yet GHC named it anyway)
                    Nothing
          f :: (Alternative, Fix (X ExprF (Set Var))) -> (Alternative, Fix (X ExprF (Set Var)))
          f = \case
            (ACon con vars, body@(Fix (X _ bodyVars))) ->
              (ACon con (map (underscore bodyVars) vars), body)
            (ATupleU vars, body@(Fix (X _ bodyVars))) -> (ATupleU (map (underscore bodyVars) vars), body)
            alt@(ALit {}, _) -> alt
            alt@(ADef, _) -> alt
       in X (ECaseF scrutinee whnf1 (map f alternatives)) usedVars
    X (EJoinF (JoinPointF ident vars defn@(Fix (X _ defnVars))) body) usedVars ->
      X (EJoinF (JoinPointF ident (map (underscore defnVars) vars) defn) body) usedVars
    expr@(X (EJoinrecF points body) usedVars) -> expr
    expr@(X (ELamF bindings body) usedVars) -> expr
    expr@(X (ELetF ident defn body) usedVars) -> expr
    --
    expr@(X EAppF {} _) -> expr
    expr@(X EIdF {} _) -> expr
    expr@(X EJumpF {} _) -> expr
    expr@(X ELitF {} _) -> expr
    expr@(X ETupleUF {} _) -> expr
    expr@(X ETyF {} _) -> expr
  where
    underscore :: Set Var -> Var -> Var
    underscore used v =
      if Set.member v used
        then v
        else case v of
          Tyvar _ ty -> Tyvar "_" ty
          Var _ ty -> Var "_" ty
