module Expr where

import Data.Set (Set)
import qualified Data.Set as Set
import Data.Text (Text)
import Type

data Expr
  = EApp Expr Expr [Expr]
  | ECase Expr (Maybe Text) [(Alternative, Expr)]
  | EId Text
  | EJoin JoinPoint Expr
  | EJoinrec [JoinPoint] Expr
  | EJump
  | ELam [Var] Expr
  | ELet Text Expr Expr
  | ELit Lit
  | ETupleU [Expr]
  | ETy Type
  deriving stock (Eq, Show)

-- TODO use this in EId
data Ident = Ident
  { package :: Maybe Text,
    modules :: [Text],
    name :: Text
  }

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
  | Var Text (Maybe Type) -- 'Foo.Bar.baz'
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
  = ACon Text [Var]
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

mungeExpression :: Expr -> Expr
mungeExpression =
  exprFToExpr
    . unannotateUsedVars
    . replaceUsedVarsWithUnderscore
    . annotateUsedVars
    . exprToExprF

data ExprF a
  = EAppF a a [a]
  | ECaseF a (Maybe Text) [(Alternative, a)]
  | EIdF Text
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

data ExprAndUsedVarsF a
  = ExprAndUsedVarsF (ExprF a) (Set Var)
  deriving stock (Functor)

-- Annotate each expression with all of the variables that are used within it
annotateUsedVars :: Fix ExprF -> Fix ExprAndUsedVarsF
annotateUsedVars expr =
  case unfix expr of
    EAppF x y zs ->
      let (x1, v1) = recur x
          (y2, v2) = recur y
          (zs1, vs) = unzip (map recur zs)
       in Fix (ExprAndUsedVarsF (EAppF x1 y2 zs1) (Set.unions (v1 : v2 : vs)))
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
       in Fix (ExprAndUsedVarsF (ECaseF scrutinee1 whnf alternatives1) (Set.unions (v1 : vs)))
    EIdF ident -> Fix (ExprAndUsedVarsF (EIdF ident) (Set.singleton (Var ident Nothing)))
    EJoinF (JoinPointF ident vars defn) body ->
      let (defn1, v1) = recur defn
          (body1, v2) = recur body
       in Fix $
            ExprAndUsedVarsF
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
            ExprAndUsedVarsF
              (EJoinrecF points1 body1)
              (Set.unions (Set.difference v1 idents : vs))
    EJumpF -> Fix (ExprAndUsedVarsF EJumpF Set.empty)
    ELamF vars body ->
      let (body1, v1) = recur body
       in Fix (ExprAndUsedVarsF (ELamF vars body1) (Set.difference v1 (Set.fromList vars)))
    ELetF ident defn body ->
      let (defn1, v1) = recur defn
          (body1, v2) = recur body
       in Fix (ExprAndUsedVarsF (ELetF ident defn1 body1) (v1 <> Set.delete (Var ident Nothing) v2))
    ELitF lit -> Fix (ExprAndUsedVarsF (ELitF lit) Set.empty)
    ETupleUF exprs ->
      let (exprs1, vs) = unzip (map recur exprs)
       in Fix (ExprAndUsedVarsF (ETupleUF exprs1) (Set.unions vs))
    ETyF ty ->
      Fix $
        ExprAndUsedVarsF
          (ETyF ty)
          ( case ty of
              TId ident -> Set.singleton (Tyvar ident Nothing)
              _ -> Set.empty
          )
  where
    recur :: Fix ExprF -> (Fix ExprAndUsedVarsF, Set Var)
    recur x =
      let y@(Fix (ExprAndUsedVarsF _ v)) = annotateUsedVars x
       in (y, v)

unannotateUsedVars :: Fix ExprAndUsedVarsF -> Fix ExprF
unannotateUsedVars =
  bottomUp \(ExprAndUsedVarsF expr _usedVars) -> expr

replaceUsedVarsWithUnderscore :: Fix ExprAndUsedVarsF -> Fix ExprAndUsedVarsF
replaceUsedVarsWithUnderscore =
  bottomUp1 \case
    ExprAndUsedVarsF (ECaseF scrutinee whnf alternatives) usedVars ->
      let f :: (Alternative, Fix ExprAndUsedVarsF) -> (Alternative, Fix ExprAndUsedVarsF)
          f = \case
            (ACon con vars, body@(Fix (ExprAndUsedVarsF _ bodyVars))) ->
              (ACon con (map (underscore bodyVars) vars), body)
            (ATupleU vars, body@(Fix (ExprAndUsedVarsF _ bodyVars))) -> (ATupleU (map (underscore bodyVars) vars), body)
            alt@(ALit {}, _) -> alt
            alt@(ADef, _) -> alt
       in ExprAndUsedVarsF (ECaseF scrutinee whnf (map f alternatives)) usedVars
    ExprAndUsedVarsF (EJoinF (JoinPointF ident vars defn@(Fix (ExprAndUsedVarsF _ defnVars))) body) usedVars ->
      ExprAndUsedVarsF (EJoinF (JoinPointF ident (map (underscore defnVars) vars) defn) body) usedVars
    expr@(ExprAndUsedVarsF (EJoinrecF points body) usedVars) -> expr
    expr@(ExprAndUsedVarsF (ELamF bindings body) usedVars) -> expr
    expr@(ExprAndUsedVarsF (ELetF ident defn body) usedVars) -> expr
    --
    expr@(ExprAndUsedVarsF EAppF {} _) -> expr
    expr@(ExprAndUsedVarsF EIdF {} _) -> expr
    expr@(ExprAndUsedVarsF EJumpF {} _) -> expr
    expr@(ExprAndUsedVarsF ELitF {} _) -> expr
    expr@(ExprAndUsedVarsF ETupleUF {} _) -> expr
    expr@(ExprAndUsedVarsF ETyF {} _) -> expr
  where
    underscore :: Set Var -> Var -> Var
    underscore used v =
      if Set.member v used
        then v
        else case v of
          Tyvar _ ty -> Tyvar "_" ty
          Var _ ty -> Var "_" ty
