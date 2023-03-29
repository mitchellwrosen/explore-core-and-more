module Expr where

import Control.Lens (over, view)
import Control.Monad.Trans.State qualified as State
import Data.Function ((&))
import Data.Generics.Product (position)
import Data.Maybe (fromMaybe, mapMaybe)
import Data.Set (Set)
import Data.Set qualified as Set
import Data.Text (Text)
import Data.Text qualified as Text
import GHC.Generics
import Type

data Expr var
  = EApp (Expr var) (Expr var) [Expr var]
  | ECase (Expr var) (Maybe Text) [(Alternative var, Expr var)]
  | EId (Ident var)
  | EJoin (JoinPoint var) (Expr var)
  | EJoinrec [JoinPoint var] (Expr var)
  | EJump
  | ELam [Var var] (Expr var)
  | ELet (LetBinding var) (Expr var)
  | ELetrec [LetBinding var] (Expr var)
  | ELit Lit
  | ETuple (Expr var) (Expr var) [Expr var]
  | ETupleU [Expr var]
  | ETy Type
  deriving stock (Eq, Show)

pattern EVar :: var -> Expr var
pattern EVar var <-
  (isEVar -> Just var)
  where
    EVar var = EId (varIdent var)

isEVar :: Expr var -> Maybe var
isEVar = \case
  EId (Ident Nothing [] var) -> Just var
  _ -> Nothing

data Ident var = Ident
  { package :: Maybe Text,
    modules :: [Text],
    name :: var
  }
  deriving stock (Eq, Ord, Show)

varIdent :: var -> Ident var
varIdent =
  Ident Nothing []

identVar :: Ident Text -> Text
identVar Ident {package, modules, name} =
  fromMaybe Text.empty package <> foldMap (\m -> m <> ".") modules <> name

data LetBinding var
  = LetBinding Text (Expr var)
  deriving stock (Eq, Show)

data JoinPoint var
  = JoinPoint Text [Var var] (Expr var)
  deriving stock (Eq, Show)

data Lit
  = LInt Text -- 0
  | LIntU Text -- 0#
  | LStrU Text -- "foobar"#
  | LWordU Text -- 0##
  | LWord64U Text -- 0##64
  deriving stock (Eq, Show)

-- TODO rename to Binder
data Var var
  = Tyvar var (Maybe Type) -- '@foo'
  | Var var (Maybe Type) -- 'foo'
  deriving stock (Show)

instance Eq var => Eq (Var var) where
  Tyvar x _ == Tyvar y _ = x == y
  Var x _ == Var y _ = x == y
  _ == _ = False

instance Ord var => Ord (Var var) where
  compare (Tyvar x _) (Tyvar y _) = compare x y
  compare (Tyvar _ _) (Var _ _) = LT
  compare (Var x _) (Var y _) = compare x y
  compare (Var _ _) (Tyvar _ _) = GT

varToTermIdent :: Var var -> Maybe (Ident var)
varToTermIdent = \case
  Var var _ -> Just (varIdent var)
  Tyvar {} -> Nothing

data Alternative var
  = ACon (Ident var) [Var var]
  | ADef
  | ALit Lit
  | ATuple (Var var) (Var var) [Var var]
  | ATupleU [Var var]
  | AUnit
  deriving stock (Eq, Show)

alternativeBoundVars :: Alternative var -> [Var var]
alternativeBoundVars = \case
  ACon _ vars -> vars
  ADef -> []
  ALit _ -> []
  ATuple var0 var1 vars -> var0 : var1 : vars
  ATupleU vars -> vars
  AUnit -> []

------------------------------------------------------------------------------------------------------------------------

optimizeExpression :: Expr Text -> Expr Text
optimizeExpression =
  exprFToExpr
    . renameVars
    -- . numberIdents
    . replaceUnusedVarsWithUnderscores
    . annotateUsedIdentifiers
    . exprToExprF ()

data ExprF x var a
  = EAppF x a a [a]
  | ECaseF x a (Maybe Text) [(Alternative var, a)]
  | EIdF x (Ident var)
  | EJoinF x (JoinPointF var a) a
  | EJoinrecF x [JoinPointF var a] a
  | EJumpF x
  | ELamF x [Var var] a
  | ELetF x (LetBindingF a) a
  | ELetrecF x [LetBindingF a] a
  | ELitF x Lit
  | ETupleF x a a [a]
  | ETupleUF x [a]
  | ETyF x Type
  deriving stock (Functor, Generic, Show)

data LetBindingF a
  = LetBindingF Text a
  deriving stock (Functor, Show)

data JoinPointF var a
  = JoinPointF Text [Var var] a
  deriving stock (Functor, Show)

extra :: forall x var a. ExprF x var a -> x
extra =
  view (position @1)

overExtra :: forall x x' var a. (x -> x') -> ExprF x var a -> ExprF x' var a
overExtra =
  over (position @1)

newtype Fix f = Fix {unfix :: f (Fix f)}

bottomUp :: (Functor f) => (forall x. f x -> g x) -> Fix f -> Fix g
bottomUp f =
  Fix . f . fmap (bottomUp f) . unfix

bottomUp1 :: (Functor f) => (f (Fix f) -> f (Fix f)) -> Fix f -> Fix f
bottomUp1 f =
  Fix . f . fmap (bottomUp1 f) . unfix

topDown :: Functor g => (forall x. f x -> g x) -> Fix f -> Fix g
topDown f =
  Fix . fmap (topDown f) . f . unfix

-- caller signals to stop (Left) or continue descending into children (Right)
topDownWithCutoff :: Functor f => (forall x. f x -> Either (f x) (f x)) -> Fix f -> Fix f
topDownWithCutoff f =
  Fix . either id (fmap (topDownWithCutoff f)) . f . unfix

exprToExprF :: x -> Expr var -> Fix (ExprF x var)
exprToExprF xxx = \case
  EApp x y zs -> Fix (EAppF xxx (exprToExprF xxx x) (exprToExprF xxx y) (map (exprToExprF xxx) zs))
  ECase scrutinee whnf alternatives ->
    Fix (ECaseF xxx (exprToExprF xxx scrutinee) whnf (map (\(alt, body) -> (alt, exprToExprF xxx body)) alternatives))
  EId ident -> Fix (EIdF xxx ident)
  EJoin point body -> Fix (EJoinF xxx (joinPointToJoinPointF xxx point) (exprToExprF xxx body))
  EJoinrec points body -> Fix (EJoinrecF xxx (map (joinPointToJoinPointF xxx) points) (exprToExprF xxx body))
  EJump -> Fix (EJumpF xxx)
  ELam bindings body -> Fix (ELamF xxx bindings (exprToExprF xxx body))
  ELet binding body -> Fix (ELetF xxx (letBindingToLetBindingF xxx binding) (exprToExprF xxx body))
  ELetrec bindings body -> Fix (ELetrecF xxx (map (letBindingToLetBindingF xxx) bindings) (exprToExprF xxx body))
  ELit lit -> Fix (ELitF xxx lit)
  ETuple expr0 expr1 exprs ->
    Fix (ETupleF xxx (exprToExprF xxx expr0) (exprToExprF xxx expr1) (map (exprToExprF xxx) exprs))
  ETupleU exprs -> Fix (ETupleUF xxx (map (exprToExprF xxx) exprs))
  ETy ty -> Fix (ETyF xxx ty)

exprFToExpr :: Fix (ExprF x var) -> Expr var
exprFToExpr = \case
  Fix (EAppF _ x y zs) -> EApp (exprFToExpr x) (exprFToExpr y) (map exprFToExpr zs)
  Fix (ECaseF _ scrutinee whnf alternatives) ->
    ECase (exprFToExpr scrutinee) whnf (map (\(alt, body) -> (alt, exprFToExpr body)) alternatives)
  Fix (EIdF _ ident) -> EId ident
  Fix (EJoinF _ point body) -> EJoin (joinPointFToJoinPoint point) (exprFToExpr body)
  Fix (EJoinrecF _ points body) -> EJoinrec (map joinPointFToJoinPoint points) (exprFToExpr body)
  Fix (EJumpF _) -> EJump
  Fix (ELamF _ bindings body) -> ELam bindings (exprFToExpr body)
  Fix (ELetF _ binding body) -> ELet (letBindingFToLetBinding binding) (exprFToExpr body)
  Fix (ELetrecF _ bindings body) -> ELetrec (map letBindingFToLetBinding bindings) (exprFToExpr body)
  Fix (ELitF _ lit) -> ELit lit
  Fix (ETupleF _ x y zs) -> ETuple (exprFToExpr x) (exprFToExpr y) (map exprFToExpr zs)
  Fix (ETupleUF _ exprs) -> ETupleU (map exprFToExpr exprs)
  Fix (ETyF _ ty) -> ETy ty

letBindingToLetBindingF :: x -> LetBinding var -> LetBindingF (Fix (ExprF x var))
letBindingToLetBindingF xxx (LetBinding ident defn) =
  LetBindingF ident (exprToExprF xxx defn)

letBindingFToLetBinding :: LetBindingF (Fix (ExprF x var)) -> LetBinding var
letBindingFToLetBinding (LetBindingF ident defn) =
  LetBinding ident (exprFToExpr defn)

joinPointToJoinPointF :: x -> JoinPoint var -> JoinPointF var (Fix (ExprF x var))
joinPointToJoinPointF xxx (JoinPoint ident bindings defn) =
  JoinPointF ident bindings (exprToExprF xxx defn)

joinPointFToJoinPoint :: JoinPointF var (Fix (ExprF x var)) -> JoinPoint var
joinPointFToJoinPoint (JoinPointF ident bindings defn) =
  JoinPoint ident bindings (exprFToExpr defn)

------------------------------------------------------------------------------------------------------------------------
-- Replace unused vars with underscores

-- Annotate each expression with all of the term identifiers that are used within it
annotateUsedIdentifiers :: Fix (ExprF () Text) -> Fix (ExprF (Set (Ident Text)) Text)
annotateUsedIdentifiers = \case
  Fix (EAppF () x y zs) ->
    let (x1, v1) = recur x
        (y2, v2) = recur y
        (zs1, vs) = unzip (map recur zs)
     in Fix (EAppF (Set.unions (v1 : v2 : vs)) x1 y2 zs1)
  Fix (ECaseF () scrutinee whnf alternatives) ->
    let (scrutinee1, v1) = recur scrutinee
        (alternatives1, vs) =
          unzip $
            map
              ( \(alt, body) ->
                  let bound =
                        maybe
                          id
                          (\v -> (varIdent v :))
                          whnf
                          (mapMaybe varToTermIdent (alternativeBoundVars alt))
                   in let (body1, vs0) = recur body
                       in ((alt, body1), Set.difference vs0 (Set.fromList bound))
              )
              alternatives
     in Fix (ECaseF (Set.unions (v1 : vs)) scrutinee1 whnf alternatives1)
  Fix (EIdF () ident) -> Fix (EIdF (Set.singleton ident) ident)
  Fix (EJoinF () (JoinPointF ident vars defn) body) ->
    let (defn1, v1) = recur defn
        (body1, v2) = recur body
     in Fix $
          EJoinF
            (Set.difference v1 (Set.fromList (mapMaybe varToTermIdent vars)) <> Set.delete (varIdent ident) v2)
            (JoinPointF ident vars defn1)
            body1
  Fix (EJoinrecF () points0 body0) -> do
    let idents = Set.fromList (map (\(JoinPointF ident _ _) -> varIdent ident) points0)
        (points1, pointsFreeIdents) =
          points0
            & map
              ( \(JoinPointF ident vars defn0) ->
                  let (defn1, defnFreeIdents) = recur defn0
                   in ( JoinPointF ident vars defn1,
                        Set.difference defnFreeIdents (Set.fromList (mapMaybe varToTermIdent vars) <> idents)
                      )
              )
            & unzip
    let (body1, bodyFreeIdents) = recur body0
    Fix (EJoinrecF (Set.unions (Set.difference bodyFreeIdents idents : pointsFreeIdents)) points1 body1)
  Fix (EJumpF ()) -> Fix (EJumpF Set.empty)
  Fix (ELamF () vars body) ->
    let (body1, v1) = recur body
     in Fix (ELamF (Set.difference v1 (Set.fromList (mapMaybe varToTermIdent vars))) vars body1)
  Fix (ELetF () (LetBindingF ident defn) body) -> do
    let (defn1, defnFreeIdents) = recur defn
    let (body1, bodyFreeIdents) = recur body
    let exprFreeIdents = defnFreeIdents <> Set.delete (varIdent ident) bodyFreeIdents
    Fix (ELetF exprFreeIdents (LetBindingF ident defn1) body1)
  Fix (ELetrecF () bindings0 body0) -> do
    let idents = Set.fromList (map (\(LetBindingF ident _) -> varIdent ident) bindings0)
    let (bindings1, bindingsFreeIdents) =
          bindings0
            & map
              ( \(LetBindingF ident defn0) ->
                  let (defn1, defnFreeIdents) = recur defn0
                   in (LetBindingF ident defn1, Set.difference defnFreeIdents idents)
              )
            & unzip
    let (body1, bodyFreeIdents) = recur body0
    Fix (ELetrecF (Set.unions (Set.difference bodyFreeIdents idents : bindingsFreeIdents)) bindings1 body1)
  Fix (ELitF () lit) -> Fix (ELitF Set.empty lit)
  Fix (ETupleF () x0 y0 zs0) -> do
    let (x1, xFreeIdents) = recur x0
    let (y1, yFreeIdents) = recur y0
    let (zs1, zsFreeIdents) = unzip (map recur zs0)
    Fix (ETupleF (Set.unions (xFreeIdents : yFreeIdents : zsFreeIdents)) x1 y1 zs1)
  Fix (ETupleUF () exprs) ->
    let (exprs1, vs) = unzip (map recur exprs)
     in Fix (ETupleUF (Set.unions vs) exprs1)
  Fix (ETyF () ty) -> Fix (ETyF Set.empty ty)
  where
    recur :: Fix (ExprF () Text) -> (Fix (ExprF (Set (Ident Text)) Text), Set (Ident Text))
    recur x =
      let y = annotateUsedIdentifiers x
       in (y, extra (unfix y))

replaceUnusedVarsWithUnderscores :: Fix (ExprF (Set (Ident Text)) Text) -> Fix (ExprF (Set (Ident Text)) Text)
replaceUnusedVarsWithUnderscores =
  bottomUp1 \case
    ECaseF freeIdents scrutinee whnf alternatives ->
      let whnf1 :: Maybe Text
          whnf1 =
            case whnf of
              Nothing -> Nothing
              Just s ->
                -- we know we won't shadow whnf with a pattern, so ignoring fst is ok
                if any (\(_, altFreeIdents) -> Set.member (varIdent s) (extra (unfix altFreeIdents))) alternatives
                  then Just s
                  else -- no pattern used whnf (yet GHC named it anyway)
                    Nothing
          f ::
            (Alternative Text, Fix (ExprF (Set (Ident Text)) Text)) ->
            (Alternative Text, Fix (ExprF (Set (Ident Text)) Text))
          f = \case
            (ACon con vars, body) -> (ACon con (map (underscore (extra (unfix body))) vars), body)
            alt@(ADef, _) -> alt
            (ATuple var0 var1 vars, body) ->
              let bodyVars = extra (unfix body)
               in (ATuple (underscore bodyVars var0) (underscore bodyVars var1) (map (underscore bodyVars) vars), body)
            (ATupleU vars, body) -> (ATupleU (map (underscore (extra (unfix body))) vars), body)
            alt@(ALit {}, _) -> alt
            alt@(AUnit, _) -> alt
       in ECaseF freeIdents scrutinee whnf1 (map f alternatives)
    EJoinF freeIdents (JoinPointF ident vars defn) body ->
      EJoinF freeIdents (JoinPointF ident (map (underscore (extra (unfix defn))) vars) defn) body
    expr@(EJoinrecF freeIdents points body) -> expr
    expr@(ELamF freeIdents bindings body) -> expr
    expr@(ELetF freeIdents (LetBindingF ident defn) usedVars) -> expr
    expr@(ELetrecF freeIdents bindings body) -> expr
    --
    expr@EAppF {} -> expr
    expr@EIdF {} -> expr
    expr@EJumpF {} -> expr
    expr@ELitF {} -> expr
    expr@ETupleF {} -> expr
    expr@ETupleUF {} -> expr
    expr@ETyF {} -> expr
  where
    underscore :: Set (Ident Text) -> Var Text -> Var Text
    underscore freeIdents = \case
      var@(Var v ty) ->
        if Set.member (varIdent v) freeIdents
          then var
          else Var "_" ty
      var@Tyvar {} -> var

data N a
  = N a Int

instance Eq a => Eq (N a) where
  N x _ == N y _ = x == y

instance Ord a => Ord (N a) where
  compare (N x _) (N y _) = compare x y

-- Give each ident an "occurrence number" of 0. This lets us reuse variables names (with a higher occurrence number)
-- after they fall out of use.
numberIdents :: Fix (ExprF (Set (Ident Text)) Text) -> Fix (ExprF (Set (N (Ident Text))) Text)
numberIdents =
  topDown (overExtra (Set.map (\ident -> N ident 0)))

renameVars :: Fix (ExprF (Set (Ident Text)) Text) -> Fix (ExprF (Set (Ident Text)) Text)
renameVars expr =
  State.evalState (renameVars1 expr) supply2
  where
    alphabet :: [Text]
    alphabet = map Text.singleton ['a' .. 'z']

    -- a, b, ..., z, aa, ab, ..., az, ba, bb, ... bz, ...
    supply :: [Text]
    supply =
      alphabet ++ do
        suffix <- supply
        prefix <- alphabet
        pure (prefix <> suffix)

    -- a0  b0       z0  aa0  ab0       az0  ba0  bb0       bz0
    -- a1  b1       z1  aa1  ab1       az1  ba1  bb1       bz1
    -- a2, b2, ..., z2, aa2, ab2, ..., az2, ba2, bb2, ..., bz2, ...
    -- .   .         .    .    .         .    .    .         .
    -- .   .         .    .    .         .    .    .         .
    -- .   .         .    .    .         .    .    .         .
    supply2 :: [[N Text]]
    supply2 =
      map (\var -> map (N var) [0 ..]) supply

type NameSupply =
  [[N Text]]

renameVars1 ::
  Fix (ExprF (Set (Ident Text)) Text) ->
  State.State NameSupply (Fix (ExprF (Set (Ident Text)) Text))
renameVars1 expr0@(Fix expr1) =
  case expr1 of
    EAppF freeIdents x0 y0 zs0 -> do
      x1 <- renameVars1 x0
      y1 <- renameVars1 y0
      zs1 <- traverse renameVars1 zs0
      pure (Fix (EAppF freeIdents x1 y1 zs1))
    ECaseF freeIdents scrutinee0 whnf0 alternatives0 -> do
      scrutinee1 <- renameVars1 scrutinee0
      (whnf1, alternatives1) <-
        case whnf0 of
          Nothing -> pure (Nothing, alternatives0)
          Just old -> do
            new <- fresh
            pure (Just new, map (\(alt, body) -> (alt, alphaRename old new body)) alternatives0)
      let loop acc = \case
            [] -> pure (reverse acc)
            (alt, body0) : alts ->
              case alt of
                ACon con vars0 -> do
                  (vars, body1) <- renameVarsIn vars0 body0
                  body2 <- renameVars1 body1
                  loop ((ACon con vars, body2) : acc) alts
                ADef -> do
                  body1 <- renameVars1 body0
                  loop ((alt, body1) : acc) alts
                ALit _ -> do
                  body1 <- renameVars1 body0
                  loop ((alt, body1) : acc) alts
                ATuple x0 y0 zs0 -> do
                  (x1, body1) <- renameVarIn x0 body0
                  (y1, body2) <- renameVarIn y0 body1
                  (zs1, body3) <- renameVarsIn zs0 body2
                  body4 <- renameVars1 body3
                  loop ((ATuple x1 y1 zs1, body4) : acc) alts
                ATupleU vars0 -> do
                  (vars, body1) <- renameVarsIn vars0 body0
                  body2 <- renameVars1 body1
                  loop ((ATupleU vars, body2) : acc) alts
                AUnit -> do
                  body1 <- renameVars1 body0
                  loop ((alt, body1) : acc) alts
      alternatives2 <- loop [] alternatives1
      pure (Fix (ECaseF freeIdents scrutinee1 whnf1 alternatives2))
    EJoinF freeIdents point0 body0 -> do
      point1 <- renameJoinPoint point0
      body1 <- renameVars1 body0
      pure (Fix (EJoinF freeIdents point1 body1))
    EJoinrecF freeIdents points0 body0 -> do
      points1 <- traverse renameJoinPoint points0
      body1 <- renameVars1 body0
      pure (Fix (EJoinrecF freeIdents points1 body1))
    ELamF freeIdents bindings0 body0 -> do
      (bindings, body1) <- renameVarsIn bindings0 body0
      body2 <- renameVars1 body1
      pure (Fix (ELamF freeIdents bindings body2))
    ELetF freeIdents binding0 body0 -> do
      binding1 <- renameLetBinding binding0
      body1 <- renameVars1 body0
      pure (Fix (ELetF freeIdents binding1 body1))
    ELetrecF freeIdents bindings0 body0 -> do
      bindings1 <- traverse renameLetBinding bindings0
      body1 <- renameVars1 body0
      pure (Fix (ELetrecF freeIdents bindings1 body1))
    ETupleF freeIdents x0 y0 zs0 -> do
      x1 <- renameVars1 x0
      y1 <- renameVars1 y0
      zs1 <- traverse renameVars1 zs0
      pure (Fix (ETupleF freeIdents x1 y1 zs1))
    ETupleUF freeIdents exprs0 -> do
      exprs1 <- traverse renameVars1 exprs0
      pure (Fix (ETupleUF freeIdents exprs1))
    --
    EIdF {} -> pure expr0
    EJumpF {} -> pure expr0
    ELitF {} -> pure expr0
    ETyF {} -> pure expr0
  where
    renameLetBinding ::
      LetBindingF (Fix (ExprF (Set (Ident Text)) Text)) ->
      State.State NameSupply (LetBindingF (Fix (ExprF (Set (Ident Text)) Text)))
    renameLetBinding (LetBindingF ident defn0) = do
      defn1 <- renameVars1 defn0
      pure (LetBindingF ident defn1)

    renameJoinPoint ::
      JoinPointF Text (Fix (ExprF (Set (Ident Text)) Text)) ->
      State.State NameSupply (JoinPointF Text (Fix (ExprF (Set (Ident Text)) Text)))
    renameJoinPoint (JoinPointF ident vars0 defn0) = do
      (vars1, defn1) <- renameVarsIn vars0 defn0
      defn2 <- renameVars1 defn1
      pure (JoinPointF ident vars1 defn2)

    -- `renameVarIn var body` tries to rename `var` (assumed to have a bad name) in `body` to the best name we can come
    -- up with. We know `var` is used in `body` if `var` is not "_", since we replace unused vars with "_" before we get
    -- here.
    --
    -- For example, `var` might be x_au9, and our supply might have [[a1, ...], [b1, ...], [c0, ...]] (i.e. we've
    -- already taken two good names a0 and b1.
    --
    -- We'd like to use the best "a" name (a1), unless an "a" name (which would be the previous one, a0) is still used
    -- within `body`, in which case we'll move on to trying the best "b" name, and so on.
    renameVarIn ::
      Var Text ->
      Fix (ExprF (Set (Ident Text)) Text) ->
      State.State NameSupply (Var Text, Fix (ExprF (Set (Ident Text)) Text))
    renameVarIn var0 body =
      case var0 of
        Var old ty | old /= "_" -> do
          new <- fresh
          pure (Var new ty, alphaRename old new body)
        _ -> pure (var0, body)

    renameVarsIn ::
      [Var Text] ->
      Fix (ExprF (Set (Ident Text)) Text) ->
      State.State NameSupply ([Var Text], Fix (ExprF (Set (Ident Text)) Text))
    renameVarsIn vars0 body0 =
      let loop vars body = \case
            [] -> pure (reverse vars, body)
            v0 : vs -> do
              (v1, body1) <- renameVarIn v0 body
              loop (v1 : vars) body1 vs
       in loop [] body0 vars0

-- FIXME hmm don't want to use something from the supply that's bound!
fresh :: State.State NameSupply Text
fresh = do
  supply <- State.get
  State.put (tail supply)
  let N name _ = head (head supply)
  pure name

-- `alphaRename old new expr` renames all free `old` to `new` in `expr`
-- Preconditions: substituting naively avoids capture (i.e. no inner lambda binds `new`)
alphaRename :: Text -> Text -> Fix (ExprF (Set (Ident Text)) Text) -> Fix (ExprF (Set (Ident Text)) Text)
alphaRename old new =
  topDownWithCutoff \expr -> do
    if Set.member oldIdent (extra expr) -- but it is free somewhere in us
      then case expr of
        EIdF _ ident -> Left (if ident == oldIdent then EIdF (Set.singleton newIdent) newIdent else expr)
        _ -> Right (overExtra (Set.insert newIdent . Set.delete oldIdent) expr)
      else Left expr
  where
    oldIdent = varIdent old
    newIdent = varIdent new
