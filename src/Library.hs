{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ParallelListComp #-}
{-# HLINT ignore "Eta reduce" #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -Wno-name-shadowing #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

module Library
  ( Term (..),
    Pattern (..),
    DefinitionMap,
    Epsilon,
    Gensym,
    drive,
    transformLts,
    residualizeLts,
  )
where

import Control.Exception (catch, throwIO, try)
import Control.Exception.Base (Exception)
import Control.Monad (unless, when)
import Data.Data (Typeable)
import Data.IORef
import qualified Data.Map as Map
import qualified Data.Set as Set

data Term
  = Var String
  | CCall String [Term]
  | Unfold String
  | Lambda String Term
  | Apply Term Term
  | Case Term [(Pattern, Term)]
  deriving (Show, Eq, Ord)

data Pattern
  = Pattern String [String]
  deriving (Show, Eq, Ord)

type EvContext = Term -> Term

data Redex
  = RUnfold String
  | RApply (String, Term) Term
  | RCaseNeutral (String, [Term]) [(Pattern, Term)]
  | RCase (String, [Term]) [(Pattern, Term)]
  deriving (Show, Eq)

data Observable
  = OApplyNeutral String [Term]
  | OCCall String [Term]
  | OLambda String Term
  deriving (Show, Eq)

decompose :: Term -> Either Observable (EvContext, Redex)
decompose = \case
  Var x -> Left (OApplyNeutral x [])
  CCall f args -> Left (OCCall f args)
  Unfold f -> Right (id, RUnfold f)
  Lambda x body -> Left (OLambda x body)
  Apply t1 t2 -> case decompose t1 of
    Left (OApplyNeutral x args) -> Left (OApplyNeutral x (args ++ [t2]))
    Left (OCCall _ _) -> error "Impossible!"
    Left (OLambda x body) -> Right (id, RApply (x, body) t2)
    Right (ev, redex) -> Right (\hole -> Apply (ev hole) t2, redex)
  Case t branches -> case decompose t of
    Left (OApplyNeutral x args) -> Right (id, RCaseNeutral (x, args) branches)
    Left (OCCall x args) -> Right (id, RCase (x, args) branches)
    Left (OLambda _ _) -> error "Impossible!"
    Right (ev, redex) -> Right (\hole -> Case (ev hole) branches, redex)

data RenameOps
  = AccumulateThetaRef (IORef Theta)
  | CheckOnlyTheta

rename :: RenameOps -> Term -> Theta -> Term -> IO ()
rename ops e1 theta e2 = case (e1, e2) of
  (Var x, Var y) -> case Map.lookup x theta of
    Just (Var y') -> unless (y == y') $ throwIO RenameFailure
    Just _ -> error "Impossible!"
    Nothing | AccumulateThetaRef thetaRef <- ops -> do
      theta' <- readIORef thetaRef
      case Map.lookup x theta' of
        Just (Var y') -> unless (y == y') $ throwIO RenameFailure
        Just _ -> error "Impossible!"
        Nothing -> writeIORef thetaRef (Map.insert x e2 theta')
    Nothing | CheckOnlyTheta <- ops -> throwIO RenameFailure
  (CCall c args, CCall c' args')
    | c == c' -> sequence_ [rename ops e1' theta e2' | e1' <- args | e2' <- args']
  (Unfold f, Unfold f') | f == f' -> return ()
  (Lambda x body, Lambda x' body') -> rename ops body (Map.insert x (Var x') theta) body'
  (Apply t1 t2, Apply t1' t2') -> do rename ops t1 theta t1'; rename ops t2 theta t2'
  (Case t branches, Case t' branches') -> do
    rename ops t theta t'
    sequence_
      [ do
          unless (c == c') $ throwIO RenameFailure
          let newTheta = extendThetaWithVars vars vars' theta
          rename ops body newTheta body'
        | (Pattern c vars, body) <- branches
        | (Pattern c' vars', body') <- branches'
      ]
  (Var _, _) -> throwIO RenameFailure
  (CCall _ _, _) -> throwIO RenameFailure
  (Unfold _, _) -> throwIO RenameFailure
  (Lambda _ _, _) -> throwIO RenameFailure
  (Apply _ _, _) -> throwIO RenameFailure
  (Case _ _, _) -> throwIO RenameFailure

renamesTo :: Term -> Theta -> Term -> IO Bool
renamesTo e1 theta e2 = do
  result <- try @RenameException $ rename CheckOnlyTheta e1 theta e2
  case result of
    Right _ -> return True
    Left _ -> return False

applyVars :: String -> [String] -> Term
applyVars x vars = foldl Apply (Var x) (map Var vars)

findBranch :: String -> [(Pattern, Term)] -> Maybe (Pattern, Term)
findBranch c = \case
  [] -> Nothing
  ((p@(Pattern c' _params), body) : rest)
    | c == c' -> Just (p, body)
    | otherwise -> findBranch c rest

data Lts
  = LtsApplyNeutral String [Lts]
  | LtsConstructor String [Lts]
  | LtsLambda String Lts
  | LtsCase Lts [(Pattern, Lts)]
  | LtsLet Lts (String, Lts)
  | LtsUnfold Term String Lts
  | LtsElimConstructor String Lts
  | LtsSubstitute Term Term Lts
  deriving (Show, Eq)

type DefinitionMap = Map.Map String Term

type Epsilon = DefinitionMap

type GeneralizationCache = Map.Map String Lts

type Theta = Map.Map String Term

type Sigma = Theta

type Rho = Set.Set MemoizationItem

type Pi = [Lts]

data MemoizationItem
  = MemoizeUnfolding String
  | MemoizeSubstitution Term
  deriving (Eq, Ord)

data RenameException = RenameFailure deriving (Show, Typeable)

data EmbedsLtsException = EmbedsFailure deriving (Show, Typeable)

data RenameLtsException = RenameLtsFailure deriving (Show, Typeable)

data GeneralizeLtsException = GeneralizeLtsFailure deriving (Show, Typeable)

instance Exception RenameException

instance Exception EmbedsLtsException

instance Exception RenameLtsException

instance Exception GeneralizeLtsException

type Gensym = IORef Int

doGensym :: Gensym -> String -> IO String
doGensym stateRef prefix = do
  counter <- readIORef stateRef
  writeIORef stateRef (counter + 1)
  return $ prefix ++ show counter

extendTheta :: [String] -> [Term] -> Theta -> Theta
extendTheta vars args = Map.union (Map.fromList (zip vars args))

extendThetaWithVars :: [String] -> [String] -> Theta -> Theta
extendThetaWithVars vars args = extendTheta vars (map Var args)

sigmaRange :: Sigma -> Set.Set String
sigmaRange sigma = Set.unions [freeVars e | e <- Map.elems sigma]

transformLts :: DefinitionMap -> Gensym -> Lts -> IO Lts
transformLts defs gensym lts = transformLts' defs gensym lts [] Map.empty

transformLts' :: DefinitionMap -> Gensym -> Lts -> Pi -> GeneralizationCache -> IO Lts
transformLts' defs gensym t pi theta = case t of
  LtsUnfold e f t' -> transformHelper defs gensym (LtsUnfold e f) t' t pi theta
  LtsSubstitute e e' t' -> transformHelper defs gensym (LtsSubstitute e e') t' t pi theta
  LtsLet t0 (x, t1) -> do
    opportunity <- lookupGeneralizationCache (Map.toList theta) t1
    case opportunity of
      Just x' -> transformLts' defs gensym (substituteVarLts t0 x x') pi theta
      Nothing -> do
        t0' <- transformLts' defs gensym t0 pi (Map.insert x t1 theta)
        t1' <- transformLts' defs gensym t1 pi theta
        return $ LtsLet t0' (x, t1')
  LtsApplyNeutral x args ->
    LtsApplyNeutral x <$> mapM (\arg -> transformLts' defs gensym arg pi theta) args
  LtsConstructor c args ->
    LtsConstructor c <$> mapM (\arg -> transformLts' defs gensym arg pi theta) args
  LtsLambda x body ->
    LtsLambda x <$> transformLts' defs gensym body pi theta
  LtsCase t branches ->
    LtsCase
      <$> transformLts' defs gensym t pi theta
      <*> mapM
        ( \(pattern, body) ->
            (pattern,) <$> transformLts' defs gensym body pi theta
        )
        branches
  LtsElimConstructor c body ->
    LtsElimConstructor c <$> transformLts' defs gensym body pi theta

transformHelper :: DefinitionMap -> Gensym -> (Lts -> Lts) -> Lts -> Lts -> Pi -> GeneralizationCache -> IO Lts
transformHelper defs gensym wrapper t' t pi theta =
  handleFoldingOrEmbedding defs gensym t pi theta
    >>= \result ->
      maybe
        (wrapper <$> transformLts' defs gensym t' (t : pi) theta)
        return
        result

handleFoldingOrEmbedding :: DefinitionMap -> Gensym -> Lts -> Pi -> GeneralizationCache -> IO (Maybe Lts)
handleFoldingOrEmbedding defs gensym t pi theta = do
  renamingOpportunity <- findLtsRenaming t pi
  case renamingOpportunity of
    Just (t'', sigma) -> return $ Just $ foldLts t'' sigma
    Nothing -> do
      couplingOpportunity <- findLtsCoupling t pi
      case couplingOpportunity of
        Just (t'', sigma) -> do
          (g, _newTheta) <- generalizeLts defs gensym t'' t theta sigma
          Just <$> transformLts' defs gensym g pi Map.empty
        Nothing -> return Nothing

findLtsRenaming :: Lts -> Pi -> IO (Maybe (Lts, Sigma))
findLtsRenaming t = \case
  [] -> return Nothing
  (t' : rest) -> do
    sigmaRef <- newIORef Map.empty
    canRename <-
      try @RenameLtsException $
        renameLts Set.empty sigmaRef (t', t)
    case canRename of
      Right _ ->
        readIORef sigmaRef >>= \sigma -> return $ Just (t', sigma)
      Left _ -> findLtsRenaming t rest

findLtsCoupling :: Lts -> Pi -> IO (Maybe (Lts, Sigma))
findLtsCoupling t = \case
  [] -> return Nothing
  (t' : rest) -> do
    sigmaRef <- newIORef Map.empty
    canCouple <-
      try @EmbedsLtsException $
        couplesLts sigmaRef Set.empty Map.empty (t', t)
    case canCouple of
      Right _ ->
        readIORef sigmaRef >>= \sigma -> return $ Just (t', sigma)
      Left _ -> findLtsCoupling t rest

generalizeLts :: DefinitionMap -> Gensym -> Lts -> Lts -> GeneralizationCache -> Sigma -> IO (Lts, GeneralizationCache)
generalizeLts defs gensym t t' theta sigma = case (t, t') of
  (LtsUnfold _e f tChild, LtsUnfold e' f' tChild') | f == f' -> do
    (tg, theta') <- generalizeLts defs gensym tChild tChild' theta sigma
    return (generalize' (LtsUnfold e' f tg) theta', Map.empty)
  (LtsSubstitute _e e1 tChild, LtsSubstitute e' e2 tChild') -> do
    canRename <- renamesTo e1 sigma e2
    if canRename
      then do
        (tg, theta') <- generalizeLts defs gensym tChild tChild' theta sigma
        return (generalize' (LtsSubstitute e' e2 tg) theta', Map.empty)
      else
        generalizeCatchAll defs gensym t t' theta sigma
  (LtsApplyNeutral x args, LtsApplyNeutral x' args') -> do
    case Map.lookup x sigma of
      Just (Var x'') | x'' == x' -> do
        unless (length args == length args') $ throwIO GeneralizeLtsFailure
        (generalizedArgs, thetaList) <-
          unzip <$> sequence [generalizeLts defs gensym e e' theta sigma | e <- args | e' <- args']
        let newTheta = foldl Map.union Map.empty thetaList
        return (LtsApplyNeutral x' generalizedArgs, newTheta)
      _ -> throwIO GeneralizeLtsFailure
  (LtsConstructor c args, LtsConstructor c' args') | c == c' -> do
    (generalizedArgs, thetaList) <-
      unzip <$> sequence [generalizeLts defs gensym e e' theta sigma | e <- args | e' <- args']
    let newTheta = foldl Map.union Map.empty thetaList
    return (LtsConstructor c' generalizedArgs, newTheta)
  (LtsLambda x tChild, LtsLambda x' tChild') -> do
    let newSigma = Map.insert x (Var x') sigma
    (tg, theta') <- generalizeLts defs gensym tChild tChild' theta newSigma
    return (LtsLambda x' tg, theta')
  (LtsCase tCase branches, LtsCase tCase' branches')
    | length branches == length branches' -> do
        (gcase, thetaCase) <- generalizeLts defs gensym tCase tCase' theta sigma
        (gbranches, thetaList) <-
          unzip
            <$> sequence
              [ do
                  unless (c == c') $ throwIO GeneralizeLtsFailure
                  let newSigma = extendThetaWithVars vars vars' sigma
                  (gbody, thetaBody) <- generalizeLts defs gensym body body' theta newSigma
                  return ((Pattern c' vars', gbody), thetaBody)
                | (Pattern c vars, body) <- branches
                | (Pattern c' vars', body') <- branches'
              ]
        let newTheta = foldl Map.union thetaCase thetaList
        return (LtsCase gcase gbranches, newTheta)
  (LtsElimConstructor c tChild, LtsElimConstructor c' tChild') | c == c' -> do
    (tg, theta') <- generalizeLts defs gensym tChild tChild' theta sigma
    return (LtsElimConstructor c' tg, theta')
  (LtsLet t1 (x, t2), LtsLet t1' (x', t2')) -> do
    (gt1, theta1) <- generalizeLts defs gensym t1 t1' theta sigma
    let newSigma = Map.insert x (Var x') sigma
    (gt2, theta2) <- generalizeLts defs gensym t2 t2' theta newSigma
    let newTheta = Map.union theta1 theta2
    return (LtsLet gt1 (x', gt2), newTheta)
  _ -> generalizeCatchAll defs gensym t t' theta sigma

generalize' :: Lts -> GeneralizationCache -> Lts
generalize' lts theta = Map.foldrWithKey (\x t' acc -> LtsLet acc (x, t')) lts theta

generalizeCatchAll :: DefinitionMap -> Gensym -> Lts -> Lts -> GeneralizationCache -> Sigma -> IO (Lts, GeneralizationCache)
generalizeCatchAll defs gensym _t t' theta sigma = do
  let gvars = Set.toList (Set.intersection (freeVarsLts t') (sigmaRange sigma))
  let t2 = foldr LtsLambda t' gvars
  opportunity <- lookupGeneralizationCache (Map.toList theta) t2
  case opportunity of
    Just x -> do
      return (driveApplication defs x gvars, Map.empty)
    Nothing -> do
      x <- doGensym gensym "v"
      return (driveApplication defs x gvars, Map.singleton x t2)

lookupGeneralizationCache :: [(String, Lts)] -> Lts -> IO (Maybe String)
lookupGeneralizationCache [] _t2 = return Nothing
lookupGeneralizationCache ((x, t1) : rest) t2 = do
  canRename <- ltsRenamesTo t1 t2
  if canRename
    then return (Just x)
    else lookupGeneralizationCache rest t2

foldLts :: Lts -> Sigma -> Lts
foldLts t sigma = Map.foldrWithKey go t sigma
  where
    go x (Var x') acc = LtsLet acc (x, LtsApplyNeutral x' [])
    go _ _ _ = error "Impossible!"

drive :: DefinitionMap -> Term -> Lts
drive defs e = drive' defs Map.empty e

drive' :: DefinitionMap -> Theta -> Term -> Lts
drive' defs theta e = case decompose e of
  Left (OApplyNeutral x args) ->
    case Map.lookup x theta of
      Just some | some /= Var x -> LtsSubstitute e some (drive' defs theta (foldl Apply some args))
      _ -> LtsApplyNeutral x [drive' defs theta e' | e' <- args]
  Left (OCCall c args) -> LtsConstructor c [drive' defs theta e' | e' <- args]
  Left (OLambda x body) -> LtsLambda x (drive' defs theta body)
  Right (ev, RUnfold f) -> LtsUnfold e f (drive' defs theta (ev $ defs Map.! f))
  Right (ev, RApply (x, body) rand) -> drive' defs (Map.insert x rand theta) (ev body)
  Right (ev, RCaseNeutral (x, []) branches) ->
    case Map.lookup x theta of
      Just some | some /= Var x -> LtsSubstitute e some (drive' defs theta (ev $ Case some branches))
      _ ->
        LtsCase
          (drive' defs theta (Var x))
          [ let newTheta = Map.insert x (CCall c (map Var cargs)) theta
             in (pattern, drive' defs newTheta (ev body))
            | (pattern@(Pattern c cargs), body) <- branches
          ]
  Right (ev, RCaseNeutral (x, args) branches) ->
    LtsCase
      (drive' defs theta (foldl Apply (Var x) args))
      [ (pattern, drive' defs theta (ev body))
        | (pattern, body) <- branches
      ]
  Right (ev, RCase (c, args) branches) ->
    case findBranch c branches of
      Just (Pattern _ vars, body) ->
        let newTheta = extendTheta vars args theta
         in LtsElimConstructor c (drive' defs newTheta (ev body))
      Nothing ->
        error $ "No such branch for constructor `" ++ c ++ "`!"

driveApplication :: DefinitionMap -> String -> [String] -> Lts
driveApplication defs x vars = drive defs (applyVars x vars)

embedsLts :: IORef Sigma -> Rho -> Sigma -> (Lts, Lts) -> IO ()
embedsLts sigmaRef rho sigma (t, t') =
  divesLts sigmaRef rho sigma (t, t') `catch` \EmbedsFailure ->
    couplesLts sigmaRef rho sigma (t, t')

divesLts :: IORef Sigma -> Rho -> Sigma -> (Lts, Lts) -> IO ()
divesLts sigmaRef rho sigma = \case
  (t, LtsUnfold _ f t') -> do
    when (Set.member (MemoizeUnfolding f) rho) $ throwIO EmbedsFailure
    embedsLts sigmaRef (Set.insert (MemoizeUnfolding f) rho) sigma (t, t')
  (t, LtsSubstitute _ e' t') -> do
    when (Set.member (MemoizeSubstitution e') rho) $ throwIO EmbedsFailure
    embedsLts sigmaRef (Set.insert (MemoizeSubstitution e') rho) sigma (t, t')
  (t, LtsApplyNeutral _x args) -> divesToAnyLts sigmaRef rho sigma t args
  (t, LtsConstructor _c args) -> divesToAnyLts sigmaRef rho sigma t args
  (t, LtsLambda _x t') -> embedsLts sigmaRef rho sigma (t, t')
  (t, LtsCase t' branches) -> divesToAnyLts sigmaRef rho sigma t (t' : [body | (_pattern, body) <- branches])
  (t, LtsLet t1 (_x, t2)) -> divesToAnyLts sigmaRef rho sigma t [t1, t2]
  (t, LtsElimConstructor _c t') -> embedsLts sigmaRef rho sigma (t, t')

divesToAnyLts :: IORef Sigma -> Rho -> Sigma -> Lts -> [Lts] -> IO ()
divesToAnyLts sigmaRef rho sigma t = \case
  [] -> throwIO EmbedsFailure
  (t' : args) ->
    embedsLts sigmaRef rho sigma (t, t') `catch` \EmbedsFailure ->
      divesToAnyLts sigmaRef rho sigma t args

couplesLts :: IORef Sigma -> Rho -> Sigma -> (Lts, Lts) -> IO ()
couplesLts sigmaRef rho sigma = \case
  (LtsApplyNeutral x args, LtsApplyNeutral x' args') -> do
    case Map.lookup x sigma of
      Just (Var x'') | x'' == x' -> do
        unless (length args == length args') $ throwIO EmbedsFailure
        sequence_ [embedsLts sigmaRef rho sigma (e, e') | e <- args | e' <- args']
      _ -> throwIO EmbedsFailure
  (LtsUnfold _ f t, LtsUnfold _ f' t') | f == f' -> do
    unless (Set.member (MemoizeUnfolding f) rho) $
      embedsLts sigmaRef (Set.insert (MemoizeUnfolding f) rho) sigma (t, t')
  (LtsSubstitute _ e1 t, LtsSubstitute _ e2 t') -> do
    rename (AccumulateThetaRef sigmaRef) e1 sigma e2
      `catch` \RenameFailure -> throwIO EmbedsFailure
    unless (Set.member (MemoizeSubstitution e2) rho) $
      embedsLts sigmaRef (Set.insert (MemoizeSubstitution e2) rho) sigma (t, t')
  (LtsConstructor c args, LtsConstructor c' args') | c == c' -> do
    sequence_ [embedsLts sigmaRef rho sigma (e, e') | e <- args | e' <- args']
  (LtsLambda x t, LtsLambda x' t') -> do
    let newSigma = Map.insert x (Var x') sigma
    embedsLts sigmaRef rho newSigma (t, t')
  (LtsCase t patterns, LtsCase t' patterns') | length patterns == length patterns' -> do
    embedsLts sigmaRef rho sigma (t, t')
    sequence_
      [ do
          unless (c == c') $ throwIO EmbedsFailure
          let newSigma = extendThetaWithVars vars vars' sigma
          embedsLts sigmaRef rho newSigma (body, body')
        | (Pattern c vars, body) <- patterns
        | (Pattern c' vars', body') <- patterns'
      ]
  (LtsElimConstructor c t, LtsElimConstructor c' t')
    | c == c' -> embedsLts sigmaRef rho sigma (t, t')
  (LtsApplyNeutral _ _, _) -> throwIO EmbedsFailure
  (LtsUnfold {}, _) -> throwIO EmbedsFailure
  (LtsSubstitute {}, _) -> throwIO EmbedsFailure
  (LtsConstructor _ _, _) -> throwIO EmbedsFailure
  (LtsLambda _ _, _) -> throwIO EmbedsFailure
  (LtsCase _ _, _) -> throwIO EmbedsFailure
  (LtsLet _ _, _) -> throwIO EmbedsFailure
  (LtsElimConstructor _ _, _) -> throwIO EmbedsFailure

renameLts :: Rho -> IORef Sigma -> (Lts, Lts) -> IO ()
renameLts rho sigmaRef = \case
  (LtsApplyNeutral x args, LtsApplyNeutral x' args') -> do
    sigma <- readIORef sigmaRef
    case Map.lookup x sigma of
      Just (Var x'') -> do
        unless (x'' == x') $ throwIO RenameFailure
        unless (length args == length args') $ throwIO RenameLtsFailure
        sequence_ [renameLts rho sigmaRef (e, e') | e <- args | e' <- args']
      Just _ -> error "Impossible!"
      Nothing ->
        writeIORef sigmaRef (Map.insert x (Var x') sigma)
  (LtsUnfold _ f t, LtsUnfold _ f' t') | f == f' -> do
    unless (Set.member (MemoizeUnfolding f) rho) $
      renameLts (Set.insert (MemoizeUnfolding f) rho) sigmaRef (t, t')
  (LtsSubstitute _ e1 t, LtsSubstitute _ e2 t') -> do
    rename (AccumulateThetaRef sigmaRef) e1 Map.empty e2
      `catch` \RenameFailure -> throwIO RenameLtsFailure
    unless (Set.member (MemoizeSubstitution e2) rho) $
      renameLts (Set.insert (MemoizeSubstitution e2) rho) sigmaRef (t, t')
  (LtsConstructor c args, LtsConstructor c' args')
    | c == c' -> sequence_ [renameLts rho sigmaRef (e, e') | e <- args | e' <- args']
  (LtsLambda x t, LtsLambda x' t') -> do
    sigma <- readIORef sigmaRef
    writeIORef sigmaRef (Map.insert x (Var x') sigma)
    renameLts rho sigmaRef (t, t')
  (LtsCase t patterns, LtsCase t' patterns')
    | length patterns == length patterns' -> do
        renameLts rho sigmaRef (t, t')
        sequence_
          [ do
              unless (c == c') $ throwIO RenameLtsFailure
              sigma <- readIORef sigmaRef
              writeIORef sigmaRef (extendThetaWithVars vars vars' sigma)
              renameLts rho sigmaRef (body, body')
            | (Pattern c vars, body) <- patterns
            | (Pattern c' vars', body') <- patterns'
          ]
  (LtsElimConstructor c t, LtsElimConstructor c' t')
    | c == c' -> renameLts rho sigmaRef (t, t')
  (LtsLet t1 (x, t2), LtsLet t1' (x', t2')) -> do
    renameLts rho sigmaRef (t1, t1')
    sigma <- readIORef sigmaRef
    writeIORef sigmaRef (Map.insert x (Var x') sigma)
    renameLts rho sigmaRef (t2, t2')
  (LtsApplyNeutral _ _, _) -> throwIO RenameLtsFailure
  (LtsUnfold {}, _) -> throwIO RenameLtsFailure
  (LtsSubstitute {}, _) -> throwIO RenameLtsFailure
  (LtsConstructor _ _, _) -> throwIO RenameLtsFailure
  (LtsLambda _ _, _) -> throwIO RenameLtsFailure
  (LtsCase _ _, _) -> throwIO RenameLtsFailure
  (LtsLet _ _, _) -> throwIO RenameLtsFailure
  (LtsElimConstructor _ _, _) -> throwIO RenameLtsFailure

ltsRenamesTo :: Lts -> Lts -> IO Bool
ltsRenamesTo t t' = do
  sigmaRef <- newIORef Map.empty
  result <- try @RenameLtsException $ renameLts Set.empty sigmaRef (t, t')
  case result of
    Right _ -> return True
    Left _ -> return False

residualizeLts :: Gensym -> IORef Epsilon -> Lts -> IO Term
residualizeLts gensym defsRef e = residualizeLts' gensym e defsRef Map.empty

residualizeLts' :: Gensym -> Lts -> IORef DefinitionMap -> Epsilon -> IO Term
residualizeLts' gensym e defsRef epsilon = case e of
  LtsApplyNeutral x args ->
    foldl Apply (Var x) <$> mapM (\e -> residualizeLts' gensym e defsRef epsilon) args
  LtsConstructor c args ->
    CCall c <$> mapM (\e -> residualizeLts' gensym e defsRef epsilon) args
  LtsLambda x body ->
    Lambda x <$> residualizeLts' gensym body defsRef epsilon
  LtsCase t branches -> do
    Case
      <$> residualizeLts' gensym t defsRef epsilon
      <*> mapM
        (\(pattern, body) -> (pattern,) <$> residualizeLts' gensym body defsRef epsilon)
        branches
  LtsLet t0 (x, t1) ->
    substitute x
      <$> residualizeLts' gensym t1 defsRef epsilon
      <*> residualizeLts' gensym t0 defsRef epsilon
  LtsUnfold e _ t -> residualizeWithMemoization gensym e t defsRef epsilon
  LtsSubstitute _e _ t ->
    -- TODO: this is a deviation from the paper, but it works somehow...
    residualizeLts' gensym t defsRef epsilon
  LtsElimConstructor _ t -> residualizeLts' gensym t defsRef epsilon

residualizeWithMemoization :: Gensym -> Term -> Lts -> IORef DefinitionMap -> Epsilon -> IO Term
residualizeWithMemoization gensym e t defsRef epsilon = do
  let fv = Set.toList (freeVarsLts t)
  let target = foldr Lambda e fv
  case Map.lookupMin (Map.filter (== target) epsilon) of
    Just (f, _) -> return $ applyVars f fv
    Nothing -> do
      f <- doGensym gensym "f"
      bodyTerm <- residualizeLts' gensym t defsRef (Map.insert f target epsilon)
      modifyIORef defsRef (Map.insert f (foldr Lambda bodyTerm fv))
      return $ applyVars f fv

-- -----------------------------------------------------------------------------
-- Boring helper functions

freeVars :: Term -> Set.Set String
freeVars = \case
  Var x -> Set.singleton x
  CCall _ args -> Set.unions (map freeVars args)
  Unfold _ -> Set.empty
  Lambda x body -> Set.delete x (freeVars body)
  Apply t1 t2 -> Set.union (freeVars t1) (freeVars t2)
  Case t branches ->
    Set.union (freeVars t) $
      Set.unions
        [Set.difference (freeVars body) (Set.fromList vars) | (Pattern _ vars, body) <- branches]

substitute :: String -> Term -> Term -> Term
substitute var replacement = go
  where
    go = \case
      Var x -> if x == var then replacement else Var x
      CCall c args -> CCall c (map go args)
      Unfold f -> Unfold f
      Lambda x body -> if x == var then Lambda x body else Lambda x (go body)
      Apply t1 t2 -> Apply (go t1) (go t2)
      Case t branches ->
        Case
          (go t)
          [ if var `elem` vars then (Pattern c vars, body) else (Pattern c vars, go body)
            | (Pattern c vars, body) <- branches
          ]

freeVarsLts :: Lts -> Set.Set String
freeVarsLts = \case
  LtsApplyNeutral x args -> Set.insert x (Set.unions (map freeVarsLts args))
  LtsConstructor _ args -> Set.unions (map freeVarsLts args)
  LtsLambda x body -> Set.delete x (freeVarsLts body)
  LtsCase t branches ->
    Set.union (freeVarsLts t) $
      Set.unions
        [ Set.difference (freeVarsLts body) (Set.fromList vars)
          | (Pattern _c vars, body) <- branches
        ]
  LtsLet body (x, binding) ->
    Set.union (Set.delete x (freeVarsLts body)) (freeVarsLts binding)
  LtsUnfold _ _ body -> freeVarsLts body
  LtsElimConstructor _ body -> freeVarsLts body
  LtsSubstitute _ _ body -> freeVarsLts body

substituteVarLts :: Lts -> String -> String -> Lts
substituteVarLts lts x y = go lts
  where
    go = \case
      LtsApplyNeutral x' args -> LtsApplyNeutral (if x' == x then y else x') (map go args)
      LtsConstructor c args -> LtsConstructor c (map go args)
      LtsLambda x' body
        | x' == x -> LtsLambda x' body
        | otherwise -> LtsLambda x' (go body)
      LtsCase t branches -> LtsCase (go t) (map goBranch branches)
        where
          goBranch (Pattern c vars, body)
            | x `elem` vars = (Pattern c vars, body)
            | otherwise = (Pattern c vars, go body)
      LtsLet body (x', binding)
        | x' == x -> LtsLet body (x', binding)
        | otherwise -> LtsLet (go body) (x', go binding)
      LtsUnfold e f body -> LtsUnfold e f (go body)
      LtsElimConstructor c body -> LtsElimConstructor c (go body)
      LtsSubstitute e e' body -> LtsSubstitute e e' (go body)
