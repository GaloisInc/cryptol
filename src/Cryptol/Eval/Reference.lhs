> -- |
> -- Module      :  $Header$
> -- Description :  The reference implementation of the Cryptol evaluation semantics.
> -- Copyright   :  (c) 2013-2016 Galois, Inc.
> -- License     :  BSD3
> -- Maintainer  :  cryptol@galois.com
> -- Stability   :  provisional
> -- Portability :  portable
>
> {-# LANGUAGE PatternGuards #-}
>
> module Cryptol.Eval.Reference where
>
> import Control.Applicative (liftA2)
> import Control.Monad (foldM)
> import Data.Bits
> import Data.List
>   (genericDrop, genericIndex, genericLength, genericReplicate, genericSplitAt,
>    genericTake, sortBy, transpose)
> import Data.Ord (comparing)
> import qualified Data.Map as Map
> import qualified Data.Text as T (pack)
>
> import Cryptol.ModuleSystem.Name (asPrim)
> import Cryptol.TypeCheck.Solver.InfNat (Nat'(..))
> import Cryptol.TypeCheck.AST
> import Cryptol.Eval.Monad (EvalError(..))
> import Cryptol.Eval.Type (TypeEnv, TValue(..), isTBit, evalValType, evalNumType, tvSeq)
> import Cryptol.Prims.Eval (lg2, divModPoly)
> import Cryptol.Utils.Ident (Ident, mkIdent)
> import Cryptol.Utils.Panic (panic)
> import Cryptol.Utils.PP
>
> import qualified Cryptol.ModuleSystem as M
> import qualified Cryptol.ModuleSystem.Env as M (loadedModules)
> --import qualified Cryptol.ModuleSystem.Monad as M
>
>
> -- Module Command --------------------------------------------------------------
>
> evaluate :: Expr -> M.ModuleCmd Value
> evaluate expr modEnv = return (Right (evalExpr env expr, modEnv), [])
>   where
>     extDgs = concatMap mDecls (M.loadedModules modEnv)
>     env = foldl evalDeclGroup mempty extDgs
>
>
> -- Values ----------------------------------------------------------------------
>
> -- | Value type for the reference evaluator. Invariant: Undefinedness
> -- and run-time exceptions are only allowed inside a @Bool@ argument
> -- of a @VBit@ constructor. All other @Value@ and list constructors
> -- should evaluate without error.
> data Value
>   = VRecord [(Ident, Value)]     -- ^ @ { .. } @
>   | VTuple [Value]               -- ^ @ ( .. ) @
>   | VBit (Either EvalError Bool) -- ^ @ Bit    @
>   | VList [Value]                -- ^ @ [n]a   @ (either finite or infinite)
>   | VFun (Value -> Value)        -- ^ functions
>   | VPoly (TValue -> Value)      -- ^ polymorphic values (kind *)
>   | VNumPoly (Nat' -> Value)     -- ^ polymorphic values (kind #)
>
> -- | Destructor for @VBit@.
> fromVBit :: Value -> Either EvalError Bool
> fromVBit (VBit b) = b
> fromVBit _        = evalPanic "fromVBit" ["Expected a bit"]
>
> -- | Destructor for @VList@.
> fromVList :: Value -> [Value]
> fromVList (VList vs) = vs
> fromVList _          = evalPanic "fromVList" ["Expected a list"]
>
> -- | Destructor for @VTuple@.
> fromVTuple :: Value -> [Value]
> fromVTuple (VTuple vs) = vs
> fromVTuple _           = evalPanic "fromVTuple" ["Expected a tuple"]
>
> -- | Destructor for @VFun@.
> fromVFun :: Value -> (Value -> Value)
> fromVFun (VFun f) = f
> fromVFun _        = evalPanic "fromVFun" ["Expected a function"]
>
> -- | Destructor for @VPoly@.
> fromVPoly :: Value -> (TValue -> Value)
> fromVPoly (VPoly f) = f
> fromVPoly _         = evalPanic "fromVPoly" ["Expected a polymorphic value"]
>
> -- | Destructor for @VNumPoly@.
> fromVNumPoly :: Value -> (Nat' -> Value)
> fromVNumPoly (VNumPoly f) = f
> fromVNumPoly _            = evalPanic "fromVNumPoly" ["Expected a polymorphic value"]
>
> -- | Destructor for @VRecord@.
> fromVRecord :: Value -> [(Ident, Value)]
> fromVRecord (VRecord fs) = fs
> fromVRecord _            = evalPanic "fromVRecord" ["Expected a record"]
>
> -- | Look up a field in a record.
> lookupRecord :: Ident -> Value -> Value
> lookupRecord f v =
>   case lookup f (fromVRecord v) of
>     Just val -> val
>     Nothing  -> evalPanic "lookupRecord" ["Malformed record"]
>
> -- | Convert a list of booleans in big-endian format to an integer.
> bitsToInteger :: [Bool] -> Integer
> bitsToInteger bs = foldl f 0 bs
>   where f x b = if b then 2 * x + 1 else 2 * x
>
> -- | Convert an integer to a big-endian format of the specified width.
> integerToBits :: Integer -> Integer -> [Bool]
> integerToBits w x = go [] w x
>   where go bs 0 _ = bs
>         go bs n a = go (odd a : bs) (n - 1) $! (a `div` 2)
>
> -- | Convert a value from a big-endian binary format to an integer.
> fromVWord :: Value -> Either EvalError Integer
> fromVWord v = fmap bitsToInteger (mapM fromVBit (fromVList v))
>
> -- | Convert an integer to big-endian binary value of the specified width.
> vWordValue :: Integer -> Integer -> Value
> vWordValue w x = VList (map (VBit . Right) (integerToBits w x))
>
> -- | Create a run-time error value of bitvector type.
> vWordError :: Integer -> EvalError -> Value
> vWordError w e = VList (genericReplicate w (VBit (Left e)))
>
> vWord :: Integer -> Either EvalError Integer -> Value
> vWord w (Left e) = vWordError w e
> vWord w (Right x) = vWordValue w x
>
> vFinPoly :: (Integer -> Value) -> Value
> vFinPoly f = VNumPoly g
>   where
>     g (Nat n) = f n
>     g Inf     = evalPanic "vFinPoly" ["Expected finite numeric type"]
>
>
> -- Conditionals ----------------------------------------------------------------
>
> condBit :: Either e Bool -> Either e a -> Either e a -> Either e a
> condBit (Left e)  _ _ = Left e
> condBit (Right b) x y = if b then x else y
>
> condValue :: Either EvalError Bool -> Value -> Value -> Value
> condValue c l r =
>   case l of
>     VRecord fs -> VRecord [ (f, condValue c v (lookupRecord f r)) | (f, v) <- fs ]
>     VTuple vs  -> VTuple (zipWith (condValue c) vs (fromVList r))
>     VBit b     -> VBit (condBit c b (fromVBit r))
>     VList vs   -> VList (zipWith (condValue c) vs (fromVList r))
>     VFun f     -> VFun (\v -> condValue c (f v) (fromVFun r v))
>     VPoly f    -> VPoly (\t -> condValue c (f t) (fromVPoly r t))
>     VNumPoly f -> VNumPoly (\n -> condValue c (f n) (fromVNumPoly r n))
>
>
> -- Environments ----------------------------------------------------------------
>
> -- | Evaluation environment.
> data Env = Env
>   { envVars       :: !(Map.Map Name Value)
>   , envTypes      :: !TypeEnv
>   }
>
> instance Monoid Env where
>   mempty = Env
>     { envVars  = Map.empty
>     , envTypes = Map.empty
>     }
>   mappend l r = Env
>     { envVars  = Map.union (envVars  l) (envVars  r)
>     , envTypes = Map.union (envTypes l) (envTypes r)
>     }
>
> -- | Bind a variale in the evaluation environment.
> bindVar :: (Name, Value) -> Env -> Env
> bindVar (n, val) env = env { envVars = Map.insert n val (envVars env) }
>
> -- | Bind a type variable of kind # or *.
> bindType :: TVar -> Either Nat' TValue -> Env -> Env
> bindType p ty env = env { envTypes = Map.insert p ty (envTypes env) }
>
>
> -- Evaluation ----------------------------------------------------------------
>
> -- | Evaluate a Cryptol expression to a value.
> evalExpr :: Env     -- ^ Evaluation environment
>          -> Expr    -- ^ Expression to evaluate
>          -> Value
> evalExpr env expr =
>   case expr of
>
>     EList es _ty   -> VList [ evalExpr env e | e <- es ]
>     ETuple es      -> VTuple [ evalExpr env e | e <- es ]
>     ERec fields    -> VRecord [ (f, evalExpr env e) | (f, e) <- fields ]
>     ESel e sel     -> evalSel (evalExpr env e) sel
>     EIf c t f      -> condValue (fromVBit (evalExpr env c)) (evalExpr env t) (evalExpr env f)
>
>     EComp _n _ty h gs ->
>       evalComp env h gs
>
>     EVar n ->
>       case Map.lookup n (envVars env) of
>         Just val -> val
>         Nothing  -> evalPanic "evalExpr" ["var `" ++ show (pp n) ++ "` is not defined" ]
>
>     ETAbs tv b ->
>       case tpKind tv of
>         KType -> VPoly    $ \ty -> evalExpr (bindType (tpVar tv) (Right ty) env) b
>         KNum  -> VNumPoly $ \n  -> evalExpr (bindType (tpVar tv) (Left n) env) b
>         k     -> evalPanic "evalExpr" ["Invalid kind on type abstraction", show k]
>
>     ETApp e ty ->
>       case evalExpr env e of
>         VPoly f     -> f $! (evalValType (envTypes env) ty)
>         VNumPoly f  -> f $! (evalNumType (envTypes env) ty)
>         _           -> evalPanic "evalExpr" ["Expected a polymorphic value"]
>
>     EApp e1 e2     -> fromVFun (evalExpr env e1) (evalExpr env e2)
>     EAbs n _ty b   -> VFun (\v -> evalExpr (bindVar (n, v) env) b)
>     EProofAbs _ e  -> evalExpr env e
>     EProofApp e    -> evalExpr env e
>     EWhere e dgs   -> evalExpr (foldl evalDeclGroup env dgs) e
>
>
> -- | Apply the the given "selector" form to the given value.  This function pushes
> --   tuple and record selections pointwise down into other value constructs
> --   (e.g., streams and functions).
> evalSel :: Value -> Selector -> Value
> evalSel val sel =
>   case sel of
>     TupleSel n _  -> tupleSel n val
>     RecordSel n _ -> recordSel n val
>     ListSel n _  -> listSel n val
>   where
>
>     tupleSel n v =
>       case v of
>         VTuple vs   -> vs !! n
>         VList vs    -> VList (map (tupleSel n) vs)
>         VFun f      -> VFun (\x -> tupleSel n (f x))
>         _           -> evalPanic "evalSel"
>                        ["Unexpected value in tuple selection."]
>
>     recordSel n v =
>       case v of
>         VRecord _   -> lookupRecord n v
>         VList vs    -> VList (map (recordSel n) vs)
>         VFun f      -> VFun (\x -> recordSel n (f x))
>         _           -> evalPanic "evalSel"
>                        ["Unexpected value in record selection."]
>
>     listSel n v =
>       case v of
>         VList vs    -> vs !! n
>         _           -> evalPanic "evalSel"
>                        ["Unexpected value in list selection."]
>
>
> -- List Comprehensions ---------------------------------------------------------
>
> -- | Evaluate a comprehension.
> evalComp :: Env         -- ^ Starting evaluation environment
>          -> Expr        -- ^ Head expression of the comprehension
>          -> [[Match]]   -- ^ List of parallel comprehension branches
>          -> Value
> evalComp env body ms = VList [ evalExpr e body | e <- envs ]
>   where
>     -- | Generate a new environment for each iteration of each parallel branch
>     benvs :: [[Env]]
>     benvs = map (branchEnvs env) ms
>
>     -- | Take parallel slices of each environment.  When the length of the list
>     -- drops below the number of branches, one branch has terminated.
>     slices :: [[Env]]
>     slices = takeWhile allBranches (transpose benvs)
>       where allBranches es = length es == length ms
>
>     -- | Join environments to produce environments at each step through the process.
>     envs :: [Env]
>     envs = map mconcat slices
>
> -- | Turn a list of matches into the final environments for each iteration of
> -- the branch.
> branchEnvs :: Env -> [Match] -> [Env]
> branchEnvs env matches = foldM evalMatch env matches
>
> -- | Turn a match into the list of environments it represents.
> evalMatch :: Env -> Match -> [Env]
> evalMatch env m =
>   case m of
>     Let d ->
>       [ bindVar (evalDecl env d) env ]
>     From n _l _ty expr ->
>       [ bindVar (n, v) env | v <- fromVList (evalExpr env expr) ]
>
>
> -- Declarations ----------------------------------------------------------------
>
> -- | Extend the given evaluation environment with the result of
> -- evaluating the given declaration group.
> evalDeclGroup :: Env -> DeclGroup -> Env
> evalDeclGroup env dg = do
>   case dg of
>     NonRecursive d ->
>       bindVar (evalDecl env d) env
>     Recursive ds ->
>       let env' = foldr bindVar env bindings
>           bindings = map (evalDeclRecursive env') ds
>       in env'
>
> -- | Evaluate a declaration.
> evalDecl :: Env -> Decl -> (Name, Value)
> evalDecl env d =
>   case dDefinition d of
>     DPrim   -> (dName d, evalPrim (dName d))
>     DExpr e -> (dName d, evalExpr env e)
>
> -- | Evaluate a declaration in a recursive context, performing a
> -- type-directed copy to build the spine of the value.
> evalDeclRecursive :: Env -> Decl -> (Name, Value)
> evalDeclRecursive env d =
>   case dDefinition d of
>     DPrim   -> (dName d, evalPrim (dName d))
>     DExpr e -> (dName d, copyBySchema env (dSignature d) (evalExpr env e))
>
> -- | Make a copy of the given value, building the spine based only on
> -- the type without forcing the value argument. This ensures that
> -- undefinedness appears in @Bool@ values, and never on any
> -- constructors of the @Value@ type. In turn, this gives the
> -- appropriate semantics to recursive definitions: The bottom value
> -- for a compound type is equal to a value of the same type where
> -- every individual bit is bottom.
> copyBySchema :: Env -> Schema -> Value -> Value
> copyBySchema env0 (Forall params _props ty) = go params env0
>   where
>     go []       env v = copyByTValue (evalValType (envTypes env) ty) v
>     go (p : ps) env v =
>       case v of
>         VPoly    f -> VPoly    $ \t -> go ps (bindType (tpVar p) (Right t) env) (f t)
>         VNumPoly f -> VNumPoly $ \n -> go ps (bindType (tpVar p) (Left n)  env) (f n)
>         _          -> evalPanic "copyBySchema" ["Expected polymorphic value"]
>
> copyByTValue :: TValue -> Value -> Value
> copyByTValue = go
>   where
>     go :: TValue -> Value -> Value
>     go ty val =
>       case ty of
>         TVBit        -> VBit (fromVBit val)
>         TVSeq w ety  -> VList (map (go ety) (copyList w (fromVList val)))
>         TVStream ety -> VList (map (go ety) (copyStream (fromVList val)))
>         TVTuple etys -> VTuple (zipWith go etys (copyList (genericLength etys) (fromVTuple val)))
>         TVFun _ bty  -> VFun (\v -> go bty (fromVFun val v))
>         TVRec fields -> VRecord [ (f, go fty (lookupRecord f val)) | (f, fty) <- fields ]
>
> copyStream :: [a] -> [a]
> copyStream xs = head xs : copyStream (tail xs)
>
> copyList :: Integer -> [a] -> [a]
> copyList 0 _ = []
> copyList n xs = head xs : copyList (n - 1) (tail xs)
>
>
> -- Primitives ------------------------------------------------------------------
>
> evalPrim :: Name -> Value
> evalPrim n
>   | Just i <- asPrim n, Just v <- Map.lookup i primTable = v
>   | otherwise = evalPanic "evalPrim" ["Unimplemented primitive", show n]
>
> primTable :: Map.Map Ident Value
> primTable = Map.fromList $ map (\(n, v) -> (mkIdent (T.pack n), v))
>   [ ("+"          , binary (arithBinary (\_ x y -> Right (x + y))))
>   , ("-"          , binary (arithBinary (\_ x y -> Right (x - y))))
>   , ("*"          , binary (arithBinary (\_ x y -> Right (x * y))))
>   , ("/"          , binary (arithBinary (const divWrap)))
>   , ("%"          , binary (arithBinary (const modWrap)))
>   -- , ("^^"         , binary (arithBinary modExp))
>   , ("lg2"        , unary  (arithUnary (const lg2)))
>   , ("negate"     , unary  (arithUnary (const negate)))
>   , ("<"          , binary (cmpOrder (\o -> o == LT)))
>   , (">"          , binary (cmpOrder (\o -> o == GT)))
>   , ("<="         , binary (cmpOrder (\o -> o /= GT)))
>   , (">="         , binary (cmpOrder (\o -> o /= LT)))
>   , ("=="         , binary (cmpOrder (\o -> o == EQ)))
>   , ("!="         , binary (cmpOrder (\o -> o /= EQ)))
>   , ("&&"         , binary (logicBinary (&&)))
>   , ("||"         , binary (logicBinary (||)))
>   , ("^"          , binary (logicBinary (/=)))
>   , ("complement" , unary  (logicUnary not))
>   , ("<<"         , shiftV shiftLV)
>   , (">>"         , shiftV shiftRV)
>   , ("<<<"        , rotateV rotateLV)
>   , (">>>"        , rotateV rotateRV)
>   , ("True"       , VBit (Right True))
>   , ("False"      , VBit (Right False))
>
>   , ("demote"     , vFinPoly $ \val ->
>                     vFinPoly $ \bits ->
>                     vWordValue bits val)
>
>   , ("#"          , VNumPoly $ \_front ->
>                     VNumPoly $ \_back  ->
>                     VPoly $ \_elty  ->
>                     VFun $ \l ->
>                     VFun $ \r -> VList (fromVList l ++ fromVList r))
>
>   , ("@"          , indexPrimOne  indexFront)
>   , ("@@"         , indexPrimMany indexFront)
>   , ("!"          , indexPrimOne  indexBack)
>   , ("!!"         , indexPrimMany indexBack)
>
>   , ("update"     , updatePrim updateFront)
>   , ("updateEnd"  , updatePrim updateBack)
>
>   , ("zero"       , VPoly (logicNullary (Right False)))
>
>   , ("join"       , VNumPoly $ \_parts ->
>                     VNumPoly $ \_each  ->
>                     VPoly $ \_a ->
>                     VFun $ \xss ->
>                     VList (concat (map fromVList (fromVList xss))))
>     -- FIXME: this doesn't handle the case [inf][0] -> [0]
>
>   , ("split"      , VNumPoly $ \parts ->
>                     vFinPoly $ \each  ->
>                     VPoly $ \_a ->
>                     VFun $ \val -> VList (splitV parts each (fromVList val)))
>
>   , ("splitAt"    , vFinPoly $ \front ->
>                     VNumPoly $ \_back ->
>                     VPoly $ \_a ->
>                     VFun $ \v ->
>                     let (xs, ys) = genericSplitAt front (fromVList v)
>                     in VTuple [VList xs, VList ys])
>
>   , ("fromThen"   , vFinPoly $ \first ->
>                     vFinPoly $ \next  ->
>                     vFinPoly $ \bits  ->
>                     vFinPoly $ \len   ->
>                     VList (map (vWordValue bits) (genericTake len [first, next ..])))
>
>   , ("fromTo"     , vFinPoly $ \first ->
>                     vFinPoly $ \lst   ->
>                     vFinPoly $ \bits  ->
>                     VList (map (vWordValue bits) [first .. lst]))
>
>   , ("fromThenTo" , vFinPoly $ \first ->
>                     vFinPoly $ \next  ->
>                     vFinPoly $ \_lst  ->
>                     vFinPoly $ \bits  ->
>                     vFinPoly $ \len   ->
>                     VList (map (vWordValue bits) (genericTake len [first, next ..])))
>
>   , ("infFrom"    , vFinPoly $ \bits ->
>                     VFun $ \first ->
>                     case fromVWord first of
>                       Left e -> VList (repeat (vWordError bits e))
>                       Right i -> VList (map (vWordValue bits) [i ..]))
>
>   , ("infFromThen", vFinPoly $ \bits ->
>                     VFun $ \first ->
>                     VFun $ \next ->
>                     case fromVWord first of
>                       Left e -> VList (repeat (vWordError bits e))
>                       Right i ->
>                         case fromVWord next of
>                           Left e -> VList (repeat (vWordError bits e))
>                           Right j -> VList (map (vWordValue bits) [i, j ..]))
>
>   , ("error"      , VPoly $ \a ->
>                     VNumPoly $ \_ ->
>                     VFun $ \_s -> logicNullary (Left (UserError "error")) a)
>                     -- TODO: obtain error string from argument s
>
>   , ("reverse"    , VNumPoly $ \_a ->
>                     VPoly $ \_b ->
>                     VFun $ \(VList vs) -> VList (reverse vs))
>
>   , ("transpose"  , VNumPoly $ \_a ->
>                     VNumPoly $ \b ->
>                     VPoly $ \_c ->
>                     VFun $ \v ->
>                     VList (map VList (transposeV b (map fromVList (fromVList v)))))
>
>   , ("pmult"      , let mul res _  _  0 = res
>                         mul res bs as n = mul (if even as then res else xor res bs)
>                                           (bs `shiftL` 1) (as `shiftR` 1) (n-1)
>                     in vFinPoly $ \a ->
>                        vFinPoly $ \b ->
>                        VFun $ \x ->
>                        VFun $ \y ->
>                        case fromVWord x of
>                          Left e -> vWordError (1 + a + b) e
>                          Right i ->
>                            case fromVWord y of
>                              Left e -> vWordError (1 + a + b) e
>                              Right j -> vWordValue (1 + a + b) (mul 0 i j (1+b)))
>   , ("pdiv"       , vFinPoly $ \a ->
>                     vFinPoly $ \b ->
>                     VFun $ \x ->
>                     VFun $ \y ->
>                     case fromVWord x of
>                       Left e -> vWordError a e
>                       Right i ->
>                         case fromVWord y of
>                           Left e -> vWordError a e
>                           Right j -> vWordValue a (fst (divModPoly i (fromInteger a) j (fromInteger b))))
>
>   , ("pmod"       , vFinPoly $ \a ->
>                     vFinPoly $ \b ->
>                     VFun $ \x ->
>                     VFun $ \y ->
>                     case fromVWord x of
>                       Left e -> vWordError b e
>                       Right i ->
>                         case fromVWord y of
>                           Left e -> vWordError b e
>                           Right j -> vWordValue b (snd (divModPoly i (fromInteger a) j (fromInteger b + 1))))
> {-
>   , ("random"     , VPoly $ \a ->
>                     wVFun $ \(bvVal -> x) -> return $ randomV a x)
>   , ("trace"      , VNumPoly $ \_n ->
>                     VPoly $ \_a ->
>                     VPoly $ \_b ->
>                      VFun $ \s ->
>                      VFun $ \x ->
>                      VFun $ \y ->
>                         msg <- fromStr =<< s
>                         doc <- ppValue defaultPPOpts =<< x
>                         yv <- y
>                         io $ putStrLn $ show $ if null msg then
>                                                  doc
>                                                else
>                                                  text msg <+> doc
>                         return yv)
> -}
>   ]
>
> unary :: (TValue -> Value -> Value) -> Value
> unary f = VPoly $ \ty -> VFun $ \x -> f ty x
>
> binary :: (TValue -> Value -> Value -> Value) -> Value
> binary f = VPoly $ \ty -> VFun $ \x -> VFun $ \y -> f ty x y
>
> type Unary = TValue -> Value -> Value
> type Binary = TValue -> Value -> Value -> Value
>
>
> -- Arith -----------------------------------------------------------------------
>
> arithUnary :: (Integer -> Integer -> Integer)
>            -> TValue -> Value -> Value
> arithUnary op = go
>   where
>     go :: TValue -> Value -> Value
>     go ty val =
>       case ty of
>         TVBit ->
>           evalPanic "arithUnary" ["Bit not in class Arith"]
>         TVSeq w a
>           | isTBit a  -> vWord w (op w <$> fromVWord val)
>           | otherwise -> VList (map (go a) (fromVList val))
>         TVStream a ->
>           VList (map (go a) (fromVList val))
>         TVFun _ ety ->
>           VFun (\x -> go ety (fromVFun val x))
>         TVTuple tys ->
>           VTuple (zipWith go tys (fromVTuple val))
>         TVRec fs ->
>           VRecord [ (f, go fty (lookupRecord f val)) | (f, fty) <- fs ]
>
> arithBinary :: (Integer -> Integer -> Integer -> Either EvalError Integer)
>             -> TValue -> Value -> Value -> Value
> arithBinary op = go
>   where
>     go :: TValue -> Value -> Value -> Value
>     go ty l r =
>       case ty of
>         TVBit ->
>           evalPanic "arithBinary" ["Bit not in class Arith"]
>         TVSeq w a
>           | isTBit a  -> case fromVWord l of
>                            Left e -> vWordError w e
>                            Right i ->
>                              case fromVWord r of
>                                Left e -> vWordError w e
>                                Right j -> vWord w (op w i j)
>           | otherwise -> VList (zipWith (go a) (fromVList l) (fromVList r))
>         TVStream a ->
>           VList (zipWith (go a) (fromVList l) (fromVList r))
>         TVFun _ ety ->
>           VFun (\x -> go ety (fromVFun l x) (fromVFun r x))
>         TVTuple tys ->
>           VTuple (zipWith3 go tys (fromVTuple l) (fromVTuple r))
>         TVRec fs ->
>           VRecord [ (f, go fty (lookupRecord f l) (lookupRecord f r)) | (f, fty) <- fs ]
>
> divWrap :: Integer -> Integer -> Either EvalError Integer
> divWrap _ 0 = Left DivideByZero
> divWrap x y = Right (x `div` y)
>
> modWrap :: Integer -> Integer -> Either EvalError Integer
> modWrap _ 0 = Left DivideByZero
> modWrap x y = Right (x `mod` y)
>
> -- Cmp -------------------------------------------------------------------------
>
> -- | Process two elements based on their lexicographic ordering.
> cmpOrder :: (Ordering -> Bool) -> TValue -> Value -> Value -> Value
> cmpOrder p ty l r = VBit (fmap p (lexCompare ty l r))
>
> -- | Lexicographic ordering on two values.
> lexCompare :: TValue -> Value -> Value -> Either EvalError Ordering
> lexCompare ty l r =
>   case ty of
>     TVBit ->
>       compare <$> fromVBit l <*> fromVBit r
>     TVSeq _w ety ->
>       lexList (zipWith (lexCompare ety) (fromVList l) (fromVList r))
>     TVStream _ ->
>       evalPanic "lexCompare" ["invalid type"]
>     TVFun _ _ ->
>       evalPanic "lexCompare" ["invalid type"]
>     TVTuple etys ->
>       lexList (zipWith3 lexCompare etys (fromVList l) (fromVList r))
>     TVRec fields ->
>       let tys    = map snd (sortBy (comparing fst) fields)
>           ls     = map snd (sortBy (comparing fst) (fromVRecord l))
>           rs     = map snd (sortBy (comparing fst) (fromVRecord r))
>        in lexList (zipWith3 lexCompare tys ls rs)
>
> -- TODO: should we make this strict in both arguments?
> lexOrdering :: Either EvalError Ordering -> Either EvalError Ordering -> Either EvalError Ordering
> lexOrdering (Left e)   _ = Left e
> lexOrdering (Right LT) _ = Right LT
> lexOrdering (Right EQ) y = y
> lexOrdering (Right GT) _ = Right GT
>
> lexList :: [Either EvalError Ordering] -> Either EvalError Ordering
> lexList = foldr lexOrdering (Right EQ)
>
>
> -- Logic -----------------------------------------------------------------------
>
> logicNullary :: Either EvalError Bool -> TValue -> Value
> logicNullary b = go
>   where
>     go TVBit          = VBit b
>     go (TVSeq n ety)  = VList (genericReplicate n (go ety))
>     go (TVStream ety) = VList (repeat (go ety))
>     go (TVFun _ bty)  = VFun (\_ -> go bty)
>     go (TVTuple tys)  = VTuple (map go tys)
>     go (TVRec fields) = VRecord [ (f, go fty) | (f, fty) <- fields ]
>
> logicUnary :: (Bool -> Bool) -> TValue -> Value -> Value
> logicUnary op = go
>   where
>     go :: TValue -> Value -> Value
>     go ty val =
>       case ty of
>         TVBit        -> VBit (fmap op (fromVBit val))
>         TVSeq _w ety -> VList (map (go ety) (fromVList val))
>         TVStream ety -> VList (map (go ety) (fromVList val))
>         TVTuple etys -> VTuple (zipWith go etys (fromVTuple val))
>         TVFun _ bty  -> VFun (\v -> go bty (fromVFun val v))
>         TVRec fields -> VRecord [ (f, go fty (lookupRecord f val)) | (f, fty) <- fields ]
>
> logicBinary :: (Bool -> Bool -> Bool) -> TValue -> Value -> Value -> Value
> logicBinary op = go
>   where
>     go :: TValue -> Value -> Value -> Value
>     go ty l r =
>       case ty of
>         TVBit        -> VBit (liftA2 op (fromVBit l) (fromVBit r))
>         TVSeq _w ety -> VList (zipWith (go ety) (fromVList l) (fromVList r))
>         TVStream ety -> VList (zipWith (go ety) (fromVList l) (fromVList r))
>         TVTuple etys -> VTuple (zipWith3 go etys (fromVTuple l) (fromVTuple r))
>         TVFun _ bty  -> VFun (\v -> go bty (fromVFun l v) (fromVFun r v))
>         TVRec fields -> VRecord [ (f, go fty (lookupRecord f l) (lookupRecord f r))
>                                 | (f, fty) <- fields ]
>
>
> -- Sequence Primitives ---------------------------------------------------------
>
> shiftV :: (Nat' -> Value -> [Value] -> Integer -> [Value]) -> Value
> shiftV op =
>   VNumPoly $ \a ->
>   VNumPoly $ \_b ->
>   VPoly $ \c ->
>   VFun $ \v ->
>   VFun $ \x ->
>   case fromVWord x of
>     Left e -> logicNullary (Left e) (tvSeq a c)
>     Right i -> VList (op a (logicNullary (Right False) c) (fromVList v) i)
>
> shiftLV :: Nat' -> Value -> [Value] -> Integer -> [Value]
> shiftLV w z vs i =
>   case w of
>     Nat n -> genericDrop (min n i) vs ++ genericReplicate (min n i) z
>     Inf   -> genericDrop i vs
>
> shiftRV :: Nat' -> Value -> [Value] -> Integer -> [Value]
> shiftRV w z vs i =
>   case w of
>     Nat n -> genericReplicate (min n i) z ++ genericTake (n - min n i) vs
>     Inf   -> genericReplicate i z ++ vs
>
> rotateV :: (Integer -> [Value] -> Integer -> [Value]) -> Value
> rotateV op =
>   vFinPoly $ \a ->
>   VNumPoly $ \_b ->
>   VPoly $ \c ->
>   VFun $ \v ->
>   VFun $ \x ->
>   case fromVWord x of
>     Left e -> VList (genericReplicate a (logicNullary (Left e) c))
>     Right i -> VList (op a (fromVList v) i)
>
> rotateLV :: Integer -> [Value] -> Integer -> [Value]
> rotateLV 0 vs _ = vs
> rotateLV w vs i = ys ++ xs
>   where (xs, ys) = genericSplitAt (i `mod` w) vs
>
> rotateRV :: Integer -> [Value] -> Integer -> [Value]
> rotateRV 0 vs _ = vs
> rotateRV w vs i = ys ++ xs
>   where (xs, ys) = genericSplitAt ((w - i) `mod` w) vs
>
> splitV :: Nat' -> Integer -> [Value] -> [Value]
> splitV w k xs =
>   case w of
>     Nat 0 -> []
>     Nat n -> VList ys : splitV (Nat (n - 1)) k zs
>     Inf   -> VList ys : splitV Inf k zs
>   where
>     (ys, zs) = genericSplitAt k xs
>
> transposeV :: Nat' -> [[Value]] -> [[Value]]
> transposeV w xss =
>   case w of
>     Nat 0 -> []
>     Nat n -> xs : transposeV (Nat (n - 1)) xss'
>     Inf   -> xs : transposeV Inf xss'
>   where
>     (xs, xss') = dest xss
>
>     dest :: [[Value]] -> ([Value], [[Value]])
>     dest [] = ([], [])
>     dest ([] : _) = evalPanic "transposeV" ["Expected non-empty list"]
>     dest ((y : ys) : yss) = (y : zs, ys : zss)
>       where (zs, zss) = dest yss
>
> -- | Indexing operations that return one element.
> indexPrimOne :: (Nat' -> TValue -> [Value] -> Integer -> Value) -> Value
> indexPrimOne op =
>   VNumPoly $ \n ->
>   VPoly $ \a ->
>   VNumPoly $ \_w ->
>   VFun $ \l ->
>   VFun $ \r ->
>   case fromVWord r of
>     Left e -> logicNullary (Left e) a
>     Right i -> op n a (fromVList l) i
>
> -- | Indexing operations that return many elements.
> indexPrimMany :: (Nat' -> TValue -> [Value] -> Integer -> Value) -> Value
> indexPrimMany op =
>   VNumPoly $ \n ->
>   VPoly    $ \a ->
>   VNumPoly $ \_m ->
>   VNumPoly $ \_w ->
>   VFun $ \l ->
>   VFun $ \r -> VList [ case fromVWord y of
>                          Left e -> logicNullary (Left e) a
>                          Right i -> op n a xs i
>                      | let xs = fromVList l, y <- fromVList r ]
>
> indexFront :: Nat' -> TValue -> [Value] -> Integer -> Value
> indexFront w a vs ix =
>   case w of
>     Nat n | n <= ix -> logicNullary (Left (InvalidIndex ix)) a
>     _               -> genericIndex vs ix
>
> indexBack :: Nat' -> TValue -> [Value] -> Integer -> Value
> indexBack w a vs ix =
>   case w of
>     Nat n | n > ix    -> genericIndex vs (n - ix - 1)
>           | otherwise -> logicNullary (Left (InvalidIndex ix)) a
>     Inf               -> evalPanic "indexBack" ["unexpected infinite sequence"]
>
> updatePrim :: (Nat' -> [Value] -> Integer -> Value -> [Value]) -> Value
> updatePrim op =
>   VNumPoly $ \len ->
>   VPoly $ \eltTy ->
>   VNumPoly $ \_idxLen ->
>   VFun $ \xs ->
>   VFun $ \idx ->
>   VFun $ \val ->
>   case fromVWord idx of
>     Left e -> logicNullary (Left e) (tvSeq len eltTy)
>     Right i -> VList (op len (fromVList xs) i val)
>
> updateFront :: Nat' -> [Value] -> Integer -> Value -> [Value]
> updateFront _ vs i x = updateAt vs i x
>
> updateBack :: Nat' -> [Value] -> Integer -> Value -> [Value]
> updateBack Inf _vs _i _x = evalPanic "Unexpected infinite sequence in updateEnd" []
> updateBack (Nat n) vs i x = updateAt vs (n - i - 1) x
>
> updateAt :: [a] -> Integer -> a -> [a]
> updateAt []       _ _ = []
> updateAt (_ : xs) 0 y = y : xs
> updateAt (x : xs) i y = x : updateAt xs (i - 1) y
>
>
> -- Pretty Printing -------------------------------------------------------------
>
> ppValue :: Value -> Doc
> ppValue val =
>   case val of
>     VRecord fs -> braces (sep (punctuate comma (map ppField fs)))
>       where ppField (f,r) = pp f <+> char '=' <+> ppValue r
>     VTuple vs  -> parens (sep (punctuate comma (map ppValue vs)))
>     VBit b     -> text (either show show b)
>     VList vs   -> brackets (fsep (punctuate comma (map ppValue vs)))
>     VFun _     -> text "<function>"
>     VPoly _    -> text "<polymorphic value>"
>     VNumPoly _ -> text "<polymorphic value>"
>
>
> -- Error Handling --------------------------------------------------------------
>
> evalPanic :: String -> [String] -> a
> evalPanic cxt = panic ("[Reference Evaluator]" ++ cxt)
