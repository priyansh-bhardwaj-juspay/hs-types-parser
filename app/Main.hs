module Main where

import Data.Maybe (catMaybes, fromMaybe, mapMaybe)
import Language.Haskell.Exts as LHE
import System.Directory (doesDirectoryExist, doesFileExist, listDirectory)
import Data.List (foldl', find, isSuffixOf)
import Text.Pretty.Simple
import Types
import Data.Generics.Labels ()
import Control.Lens hiding (List)
import qualified Data.HashMap.Strict as HM
import Data.HashMap.Strict ((!), (!?))
import GHC.Utils.Misc (split)
import Data.Aeson.Encode.Pretty (encodePretty)
import Data.ByteString.Lazy.Char8 (unpack)

allFiles :: FilePath -> IO [FilePath]
allFiles basePath = allFilesHelper basePath =<< listDirectory basePath
  where
  allFilesHelper _ [] = return []
  allFilesHelper basePath' (fp : fps) = do
    fileExists <- doesFileExist $ basePath' <> fp
    dirExists <- doesDirectoryExist $ basePath' <> fp
    if fileExists
      then (basePath' <> fp :) <$> allFilesHelper basePath' fps
      else
        if dirExists
          then do
            l1 <- allFilesHelper (basePath' <> fp <> "/") =<< listDirectory (basePath' <> fp)
            l2 <- allFilesHelper basePath' fps
            return $ l1 <> l2
          else allFilesHelper basePath' fps

getImportsFromHead :: NonGreedy (ModuleHeadAndImports SrcSpanInfo) -> [String]
getImportsFromHead (NonGreedy (ModuleHeadAndImports _ _ _ mimports)) =
  map (helper . importModule) mimports
 where
  helper (ModuleName _ iname) = iname

getModuleNameFromHead :: NonGreedy (ModuleHeadAndImports SrcSpanInfo) -> Maybe String
getModuleNameFromHead (NonGreedy (ModuleHeadAndImports _ _ (Just (ModuleHead _ (ModuleName _ name') _ _)) _)) = pure name'
getModuleNameFromHead (NonGreedy (ModuleHeadAndImports _ _ Nothing _)) = Nothing

fileModules :: FilePath -> IO (Module SrcSpanInfo)
fileModules fname = do
  fcontents <- readFile fname
  -- case parse $ sanitize fcontents of
  let parsedFile =
        parseWithMode
          ( defaultParseMode
              { parseFilename = fname
              , ignoreLinePragmas = False
              , extensions =
                  [ EnableExtension PackageImports
                  , EnableExtension ExplicitNamespaces
                  ]
              , ignoreLanguagePragmas = False
              }
          )
          fcontents
  case parsedFile of
    (ParseOk moduleInfo) -> return moduleInfo
    (ParseFailed (SrcLoc _ line col) err) ->
      error $
        "Failed to parse module in "
          ++ fname
          ++ ":\n"
          ++ "  ("
          ++ show line
          ++ ":"
          ++ show col
          ++ ") "
          ++ err
          ++ "\n"
          ++ "  "
          ++ getLineCol fcontents (line, col)
  where
  getLineCol fcontents (line, col) =
    ln
      ++ "\n"
      ++ "  "
      ++ replicate (col' - 3) ' '
      ++ "^^^"
    where
    ln = lines fcontents !! line
    col' =
      let l = length ln
      in min col l

parseModuleT :: Module SrcSpanInfo -> IO ModuleT
parseModuleT (Module _ (Just (ModuleHead _ (ModuleName _ name') _ _)) _ importDecls decls) = do
  let imports' = foldr mkImport [] importDecls
      types' = foldr mkTypeR [] decls
  return $ ModuleT
    { name = name'
    , imports = imports'
    , types = types'
    }
parseModuleT _other = error $ "Unknown module type " <> show _other

moduleName :: ModuleName SrcSpanInfo -> String
moduleName (ModuleName _ name') = name'

getName :: Name SrcSpanInfo -> String
getName (Ident _ name') = name'
getName (Symbol _ name') = name'

getConstructor :: CName SrcSpanInfo -> Maybe String
getConstructor (ConName _ name') = Just $ getName name'
getConstructor _ = Nothing

mkImportSpec :: ImportSpec SrcSpanInfo -> Maybe ImportItem
mkImportSpec (IVar _ _) = Nothing
mkImportSpec (IAbs _ _ name') = Just $
  ImportItem
    { name = getName name'
    , includes = None
    }
mkImportSpec (IThingAll _ name') = Just $
  ImportItem
    { name = getName name'
    , includes = All
    }
mkImportSpec (IThingWith _ name' list) = Just $
  ImportItem
    { name = getName name'
    , includes = Some (mapMaybe getConstructor list)
    }

mkImport :: ImportDecl SrcSpanInfo -> [Import] -> [Import]
mkImport (ImportDecl _ (ModuleName _ name') qualified' _ _ _ importAs' mImportSpecList) res =
  let specsList' = maybe (Hide [])
        (\ (ImportSpecList _ hiding list) -> let list' = mapMaybe mkImportSpec list in if hiding then Hide list' else Include list')
        mImportSpecList
      _import = Import
        { _module = name'
        , qualified = qualified'
        , alias = moduleName <$> importAs'
        , specsList = specsList'
        }
  in _import : res

mkTypeR :: Decl SrcSpanInfo -> [TypeInfo] -> [TypeInfo]
mkTypeR decl res = maybe res (:res) $ mkType decl

mkType :: Decl SrcSpanInfo -> Maybe TypeInfo
mkType decl@(DataDecl (SrcSpanInfo (SrcSpan _ x1 y1 x2 y2) _) _ _ declHead consDecl _) =
  let constructors' = map constructorName consDecl
      name' = searchNameDecl declHead
      typeInfo = TypeInfo
        { pos = ((x1, y1), (x2, y2))
        , name = name'
        , stringified = prettyPrint decl
        , constructors = constructors'
        }
  in Just typeInfo
mkType decl@(TypeDecl (SrcSpanInfo (SrcSpan _ x1 y1 x2 y2) _) declHead _) =
  let name' = searchNameDecl declHead
      typeInfo = TypeInfo
        { pos = ((x1, y1), (x2, y2))
        , name = name'
        , stringified = prettyPrint decl
        , constructors = []
        }
  in Just typeInfo
mkType _ = Nothing

constructorName :: QualConDecl SrcSpanInfo -> String
constructorName (QualConDecl _ _ _ (ConDecl _ name' _)) = getName name'
constructorName (QualConDecl _ _ _ (RecDecl _ name' _)) = getName name'
constructorName _other = error $ "Unknown mkConstructor : " <> show _other

searchNameDecl :: DeclHead SrcSpanInfo -> String
searchNameDecl (DHead _ name') = getName name'
searchNameDecl (DHApp _ declHead _) = searchNameDecl declHead
searchNameDecl _other = error $ "Unknown parseDataDecl : " <> show _other

tyVarBind :: TyVarBind SrcSpanInfo -> String
tyVarBind (UnkindedVar _ name') = getName name'
tyVarBind _other = error $ "Unknown tyVarBind : " <> show _other

clearImports :: [String] -> ModuleT -> ModuleT
clearImports moduleNames module' =
  module'
    { imports = filter (\ importT -> importT ^. #_module `elem` moduleNames) (module' ^. #imports)
    }

findDependencyM :: Map String ModuleT -> Map Entity [EntityDef] -> Module SrcSpanInfo -> Map Entity [EntityDef]
findDependencyM modulesMap depMap (Module _ (Just (ModuleHead _ (ModuleName _ modName) _ _)) _ _ decl) =
  foldl' (findDependencyD modulesMap modName) depMap decl
findDependencyM _ _ _other = error $ "Unknown findDependencyM : " <> show _other

findDependencyD :: Map String ModuleT -> String -> Map Entity [EntityDef] -> Decl SrcSpanInfo -> Map Entity [EntityDef]
findDependencyD modulesMap modName depMap (TypeDecl _ declHead def) =
  let name' = searchNameDecl declHead
      module' = modulesMap ! modName
      imports' = module' ^. #imports
      entity = Type $ EntityDef modName name'
      deps = collectTypes (modulesMap, imports', modName) def []
  in if null deps then depMap else HM.insert entity deps depMap
findDependencyD modulesMap modName depMap (DataDecl _ _ _ declHead consList _) =
  let name' = searchNameDecl declHead
      module' = modulesMap ! modName
      imports' = module' ^. #imports
      entity = Type $ EntityDef modName name'
      deps = foldr (scanConstructor (modulesMap, imports', modName)) [] consList
  in if null deps then depMap else HM.insert entity deps depMap
findDependencyD modulesMap modName depMap (TypeSig _ nameL t1) =
  let name' = getName $ head nameL
      module' = modulesMap ! modName
      imports' = module' ^. #imports
      entity = Function $ EntityDef modName name'
      deps' = fromMaybe [] $ depMap !? entity
      deps = collectTypes (modulesMap, imports', modName) t1 deps'
  in if null deps then depMap else HM.insert entity deps depMap
findDependencyD modulesMap modName depMap (FunBind _ matches) =
  let module' = modulesMap ! modName
      imports' = module' ^. #imports
      depMap' = foldr (scanMatches (modulesMap, imports', modName)) depMap matches
  in depMap'
findDependencyD _ _ depMap _other = depMap
-- findDependencyD _ _ _ _other = error $ "Unknown findDependencyD : " <> show _other

scanMatches :: Payload -> Match SrcSpanInfo -> Map Entity [EntityDef] -> Map Entity [EntityDef]
scanMatches payload@(_, _, modName) (Match _ nameT _ rhs mBinds) depMap =
  let name' = getName nameT
      entity = Function $ EntityDef modName name'
      deps' = fromMaybe [] $ depMap !? entity
      deps = maybe id (scanBinds payload) mBinds $ evalRhs payload rhs deps'
  in if null deps then depMap else HM.insert entity deps depMap
scanMatches payload@(_, _, modName) (InfixMatch _ _ nameT _ rhs mBinds) depMap =
  let name' = getName nameT
      entity = Function $ EntityDef modName name'
      deps' = fromMaybe [] $ depMap !? entity
      deps = maybe id (scanBinds payload) mBinds $ evalRhs payload rhs deps'
  in if null deps then depMap else HM.insert entity deps depMap

evalRhs :: Payload -> Rhs SrcSpanInfo -> [EntityDef] -> [EntityDef]
evalRhs payload (UnGuardedRhs _ exp') res = collectCons payload exp' res
evalRhs payload (GuardedRhss _ list) res = foldr (collectCons payload . (\ (GuardedRhs _ _ exp') -> exp')) res list

collectCons :: Payload -> Exp SrcSpanInfo -> [EntityDef] -> [EntityDef]
collectCons payload (Con _ qName) res = maybe res (<:res) $ findEntityDefForCons payload qName
collectCons payload (InfixApp _ e1 _ e2) res = collectCons payload e1 $ collectCons payload e2 res
collectCons payload (App _ e1 e2) res = collectCons payload e1 $ collectCons payload e2 res
collectCons payload (NegApp _ e1) res = collectCons payload e1 res
collectCons payload (Lambda _ _ e1) res = collectCons payload e1 res
collectCons payload (Let _ _ e1) res = collectCons payload e1 res
collectCons payload (If _ e1 e2 e3) res = collectCons payload e1 $ collectCons payload e2 $ collectCons payload e3 res
collectCons payload (MultiIf _ rhsL) res = foldr (collectCons payload . (\ (GuardedRhs _ _ exp') -> exp')) res rhsL
collectCons payload (Case _ e1 altL) res = foldr (scanAlt payload) (collectCons payload e1 res) altL
collectCons payload (Do _ stmts) res = foldr (scanStmt payload) res stmts
collectCons payload (MDo _ stmts) res = foldr (scanStmt payload) res stmts
collectCons payload (Tuple _ _ expL) res = foldr (collectCons payload) res expL
collectCons payload (UnboxedSum _ _ _ e1) res = collectCons payload e1 res
collectCons payload (TupleSection _ _ expL) res = foldr (collectCons payload) res . catMaybes $ expL
collectCons payload (List _ expL) res = foldr (collectCons payload) res expL
collectCons payload (ParArray _ expL) res = foldr (collectCons payload) res expL
collectCons payload (Paren _ e1) res = collectCons payload e1 res
collectCons payload (LeftSection _ e1 _) res = collectCons payload e1 res
collectCons payload (RightSection _ _ e1) res = collectCons payload e1 res
collectCons payload (RecConstr _ qName updatesL) res = foldr (scanFieldUpdate payload) (maybe res (<:res) $ findEntityDefForCons payload qName) updatesL
collectCons payload (RecUpdate _ e1 updatesL) res = foldr (scanFieldUpdate payload) (collectCons payload e1 res) updatesL
collectCons payload (EnumFrom _ e1) res = collectCons payload e1 res
collectCons payload (EnumFromTo _ e1 e2) res = collectCons payload e1 $ collectCons payload e2 res
collectCons payload (EnumFromThen _ e1 e2) res = collectCons payload e1 $ collectCons payload e2 res
collectCons payload (EnumFromThenTo _ e1 e2 e3) res = collectCons payload e1 $ collectCons payload e2 $ collectCons payload e3 res
collectCons payload (ParArrayFromTo _ e1 e2) res = collectCons payload e1 $ collectCons payload e2 res
collectCons payload (ParArrayFromThenTo _ e1 e2 e3) res = collectCons payload e1 $ collectCons payload e2 $ collectCons payload e3 res
collectCons payload (ListComp _ e1 qStmtList) res = collectCons payload e1 $ foldr (scanQualStmt payload) res qStmtList
collectCons payload (ParComp _ e1 qStmtList) res = collectCons payload e1 $ foldr (scanQualStmt payload) res $ concat qStmtList
collectCons payload (ParArrayComp _ e1 qStmtList) res = collectCons payload e1 $ foldr (scanQualStmt payload) res $ concat qStmtList
collectCons payload (ExpTypeSig _ e1 t1) res = collectCons payload e1 $ collectTypes payload t1 res
collectCons payload (TypeApp _ t1) res = collectTypes payload t1 res
collectCons payload (Proc _ _ e1) res = collectCons payload e1 res
collectCons payload (LeftArrApp _ e1 e2) res = collectCons payload e1 $ collectCons payload e2 res
collectCons payload (RightArrApp _ e1 e2) res = collectCons payload e1 $ collectCons payload e2 res
collectCons payload (LeftArrHighApp _ e1 e2) res = collectCons payload e1 $ collectCons payload e2 res
collectCons payload (RightArrHighApp _ e1 e2) res = collectCons payload e1 $ collectCons payload e2 res
collectCons payload (ArrOp _ e1) res = collectCons payload e1 res
collectCons payload (LCase _ alt') res = foldr (scanAlt payload) res alt'
collectCons _ _ res = res

scanAlt :: Payload -> Alt SrcSpanInfo -> [EntityDef] -> [EntityDef]
scanAlt payload (Alt _ _ rhs binds') = maybe id (scanBinds payload) binds' . evalRhs payload rhs

scanQualStmt :: Payload -> QualStmt SrcSpanInfo -> [EntityDef] -> [EntityDef]
scanQualStmt payload (QualStmt _ stmt) res = scanStmt payload stmt res
scanQualStmt payload (ThenTrans _ e1) res = collectCons payload e1 res
scanQualStmt payload (ThenBy _ e1 e2) res = collectCons payload e1 $ collectCons payload e2 res
scanQualStmt payload (GroupBy _ e1) res = collectCons payload e1 res
scanQualStmt payload (GroupUsing _ e1) res = collectCons payload e1 res
scanQualStmt payload (GroupByUsing _ e1 e2) res = collectCons payload e1 $ collectCons payload e2 res

scanFieldUpdate :: Payload -> FieldUpdate SrcSpanInfo -> [EntityDef] -> [EntityDef]
scanFieldUpdate payload (FieldUpdate _ _ e1) res = collectCons payload e1 res
scanFieldUpdate _ (FieldPun _ _) res = res
scanFieldUpdate _ (FieldWildcard _) res = res

scanStmt :: Payload -> Stmt SrcSpanInfo -> [EntityDef] -> [EntityDef]
scanStmt payload (Generator _ _ e1) res = collectCons payload e1 res
scanStmt payload (Qualifier _ e1) res = collectCons payload e1 res
scanStmt payload (LetStmt _ binds') res = scanBinds payload binds' res
scanStmt payload (RecStmt _ stmts) res = foldr (scanStmt payload) res stmts

scanBinds :: Payload -> Binds SrcSpanInfo -> [EntityDef] -> [EntityDef]
scanBinds _ (BDecls _ _) res = res
scanBinds payload (IPBinds _ binds') res = foldr (collectCons payload . (\ (IPBind _ _ exp') -> exp')) res binds'

scanConstructor :: Payload -> QualConDecl SrcSpanInfo -> [EntityDef] -> [EntityDef]
scanConstructor payload (QualConDecl _ _ _ (ConDecl _ _ tList)) res = foldr (collectTypes payload) res tList
scanConstructor payload (QualConDecl _ _ _ (InfixConDecl _ t1 _ t2)) res = collectTypes payload t1 $ collectTypes payload t2 res
scanConstructor payload (QualConDecl _ _ _ (RecDecl _ _ fList)) res = foldr (collectTypes payload . (\ (FieldDecl _ _ t) -> t)) res fList

collectTypes :: Payload -> Type SrcSpanInfo -> [EntityDef] -> [EntityDef]
collectTypes payload (TyForall _ _ _ t1) res = collectTypes payload t1 res
collectTypes _ (TyStar _) res = res
collectTypes payload (TyFun _ t1 t2) res = collectTypes payload t1 $ collectTypes payload t2 res
collectTypes payload (TyTuple _ _ list) res = foldr (collectTypes payload) res list
collectTypes payload (TyUnboxedSum _ list) res = foldr (collectTypes payload) res list
collectTypes payload (TyList _ t1) res = collectTypes payload t1 res
collectTypes payload (TyParArray _ t1) res = collectTypes payload t1 res
collectTypes payload (TyApp _ t1 t2) res = collectTypes payload t1 $ collectTypes payload t2 res
collectTypes _ (TyVar _ _) res = res
collectTypes payload (TyCon _ qName) res = maybe res (<:res) $ findEntityDefForType payload qName
collectTypes payload (TyParen _ t1) res = collectTypes payload t1 res
collectTypes payload (TyInfix _ t1 (PromotedName _ qName) t2) res = collectTypes payload t1 $ (\ res' -> maybe res' (<:res') (findEntityDefForType payload qName)) $ collectTypes payload t2 res
collectTypes payload (TyInfix _ t1 (UnpromotedName _ qName) t2) res = collectTypes payload t1 $ (\ res' -> maybe res' (<:res') (findEntityDefForType payload qName)) $ collectTypes payload t2 res
collectTypes payload (TyKind _ t1 _) res = collectTypes payload t1 res
collectTypes _ (TyPromoted _ _) res = res
collectTypes payload (TyEquals _ t1 t2) res = collectTypes payload t1 $ collectTypes payload t2 res
collectTypes _ (TySplice _ _) res = res
collectTypes payload (TyBang _ _ _ t1) res = collectTypes payload t1 res
collectTypes _ (TyWildCard _ _) res = res
collectTypes _ (TyQuasiQuote {}) res = res

(<:) :: EntityDef -> [EntityDef] -> [EntityDef]
x <: xr | x `elem` xr = xr
        | otherwise = x : xr

findEntityDefForType :: Payload -> QName SrcSpanInfo -> Maybe EntityDef
findEntityDefForType (modulesMap, imports', _) (Qual _ (ModuleName _ alias') tNameT) =
  let tName = getName tNameT
      moduleM = find (checkForType tName) . map ((modulesMap !) . (^. #_module)) . filter (checkImportForType (Just alias') tName) $ imports'
  in (\ ModuleT {name = name'} -> EntityDef name' tName) <$> moduleM
findEntityDefForType (modulesMap, imports', modName) (UnQual _ tNameT) =
  let tName = getName tNameT
      moduleM = find (checkForType tName) . ((modulesMap ! modName):) . map ((modulesMap !) . (^. #_module)) . filter (checkImportForType Nothing tName) $ imports'
  in (\ ModuleT {name = name'} -> EntityDef name' tName) <$> moduleM
findEntityDefForType _ (Special _ _) = Nothing

checkImportForType :: Maybe String -> String -> Import -> Bool
checkImportForType mAlias typeN Import {..} = maybe (not qualified) ((alias ==) . Just) mAlias && matchSpecsForType specsList typeN

matchSpecsForType :: SpecsList -> String -> Bool
matchSpecsForType (Include list) typeN = any ((typeN ==) . (^. #name)) list
matchSpecsForType (Hide list) typeN = all ((typeN /=) . (^. #name)) list

checkForType :: String -> ModuleT -> Bool
checkForType typeN moduleT = any ((typeN ==) . (^. #name)) (moduleT ^. #types)

findEntityDefForCons :: Payload -> QName SrcSpanInfo -> Maybe EntityDef
findEntityDefForCons payload@(modulesMap, imports', _) (Qual _ (ModuleName _ alias') cNameT) =
  let cName = getName cNameT
      moduleM = find (\ moduleT -> any (elem cName . (^. #constructors)) (moduleT ^. #types)) . map ((modulesMap !) . (^. #_module)) . filter (checkImportForCons payload (Just alias') cName) $ imports'
  in moduleM >>= \ moduleT ->
     find (elem cName . (^. #constructors)) (moduleT ^. #types) >>=
     Just . EntityDef (moduleT ^. #name) . (^. #name)
findEntityDefForCons payload@(modulesMap, imports', modName) (UnQual _ cNameT) =
  let cName = getName cNameT
      moduleM = find (\ moduleT -> any (elem cName . (^. #constructors)) (moduleT ^. #types)) . ((modulesMap ! modName):) . map ((modulesMap !) . (^. #_module)) . filter (checkImportForCons payload Nothing cName) $ imports'
  in moduleM >>= \ moduleT ->
     find (elem cName . (^. #constructors)) (moduleT ^. #types) >>=
     Just . EntityDef (moduleT ^. #name) . (^. #name)
findEntityDefForCons _ (Special _ _) = Nothing

checkImportForCons :: Payload -> Maybe String -> String -> Import -> Bool
checkImportForCons (modulesMap, _, _) mAlias typeN Import {..} = maybe (not qualified) ((alias ==) . Just) mAlias && matchSpecsForCons (modulesMap ! _module) specsList typeN

matchSpecsForCons :: ModuleT -> SpecsList -> String -> Bool
matchSpecsForCons moduleT (Include list) consN = any (consIncluded moduleT consN) list
matchSpecsForCons moduleT (Hide list) consN = not $ any (consIncluded moduleT consN) list

consIncluded :: ModuleT -> String -> ImportItem -> Bool
consIncluded moduleT consN (ImportItem name' All) =
  let typeT = find ((name' ==) . (^. #name)) (moduleT ^. #types)
  in maybe False (\ tp -> consN `elem` tp ^. #constructors) typeT
consIncluded _ consN (ImportItem _ (Some list)) = consN `elem` list
consIncluded _ _ (ImportItem _ None) = False

checkForCons :: String -> ModuleT -> Bool
checkForCons consN moduleT = any (elem consN . (^. #constructors)) (moduleT ^. #types)

mkTypesDump :: [ModuleT] -> Map String (Map String TypeDump)
mkTypesDump = foldl' (\ hm mod' -> HM.insert (mod' ^. #name) (foldl' (\ hm' typeT -> HM.insert (typeT ^. #name) (mkTypeDump (mod' ^. #name) typeT) hm') HM.empty (mod' ^. #types)) hm) HM.empty

mkTypeDump :: String -> TypeInfo -> TypeDump
mkTypeDump modName typeT =
  let src = foldl' (\ path step -> path <> "/" <> step) "src" (split '.' modName)
      ((x1, y1), (_, _)) = typeT ^. #pos
      srcLoc = src <> ":" <> show x1 <> ":" <> show y1
  in TypeDump
    { name = typeT ^. #name
    , srcLoc = srcLoc
    , _module = modName
    , stringified = typeT ^. #stringified
    }

mkDepsDump :: Map Entity [EntityDef] -> Map String (Map String [EntityDef])
mkDepsDump = foldr (\ (entity, dep) hm -> HM.alter (\ mMod -> Just $ HM.insert (entity ^. name_) dep $ fromMaybe HM.empty mMod) (entity ^. module_) hm) HM.empty . HM.toList

main :: IO ()
main = do
  files <- filter (isSuffixOf ".hs") <$> allFiles "/Users/priyanshbhardwaj/Documents/rust-migration/basic_haskell/"
  moduleInfo <- mapM fileModules files
  modules' <- mapM parseModuleT moduleInfo
  let moduleNames :: [String] = map (^. #name) modules'
      modules = map (clearImports moduleNames) modules'
      modulesMap = foldl' (\ hm mod' -> HM.insert (mod' ^. #name) mod' hm) HM.empty modules
      dependencies = foldl' (findDependencyM modulesMap) HM.empty moduleInfo
      typesDump = mkTypesDump modules
      depsDump = mkDepsDump dependencies
  writeFile "types.json" $ unpack $ encodePretty typesDump
  writeFile "dependencies.json" $ unpack $ encodePretty depsDump
