module Ast where
import Data.Map as Map
import Data.List as List
import Data.Maybe as Maybe

newtype Env k v = Env (Map k v)

lookup :: Ord k => k -> Env k v -> Maybe v
lookup k (Env m) = Map.lookup k m

emp :: Env k v
emp = Env Map.empty

merge :: Ord k => Env k v -> Env k v -> Env k v
merge (Env m1) (Env m2) = Env (Map.union m1 m2)

bind :: Ord k => k -> v -> Env k v -> Env k v
bind k v (Env m) = Env (Map.insert k v m)

distinct :: (Eq a, Ord a) => [a] -> Bool
distinct ls = check (sort ls)
  where check [] = True
        check [x] = True
        check (x:y:zs) = if x == y then False else check (y:zs)

listToEnv :: Ord k => [(k,v)] -> Env k v
listToEnv l = Env (Map.fromList l)

envToList :: Env k v -> [(k,v)]
envToList (Env m) = Map.assocs m

envAll :: (k -> v -> Bool) -> Env k v -> Bool
envAll f (Env m) = List.all (\(x,y) -> f x y) (Map.assocs m)

envElem :: Ord k => k -> Env k v -> Bool
envElem k (Env m) = Map.member k m

data Lit = 
    IntLit Integer
  | Bool Bool
  | Unit

data Opn = Plus | Minus | Times | Divide | Modulo
data Opb = Lt | Gt | Leq | Geq

opn_lookup :: Opn -> Integer -> Integer -> Integer
opn_lookup Plus = (+)
opn_lookup Minus = (-)
opn_lookup Times = ( * )
opn_lookup Divide = (div)
opn_lookup Modulo = (mod)

opb_lookup :: Opb -> Integer -> Integer -> Bool
opb_lookup Lt = (<)
opb_lookup Gt = (>)
opb_lookup Leq = (<=)
opb_lookup Geq = (>=)

data Op = 
    Opn Opn
  | Opb Opb
  | Equality
  | Opapp
  | Opassign

data Uop = Opref | Opderef

data Lop = And | Or

type ModN = String

data Id a = Short a
          | Long ModN a
  deriving (Eq, Ord)

type VarN = String

type ConN = String

type TypeN = String

type TvarN = String

mk_id :: Maybe ModN -> a -> Id a
mk_id Nothing n = Short n
mk_id (Just mn) n = Long mn n

data Tc = 
    TC_name (Id TypeN)
  | TC_int
  | TC_bool
  | TC_unit
  | TC_ref
  | TC_fn
  | TC_tup
  deriving Eq

data T = 
    Tvar TvarN
  | Tvar_db Integer
  | Tapp [T] Tc
  deriving Eq

tint = Tapp [] TC_int
tunit = Tapp [] TC_unit
tbool = Tapp [] TC_bool
tref t = Tapp [t] TC_ref
tfn t1 t2 = Tapp [t1,t2] TC_fn

data Pat = 
    Pvar VarN
  | Plit Lit
  | Pcon (Maybe (Id ConN)) [Pat]
  | Pref Pat

data Error = 
    Bind_error
  | Div_error
  | Eq_error
  | Int_error Integer

data Exp = 
    Raise Error
  | Handle Exp VarN Exp
  | Lit Lit
  | Con (Maybe (Id ConN)) [Exp]
  | Var (Id VarN)
  | Fun VarN Exp
  | Uapp Uop Exp
  | App Op Exp Exp
  | Log Lop Exp Exp
  | If Exp Exp Exp
  | Mat Exp [(Pat,Exp)]
  | Let VarN Exp Exp
  | Letrec [(VarN,VarN,Exp)] Exp

type Type_def = [([TvarN], TypeN, [(ConN, [T])])]

data Dec = 
    Dlet Pat Exp
  | Dletrec [(VarN, VarN, Exp)]
  | Dtype Type_def

type Decs = [Dec]

data Spec = 
    Sval VarN T
  | Stype Type_def
  | Stype_opq [TvarN] TypeN

type Specs = [Spec]

data Top = 
    Tmod ModN (Maybe Specs) Decs
  | Tdec Dec

type Prog = [Top]

pat_bindings :: Pat -> [VarN] -> [VarN]
pat_bindings (Pvar n) already_bound = n:already_bound
pat_bindings (Plit l) already_bound = already_bound
pat_bindings (Pcon _ ps) already_bound = pats_bindings ps already_bound
pat_bindings (Pref p) already_bound = pat_bindings p already_bound
pats_bindings [] already_bound = already_bound
pats_bindings (p:ps) already_bound = pats_bindings ps (pat_bindings p already_bound)

data Ast_pat = 
    Ast_Pvar VarN
  | Ast_Plit Lit
  | Ast_Pcon (Maybe (Id ConN)) [Ast_pat]
  | Ast_Pref Ast_pat

data Ast_exp =
    Ast_Raise Error
  | Ast_Handle Ast_exp VarN Ast_exp
  | Ast_Lit Lit
  | Ast_Var (Id VarN)
  | Ast_Con (Maybe (Id ConN)) [Ast_exp]
  | Ast_Fun VarN Ast_exp
  | Ast_App Ast_exp Ast_exp
  | Ast_Log Lop Ast_exp Ast_exp
  | Ast_If Ast_exp Ast_exp Ast_exp
  | Ast_Mat Ast_exp [(Ast_pat, Ast_exp)]
  | Ast_Let VarN Ast_exp Ast_exp
  | Ast_Letrec [(VarN, VarN, Ast_exp)] Ast_exp

data Ast_t =
    Ast_Tvar TvarN
  | Ast_Tapp [Ast_t] (Maybe (Id TypeN))
  | Ast_Tfn Ast_t Ast_t

type Ast_type_def = [([TvarN], TypeN, [(ConN, [Ast_t])])]

data Ast_dec =
    Ast_Dlet Ast_pat Ast_exp
  | Ast_Dletrec [(VarN, VarN, Ast_exp)]
  | Ast_Dtype Ast_type_def

type Ast_decs = [Ast_dec]

data Ast_spec =
    Ast_Sval VarN Ast_t
  | Ast_Stype Ast_type_def
  | Ast_Stype_opq [TvarN] TypeN

type Ast_specs = [Ast_spec]

data Ast_top =
    Ast_Tmod ModN (Maybe Ast_specs) Ast_decs
  | Ast_Tdec Ast_dec

type Ast_prog = [Ast_top]

type Ctor_env = Env ConN (Id ConN)

elab_p :: Ctor_env -> Ast_pat -> Pat
elab_p ctors (Ast_Pvar n) = Pvar n
elab_p ctors (Ast_Plit l) = Plit l
elab_p ctors (Ast_Pcon (Just (Short cn)) ps) =
  case Ast.lookup cn ctors of
     Just cid -> Pcon (Just cid) (elab_ps ctors ps)
     Nothing -> Pcon (Just (Short cn)) (elab_ps ctors ps)
elab_p ctors (Ast_Pcon cn ps) =
  Pcon cn (elab_ps ctors ps)
elab_p ctors (Ast_Pref p) = Pref (elab_p ctors p)
elab_ps ctors [] = []
elab_ps ctors (p:ps) = elab_p ctors p : elab_ps ctors ps

type Tdef_env = Env TypeN Tc

elab_t :: Tdef_env -> Ast_t -> T
elab_e :: Ctor_env -> Ast_exp -> Exp
elab_funs :: Ctor_env -> [(VarN, VarN, Ast_exp)] -> [(VarN, VarN, Exp)]
elab_dec :: Maybe ModN -> Tdef_env -> Ctor_env -> Ast_dec -> (Tdef_env, Ctor_env, Dec)
elab_decs :: Maybe ModN -> Tdef_env -> Ctor_env -> [Ast_dec] -> (Tdef_env, Ctor_env, [Dec])
elab_spec :: Maybe ModN -> Tdef_env -> [Ast_spec] -> [Spec]
elab_top :: Tdef_env -> Ctor_env -> Ast_top -> (Tdef_env, Ctor_env, Top)
elab_prog :: Tdef_env -> Ctor_env -> [Ast_top] -> (Tdef_env, Ctor_env, Prog)

elab_e ctors (Ast_Raise err) = Raise err
elab_e ctors (Ast_Handle e1 x e2) =
  Handle (elab_e ctors e1) x (elab_e ctors e2)
elab_e ctors (Ast_Lit l) =
  Lit l
elab_e ctors (Ast_Var id) =
  Var id
elab_e ctors (Ast_Con (Just (Short cn)) es) =
  case Ast.lookup cn ctors of
    Just cid -> Con (Just cid) (List.map (elab_e ctors) es)
    Nothing -> Con (Just (Short cn)) (List.map (elab_e ctors) es)
elab_e ctors (Ast_Con cn es) =
  Con cn (List.map (elab_e ctors) es)
elab_e ctors (Ast_Fun n e) =
  Fun n (elab_e ctors e)
elab_e ctors (Ast_App e1 e2) =
  App Opapp (elab_e ctors e1) (elab_e ctors e2)
elab_e ctors (Ast_Log lop e1 e2) =
  Log lop (elab_e ctors e1) (elab_e ctors e2)
elab_e ctors (Ast_If e1 e2 e3) =
  If (elab_e ctors e1) (elab_e ctors e2) (elab_e ctors e3)
elab_e ctors (Ast_Mat e pes) =
  Mat (elab_e ctors e) 
      (List.map (\(p,e) -> 
                   let p' = elab_p ctors p in
                     (p', elab_e ctors e))
                pes)
elab_e ctors (Ast_Let x e1 e2) =
  Let x (elab_e ctors e1) (elab_e ctors e2)
elab_e ctors (Ast_Letrec funs e) =
  Letrec (elab_funs ctors funs) 
         (elab_e ctors e)
elab_funs ctors [] =
  []
elab_funs ctors ((n1,n2,e):funs) =
  (n1,n2,elab_e ctors e) : elab_funs ctors funs

elab_t type_bound (Ast_Tvar n) = Tvar n
elab_t type_bound (Ast_Tfn t1 t2) =
  tfn (elab_t type_bound t1) (elab_t type_bound t2)
elab_t type_bound (Ast_Tapp ts Nothing) =
  let ts' = List.map (elab_t type_bound) ts in
    Tapp ts' TC_tup
elab_t type_bound (Ast_Tapp ts (Just (Long m tn))) =
  let ts' = List.map (elab_t type_bound) ts in
    Tapp ts' (TC_name (Long m tn))
elab_t type_bound (Ast_Tapp ts (Just (Short tn))) =
  let ts' = List.map (elab_t type_bound) ts in
    case Ast.lookup tn type_bound of
      Nothing -> Tapp ts' (TC_name (Short tn))
      Just tc -> Tapp ts' tc

get_ctors_bindings mn t =
  List.concat (List.map (\(tvs,tn,ctors) -> List.map (\(cn,t) -> (cn, mk_id mn cn)) ctors) t)
   
elab_td type_bound (tvs,tn,ctors) =
  (tvs, tn, List.map (\(cn,t) -> (cn, List.map (elab_t type_bound) t)) ctors)

elab_dec mn type_bound ctors (Ast_Dlet p e) =
  let p' = elab_p ctors p in
    (emp, emp, Dlet p' (elab_e ctors e))
elab_dec mn type_bound ctors (Ast_Dletrec funs) =
  (emp, emp, Dletrec (elab_funs ctors funs))
elab_dec mn type_bound ctors (Ast_Dtype t) = 
  let type_bound' = listToEnv (List.map (\(tvs,tn,ctors) -> (tn, TC_name (mk_id mn tn))) t) in
    (type_bound',
     merge (listToEnv (get_ctors_bindings mn t)) ctors,
     Dtype (List.map (elab_td (merge type_bound' type_bound)) t))

elab_decs mn type_bound ctors [] = (emp,emp,[])
elab_decs mn type_bound ctors (d:ds) = 
  let (type_bound', ctors', d') = elab_dec mn type_bound ctors d in
  let (type_bound'',ctors'',ds') = elab_decs mn (merge type_bound' type_bound) (merge ctors' ctors) ds in
    (merge type_bound'' type_bound', merge ctors'' ctors', d':ds')

elab_spec mn type_bound [] = []
elab_spec mn type_bound (Ast_Sval x t:spec) =
  Sval x (elab_t type_bound t) : elab_spec mn type_bound spec
elab_spec mn type_bound (Ast_Stype td : spec) =
  let type_bound' = listToEnv (List.map (\(tvs,tn,ctors) -> (tn, TC_name (mk_id mn tn))) td) in
    Stype (List.map (elab_td (merge type_bound' type_bound)) td) : elab_spec mn (merge type_bound' type_bound) spec
elab_spec mn type_bound (Ast_Stype_opq tvs tn:spec) =
  Stype_opq tvs tn : elab_spec mn (bind tn (TC_name (mk_id mn tn)) type_bound) spec

elab_top type_bound ctors (Ast_Tdec d) =
  let (type_bound', ctors', d') = elab_dec Nothing type_bound ctors d in
      (type_bound', ctors', Tdec d')
elab_top type_bound ctors (Ast_Tmod mn spec ds) =
  let (type_bound',ctors',ds') = elab_decs (Just mn) type_bound ctors ds in
      (type_bound,ctors,Tmod mn (fmap (elab_spec (Just mn) type_bound) spec) ds')

elab_prog type_bound ctors [] = (emp,emp,[])
elab_prog type_bound ctors (top:prog) =
  let (type_bound',ctors',top') = elab_top type_bound ctors top in
  let (type_bound'',ctors'',prog') = elab_prog (merge type_bound' type_bound) (merge ctors' ctors) prog in
    (merge type_bound'' type_bound', merge ctors'' ctors', top':prog') 

check_dup_ctors :: Maybe ModN -> Env (Id ConN) a -> [([TvarN], TypeN, [(ConN, [T])])] -> Bool
check_dup_ctors mn_opt cenv tds =
  List.all (\(tvs,tn,condefs) ->
               List.all (\(n,ts) -> Maybe.isNothing (Ast.lookup (mk_id mn_opt n) cenv)) condefs)
           tds &&
  distinct (let x2 = ([]) in List.foldr (\(tvs, tn, condefs) x2 -> List.foldr (\(n, ts) x2 ->  if True then n : x2 else x2) x2 condefs) x2 tds)
