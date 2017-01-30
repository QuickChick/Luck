{ 
module Outer.Parser where
  
import Outer.Lexer
import Common.Error
import Common.SrcLoc
import Outer.ParseMonad
import Outer.AST 
import Common.Types

import Control.Monad.Error

import Debug.Trace

}

%name parser program
%tokentype { (Located Token) }
%error { happyError }
%monad { P } { >>= } { return }
%lexer { lexer } { L _ TEof }

%name typeParser type

%nonassoc 'in'
%nonassoc 'else'
%right ':'
%left '!'
%nonassoc '{'
%nonassoc '}'
%left '||'
%left '&&'
%nonassoc '==' '/=' '>' '<' '<=' '>='
%left '+' '-'
%left '*' '/'
%left 'not' SIGN
%nonassoc PAT
%nonassoc PATS CONID

%token
    '='         { L _ TAssign }
    INT         { L _ (TInt _) }
    VARID       { L _ (TVar _) }
    CONID       { L _ (TCon _) }
    STRING      { L _ (TStr _) }
    '()'        { L _ TUnit }
    '('         { L _ TLParen }
    ')'         { L _ TRParen }
    '['         { L _ TLBracket }
    ']'         { L _ TRBracket }
    '{'         { L _ TLCurBracket }
    '}'         { L _ TRCurBracket }
    '!'         { L _ TBang }
    'case'      { L _ TCase }
    'of'        { L _ TOf }
    'end'       { L _ TEnd }
    'let'       { L _ TLet }
    'let\''     { L _ TLetPrime }
    'in'        { L _ TIn }
    'if'        { L _ TIf }
    'then'      { L _ TThen }
    'else'      { L _ TElse }
    'data'      { L _ TData }
    'sig'       { L _ TSig }
    'fun'       { L _ TFun }
    'trace'     { L _ TTRACE }
    'fix'       { L _ TFix }
    'fresh'     { L _ TFresh }
    'collect'   { L _ TCollect }
    'include'   { L _ TInclude }
    'class'     { L _ TClass }
    'instance'  { L _ TInstance }
    'where'     { L _ TWhere }
    'record'    { L _ TRecord }
    
    '_'         { L _ TUnd }
    '::'        { L _ TCons }
    ':'         { L _ TColon }
    ','         { L _ TComma }    
    'not'       { L _ TNot }
    '+'         { L _ TPlus }
    '-'         { L _ TMinus }
    '*'         { L _ TTimes }
    '/'         { L _ TDiv }
    '%'         { L _ TPercent }
    '&&'        { L _ TLAnd }
    '||'        { L _ TLOr }
    '=='        { L _ TEq }
    '/='        { L _ TNe }
    '<'         { L _ TLt }
    '>'         { L _ TGt }
    '<='        { L _ TLe }
    '>='        { L _ TGe }
    '->'        { L _ TArrow }
    '|'         { L _ TBar }
    '=>'        { L _ TFatArrow }
    ';'         { L _ TSemiColon }
    '.'         { L _ TColon }

%% --Like yacc, we include %% here, for no real reason.

program :: { Prg } 
    : decls                {% checkRevDecls $1 }

-- | Declarations. To avoid conflicts we include keywords in the beginning (TODO: fix)
decls :: { [Decl] }           
    : {- empty -}            { [] } 
    | 'data' dataDecl decls  { $2 : $3 }
    | 'fun' funDecl   decls  { $2 : $3 }
    | 'sig' sigDecl   decls  { $2 : $3 }
    | 'include' STRING decls  { (IncludeDecl (unSTRING $2)) : $3 }
    | 'class' classDecl decls { $2 : $3 }
    | 'instance' instanceDecl decls { $2 : $3 }
    | 'record' recordDecl decls { $2 ++ $3 }

instanceDecl :: { Decl }
    : className 'where' funDecls { InstanceDecl (getLoc $2) (fst $1) (snd $1) [] (fromFunDecls $3) }
    | classCtrs '=>' className 'where' funDecls { InstanceDecl (getLoc $2) (fst $3) (snd $3) $1 (fromFunDecls $5) }

classCtrs :: { [(ClassId, OTcType)] }
    : className { [$1] }
    | '(' classCtrsComma ')' { $2 }

classCtrsComma :: { [(ClassId, OTcType)] }
    : className { [$1] }
    | className ',' classCtrsComma  { $1 : $3 }

className :: { (ClassId, OTcType) }
    : CONID btype { (unCONID $1, $2) }

classDecl :: { Decl }
    : className 'where' sigDecls { ClassDecl (getLoc $2) (fst $1) (unType (snd $1)) (fromSigDecls $3) }

sigDecls :: { [Decl] }
    : sigDecl { [$1] }
    | sigDecl ';' sigDecls { $1 : $3 }

sigDecl :: { Decl }          
    : VARID '::' type        { TypeSig (getLoc $1) (unVARID $1) [] $3 }
    | VARID '::' '{' classCtrsComma '}' '=>' type { TypeSig (getLoc $1) (unVARID $1) $4 $7 }

recordDecl :: { [Decl] }
    : type '=' '{' accessors '}' {% do { (c,ts) <- checkDataHeader $1
                                       ; l <- getSrcLoc 
                                       ; return $ recordDeclaration l c ts $4 } }

accessors :: { [(VarId, OTcType)] }
    : VARID '::' type { [(unVARID $1, $3)] }
    | VARID '::' type ';' accessors { (unVARID $1,$3) : $5 }

-- | Single datatype declaration. Need to reverse conDecls
dataDecl :: { Decl } 
    : type '=' constrs  {% do { (c,ts) <- checkDataHeader $1
                              ; l <- getSrcLoc 
                              ; return $ DataDecl l c ts (reverse $3) } }

-- | Constructor declarations. Returned in reverse order!
constrs :: { [ConDecl] } 
    : constr                  { [$1] } 
    | constrs '|' constr      { $3 : $1 } 

-- | Single constructor declaration
constr :: { ConDecl } 
    : btype                   {% mkConDecl $1 }

btype :: { OTcType } 
    : btype1                  { fixConType (reverse $1) }

btype1 :: { [OTcType] } 
    : btype1 atype            { $2 : $1 }
    | atype                   { [$1] } 

atype :: { OTcType } 
    : gtycon                  { TcCon $1 0 [] } 
    | VARID                   { TcVar (unVARID $1) } 
    | '(' types ')'           { let n = length $2 in 
                                TcCon (tuple_tycon_name n) n (reverse $2) }
    | '[' type ']'            { TcCon list_tycon_name 1 [$2] }
    | '(' type ')'            { $2 } 

gtycon :: { TyConId } 
    : CONID                   { unCONID $1 } 

types :: { [OTcType] } 
    : types ',' type          { $3 : $1 }
    | type  ',' type          { [$3, $1] }

type :: { OTcType } 
    : btype '->' type         { TcFun $1 $3 }
    | btype                   { $1 }

funDecls :: { [Decl] }
    : funDecl { [$1] }
    | funDecl ';' funDecls { $1 : $3 }

funDecl :: { Decl } 
    : VARID vars '=' exp      {% do { l <- getSrcLoc
                                    ; checkValDef l (unVARID $1) $2 $4 } }

vars :: { [(VarId, Maybe Int)] } 
    : VARID                     { [(unVARID $1,Nothing)] }
    | '{' VARID '::' INT '}'    { [(unVARID $2, Just $ unINT $4)] }
    | VARID vars                { (unVARID $1, Nothing) : $2 } 
    | '{' VARID '::' INT '}' vars   
                                { (unVARID $2, Just $ unINT $4) : $6 } 

sexp :: { Exp } 
    : INT                     { Lit . LitInt $ unINT $1 }
    | CONID                   { Con $ unCONID $1 } 
    | VARID                   { (Var (unVARID $1, Nothing)) }
    | '()'                    { Con "()" }
    | '(' exp ')'             { $2 }
    | '(' ccexps ')'          { appify (Con $ tuple_con_name $ length $2) $2 }
    | '[' exps ']'            { listify $2 }
    | '(' 'fun' vars '->' exp ')' { Fun $3 $5 }

exp :: { Exp } 
    : sexp                    { $1 } 
    | sexp sexps              { appify $1 $2 }
    | '+' exp %prec SIGN      { $2 }
    | '-' exp %prec SIGN      { Unop OpNeg $2 }
    | 'not' exp               { Unop OpNot $2 }
    | exp '+' exp             { Binop $1 OpPlus $3 }
    | exp '-' exp             { Binop $1 OpMinus $3 }
    | exp '*' exp             { Binop $1 OpTimes $3 }
    | exp '/' exp             { Binop $1 OpDiv $3 }
    | exp '&&' exp            { Conj $1 $3 }
    | exp '{' exp '}' '||' '{' exp '}' exp 
                              { Disj (Just $3) $1 (Just $7) $9 }
    | exp '||' exp            { Disj Nothing $1 Nothing $3 }
    | exp '==' exp            { Binop $1 OpEq $3 }
    | exp '/=' exp            { Binop $1 OpNe $3 }
    | exp '<' exp             { Binop $1 OpLt $3 }
    | exp '>' exp             { Binop $1 OpGt $3 }
    | exp '<=' exp            { Binop $1 OpLe $3 }
    | exp '>=' exp            { Binop $1 OpGe $3 }
    | exp ':' exp             { App (App (Con cons_con_name) $1) $3 }
    | 'case' exp 'of' branches 'end'
                              { Case $2 $4 }
    | 'let' decls 'in' exp    { Let $2 $4 }
    | 'let\'' pat '=' exp 'in' exp 
                              { Case $4 [Alt (getLoc $1) Nothing $2 $6] }
    | 'if' exp 'then' exp 'else' exp
                              { If $2 $4 $6 }
    | 'fix' '{' exp '}'       { Fix $3 }
    | 'fix' '{' INT '::' exp '}'       { FixN (unINT $3) $5 }
    | 'fresh' '{' VARID '::' btype '::' exp '}' 'in' exp  { Fresh (unVARID $3) $5 $7 $10 }
    | exp '!' VARID           { Inst $1 (unVARID $3) }
    | 'trace' VARID '(' exp ')' { TRACE (unVARID $2) $4 }
    | 'collect' '{' exp '}' exp  { Collect $3 $5 }

sexps :: { [Exp] }
    : sexp                 { [$1] }
    | sexp sexps           { $1 : $2 }

exps :: { [Exp] }
    :                      { [] }
    | cexps                { $1 }

cexps :: { [Exp] }
    : exp                  { [$1] } 
    | ccexps               { $1 }

ccexps :: { [Exp] }  
    : exp ',' cexps        { $1 : $3 }

branches :: { [Alt] } 
    : branch               { [$1] }
    | branch branches      { $1 : $2 }

branch :: { Alt }
    : '|' pat '->' exp     { Alt (getLoc $1) Nothing $2 $4 }
    | '|' VARID '%' pat '->' exp
                           { Alt (getLoc $1) (Just (Var (unVARID $2, Nothing))) $4 $6 }
    | '|' INT '%' pat   '->' exp
                           { Alt (getLoc $1) (Just (Lit (LitInt (unINT $2)))) $4 $6 }
    | '|' '%' exp '%' pat '->' exp
                           { Alt (getLoc $1) (Just $3) $5 $7 }

pat :: { Pat } 
    : ppat                 { $1 }
    | CONID ppats          { PApp (unCONID $1) $2 } 
    | pat ':' pat          { PApp cons_con_name [$1, $3] }

ppat :: { Pat }
    : '_'                  { PWild }
    | VARID                { PVar $ unVARID $1 }
    | CONID                { PApp (unCONID $1) [] }
    | '()'                 { PApp "()" [] }
    | '(' pat ')'          { $2 }
    | '(' ccpats ')'       { PApp (tuple_con_name (length $2)) $2 }
    | '[' ']'              { PApp nil_con_name [] }
    | '[' cpats ']'        { plistify $2 } 

{- {ppat}+ -}
ppats :: { [Pat] }
    : ppat                 { [$1] }
    | ppat ppats           { $1 : $2 }

cpats :: { [Pat] } 
    : pat                  { [$1] }
    | ccpats               { $1 }

ccpats :: { [Pat] } 
    : pat ',' cpats        { $1 : $3}

{

unINT :: Located Token -> Int
unINT t  = let (TInt i) = unLoc t in i 

unVARID :: Located Token -> VarId
unVARID t  = let (TVar i) = unLoc t in i

unCONID :: Located Token -> TyConId
unCONID t = let (TCon i) = unLoc t in i

unSTRING :: Located Token -> String
unSTRING t = let (TStr i) = unLoc t in i

happyError :: (Located Token) -> P a
happyError (L loc tok) = throwError $ mkParseError "" loc (show tok)

mkConDecl :: OTcType -> P ConDecl
mkConDecl (TcCon c _n ts) = return $ ConDecl c ts
mkConDecl _ = error "Illegal data declaration"

fixConType :: [OTcType] -> OTcType 
fixConType (TcCon c 0 [] : ts') = TcCon c (length ts') ts'
fixConType [t] = t
fixConType t = error $ "Illegal type application : " ++ show t

appify :: Exp -> [Exp] -> Exp
appify e [] = e 
appify e (x:xs) = appify (App e x) xs

listify :: [Exp] -> Exp 
listify (e:es) = App (App (Con cons_con_name) e) (listify es)
listify [] = Con nil_con_name

plistify :: [Pat] -> Pat 
plistify [] = PApp nil_con_name []
plistify (x:xs) = PApp cons_con_name [x,plistify xs]

-- | TODO: Actually check declarations
checkRevDecls :: [Decl] -> P [Decl]
checkRevDecls = return 

extractTVar :: OTcType -> TyVarId 
extractTVar (TcVar x) = x
extractTVar _ = error "Not a variable"

checkDataHeader :: OTcType -> P (TyConId, [TyVarId])
checkDataHeader (TcCon c _ ts) = return (c, map extractTVar ts)
checkDataHeader _ = error "Illegal header declaration"

checkValDef :: SrcLoc -> VarId -> [(VarId,Maybe Int)] -> Exp -> P Decl
checkValDef s i is e = return $ FunDecl s i is e Nothing

fromSigDecls :: [Decl] -> [(VarId, OTcType)]
fromSigDecls = map (\(TypeSig _ v _ t) -> (v,t))

--fromFunDecls :: [Decl] -> [(VarId, [(VarId, Maybe Int)], Exp, Maybe )]
fromFunDecls = map (\(FunDecl _ v l e _) -> (v,l,e, Nothing))

unType :: OTcType -> TyVarId
unType (TcVar x) = x 
unType _ = error "wtf/Parser.y"

recordDeclaration :: SrcLoc -> TyConId -> [TyVarId] -> [(VarId, OTcType)] -> [Decl]
recordDeclaration l c ts accessors = 
  let (names, types) = unzip accessors
      cname = "Mk" ++ c
      patnames = zipWith (\i _ -> "_rec_n_" ++ show i) [1..] names
      funs = zipWith (\i (fid, typ) -> 
                       [ -- TypeSig l fid [] typ ,
                         FunDecl l fid [("_rec", Nothing)] 
                           (Case (Var ("_rec", Nothing)) [Alt noLoc Nothing (PApp cname (map PVar patnames))
                                                          (Var ((patnames !! i), Nothing))])
                           Nothing ]
                     ) [0..] accessors
  in concat $ [DataDecl l c ts [ConDecl cname types]] : funs 

}

