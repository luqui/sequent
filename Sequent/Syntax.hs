{-# LANGUAGE PatternGuards #-}

module Sequent.Syntax where

import Prelude hiding (lex, mapM, sequence)
import Data.Maybe (isNothing)
import Control.Applicative
import Control.Monad (guard)
import Data.List (intercalate)
import Sequent.Fixpoint (Error)
import Control.Arrow
import Data.Traversable (mapM, sequence)
import qualified Data.Set as Set
import qualified Data.Map as Map
import qualified Text.PrettyPrint as PP
import qualified Text.Parsec as P
import qualified Text.Parsec.Token as P
import qualified Text.Parsec.Language as P


newtype Name = Name { getName :: String }
    deriving (Eq,Ord)

data Type
    = TObject
    | TProp Prop

data Prop
    = PDoc Doc
    | PClause Clause

newtype Doc = Doc [Either String Expr]
    deriving (Eq)

data Expr
    = EVar Ref
    deriving (Eq)

data Ref = RBound Int Name -- de bruijn style
    deriving (Eq)

newtype Clause = Clause (Binder (Binder ()))

type Group a = Map.Map Name a

data Binder a = Binder (Group Type) a



class Bump a where
    bump :: Int -> a -> a

instance Bump Expr where
    bump n (EVar r) = EVar (bump n r)

instance Bump Ref where
    bump n (RBound z v) = (RBound $! z+n) v



class Subst a where
    subst :: Int -> Group Expr -> a -> a

instance Subst () where
    subst _ _ () = ()

instance Subst Type where
    subst _ _ TObject   = TObject
    subst n g (TProp p) = TProp (subst n g p)

instance Subst Prop where
    subst n g (PDoc d)    = PDoc (subst n g d)
    subst n g (PClause c) = PClause (subst n g c)

instance Subst Doc where
    subst n g (Doc xs)  = Doc $ (map.right) (subst n g) xs

instance Subst Expr where
    subst n g (EVar (RBound n' v))
        | n == n',
          Just e <- Map.lookup v g
        = e

instance Subst Clause where
    subst n g (Clause bs) = Clause (subst n g bs)

instance (Subst a) => Subst (Binder a) where
    subst n g (Binder bs exp) = 
        Binder (subst (n+1) g' <$> bs) (subst (n+1) g' exp)
        where
        g' = bump 1 <$> g

render1 = PP.renderStyle (PP.style { PP.mode=PP.OneLineMode }) 



class Pretty a where
    pretty :: a -> PP.Doc

instance Pretty Name where
    pretty (Name s) = PP.text s

instance Pretty Type where
    pretty TObject = PP.text "*"
    pretty (TProp p) = pretty p

instance Pretty Prop where
    pretty (PDoc d) = PP.brackets (pretty d)

instance Pretty Doc where
    pretty (Doc xs) = PP.hsep (map showX xs)
        where
        showX (Left s) = PP.text s
        showX (Right e) = PP.text "'" PP.<> pretty e

instance Pretty Expr where
    pretty (EVar v) = pretty v

instance Pretty Ref where
    pretty (RBound n v) = pretty v
        -- TODO two identically-named vars at different levels?

instance Pretty Clause where
    pretty (Clause (Binder hyp (Binder con ()))) = 
        PP.sep [ showTypeGroup hyp, PP.text "->", showTypeGroup con ]

showTypeGroup :: Group Type -> PP.Doc
showTypeGroup m = PP.sep (pvars : (line <$> Map.assocs hyps))
    where
    (vars, hyps) = Map.partition isObject m
    line (v,h) = pretty v PP.<> PP.text ":" PP.<+> pretty h
    pvars = PP.fsep (pretty <$> Map.elems vars)

isObject :: Type -> Bool
isObject TObject = True
isObject _ = False

showGroup :: (a -> PP.Doc) -> Group a -> PP.Doc
showGroup f = PP.sep . map line . Map.assocs
    where
    line (v,h) = pretty v PP.<> PP.text ":" PP.<+> f h



type Parser = P.Parsec String ()

lex = P.makeTokenParser P.haskellDef 
    { P.reservedNames = [] }

class Parse a where
    parse :: Parser a

instance Parse Name where
    parse = Name <$> P.identifier lex

instance Parse Type where
    parse = P.choice [
        TObject <$ P.symbol lex "*",
        TProp <$> parse ]

instance Parse Prop where
    parse = P.choice [ 
        PDoc <$> P.brackets lex parse,
        PClause <$> P.parens lex parse ]

instance Parse Doc where
    parse = Doc <$> P.many docPart
        where
        docPart = Left <$> word <|> Right <$> qexpr
        word = P.lexeme lex (P.many1 (P.noneOf "[] \t\n'"))
        qexpr = P.char '\'' *> parse

instance Parse Expr where
    parse = EVar <$> parse

instance Parse Ref where
    -- a bit evil during parsing; we will
    -- do another pass to set the references
    -- properly
    parse = RBound (-1) <$> parse

instance Parse Clause where
    parse = conv <$> parseTypeGroup <* P.symbol lex "->" <*> parseTypeGroup
        where
        conv g1 g2 = Clause . Binder g1 . Binder g2 $ ()

parseTypeGroup :: Parser (Group Type)
parseTypeGroup = Map.fromList <$> P.many idful
    where
    idful = convert <$> parse <*> P.optionMaybe (P.symbol lex ":" *> parse)
    convert n Nothing = (n, TObject)
    convert n (Just a) = (n, a)



class NamePass a where
    namePass :: Map.Map Name Int -> a -> Error a

instance NamePass () where
    namePass _ = return

instance NamePass Type where
    namePass env TObject = return $ TObject
    namePass env (TProp p) = TProp <$> namePass env p

instance NamePass Prop where
    namePass env (PDoc d) = PDoc <$> namePass env d
    namePass env (PClause c) = PClause <$> namePass env c

instance NamePass Doc where
    namePass env (Doc xs) = Doc <$> (mapM.mapM) (namePass env) xs

instance NamePass Expr where
    namePass env (EVar v) = EVar <$> namePass env v

instance NamePass Ref where
    namePass env (RBound (-1) v)
        | Just z <- Map.lookup v env = return $ RBound z v
        | otherwise = fail $ "Not in scope: " ++ getName v
    namePass env (RBound n v) = return $ RBound n v

instance NamePass Clause where
    namePass env (Clause bs) = Clause <$> namePass env bs

instance (NamePass a) => NamePass (Binder a) where
    namePass env (Binder g body) = Binder <$> mapM (namePass env') g <*> namePass env' body
        where
        env' = (const 0 <$> g) `Map.union` (succ <$> env)
        
