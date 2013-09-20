(* File: int_base.sml  created on April 22, 2005 by Edward Doyle *)
(*  This file contains common data structures and code needed    *)
(* For different intuitioistic logic proof methods.              *)

type stringIndex = int

datatype fileSourceType = fileSource of stringIndex * stringIndex option

datatype functorType = functorName of stringIndex |
                       functorCall of stringIndex * generalTermType list
and
         generalTermType = genTermFunctor of functorType |
              termStr of stringIndex;

datatype binaryTableauOp = tableauOr | tableauAnd | tableauImp;
datatype unaryTableauOp = tableauNeg;

datatype quantifierType = forAll_quant | thereExists_quant | null_quant

datatype formulaRoleType = axiom | hypothesis | definition | lemma |
                  theorem | conjecture | lemma_conjecture |
                  negated_conjecture | plain | fi_domain |
                  fi_functors | fi_predicates | unknown |
                  nullFormulaRole

datatype languageType = lang_cnf | lang_fof

datatype nameType = wordName of stringIndex |
                    singleQuoteStrName of stringIndex |
                    intName of int

datatype predExprTree =
      nullTree | (* used as an error flag *)
      TRUE | FALSE |
      atom  of string |
      binNode of binaryTableauOp * predExprTree * predExprTree |
      unaryNode of unaryTableauOp * predExprTree


datatype condItem = condAtom of string;
datatype ruleType = oneChild | alpha | beta | gamma | delta |
                     atomRule | doNothing |
                     varRule of int |
                     TBD | formulaRule |
                     closeBranch;

datatype forceVal = unforced | forced (* | unforcedButPropogate *)
                       (* Dec 3, 2008 *) | unused;
