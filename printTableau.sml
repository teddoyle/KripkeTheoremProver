
fun printBinOp(tableauOr) = print "tabOr"
|   printBinOp(tableauAnd) = print "tabAnd"
|   printBinOp(tableauImp) = print "tabImp"

fun printUnaryOp(tableauNeg) = print "tabNeg"

fun printExprTree(nullTree) = 
    print "<null_Tree />"
|   printExprTree(TRUE) = (
    print "<expr>";
    print "TRUE";
    print "</expr>" )
|   printExprTree(FALSE) = (
    print "<expr>";
    print "FALSE";
    print "</expr>" )
|   printExprTree(atom(atomStr)) = (
    print "<atom>";
    print atomStr;
    print "</atom>"
    )
|   printExprTree(binNode(binOP, leftExpr, rightExpr)) = (
    print "<expr>";
    print "<binOp>";
    printBinOp(binOP);
    print "</binOp>";
    print "<leftExpr>";
    printExprTree leftExpr;
    print "</leftExpr>";
    print "\n";
    print "<rightExpr>";
    printExprTree rightExpr;
    print "</rightExpr>";
    print "</expr>"
    )
|   printExprTree(unaryNode(unaryOp, expr)) = (
    print "<expr>";
    print "<unaryOp>";
    printUnaryOp(unaryOp);
    print "</unaryOp>";
    print "<UnaryExpr>";
    printExprTree expr;
    print "</UnaryExpr>";
    print "\n";
    print "</expr>"
    )


fun printExprCompact(nullTree) = 
    print "<null_Tree />"
|  printExprCompact(atom(atomStr)) = print atomStr
|  printExprCompact(binNode(binOP, leftExpr, rightExpr)) = (
      print "(";
      printBinOp(binOP);
      print " ";
      printExprCompact leftExpr;
      print " ";
      printExprCompact rightExpr;
      print ") " )
|  printExprCompact(unaryNode(unaryOp, expr)) = (
      print "(";
      printUnaryOp(unaryOp);
      print " ";
      printExprCompact expr;
      print ")"
    )
|  printExprCompact(TRUE) = (
      print "True" )
|  printExprCompact(FALSE) = (
      print "False" )

fun printForceValue forceValue =
    if forceValue = unforced then print "F "
    else if forceValue = forced then print "T "
    else print "ERROR "


(* fun printTableauNode(tabNode(tablePos, branchSegment, forceValue,
             PO_TreeIndex, tabExprTree, sourceNode, binTreeData)) =
let
   val tabPos(currTabPos) = tablePos
   val PO_TreePos(PO_pos) = PO_TreeIndex
   val tabPos(sourceNodePos) = sourceNode
in
   (* (firstChild, nextSibling, parentPos  ))) = *)
   (
   print "<tabNode> <tabSign>";
   printForceValue forceValue;
(*   if forceValue then print "forced"
   else print "unforced"; *)
   print "</tabSign>";
   print "<branchSeg>";
   print (Int.toString(branchSeg_to_int branchSegment) );
   print "</branchSeg>";
   print "<PO_pos>";
   print (Int.toString(PO_pos));
   print "</PO_pos>";
   print "<exprTree>";
   printExprTree(tabExprTree);
   print "</exprTree>";
   print "<parentNode>";
   print (Int.toString(sourceNodePos));
   print "</parentNode>";
   print "</tabNode>\n"
   )
end *)
