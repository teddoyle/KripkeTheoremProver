
(* use "genGraph.sml"; *)
(* use "expr_tree.sml"; *)
use "int_base_prop.sml";
use "printTableau.sml";

load "Int";

(* =-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-

T \/   beta   forced                forced
F \/   alpha  unforced              unforced       
T /\   alpha  forced                forced
F /\   beta   unforced              unforced
T ->   beta   unforced              forced
F ->   alpha  forced*               unforced*
                  * for some new p
T ~    oneChild  unforced
F ~    oneChild  forced*

datatype forceValue = forced | unforced
*)

val debugFlag = false;

datatype proofCond = notProven | closedBranch
datatype frameType = New | Current | CurrentAndFuture
datatype conditionType = noSpecialCond | newConstant |
                         appropriateConst
exception noChild and noRightChild and notAtom and
          Invalid_Ruletype and RuleError

val stepId = ref 0;

fun member(_, []) = false
|   member(needle, x::xs) =
    if x = needle then true
    else member(needle, xs)


fun getLeftChild(unaryNode(_, A)) = A
|   getLeftChild(binNode(_, A, _)) = A
|   getLeftChild(_) = raise noChild


fun getRightChild(unaryNode(_, _)) = raise noChild
|   getRightChild(binNode(_, _, B)) = B
|   getRightChild(_) = raise noChild

(* val (ruleType, lookupFrameType,
          leftForceValue, rightForceValue, specialCondition) =
      lookupRule(forceVal, logicExpr)   (* what about new p >= p' *)
 *)

fun lookupRule(unused, _) = raise RuleError
|   lookupRule(_, nullTree) =
         (doNothing, Current, unused, unused, noSpecialCond)
|   lookupRule(forced, TRUE) =
         (doNothing, Current, unused, unused, noSpecialCond)
|   lookupRule(unforced, TRUE) =
         (closeBranch, Current, unused, unused, noSpecialCond)
|   lookupRule(forced, FALSE) =
         (closeBranch, Current, unused, unused, noSpecialCond)
|   lookupRule(unforced, FALSE) =
         (doNothing, Current, unused, unused, noSpecialCond)
|   lookupRule(forceVal, atom(A)) =
         (atomRule, Current, forceVal, unused, noSpecialCond)
|   lookupRule(forced, binNode(tableauOr, _, _)) =
         (beta, Current, forced, forced, noSpecialCond)
|   lookupRule(unforced, binNode(tableauOr, _, _)) =
         (alpha, Current, unforced, unforced, noSpecialCond)
|   lookupRule(forced, binNode(tableauAnd, _, _)) =
         (alpha, Current, forced, forced, noSpecialCond)
|   lookupRule(unforced, binNode(tableauAnd, _, _)) =
         (beta, Current, unforced, unforced, noSpecialCond)
|   lookupRule(unforced, binNode(tableauImp, _, _)) =
         (alpha, New, forced, unforced, noSpecialCond)
|   lookupRule(forced, binNode(tableauImp, _, _)) =
      (beta, CurrentAndFuture,
                unforced, forced, noSpecialCond)
|   lookupRule(unforced, unaryNode(tableauNeg, _)) = 
         (oneChild, New, forced, unused, noSpecialCond)
|   lookupRule(forced, unaryNode(tableauNeg, _)) =
         (oneChild, CurrentAndFuture, unforced, unused, noSpecialCond)


fun printRuleType(oneChild) = print "One child"
|   printRuleType(alpha) = print "Alpha"
|   printRuleType(beta) = print "Beta"
|   printRuleType(gamma) = print "Gamma"
|   printRuleType(delta) = print "Delta"
|   printRuleType(atomRule) = print "atom"
|   printRuleType(doNothing) = print "do nothing"
|   printRuleType(varRule(n)) = print ("Var" ^ (Int.toString(n)) )
|   printRuleType(TBD) = print "TBD"
|   printRuleType(formulaRule) = print "formula"
|   printRuleType(closeBranch) = print "close Branch"

(* ---------------------------

fun Kripke method

  parameters
     -- Agenda list
     -- forced / unforced atoms
     -- 
     -- curr / new list (* use up curr list before new list *)
     -- forced list (non-atoms)
     -- alternatives (* two way recursion *)
--------------------------- *)

exception EmptyList
exception ForceException
exception unknownRuleType

fun atomMember(_, nil) = false
|   atomMember(atomStr, x::xs) =
        if atomStr = x then true
        else atomMember(atomStr, xs)

fun doubleListHead(nil, nil) = raise EmptyList
|   doubleListHead(nil, y::ys) = (New, y , nil, ys)
|   doubleListHead(x::xs, nil) = (Current, x, xs, nil)
|   doubleListHead(x::xs, y::ys) = (Current, x, xs, y::ys)

fun tripleTuppleMerge( (xa, xb, xc), (ya, yb, yc) ) =
                           (xa @ ya, xb @ yb, xc @ yc )
(* fun forcedListUpdateSingle(forceVal, expr) = *)
fun forcedListUpdateSingle(forced, expr) = [(expr, nil, nil)]
|   forcedListUpdateSingle(unforced, expr) = [(nil, expr, nil)]
|   forcedListUpdateSingle(unused, expr) = raise ForceException

fun forcedListUpdateProc (frameVal, nil) = nil
|   forcedListUpdateProc (frameVal, (forceVal, expr)::forceListTail) =
    (* returns changes to forced list, unforcedList and newList *)
    forcedListUpdateSingle(forceVal, expr) @
       forcedListUpdateProc(frameVal, forceListTail)

fun printStringList(nil) = ()
|   printStringList(atom(x)::xs) = (
       print (x ^ "  ");
       printStringList(xs) )
|   printStringList(_::xs) = printStringList(xs)

fun printAtomLists(atomData) =
   let
      val (forcedAtoms, unforcedAtoms) = atomData
   in
      print "forced Atoms: ";
      printStringList forcedAtoms;
      print "\nunforced Atoms: ";
      printStringList unforcedAtoms;
      print "\n"
   end

fun printExprCompactList(nil) =()
|   printExprCompactList((forceVal, expr)::xs) = (
    if forceVal = forced then print "Forced- "
    else print "Unforced- ";
    printExprCompact(expr);
    if xs <> nil then print "\n"
    else print "";
    printExprCompactList(xs)
    )

fun printExprCompactListList(nil) =()
|   printExprCompactListList((exprList)::xs) = (
       print "-=";
       printExprCompactList(exprList);
       print "=-\n";
       printExprCompactListList(xs)
    )

fun printAndReturn(str, step, result) =
    (  if debugFlag then
          print ("Branch ID: " ^ str ^ " Step: " ^ (Int.toString(step)) ^
                  (if result = closedBranch then " closedBranch"
                   else " not Proven") ^ "\n" ) 
       else print "";
       result )

fun reverse(nil) = nil  (*reserves a list *)
                        (* function from "Elements of ML programming" *)
                        (* by Jeffery Ullman, page 84 *)
|   reverse(x::xs) = reverse(xs) @ [x];

fun removeDups(nil) = nil   (* removes duplicates from list *)
                     (* leaves only last copy of duplicate in list. *)
                     (* You might want to reverse the list before *)
                     (* and after calling *)
|   removeDups(x::xs) = 
(
    if member(x, xs) then removeDups(xs)
    else [x] @ removeDups(xs)
)

fun removeDupsAtEnd(x) =
    reverse( removeDups( reverse(x) ) )

fun subset(nil, _ ) = true
|   subset(x::xs, nil) = false
|   subset(x::xs, y) =
(
   if member(x, y) then subset(xs, y)
   else false
)

fun handleNewSublist(nil) = nil
|   handleNewSublist(x::xs) =
      [x] :: handleNewSublist(xs)

fun solveNewList(atomData, propogateList,
          nil, _, _,step_new) = notProven (* closedBranch *)
|   solveNewList(atomData, propogateList,
                newHead::newTail, branchID, oldState, stepNum) =
    let
       val (forcedAtoms, unforcedAtoms) = atomData 
       val  newAtomData = (forcedAtoms, nil)
       val currStep = !stepId
    in
       stepId := !stepId + 1;
       if solveKripkeMethod(newAtomData, nil (*propogateList *),
                removeDupsAtEnd(newHead @ propogateList), nil,
                branchID, oldState, currStep) = closedBranch
       then closedBranch
       else solveNewList(atomData, propogateList, newTail,
                     branchID ^ "n", oldState, currStep)
(*       then ( print ("Closing at step: " ^
                   Int.toString(stepNum) ^ "\n");
              closedBranch )
       else solveNewList(atomData, propogateList,
                         newTail, branchID, oldState, currStep) *)
    end
and

    solveKripkeMethod(_, _, nil, nil, _, _, parentStep) =
       (  if debugFlag then
             print ("returning NOT PROVEN- nil Agenda - nil New step: " ^
                Int.toString(parentStep) ^ "\n")
          else print "";
          notProven )
|   solveKripkeMethod(atomData, propogateList,
                               nil, (* empty Agenda List *)
                           newList, branchID, oldState, parentStep) =
       let
          val (forcedAtoms, unforcedAtoms) = atomData
          val (oldPropList, oldAtomData) = oldState
          val (oldForcedAtoms, oldUnforcedAtoms) = oldAtomData
          val newBranchID = branchID ^ "n";
          val currStep = !stepId + 1;
       in
          stepId := !stepId + 1;
     (* July 3 start *)
          if subset(propogateList, oldPropList)
             andalso propogateList <> nil
             andalso subset(forcedAtoms, oldForcedAtoms)
          then ( if debugFlag then
                    print "returning NOT PROVEN - inf loop \n"
                 else print "";
                 notProven )
          else (* July 3 end*)
          solveNewList((forcedAtoms, nil), propogateList, newList,
                 branchID, (propogateList, atomData), currStep )
       end
|   solveKripkeMethod(atomData, propogateList,
                        currAgendaHead::currAgendaTail, newAgendaList,
                       branchID, oldState, parentStep) =
(* If current Agenda list is not empty then take first expression
   off of currAgendaList, If current agendaList is empty then take
   first expression off of newAgendaList.  If both are empty then
   return unproven. *)
   let
      val (forcedAtoms, unforcedAtoms) = atomData
      val newAtomData = (forcedAtoms, nil)
      val (forceVal, logicExpr) = currAgendaHead
      (* val unforcedList = if exprFrameType = New then nil
                   else unforcedAtoms *)
      val propogateList = propogateList @
           ( if forceVal <> unforced andalso
                not(member((forceVal, logicExpr), propogateList)) then 
                      [(forceVal, logicExpr)]
             else []
           )
      val (ruleType, lookupFrameType,
               leftForceValue, rightForceValue, specialCond) =
            lookupRule(forceVal, logicExpr)   (* what about new p >= p' *)
      val currStep = !stepId + 1;
   in
      stepId := !stepId + 1; 
      if debugFlag then (
         print ("------------\n Step: " ^ Int.toString(!stepId) ^
                    "parentStep: " ^ Int.toString(parentStep) ^
                    " Branch ID: " ^ branchID ^ "\n");
         printAtomLists atomData;
         print "propogate List: ";
         printExprCompactList(propogateList);
         print "\nCurrent Agenda: \n";
         printExprCompactList([currAgendaHead]);
         print "\n";
         printExprCompactList(currAgendaTail);
         print "\nNew Agenda: ";
         printExprCompactListList(newAgendaList);
         print "\n";
         printRuleType(ruleType);
         print "\n";
         if ruleType <> atomRule then
         (
            print "Left Child: ";
            printExprCompactList( [(leftForceValue,
                                (getLeftChild logicExpr) )] );
            printForceValue leftForceValue;
            print "\n"
         )
         else ();
         if ruleType = alpha orelse ruleType = beta then
         (
            print "Right Child: ";
            printExprCompactList( [(rightForceValue,
                                (getRightChild logicExpr) )] );
            printForceValue rightForceValue; 
            print "\n" )
         else ()
      )
      else print "";

      if ruleType = doNothing then
         solveKripkeMethod(atomData, propogateList, currAgendaTail,
                    newAgendaList, branchID, oldState, currStep)
      else if ruleType = closeBranch then closedBranch
      else if ruleType = oneChild then
         let
            val newListItem = [(leftForceValue, (getLeftChild logicExpr))]
            val updatedPropogateList =
                if leftForceValue = forced andalso lookupFrameType <> New
                       (* orelse currAgendaProp *) then
                     propogateList @ newListItem
                else propogateList
         in
            if lookupFrameType = Current then
               printAndReturn( ("oneChild " ^ branchID), parentStep,
               solveKripkeMethod(atomData, (*updated *) propogateList,
                   currAgendaTail @ newListItem, newAgendaList,
                   branchID, oldState, currStep) )
            else if lookupFrameType = CurrentAndFuture then
               printAndReturn( ("oneChild " ^ branchID), parentStep,
               solveKripkeMethod(atomData,
                   propogateList (* @ newListItem *),
                   currAgendaTail @ newListItem, newAgendaList,
                   branchID, oldState, currStep) )
            else (* lookupFrameType = New *)
               printAndReturn( ("oneChild " ^ branchID), parentStep,
               solveKripkeMethod(newAtomData, (*updated*) propogateList,
                    currAgendaTail,
                    newAgendaList @ [newListItem],
                    branchID, oldState, currStep) )
         end
      else if ruleType = alpha then
         let
            val leftBranch = (leftForceValue, (getLeftChild logicExpr))
            val rightBranch = (rightForceValue, (getRightChild logicExpr))
            val updatedPropogateList =
                if leftForceValue = forced then
                   if rightForceValue = forced then
                      [leftBranch, rightBranch] @ propogateList
                   else [leftBranch] @ propogateList
                else if rightForceValue = forced then
                     [rightBranch] @ propogateList
                else propogateList
         in
            if lookupFrameType = Current then
               printAndReturn( ("Alpha " ^ branchID), parentStep,
               solveKripkeMethod(atomData, (*updated *)propogateList,
                    currAgendaTail @ [leftBranch, rightBranch],
                      newAgendaList, branchID, oldState, currStep) )
            else if lookupFrameType = CurrentAndFuture then
               printAndReturn( ("Alpha " ^ branchID), parentStep,
               solveKripkeMethod(atomData,
                    propogateList (* @ [leftBranch, rightBranch] *),
                    currAgendaTail @ [leftBranch, rightBranch],
                    newAgendaList, branchID, oldState, currStep) )
            else  (* lookupFrameType = New *)
               printAndReturn( ("Alpha " ^ branchID), parentStep,
               solveKripkeMethod( newAtomData, (* updated *) propogateList,
                    currAgendaTail,
                    newAgendaList @ [[leftBranch, rightBranch]],
                    branchID, oldState, currStep) )
          end
      else if ruleType = beta then
         let
            val leftBranch = [(leftForceValue,
                     (*  currAgendaProp orelse  leftForceValue = forced,*)
                          (getLeftChild logicExpr))]
            val rightBranch = [(rightForceValue,
                  (* currAgendaProp orelse rightForceValue = forced, *)
                          (getRightChild logicExpr))]
            val newPropogateList =
                if forceVal = forced then propogateList @ [currAgendaHead]
                else propogateList
         in
            if lookupFrameType = Current then
               if printAndReturn( ("Beta " ^ branchID), parentStep,
                     solveKripkeMethod(atomData, (* new *) propogateList,
                        currAgendaTail @ leftBranch,
                        newAgendaList, (branchID ^ "l"),
                        oldState, currStep) ) = closedBranch andalso
                  printAndReturn( ("Beta " ^ branchID), parentStep,
                     solveKripkeMethod(atomData, (* new *) propogateList,
                        currAgendaTail @ rightBranch,
                        newAgendaList, (branchID ^ "r"),
                        oldState, currStep) ) = closedBranch
               then closedBranch
               else ( if debugFlag then
                         print ("Beta- Returning not proven " ^
                             branchID ^ "\n")
                      else print "";
                      notProven)
            else if lookupFrameType = CurrentAndFuture then
               if
               printAndReturn( ("Beta " ^ branchID), parentStep,
                   solveKripkeMethod(atomData, (*newP*) propogateList,
                      currAgendaTail @ leftBranch,
                      newAgendaList, (branchID ^ "l"),
                      oldState, currStep) ) = closedBranch andalso
               printAndReturn( ("Beta " ^ branchID), parentStep,
                  solveKripkeMethod(atomData, (* newP*) propogateList,
                      currAgendaTail @ rightBranch,
                      newAgendaList, (branchID ^ "r"),
                      oldState, currStep) ) = closedBranch
                  then closedBranch
               else (
                  if debugFlag then
                      print ("Beta - Returning not proven " ^
                           branchID ^ "\n")
                  else print "";
                  notProven )
            else (*lookupFrameType = new *)
               if
               printAndReturn( ("Beta " ^ branchID), parentStep,
                  solveKripkeMethod(newAtomData, nil,
                     (*new *) propogateList @ currAgendaTail,
                     newAgendaList @ [leftBranch], (branchID ^ "l"),
                     oldState, currStep) ) = closedBranch andalso
               printAndReturn( ("Beta " ^ branchID), parentStep,
                  solveKripkeMethod(newAtomData, nil,
                     (* new *) propogateList @ currAgendaTail,
                     newAgendaList @ [rightBranch], (branchID ^ "r"),
                     oldState, currStep) ) = closedBranch
               then closedBranch
               else ( if debugFlag then
                         print ("Beta - Returning not proven " ^
                                  branchID ^ "\n")
                      else print "";
                       notProven )
         end
      else if ruleType = gamma then closedBranch (* TBD *)
      else if ruleType = delta then closedBranch (* TBD *)
      else if ruleType = atomRule then
         ( 
            if debugFlag then
                printForceValue leftForceValue
            else print "";
            if leftForceValue = unforced then
               if member(logicExpr, forcedAtoms) then closedBranch
               else 
                  if leftForceValue = unforced then (
                   (*  print "Adding to unforced list\n"; *) print "";
                  printAndReturn( ("atom " ^ branchID ^ " "), parentStep,
                       solveKripkeMethod( (forcedAtoms,
                              unforcedAtoms @ [logicExpr] ),
                       propogateList, currAgendaTail,
                       newAgendaList, branchID, oldState, currStep) )
                  )
                  else
                     printAndReturn( ("atom " ^ branchID ^ " "), parentStep,
                     solveKripkeMethod( (forcedAtoms, unforcedAtoms),
                          propogateList, currAgendaTail,
                          newAgendaList, branchID, oldState, currStep) )
         else (* if leftForceValue = forced then *)
            if member(logicExpr, unforcedAtoms) then closedBranch
            else printAndReturn( ("atom " ^ branchID ^ " "), parentStep,
                    solveKripkeMethod(
                         (forcedAtoms @ [logicExpr], unforcedAtoms),
                          propogateList, currAgendaTail,
                          newAgendaList, branchID, oldState, currStep) )
         )
      else (* ruleType = unknown *)
         raise unknownRuleType
    (* endif *)
    
   end ;

fun proveKripke(expr) = (
    stepId := 0;
    solveKripkeMethod((nil, nil), nil, [(unforced, expr)], 
          nil, "", (nil, (nil, nil) ), !stepId )  )

val A_lit = atom("A");
val B_lit = atom("B");
val C_lit = atom("C");
val D_lit = atom("D");

(* basic test one -- True *)
fun basicTest1() = proveKripke(TRUE)

(* basic test two -- FALSE *)
fun basicTest1a_open() = proveKripke(FALSE)


(* test 1 -- A ^ B --> B ^ A *)
fun kripTest1_vd() = proveKripke(
                      binNode(tableauImp,
                         binNode(tableauAnd, A_lit, B_lit),
                         binNode(tableauAnd, B_lit, A_lit)) )
(* test 2 -- C v D --> D v C *)
fun kripTest2_vd() = proveKripke(
                      binNode(tableauImp,
                         binNode(tableauOr, C_lit, D_lit),
                         binNode(tableauOr, D_lit, C_lit) ) )
(* test 3 -- (A ^ B) ^ C --> A ^ (B ^ C) *) 
fun kripTest3_vd() = proveKripke(
                      binNode(tableauImp,
                         binNode(tableauAnd,
                            binNode(tableauAnd, A_lit, B_lit),
                               C_lit),
                         binNode(tableauAnd, A_lit,
                            binNode(tableauAnd, B_lit, C_lit) )) )
(* test 3a -- A ^ (B ^ C) --> (A ^ B) ^ C *)
fun kripTest3a_vd() = proveKripke(
                       binNode(tableauImp,
                          binNode(tableauAnd, A_lit,
                             binNode(tableauAnd, B_lit, C_lit) ),
                          binNode(tableauAnd,
                             binNode(tableauAnd, A_lit, B_lit),
                                C_lit)) )
(* test 4 -- (A v B) v C --> A v (B v C) *)
fun kripTest4_vd() = proveKripke(
                      binNode(tableauImp,
                         binNode(tableauOr,
                            binNode(tableauOr, A_lit, B_lit),
                               C_lit),
                         binNode(tableauOr, A_lit,
                            binNode(tableauOr, B_lit, C_lit) )) )
(* test 4a -- A v (B v C) --> (A v B) v C *)
fun kripTest4a_vd() = proveKripke(
                       binNode(tableauImp,
                          binNode(tableauOr, A_lit,
                             binNode(tableauOr, B_lit, C_lit) ),
                          binNode(tableauOr,
                             binNode(tableauOr, A_lit, B_lit),
                                C_lit) ) )
(* test5 -- A v (B ^ C) --> (A ^ B) v (A ^ C) *)
fun kripTest5_vd() = proveKripke(
                      binNode(tableauImp,
                         binNode(tableauOr, A_lit,
                            binNode(tableauAnd, B_lit, C_lit) ),
                         binNode(tableauAnd,
                            binNode(tableauOr, A_lit, B_lit),
                            binNode(tableauOr, A_lit, C_lit) ) ) )
(* test5a -- (A ^ B) v (A ^ C) --> A v (B ^ C) *)
fun kripTest5a_vd() = proveKripke(
                      binNode(tableauImp,
                         binNode(tableauAnd,
                            binNode(tableauOr, A_lit, B_lit),
                            binNode(tableauOr, A_lit, C_lit) ),
                         binNode(tableauOr, A_lit,
                            binNode(tableauAnd, B_lit, C_lit) ) ) )

(* test6 -- A ^ (B v C) --> (A ^ B) v (A ^ C) *)
fun kripTest6_vd() = proveKripke(
                      binNode(tableauImp,
                         binNode(tableauAnd, A_lit,
                            binNode(tableauOr, B_lit, C_lit) ),
                         binNode(tableauOr,
                            binNode(tableauAnd, A_lit, B_lit),
                            binNode(tableauAnd, A_lit, C_lit) ) ) )
(* test6a -- (A v B) ^ (A v C) --> A ^ (B v C) *)
fun kripTest6a_vd() = proveKripke(
                       binNode(tableauImp,
                          binNode(tableauOr,
                             binNode(tableauAnd, A_lit, B_lit),
                             binNode(tableauAnd, A_lit, C_lit) ),
                          binNode(tableauAnd, A_lit,
                             binNode(tableauOr, B_lit, C_lit) ) ) )
(* test 7 -- A --> ~ ~A *)
fun kripTest7_vd() = proveKripke(
                      binNode(tableauImp, A_lit,
                         unaryNode(tableauNeg,
                            unaryNode(tableauNeg, A_lit) ) ) )
(* test 7a --  ~ ~A --> A *) (* open *)
fun kripTest7a_vd_open() = proveKripke(
                      binNode(tableauImp,
                 unaryNode(tableauNeg, unaryNode(tableauNeg, A_lit) ),
                              A_lit ) )

(* test 8 -- (A --> (B --> C)) --> ((A ^ B) --> C) *)
fun kripTest8_vd() = proveKripke(
                      binNode(tableauImp,
                         binNode(tableauImp, A_lit,
                            binNode(tableauImp, B_lit, C_lit)),
                         binNode(tableauImp,
                            binNode(tableauAnd, A_lit, B_lit), 
                            C_lit) ))
(* test 8a -- ((A ^ B) --> C) --> (A --> ( B --> C)) *)
fun kripTest8a_vd() = proveKripke(
                       binNode(tableauImp,                    
                          binNode(tableauImp,
                             binNode(tableauAnd, A_lit, B_lit), 
                             C_lit),
                          binNode(tableauImp, A_lit,
                             binNode(tableauImp, B_lit, C_lit)) ))
(* test 9 -- A --> (B --> A) *)
fun kripTest9_vd() = proveKripke(
                      binNode(tableauImp, A_lit,
                         binNode(tableauImp, B_lit, A_lit) ))
(* test 9a -- (B --> A) --> A *) (* open *)
fun kripTest9a_vd_open() = proveKripke(
                      binNode(tableauImp,
                         binNode(tableauImp, B_lit, A_lit),
                                 A_lit ))

(* test 10 -- A --> (~A --> B) *)
fun kripTest10_vd() = proveKripke(
                       binNode(tableauImp, A_lit,
                          binNode(tableauImp,
                             unaryNode(tableauNeg, A_lit),
                             B_lit) ) )
(* test 10a -- (~A --> B) --> A *) (* open *)
fun kripTest10a_vd_open() = proveKripke(
                       binNode(tableauImp,
                          binNode(tableauImp,
                             unaryNode(tableauNeg, A_lit),
                             B_lit), A_lit ) )
(* test 11 -- ~(A v B) --> ~A ^ ~B *)
fun kripTest11_vd() = proveKripke(
                       binNode(tableauImp,
                          unaryNode(tableauNeg,
                             binNode(tableauOr, A_lit, B_lit)),
                          binNode(tableauAnd,
                             unaryNode(tableauNeg, A_lit),
                             unaryNode(tableauNeg, B_lit) ) ))
(* test 11a -- ~A ^ ~B --> ~(A v B) *)
fun kripTest11a_vd() = proveKripke(
                       binNode(tableauImp,
                          binNode(tableauAnd,
                             unaryNode(tableauNeg, A_lit),
                             unaryNode(tableauNeg, B_lit) ),
                          unaryNode(tableauNeg,
                             binNode(tableauOr, A_lit, B_lit)) ))
(* test 12 -- ~A v ~B --> ~(A ^ B) *)
fun kripTest12_vd() = proveKripke(
                       binNode(tableauImp,
                          binNode(tableauOr,
                             unaryNode(tableauNeg, A_lit),
                             unaryNode(tableauNeg, B_lit) ),
                          unaryNode(tableauNeg,
                             binNode(tableauAnd, A_lit, B_lit)) ))
(* test 12a -- ~(A ^ B) --> ~A v ~B *) (* open *)
fun kripTest12a_vd_open() = proveKripke(
                       binNode(tableauImp,
                          unaryNode(tableauNeg,
                             binNode(tableauAnd, A_lit, B_lit)),
                          binNode(tableauOr,
                             unaryNode(tableauNeg, A_lit),
                             unaryNode(tableauNeg, B_lit) )  ))
(* test 13 -- (~A v B) --> (A --> B) *)
fun kripTest13_vd() = proveKripke(
                       binNode(tableauImp,
                          binNode(tableauOr,
                             unaryNode(tableauNeg, A_lit), B_lit),
                          binNode(tableauImp, A_lit, B_lit) ));
(* test 13a -- (A --> B) --> (~A v B) *) (* open *)
fun kripTest13a_vd_open() = proveKripke(
                       binNode(tableauImp,
                          binNode(tableauImp, A_lit, B_lit),
                          binNode(tableauOr,
                             unaryNode(tableauNeg, A_lit), B_lit) ));
(* test 14 -- (A --> B) --> ( ~B --> ~A) *)
fun kripTest14_vd() = proveKripke(
                       binNode(tableauImp,
                          binNode(tableauImp, A_lit, B_lit),
                          binNode(tableauImp,
                             unaryNode(tableauNeg, B_lit),
                             unaryNode(tableauNeg, A_lit) ) ))
(* test 14a -- ( ~B --> ~A) --> (A --> B) *) (* open *)
fun kripTest14a_vd_open() = proveKripke(
                       binNode(tableauImp,
                          binNode(tableauImp,
                             unaryNode(tableauNeg, B_lit),
                             unaryNode(tableauNeg, A_lit) ),
                          binNode(tableauImp, A_lit, B_lit) ))
(* test 15 -- (A --> B) --> ((B --> C) --> (A --> C)) *)
fun kripTest15_vd() = proveKripke(
                       binNode(tableauImp,
                          binNode(tableauImp, A_lit, B_lit),
                          binNode(tableauImp,
                             binNode(tableauImp, B_lit, C_lit),
                             binNode(tableauImp, A_lit, C_lit))) )
(* test 15a -- ((B --> C) --> (A --> C)) --> (A --> B) *)
fun kripTest15a_vd_open() = proveKripke(   (* open *)
                       binNode(tableauImp,
                          binNode(tableauImp,
                             binNode(tableauImp, B_lit, C_lit),
                             binNode(tableauImp, A_lit, C_lit)),
                          binNode(tableauImp, A_lit, B_lit)  ) )

(* test 16 -- False --> (A ^ ~A) *)
fun kripTest16_vd() = proveKripke(
                         binNode(tableauImp, FALSE,
                            binNode(tableauAnd, A_lit,
                               unaryNode(tableauNeg, A_lit) ) ) )

(* test 16a --  (A ^ ~A) --> False *)
fun kripTest16a_vd() = proveKripke(
                         binNode(tableauImp,
                            binNode(tableauAnd, A_lit,
                               unaryNode(tableauNeg, A_lit) ),
                            FALSE) )
(* VD Lemma 5_2_2_num_1 ~A --> ~~~A *)
fun kripTest_Lemma_5_2_2_num_1() = proveKripke(
                          binNode(tableauImp,
                             unaryNode(tableauNeg, A_lit),
                             unaryNode(tableauNeg,
                                unaryNode(tableauNeg,
                                   unaryNode(tableauNeg, A_lit))) ) )

(* VD Lemma 5_2_2_num_1a ~~~A --> ~A *)
fun kripTest_Lemma_5_2_2_num_1a() = proveKripke(
                          binNode(tableauImp,
                             unaryNode(tableauNeg,
                                unaryNode(tableauNeg,
                                   unaryNode(tableauNeg, A_lit))),
                             unaryNode(tableauNeg, A_lit) ) )

(* VD Lemma 5_2_2_num_2 (A ^ ~B) --> ~(A --> B) *)
fun kripTest_Lemma_5_2_2_num_2() = proveKripke(
                         binNode(tableauImp,
                            binNode(tableauAnd, A_lit,
                               unaryNode(tableauNeg, B_lit)),
                            unaryNode(tableauNeg,
                               binNode(tableauImp, A_lit, B_lit)) ))
(* VD Lemma 5_2_2_num_2a_open  ~(A --> B) --> (A ^ ~B) *)
fun kripTest_Lemma_5_2_2_num_2a_open() = proveKripke(
                         binNode(tableauImp,
                            unaryNode(tableauNeg,
                               binNode(tableauImp, A_lit, B_lit)),
                            binNode(tableauAnd, A_lit,
                               unaryNode(tableauNeg, B_lit)) ))
(* VD Lemma 5_2_2_num_3  (A --> B) --> (~~A --> ~~B) *)
fun kripTest_Lemma_5_2_2_num_3() = proveKripke(
                         binNode(tableauImp,
                            binNode(tableauImp, A_lit, B_lit),
                            binNode(tableauImp,
                               unaryNode(tableauNeg,
                                  unaryNode(tableauNeg, A_lit) ),
                               unaryNode(tableauNeg,
                                  unaryNode(tableauNeg, B_lit) ) )) )
(* VD Lemma 5_2_2_num_3a_open (~~A --> ~~B) --> (A --> B) *)
fun kripTest_Lemma_5_2_2_num_3a_open() = proveKripke(
                         binNode(tableauImp,
                            binNode(tableauImp,
                               unaryNode(tableauNeg,
                                  unaryNode(tableauNeg, A_lit) ),
                               unaryNode(tableauNeg,
                                  unaryNode(tableauNeg, B_lit) )),
                            binNode(tableauImp, A_lit, B_lit) ))

(* VD Lemma 5_2_2_num_4  ~~(A --> B) --> (~~A --> ~~B) *)
fun kripTest_Lemma_5_2_2_num_4() = proveKripke(
                         binNode(tableauImp,
                            unaryNode(tableauNeg,
                               unaryNode(tableauNeg,
                                  binNode(tableauImp, A_lit, B_lit))),
                            binNode(tableauImp,
                               unaryNode(tableauNeg,
                                  unaryNode(tableauNeg, A_lit) ),
                               unaryNode(tableauNeg,
                                  unaryNode(tableauNeg, B_lit) ) )) )
(* VD Lemma 5_2_2_num_4a (~~A --> ~~B) --> ~~(A --> B) *)
fun kripTest_Lemma_5_2_2_num_4a() = proveKripke(
                         binNode(tableauImp,
                            binNode(tableauImp,
                               unaryNode(tableauNeg,
                                  unaryNode(tableauNeg, A_lit) ),
                               unaryNode(tableauNeg,
                                  unaryNode(tableauNeg, B_lit) ) ),
                            unaryNode(tableauNeg,
                               unaryNode(tableauNeg,
                                  binNode(tableauImp, A_lit, B_lit)))
				  ) )
(* VD Lemma 5_2_2_num_5  ~~(A ^ B) --> (~~A ^ ~~B) *)
fun kripTest_Lemma_5_2_2_num_5() = proveKripke(
                         binNode(tableauImp,
                            unaryNode(tableauNeg,
                               unaryNode(tableauNeg,
                                  binNode(tableauAnd, A_lit, B_lit))),
                            binNode(tableauAnd,
                               unaryNode(tableauNeg,
                                  unaryNode(tableauNeg, A_lit) ),
                               unaryNode(tableauNeg,
                                  unaryNode(tableauNeg, B_lit) ) )) )
(* VD Lemma 5_2_2_num_5a (~~A ^ ~~B) --> ~~(A ^ B) *)
fun kripTest_Lemma_5_2_2_num_5a() = proveKripke(
                         binNode(tableauImp,
                            binNode(tableauAnd,
                               unaryNode(tableauNeg,
                                  unaryNode(tableauNeg, A_lit) ),
                               unaryNode(tableauNeg,
                                  unaryNode(tableauNeg, B_lit) ) ),
                            unaryNode(tableauNeg,
                               unaryNode(tableauNeg,
                                  binNode(tableauAnd, A_lit, B_lit)))
				  ) )

fun testAll() = (
    print   "Test 1_vd:        expected: closedBranch  Actual: ";
    printVal (kripTest1_vd());
    print "\nTest 2_vd:        expected: closedBranch  Actual: ";
    printVal (kripTest2_vd());
    print "\nTest 3_vd:        expected: closedBranch  Actual: ";
    printVal (kripTest3_vd());
    print "\nTest 3a_vd:       expected: closedBranch  Actual: ";
    printVal (kripTest3a_vd());
    print "\nTest 4_vd:        expected: closedBranch  Actual: ";
    printVal (kripTest4_vd());
    print "\nTest 4a_vd:       expected: closedBranch  Actual: ";
    printVal (kripTest4a_vd());
    print "\nTest 5_vd:        expected: closedBranch  Actual: ";
    printVal (kripTest5_vd());
    print "\nTest 5a_vd:       expected: closedBranch  Actual: ";
    printVal (kripTest5a_vd());
    print "\nTest 6_vd:        expected: closedBranch  Actual: ";
    printVal (kripTest6_vd());
    print "\nTest 6a_vd:       expected: closedBranch  Actual: ";
    printVal (kripTest6a_vd());
    print "\nTest 7_vd:        expected: closedBranch  Actual: ";
    printVal (kripTest7_vd());
    print "\nTest 7a_vd_open:  expected: notProven     Actual: ";
    printVal (kripTest7a_vd_open());
    print "\nTest 8_vd:        expected: closedBranch  Actual: ";
    printVal (kripTest8_vd());
    print "\nTest 8a_vd:       expected: closedBranch  Actual: ";
    printVal (kripTest8a_vd());
    print "\nTest 9_vd:        expected: closedBranch  Actual: ";
    printVal (kripTest9_vd());
    print "\nTest 9a_vd_open:  expected: notProven     Actual: ";
    printVal (kripTest9a_vd_open());
    print "\nTest 10_vd:       expected: closedBranch  Actual: ";
    printVal (kripTest10_vd());
    print "\nTest 10a_vd_open: expected: notProven     Actual: ";
    printVal (kripTest10a_vd_open());
    print "\nTest 11_vd:       expected: closedBranch  Actual: ";
    printVal (kripTest11_vd());
    print "\nTest 11a_vd:      expected: closedBranch  Actual: ";
    printVal (kripTest11a_vd());
    print "\nTest 12_vd:       expected: closedBranch  Actual: ";
    printVal (kripTest12_vd());
    print "\nTest 12a_vd_open: expected: notProven     Actual: ";
    printVal (kripTest12a_vd_open());
    print "\nTest 13_vd:       expected: closedBranch  Actual: ";
    printVal (kripTest13_vd());
    print "\nTest 13a_vd_open: expected: notProven     Actual: ";
    printVal (kripTest13a_vd_open());
    print "\nTest 14_vd:       expected: closedBranch  Actual: ";
    printVal (kripTest14_vd());
    print "\nTest 14a_vd_open: expected: notProven     Actual: ";
    printVal (kripTest14a_vd_open());
    print "\nTest 15_vd:       expected: closedBranch  Actual: ";
    printVal (kripTest15_vd());
    print "\nTest 15a_vd_open: expected: notProven     Actual: ";
    printVal (kripTest15a_vd_open());
    print "\nTest 16_vd:       expected: closedBranch  Actual: ";
    printVal (kripTest16_vd());
    print "\nTest 16a_vd:      expected: closedBranch  Actual: ";
    printVal (kripTest16a_vd());

    print "\nTest Lemma_5_2_2_num_1:       expected: closedBranch  Actual: ";
    printVal(kripTest_Lemma_5_2_2_num_1() );
    print "\nTest Lemma_5_2_2_num_1a:      expected: closedBranch  Actual: ";
    printVal(kripTest_Lemma_5_2_2_num_1a() );
    print "\nTest Lemma_5_2_2_num_2:       expected: closedBranch  Actual: ";
    printVal(kripTest_Lemma_5_2_2_num_2() );
    print "\nTest Lemma_5_2_2_num_2a_open: expected: notProven     Actual: ";
    printVal(kripTest_Lemma_5_2_2_num_2a_open() );
    print "\nTest Lemma_5_2_2_num_3:       expected: closedBranch  Actual: ";
    printVal(kripTest_Lemma_5_2_2_num_3() );
    print "\nTest Lemma_5_2_2_num_3a_open: expected: notProven     Actual: ";
    printVal(kripTest_Lemma_5_2_2_num_3a_open() );
    print "\nTest Lemma_5_2_2_num_4:       expected: closedBranch  Actual: ";
    printVal(kripTest_Lemma_5_2_2_num_4() );
    print "\nTest Lemma_5_2_2_num_4a:      expected: closedBranch  Actual: ";
    printVal(kripTest_Lemma_5_2_2_num_4a() );
    print "\nTest Lemma_5_2_2_num_5:       expected: closedBranch  Actual: ";
    printVal(kripTest_Lemma_5_2_2_num_5() );
    print "\nTest Lemma_5_2_2_num_5a:      expected: closedBranch  Actual: ";
    printVal(kripTest_Lemma_5_2_2_num_5a() );

    print "\nBasic Test 1:         expected: closedBranch  Actual: ";
    printVal(basicTest1() );
    print "\nBasic Test 1a_open:   expected: notProven     Actual: ";
    printVal(basicTest1a_open() );

    print "\n"
)
