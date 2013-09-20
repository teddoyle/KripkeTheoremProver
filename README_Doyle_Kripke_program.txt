
Kripke Tableau program manual 
    Written by Edward Doyle

Table of contents
-----------------
I.   Introduction
II.  List of Files
III. Differences in Program and Dissertation Terminology
IV.  Installation and Usage
   1. Testing for the presence of ML 
   2. Acquiring Moscow ML
   3. Running Moscow ML
   4. Starting the Kripke Theorem Prover
   5. Using the Existing Test Cases
   6. Building Formulas
   7. The Naming Convention for Test Cases
   8. Writing New Test Cases
======================

I. Introduction
----------------
     This file describes how to use a ML program that
implements the Kripke tableau method for deciding
if a logic formula is a theorem in propositional
intuitionistic logic.

     This file and the ML source code files are a
supplement to Edward Doyle's dissertation "Two
Categories of Refutation Decision Procedures for
Classical and Intuitionistic Propositional Logic",
completed in December 2008, for his PhD in Computer
Science at Clemson University in the School of
Computing.  A pdf file containing the dissertation
is located at
http://etd.lib.clemson.edu/documents/1239896403/Doyle_clemson_0050D_10080.pdf

     As part of the research, a computer program was
written to implement the propositional part of Kripke's
method for proving theorems in intuitionistic
propositional logic.  This procedure is described in:
"Semantical Analysis of Intuitionistic Logic I" by
Saul Kripke, Proceedings of the Eighth Logic Colloquium,
Oxford, July 1963. Republished in "Formal Systems and
Recursive Functions", edited by J. Crossley and M. A. E.
Dummett, pages 92-130, in 1965 and published by
North-Holland Publishing Company, Amsterdam.


II. List of Files
-----------------
1. README_Doyle_Kripke_program.txt
      (this file)
2. kripke_method.sml
      (An ML source file containing the major functions 
       needed to implement and test Kripke's method.)
3. printTableau.sml:         
      (An ML source file containing a collection of
       function definitions used to print data structures
       used in the program.)
4. int_base_prop.sml :
      (A ML source file containing datatype declarations
      that are used by the functions in the other files.)

III. Differences in Program and Dissertation Terminology
-----------------------------------------------------
     The program was written before the dissertation,
during the writing of the program and early in the
dissertation the word expression was used instead of
formula, and hence, this program uses the word expression
instead of formula.  Also during the writing of the
dissertation a decision was made to use vertex and
vertices instead of node and nodes.


IV.  Installation and Usage
---------------------------
1. Testing for the presence of ML
-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
    Before acquiring and installing Moscow ML, one should
check to see if it is already installed.  To run Moscow ML
on a computer, enter "mosml" (without the quotes) at a
command prompt.  If the system responds with
something like:

---------
Moscow ML version 2.01 (January 2004)
Enter `quit();' to quit.
-      
---------

Then one can skip to step 3.  Note this program has only
been tested on version 2.01 (the current version as of
December 2008), other versions may not function correctly.

2. Acquiring Moscow ML
-=-=-=-=-=-=-=-=-=-=
    Moscow ML version 2.01 is available at the for a
variety of operating systems at the URL below.

http://www.itu.dk/~sestoft/mosml.html

    Download and install Moscow ML for the computer.

3. Running Moscow ML
-=-=-=-=-=-=-=-=-=-=
   Moscow ML is started by typing "mosml" on the command
line.  To exit Moscow ML, enter:

quit();

at a command prompt.

4. Starting the Kripke Theorem Prover
-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
After starting Moscow ML the Kripke tableau theorem
prover can be loaded using the command:

use "kripke_method.sml";

This command will read in kripke_method.sml which contains
commands to read the other two ML source files.


5. Using the Existing Test Cases
-=-=-=-=-=-=-=-=-=-=-=-=-=-=-=-
After the program is loaded, functions can now be invoked.
There are many test cases included in kripke_method.sml 
and are discussed below.  If one wants to test all cases
enter:

testAll();

The test cases can be run individually by invoking using
the names of the functions.  Section 7 discusses the
naming conventions.

6. Building Formulas
-=-=-=-=-=-=-=-=-=-=

Constructors:
--------------
   TRUE  -- the constant top
   FALSE -- the constant bot
   atom  -- Used to construct propositional variables.
         It has a single parameter, a string with the
         name of the propositional variable.

   binNode -- Used to construct formulas with a binary
         connective.  It has three parameters, the connective,
         the left subformula, and the right subformula.
         The binary operations are: tableauImp, tableauAnd,
         and tableauOr.

   unaryNode -- Used to construct formulas with a unary
        connective.  It has two parameters, the connective,
        and its subformula.  Currently there is only one
        unary connective, tableauNeg.

Examples of formulas:
---------------------
first declare some propositional variables:
     val A_prop = atom("A");
     val B_prop = atom("B");
     val C_prop = atom("C");
     val D_prop = atom("D");

    Each of the eight formulas below is displayed in three
formats, 1) in ASCII text form, 2) in Latex form, and
3) in ML form using the constructors present in the program.
-----------------------------------------------
Example 1:

ASCII:             ~A 
Latex:            \neg A
kripke_method:    unaryNode(tableauNeg, A_prop)
--------------------------
Example 2:

ASCII:            A /\ B 
Latex:            ( A \wedge B)
kripke_method:    binNode(tableauAnd, A_prop, B_prop) 
--------------------------
Example 3:

ASCII:             A \/ B 
Latex:           ( A \vee B)
kripke_method:    binNode(tableauOr, A_prop, B_prop) 
--------------------------
Example 4:

ASCII:            A ==> B
Latex:            (A \RightArrow B)
kripke_method:    binNode(tableauImp, A_prop, B_prop) 
--------------------------
Example 5:
 
ASCII:    (A /\ B) \/ C
Latex:    ( A \wedge B) \vee C

kripke_method:  binNode(tableauOr,
                     binNode(tableauAnd, A_prop, B_prop),
                     C_prop) 
--------------------------
Example 6:

ASCII:     ~(~A /\ ~B) 
Latex:    \neg ( \neg A \wedge \neg B)
 
kripke_method:   unaryNode(tableauNeg,
                    binNode(tableauAnd,
                       unaryNode(tableauNeg, A_prop),
                       unaryNode(tableauNeg, B_prop) ))
--------------------------
Example 7:

ASCII:  (~~A) \Rightarrow (~A) 
Latex:    (\neg \neg A) \Rightarrow (\neg A)

kripke_method:     binNode(tableauImp,
                      unaryNode(tableauNeg,
                         unaryNode(tableauNeg, A_prop)),
                      unaryNode(tableauNeg, A_prop) )
--------------------------
Example 8:

ASCII: (A --> (B --> C)) --> ((A /\ B) --> C)

Latex:  ( A \Rightarrow ( B \Rightarrow C)) -->
                      (( A \wedge B ) \Rightarrow C)

kripke_method:     binNode(tableauImp,
                      binNode(tableauImp, A_prop,
                         binNode(tableauImp, B_prop, C_prop)),
                      binNode(tableauImp,
                         binNode(tableauAnd, A_prop, B_prop), 
                         C_prop) )



7. The Naming Convention for Test Cases
-=-=-=-=-=-=-=-=-=-=-=-=--=-=-=-=-=-=-=

         The functions that test the Kripke method
implementation use suffixes in the function names to
indicate the type and source of the test case.

     _open - indicates the the formula being tested is
             a non-theorem.

     _vd   - indicates that the formula is taken from Dirk van
             Dalen's book "Logic and Structure", third edition.
             In his chapter on intuitionistic logic several
             theorems and non theorems are listed.
             In van Dalen's book each formula has either
             a bi-implication or an implication.
             The bi-implication indicates that the left side
             of the formula implies the right, and the right
             side implies the left.  While implication means
             the left side implies the right, but the right
             does not imply the left.  For each of van Dalen's
             formulas two tests were created, if formula N is
             of the form A <==> B, then two tests were created,
             kripTestN_vd() to test A ==> B and
             kripTestNa_vd() to test B ==> A.
             If formula N is of the form A ==> B, then two
             tests were created kripTestN_vd() to test A ==> B
             and kripTestNa_vd_open to test B ==> A
             (a non-theorem).

       _Lemma_5_2_2 - indicates that the formula is taken from
             Lemma 5.2.2 of van Dalen's book.  This lemma shows
             that other formulas are also theorems.  The same
             labeling rule used for his earlier formulas.
     

The function testAll runs each of the test cases displaying
both the returned result and the expected result.


8. Writing New Test Cases
-=-=-=-=-=-=-=-=-=-=-=-=-
    To test a formula, first constructors must be use to
create the formula and then pass it to the function
proveKripke.  There are many test cases in kripke_method.sml
that can be used as a guide.

To test the formula in example 2,  A /\ B, the ML function 
would be:

fun kripTest_exam2_open() = proveKripke(
                binNode(tableauAnd, A_prop, B_prop));

and can be invoked with the command:

kripTest_exam2_open();

==========================
END OF FILE
