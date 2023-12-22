type Integer_Constant = int;
type Boolean_Constant = bool;
datatype Variable = DC of string;
datatype Arithmatic_Op = Plus | Minus | Times | Div;
datatype Relational_Op = Lt | Le | Eq | Ne | Ge | Gt;
datatype Boolean_Op = And | Or;
datatype Operator = AO of Arithmatic_Op |
                    RO of Relational_Op | 
                    BO of Boolean_Op;
datatype Expression = Var of Variable |
                      Int_Const of Integer_Constant |
                      Bool_Const of Boolean_Constant |
                      OEE of Operator * Expression * Expression;
datatype Instruction = Skip |
                       Assign of Variable * Expression |
                       Cond of Expression * Instruction * Instruction |
                       loop of Expression * Instruction |
                       InstrSeq of Instruction list;
datatype Type = IV | BV;
type Declaration = Variable * Type;
type DeclarationList = Declaration list;
type Program = DeclarationList * Instruction;

(*Step1*)
(*/*
Sample 8.
A Neon number is an integer where the digits of square of the number sums up to the number itself.
For example, 9 is a Neon number because 9^2 = 81, 8 + 1 = 9.
The program is to determine whether a given number is a Neon number.
In this sample program, define num = 12, and the answer should be False.
*/
PROGRAM isNeonNum
{
num Integer;
square Integer;
temp Integer;
digit Integer;
sum Integer;
answer Boolean;
num = 12;
IF (num Lt 0) THEN answer = False;
ELSE
{
square = num Times num;
sum = 0;
WHILE (square Ne 0)
{
temp = square;
square = square Div 10;
digit = temp Minus square Times 10;
sum = sum Plus digit;
}
IF (sum Eq num) THEN answer = True;
ELSE answer = False;
}
}
*)

val d1: Declaration = (DC "num", IV);
val d2: Declaration = (DC "square", IV);
val d3: Declaration = (DC "temp", IV);
val d4: Declaration = (DC "digit", IV);
val d5: Declaration = (DC "sum", IV);
val d6: Declaration = (DC "answer", BV);

val DecVarList = [d1, d2, d3, d4, d5, d6];
val DVarList : DeclarationList = DecVarList;

(* WHILE *)
(* temp = square; *)
val a1 = Assign(DC "temp", Var (DC "square"));
(* square Div 10; *)
val exp1 = OEE(AO Div, Var (DC "square"), Int_Const (10));
(* square = square Div 10; *)
val a2 = Assign(DC "square", exp1);
(* square Times 10; *)
val exp2 = OEE(AO Times, Var (DC "square"), Int_Const (10));
(* temp Minus square Times 10; *)
val exp3 = OEE(AO Minus, Var (DC "temp"), exp2);
(* digit = temp Minus square Times 10; *)
val a3 = Assign(DC "digit", exp3);
(* sum Plus digit; *)
val exp4 = OEE(AO Plus, Var (DC "sum"), Var (DC "digit"));
(* sum = sum Plus digit; *)
val a4 = Assign(DC "sum", exp4);
(* WHILE (square Ne 0) *)
val whilecond1 = OEE(RO Ne, Var (DC "square"), Int_Const (0));
val whileSeqList = InstrSeq [a1, a2, a3, a4];
val while1 = loop (whilecond1, whileSeqList);

(* Inner If then else *)
(* IF (sum Eq num) THEN answer = True; ELSE answer = False; *)
(* (sum Eq num) *)
val Ifcond2 = OEE(RO Eq, Var (DC "sum"), Var (DC "num"));
(* answer = True *)
val ThenStmt2 = Assign(DC "answer", Bool_Const (true));
(* answer = False *)
val elseStmt2 = Assign(DC "answer", Bool_Const (false));
val if1 = Cond (Ifcond2, ThenStmt2, elseStmt2);

(* else part *)
(* square = num Times num; sum = 0; *)
val exp5 = OEE(AO Times, Var (DC "num"), Var (DC "num"));
(* square = num Times num; *)
val a5 = Assign(DC "square", exp5);
(* sum = 0; *)
val a6 = Assign(DC "sum", Int_Const (0));
val elseStmt1 = InstrSeq [a5, a6, while1, if1];

(* IF (num Lt 0) THEN answer = False; *)
val Ifcond1 = OEE(RO Lt, Var (DC "num"), Int_Const (0));
val ThenStmt1 = Assign(DC "answer", Bool_Const (false));
val IFCOND1 = Cond (Ifcond1, ThenStmt1, elseStmt1);

(* num = 9; *)
val a7 = Assign(DC "num", Int_Const (9));
val PrgmList = InstrSeq [a7, IFCOND1];

val Prgm = (DVarList, PrgmList);


(*Step2*)

(* Static Semantics *)

(*1-2 Check Validity for any declaration list*)

(*1. NOShowInDeclist: DeclarationList->Variable->Bool*)

val rec NOShowInDeclist= (
    fn ([])=>(fn(z:Variable)=>true) | 
    ((x:Variable,y:Type)::TailOfList)=>(fn(z:Variable)=>(z<>x) andalso NOShowInDeclist(TailOfList)(z)))

(*2. DecListValidity:DeclrationList->Bool*)

val rec DecListValidity = (
    fn (((x,y)::TailOfList):DeclarationList)=> (
       DecListValidity(TailOfList) andalso NOShowInDeclist(TailOfList)(x)) | ([]) => true)

(*Testcase 1*)
(*TestCase 1 (resTC1) - Good Case (true)*)
val DecGoodresTC1 = DecListValidity(DecVarList);

(*TestCase 2 (resTC2) - Bad Case (false)*)
val Bad_d1: Declaration = (DC "num", IV);
val Bad_d2: Declaration = (DC "square", IV);
val Bad_d3: Declaration = (DC "temp", IV);
val Bad_d4: Declaration = (DC "num", IV);
val Bad_d5: Declaration = (DC "sum", IV);
val Bad_d6: Declaration = (DC "answer", BV);

val Bad_DecVarList = [Bad_d1, Bad_d2, Bad_d3, Bad_d4, Bad_d5, Bad_d6];

val DecBadresTC2 = DecListValidity(Bad_DecVarList);

(*3-7: DeclarationList->TypeMapTable *)

datatype InternalType = InternalNoType | InternalTypeInt |InternalTypeBool;
type TypeMapTable =Variable->InternalType;

(*FirstTypeMapTable: TypeMapTable*)
val FirstTypeMapTable =(
    fn(v:Variable)=>InternalNoType);

(*Testcase 2 *)

val FirstTMTresTC2_Var1 = FirstTypeMapTable(DC "num");
val FirstTMTresTC2_Var2 = FirstTypeMapTable(DC "square");
val FirstTMTresTC2_Var3 = FirstTypeMapTable(DC "temp");
val FirstTMTresTC2_Var4 = FirstTypeMapTable(DC "digit");
val FirstTMTresTC2_Var5 = FirstTypeMapTable(DC "sum");
val FirstTMTresTC2_Var6 = FirstTypeMapTable(DC "answer");

(*ChangeTypeMapTable: TypeMapTable->Declaration->TypeMapTable*)


val ChangeTypeMapTable = (
    fn(X:TypeMapTable)=>(
        fn(a:Variable,BV)=>(fn(y:Variable)=>if y=a then InternalTypeBool else X(y)) |
		  (c:Variable,IV)=>(fn(m:Variable)=>if m=c then InternalTypeInt else X(m))));


(*Testcase 3*)

val MyTypeMapTable1 = ChangeTypeMapTable(FirstTypeMapTable)(d1);
MyTypeMapTable1(DC "num");
MyTypeMapTable1(DC "square");
MyTypeMapTable1(DC "temp");
MyTypeMapTable1(DC "digit");
MyTypeMapTable1(DC "sum");
MyTypeMapTable1(DC "answer");


val MyTypeMapTable2 = ChangeTypeMapTable(FirstTypeMapTable)(d2);
MyTypeMapTable2(DC "num");
MyTypeMapTable2(DC "square");
MyTypeMapTable2(DC "temp");
MyTypeMapTable2(DC "digit");
MyTypeMapTable2(DC "sum");
MyTypeMapTable2(DC "answer");

(*DecListToTypeMapTable : DeclarationList->TypeMapTable*)

val rec DecListToTypeMapTable = (
    fn ([]) => FirstTypeMapTable | 
    ((HeadofList::TailOfList):DeclarationList)=>
	    ChangeTypeMapTable(DecListToTypeMapTable(TailOfList))(HeadofList));


(*Testcase 4*)

val MyTable1 = DecListToTypeMapTable(DecVarList);
MyTable1(DC "num");
MyTable1(DC "square");
MyTable1(DC "temp");
MyTable1(DC "digit");
MyTable1(DC "sum");
MyTable1(DC "answer");
MyTable1(DC "DummyVar");

(*8-9 : Check validity for expressions*)

(*TypeOfExpression: TypeMapTable->Expression->InternalType  *)
val TypeOfExpression = (
    fn(tmt:TypeMapTable) => 
        fn(Var(v)) => tmt(v) |
          (Int_Const(ic)) => InternalTypeInt |
          (Bool_Const(bc)) => InternalTypeBool |
          (OEE(AO(aop),e1,e2)) => InternalTypeInt |
          (OEE(BO(bop),e1,e2)) => InternalTypeBool |
          (OEE(RO(rop),e1,e2)) => InternalTypeBool 
          )            

(*ExpressionValidity : Expression -> TypeMapTable -> Bool*)

val rec ExpressionValidity = (
    fn(Var(v)) => ( fn(tmt: TypeMapTable) => ( tmt(v) <> InternalNoType ) ) |
      (Int_Const(ic)) => (fn(tmt: TypeMapTable) => true ) |
      (Bool_Const(bc)) => (fn(tmt: TypeMapTable) => true ) |
      (OEE(AO(aop),e1,e2)) => (
        fn(tmt: TypeMapTable)=> ExpressionValidity(e1)(tmt) andalso
                                  ExpressionValidity(e2)(tmt) andalso
                                  TypeOfExpression(tmt)(e1) = InternalTypeInt andalso
                                  TypeOfExpression(tmt)(e2) = InternalTypeInt) |

      (OEE(BO(bop),e1,e2)) => (
        fn(tmt: TypeMapTable)=> ExpressionValidity(e1)(tmt) andalso
                                  ExpressionValidity(e2)(tmt) andalso
                                  TypeOfExpression(tmt)(e1) = InternalTypeBool andalso
                                  TypeOfExpression(tmt)(e2) = InternalTypeBool) |

      (OEE(RO(rop),e1,e2)) => (
        fn(tmt: TypeMapTable) => ExpressionValidity(e1)(tmt) andalso
                                 ExpressionValidity(e2)(tmt) andalso
                                 TypeOfExpression(tmt)(e1) = InternalTypeInt andalso
                                 TypeOfExpression(tmt)(e2) = InternalTypeInt) )

(*TestCase 5*)
(*Checks test cases for Airthematic operator exp, Var exp, Integer Constant exp*)
val ExpGoodResTC1 = ExpressionValidity(exp1)(MyTable1);
val ExpGoodResTC2 = ExpressionValidity(exp2)(MyTable1);

(*Checks test cases for boolean operator exp, Boolean Constant exp*)
val ExpGoodResTC3 = ExpressionValidity(OEE(BO And, Bool_Const(true), Bool_Const(true)))(MyTable1);

(*Checks test cases for Relational operator exp, Var exp, Integer Constant exp*)
val ExpGoodResTC4 = ExpressionValidity(whilecond1)(MyTable1);
val ExpGoodResTC5 = ExpressionValidity(Ifcond1)(MyTable1);

(*Checks test cases for Boolean Constant exp*)
val ExpGoodResTC6 = ExpressionValidity(Bool_Const(true))(MyTable1);

(*Checks a realistic bianry expression*)
val ExpGoodResTC7 = OEE(AO  Times, Int_Const 7, OEE(AO Plus, Int_Const 3, Int_Const 4));
val ExpGoodResTC8 = ExpressionValidity(ExpGoodResTC7)(MyTable1);

(*Checks for a realistic bad case*)
val badexp = OEE(AO Times, Var (DC "count"), OEE(AO Plus, Int_Const 5, OEE(AO Div, Var (DC "total"), Int_Const 2)));
val ExpBadResTC1 = ExpressionValidity(badexp)(MyTable1);

(*10: Check validity for Instruction*)

(* InstructionValidity : Instruction -> TypeMapTable -> Bool *)

val rec InstructionValidity = (
    fn(Skip) => (fn(tmt: TypeMapTable) => true ) |
      (Assign(v,e)) => (fn(tmt: TypeMapTable) => 
                          (tmt(v) = TypeOfExpression(tmt)(e)) andalso
                          (tmt(v) <> InternalNoType) andalso
                          ExpressionValidity(e)(tmt)) |
      (Cond(e,i1,i2)) => (fn(tmt: TypeMapTable) => 
                          (TypeOfExpression(tmt)(e) = InternalTypeBool) andalso
                          ExpressionValidity(e)(tmt) andalso
                          InstructionValidity(i1)(tmt) andalso
                          InstructionValidity(i2)(tmt)) |

      (loop(e,i)) => (fn(tmt: TypeMapTable) => 
                          (TypeOfExpression(tmt)(e) = InternalTypeBool) andalso
                          ExpressionValidity(e)(tmt) andalso
                          InstructionValidity(i)(tmt)) |

      (InstrSeq([])) => (fn(tmt: TypeMapTable) => true ) |
      (InstrSeq (HeadofList :: TOL) ) => 
                          (fn(tmt: TypeMapTable) => InstructionValidity(HeadofList)(tmt) andalso
                                                    InstructionValidity(InstrSeq(TOL))(tmt)));

(*Testcases 6 - good testcases for all 6 patterns in instructions*)
val InstGoodResTC1 = InstructionValidity(Skip)(MyTable1);
val InstGoodResTC2 = InstructionValidity(a1)(MyTable1);
val InstGoodResTC3 = InstructionValidity(if1)(MyTable1);
val InstGoodResTC4 = InstructionValidity(while1)(MyTable1);
val InstGoodResTC5 = InstructionValidity(InstrSeq[])(MyTable1)
val InstGoodResTC6 = InstructionValidity(whileSeqList)(MyTable1);

val badInstAssign = Assign(DC "digit", Bool_Const(true));
val InstBadResTC1 = InstructionValidity(badInstAssign)(MyTable1);


exception InvalidDecList;

exception InvalidProgramBody;


(*ProgramValidity : Program -> Bool *)

val ProgramValidity = (fn(decList: DeclarationList, ProgramBody: Instruction)=> 
                            if DecListValidity(decList) <> true 
                            then raise InvalidDecList
                            else (
                                if InstructionValidity(ProgramBody)(DecListToTypeMapTable (decList))
                                then true
                                else raise InvalidProgramBody
                            ));

(*TestCases 7*)

(*good test case*)
val ProgramValidity_TC1 = ProgramValidity(Prgm);

(*bad test cases *)

(*val InvalidProgramBody1 = Assign(DC "result", OEE(RO Eq, Var (DC "test"), Bool_Const true));

val BadPrgmDec = (Bad_DecVarList, PrgmList);
val BadPrgBody = (DVarList, InstrSeq [InvalidProgramBody1]);



val ProgramValidity_TC3 = ProgramValidity(BadPrgBody);
val ProgramValidity_TC2 = ProgramValidity(BadPrgmDec);*)

(* Step 3 - Dynamic Semantics *)

(*Step 1-4*)
 

 datatype ValueInMemory = VTrash | VI of int | VB of bool;
 type ProgStateInMemory= Variable -> ValueInMemory;

 (*FirstProgStateInMemory = ProgStateInMemory *)
 fun FirstProgStateInMemory(x:Variable) = VTrash;

 (*Testcases for each variable from sample for FirstProgStateInMemory*)
 val MyFirstProgStateInMemoryTC = FirstProgStateInMemory (DC "num");
 val MyFirstProgStateInMemoryTC = FirstProgStateInMemory (DC "square");
 val MyFirstProgStateInMemoryTC = FirstProgStateInMemory (DC "temp");
 val MyFirstProgStateInMemoryTC = FirstProgStateInMemory (DC "digit");
 val MyFirstProgStateInMemoryTC = FirstProgStateInMemory (DC "sum");
 val MyFirstProgStateInMemoryTC = FirstProgStateInMemory (DC "answer");


 (*ChangeProgramStateInMemoryByOneVar = Variable -> ValueInMemory -> ProgStateInMemory -> ProgStateInMemory*)

 val ChangeProgramStateInMemory = (
    fn(v:Variable)=>(fn(vim:ValueInMemory)=>(
        fn(psim:ProgStateInMemory)=>(
            fn(y:Variable)=> if y = v then vim else psim(y)
            )
        )
    )
)
(*2 step testing*)
val MyProgStateInMemory_TC1 = ChangeProgramStateInMemory(DC "num")(VI 9) FirstProgStateInMemory;
MyProgStateInMemory_TC1(DC "num");
MyProgStateInMemory_TC1(DC "square");
MyProgStateInMemory_TC1(DC "temp");
MyProgStateInMemory_TC1(DC "digit");
MyProgStateInMemory_TC1(DC "sum");
MyProgStateInMemory_TC1(DC "answer");

val MyProgStateInMemory_TC2 = ChangeProgramStateInMemory(DC "square")(VI 81) MyProgStateInMemory_TC1;
MyProgStateInMemory_TC2(DC "square");
MyProgStateInMemory_TC2(DC "num");
MyProgStateInMemory_TC2(DC "temp");
MyProgStateInMemory_TC2(DC "digit");
MyProgStateInMemory_TC2(DC "sum");
MyProgStateInMemory_TC2(DC "answer");

val MyProgStateInMemory_TC3 = ChangeProgramStateInMemory(DC "sum")(VI 0) MyProgStateInMemory_TC2;
MyProgStateInMemory_TC3(DC "sum");
MyProgStateInMemory_TC3(DC "square");
MyProgStateInMemory_TC3(DC "num");
MyProgStateInMemory_TC3(DC "temp");
MyProgStateInMemory_TC3(DC "digit");
MyProgStateInMemory_TC3(DC "answer");

val MyProgStateInMemory_TC4 = ChangeProgramStateInMemory(DC "temp")(VI 500) MyProgStateInMemory_TC3;
MyProgStateInMemory_TC4(DC "temp");
MyProgStateInMemory_TC4(DC "sum");
MyProgStateInMemory_TC4(DC "square");
MyProgStateInMemory_TC4(DC "num");
MyProgStateInMemory_TC4(DC "digit");
MyProgStateInMemory_TC4(DC "answer");

val MyProgStateInMemory_TC5 = ChangeProgramStateInMemory(DC "digit")(VI 1) MyProgStateInMemory_TC4;
MyProgStateInMemory_TC5(DC "digit");
MyProgStateInMemory_TC5(DC "sum");
MyProgStateInMemory_TC5(DC "square");
MyProgStateInMemory_TC5(DC "num");
MyProgStateInMemory_TC5(DC "temp");
MyProgStateInMemory_TC5(DC "answer");

val MyProgStateInMemory_TC6 = ChangeProgramStateInMemory(DC "answer")(VB true) MyProgStateInMemory_TC5;
MyProgStateInMemory_TC6(DC "answer");
MyProgStateInMemory_TC6(DC "sum");
MyProgStateInMemory_TC6(DC "square");
MyProgStateInMemory_TC6(DC "num");
MyProgStateInMemory_TC6(DC "temp");
MyProgStateInMemory_TC6(DC "digit");



(*Step 5 - ZeroDivisionException - raise exception when attempting to perform a division by zero*)

exception ZeroInDivision;

(*Step 6 - WrongOperationInArithE - raise when an invalid arithmetic operation other 
than 'Plus', 'Minus', 'Times', 'Div' is performed*)

exception WrongOperationInArithE;

(*Step 7 - takes 2 values as parameters and returns the result of applying the specified operation to the given values*)

val MeaningArithE = (
  fn(VI(i1), VI(i2)) => (
    fn(Plus) => VI(i1 + i2)  |
      (Minus) => VI(i1 - i2) | 
      (Times) => VI(i1 * i2) |
      (Div) => if i2 = 0
               then raise ZeroInDivision
               else VI(i1 div i2)) |
(_,_) => (fn( _ ) => raise WrongOperationInArithE ));

(*Step 8*)

exception WrongOperandInRelaE;
  
(*Step 9*)

val MeaningRelaE = (
  fn(VI(i1), VI(i2)) => (
    (fn (Lt) => VB(i1 < i2)  |
        (Le) => VB(i1 <= i2) |
        (Eq) => VB(i1 = i2)  |
        (Ne) => VB(i1 <> i2) |
        (Ge) => VB(i1 >= i2) |
        (Gt) => VB(i1 > i2))) |
(_,_) => (fn( _ ) => raise WrongOperandInRelaE));

(*Step 10*)

exception WrongOperandInBoolE;

(*Step 11*)

val MeaningBoolE = (
  fn (VB(i1), VB(i2)) => (
    fn(And) => VB(i1 andalso i2) |
      (Or)  => VB(i1 orelse i2)) |
(_,_) => (fn( _ ) => raise WrongOperandInBoolE));


(*Step 12*)

(*MeaningExpression: Expression -> PrgStateInMemory -> ValueInMemory*)

fun MeaningExpression (Var(v))(psim:ProgStateInMemory) = psim(v)  |
    MeaningExpression (Int_Const(ic))(psim:ProgStateInMemory) = VI(ic) |
    MeaningExpression (Bool_Const(bc))(psim:ProgStateInMemory) = VB(bc) |
    MeaningExpression (OEE(AO(aop),exp1,exp2))(psim:ProgStateInMemory) = 
       MeaningArithE(MeaningExpression (exp1)(psim), MeaningExpression (exp2)(psim)) (aop) |
    MeaningExpression (OEE(BO(bop),exp1,exp2))(psim:ProgStateInMemory) = 
       MeaningBoolE(MeaningExpression (exp1)(psim),MeaningExpression (exp2)(psim)) (bop) |
    MeaningExpression (OEE(RO(rop),exp1,exp2))(psim:ProgStateInMemory) = 
       MeaningRelaE(MeaningExpression (exp1)(psim),MeaningExpression (exp2)(psim)) (rop) 
    
(*6 Good testcases*)
(*Testcase for expression type "Variable" *)
val MeaningExpression_TC1 = MeaningExpression( Var (DC "num"))(MyProgStateInMemory_TC1);
(*Testcase for expression type "Integer" *)
val MeaningExpression_TC2 = MeaningExpression(Int_Const(1))(MyProgStateInMemory_TC1)
(*Testcase for expression type "Boolean" *)
val MeaningExpression_TC3 = MeaningExpression(Bool_Const(true))(MyProgStateInMemory_TC1)
(*Testcase for expression type "Arithematic Operator" *)
val MeaningExpression_TC4 = MeaningExpression(OEE(AO(Plus), Var (DC "num"),  Var (DC "square")))(MyProgStateInMemory_TC2);
(*Testcase for expression type "Relational Operator" *)
val MeaningExpression_TC5 = MeaningExpression(OEE(RO(Le), Var (DC "num"),  Var (DC "square")))(MyProgStateInMemory_TC2);
(*Testcase for expression type "Boolean Operator" *)
val MeaningExpression_TC6 = MeaningExpression(OEE(BO(And),(OEE(RO(Le), Var (DC "num"),  Var (DC "square"))),
                                             (OEE(RO(Gt), Var (DC "num"),  Var (DC "square")))))(MyProgStateInMemory_TC2);



(*Bad Testcases*)
(*
(*Bad testcase for "ZeroInDivision" from expression type "Arithematic Operator" *)
val MeaningExpression_BadTC1 = MeaningExpression (OEE(AO Div,  Var (DC "num"), Int_Const 0)) MyProgStateInMemory_TC1;
(*Bad testcase for "WrongOperationInArithE" from expression type "Arithematic Operator" *)
val MeaningExpression_BadTC2 = MeaningExpression(OEE(AO(Plus), Var (DC "num"),  Var (DC "square")))(MyProgStateInMemory_TC1);
(*Bad Testcase for "WrongOperationInRelaE" from expression type "Relational Operator" *)
val MeaningExpression_BadTC3 = MeaningExpression (OEE(RO Eq, Var (DC "num"), Bool_Const true)) MyProgStateInMemory_TC1;
(*Bad Testcase for "WrongOperationInBoolE" from expression type "Boolean Operator" *)
val MeaningExpression_BadTC4 = MeaningExpression (OEE(BO And, Var (DC "num"), Int_Const 5)) MyProgStateInMemory_TC1; 
*)

(*Step 13*)
(*MeaningInstruction: Instruction -> ProgStateInMemory -> ProgStateInMemory*)

fun MeaningInstruction (Skip) = (
      fn (psim:ProgStateInMemory) => psim) |
    MeaningInstruction (Assign(v, exp)) = (
      fn (psim:ProgStateInMemory) => ChangeProgramStateInMemory(v) (MeaningExpression(exp)(psim)) (psim)) |
    MeaningInstruction (Cond(exp,inst1,inst2)) = (
      fn (psim:ProgStateInMemory) => if MeaningExpression (exp)(psim) = VB(true)
                                     then MeaningInstruction (inst1)(psim)
										                 else MeaningInstruction (inst2)(psim)) |
    MeaningInstruction (loop(exp, inst)) = (
      fn (psim:ProgStateInMemory) => if MeaningExpression (exp)(psim) = VB(true)
                                     then MeaningInstruction (loop(exp, inst)) (MeaningInstruction (inst)(psim))
									                   else psim) |
    MeaningInstruction (InstrSeq([])) = (
      fn (psim: ProgStateInMemory) => psim ) |
    MeaningInstruction (InstrSeq(HeadOfList :: TailOfList )) = (
      fn(psim : ProgStateInMemory) => MeaningInstruction (InstrSeq(TailOfList )) (MeaningInstruction(HeadOfList)(psim))) ;

(*Testcases*)
(*Assign*)
val MeaningInstruction_TC1 = MeaningInstruction(a6)(FirstProgStateInMemory);
MeaningInstruction_TC1(DC "num");
MeaningInstruction_TC1(DC "square");
MeaningInstruction_TC1(DC "temp");
MeaningInstruction_TC1(DC "sum");
MeaningInstruction_TC1(DC "digit");
MeaningInstruction_TC1(DC "answer");

(*Cond*)
val MeaningInstruction_TC2 = MeaningInstruction(if1)(MyProgStateInMemory_TC3);

MeaningInstruction_TC2(DC "num");
MeaningInstruction_TC2(DC "square");
MeaningInstruction_TC2(DC "temp");
MeaningInstruction_TC2(DC "sum");
MeaningInstruction_TC2(DC "digit");
MeaningInstruction_TC2(DC "answer");

(*Loop*)
val MeaningInstruction_TC3 = MeaningInstruction(while1)(MyProgStateInMemory_TC3);
MeaningInstruction_TC3(DC "num");
MeaningInstruction_TC3(DC "square");
MeaningInstruction_TC3(DC "temp");
MeaningInstruction_TC3(DC "sum");
MeaningInstruction_TC3(DC "digit");
MeaningInstruction_TC3(DC "answer");

(*InstrSeq*)
val MeaningInstruction_TC4 = MeaningInstruction(whileSeqList)(MyProgStateInMemory_TC3);

MeaningInstruction_TC4(DC "num");
MeaningInstruction_TC4(DC "square");
MeaningInstruction_TC4(DC "temp");
MeaningInstruction_TC4(DC "sum");
MeaningInstruction_TC4(DC "digit");
MeaningInstruction_TC4(DC "answer");


(*Step 14*)
exception InvalidProgram;

(*Step 15*)
(* MeaningProgram : Program -> ProgStateInMemory *)

val MeaningProgram = (
  fn((DVarList,PrgmList):Program) => if ProgramValidity(DVarList, PrgmList)
							then MeaningInstruction(PrgmList)(FirstProgStateInMemory)
							else raise InvalidProgram);

(*Testcases*)
(*For this program the value program will execute with num = 9, since it is a valid neon number. The answer will be true
  However if the value for num is not a valid neon number, the answer will be false*)
val MyResult1 = MeaningProgram(Prgm);
MyResult1(DC "num");
MyResult1(DC "square");
MyResult1(DC "temp");
MyResult1(DC "digit");
MyResult1(DC "sum");
MyResult1(DC "answer");

(*Apply to the variable which is not in the sample program*)
MyResult1(DC "UnkVar");