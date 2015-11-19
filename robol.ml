(*

INF3110, assignment 1
Interpreter for ROBOL
Made by Kjetil Svalestuen / kjetisva

*)

(* Defining data types and exceptions *)
datatype direction = 
	  North
	| East 
	| South 
	| West;

datatype exp =
	  Ident of string
	| Number of int
	| Plus of exp * exp
	| Minus of exp * exp
	| Times of exp * exp
	| LargerThan of exp * exp
	| SmallerThan of exp * exp
	| Equals of exp * exp;

datatype stmt =
	  Stop
	| Move of direction * exp
	| Assignment of string * exp
	| While of exp * stmt list;

type position = int * int;
type stmtlst = stmt list

datatype grid = Grid of int * int;
datatype vardecl = VarDecl of string * exp;
datatype start = Start of position;
datatype robot = Robot of vardecl list * start * stmtlst;
datatype program = Program of grid * robot;

exception OutOfBounds of position * direction;

(* Evaluate all types of expressions *)
fun evalExp(LargerThan(e1, e2), decls) =
	  if evalExp(e1, decls) > evalExp(e2, decls) then 1 else 0
	| evalExp(SmallerThan(e1, e2), decls) =
	  if evalExp(e1, decls) < evalExp(e2, decls) then 1 else 0
	| evalExp(Equals(e1, e2), decls) =
	  if evalExp(e1, decls) = evalExp(e2, decls) then 1 else 0

	| evalExp(Plus(e1, e2), decls) = evalExp(e1, decls) + evalExp(e2, decls)
	| evalExp(Minus(e1, e2), decls) = evalExp(e1, decls) - evalExp(e2, decls)
	| evalExp(Times(e1, e2), decls) = evalExp(e1, decls) * evalExp(e2, decls)
	| evalExp(Number(n), decls) = n
	| evalExp(Ident(s), decls) = lookup(s, decls, decls)

(* Mutual recursion - lookup needs to be defined together with evalExp *)
and lookup(s, VarDecl(name, exp)::rest, decls) =
		if s = name then evalExp(exp, decls)
		else lookup(s, rest, decls);


fun checkBoundaries(i, imax) =
	if i < 0 orelse i > imax then 0 else 1;

(* Functions for evaluating types of statements ===*)
fun evalMove(Grid(xmax, ymax), (x, y), Move(direction, exp), decls) =
	case direction of
		  North => if checkBoundaries(y + 1, ymax) = 1 then (x, y + evalExp(exp, decls))
		  			else raise OutOfBounds((x, y), direction)
		| South => if checkBoundaries(y - 1, ymax) = 1 then (x, y - evalExp(exp, decls))
		  			else raise OutOfBounds((x, y), direction)
		| West => if checkBoundaries(x - 1, xmax) = 1 then (x - evalExp(exp, decls), y)
		  			else raise OutOfBounds((x, y), direction)
		| East => if checkBoundaries(x + 1, xmax) = 1 then (x + evalExp(exp, decls), y)
		  			else raise OutOfBounds((x, y), direction);

fun evalAssignment(Assignment(var, newexp), VarDecl(name, oldexp)::rest, decls) =
		if var = name then
			 VarDecl(name, Number(evalExp(newexp, decls)))::rest
		else VarDecl(name, oldexp)::evalAssignment(Assignment(var, newexp), rest, decls);

fun evalWhile(While(exp, whilestmts), rest, decls, copy) =
	if evalExp(exp, decls) = 1 then whilestmts @ (copy::rest)
	else rest;


(* Help function for interpret *)
fun inter (Grid(xmax, ymax), (x, y), decls, nil) = (x, y)
	| inter (Grid(xmax, ymax), (x, y), decls, Stop::stmtlst) = (x, y)
	| inter (Grid(xmax, ymax), (x, y), decls, Move(direction, exp)::stmtlst) =
		inter (Grid(xmax, ymax), evalMove(Grid(xmax, ymax), (x, y), Move(direction, exp), decls), decls, stmtlst)
	| inter (Grid(xmax, ymax), (x, y), decls, Assignment(s, exp)::stmtlst) =
		inter (Grid(xmax, ymax), (x, y), evalAssignment(Assignment(s, exp), decls, decls), stmtlst)
	| inter (Grid(xmax, ymax), (x, y), decls, While(exp, whilestmts)::stmtlst) =
		inter (Grid(xmax, ymax), (x, y), decls, 
			   evalWhile(While(exp, whilestmts), stmtlst, decls, While(exp, whilestmts)));

(* Main function - interprets a whole program *)
fun interpret (Program(Grid(xmax, ymax), 
			  Robot(decls,
			  		Start(xpos, ypos),
			  		stmtlst))) =
	inter (Grid(xmax, ymax), (xpos, ypos), decls, stmtlst)


(* Example programs from assignment text *)
val prog1 =
	Program(
		Grid(64, 64),
		Robot(
			[],

			Start(23, 30), [
				Move(West, Number(15)),
				Move(South, Number(15)),
				Move(East, Plus(Number(2), Number(3))),
				Move(North, Plus(Number(10), Number(27))),

				Stop
			]
		));

val prog2 =
	Program(
		Grid(64, 64),
		Robot(
			[VarDecl("i", Number(5)),
			 VarDecl("j", Number(3))],

			Start(23, 6), [
				Move(North, Times(Number(3), Ident("i"))),
				Move(East, Number(15)),
				Move(South, Number(4)),
				Move(West, Plus(Plus(Times(Number(2), Ident("i")),
									 Times(Number(3), Ident("j"))),
								Number(5))),
				Stop
			]
		));


val prog3 = 
	Program(
		Grid(64, 64), 
		Robot(
			[VarDecl("i", Number(5)),
			 VarDecl("j", Number(3))],

			Start(23, 6), [
				Move(North, Times(Number(3), Ident("i"))),
				Move(West, Number(15)),
				Move(East, Number(4)),

				While(LargerThan(Ident("j"), Number(0)), [
					Move(South, Ident("j")),
					Assignment("j", (Minus(Ident("j"), Number(1))))
				]),

				Stop
			]

		));

val prog4 =
	Program(
		Grid(64, 64),
		Robot(
			[VarDecl("j", Number(3))],
			Start(1, 1), [
				While(LargerThan(Ident("j"), Number(0)), [
					Move(North, Number(1))
				]),
			 	Stop
			]
		));

interpret(prog1);
interpret(prog2);
interpret(prog3);
interpret(prog4);