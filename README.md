# NeonNumber-SML
This project is designed to write an executable specification of an abstract language system for a simple imperative programming language using SML(Standard Meta Language).


A Neon number is an integer where the digits of the square of the number sum up to the number itself.
For example, 9 is a Neon number because 9*9 = 81, 8 + 1 = 9.
The program is to determine whether a given number is a Neon number.
In this sample program, define num = 12, and the answer should be False.


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
