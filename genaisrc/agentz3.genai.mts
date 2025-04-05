script({
    tools: ["agent_z3"],
})

$`Solve the following problems using Z3:

The Zhang family has 6 children: Harry, Hermione, Ron, Fred, George, and Ginny. 
The cost of taking Harry is $1200, Hermione is $1650, Ron is $750, Fred is $800, 
George is $800, and Ginny is $1500. Which children should the couple take to minimize 
the total cost of taking the children? They can take up to four children on the upcoming trip.

Ginny is the youngest, so the Zhang family will definitely take her.

If the couple takes Harry, they will not take Fred because Harry does not get along with him.

If the couple takes Harry, they will not take George because Harry does not get along with him.

If they take George, they must also take Fred.

If they take George, they must also take Hermione.

Even though it will cost them a lot of money, the Zhang family has decided to take at least three children.

The SMTLIB2 formula must not contain forall or exists. 
Use the Z3 command "minimize" to instruct the solver to minimize the cost of taking the children.
use the Z3 command "(check-sat)" to check if the formula is satisfiable.
`


/*


Twenty golfers wish to play in foursomes for 5 days. Is it possible for each golfer to play no more
 than once with any other golfer?

Use SMTLIB2 to formulate the problem as a quantifier free formula over linear integer arithmetic, 
also known as QF_LIA. 

For every golfer and for every day assign a slot.
The golfers are numbered from 1 to 20 and the days are numbered from 1 to 5.
Express the problem as a set of integer variables, where each variable represents a golfer's slot on a given day.
The variables should be named as follows: golfer_1_day_1, golfer_1_day_2, ..., golfer_20_day_5.

*/