script({
    tools: ["agent_z3"],
})

$`Solve the following problems using Z3:

Twenty golfers wish to play in foursomes for 5 days. Is it possible for each golfer to play no more
 than once with any other golfer?

Use SMTLIB2 to formulate the problem as a quantifier free formula over linear integer arithmetic, 
also known as QF_LIA. The formula should produce an assignemnt to the twenty golfers for the 5 days of foursomes. The SMTLIB2 formula must not contain forall or exists. 
`