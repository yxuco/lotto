# lotto

My first Rust code.

It searches for a collection of lotto tickets that guarantees a win of 4 matching balls in any lotto drawing.

It is interesting because there appears no math formula that can tell you the minimum number of tickets required for such guarantees.

Using the classic lotto game of choosing 6 out of 49 balls, how many tickets would you have to buy to guarantee that at least one of the tickets will match 4 numbers every week?

A brute force search in sequence of 1 through 49 will result in 8,563 tickets.  However, this number is not the minimal number required.

This Rust code proves that a search using random sequences can find a collection of less number tickets that is also enough to guarantee a match of 4 numbers every week.  One of the runs of this code produced a list of 6,681 tickets, although the result of multiple runs will produce different numbers, and I guess that there may be better algorithms that can beat the random search.