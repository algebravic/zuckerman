Zuckerman Numbers
=================

What do the numbers 36 and 384 have in common? They are both evenly
divisible by the product of their digits: $36 = 2 \times 3 \time 6$
and $384 = 4 \times 3 \times 8 \times 4$. A positive integer with
this property is called a *Zuckerman Number*. Properties of these
numbers are detailed in a number of sequences in the OEIS
1) [Numbers that are divisible by the product of their digits.](https://oeis.org/A007602 "Zuckerman Numbers")
2) [Quotients obtained when the Zuckerman numbers are divided by the product of their digits.](https://oeis.org/A007602 "quotients")
3) [Smallest number that is n times the product of its digits or 0 if impossible. ](https://oeis.org/A056770 "Smallest")

In investigating this we can slightly alter the problem: given a
positive integer multiple $m$, find all positive integers, $n$ so that
$n$ is equal to $m$ times the product of the decimal digits of $n$.

First one can easily show that, for a given $m$, there are only a
finite number of possible integers $n$ for which $n$ is $m$ times the
product of the digits of $n$. The reasoning is the following:

If $n$ is $k$ digits in length, then the largest the product can be is
$m \times 9^k$, since there are $k$ digits each of which is $\le
9$. However, any $k$-digit number must be $\ge 10^{k-1}$. Taking
logarithms and rearranging yields $k \le \frac{\log(9m)}{\log(10/9)}$.
The program given in <https://oeis.org/A056770> implicitly uses this
fact by considering all possible $k$, and then considering all
possible multisets of digits of length $k$, taking their product with
$m$ and checking if the result gives back the same multiset of
digits. This, however, is very wasteful. We would only like to
consider all multisets of digits of size $k$ so that $m$ times their
product is in the interval $[10^{k-1}, 10^k - 1]$. We give an
efficieng backtrack program which accomplishes this. In addition, it
appears that the number of such grows only linearly with $m$.
