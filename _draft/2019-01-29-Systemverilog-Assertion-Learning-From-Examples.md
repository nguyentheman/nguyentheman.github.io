---
layout: post
title:  "Systemverilog Assertion : Learning from examples"
date:   2019-01-29
categories: SystemVerilog
---

This is a study notebook for learning SystemVerilog Assertion. Most of information, code examples in this note are collected from "SystemVerilog Assertions and Functional Coverage", A.B. Mehta

http://www.eecs.umich.edu/courses/eecs578/eecs578.f15/miniprojects/SVAproject/manuals/SVA_EZ_startguide.pdf
http://www.project-veripage.com/sva_16.php

# 1. Background
## 1.1. Types of SystemVerilog Assertion
### 1.1.1. Immediate Assertion
> Immediate assertions are simple non-temporal domain assertions that are executed like statements in a procedural block. Interpret them as an expression in the condition of a procedural ‘if’ statement.

A sample of Immediate Assertion:
{% highlight verilog %}
assert (<Boolean expression>)
   pass_block;
else 
   fail_block;
{% endhighlight %}

The equivalent 'if' statement:

{% highlight verilog %}
if (<Boolean expression>)
   fail_block;
else 
   pass_block;
{% endhighlight %}

### 1.1.2. Concurrency Assertion
> In contract with Immediate Assertion, Concurrency Assertion describes the behavior of design. It similar a "checker block" which attached to original design to monitor the abnormal activities. 

Example Concurrency Assertion

{% highlight verilog %}
assert_example : assert property (@(posedge clk)
                 disable iff(rst_n) ($rose(req) |=> ##[1:3] gnt));
{% endhighlight %}

The upper assertion code describe the function: 
> At posedge clock which req = 1, the gnt signal must be asserted to 1 on next 1,2, or 3 clock cycle 

Detail component of "concurrency Assertion" is:
1. 'assert_example' : Assertion Label (option) - identifies the assertion. This is useful for reports and debugging.
2. 'assert property': Directive (required) - Specifies how the assertion is used during the verification process: as an assertion or constraint, or for collecting coverage information  
3. '@(posedge clk)' : Clocking (required) - Indicates how or when the signals in the assertion are sampled
4. 'disable iff(rst_n)': Disabling condition (option) - disable the assertion during certain conditions.
5. '($rose(req) |=> ##[1:3] gnt)': Property Expression (required)
  a. '$rose' : System function - Indicate one of the System Function that are used to automate some common operations.
  b. '|=>' : Implication Operator - specifies that the behavior defined on the right-hand side of the operator be checked only if the condition on the left-hand side occurs.
  c. '##'  : Cycle Operator - distinguishes between cycles of a sequence.
  d. '[1:3]' : Non-consecutive repetition operation - Enable the repetition of signal. 

## 1.2. Property Expression
## 1.2.1. Implication Operator

| Operator                                                   | Description                                                                                       |
|------------------------------------------------------------|---------------------------------------------------------------------------------------------------|
| ##m <br> ##[m:n]                                           | Clock delay                                                                                       |
| [*m] <br> [*m:n]                                           | Repetition-consecutive                                                                            |
| [=m] <br> [=m:n]                                           | Repetition-non consecutive                                                                        |
| [->m] <br> [->m:n]                                         | Goto repetition-non consecutive                                                                   |
| Sig1 throughout seq1                                       | Signal sig1 must be true throughout sequence seq1                                                 |
| Seq1 within seq2                                           | 'intersect' of two sequences; same as 'and' but both sequences must also 'end' at different times |
| Seq1 or seq2                                               | 'or' of two sequences. It succeeds if either sequence succeeds                                    |
| first_match_complex_seq1                                   | Matches only the first of possibly multiple matches                                               |
| not <property_expr>                                        | If <property_expr> evaluates to true, then not <property_expr> evaluates to false; and vice versa |
| if(expression) <property_expr1> <br> else <property_expr2> | if...else... within a property                                                                    |
| |->                                                        | Overlapping implication operator                                                                  |
| |=>                                                        | Non-overlapping implication operator                                                              |

## 1.2.2 System Function

| Function                                          | Meaning                                                                                                     |
|---------------------------------------------------|-------------------------------------------------------------------------------------------------------------|
| $rose(expression[,clocking_event])                | True, if the lease significant bit of expression changed to 1 <br> False, otherwise                         |
| $fell(expression[,clocking_event])                | True, if the least significant bit of the expression changed to 0 <br> False, otherwise                     |
| $stable(expression[,clocking_event])              | True, if the value of the expression did not change <br> False, otherwise                                   |
| $past(expression[,tick][,expr2][,clocking_event]) | returns the sampled value ticks clock ticks earlier (default 1) when expr2 was true (default expr2 is true) |

