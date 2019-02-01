---
layout: post
title:  "Systemverilog Assertion : Learning from examples"
date:   2019-01-29
categories: SystemVerilog
---

This is a study notebook for learning SystemVerilog Assertion. Most of information, code examples in this note are collected from "SystemVerilog Assertions and Functional Coverage", A.B. Mehta

# 1. Immediate Assertions

> Immediate assertions are simple non-temporal domain assertions that are executed like statements in a procedural block. Interpret them as an expression in the condition of a procedural ‘if’ statement.

An simple example of immediate Assertion:

{% highlight verilog %}
module test_immediate
(
    clk,
    a,b,c,d
);
    input clk;
    input a,b,c,d;
    always @(posedge clk)
    begin
        if(a) begin
            @(posedge d);
            bORc : assert (b||c) 
                    $display("\n",$stime,,,"%m assert passed\n");
                   else //This 'else' is for the 'assert'
                    $fatal("\n",$stime,,,"%m assert failed\n");
        end
    end
endmodule
{% endhighlight %}
 
There are 3 type of immediate Assertion:

1. immediate **assert**
2. immediate **assume**
3. immediate **cover**

# 2. Concurrent Assertions (sequence, property, assert)

> SPEC: At posedge clk, if cStart is High, that 'req' is high the same clock and 'gnt' is high 2 clocks later.

Step 1: DECLARE a sequence:: sequence 'sr1' states that "req be true this clock; that gnt must be true 2 clocks afters"

{% highlight verilog %}
sequence sr1;
  req ##2 gnt;
endsequence
{% endhighlight %}

Step 2: DECLARE a property :: property "pr1" triggers the 'sequence sr1' when cStart is true at posedge clk

{% highlight verilog %}
property pr1;
  @(posedge clk) cStart |-> sr1;
endproperty
{% endhighlight %}

Step 3: ASSERT a property:: A property on it's own is never evaluated. It must be 'asserted' (or covered or assumed)
{% highlight verilog %}
reqGnt: assert property(pr1) 
          $display($stime,,,"\t\t%m PASS");
        else
          $display($stime,,,"\t\t%m FAIL");
{% endhighlight %}