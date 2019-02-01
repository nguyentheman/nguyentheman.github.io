---
layout: post
title:  "Systemverilog Assertion : Learning from examples"
date:   2019-01-29
categories: SystemVerilog
---

This is a study notebook for learning SystemVerilog Assertion. Most of information, code examples in this note are collected from "SystemVerilog Assertions and Functional Coverage", A.B. Mehta

# Immediate Assertions

> Immediate assertions are simple non-temporal domain assertions that are executed like statements in a procedural block. Interpret them as an expression in the condition of a procedural ‘if’ statement.

{% highlight systemverilog %}
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
 
