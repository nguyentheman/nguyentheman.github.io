---
layout: post
title:  "Efficient Synchronizer model for Cross-Clock-Domain design verification"
date:   2019-03-17
categories: SystemVerilog
---

{% highlight verilog %}
module syn2 #(parameter SIZE=1)
(
  output reg[SIZE-1] q2 ,
  input  reg[SIZE-1] d  ,
  input              clk,
  input              rst_n
);

`ifdef SYNTHESIS
  reg[SIZE-1:0] q1;
  always_ff @(posedge clk, negedge rst_n) begin
    if(!rst_n)  {q2,q1} <= '0;
    else        {q2,q1} <= {q1,d};
  end
`else
  reg [SIZE-1:0] y1, q1a, q1b;
  reg [SIZE-1:0] DLY = '0;

  assign y1 = (~DLY & q1a) | (DLY & q1b)
  always_ff @(posedge clk, negedge rst_n) begin
    if(!rst_n) {q2,q1b,q1a} <= '0;
    else       {q2,q1b,q1a} <= {y1,q1a,d}
  end
`endif

{% endhighlight %} 

#Reference 
[http://www.sunburst-design.com/papers/CummingsSNUG2008Boston_CDC.pdf](http://www.sunburst-design.com/papers/CummingsSNUG2008Boston_CDC.pdf "Clock Domain Crossing (CDC) Design and Verification Techniques Using System Verilog ")