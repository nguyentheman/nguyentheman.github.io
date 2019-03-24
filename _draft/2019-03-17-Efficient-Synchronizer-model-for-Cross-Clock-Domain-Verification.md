---
layout: post
title:  "Efficient Synchronizer model for Cross-Clock-Domain design verification"
date:   2019-03-17
categories: SystemVerilog
---

#Limitation of traditional Synchronizer modeling

Have you ever stuck at Silicon test which fails on designed clock, but pass on lower clock speed. In this situation, Cross-Domain-Clock (CDC) verifiation is the one of thing you should review first, before deeper analyzing on silicon chip. In this article, I will point out the reason we usually miss-case when duing CDC verification.

Let's start with simple example, assume that you must to design a circuit which capture data in bclk clock domain with valid signal is generated in aclk clock domain. This is a multi-clock domain design, then Designer use a synchronizer to avoiding metastability.

{% include image.html
  file="/assets/20190317/fig4.jpg" 
  figure="Figure 1.1."
  caption="Assumed design situation" %}

And during RTL simulation, this circuit works correctly. The verification done with waveform as below, data is captured exactly.

{% include image.html
  file="/assets/20190317/fig7.jpg" 
  figure="Figure 1.2."
  caption="Design waveform" %}

Everything seems okay until STA team do their work. To close timing for this circuit, the timing path "path 2" is set to "multi-cycle" path.

{% include image.html
  file="/assets/20190317/fig2.jpg" 
  figure="Figure 1.3."
  caption="Timing path on CDC circuit" %}








For solving metastability in multi-clock design, designer usually uses 2-stage flipflop (or 3-stage flip-flops) as a synchronizer like below circuit

{% include image.html
  file="/assets/20190317/fig1.jpg" 
  figure="Figure 1.1."
  caption="2-stage flip-flop synchronizer circuit." %}

In most of case, designer implement exactly what they think. It means below HDL code usually is used.  

{% highlight verilog %}
module sync2 #(parameter SIZE=1)
(
  output reg[SIZE-1] q2 ,
  input  reg[SIZE-1] d  ,
  input              clk,
  input              rst_n
);
  reg[SIZE-1:0] q1;
  always_ff @(posedge clk, negedge rst_n) begin
    if(!rst_n)  {q2,q1} <= '0;
    else        {q2,q1} <= {q1,d};
  end
endmodule
{% endhighlight %} 

The upper code is correct, but it is not enough good for verification. As you know, in case of design circuit as Figure 1.1, STA engineer will set failed path (or multi-cycle path) to timing path from the last aclk flip-flop to first bclk flip-flop ("path 1" in Figure 1.2). This means we accept a timing violation on *bff1*, designer must ensure that *adat* signal will be stable on next clock cycle.

{% include image.html
  file="/assets/20190317/fig2.jpg" 
  figure="Figure 1.2."
  caption="Timing path on CDC circuit" %}

Let's take a lock on waveform, remember that depend on clock-skew between aclk and bclk, the timing-violation can be happened or not. It means, the logic at t1 is unknown, it can be 0 (in case, adat fails setup-time) or 1 (in case, adat meet timing).  

{% include image.html
  file="/assets/20190317/fig3.jpg" 
  figure="Figure 1.3."
  caption="Timing Violation problem" %}

Assume that, in out design, *adat* is valid signal, then we used it to capture data on bclk domain (See figure 1.3). Designer must to ensure data will valid before "valid" signal transition to logic 1. 


According upper discussion, we know that there is 2 case can be happen on "silicon", and the mission of verification is prove that design will capture correct data in both of 2 situation.

{% include image.html
  file="/assets/20190317/fig5.jpg" 
  figure="Figure 1.5a."
  caption="Case 1, timing violation" %}

{% include image.html
  file="/assets/20190317/fig6.jpg" 
  figure="Figure 1.5b."
  caption="Case 2, meets timing constraint" %}

Let's back on behavior model of "sync2" module, then put it in context of our waveform. We can see that, the RTL verification just simulate only "case 2". It's not good verification. 


# Efficient Synchornizer modeling



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
endmodule
{% endhighlight %} 

#Reference 
[http://www.sunburst-design.com/papers/CummingsSNUG2008Boston_CDC.pdf](http://www.sunburst-design.com/papers/CummingsSNUG2008Boston_CDC.pdf "Clock Domain Crossing (CDC) Design and Verification Techniques Using System Verilog ")

[http://vlsibyjim.blogspot.com/p/static-timing-analysis-sta-basics.html](http://vlsibyjim.blogspot.com/p/static-timing-analysis-sta-basics.html "STA Basics")

[https://www.edn.com/design/integrated-circuit-design/4433229/Basics-of-multi-cycle---false-paths](https://www.edn.com/design/integrated-circuit-design/4433229/Basics-of-multi-cycle---false-paths "https://www.edn.com/design/integrated-circuit-design/4433229/Basics-of-multi-cycle---false-paths")