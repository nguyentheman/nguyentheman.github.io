---
layout: post
title:  "Efficient Synchronizer model for Cross-Clock-Domain design verification"
date:   2019-03-17
categories: Design for Verification
author    : Nguyen The Man
---

# 1. Limitation of traditional Synchronizer implementation.

Have you ever stuck at Silicon test which fails on designed clock, but pass on lower clock speed. In this situation, Cross-Domain-Clock (CDC) verifiation is the one of thing you should review first, before deeper analyzing on silicon chip. In this article, I will point out the reason we usually miss-case when duing CDC verification.

Let's start with an example, assume that you must to design a circuit which capture data in bclk clock domain with valid signal is generated in aclk clock domain. This is a multi-clock domain design, then Designer use a synchronizer to avoiding metastability.

{% include image.html
  file="/assets/20190317/fig1.jpg" 
  figure="Figure 1.1."
  caption="Assumed design situation" %}

And this is designer's implementation of Synchronizer

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

This circuit works correctly during RTL verification phase with below waveform. Data is always captured exactly.

{% include image.html
  file="/assets/20190317/fig2.jpg" 
  figure="Figure 1.2."
  caption="Design waveform" %}

Everything seems okay until Static Timing Analysis (STA) guys set "path 1" to multi-cycle path for timing closing. 

{% include image.html
  file="/assets/20190317/fig3.jpg" 
  figure="Figure 1.3."
  caption="Timing path on CDC circuit" %}

In this situation, "path 1" is set to 2-cylcle path. It means we can not sure "avld" signal can meet timing at t1 or t3. This means there are two possible cases we need to verify in this design.

The first case is "avld" will meet timing at t1, then the waveform will be like the RTL simulation result at Figure 1.2

{% include image.html
  file="/assets/20190317/fig4.jpg" 
  figure="Figure 1.4."
  caption="Uncertainly captured edge of <b>avld</b> " %}

The second case is "avld" will meet timing at t3, then the waveform will be Figure 1.5 below. As you can see, our design can not capture correct Data in this situation. 

{% include image.html
  file="/assets/20190317/fig5.jpg" 
  figure="Figure 1.5."
  caption="<b>avld</b> is captured at t3" %}

# 2. Better Synchornizer modeling

For breaking out of the limitation of current Synchronizer implementation. Clifford (Refer to [1] for detail) suggest a better solution, he added a random select DLY value to add an extra flip-flop delay as circuit in Figure 1.6. 

{% include image.html
  file="/assets/20190317/fig6.jpg" 
  figure="Figure 2.1."
  caption="Sample Synchronizer cell" %}

The verilog implementation as below, DLY variable can be hierarchically set from the testbench to a reproducible 1's and 0's random value for testing purpose.

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

The upper implementation is good for RTL verification, but it take a bit inconvenient for Timing Backanotation check later. As we know the STA team will set the timing path the first flip-flop of Synchronizer is multi-cycle path (the path1 of Figure 1.3), then we accept the setup/hold violation in this flip-flop. However, the standard cell model will force output of flip-flop to "Unknow Value (X)" anytime the timing violation happens. So that, we must disable timing-check of the first flip-flop of Synchronizer, unless an "Unknown Value" will be propagate to behind logic.

{% include image.html
  file="/assets/20190317/fig7.jpg" 
  figure="Figure 2.2."
  caption="Trouble on Timing Back-Anotation check" %}

Clifford's coding style for Syn2 has not convenient to find out the list of flip-flop of Synchronizer which will be disable timing check. My colleague modified this code by using explicits flip-flops cell to implement sync2 block as below. In this code, SDFF is a cell-namle of flip-flop will be used to implement Synchronizer 

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

  SDFF S1 (q1,d,clk,rst_n);
  SDFF S2 (q2,q1,clk,rst_n);

`else
  reg [SIZE-1:0] y1, q1a, q1b;
  reg [SIZE-1:0] DLY = '0;

  SDFF S1 (q1a,d,clk,rst_n);

  //Extra added flip-flops
  SDFF S2 (q1b,q1a,clk,rst_n);
  assign y1 = (~DLY & q1a) | (DLY & q1b);

  SDFF S3 (q2,y1,clk,rst_n);
`endif
endmodule
{% endhighlight %} 

By this implement, we can easy search all instance of "syn2" module and access to S1 flip-flops for timing check disabling.

# 3. Reference 

[1] [http://www.sunburst-design.com/papers/CummingsSNUG2008Boston_CDC.pdf](http://www.sunburst-design.com/papers/CummingsSNUG2008Boston_CDC.pdf "Clock Domain Crossing (CDC) Design and Verification Techniques Using System Verilog ")

[2] [http://vlsibyjim.blogspot.com/p/static-timing-analysis-sta-basics.html](http://vlsibyjim.blogspot.com/p/static-timing-analysis-sta-basics.html "STA Basics")

[3] [https://www.edn.com/design/integrated-circuit-design/4433229/Basics-of-multi-cycle---false-paths](https://www.edn.com/design/integrated-circuit-design/4433229/Basics-of-multi-cycle---false-paths "https://www.edn.com/design/integrated-circuit-design/4433229/Basics-of-multi-cycle---false-paths")

[4] [http://www.design4silicon.com/2016/03/multicycle-path-all-you-know-about.html?fbclid=IwAR05-pOjWYH1B9UyD6kPktyoGUhzMdhEJt05vrGA54yD5JolDtCm8MW097A](http://www.design4silicon.com/2016/03/multicycle-path-all-you-know-about.html?fbclid=IwAR05-pOjWYH1B9UyD6kPktyoGUhzMdhEJt05vrGA54yD5JolDtCm8MW097A ""Multi-cycle path" All you want to know")