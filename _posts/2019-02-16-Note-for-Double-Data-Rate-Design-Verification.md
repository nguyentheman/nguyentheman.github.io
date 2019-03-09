---
layout: post
title:  "Note for Double Data Rate Design Verification"
date:   2019-02-16
categories: Verification
---
# 1. Issue
During working on a Double Data Rate design, I missed a serious bug which can be a cause of tape-out failed. My Design Under Test (DUT) captured data on both positive and negative clock edge (this is the reason why I call it a Double Data Rate Design). 

{% include image.html
            img="/assets/20190216/20190216_1.jpg"
            title="Figure 1.1. Double Data Rate" %}

To capture data, designer want to use a double-flops structure as below figure. In this structure, the data at rising edge will be captured by positive edge flip-flop RF0,RF1 ; data at falling edge will be capture by negative edge flip-flop FF0, FF1

![](/assets/20190216/20190216_2a.jpg)
*Figure 1.2. Correct Design Idea*

Unfortunately, designer get wrong implementation. Instead of using negative edge flip-flop for FF1, he used positive edge flip-flop. This bug has not detected during RTL Verification phase, all test-cases still "get pass report". I just detect it when doing timing check, when STA engineer report that It is very hard to close-timing on this path. Thank god, my DUT is a very high-speed design, unless STA process can be done more easier.
 
![](/assets/20190216/20190216_2b.jpg)
*Figure 1.3. Wrong Design Implement*

The reason why the STA can not done.

![](/assets/20190216/20190216_2c.jpg)

Figure 1.4. Issue on STA

# 2. Solution
Okay, let's trace back to the reason why my test-bench do not detects this bug. Traditionally, I control Din for each rising clock cycle. A "miracle delay" - #1 is added to get better looking on waveform. 

{% highlight verilog %}
initial begin
  Din = 0;
  @(posedge clk); #1ns;
  Din = 1;
  @(posedge clk); #1ns;
  Din = 0;
end
{% endhighlight %} 

Assume that, we asserts Din at t0, then expected f_dout can be captured after 2.5 cycle (at t5). In case the design is implemented correctly, the output waveform should be: 

![](/assets/20190216/20190216_3a.jpg) 
*Figure 2.1. Expected Waveform*

Let's see the waveform at the bug case. Designer implements his circuit as figure 1.3. 

![](/assets/20190216/20190216_3b.jpg) 
*Figure 2.2. Bug-case Waveform*

You can see, if our test-bench captures f_dout at t5, we always get correct value, although the verification is working on the wrong RTL. The important question here, **how to find out this bug on RTL simulation?**

I do not know the solution for a general case. But, in my DUT, the first-stage of double-flops structure (RF0, RF1 flip-flop in figure 1.2) is a behavior model of a analog cell, then I can modified it to add a half-clock-cycle delay as below code:

{% highlight verilog %}
//RF0
always @(posedge clk, negedge rst_n) begin
  if(!rst_n) begin
    Q <= #half_clock_cycle 1'b0;
  end else begin
    Q <= #half_clock_cycle D;
  end
end

//FF0
always @(negedge clk, negedge rst_n) begin
  if(!rst_n) begin
    Q <= #half_clock_cycle 1'b0;
  end else begin
    Q <= #half_clock_cycle D;
  end
end
{% endhighlight %} 
 
By this way, we will get wrong value at t5. Then the bug can be found.

![](/assets/20190216/20190216_3c.jpg)
*Figure 2.3. Bug-case were found.*
 
# 3. Open Discussion

As I mentioned from previous session, my idea is not a general solution. It just be applied to "white-box" check where the tester has depth understand about the design concept. Please feel free to ask me if you have a better solution.

