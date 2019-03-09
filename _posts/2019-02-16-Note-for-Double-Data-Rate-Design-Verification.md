---
layout: post
title:  "Note for Double Data Rate Design Verification"
date:   2019-01-29
categories: Verification
---
# Issue
During working on a Double Data Rate design, I missed a serious bug which can be a cause of tape-out failed. My Design Under Test (DUT) captured data on both positive and negative clock edge (this is the reason why I call it a Double Data Rate Design). 

![Figure 1. Double Data Rate](/assets/20190216/20190216_1.jpg)

To capture data, designer want to use a double-flops structure as below figure. In this structure, the data at rising edge will be captured by positive edge flip-flop RF0,RF1 ; data at falling edge will be capture by negative edge flip-flop FF0, FF1

![Figure 2a. Correct Design Idea](/assets/20190216/20190216_2a.jpg)

Unfortunately, designer get wrong implementation. Instead of using negative edge flip-flop for FF1, he used positive edge flip-flop. This bug has not detected during RTL Verification phase, all test-cases still "get pass report". I just detect it when doing timing check, when STA engineer report that It is very hard to close-timing on this path. Thank god, my DUT is a very high-speed design, unless STA process can be done more easier.
 
![Figure 2b. Wrong Design Implement](/assets/20190216/20190216_2b.jpg)

The reason why the STA can not done.

![Figure 2c. Issue on STA](/assets/20190216/20190216_2c.jpg)

# Solution

Okay, let's analyze why my test-bench can not detect this problem on RTL simulation. Firstly, I crated a traditional test-bench like this

{% highlight verilog %}
initial begin
  Din = 0;
  @(posedge clk); #1ns;
  Din = 1;
  @(posedge clk); #1ns;
  Din = 0;
end
{% endhighlight %} 

The waveform on simulation will be like:

![Figure 3a. Missed-bug test-bench](/assets/20190216/20190216_3a.jpg)

You can see here, ff0.Q get expected value before t3. So that, despite activation edge of ff1 is positive or negative edge,  ff1.Q is always get correct value. This is reason why I can not detect this bug in RTL verification.

For considering this issue quickly, I added half_clock_cycle sequence delay to ff0 and rf0 inside RTL code

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
 
By this way, ff1 will capture valid data at next clock cycle. This lead to a logic synchronization failed, then the bug can be detected

![Figure 3a. Modified test-bench](/assets/20190216/20190216_3b.jpg)
 
# Open Discussion

The upper solution is not a completed solution, because it require modify RTL code and the verifier must have good understand about RTL design. These requirements cannot satisfy for all project situation. The better solution is create a Coding Rule which request Designer add a "half-cycle-delay" at first stage (FF0 and RF0) when using upper solution.

