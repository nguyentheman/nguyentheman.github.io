---
layout: post
title:  "Note for Double Data Rate Design Verification"
date:   2019-01-29
categories: Verification
---


# Issue
Double Data Rate design request data must to be captured on both positive and negative edge of clock. You can refer to [http://www.ni.com/white-paper/7284/en/](http://www.ni.com/white-paper/7284/en/ "this article") for detail concept of Double Data Rate
![Figure 1. Double Data Rate](https://nguyentheman.github.io/_img/20190216_1.jpg)

In common design solution, designer will use a double flops structure, one active on positive clock and another one active on negative clock as figure below:
![Figure 2a. Correct Design Idea](https://nguyentheman.github.io/_img/20190216_2a.jpg)

However, designer get wrong implementation, the FF1 flipflop actives at positive clock edge instead of negative clock edge. Unfortunately, my testbench can not detect this bug on RTL verification. Luckily, the problem is detected on Timing Back Annotation test-phase, when FF1 get a setup violation error. I call this is a lucky because this circuit is applied to 32 flip-flops but there are only 5 flip-flops get timing violation error.

![Figure 2b. Wrong Design Implement](https://nguyentheman.github.io/_img/20190216_2b.jpg)

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

The waveform on simulation will be like this:
![Figure 3a. Missed-bug test-bench](https://nguyentheman.github.io/_img/20190216_3a.jpg)

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
![Figure 3a. Modified test-bench](https://nguyentheman.github.io/_img/20190216_3b.jpg)
 
# Solution Limitation

The upper solution is not a completed solution, because it require modify RTL code and the verifier must have good understand about RTL design. These requirements cannot satisfy for all project situation. The better solution is create a Coding Rule which request Designer add a "half-cycle-delay" at first stage (FF0 and RF0) when using upper solution.

