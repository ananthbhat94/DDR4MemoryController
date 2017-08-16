//The modules here are used in the Scheduler for calculations
//Author: Sriram VB
module Compare(Count1, Count2, Index1, Index2, Max);
input [15:0]Count1, Count2;
input [2:0]Index1,Index2;
output logic [2:0] Max;

always_comb begin
	if(Count2>Count1)
		Max = Index2;
	else 
		Max = Index1;
end

endmodule


module CalcMax#(parameter BuffLength = 8)(Counters, MaxValue);
input [BuffLength - 1:0][15:0] Counters;
output logic [2:0]MaxValue;

wire [5:0][2:0]max;
Compare c0(Counters[0],Counters[1],3'd0,3'd1,max[0]);
Compare c1(Counters[2],Counters[3],3'd2,3'd3,max[1]);
Compare c2(Counters[4],Counters[5],3'd4,3'd5,max[2]);
Compare c3(Counters[6],Counters[7],3'd6,3'd7,max[3]);

Compare c4(Counters[max[0]],Counters[max[1]],max[0],max[1],max[4]);
Compare c5(Counters[max[2]],Counters[max[3]],max[2],max[3],max[5]);

Compare c6(Counters[max[4]],Counters[max[5]],max[4],max[5],MaxValue);
endmodule
